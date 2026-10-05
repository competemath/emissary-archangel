#!/usr/bin/env python3
"""bundle_layers.py — cut a finished bundle into PARTS that a merge queue can build one at a time.

A library of thousands of modules cannot arrive as one intake PR: the queue builds what a PR adds inside a 40-minute check, and a module costs about 3 seconds
on a 4-core runner (lean-pool's 4,186 modules: about 3.4 hours; tauceti's 5,544: about 4.5). So the bundle is cut into parts of at most N modules each
(default 300, about 15 minutes). A part is a consecutive slice of ONE topological order of the bundle's own modules, so the rule that makes parts safe holds
by construction: every module imports only the seed, modules of earlier parts, and modules of its own part, never a later one. The parts then merge in order,
each on top of the tree the earlier ones made.

The order is a depth-first post-order over the modules sorted by name: a module comes right after the modules it imports, so a directory of related modules
mostly lands in one part and few imports cross a cut. It is a pure function of the bundle (the same bundle, the same parts, byte for byte).

What a part holds (the same layout as a bundle, which is what the gate will check the PR against):
  - the part's own modules, unchanged;
  - the library's umbrella `Tengoku/<Ns>.lean` as it stands AFTER this part: the imports of every umbrella-listed module of the parts so far, in the original order;
  - the lines of `manifest.jsonl` whose module is in this part (the manifest of the library is the parts' lines appended in order);
  - a `report.json` of this part (counts, and the digest of the whole bundle it was cut from).
A file that is not a module of the library's tree path (the marker `Deps.lean`) goes with the first part.

  bundle_layers.py --bundle DIR --out OUT [--max-modules 300] [--tar]
      DIR is a composed bundle (DIR/Tengoku/<Ns>.lean, DIR/Tengoku/<Ns>/**.lean, DIR/manifest.jsonl, DIR/report.json); OUT/part-NNN/ per part and OUT/plan.json
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from dataclasses import dataclass, field
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import tolerant_build as tb  # noqa: E402

DEFAULT_MAX = 300


class BundleError(ValueError):
    pass


@dataclass
class Part:
    index: int  # from 1
    modules: list[str]  # in the order they were cut
    files: dict[str, bytes] = field(default_factory=dict)  # path -> bytes, ready to be archived
    manifest_lines: list[str] = field(default_factory=list)


def module_name(path: str) -> str:
    return path.removesuffix(".lean").replace("/", ".")


def own_modules(files: dict[str, bytes], ns: str) -> dict[str, str]:
    """module name -> path, for every `Tengoku/<ns>/**.lean` of the bundle."""
    prefix = f"Tengoku/{ns}/"
    return {module_name(p): p for p in files if p.startswith(prefix) and p.endswith(".lean")}


def import_graph(files: dict[str, bytes], mods: dict[str, str]) -> dict[str, list[str]]:
    own = set(mods)
    return {m: sorted({d for d in tb.header_imports(files[p].decode("utf-8", errors="replace")) if d in own and d != m}) for m, p in mods.items()}


def topological_order(graph: dict[str, list[str]], first: tuple[str, ...] = ()) -> list[str]:
    """Depth-first post-order over the names sorted (those in `first` before the rest): each module right after its imports. Raises BundleError on a cycle (Lean
    refuses one too)."""
    state: dict[str, int] = {}  # 1 on the stack, 2 done
    out: list[str] = []
    for root in sorted(graph, key=lambda m: (m not in first, m)):
        if state.get(root) == 2:
            continue
        stack = [(root, iter(graph[root]))]
        state[root] = 1
        while stack:
            node, it = stack[-1]
            for dep in it:
                if state.get(dep) == 1:
                    raise BundleError(f"an import cycle through {node} and {dep}")
                if dep not in state:
                    state[dep] = 1
                    stack.append((dep, iter(graph[dep])))
                    break
            else:
                state[node] = 2
                out.append(node)
                stack.pop()
    return out


def slices(order: list[str], max_modules: int) -> list[list[str]]:
    """Consecutive slices, as equal as they can be (sizes differ by at most one), none longer than `max_modules`."""
    if max_modules < 1:
        raise BundleError("a part holds at least one module")
    n = len(order)
    if n == 0:
        return []
    parts = -(-n // max_modules)
    base, extra = divmod(n, parts)
    out, i = [], 0
    for k in range(parts):
        size = base + (1 if k < extra else 0)
        out.append(order[i : i + size])
        i += size
    return out


def umbrella_after(umbrella: str, listed: set[str]) -> str:
    """The umbrella with only the imports of `listed` modules, in the original order; every other line is kept where it was."""
    out = []
    for ln in umbrella.split("\n"):
        s = ln.strip()
        if s.startswith("import "):
            mod = s.split()[-1]
            if mod not in listed:
                continue
        out.append(ln)
    text = "\n".join(out)
    return text if text.endswith("\n") or not text else text + "\n"


def plan(files: dict[str, bytes], ns: str, max_modules: int = DEFAULT_MAX) -> list[Part]:
    """The parts of the bundle in `files` (path -> bytes), library namespace `ns`. Raises BundleError for a bundle that cannot be cut."""
    mods = own_modules(files, ns)
    if not mods:
        raise BundleError(f"no module under Tengoku/{ns}/ in the bundle")
    umbrella_path = f"Tengoku/{ns}.lean"
    if umbrella_path not in files:
        raise BundleError(f"no umbrella {umbrella_path}")
    umbrella = files[umbrella_path].decode("utf-8")
    listed = {ln.split()[-1] for ln in umbrella.split("\n") if ln.strip().startswith("import ")}
    graph = import_graph(files, mods)
    # the marker `Deps.lean` (it tells tengoku's generator the library is in All.lean) is what the first part, the intake PR, must carry: it goes first
    order = topological_order(graph, (f"Tengoku.{ns}.Deps",))
    manifest = [ln for ln in files.get("manifest.jsonl", b"").decode("utf-8").split("\n") if ln.strip()]
    by_module: dict[str, list[str]] = {}
    for ln in manifest:
        m = json.loads(ln).get("module")
        if m not in mods:
            raise BundleError(f"a manifest record names a module the bundle does not have: {m!r}")
        by_module.setdefault(m, []).append(ln)
    digest = hashlib.sha256(b"".join(p.encode() + b"\0" + files[p] for p in sorted(files))).hexdigest()
    report = json.loads(files["report.json"]) if "report.json" in files else {}
    parts: list[Part] = []
    seen: set[str] = set()
    for i, chunk in enumerate(slices(order, max_modules), 1):
        seen |= set(chunk)
        part = Part(i, chunk)
        for m in chunk:
            part.files[mods[m]] = files[mods[m]]
            part.manifest_lines += by_module.get(m, [])
        if i == 1:  # the marker and any other file outside the modules of the library
            for p, data in files.items():
                if p not in (umbrella_path, "manifest.jsonl", "report.json") and p not in mods.values():
                    part.files[p] = data
        part.files[umbrella_path] = umbrella_after(umbrella, listed & seen).encode("utf-8")
        part.files["manifest.jsonl"] = ("\n".join(part.manifest_lines) + ("\n" if part.manifest_lines else "")).encode("utf-8")
        part.files["report.json"] = (
            json.dumps(
                {
                    "library": report.get("library"),
                    "part": i,
                    "modules": len(chunk),
                    "theorems": len(part.manifest_lines),
                    "lint_mode": report.get("lint_mode"),
                    "bundle_sha256": digest,
                },
                indent=1,
                sort_keys=True,
            )
            + "\n"
        ).encode("utf-8")
        parts.append(part)
    return parts


def check(parts: list[Part], files: dict[str, bytes], ns: str) -> None:
    """The rules that make the parts safe, checked on the result (not trusted from the construction). Raises BundleError at the first one broken."""
    mods = own_modules(files, ns)
    graph = import_graph(files, mods)
    where: dict[str, int] = {}
    for part in parts:
        for m in part.modules:
            if m in where:
                raise BundleError(f"{m} is in parts {where[m]} and {part.index}")
            where[m] = part.index
    if set(where) != set(mods):
        raise BundleError("the parts do not hold exactly the bundle's modules")
    for m, deps in graph.items():
        for d in deps:
            if where[d] > where[m]:
                raise BundleError(f"{m} (part {where[m]}) imports {d} (part {where[d]}), a later one")
    lines = [ln for p in parts for ln in p.manifest_lines]
    want = [ln for ln in files.get("manifest.jsonl", b"").decode("utf-8").split("\n") if ln.strip()]
    if sorted(lines) != sorted(want):
        raise BundleError("the parts' manifest lines are not the bundle's manifest lines")


def write_parts(parts: list[Part], out: Path, tar: bool = False) -> dict:
    out.mkdir(parents=True, exist_ok=True)
    summary = []
    for part in parts:
        d = out / f"part-{part.index:03d}"
        for path, data in part.files.items():
            dest = d / path
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(data)
        row = {
            "part": part.index,
            "modules": len(part.modules),
            "theorems": len(part.manifest_lines),
            "first": part.modules[0],
            "last": part.modules[-1],
        }
        if tar:
            import bundle_tar

            row["tar_sha256"] = bundle_tar.write_tar(part.files, str(out / f"part-{part.index:03d}.tar"))
        summary.append(row)
    plan_json = {
        "parts": summary,
        "modules": sum(r["modules"] for r in summary),
        "theorems": sum(r["theorems"] for r in summary),
    }
    (out / "plan.json").write_text(json.dumps(plan_json, indent=1) + "\n", encoding="utf-8")
    return plan_json


def read_bundle(d: Path) -> dict[str, bytes]:
    root = d.resolve()
    return {str(p.relative_to(root)): p.read_bytes() for p in sorted(root.rglob("*")) if p.is_file() and not p.is_symlink()}


def namespace(files: dict[str, bytes]) -> str:
    umbrellas = [p for p in files if p.count("/") == 1 and p.startswith("Tengoku/") and p.endswith(".lean")]
    if len(umbrellas) != 1:
        raise BundleError(f"a bundle has one umbrella Tengoku/<Ns>.lean, found {umbrellas}")
    return umbrellas[0].removeprefix("Tengoku/").removesuffix(".lean")


def main(argv: list[str]) -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--bundle", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--max-modules", type=int, default=DEFAULT_MAX)
    ap.add_argument(
        "--tar",
        action="store_true",
        help="also write each part as a canonical archive (bundle_tar.py)",
    )
    a = ap.parse_args(argv)
    files = read_bundle(Path(a.bundle))
    ns = namespace(files)
    parts = plan(files, ns, a.max_modules)
    check(parts, files, ns)
    summary = write_parts(parts, Path(a.out), a.tar)
    print(f"{ns}: {summary['modules']} modules, {summary['theorems']} theorems in {len(parts)} parts of at most {a.max_modules} modules")


if __name__ == "__main__":
    main(sys.argv[1:])
