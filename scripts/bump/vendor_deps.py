#!/usr/bin/env python3
"""vendor_deps.py — bring the code a library imports from the OTHER Lake packages it requires into the library, so that it is built, checked and shipped with it.

  vendor_deps.py --lib LIB --roots A,B [--out vendored.json] [--print-roots]

Why. A library can `require` another Lake package (stafford38-formal requires algebraic-analysis; 84 of the 148 registered libraries require something besides Mathlib, mostly documentation tools, but
albert-frame-triple-invariants, derived-alg-geo-lean, epsilon-sml, quadratic-number-fields and stafford38-formal import real code). The factory builds a library with its own driver
(tolerant_build.py) and `lake update` only DOWNLOADS the packages: nothing builds them, so every `import AlgebraicAnalysis.X` was a "bad import" (2026-10-28, stafford38-formal: 20 of
the 34 modules that failed of their own accord, and 365 of 436 modules taken out with them). The tree has no cross-library imports either (tree_verify.py), so the dependency cannot be
"imported from the tree" in the end: what the library uses of it has to ship with the library, as lean-pool ships its vendored AddCombi.

What it does. From the library's own modules it follows the imports; an import that is a module of a required package (and not Lean, Mathlib or one of the packages the tree is seeded
from) is copied into LIB at its module path, and so are the imports of that module, and so on. Only the modules reached are copied. The roots of the copies (`AlgebraicAnalysis`) are
printed, to be added to the roots of the build.

What it checks before anything enters the library (each failure is a recorded reason, never a guess):
  * FETCH: a package the manifest names and that is not on disk is downloaded at the pinned commit (https://github.com/ only, a full 40-hex commit, never a branch or tag), and the checkout must
    be exactly that commit;
  * PIN: a package that is a git checkout must be at the commit the manifest pins, or it is refused;
  * CODE: compiling Lean runs code, so a module is not copied if it declares or uses what runs code or trusts the compiler (`unsafe`, `initialize`, `elab`, `run_cmd`, `@[extern]`,
    `@[implemented_by]`, `native_decide`, `IO.Process`, `System.*`, …: the hard part of the tree's own content lint, scripts/bump/lint/allowlist.py); notation and macros are the tree's policy for the
    bundle step, not a reason to keep a dependency out. Comments and strings are not read as code;
  * LICENCE: the package's licence file, and a licence a module's own header claims (`SPDX-License-Identifier`, `Released under X license`), must both be permissive.
There is no vulnerability database for Lean packages (OSV and GitHub's advisory database have no Lean ecosystem), so "vulnerable" here means exactly the above: code that would run at compile time or
be trusted without the kernel, a pin that is not what was reviewed, and a licence that does not allow redistribution.

What it will not do (each is a recorded reason, never a guess):
  * copy a package whose licence it cannot read as one of the permissive ones (Apache-2.0, MIT, BSD-2/3, CC0, Unlicense): an unlicensed or copyleft package is `refused`, and what imports it stays unresolved;
  * overwrite a file the library already has with a different one (`conflict`), or choose between two packages that both have a module of the same name (`ambiguous`);
  * copy anything that is not reached from the library.
The copies are the package's files at the revision the library's lake-manifest.json pins, byte for byte; the report says package, url, revision, licence and module for each, so that the intake
pull request can say what it carries and under which licence.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE / "lint"))
import allowlist  # noqa: E402
import tolerant_build as tb  # noqa: E402
from lean_lex import code_only  # noqa: E402

# Modules the tree is seeded with or that ship with Lean: never vendored (their top-level name).
SEEDED = {"Init", "Std", "Lean", "Lake", "Mathlib", "Batteries", "Aesop", "Qq", "ProofWidgets", "Plausible", "LeanSearchClient", "ImportGraph", "Cli"}

# Words of the tree's lint that only concern how the bundle reads (notation, macros, syntax): the tree's policy for the bundle step, not a reason to keep a dependency out. Every other
# forbidden word runs code at compile time or trusts the compiler.
SOFT_WORDS = {"import", "notation", "notation3", "infix", "infixl", "infixr", "prefix", "postfix", "macro", "macro_rules", "syntax", "declare_syntax_cat"}
FETCH_PREFIXES = ("https://github.com/",)
_FULL_COMMIT = re.compile(r"[0-9a-f]{40}")

# `#` commands that only write a message: inert, and taken out later by inert_commands.py. Every other `#` command stays a risk: `#eval` and `#exec` run code at compile time, and an unknown one is not assumed harmless.
INERT_HASH = {"print", "check", "check_failure", "reduce", "synth", "find", "help", "lint", "time", "guard", "guard_expr", "guard_msgs", "adaptation_note", "count_heartbeats", "explode", "leansearch", "loogle", "moogle", "min_imports", "long_names", "sample"}

PERMISSIVE = ("Apache-2.0", "MIT", "BSD-2-Clause", "BSD-3-Clause", "CC0-1.0", "Unlicense")
_LICENCE_FILES = ("LICENSE", "LICENSE.md", "LICENSE.txt", "LICENCE", "COPYING", "COPYING.md", "UNLICENSE")
# Phrases that identify a licence text. Order matters: the first match wins and the copyleft ones come first, so that a file that mentions two is read as the stricter.
_SIGNATURES = (
    ("GPL", re.compile(r"GNU (?:AFFERO |LESSER )?GENERAL PUBLIC LICENSE", re.I)),
    ("MPL", re.compile(r"Mozilla Public License", re.I)),
    ("Apache-2.0", re.compile(r"Apache License[\s,]+Version 2\.0", re.I)),
    ("MIT", re.compile(r"Permission is hereby granted, free of charge", re.I)),
    ("BSD-3-Clause", re.compile(r"Redistributions in binary form must reproduce.*?Neither the name", re.I | re.S)),
    ("BSD-2-Clause", re.compile(r"Redistributions in binary form must reproduce", re.I)),
    ("CC0-1.0", re.compile(r"CC0 1\.0 Universal|Creative Commons Zero", re.I)),
    ("Unlicense", re.compile(r"This is free and unencumbered software released into the public domain", re.I)),
)


def has_licence_file(pkg_dir: Path) -> bool:
    return any((pkg_dir / n).is_file() for n in _LICENCE_FILES)


def read_licence(pkg_dir: Path) -> str | None:
    """The SPDX name of the package's licence, or None when there is no licence file or it is not one of the known texts."""
    for name in _LICENCE_FILES:
        f = pkg_dir / name
        if f.is_file():
            text = f.read_text(errors="replace")
            for spdx, rx in _SIGNATURES:
                if rx.search(text):
                    return spdx
            return None
    return None


def package_src_dirs(pkg_dir: Path) -> list[Path]:
    """Where a package keeps its modules: every `srcDir` its lakefile names (a package with several `lean_lib` targets can have several), else its root."""
    dirs: list[Path] = []
    for name in ("lakefile.toml", "lakefile.lean"):
        f = pkg_dir / name
        if f.is_file():
            for m in re.finditer(r'srcDir\s*(?:=|:=)\s*"([^"]+)"', f.read_text(errors="replace")):
                d = pkg_dir / m.group(1)
                if d not in dirs:
                    dirs.append(d)
    return dirs or [pkg_dir]



def hard_risks(text: str) -> list[str]:
    """What in a module runs code at compile time or trusts the compiler (the hard part of the tree's lint), read from code only."""
    code = code_only(text)
    risks = []
    for msg in allowlist._token_violations(code):
        m = re.match(r"`([^`]+)`", msg)
        if m and m.group(1) in SOFT_WORDS:
            continue
        if m and m.group(1).startswith("#") and m.group(1)[1:] in INERT_HASH:  # `#print axioms` and the like write a message and declare nothing: inert_commands.py takes them out
            continue
        risks.append(msg)
    attr_msgs, _ = allowlist._attribute_violations(code)
    risks += [m for m in attr_msgs if any(w in m for w in ("`extern`", "`implemented_by`", "`init`", "`builtin_init`", "`export`", "`never_extract`", "`csimp`", "`macro`", "`command_elab`", "`term_elab`", "`tactic`"))]
    return list(dict.fromkeys(risks))


_SPDX_TAG = re.compile(r"SPDX-License-Identifier:\s*([A-Za-z0-9.\-+ ]+?)\s*(?:\*/|-/|$)", re.M)
_RELEASED = re.compile(r"Released under ([A-Za-z0-9.\- ]+?) licen[cs]e", re.I)
_NAMES = {"apache 2.0": "Apache-2.0", "apache-2.0": "Apache-2.0", "apache2": "Apache-2.0", "mit": "MIT", "bsd": "BSD-3-Clause", "bsd-3-clause": "BSD-3-Clause", "bsd-2-clause": "BSD-2-Clause"}


def declared_licence(text: str) -> str | None:
    """The licence a module's own header claims (first 40 lines), or None when it claims none."""
    head = "\n".join(text.splitlines()[:40])
    m = _SPDX_TAG.search(head) or _RELEASED.search(head)
    if not m:
        return None
    raw = m.group(1).strip()
    return _NAMES.get(raw.lower(), raw)


def pinned_commit(pkg_dir: Path) -> str | None:
    """The commit a package checkout is at, or None when it is not a git checkout."""
    if not (pkg_dir / ".git").exists():
        return None
    r = subprocess.run(["git", "-C", str(pkg_dir), "rev-parse", "HEAD"], capture_output=True, text=True)
    return r.stdout.strip() if r.returncode == 0 else None


def _norm(name: str) -> str:
    return re.sub(r"[^a-z0-9]", "", name.lower())


def fetch_missing(lib: Path, *, wanted: set[str] | None = None, allow: tuple[str, ...] = FETCH_PREFIXES, run=subprocess.run) -> list[dict]:
    """Download the packages the manifest names and that are not on disk, at the pinned commit. Returns what was done, one entry per package; nothing is fetched that is not a
    https://github.com/ URL at a full commit (a branch or a tag moves; a pinned commit is what was reviewed). With `wanted` (the top-level module names the library imports and does not have), only a
    package whose name is one of them (case and punctuation aside: `algebraicAnalysis` provides `AlgebraicAnalysis`) is fetched: Mathlib, and the documentation tools a library requires, are not."""
    manifest_path = lib / "lake-manifest.json"
    done: list[dict] = []
    if not manifest_path.is_file():
        return done
    manifest = json.loads(manifest_path.read_text())
    packages_dir = lib / manifest.get("packagesDir", ".lake/packages")
    for p in manifest.get("packages", []):
        url, rev = str(p.get("url", "")), str(p.get("rev", ""))
        name = p.get("name") or url.rsplit("/", 1)[-1].removesuffix(".git")
        d = packages_dir / name
        if d.is_dir():
            continue
        if wanted is not None and _norm(name) not in {_norm(w) for w in wanted}:
            continue
        if not url.startswith(allow) or not _FULL_COMMIT.fullmatch(rev) or any(c in name for c in "/\\") or name in (".", ".."):
            done.append({"package": name, "fetched": False, "reason": "not a pinned https://github.com/ commit"})
            continue
        d.parent.mkdir(parents=True, exist_ok=True)
        try:
            for cmd in (["git", "clone", "--quiet", "--no-checkout", url, str(d)], ["git", "-C", str(d), "checkout", "--quiet", "--detach", rev]):
                r = run(cmd, capture_output=True, text=True, timeout=600)
                if r.returncode != 0:
                    raise RuntimeError((r.stderr or "")[:200])
            got = pinned_commit(d)
            if got != rev:
                raise RuntimeError(f"checked out {got}, not the pin")
            done.append({"package": name, "fetched": True, "commit": rev})
        except Exception as e:  # noqa: BLE001 — a failed fetch must leave nothing half-installed
            import shutil

            shutil.rmtree(d, ignore_errors=True)
            done.append({"package": name, "fetched": False, "reason": str(e)[:200]})
    return done


def inside(base: Path, p: Path) -> bool:
    """Whether p, with every symlink resolved, is base or lies beneath it (base resolved too)."""
    try:
        return p.resolve().is_relative_to(base.resolve())
    except (OSError, RuntimeError, ValueError):
        return False


def index_package(pkg_dir: Path) -> dict[str, Path]:
    """module name -> file, for the package's own sources (not its dependencies' packages, tests, or build output)."""
    out: dict[str, Path] = {}
    for src in package_src_dirs(pkg_dir):
        if not src.is_dir():
            continue
        for p in sorted(src.rglob("*.lean")):
            rel = p.relative_to(src)
            parts = rel.with_suffix("").parts
            if any(x in (".lake", "lake-packages", ".git") for x in parts) or (len(parts) == 1 and parts[0].lower().startswith("lakefile")):
                continue
            if p.is_symlink() or not inside(pkg_dir, p):  # a link to a file outside the package would be vendored under the package's name and licence
                continue
            out.setdefault(".".join(tb.esc(x) for x in parts), p)
    return out


def own_modules(lib: Path, roots: list[str]) -> dict[str, Path]:
    return tb.module_files(lib, roots)


def load_packages(lib: Path, report: dict | None = None) -> dict[str, dict]:
    """The packages of the manifest that are on disk: name -> {dir, root, url, rev, index}. A checkout that is not at the pinned commit is listed with an empty index (and refused in `report`)."""
    manifest = json.loads((lib / "lake-manifest.json").read_text())
    packages_dir = lib / manifest.get("packagesDir", ".lake/packages")
    pkgs: dict[str, dict] = {}
    for p in manifest.get("packages", []):
        name = p.get("name") or str(p.get("url", "")).rsplit("/", 1)[-1].removesuffix(".git")
        d = packages_dir / name
        if not d.is_dir():
            continue
        # a package can live in a subdirectory of its repository (`subDir` in the manifest): its modules, and its own LICENSE if it has one, are there
        sub = p.get("subDir") or ""
        root = d / sub if sub and ".." not in Path(sub).parts and not Path(sub).is_absolute() else d
        if not inside(d, root):  # a symlinked subDir can leave the checkout whatever its spelling
            root = d / "\0nonexistent" if sub else d
        pkgs[name] = {"dir": d, "root": root, "url": p.get("url", ""), "rev": p.get("rev", ""), "index": index_package(root)}
        at = pinned_commit(d)
        if at is not None and p.get("rev") and at != p.get("rev"):
            pkgs[name]["index"] = {}  # not what the manifest pins: nothing of it is used
            if report is not None:
                report["refused"].append({"package": name, "reason": f"checkout is at {at}, the manifest pins {p.get('rev')}"})
    return pkgs


def unresolved_tops(lib: Path, roots: list[str]) -> set[str]:
    """The top-level module names that the library, and every package module it reaches, imports and that no package on disk (and nothing seeded or of the library) provides."""
    pkgs = load_packages(lib)
    own = own_modules(lib, roots)
    seen = set(own)
    queue = list(own.values())
    out: set[str] = set()
    while queue:
        f = queue.pop()
        for dep in tb.header_imports(f.read_text(errors="replace")):
            t = tb.split_mod(dep)[0]
            if t in SEEDED or dep in seen or t in set(roots):
                continue
            owners = [n for n, p in pkgs.items() if dep in p["index"]]
            if len(owners) == 1:
                seen.add(dep)
                queue.append(pkgs[owners[0]]["index"][dep])
            elif not owners:
                out.add(t)
    return out


def vendor(lib: Path, roots: list[str], *, permissive: tuple[str, ...] = PERMISSIVE, fetch: bool = False, fetch_run=subprocess.run, fetch_allow: tuple[str, ...] = FETCH_PREFIXES) -> dict:
    manifest_path = lib / "lake-manifest.json"
    report: dict = {"vendored": [], "unsafe": [], "packages": {}, "unresolved": [], "conflicts": [], "ambiguous": [], "refused": [], "roots": [], "copied": 0}
    if not manifest_path.is_file():
        return report
    if fetch:
        # fetch as the traversal discovers what is missing: a package that only a package imports is found on the next pass
        report["fetched"] = []
        for _ in range(8):
            got = fetch_missing(lib, wanted=unresolved_tops(lib, roots), allow=fetch_allow, run=fetch_run)
            report["fetched"] += got
            if not any(g["fetched"] for g in got):
                break
    pkgs = load_packages(lib, report)

    # What an earlier run copied is the factory's to manage, not the library's: the roots may have grown to include the copies, the repair rounds may have edited them, and the
    # dependency or the library's imports may have changed since. The marker (beside LIB, as LIB.vendored.json: never inside the third-party checkout) says which files are ours.
    marker = lib.with_name(lib.name + ".vendored.json")  # beside the checkout, never in it: the library is third-party and could ship a marker of its own
    earlier: dict[str, dict] = {}
    if marker.is_file():
        earlier = {v["module"]: v for v in json.loads(marker.read_text()).get("vendored", [])}
    own = {m: f for m, f in own_modules(lib, roots).items() if m not in earlier}
    seen_own = set(own)
    queue = [m for m in own.values()]
    vendored: dict[str, tuple[str, Path]] = {}  # module -> (package, source file)
    unresolved: set[str] = set()
    refused: dict[str, str] = {}
    licence_of: dict[str, str | None] = {}

    def top(mod: str) -> str:
        return tb.split_mod(mod)[0]

    while queue:
        f = queue.pop()
        for dep in tb.header_imports(f.read_text(errors="replace")):
            if top(dep) in SEEDED or dep in seen_own or dep in vendored:
                continue
            owners = [n for n, p in pkgs.items() if dep in p["index"]]
            if not owners:
                unresolved.add(dep)
                continue
            if len(owners) > 1:
                report["ambiguous"].append({"module": dep, "packages": sorted(owners)})
                continue
            name = owners[0]
            if name not in licence_of:
                # a package in a subdirectory is licensed by its own file when it has one, and by the repository's only when it has none: an unrecognised local licence is refused,
                # never replaced by a permissive one of the repository around it
                licence_of[name] = read_licence(pkgs[name]["root"]) if has_licence_file(pkgs[name]["root"]) else read_licence(pkgs[name]["dir"])
            if licence_of[name] not in permissive:
                refused[name] = f"licence {licence_of[name] or 'not found or not recognised'}"
                unresolved.add(dep)
                continue
            src = pkgs[name]["index"][dep]
            text = src.read_text(errors="replace")
            claimed = declared_licence(text)
            risks = hard_risks(text)
            if claimed is not None and claimed not in permissive:
                risks = [f"the module's own header claims the licence {claimed}"] + risks
            if risks:
                if not any(u["module"] == dep for u in report["unsafe"]):
                    report["unsafe"].append({"module": dep, "package": name, "risks": risks[:6]})
                unresolved.add(dep)
                continue
            vendored[dep] = (name, src)
            queue.append(src)

    for mod, (name, src) in sorted(vendored.items()):
        dst = lib / Path(*tb.split_mod(mod)).with_suffix(".lean")
        data = src.read_bytes()
        ours = mod in earlier and earlier[mod].get("package") == name
        same_pin = ours and earlier[mod].get("rev") == pkgs[name]["rev"]
        if dst.exists() and dst.read_bytes() != data:
            if not ours:
                report["conflicts"].append({"module": mod, "package": name, "path": str(dst.relative_to(lib))})
                continue
            if same_pin:  # ours, at the same revision, edited since (a repair round): left as it is
                report["vendored"].append({"module": mod, "package": name, "rev": pkgs[name]["rev"], "path": str(dst.relative_to(lib)), "sha256": hashlib.sha256(data).hexdigest()})
                continue
            # ours, and the package moved on: the new revision replaces it
        if not dst.exists() or dst.read_bytes() != data:
            dst.parent.mkdir(parents=True, exist_ok=True)
            dst.write_bytes(data)
            report["copied"] += 1
        report["vendored"].append({"module": mod, "package": name, "rev": pkgs[name]["rev"], "path": str(dst.relative_to(lib)), "sha256": hashlib.sha256(data).hexdigest()})
    # a file we copied earlier that nothing reaches any more (the library or the dependency changed) is removed: it must not stay buildable
    reached = {m for m in vendored}
    for mod, v in earlier.items():
        if mod not in reached:
            stale = lib / str(v.get("path", ""))
            # the marker is a file of the library checkout and is not trusted: a path that leaves the library (absolute, `..`, a symlink) is never touched
            if inside(lib, stale) and not stale.is_symlink() and stale.is_file():
                stale.unlink()
                report.setdefault("removed", []).append(mod)
    done = {v["module"] for v in report["vendored"]}
    # a module that was not copied (a conflict) leaves what imports it unresolved; say so
    report["unresolved"] = sorted(unresolved | {m for m in vendored if m not in done})
    for name in sorted({v["package"] for v in report["vendored"]} | set(refused)):
        report["packages"][name] = {
            "url": pkgs[name]["url"],
            "rev": pkgs[name]["rev"],
            "licence": licence_of.get(name),
            "modules": sum(1 for v in report["vendored"] if v["package"] == name),
            **({"refused": refused[name]} if name in refused else {}),
        }
    report["refused"] += [{"package": n, "reason": r} for n, r in sorted(refused.items())]
    report["roots"] = sorted({top(v["module"]) for v in report["vendored"]} - set(roots) - {top(m) for m in own})
    if report["vendored"] or marker.is_file():
        marker.write_text(json.dumps({"vendored": sorted(report["vendored"], key=lambda v: v["module"])}, indent=1))
    return report


def modules_differ(report: dict, expected: dict) -> tuple[list[str], list[str]]:
    """(the modules `expected` vendored that this report did not, the modules this report vendored that `expected` did not). Names only: the revision a floating requirement resolves to
    may differ between the plan job and a shard (a retargeted library has no lake-manifest.json until `lake update` writes a new one), the set of modules the plan cut into shards may not."""
    have = {v["module"] for v in report.get("vendored", [])}
    want = {v["module"] for v in expected.get("vendored", [])}
    return sorted(want - have), sorted(have - want)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--lib", required=True)
    ap.add_argument("--roots", required=True, help="comma list")
    ap.add_argument("--out")
    ap.add_argument("--fetch", action="store_true", help="download the packages the manifest names and that are not on disk, at the pinned commit")
    ap.add_argument("--expect", help="the report of the plan job (sharded route): exit 1 unless exactly the same modules were vendored here, since the plan cut the shards over them")
    ap.add_argument("--print-roots", action="store_true", help="print the roots of the library with the roots of the copies, as a comma list, and nothing else")
    a = ap.parse_args()
    roots = [r for r in a.roots.split(",") if r]
    rep = vendor(Path(a.lib), roots, fetch=a.fetch)
    if a.out:
        Path(a.out).write_text(json.dumps(rep, indent=1))
    if a.print_roots:
        print(",".join(roots + rep["roots"]))
    print(
        f"vendored {len(rep['vendored'])} modules of {len(rep['packages'])} packages ({rep['copied']} files written); unresolved {len(rep['unresolved'])}, "
        f"refused {len(rep['refused'])}, unsafe {len(rep['unsafe'])}, conflicts {len(rep['conflicts'])}, ambiguous {len(rep['ambiguous'])}",
        file=sys.stderr,
    )
    if a.expect:
        try:
            expected = json.loads(Path(a.expect).read_text())
        except (OSError, ValueError) as e:
            print(f"::error::the plan's vendoring report {a.expect} cannot be read ({e}): the shards were cut over modules this job cannot compare with", file=sys.stderr)
            return 1
        missing, extra = modules_differ(rep, expected)
        if missing or extra:
            print(
                f"::error::the shard vendored other modules than the plan cut the shards over: {len(missing)} missing here ({', '.join(missing[:5])}), {len(extra)} not in the plan ({', '.join(extra[:5])}). "
                "A module the plan does not know is in no shard's list and is never built; one it knows and this job lacks makes its importers fail. The plan reads the library's committed lake-manifest.json, the shard the one `lake update` wrote after the retarget: a requirement on a moving branch can differ between them; run the workflow again, and if it recurs the requirement needs a pinned revision.",
                file=sys.stderr,
            )
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
