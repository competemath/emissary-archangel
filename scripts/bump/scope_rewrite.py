#!/usr/bin/env python3
"""scope_rewrite.py — make what a library registers for other libraries' types local to the module that registers it.

Once the tree is imported as one, a GLOBAL instance or simp lemma that mentions nothing of its own library changes how every other
library's statements elaborate (formal-mathfin's `attribute [instance] Matrix.linftyOpNormedAddCommGroup` makes the norm of every matrix
the L-infinity operator norm; compfiles' `Coe (ℕ × ℕ) (ℤ × ℤ)` is a silent coercion everywhere). The merge queue's `tengoku-leakscan` lists
them, with positions, from the compiled environment:

    leak: instance Imo1977P2.instCoeForallIntForallReal registered in Tengoku.Compfiles.Compfiles.Imo1977P2 (declared at line 34)
    leak: instance Matrix.linftyOpNormedAddCommGroup registered in Tengoku.X.Y (declared in Tengoku.Analysis.Matrix.Normed: an `attribute` command ...)
    leak: simp Imo1979P6.Walk.take_append registered in Tengoku.Compfiles.Compfiles.Imo1979P6 (declared at line 62)

This turns each of those into `local` (`instance` -> `local instance`, `@[simp]` -> `@[local simp]`, `attribute [instance] X` ->
`attribute [local instance] X`) in the bundle's module. It edits inside lines and never adds one, so the positions of the report stay valid;
a note is appended at the end of each changed file. Nothing is trusted: the tree's build of the rewritten bundle decides whether a
module still compiles (a later module of the library that used the instance fails and is dropped, as any module that does not build).

  scope_rewrite.py [--bundle DIR …] [--pruned DIR …] --leaks "<report lines, separated by newlines or ;>"
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import tolerant_build as tb  # noqa: E402

LEAK = re.compile(
    r"leak:\s+(?P<kind>instance|simp)\s+(?P<name>\S+)\s+registered in\s+(?P<mod>\S+)"
    r"(?:\s+\(priority (?P<prio>\d+)\))?"
    r"(?:\s+\(declared at line (?P<line>\d+)\)|\s+\(declared in (?P<other>\S+?):)?"
)
ATTR_CMD = re.compile(r"^\s*attribute\s*\[")


def parse(text: str) -> list[dict]:
    # every `leak:` entry of the text, whatever separates them (newlines, `;`, or the single line a log flattens them to)
    return [
        {"kind": m["kind"], "name": m["name"], "mod": m["mod"], "line": int(m["line"]) if m["line"] else None, "prio": int(m["prio"]) if m["prio"] else None}
        for m in LEAK.finditer(text)
    ]


PART = r"«[^»/\\]*»|[^.«»/\\\s]+"
MODULE_NAME = re.compile(rf"(?:{PART})(?:\.(?:{PART}))*")


def parts_of(mod: str) -> list[str] | None:
    """the components of a module name (`«1102.4662»` is one), or None for anything that is not a plain module name"""
    if not MODULE_NAME.fullmatch(mod):
        return None
    parts = [m.group(0).strip("«»") for m in re.finditer(PART, mod)]
    return None if any(p in ("", ".", "..") for p in parts) else parts


def module_file(root: Path, mod: str, skip: int = 0) -> Path | None:
    """the file of a module in a bundle (`Tengoku/<Library>/…`) or, with skip=2, in the library's own layout (the leading `Tengoku.<Library>`
    dropped); never a file outside the root (a module name is input, and the files came from a build of the library's code)"""
    parts = parts_of(mod)
    if parts is None or len(parts) <= skip:
        return None
    p = root.joinpath(*parts[skip:]).with_suffix(".lean")
    if p.is_symlink() or not p.is_file() or not p.resolve().is_relative_to(root.resolve()):
        return None
    return p


def short(name: str) -> str:
    n = name.split(".")[-1]
    return n[1:-1] if n.startswith("«") and n.endswith("»") else n


def mask(text: str) -> str:
    """the text with every comment (line, nested block, doc) and string literal blanked to spaces: same length and same columns, so a word
    found in the mask is code, and its position is the position in the text"""
    out, i, n = [], 0, len(text)
    while i < n:
        c = text[i]
        if text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
        elif text.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/-", j):
                    depth, j = depth + 1, j + 2
                elif text.startswith("-/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            out.append("".join("\n" if ch == "\n" else " " for ch in text[i:j]))
            i = j
        elif c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            j = min(j + 1, n)
            out.append("".join("\n" if ch == "\n" else " " for ch in text[i:j]))
            i = j
        else:
            out.append(c)
            i += 1
    return "".join(out)


class Lines:
    """a file as lines, with the mask of each; an edit goes into both so that later edits find their columns"""

    def __init__(self, text: str):
        self.text, self.code = text.split("\n"), mask(text).split("\n")

    def insert(self, i: int, col: int, word: str) -> None:
        self.text[i] = self.text[i][:col] + word + self.text[i][col:]
        self.code[i] = self.code[i][:col] + word + self.code[i][col:]


NOT_LOCAL = r"(?<!local )(?<!scoped )"


def edit_declaration(f: Lines, line: int, kind: str) -> str:
    """`instance` of the declaration that starts at `line` (1-based; the range includes its doc comment and attributes), or the `simp` of an
    `@[...]` on it: "edited", "already" when it is local/scoped already, "missing" when it is not found"""
    for i in range(max(0, line - 1), min(len(f.text), line + 14)):
        code = f.code[i]
        col = None
        if kind == "instance":
            if ATTR_CMD.match(code):
                continue
            if re.search(r"\b(?:local|scoped)\s+instance\b", code):
                return "already"
            m = re.search(rf"(?<![\w.]){NOT_LOCAL}\binstance\b", code)
            col = m.start() if m else None
        else:
            for attrs in re.finditer(r"@\[([^\]]*)\]", code):
                if re.search(r"\b(?:local|scoped)\s+simp\b", attrs.group(1)):
                    return "already"
                hit = re.search(rf"(?<![\w.]){NOT_LOCAL}\bsimp\b", attrs.group(1))
                if hit:
                    col = attrs.start(1) + hit.start()
                    break
        if col is not None:
            f.insert(i, col, "local ")
            return "edited"
    return "missing"


def edit_attribute_command(f: Lines, name: str, kind: str) -> str:
    """an `attribute [instance] … name …` (or `[simp]`) command that registers a declaration of another library"""
    n = short(name)
    word = "instance" if kind == "instance" else "simp"
    for i, s in enumerate(f.code):
        if not ATTR_CMD.match(s):
            continue
        j = i
        while j + 1 < len(f.code) and f.code[j + 1].strip() and not f.code[j + 1].lstrip().startswith(("theorem", "lemma", "def", "instance", "@[")):
            j += 1
        block = "\n".join(f.code[i : j + 1])
        if not re.search(rf"(?<![\w]){re.escape(n)}(?![\w'])", block):
            continue
        head = re.match(r"(\s*attribute\s*\[)([^\]]*)(\])", s)
        if not head:
            continue
        if re.search(rf"\b(?:local|scoped)\s+{word}\b", head.group(2)):
            return "already"
        hit = re.search(rf"(?<![\w.]){NOT_LOCAL}\b{word}\b", head.group(2))
        if hit:
            f.insert(i, head.start(2) + hit.start(), "local ")
            return "edited"
    return "missing"


def rewrite_file(path: Path, leaks: list[dict]) -> tuple[int, list[str]]:
    text = path.read_text()
    f = Lines(text)
    done, skipped = 0, []
    for lk in sorted(leaks, key=lambda x: -(x["line"] or 0)):
        r = edit_declaration(f, lk["line"], lk["kind"]) if lk["line"] else edit_attribute_command(f, lk["name"], lk["kind"])
        if r == "edited":
            done += 1
        elif r == "missing":
            skipped.append(f"{lk['kind']} {lk['name']}")
    if done:
        new = "\n".join(f.text)
        path.write_text(new + ("" if new.endswith("\n") else "\n") + f"-- Tengoku: {done} registration(s) of this module made local so they do not change other libraries (generated)\n")
    return done, skipped


def apply_bundle(root: Path, leaks: list[dict], skip: int = 0) -> dict:
    by_mod: dict[str, list[dict]] = {}
    for lk in leaks:
        by_mod.setdefault(lk["mod"], []).append(lk)
    report = {"rewritten": 0, "skipped": [], "missing_modules": []}
    for mod, ls in sorted(by_mod.items()):
        f = module_file(root, mod, skip)
        if not f:
            report["missing_modules"].append(mod)  # a leak of a module this bundle does not carry (the other bundle: strict vs proposed)
            continue
        done, skipped = rewrite_file(f, ls)
        report["rewritten"] += done
        report["skipped"] += [f"{mod}: {s}" for s in skipped]
    return report



HEADER_LINE = re.compile(r"^\s*(?:(?:public|private|meta)\s+)*(?:import\s|module\s*$|prelude\s*$)")
SECTION = re.compile(r"^\s*(?:@\[expose\]\s*)?(?:(?:public|noncomputable)\s+)*section\b")


def body_start(lines: list[str]) -> int:
    """the index of the first line after the header: blank lines, comments (line and block), `module`/`prelude` and imports are the header; a
    `section` line that opens the body is part of it (the inserted commands go inside it)"""
    depth = 0
    for i, ln in enumerate(lines):
        s = ln.strip()
        if depth:
            depth = max(depth + s.count("/-") - s.count("-/"), 0)
            continue
        if not s or s.startswith("--"):
            continue
        if s.startswith("/-"):
            depth = max(s.count("/-") - s.count("-/"), 0)
            continue
        if HEADER_LINE.match(ln):
            continue
        return i + 1 if SECTION.match(ln) else i
    return len(lines)


def nameable(n: str) -> bool:
    """a declaration name an `attribute` command can say: not private, not a hygienic or auxiliary name"""
    return not (n.startswith("_private") or "_@" in n or "._hyg" in n or n.startswith("_"))


def native_names(root: Path, skip: int) -> dict[str, Path]:
    """module (the library's own name) -> file, for a bundle directory (`Tengoku/<Library>/…`, skip=0) or the library's layout (skip=2)"""
    base = root
    if skip == 0:
        libs = [d for d in (root / "Tengoku").iterdir() if d.is_dir()] if (root / "Tengoku").is_dir() else []
        if len(libs) != 1:
            return {}
        base = libs[0]
    out = {}
    for f in base.rglob("*.lean"):
        if f.is_symlink() or f.name == "Deps.lean":
            continue
        out[".".join(f.relative_to(base).with_suffix("").parts)] = f
    return out


def reexport(root: Path, leaks: list[dict], skip: int = 0) -> dict:
    """What a module of the library registered globally, the library's OTHER modules saw as given: every module that imports (even
    indirectly) a module with a flagged registration gets `attribute [local instance] X` / `[local simp] X` for it, so inside the library nothing
    changes while the tree outside sees none of it. A module's own registrations are local already (rewrite_file)."""
    files = native_names(root, skip)
    if not files:
        return {"reexported": 0, "modules": 0}
    own_leaks: dict[str, list[dict]] = {}
    for lk in leaks:
        parts = parts_of(lk["mod"])
        if parts and len(parts) > 2 and nameable(lk["name"]):
            own_leaks.setdefault(".".join(parts[2:]), []).append(lk)
    imports: dict[str, list[str]] = {}
    for mod, f in files.items():
        imports[mod] = []
        for imp in tb.header_imports(f.read_text()):
            parts = parts_of(imp)
            if not parts:
                continue
            cand = ".".join(parts[2:]) if (skip == 0 and parts[:1] == ["Tengoku"] and len(parts) > 2) else ".".join(parts)
            if cand in files:
                imports[mod].append(cand)

    def closure(mod: str) -> set[str]:
        seen, stack = set(), list(imports[mod])
        while stack:
            m = stack.pop()
            if m not in seen:
                seen.add(m)
                stack.extend(imports[m])
        return seen

    patched = names_total = 0
    for mod, f in sorted(files.items()):
        inherited: list[dict] = []
        for dep in sorted(closure(mod) - {mod}):
            inherited += own_leaks.get(dep, [])
        if not inherited:
            continue
        lines = f.read_text().split("\n")
        groups: dict[tuple[str, int | None], list[str]] = {}
        for lk in inherited:
            groups.setdefault((lk["kind"], lk.get("prio") if lk["kind"] == "instance" else None), []).append(lk["name"])
        ins = []
        for (kind, prio), ns in sorted(groups.items(), key=lambda kv: (kv[0][0], kv[0][1] or 0)):
            word = "instance" if kind == "instance" else "simp"
            attr = f"local {word}" + (f" {prio}" if prio not in (None, 1000) else "")
            uniq = sorted(set(ns))
            for k in range(0, len(uniq), 6):
                ins.append(f"attribute [{attr}] " + " ".join(uniq[k : k + 6]))
            names_total += len(uniq)
        at = body_start(lines)
        lines[at:at] = ins + [""]
        f.write_text("\n".join(lines))
        patched += 1
    return {"reexported": names_total, "modules": patched}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--bundle", action="append", default=[], help="a bundle directory (Tengoku/<Library>/… inside)")
    ap.add_argument("--pruned", action="append", default=[], help="a directory of the library's own layout (the factory's pruned sources)")
    ap.add_argument("--leaks", required=True)
    ap.add_argument("--reexport", action="store_true", help="also give every module that imports a flagged module the same registrations, local to it")
    a = ap.parse_args()
    leaks = parse(a.leaks)
    if not leaks:
        print(json.dumps({"rewritten": 0, "note": "no leak lines"}))
        return
    for dirs, skip in ((a.bundle, 0), (a.pruned, 2)):
        for b in dirs:
            if Path(b).exists():
                rep = apply_bundle(Path(b), leaks, skip)
                if a.reexport:
                    rep.update(reexport(Path(b), leaks, skip))
                print(b, json.dumps(rep))


if __name__ == "__main__":
    main()
