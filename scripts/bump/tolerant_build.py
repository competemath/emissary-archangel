#!/usr/bin/env python3
"""tolerant_build.py — build a Lean library's modules in dependency order, writing every module's .olean even when it has errors.

`lake build` stops a module at its first error and blocks everything that imports it; after a toolchain or Mathlib bump one
failing proof then hides the rest of its module and all downstream modules from every later step. This runs each module
through scripts/bump/TolerantBuild.lean (the toolchain's own frontend, saving the environment Lean's error recovery leaves)
so a failing declaration costs that declaration. Only a bad import (a module that no longer exists) or a crash stops a module.
The checks that make this safe are elsewhere: gate2_batch.py rejects every declaration whose axioms include `sorryAx`.

Modules are scheduled by their `import` lines (the library's own and the dependencies', the latter found on LEAN_PATH),
N at a time, and a module is skipped when its source and the oleans of its imports are byte-identical to the last run
(--cache), which is what makes the repair rounds cheap: only edited modules and their dependents are rebuilt.

  tolerant_build.py --lib DIR --roots R,R [--jobs N] [--timeout MIN] [--log build.log] [--report tb.json] [--cache DIR]

The log is in Lake's format (`error: path:line:col: message`) so scripts/trial-library-build.py's parser reads it.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent
DRIVER = HERE / "TolerantBuild.lean"
MSG = re.compile(r"^(\S+?\.lean):(\d+):(\d+): (error|warning|info)(?:\([^)]*\))?: ?(.*)$")
CORE = ("Init", "Std", "Lean", "Lake")


def lake_env(lib: Path) -> dict[str, str]:
    r = subprocess.run(["lake", "env", sys.executable, "-c", "import os,json;print(json.dumps(dict(os.environ)))"], cwd=lib, capture_output=True, text=True)
    if r.returncode:
        sys.exit(f"lake env failed: {r.stderr[:300]}")
    return json.loads(r.stdout.splitlines()[-1])


def esc(part: str) -> str:
    """A path component as Lean writes it in a module name: `1102.4662` is «1102.4662»."""
    return part if re.fullmatch(r"[^\W\d][\w']*", part) else f"«{part}»"


def split_mod(mod: str) -> list[str]:
    return [m.group(0).strip("«»") for m in re.finditer(r"«[^»]*»|[^.]+", mod)]


def module_files(lib: Path, roots: list[str]) -> dict[str, Path]:
    found: dict[str, Path] = {}
    for r in roots:
        top = lib / f"{r}.lean"
        if top.exists():
            found[r] = top
        if (lib / r).is_dir():
            for p in sorted((lib / r).rglob("*.lean")):
                found[".".join(esc(x) for x in p.relative_to(lib).with_suffix("").parts)] = p
    return found


MODNAME = r"(?:«[^»]*»|[^\s«»])+"
HEADER_IMPORT = re.compile(r"(?:(?:public|private|meta)[ \t]+)*import[ \t]+(?:all[ \t]+)?(" + MODNAME + ")")
HEADER_KEYWORD = re.compile(r"(?:module|prelude)\b")


def header_imports(text: str) -> list[str]:
    """The imports of a file: the `import` lines of its header, after any comments (`/- … -/`, nested, and `--`) and a
    `module` / `prelude` keyword, up to the first command."""
    out, i, n = [], 0, len(text)
    while i < n:
        if text[i].isspace():
            i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j + 1
        elif text.startswith("/-", i):
            depth, i = 1, i + 2
            while i < n and depth:
                if text.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif text.startswith("-/", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
        else:
            m = HEADER_KEYWORD.match(text, i) or HEADER_IMPORT.match(text, i)
            if not m:
                break
            if m.re is HEADER_IMPORT:
                out.append(m.group(1))
            i = m.end()
    return out


class Builder:
    def __init__(self, a: argparse.Namespace):
        self.lib = Path(a.lib).resolve()
        self.roots = [r for r in a.roots.split(",") if r]
        self.env = lake_env(self.lib)
        self.search = [Path(p) for p in self.env.get("LEAN_PATH", "").split(":") if p]
        self.out = self.lib / ".lake" / "build" / "lib" / "lean"
        self.out.mkdir(parents=True, exist_ok=True)
        self.cache = Path(a.cache) if a.cache else self.lib / ".bump-cache"
        self.cache.mkdir(parents=True, exist_ok=True)
        self.timeout = a.timeout * 60
        self.jobs = a.jobs or os.cpu_count() or 2
        self.mods = module_files(self.lib, self.roots)
        if a.modules:  # a shard: only these (a dependency-closed set: everything they import is in it)
            keep = {ln.strip() for ln in Path(a.modules).read_text().splitlines() if ln.strip()}
            self.mods = {m: p for m, p in self.mods.items() if m in keep}
        self.lock = threading.Lock()
        self.status: dict[str, dict] = {}
        self.log_lines: list[str] = []
        self.sha: dict[str, str] = {}  # module -> olean hash, once built
        self.done = {m: threading.Event() for m in self.mods}
        self.imports = {m: header_imports(p.read_text(errors="replace")) for m, p in self.mods.items()}
        self.ext_cache: dict[str, bool] = {}

    def olean_of(self, mod: str, base: Path | None = None) -> Path:
        parts = split_mod(mod)
        return (base or self.out).joinpath(*parts[:-1], parts[-1] + ".olean")

    def external_exists(self, mod: str) -> bool:
        if split_mod(mod)[0] in CORE:
            return True
        if mod not in self.ext_cache:
            self.ext_cache[mod] = any(self.olean_of(mod, d).exists() for d in self.search)
        return self.ext_cache[mod]

    def external_sha(self, mod: str) -> str:
        if split_mod(mod)[0] in CORE:
            return "core"
        for d in self.search:
            f = self.olean_of(mod, d)
            if f.exists():
                st = f.stat()
                return f"{st.st_size}:{int(st.st_mtime)}"  # an external olean only changes with the dependency's rebuild
        return "missing"

    def emit(self, lines: list[str]) -> None:
        with self.lock:
            self.log_lines += lines

    def build_one(self, mod: str) -> None:
        src = self.mods[mod]
        rel = str(src.relative_to(self.lib))
        try:
            for dep in self.imports[mod]:
                if dep in self.mods:
                    self.done[dep].wait()
            bad = [d for d in self.imports[mod] if (d not in self.mods and not self.external_exists(d))]
            blocked = [d for d in self.imports[mod] if d in self.mods and self.status[d]["state"] in ("blocked", "bad_import", "crashed")]
            if bad:
                self.emit([f"error: {rel}: bad import '{d}'" for d in bad])
                self.status[mod] = {"state": "bad_import", "bad": bad, "errors": 0}
                return
            if blocked:
                self.status[mod] = {"state": "blocked", "behind": blocked, "errors": 0}
                return
            h = hashlib.sha256()
            h.update(src.read_bytes())
            h.update(DRIVER.read_bytes())
            for dep in self.imports[mod]:
                h.update((self.sha[dep] if dep in self.mods else self.external_sha(dep)).encode())
            key = h.hexdigest()
            kf, lf, olean = self.cache / f"{mod}.key", self.cache / f"{mod}.log.json", self.olean_of(mod)
            if kf.exists() and kf.read_text() == key and lf.exists() and olean.exists():
                st = json.loads(lf.read_text())
                st["cached"] = True
                self.status[mod] = st
                self.sha[mod] = hashlib.sha256(olean.read_bytes()).hexdigest()
                self.emit(st.pop("log", []))
                return
            olean.parent.mkdir(parents=True, exist_ok=True)
            if olean.exists():
                olean.unlink()
            t0 = time.time()
            try:
                r = subprocess.run(["lean", "--run", str(DRIVER), rel, mod, str(olean)], cwd=self.lib, env=self.env, capture_output=True, text=True, timeout=self.timeout)
                code, out = r.returncode, r.stdout + r.stderr
            except subprocess.TimeoutExpired as e:
                code, out = 124, ((e.stdout or b"").decode(errors="replace") if isinstance(e.stdout, bytes) else (e.stdout or "")) + f"\n{rel}:1:0: error: tolerant_build: timeout after {self.timeout // 60} min"
            lines, nerr, nwarn = [], 0, 0
            for ln in out.splitlines():
                m = MSG.match(ln)
                if m:
                    kind = m.group(4)
                    nerr += kind == "error"
                    nwarn += kind == "warning"
                    lines.append(f"{kind}: {m.group(1)}:{m.group(2)}:{m.group(3)}: {m.group(5)}")
                else:
                    lines.append(ln)
            state = "clean" if code == 0 and olean.exists() else "errors" if code == 2 and olean.exists() else "crashed"
            st = {"state": state, "errors": nerr, "warnings": nwarn, "seconds": round(time.time() - t0, 1), "exit": code}
            if state == "crashed":
                st["tail"] = out[-600:]
            if olean.exists():
                self.sha[mod] = hashlib.sha256(olean.read_bytes()).hexdigest()
                kf.write_text(key)
                lf.write_text(json.dumps({**st, "log": lines}))
            self.status[mod] = st
            self.emit(lines)
        finally:
            self.status.setdefault(mod, {"state": "crashed", "errors": 0, "tail": "scheduler error"})
            self.done[mod].set()

    def run(self) -> dict:
        t0 = time.time()
        with ThreadPoolExecutor(max_workers=self.jobs) as ex:
            # submit in an order where a module's imports come first, so waiting workers are never starved
            order, seen = [], set()

            def visit(m: str) -> None:
                if m in seen:
                    return
                seen.add(m)
                for d in self.imports[m]:
                    if d in self.mods:
                        visit(d)
                order.append(m)

            sys.setrecursionlimit(100000)
            for m in sorted(self.mods):
                visit(m)
            list(ex.map(self.build_one, order))
        counts: dict[str, int] = {}
        for st in self.status.values():
            counts[st["state"]] = counts.get(st["state"], 0) + 1
        # what `lake build` would have produced: a module is only built if every import was built without error
        strict, memo = 0, {}

        def lake_ok(m: str) -> bool:
            if m not in memo:
                memo[m] = self.status[m]["state"] == "clean" and all(lake_ok(d) for d in self.imports[m] if d in self.mods)
            return memo[m]

        strict = sum(lake_ok(m) for m in self.mods)
        return {"modules": len(self.mods), "by_state": counts, "lake_would_build": strict, "seconds": round(time.time() - t0, 1), "status": self.status}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--lib", required=True)
    ap.add_argument("--roots", required=True)
    ap.add_argument("--jobs", type=int, default=0)
    ap.add_argument("--timeout", type=int, default=90, help="minutes per module")
    ap.add_argument("--log", default="build.log")
    ap.add_argument("--report", default="tb.json")
    ap.add_argument("--cache", default="")
    ap.add_argument("--modules", default="", help="file with one module per line: build only these (a dependency-closed set)")
    a = ap.parse_args()
    b = Builder(a)
    res = b.run()
    Path(a.log).write_text("\n".join(b.log_lines) + "\n")
    Path(a.report).write_text(json.dumps(res, indent=1))
    print(f"- Modules: {res['modules']}: {res['by_state']}; lake build would have produced {res['lake_would_build']} of them; {res['seconds']} s")


if __name__ == "__main__":
    main()
