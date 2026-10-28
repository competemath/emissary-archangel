#!/usr/bin/env python3
"""explain_ejection.py — why the merge queue rejected a part, module by module.

  explain_ejection.py --queue-log queue-build.log --shards DIR --shipped TAR_OR_DIR [--json out.json]

  queue-build.log  the `queue-build` job log of the failed merge group (`gh api repos/competemath/tengoku/actions/jobs/<id>/logs`)
  DIR              the shard artifacts of the ORIGINAL bump run (`gh run download <run> -p 'shard-<key>-*' -D DIR`): DIR/shard-*/shard-pack/{errors.log,src/}
  TAR_OR_DIR       what was shipped: the part's (or the whole bundle's) tar, or a directory holding Tengoku/<Ns>/...

Every error of the queue build is put in one class (2026-10-11: three real causes were found by exactly this comparison, by hand):

  A  the declaration the error is in ALSO failed in the factory's own build, and was shipped anyway (it was kept for the text of another, or a passed theorem leans on it)
  B  'Unknown identifier / constant X' or 'invalid field X' where X is a declaration of the library that the pruning left out of every shipped module
  C  the module lost attributes the packager stripped (strip_attrs: the allow-list refuses them), and the error is not A or B: a proof that unfolds through them stops working
  E  'Unknown identifier / constant X' where X is declared nowhere in the library or the shipped files: a name the tree's Mathlib does not have
  D  none of these: look at the shipped lines by hand (headers, options, imports, instances)

Nothing is run but regular expressions: the files are data.
"""

from __future__ import annotations

import argparse
import collections
import json
import re
import sys
import tarfile
from pathlib import Path

ERR = re.compile(r"error: Tengoku/(?P<ns>[^/\s]+)/(?P<rel>\S+?\.lean):(?P<line>\d+):(?P<col>\d+): (?P<msg>.*)$")
FAC = re.compile(r"error: (?:\./)*(?P<rel>\S+?\.lean):(?P<line>\d+):\d+: (?P<msg>.*)$")
TARGET = re.compile(r"^\S*\s*- Tengoku\.(?P<mod>\S+)\s*$")
# Lean has spelled these `Unknown identifier `x``, `unknown constant 'x'` and `unknown namespace ‘x’`; a name may end in primes (`'mul_comm''`), so a single-quoted name runs to the quote that ends a word
UNKNOWN = re.compile(r"(?:[Uu]nknown (?:identifier|constant|namespace)|[Ii]nvalid field) (?:`(?P<bt>[^`]+)`|['‘’](?P<sq>\S+?)['’](?=[\s,.:;)]|$))")


def unknown_name(msg: str) -> str | None:
    """The name an 'unknown identifier / constant / namespace' or 'invalid field' error says, in any of the spellings Lean has used; None for any other message."""
    m = UNKNOWN.search(msg)
    return (m.group("bt") or m.group("sq")) if m else None
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:private |protected |noncomputable |nonrec |unsafe )*(?:theorem|lemma|def|abbrev|instance|structure|inductive|class)\s+(?P<name>[^\s:({\[⦃]+)")
DECL_HEAD = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:private |protected |noncomputable |nonrec |unsafe )*(?:theorem|lemma|def|abbrev|instance|structure|inductive|class)\b")
ATTR = re.compile(r"@\[([^\]]*)\]")


def enclosing(lines: list[str], line: int) -> str | None:
    """The first line of the declaration that contains `line` (1-based)."""
    for i in range(min(line, len(lines)) - 1, -1, -1):
        if DECL_HEAD.match(lines[i]):
            return lines[i].strip()
    return None


def attributes(text: str) -> collections.Counter:
    out: collections.Counter = collections.Counter()
    for m in ATTR.finditer(text):
        for a in m.group(1).split(","):
            words = [w for w in a.split() if w not in ("local", "scoped")]
            if words:
                out[words[0]] += 1
    return out


def declared(text: str) -> set[str]:
    return {m.group("name") for ln in text.split("\n") if (m := DECL.match(ln))}


class Shipped:
    """The shipped files, from a tar or a directory: relative path (below Tengoku/<Ns>/) -> text."""

    def __init__(self, where: Path):
        self.files: dict[str, str] = {}
        self.namespaces: set[str] = set()  # the <Ns> of every Tengoku/<Ns>/… file (one library's bundle has one)
        if where.is_dir():
            for p in where.rglob("*.lean"):
                parts = p.relative_to(where).parts
                if len(parts) > 2 and parts[0] == "Tengoku" and not p.is_symlink():  # a link in a bundle is not a module (bundle_cut.py skips them too)
                    self.files["/".join(parts[2:])] = p.read_text(errors="replace")
                    self.namespaces.add(parts[1])
        else:
            with tarfile.open(where) as t:
                for m in t:
                    parts = m.name.removeprefix("./").split("/")
                    if m.isfile() and m.name.endswith(".lean") and len(parts) > 2 and parts[0] == "Tengoku":
                        f = t.extractfile(m)
                        assert f is not None
                        self.files["/".join(parts[2:])] = f.read().decode("utf-8", "replace")
                        self.namespaces.add(parts[1])
        self.last = {n.rsplit(".", 1)[-1] for text in self.files.values() for n in declared(text)}


class Factory:
    """What the original run's shards recorded: the errors per file, and the source of every module."""

    def __init__(self, shards: Path | None):
        """`shards` None (or a directory with no shard in it): nothing is known of the factory's build, and A, B and C cannot be told (see `present`)."""
        self.errors: dict[str, list[tuple[int, str]]] = collections.defaultdict(list)
        self.src: dict[str, str] = {}
        for log in sorted(shards.glob("shard-*/shard-pack/errors.log")) if shards else ():
            for ln in log.read_text(errors="replace").splitlines():
                m = FAC.match(ln)
                if m:
                    self.errors[m.group("rel")].append((int(m.group("line")), m.group("msg")))
            for p in (log.parent / "src").rglob("*.lean"):
                self.src.setdefault(str(p.relative_to(log.parent / "src")), p.read_text(errors="replace"))
        self.present = bool(self.src)
        self.last = collections.defaultdict(set)  # last component of a declared name -> modules of the source that declare it
        for rel, text in self.src.items():
            for n in declared(text):
                self.last[n.rsplit(".", 1)[-1]].add(rel)

    def failed_heads(self, rel: str) -> set[str]:
        lines = self.src.get(rel, "").split("\n")
        return {h for ln, _ in self.errors.get(rel, ()) if (h := enclosing(lines, ln))}


def classify(rel: str, line: int, msg: str, shipped: Shipped, fac: Factory) -> tuple[str, str]:
    lines = shipped.files.get(rel, "").split("\n")
    head = enclosing(lines, line)
    if head and head in fac.failed_heads(rel):
        return "A", f"the declaration `{head[:70]}` also failed in the factory's own build"
    name = unknown_name(msg)
    if name:
        last = name.rsplit(".", 1)[-1]
        if last in fac.last and last not in shipped.last:
            return "B", f"`{name}` is declared in {sorted(fac.last[last])[0]} and no shipped module declares it"
        if last not in fac.last and last not in shipped.last:
            return "E", f"`{name}` is declared nowhere in the library: a name the tree's Mathlib does not have"
    stripped = attributes(fac.src.get(rel, "")) - attributes(shipped.files.get(rel, ""))
    if stripped:
        return "C", "attributes of the source are missing in the shipped file: " + ", ".join(f"{a} x{n}" for a, n in sorted(stripped.items()))
    return "D", "shipped lines: " + " | ".join(x.strip()[:60] for x in lines[max(0, line - 2) : line + 1])


def explain(log_text: str, shipped: Shipped, fac: Factory) -> dict:
    failing = [m.group("mod") for ln in log_text.splitlines() if (m := TARGET.match(ln))]
    per_module: dict[str, list[dict]] = collections.defaultdict(list)
    seen = set()
    for ln in log_text.splitlines():
        m = ERR.search(ln)
        if not m:
            continue
        rel, line, msg = m.group("rel"), int(m.group("line")), m.group("msg")
        if (rel, line) in seen:
            continue
        seen.add((rel, line))
        cls, why = classify(rel, line, msg, shipped, fac)
        per_module[rel].append({"line": line, "message": msg[:90], "class": cls, "why": why})
    counts = collections.Counter(e["class"] for es in per_module.values() for e in es)
    first = {rel: es[0]["class"] for rel, es in per_module.items()}
    return {"failing_targets": failing, "modules": per_module, "error_classes": dict(counts), "module_first_class": dict(collections.Counter(first.values()))}


def render(r: dict) -> str:
    out = [f"{len(r['failing_targets'])} failing target(s), {len(r['modules'])} module(s) with errors; errors by class: {r['error_classes']}"]
    for rel, es in sorted(r["modules"].items()):
        out.append(f"  {rel}")
        for e in es[:4]:
            out.append(f"    {e['class']} line {e['line']}: {e['message']}\n         {e['why']}")
        if len(es) > 4:
            out.append(f"    … and {len(es) - 4} more")
    out.append("A = shipped a declaration that failed in the factory; B = a cut declaration still named; C = stripped attributes; E = a name the tree's Mathlib lacks; D = unexplained")
    return "\n".join(out)


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--queue-log", required=True)
    ap.add_argument("--shards", required=True)
    ap.add_argument("--shipped", required=True)
    ap.add_argument("--json", default="")
    a = ap.parse_args(argv)
    r = explain(Path(a.queue_log).read_text(errors="replace"), Shipped(Path(a.shipped)), Factory(Path(a.shards)))
    print(render(r))
    if a.json:
        Path(a.json).write_text(json.dumps(r, indent=1) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
