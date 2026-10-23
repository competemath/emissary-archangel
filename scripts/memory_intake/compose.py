"""Compose a studied bundle from the candidates of competemath.com: modules, manifest, report, the verdict on every theorem, and what to tell the account.

Pure: no network, no clock, no file. `run.py` does the I/O. The studied lane's contract is in competemath/tengoku, `scripts/ci/studied_check.py` (what a PR must look like) and
`docs/pr-classes.md` section 9; the bar a theorem must clear is praiser's `bar.py` (`bar/0`); the words a verdict becomes are the notices catalogue of competemath.com
(`src/app/lib/leak-memory/notices-catalogue.ts`).

What one candidate bundle becomes (one account, one target, at most ten theorems):

  every theorem   a module `Tengoku/Studied/<Ns>/S<id12>.lean` (`import Tengoku.Seed`, a module docstring, the closure inside `namespace Tengoku.Studied.<Ns>.S<id12>`)
  the reviewer    praiser's checks over those modules (injected: `review_fn`), and the bar's verdict on each: accept, return (with codes) or reject
  the accepted    manifest lines, the report, the bundle id: the PR the studied App opens (`bundle_files`)
  the others      events for the account's notices: returned (fixable, with the codes) or rejected (final)

This job compiles nothing: a candidate is a theorem the run's own verifier (Leak IV) accepted when it was saved and the site judged its harness evidence, and the Tengoku tree
builds every module twice before anything merges (the autotag build, then the merge queue). The report says so.
"""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass, field
from typing import Callable

BAR = "bar/0"
SOURCE = "leak-memory"
MAX_THEOREMS = 10
IMPORT = "import Tengoku.Seed"
NAME = re.compile(r"[A-Za-z_][\w.'!?]{0,120}")
ENTRY_ID = re.compile(r"[0-9a-f]{8,64}")
AUTHOR = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.-]{0,99}")
TARGET_ID = re.compile(r"[a-z][a-z0-9]*(?:-[a-z0-9]+)*")


def pascal(target: str) -> str:
    return "".join(w[:1].upper() + w[1:] for w in re.split(r"[-_ ]+", target) if w)


def squash(s: str) -> str:
    return re.sub(r"\s+", " ", s).strip()


def entry_module(target: str, entry_id: str) -> tuple[str, str]:
    """(module name, path) of a theorem's module: S + the first 12 hex digits of its id."""
    ns, stem = pascal(target), f"S{entry_id[:12]}"
    return f"Tengoku.Studied.{ns}.{stem}", f"Tengoku/Studied/{ns}/{stem}.lean"


def bundle_id(target: str, author: str, entries: list[str]) -> str:
    """The same function as studied_check.py: stable for the same author, target and theorems, whatever order they were found in."""
    return hashlib.sha256((f"{target}\n{author}\n" + "\n".join(sorted(entries))).encode()).hexdigest()


def tidy(closure: str) -> str:
    """The closure as module text: no import lines (the module's header has the one import), no trailing whitespace or tabs, one final newline."""
    lines = [ln.rstrip().replace("\t", "  ") for ln in closure.replace("\r\n", "\n").split("\n") if not re.match(r"^\s*import\s", ln)]
    while lines and not lines[0].strip():
        lines.pop(0)
    while lines and not lines[-1].strip():
        lines.pop()
    return "\n".join(lines) + "\n"


def render_module(entry: dict, target: str, author: str, module: str) -> str:
    name = entry["name"]
    stars = (entry.get("quality") or {}).get("s")
    doc = (
        f"/-!\n# {name}\n\nA theorem that Leak proved on the target `{target}`, put forward by `{author}`"
        + (f" ({stars} stars)" if isinstance(stars, int) else "")
        + f".\n\n## Main results\n\n* `{module}.{name}`: see the statement below.\n-/\n"
    )
    return f"{IMPORT}\n\n{doc}\nnamespace {module}\n\n{tidy(entry['closure'])}\nend {module}\n"


def cited_by(entries: list[dict]) -> dict[str, int]:
    """How many OTHER theorems of the bundle use each one: its name occurs in their closure beyond the declaration of it that the closure carries."""
    out = {}
    for e in entries:
        n = 0
        pat = re.compile(r"(?<![\w.'])" + re.escape(e["name"].split(".")[-1]) + r"(?![\w'])")
        for o in entries:
            if o is not e and len(pat.findall(o["closure"])) >= 2:
                n += 1
        out[e["id"]] = n
    return out


@dataclass
class Verdict:
    entry: dict
    verdict: str  # accept | return | reject
    codes: list = field(default_factory=list)
    merit: list = field(default_factory=list)


@dataclass
class Composition:
    target: str
    author: str
    verdicts: list = field(default_factory=list)
    modules: dict = field(default_factory=dict)  # path -> text, accepted only
    manifest_lines: list = field(default_factory=list)
    report: dict = field(default_factory=dict)
    bundle: str = ""

    @property
    def accepted(self) -> list:
        return [v for v in self.verdicts if v.verdict == "accept"]

    def events(self) -> list:
        """The notices for the theorems that are not going into a PR: one event per code, listing the theorems it is about."""
        out = []
        for kind in ("return", "reject"):
            by_code: dict[str, list] = {}
            for v in self.verdicts:
                if v.verdict == kind:
                    for c in v.codes or ["bar.other"]:
                        by_code.setdefault(c, []).append(v.entry)
            for code, es in sorted(by_code.items()):
                out.append({
                    "username": self.author, "target": self.target, "kind": "returned" if kind == "return" else "rejected", "code": code,
                    "ids": [e["id"] for e in es][:50], "names": [e["name"] for e in es][:50],
                    "detail": f"{BAR}: " + ", ".join(sorted({c for v in self.verdicts if v.verdict == kind for c in v.codes if c == code})),
                })
        return out


def clean_candidate(bundle: object) -> tuple[dict | None, str]:
    """The candidate bundle of the site, or None and why not. Nothing out of shape is repaired."""
    if not isinstance(bundle, dict):
        return None, "not an object"
    t, a, es = bundle.get("target"), bundle.get("author"), bundle.get("entries")
    if not isinstance(t, str) or not TARGET_ID.fullmatch(t) or not isinstance(a, str) or not AUTHOR.fullmatch(a):
        return None, "target or author is not an id"
    if not isinstance(es, list) or not 1 <= len(es) <= MAX_THEOREMS:
        return None, f"1 to {MAX_THEOREMS} entries"
    for e in es:
        if not isinstance(e, dict) or not all(isinstance(e.get(k), str) and e[k].strip() for k in ("id", "name", "statement", "closure")):
            return None, "an entry lacks id, name, statement or closure"
        if not ENTRY_ID.fullmatch(e["id"]) or not NAME.fullmatch(e["name"]):
            return None, f"entry {e.get('id')!r}: id or name is not well formed"
    if len({e["id"][:12] for e in es}) != len(es) or len({e["name"] for e in es}) != len(es):
        return None, "two entries share an id prefix or a name"
    return bundle, ""


def harness_record(entry: dict) -> dict | None:
    """The harness evidence the site judged (candidates endpoint), in the studied report's shape; None when it is not there."""
    h = entry.get("harness") or {}
    r = h.get("receipt") or {}
    try:
        return {
            "entry": entry["id"], "build": h["buildId"], "build_verified": True, "ticket_age_s": round(h["ticketAgeMs"] / 1000),
            "seconds": int(r["seconds"]), "verify_ok": int(r["verifyOk"]), "verify_fail": int(r["verifyFail"]), "searches": int(r["searches"]),
            "attempts": int(r["attempts"]), "model": str(r.get("model") or "")[:80], "strategy": str(r["strategy"]),
        }
    except (KeyError, TypeError, ValueError):
        return None


def compose(candidate: dict, review_fn: Callable[[dict, dict], tuple], max_bytes: int = 60 * 1024) -> Composition:
    """`review_fn(modules, facts) -> (verdicts, ran)`: the reviewer and the bar over {module name: text}; `facts` maps an entry id to {module, stars, cited_by}.
    verdicts: {entry id: {"verdict", "codes", "merit"}}."""
    cand, why = clean_candidate(candidate)
    if cand is None:
        raise ValueError(f"candidate bundle refused: {why}")
    target, author, entries = cand["target"], cand["author"], cand["entries"]
    comp = Composition(target, author)
    cites = cited_by(entries)
    texts, facts = {}, {}
    early: dict[str, Verdict] = {}
    for e in entries:
        module, path = entry_module(target, e["id"])
        text = render_module(e, target, author, module)
        stars = (e.get("quality") or {}).get("s")
        if not isinstance(stars, int) or stars < 4:
            early[e["id"]] = Verdict(e, "return", ["bar.merit"])
        elif harness_record(e) is None:
            early[e["id"]] = Verdict(e, "return", ["gate.studied"])
        elif len(text.encode()) > max_bytes or squash(e["statement"]) not in squash(text) or re.search(r"(?m)^\s*(namespace|end)\s", tidy(e["closure"])):
            early[e["id"]] = Verdict(e, "return", ["gate.studied"])  # a module the gate would refuse: too large, the statement is not what it declares, its own namespace
        texts[module] = text
        facts[e["id"]] = {"module": module, "stars": stars, "cited_by": cites[e["id"]]}
    verdicts, _ran = review_fn({m: t for m, t in texts.items()}, facts)
    for e in entries:
        v = early.get(e["id"])
        if v is None:
            r = verdicts.get(e["id"]) or {"verdict": "return", "codes": ["bar.other"], "merit": []}
            v = Verdict(e, r["verdict"], list(r.get("codes") or []), list(r.get("merit") or []))
        comp.verdicts.append(v)
    acc = comp.accepted
    if not acc:
        return comp
    ids = [v.entry["id"] for v in acc]
    comp.bundle = bundle_id(target, author, ids)
    for v in acc:
        module, path = entry_module(target, v.entry["id"])
        comp.modules[path] = texts[module]
        comp.manifest_lines.append(json.dumps({
            "name": v.entry["name"], "statement": squash(v.entry["statement"]), "module": module, "target": target, "entry": v.entry["id"],
            "stars": (v.entry.get("quality") or {}).get("s"), "author": author, "bundle": comp.bundle, "toolchain": "{toolchain}", "source": SOURCE,
        }, ensure_ascii=False, sort_keys=False))
    comp.report = {
        "schema": "studied-bundle/1", "target": target, "author": author, "bundle": comp.bundle, "entries": ids,
        "preflight": {"entries": len(ids), "compiled": len(ids), "how": "each was accepted by the run's verifier (Leak IV) when it was saved; the tree builds every module in the autotag build and again in the merge queue"},
        "rerated": [{"entry": v.entry["id"], "stars": (v.entry.get("quality") or {}).get("s"), "by": BAR, "merit": v.merit} for v in acc],
        "harness": [harness_record(v.entry) for v in acc],
        "review": {"model": "praiser", "bar": BAR, "blocking": 0, "verdicts": [{"rubric": "bar", "verdict": "pass"}] + [{"rubric": c, "verdict": "pass"} for c in sorted(_ran)]},
    }
    return comp


def fill_toolchain(lines: list[str], toolchain: str) -> list[str]:
    """The manifest lines with the tree's toolchain (lean-toolchain of the checkout the PR is made against) where the composition left its placeholder."""
    return [ln.replace('"{toolchain}"', json.dumps(toolchain)) for ln in lines]
