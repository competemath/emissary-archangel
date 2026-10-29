#!/usr/bin/env python3
"""propose_cut.py — from the merge queue's rejection of a bundle to the `drop=` of its recut, without a person.

  propose_cut.py --queue-log queue-build.log --shipped TAR_OR_DIR [--shards DIR] [--prior-drop A.B,C] [--previous proposal.json] [--drop-unexplained] [--json proposal.json]

Until now a person read `explain_ejection.py`'s output and typed `drop=A.B,C` into a recut of bump-library.yml (`bundle_cut.py` leaves those modules out, and every module that
imports one). This is that step as code. It reads what `explain_ejection.py` reads (the queue's log; the shipped bundle; the original run's shard artifacts, when there are any) and
writes the list. Nothing is run but regular expressions and the import graph; there is no network, no clock and no randomness: the same inputs give the same bytes.

WHAT IT DECIDES
  * drop      the modules that have an error of their OWN, in the library's own module names (what the recut's `drop` takes). An error is explained when `explain_ejection.classify`
              puts it in A, B, C or E. D (unexplained) is not proposed unless `--drop-unexplained`: it goes to `residual` and the proposal is not `auto`.
  * cascade   per dropped module, the modules that import it, which `bundle_cut.py` cuts with it. A module whose only errors name a declaration of a module that is itself cut
              (`Unknown identifier x`, `unknown namespace X`, `object file … does not exist`, with x declared by a module it imports) is NOT proposed: it is in this list.
              Importers are found by `bundle_cut.module_graph` / `importer_closure`, the code the cut itself uses, not a second reading of the imports.
  * keep      every other module of the shipped bundle.
  * shared_causes   one missing name (a Mathlib lemma the tree lacks, a declaration the pruning cut) that several dropped modules fail on.
  * recut_drop      `--prior-drop` and `drop` together: a recut starts from the ORIGINAL run, so it must list again what the shipped bundle was already cut of.

WHAT IT DOES NOT DECIDE
  * why a module fails, beyond explain_ejection's classes; a module whose errors are all D is left to a person (`residual`), and so is an error in a file that is not in the bundle,
    in another library's namespace, or a failing target the log gives no error for. A proposal with a residual is never `auto`.
  * anything about the tree: it reads one log. It does not know a module that would fail in the NEXT queue build; the recut is built and queued again, and this runs again on its log.
  * with no `--shards`, A, B and C cannot be told (they need the factory's errors and sources): the errors that name an unknown declaration are still dropped (as `E`, which then
    also covers B), everything else is D.

THE GUARD (a proposal that fails it is written with an empty `drop`, `refused` set, and exit status 3)
  * closed     no module that is kept imports one that is cut (checked on the graph again, after the proposal is made);
  * monotone   with `--previous`, a module the earlier proposal cut stays cut (a longer log of the same build may not un-drop one);
  * not all    a cut that would leave nothing of the library is a wrong log or a wrong bundle, not a proposal.
Exit status: 0 a proposal (see `auto`), 3 refused, 2 unusable arguments.

The files are data: run it as `python3 -I`. Evidence lines are quoted from the log, which the library's own code can write to: they are scrubbed (no control characters, no `::`
workflow commands, no code fence) and cut short before they go to the JSON or to the terminal.
"""

from __future__ import annotations

import argparse
import collections
import heapq
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import bundle_cut as bc  # noqa: E402
import explain_ejection as ex  # noqa: E402
import scope_rewrite as sr  # noqa: E402
import tolerant_build as tb  # noqa: E402

EXPLAINED = {"A", "B", "C", "E"}
# Lean when an import has no .olean (the module before it failed, or was never built): the module is named in full
MISSING_OLEAN = re.compile(r"object file '[^']*' of module (?P<mod>\S+) does not exist")
# a module name cannot be passed on as `drop` (a comma list, in a workflow input, on a command line) if it holds a space, a control character or a comma (`Lib.«A,B»` is one module)
UNSAFE = re.compile(r"[\s\x00-\x1f\x7f,]")
MAX_EVIDENCE = 240
NOTHING_LEFT = "the cut would remove the whole library"


def scrub(text: str, limit: int = MAX_EVIDENCE) -> str:
    """A line of the log as evidence: it may have been written by the library's code, and goes to the runner's log and a step summary."""
    t = "".join(" " if ord(c) < 32 or ord(c) == 127 else c for c in text).strip()
    t = t.replace("::", ": :").replace("##[", "# #[").replace("```", "'''")
    return t if len(t) <= limit else t[: limit - 1] + "…"


def module_of(rel: str) -> str:
    return ".".join(tb.esc(x) for x in rel.removesuffix(".lean").split("/"))


class Err:
    __slots__ = ("ns", "rel", "line", "col", "msg", "raw")

    def __init__(self, ns: str, rel: str, line: int, col: int, msg: str, raw: str):
        self.ns, self.rel, self.line, self.col, self.msg, self.raw = ns, rel, line, col, msg, raw

    @property
    def key(self) -> tuple:
        return (self.ns, self.rel, self.line, self.col, self.msg)


def parse_errors(log_text: str) -> list[Err]:
    """Every distinct `error: Tengoku/<Ns>/<path>.lean:L:C: msg` of the log, in a fixed order. Two lines that agree on all of file, position and message are one error; two that differ
    in the message or the column are two (explain_ejection keeps the first per line, which makes its answer depend on the order of the log; this does not)."""
    seen: dict[tuple, Err] = {}
    for ln in log_text.splitlines():
        m = ex.ERR.search(ln)
        if m:
            e = Err(m.group("ns"), m.group("rel"), int(m.group("line")), int(m.group("col")), m.group("msg"), ln)
            if e.key not in seen or e.raw < seen[e.key].raw:  # the same error printed twice (another timestamp): the smallest line is the evidence, whatever the order of the log
                seen[e.key] = e
    return sorted(seen.values(), key=lambda e: e.key)


def failing_targets(log_text: str, ns: str) -> set[str]:
    """The library modules (own names) the build lists under `Some required targets logged failures:`."""
    pre = f"{ns}."
    return {m.group("mod").removeprefix(pre) for ln in log_text.splitlines() if (m := ex.TARGET.match(ln)) and m.group("mod").startswith(pre)}


def build_order(graph: dict[str, list[str]]) -> list[str]:
    """Imports before importers; ties by name; the modules of an import cycle (Lean refuses one, but a bundle is data) last, by name."""
    pending = {m: len(set(ds)) for m, ds in graph.items()}
    importers: dict[str, list[str]] = collections.defaultdict(list)
    for m, ds in graph.items():
        for d in set(ds):
            importers[d].append(m)
    heap = [m for m, n in pending.items() if n == 0]
    heapq.heapify(heap)
    out: list[str] = []
    while heap:
        m = heapq.heappop(heap)
        out.append(m)
        for i in importers[m]:
            pending[i] -= 1
            if pending[i] == 0:
                heapq.heappush(heap, i)
    return out + sorted(set(graph) - set(out))


class Reach:
    """The modules a module imports, directly or not (cycle-safe, memoised)."""

    def __init__(self, graph: dict[str, list[str]]):
        self.graph, self.memo = graph, {}

    def of(self, m: str) -> set[str]:
        if m not in self.memo:
            seen: set[str] = set()
            todo = list(self.graph.get(m, ()))
            while todo:
                d = todo.pop()
                if d not in seen:
                    seen.add(d)
                    todo.extend(self.graph.get(d, ()))
            self.memo[m] = seen
        return self.memo[m]


class Declarations:
    """What each shipped module declares, to find the module a name in an error message comes from."""

    def __init__(self, shipped: ex.Shipped, graph: dict[str, list[str]]):
        self.by_last: dict[str, set[str]] = collections.defaultdict(set)
        self.by_namespace: dict[str, set[str]] = collections.defaultdict(set)
        for rel, text in shipped.files.items():
            m = module_of(rel)
            if m not in graph:
                continue
            for n in ex.declared(text):
                self.by_last[n.rsplit(".", 1)[-1]].add(m)
                parts = n.split(".")
                for i in range(1, len(parts)):
                    self.by_namespace[".".join(parts[:i])].add(m)
            for n in ex.NAMESPACE_DECL.findall(text):
                self.by_namespace[n].add(m)

    def modules_named_by(self, msg: str, ns: str, graph: dict[str, list[str]]) -> set[str]:
        """The modules whose declarations the message says are unknown (by the last component of the name, as explain_ejection reads them), or the module it says has no object file."""
        out: set[str] = set()
        if (name := ex.unknown_name(msg)) is not None:  # identifier, constant, field or namespace, whichever way Lean quotes it
            out |= self.by_last.get(name.rsplit(".", 1)[-1], set())
            out |= self.by_namespace.get(name, set())
        if (m := MISSING_OLEAN.search(msg)) is not None:
            mod = m.group("mod").removeprefix(f"Tengoku.{ns}.")
            if mod in graph:
                out.add(mod)
        return out


def classify(e: Err, shipped: ex.Shipped, fac: ex.Factory) -> tuple[str, str]:
    cls, why = ex.classify(e.rel, e.line, e.msg, shipped, fac)
    if not fac.present and cls == "E":
        why = "(no shard artifacts: B and E cannot be told apart) " + why
    return cls, why


def propose(log_text: str, shipped: ex.Shipped, fac: ex.Factory, prior_drop: set[str] | None = None, drop_unexplained: bool = False, previous_cut: set[str] | None = None) -> dict:
    prior = set(prior_drop or ())
    out: dict = {
        "version": 1, "namespace": None, "drop": [], "recut_drop": sorted(prior), "cut": [], "reasons": {}, "keep": [], "cascade": {}, "shared_causes": [], "residual": [], "stats": {}, "auto": False,
        "refused": None,
    }  # fmt: skip
    if len(shipped.namespaces) != 1:
        out["refused"] = f"the shipped files hold {len(shipped.namespaces)} libraries ({sorted(shipped.namespaces)[:3]}): one bundle is one library" if shipped.namespaces else "no Tengoku/<Library>/… module in the shipped files"
        return out
    ns = next(iter(shipped.namespaces))
    out["namespace"] = ns
    graph = bc.module_graph(shipped.files, ns)
    if not graph:
        out["refused"] = "the shipped files hold no module"
        return out
    decls = Declarations(shipped, graph)
    reach = Reach(graph)

    def entry(module: str | None, e: Err, cls: str, why: str) -> dict:
        return {"module": module, "file": f"Tengoku/{e.ns}/{e.rel}", "line": e.line, "message": scrub(e.msg, 120), "class": cls, "why": scrub(why), "log": scrub(e.raw)}

    errors = parse_errors(log_text)
    by_module: dict[str, list[Err]] = collections.defaultdict(list)
    elsewhere: list[dict] = []  # errors in no module of this bundle: nothing a cut of the bundle can answer
    for e in errors:
        mod = module_of(e.rel)
        if e.ns != ns or mod not in graph:
            elsewhere.append(entry(None, e, "D", f"Tengoku/{e.ns}/{e.rel} is not a module of this bundle (Tengoku/{ns}/…)"))
        else:
            by_module[mod].append(e)
    # a target the build lists as failed and gives no error line for is an unexplained failure of that module
    synthetic: set[tuple] = set()
    for t in sorted(failing_targets(log_text, ns)):
        if t in graph and t not in by_module:
            e = Err(ns, "/".join(tb.split_mod(t)) + ".lean", 0, 0, "(the build lists this module as failed and the log has no error line for it)", f"- Tengoku.{ns}.{t}")
            synthetic.add(e.key)
            by_module[t].append(e)

    info: dict[tuple, tuple[str, str]] = {}
    for es in by_module.values():
        for e in es:
            info[e.key] = ("D", e.msg) if e.key in synthetic else classify(e, shipped, fac)

    # The cut, importers after what they import. A module that imports a cut one is cut with it. An error that names a declaration of a module this one imports and that is cut is
    # the cascade of that cut, not a reason of its own. Whatever else is an explained error (or any error, with drop_unexplained) is the module's own, and the module is proposed.
    # Modules the shipped bundle still has that the earlier recut's `drop` names are cut again by the next recut (it starts from the original run): they count as cut here, with their
    # importers, so that the guard below sees what the recut will really leave.
    S: set[str] = bc.importer_closure(prior, graph)
    own: dict[str, list[Err]] = {}
    unexplained: dict[str, list[Err]] = {}
    for m in build_order(graph):
        if any(d in S for d in graph[m]):
            S.add(m)
        can_drop = sr.parts_of(m) is not None and not UNSAFE.search(m)  # the name is passed on as `drop`
        for e in by_module.get(m, ()):
            if (decls.modules_named_by(e.msg, ns, graph) - {m}) & S & reach.of(m):
                continue
            if info[e.key][0] in EXPLAINED or drop_unexplained:
                if can_drop:
                    own.setdefault(m, []).append(e)
                else:  # a person has to cut it: the name cannot travel in a comma list
                    info[e.key] = (info[e.key][0], info[e.key][1] + " [not proposed: the module's name cannot be passed as `drop` (a space, a control character or a comma)]")
                    unexplained.setdefault(m, []).append(e)
            else:
                unexplained.setdefault(m, []).append(e)
        if m in own:
            S.add(m)
    roots = sorted(own)
    cut = bc.importer_closure(S, graph)
    residual = list(elsewhere)
    for m, es in sorted(unexplained.items()):
        if m not in cut:  # a module that goes with a cut one: its own failure is moot
            residual += [entry(m, e, *info[e.key]) for e in es]

    out["drop"] = roots
    out["recut_drop"] = sorted(prior | set(roots))
    out["cut"] = sorted(cut)
    out["keep"] = sorted(set(graph) - cut)
    out["cascade"] = {r: sorted(bc.importer_closure({r}, graph) - {r}) for r in roots}
    out["reasons"] = {r: f"{info[own[r][0].key][0]}: {scrub(info[own[r][0].key][1])} | {scrub(own[r][0].raw)}" for r in roots}
    causes: dict[tuple[str, str], set[str]] = collections.defaultdict(set)
    for r in roots:
        for e in own[r]:
            n = ex.unknown_name(e.msg)
            if n and info[e.key][0] in ("B", "E"):
                causes[(info[e.key][0], n)].add(r)
    out["shared_causes"] = [{"class": c, "cause": f"`{scrub(n, 120)}` is unknown", "modules": sorted(ms)} for (c, n), ms in sorted(causes.items()) if len(ms) > 1]
    out["residual"] = sorted(residual, key=lambda r: (r["module"] or "", r["file"], r["line"], r["message"]))
    out["stats"] = {
        "modules": len(graph),
        "errors": len(errors),
        "error_classes": dict(sorted(collections.Counter(c for c, _ in info.values()).items())),
        "roots": len(roots),
        "cut": len(cut),
        "kept": len(graph) - len(cut),
        "factory": fac.present,
    }
    problem = guard(out, graph, previous_cut)
    if problem:
        # nothing is proposed; what would have been is in the residual, for a person
        out["residual"] += [entry(m, e, *info[e.key]) for m, es in sorted(own.items()) for e in es]
        out["residual"].append({"module": None, "file": "", "line": 0, "message": problem, "class": "D", "why": "refused by the guard", "log": ""})
        out["refused"] = problem
        out["drop"], out["recut_drop"], out["cascade"], out["reasons"], out["shared_causes"] = [], sorted(prior), {}, {}, []
        out["keep"], out["cut"] = sorted(graph), []
        return out
    out["auto"] = bool(roots) and not out["residual"]
    return out


def guard(p: dict, graph: dict[str, list[str]], previous_cut: set[str] | None) -> str | None:
    """None when the proposal may be used; else why not. Closed: re-derived from the graph, not trusted from how the cut was made."""
    cut, keep = set(p["cut"]), set(p["keep"])
    if cut | keep != set(graph) or cut & keep:
        return "internal: cut and keep are not a partition of the bundle's modules"
    if not set(p["drop"]) <= cut:
        return "internal: a proposed module is not in the cut"
    if bc.importer_closure(cut, graph) != cut:
        return "not closed: a module that is kept imports one that is cut"
    for m in sorted(keep):
        if any(d in cut for d in graph[m]):
            return f"not closed: {m} is kept and imports a cut module"
    if previous_cut and not previous_cut <= cut:
        return f"not monotone: the earlier proposal cut {len(previous_cut - cut)} module(s) this one keeps ({sorted(previous_cut - cut)[:3]})"
    if cut and not keep:
        return NOTHING_LEFT
    return None


def render(p: dict) -> str:
    if p["refused"]:
        head = f"REFUSED: {p['refused']}"
    else:
        head = f"{'AUTO ' if p['auto'] else 'NOT AUTO '}proposal: drop {len(p['drop'])} module(s); the cut is {len(p['cut'])} of {len(p['cut']) + len(p['keep'])}; {len(p['residual'])} residual error(s)"
    out = [head]
    if p["drop"]:
        out.append("drop=" + ",".join(p["recut_drop"]))
    for r in p["drop"][:40]:
        extra = f" (+{len(p['cascade'][r])} importer(s))" if p["cascade"][r] else ""
        out.append(f"  {r}{extra}: {p['reasons'][r]}")
    if len(p["drop"]) > 40:
        out.append(f"  … and {len(p['drop']) - 40} more")
    for c in p["shared_causes"][:10]:
        out.append(f"  one cause, {len(c['modules'])} modules: {c['cause']} ({c['class']}): {', '.join(c['modules'][:5])}")
    for r in p["residual"][:20]:
        out.append(f"  RESIDUAL {r['module'] or r['file']} line {r['line']}: {r['message']} | {r['why']}")
    return "\n".join(out)


def names(arg: str) -> set[str]:
    out = {m.strip() for m in arg.split(",") if m.strip()}
    bad = sorted(m for m in out if sr.parts_of(m) is None or UNSAFE.search(m))
    if bad:
        sys.exit(f"not module names: {bad[:5]}")
    return out


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--queue-log", required=True)
    ap.add_argument("--shipped", required=True, help="the bundle that was queued: a tar (the whole bundle's, or a part's) or a directory holding Tengoku/<Ns>/…")
    ap.add_argument("--shards", default="", help="the shard artifacts of the original bump run (DIR/shard-*/shard-pack/{errors.log,src/}); without them A, B and C cannot be told")
    ap.add_argument("--prior-drop", default="", help="the `drop` of the recut that made the shipped bundle: the next recut starts from the original run and must list it again")
    ap.add_argument("--previous", default="", help="an earlier proposal.json of the same build: what it cut must stay cut")
    ap.add_argument("--drop-unexplained", action="store_true", help="also propose the modules whose errors are class D (nothing explains them); default: they are the residual and the proposal is not `auto`")
    ap.add_argument("--json", default="")
    ap.add_argument("--github-output", default="", help="append `go=true|false` (a complete proposal: nothing left over, something to drop, not refused) and `drop=<recut_drop>` to this file (Actions' $GITHUB_OUTPUT)")
    a = ap.parse_args(argv)
    prior = names(a.prior_drop)
    previous = set(json.loads(Path(a.previous).read_text())["cut"]) if a.previous else None
    p = propose(
        Path(a.queue_log).read_text(errors="replace"),
        ex.Shipped(Path(a.shipped)),
        ex.Factory(Path(a.shards) if a.shards else None),
        prior,
        a.drop_unexplained,
        previous,
    )
    print(render(p))
    if a.json:
        Path(a.json).write_text(json.dumps(p, indent=1, ensure_ascii=False) + "\n")
    if a.github_output:
        go = p["auto"] and not p["refused"]
        # one line, no whitespace: a module name is checked to be passable as `drop` before it is proposed, and again here, because this is what reaches another workflow
        if not all(sr.parts_of(m) is not None and not UNSAFE.search(m) for m in p["recut_drop"]):
            sys.exit("unsafe module name in the drop list")
        with Path(a.github_output).open("a", encoding="utf-8") as f:
            f.write(f"go={'true' if go else 'false'}\ndrop={','.join(p['recut_drop']) if go else ''}\n")
    return 3 if p["refused"] else 0


if __name__ == "__main__":
    sys.exit(main())
