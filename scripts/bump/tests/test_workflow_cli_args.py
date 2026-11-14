"""Every command line a workflow passes to a bump script is one that script's own argument parser accepts.

The real case: the first recut on main after #178 (prime-gaps-186, bump-sharded run 43263333838, 12 Nov 2026) stopped in compose at
"The run this one recuts built this library": the step calls `fill_from.py --repo R --key K --check-library RUN --library-from emissary`, and
fill_from.py required --shards and --work for every mode. The step's own test (test_lane_chain.py) only read the step's text, so a command line
the script refuses passed the suite; flt-anthropic's bundle recuts through the same step.

Invariants:
  1. CLASS: every invocation of scripts/bump/X.py in every workflow (X has an argparse main) parses with X's parser, as the shell would pass it
     (expressions and variables become a value, arrays expanded to nothing, the line cut at the first shell operator). The parse is run for real
     (argparse.ArgumentParser.parse_args/parse_known_args are wrapped: the real parse runs, then the test stops the script before it does anything).
     Every invocation is accounted for: parsed, or a script without an argparse main (named); none is skipped silently.
  2. fill_from.py's modes: --check-library takes no --shards/--work and runs through to the check; a fill or a promotion without them is an error.
  3. Mutant: fill_from.py with --shards/--work required again fails invariant 1 on the real workflows (the bug as it was).
"""

import argparse
import contextlib
import importlib
import inspect
import io
import json
import re
import shlex
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

import yaml

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
ROOT = Path(__file__).resolve().parents[3]
WORKFLOWS = sorted([*(ROOT / ".github" / "workflows").glob("*.yml"), *(ROOT / ".github" / "workflows").glob("*.yaml")])  # both spellings GitHub runs (cubic, #183)

CALL = re.compile(r"python3?\s+(?:-[A-Za-z]+\s+)*(?:\S*/)?scripts/bump/([A-Za-z0-9_]+)\.py\b([^\n]*)")  # gate2_batch.py and the like too (cubic, #183)
OPERATORS = {"|", "||", "&&", ";", ">", ">>", "<", "&", ">&", "<<", "(", ")", ")>>", "2>&1", "1>&2", ">&2"}


class Parsed(Exception):
    pass


def argparse_main(name: str) -> bool:
    text = (HERE / f"{name}.py").read_text()
    return "ArgumentParser" in text and re.search(r"^def main\(", text, re.M) is not None


def unresolved(rest: str) -> str | None:
    """why the shell's arguments cannot be known from the text alone (None: they can): an array, an unquoted variable that word-splits, arithmetic,
    or an unquoted command substitution, each built by the lines before it"""
    if re.search(r"\$\{[A-Za-z_][A-Za-z0-9_]*\[@\]\}", rest):
        return "an array"
    if "$((" in rest:
        return "arithmetic"
    bare = re.sub(r'"(?:[^"\\]|\\.)*"', '""', rest)  # what is outside double quotes
    if re.search(r"\$\(", bare):
        return "an unquoted command substitution"
    if re.search(r"(?<![\w])\$\{?[A-Za-z_][A-Za-z0-9_]*\}?", bare):
        return "an unquoted variable"
    return None


def argv_of(rest: str) -> list[str]:
    """the arguments the shell passes, from the text after `X.py` on one (continuation-joined) line; a value the step computes becomes 7"""
    rest = re.sub(r'"?\$\{[A-Za-z_][A-Za-z0-9_]*\[@\]\}"?', " ", rest)  # "${arr[@]}": an array the step builds, taken as empty
    rest = re.sub(r"\$\{\{[^}]*\}\}", "7", rest)  # workflow expressions
    rest = re.sub(r"\$\((?:[^()]|\([^()]*\))*\)", "7", rest)  # $(...), one level of nesting
    rest = re.sub(r"\$\{?[A-Za-z_][A-Za-z0-9_]*\}?", "7", rest)  # $VAR, ${VAR}
    rest = re.sub(r"(?<![\w-])[0-9]*>&[0-9]+", " ", rest)  # 2>&1, >&2
    lex = shlex.shlex(rest, posix=True, punctuation_chars=True)
    lex.whitespace_split = True
    out: list[str] = []
    for tok in lex:
        if tok in OPERATORS or tok.startswith((">", "<", "|", "&", ";", ")")):
            break
        out.append(tok)
    return out


def invocations() -> list[tuple[str, str, str, list[str], str | None]]:
    """(workflow, step name, script, argv, why argv cannot be known or None) for every call of a bump script"""
    out = []
    for wf in WORKFLOWS:
        jobs = (yaml.safe_load(wf.read_text()) or {}).get("jobs", {})
        for job in jobs.values():
            for step in job.get("steps", []) or []:
                run = step.get("run")
                if not isinstance(run, str):
                    continue
                text = re.sub(r"\\\n\s*", " ", run)
                for line in text.splitlines():
                    if line.lstrip().startswith("#"):
                        continue
                    for m in CALL.finditer(line):
                        out.append((wf.name, step.get("name", "?"), m.group(1), argv_of(m.group(2)), unresolved(m.group(2))))
    return out


def parse_only(name: str, argv: list[str], parse=None):
    """run X.main() with argv until its parser has parsed (for real); returns the namespace, or the SystemExit the parser raised.

    The script's own parse is the OUTERMOST parse_args/parse_known_args call (a subparser parses inside it): it is stopped there by depth, never by
    the parser's prog, which Python 3.14 takes from how __main__ was started ("python3 -m unittest" under the test runner: the bump-tests job of #183)."""
    mod = importlib.import_module(name)
    real_parse, real_known = argparse.ArgumentParser.parse_args, argparse.ArgumentParser.parse_known_args
    depth = [0]

    def stop(self, args=None, namespace=None):
        outer = depth[0] == 0
        depth[0] += 1
        try:
            ns = (parse or real_parse)(self, args, namespace)
        finally:
            depth[0] -= 1
        if outer:
            raise Parsed(ns)
        return ns

    def stop_known(self, args=None, namespace=None):
        outer = depth[0] == 0
        depth[0] += 1
        try:
            ns, extra = real_known(self, args, namespace)
        finally:
            depth[0] -= 1
        if outer and not extra:
            raise Parsed(ns)
        return ns, extra

    err = io.StringIO()
    with mock.patch.object(argparse.ArgumentParser, "parse_args", stop), mock.patch.object(argparse.ArgumentParser, "parse_known_args", stop_known), \
            mock.patch.object(sys, "argv", [f"scripts/bump/{name}.py", *argv]), contextlib.redirect_stderr(err), contextlib.redirect_stdout(io.StringIO()):
        try:
            params = inspect.signature(mod.main).parameters
            mod.main(argv) if params and next(iter(params.values())).default is inspect.Parameter.empty else mod.main()  # main(argv) or main()
        except Parsed as p:
            return p.args[0]
        except SystemExit as e:
            return SystemExit(f"{e.code}: {err.getvalue().strip()[-300:]}")
    return SystemExit("main() returned without parsing its arguments")


class EveryCallParses(unittest.TestCase):
    # the calls whose arguments the step builds in the lines before (named: a new one is a decision, never a silent skip). Those whose only
    # unknown is an array (optional flags the step adds) are still parsed with the array empty.
    UNRESOLVED = sorted([
        ("bump-autocut.yml", "propose_cut", "an array"), ("bump-library.yml", "autonames", "an unquoted variable"),
        ("bump-library.yml", "bundle_layers", "an unquoted variable"), ("bump-library.yml", "bundle_rehead", "an unquoted variable"),
        ("bump-library.yml", "canonicalise_bundle", "an unquoted variable"), ("bump-library.yml", "gate2_driver", "an unquoted variable"),
        ("bump-library.yml", "scope_rewrite", "an unquoted variable"), ("bump-shard.yml", "gate2_driver", "an unquoted command substitution"),
        ("bump-pickup.yml", "bump_pickup", "an unquoted command substitution"), ("setup-pickup.yml", "setup_pickup", "an unquoted command substitution"), ("waves-watch.yml", "waves_watch", "an unquoted command substitution"), ("bump-shard.yml", "build_rounds", "arithmetic"),
        ("bump-sharded.yml", "bundle_layers", "an unquoted variable"), ("bump-sharded.yml", "canonicalise_bundle", "an unquoted command substitution"),
        ("bump-sharded.yml", "tree_dups", "an array"), ("bump-sharded.yml", "tree_dups", "an array"), ("bump-sharded.yml", "tree_dups", "an array"),
        ("bump-sharded.yml", "tree_dups", "an unquoted command substitution"), ("bump-sharded.yml", "tree_repair", "an array"),
        ("bump-sharded.yml", "tree_repair", "an unquoted variable"), ("bump-sharded.yml", "tree_verify", "an array"), ("bump-sharded.yml", "tree_verify", "an array"),
        ("bump-sharded.yml", "tree_verify", "an array"), ("bump-sharded.yml", "tree_verify", "an array"), ("bump-waves.yml", "lane_reuse", "an unquoted variable"),
        ("intake-open.yml", "intake_open", "an array"), ("notation-census.yml", "notation_census", "an array"), ("notation-census.yml", "scope_rewrite", "an unquoted variable"),
    ])
    BY_HAND = {"adapters", "bundle", "bundle_tar", "engine", "gate2_batch", "import_graph", "in_tree", "lake_fetch", "leakscan_args", "ledger_rows", "link_srcdir", "mine_moves",
               "plan_inputs", "portfolio", "records", "rerun_killed", "shard_pack", "tentative_files"}

    def test_every_invocation(self):
        calls = invocations()
        self.assertGreaterEqual(len(calls), 100, "the workflows call bump scripts 112 times (12 Nov 2026); far fewer means the scan broke")
        parsed, left, n_by_hand, by_hand, unresolved, bad = 0, 0, 0, set(), [], []
        for wf, step, name, argv, why in calls:
            if not argparse_main(name):
                by_hand.add(name)
                n_by_hand += 1
                continue
            if why:
                unresolved.append((wf, name, why))
                if why != "an array":
                    left += 1
                    continue
            got = parse_only(name, argv)
            if isinstance(got, SystemExit):
                if why:  # an array the step fills may hold a required argument: that call stays unresolved, not wrong
                    left += 1
                    continue
                bad.append(f"{wf} / {step}: {name}.py {' '.join(argv)} -> {got}")
            else:
                parsed += 1
        self.assertEqual(bad, [])
        self.assertEqual(sorted(unresolved), self.UNRESOLVED)
        self.assertEqual(by_hand, self.BY_HAND)
        self.assertGreaterEqual(parsed, 40)
        self.assertEqual(len(calls), parsed + left + n_by_hand)  # every call is parsed, named as unresolved, or a script read by hand

    def test_the_stop_does_not_depend_on_the_program_name(self):
        # Python 3.14 names the parser after how __main__ was started: under `python3 -m unittest` (the bump-tests job) every script's parser is
        # "python3 -m unittest". #183's first version stopped a script by that name, so on 3.14 the scripts ran for real and the job failed.
        real_init = argparse.ArgumentParser.__init__

        def as_on_314(self, *a, **k):
            real_init(self, *a, **k)
            self.prog = "python3 -m unittest"

        argv = ["--repo", "competemath/emissary-archangel", "--key", "prime-gaps-186", "--check-library", "42549840777", "--library-from", "emissary"]
        with mock.patch.object(argparse.ArgumentParser, "__init__", as_on_314):
            ns = parse_only("fill_from", argv)
            self.assertNotIsInstance(ns, SystemExit, ns)
            self.assertEqual(ns.check_library, "42549840777")
            # a script with subcommands: the outer parse is the one stopped, the subparser's runs inside it
            sub = parse_only("tree_dups", ["after-verdict", "--fp-before", "a", "--fp-after", "b", "--candidates", "c", "--dups", "d", "--new", "n", "--tree", "t", "--log2", "l", "--out", "o"])
            self.assertNotIsInstance(sub, SystemExit, sub)

    def test_the_real_failing_call(self):
        # bump-sharded run 43263333838, compose, as it ran
        argv = ["--repo", "competemath/emissary-archangel", "--key", "prime-gaps-186", "--check-library", "42549840777", "--library-from", "emissary"]
        ns = parse_only("fill_from", argv)
        self.assertNotIsInstance(ns, SystemExit, ns)
        self.assertEqual((ns.check_library, ns.library_from, ns.shards, ns.work), ("42549840777", "emissary", "", ""))

    def test_the_step_text_gives_that_call(self):
        calls = [c for c in invocations() if c[0] == "bump-sharded.yml" and c[1] == "The run this one recuts built this library"]
        self.assertEqual(len(calls), 1)
        self.assertEqual(calls[0][2:], ("fill_from", ["--repo", "7", "--key", "7", "--check-library", "7", "--library-from", "emissary"], None))

    def test_mutant_the_bug_as_it_was(self):
        import fill_from

        src = (HERE / "fill_from.py").read_text()
        self.assertIn('ap.add_argument("--shards", default="")', src)
        real_parse = argparse.ArgumentParser.parse_args

        def required_again(self, args=None, namespace=None):
            for act in self._actions:
                if act.dest in ("shards", "work"):  # only fill_from.py's parser has both
                    act.required = True
            return real_parse(self, args, namespace)

        bad = [argv for wf, step, name, argv, why in invocations() if name == "fill_from" and isinstance(parse_only("fill_from", argv, parse=required_again), SystemExit)]
        self.assertEqual(len(bad), 1)  # exactly the recut's check
        self.assertIn("--check-library", bad[0])
        self.assertTrue(fill_from)


class FillFromModes(unittest.TestCase):
    def run_main(self, argv, **patches):
        import fill_from

        err, out = io.StringIO(), io.StringIO()
        with mock.patch.object(sys, "argv", ["fill_from.py", *argv]), contextlib.redirect_stderr(err), contextlib.redirect_stdout(out), \
                contextlib.ExitStack() as st:
            for k, v in patches.items():
                st.enter_context(mock.patch.object(fill_from, k, v))
            try:
                fill_from.main()
                return 0, out.getvalue(), err.getvalue()
            except SystemExit as e:
                return e.code, out.getvalue(), err.getvalue()

    def test_check_library_runs_through_without_shards_or_work(self):
        with tempfile.TemporaryDirectory() as d:
            base = Path(d)
            (base / "data" / "exports" / "prime-gaps-186").mkdir(parents=True)
            (base / "data" / "exports" / "prime-gaps-186" / "setup.ci.json").write_text("{}")
            (base / "sources.json").write_text(json.dumps({"sources": {}}))
            seen = []
            with mock.patch("lane_reuse.library_identity", return_value={"id": "x"}):
                code, out, err = self.run_main(["--repo", "competemath/emissary-archangel", "--key", "prime-gaps-186", "--check-library", "42549840777", "--library-from", d],
                                               check_library=lambda repo, key, run, lib: seen.append((repo, key, run, lib)))
            self.assertEqual(code, 0, err)
            self.assertIn("run 42549840777 built this library", out)
            self.assertEqual(seen[-1], ("competemath/emissary-archangel", "prime-gaps-186", "42549840777", {"id": "x"}))

    def test_fill_and_promote_still_need_them(self):
        for argv in (["--runs", "43146942669"], ["--promote-from", "43146942669"], ["--runs", "43146942669", "--shards", "s"], ["--promote-from", "1", "--work", "w"],
                     ["--promote-from", "43146942669", "--check-library", "42549840777", "--library-from", "emissary"]):  # a promotion writes: never exempt (cubic, #183)
            code, out, err = self.run_main(["--repo", "r", "--key", "k", *argv])
            self.assertEqual(code, 2, argv)
            self.assertIn("--shards and --work are required for a fill or a promotion", err)


if __name__ == "__main__":
    unittest.main()
