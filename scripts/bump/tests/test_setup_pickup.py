"""Which newly registered library the setup pickup sets up (setup_pickup.py), and with which tree branch, on the repository's real history (fixtures/real-setup-pickup.json.gz, fetched 13 Nov 2026
02:47 UTC: the whole `git log -p` of sources.json (174 libraries, 3 removed), the 147 real setup records, 176 real runs of setup-auto.yml and setup-sharded.yml since 30 Oct, the 5 latest real
`records:` pull requests of the tree with their files, and whether each of their 26 record files is on the tree's main) and on 5,000 random states against an oracle written apart.

The real case: batch 6 (ck-hopf-formalization, nlalib, lean-eval-pi-succ-sphere-n-mulequiv-zmod-two, rankamplificationtotient) was registered at 01:48 and set up by hand at 02:31 (four setup-auto
dispatches with tengoku_ref=content/fatex-libraries-batch-6, the branch of competemath/tengoku#789).

Invariants: at most MAX_STARTS libraries start in a run (the first with bump_pickup.NEED_FREE runners free, each further one with PER_START more), decide() names the first; never one registered before FIRST_REGISTER or outside the window, or no longer in sources.json; never one with a setup record; never one with a real setup
started at or after its registration (a dry run of setup-auto does not count; a setup-sharded run does); the tree branch is the one open records pull request of the tree repository holding ALL the
library's record files, '' when they are on main, and nothing starts when no such pull request or several exist or it is a fork's; nothing starts with too few free runners; the one registered first
starts first. Mutants (each must fail a check): dry runs counted, attempts ignored, the window ignored, a fork's branch taken, any indentation read as a registration, a partial set of record files taken."""

import gzip
import inspect
import json
import random
import subprocess
import sys
import unittest
from pathlib import Path
from unittest import mock

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))

import bump_pickup as bp  # noqa: E402
import setup_pickup as sp  # noqa: E402
import yaml  # noqa: E402

R = json.loads(gzip.open(HERE / "fixtures" / "real-setup-pickup.json.gz").read())
NOW = sp._epoch(R["fetched"])
TREE = "competemath/tengoku"
BATCH6 = ["ck-hopf-formalization", "lean-eval-pi-succ-sphere-n-mulequiv-zmod-two", "nlalib", "rankamplificationtotient"]
OPEN = [p for p in R["records_prs"] if p["number"] == 789]  # the only one of the five open when fetched
WF = HERE.parents[2] / ".github" / "workflows"


def mutant(name, old, new):
    """the function `name` (as setup_pickup.py has it) with `old` replaced by `new` in its source (which must hold `old` once)"""
    fn = getattr(sp, name)
    src = inspect.getsource(fn)
    if src.count(old) != 1:
        raise AssertionError(f"{name}: {old!r} is not in it once")
    ns = dict(vars(sys.modules[fn.__module__]))  # the module that defines it (tree_records for the records rules)
    exec(src.replace(old, new), ns)
    return ns[name]


MAIN = {f for f, v in R["on_main"].items() if v}  # the real record files on the tree's main when fetched


def refs_for(keys, prs=OPEN, main=None):
    main = MAIN if main is None else main
    return {k: sp.records_ref(k, R["sources"][k], main, prs, TREE, rule=sp.setup_holds) for k in keys}


def run_pickup(runs, now=NOW, prs=OPEN, free=20, mod=sp):
    reg = mod.registered(R["log"])
    since = mod.window_start(now)
    keys = mod.pending(reg, R["sources"], set(R["set_up"]), mod.attempts(runs), since)
    return keys, mod.decide(keys, refs_for(keys, prs), free)


def without_batch6(runs):
    return [r for r in runs if not any(f" {k} (" in r["displayTitle"] for k in BATCH6)]


class RealRegistry(unittest.TestCase):
    def setUp(self):
        self.reg = sp.registered(R["log"])

    def test_every_library_has_its_registration(self):
        self.assertEqual(len(R["sources"]), 174)
        self.assertEqual(set(R["sources"]) - set(self.reg), set())
        # read off the entry lines only: what else was registered once is exactly what was removed since
        self.assertEqual(set(self.reg) - set(R["sources"]), {"lean-wasm", "software-foundations-lean", "riemann-roch-function-fields"})

    def test_batch6_is_registered_at_its_commit(self):
        for k in BATCH6:
            self.assertEqual(self.reg[k], 1794534508, k)  # f91e13c3, 13 Nov 01:48 UTC

    def test_the_old_libraries_without_a_setup_are_before_the_cut(self):
        old = [k for k in R["sources"] if k not in R["set_up"] and k not in BATCH6]
        self.assertEqual(len(old), 23)
        self.assertTrue(all(self.reg[k] < sp.FIRST_REGISTER for k in old))

    def test_nested_objects_and_the_top_level_are_not_libraries(self):
        self.assertIn('+      "setup": {', R["log"])
        self.assertIn('+  "sources": {', R["log"])
        self.assertNotIn("setup", self.reg)
        self.assertNotIn("sources", self.reg)

    def test_mutant_any_indentation_is_caught(self):
        loose = mock.patch.object(sp, "ENTRY", sp.re.compile(r'^\+\s+"([a-z0-9][a-z0-9-]*)": \{'))
        with loose:
            self.assertIn("setup", sp.registered(R["log"]))


class RealPast(unittest.TestCase):
    def test_the_real_present_starts_nothing(self):
        """batch 6 was set up by hand at 02:31: the day this is switched on, nothing may start a second setup"""
        keys, (key, ref, notes) = run_pickup(R["runs"])
        self.assertEqual(keys, [])
        self.assertIsNone(key)
        self.assertEqual(notes, [])

    def test_batch6_without_its_hand_setups_is_picked_with_its_branch(self):
        keys, (key, ref, notes) = run_pickup(without_batch6(R["runs"]))
        self.assertEqual(keys, BATCH6)  # registered together: by name
        self.assertEqual((key, ref), ("ck-hopf-formalization", "content/fatex-libraries-batch-6"))
        self.assertEqual(notes, [f"{k}: waits for the next run" for k in BATCH6[1:]])  # decide is the one-start view; plan starts all four (SeveralStarts)

    def test_the_hand_setups_were_what_the_pickup_would_have_started(self):
        """each real setup-auto dispatch of batch 6 is exactly dispatch_args for that library and branch"""
        args = sp.dispatch_args("nlalib", "content/fatex-libraries-batch-6", "competemath/emissary-archangel")
        self.assertEqual(args[:9], ["gh", "workflow", "run", "setup-auto.yml", "-R", "competemath/emissary-archangel", "--ref", "main", "-f"])
        self.assertEqual(args[9:], ["key=nlalib", "-f", "tengoku_ref=content/fatex-libraries-batch-6"])

    def test_one_at_a_time_in_order(self):
        runs = without_batch6(R["runs"])
        started = []
        for i in range(5):
            _, (key, ref, _) = run_pickup(runs, now=NOW + 60 * i)
            if key is None:
                break
            started.append(key)
            runs = runs + [{"displayTitle": f"setup-auto {key} (auto)", "createdAt": f"2026-11-13T03:{10 + i:02d}:00Z"}]
        self.assertEqual(started, BATCH6)

    def test_a_dry_run_is_not_a_setup_but_a_staged_one_is(self):
        dry = without_batch6(R["runs"]) + [{"displayTitle": f"setup-auto {k} (auto{sp.DRY_MARK})", "createdAt": "2026-11-13T02:29:00Z"} for k in BATCH6]
        self.assertEqual(run_pickup(dry)[0], BATCH6)
        sharded = without_batch6(R["runs"]) + [{"displayTitle": "setup-sharded nlalib (round 1)", "createdAt": "2026-11-13T02:31:00Z"}]
        self.assertNotIn("nlalib", run_pickup(sharded)[0])

    def test_mutant_dry_runs_counted(self):
        dry = without_batch6(R["runs"]) + [{"displayTitle": f"setup-auto {k} (auto{sp.DRY_MARK})", "createdAt": "2026-11-13T02:29:00Z"} for k in BATCH6]
        with mock.patch.object(sp, "DRY_MARK", "\0never"):
            self.assertEqual(run_pickup(dry)[0], [])

    def test_mutant_attempts_ignored(self):
        with mock.patch.object(sp, "attempts", lambda runs: {}):
            self.assertEqual(run_pickup(R["runs"])[0], BATCH6)  # the real present would start batch 6 a second time

    def test_mutant_window_ignored(self):
        with mock.patch.object(sp, "window_start", lambda now: 0):
            keys = run_pickup(R["runs"])[0]
        # the September libraries left alone on purpose, but for the two a person tried to set up again (setup-auto runs since 30 Oct, no record): a failed setup is never retried by this
        old = {k for k in R["sources"] if k not in R["set_up"] and k not in BATCH6}
        self.assertEqual(set(keys), old - {"classfieldtheory", "frenzymath-reap"})
        self.assertEqual(len(keys), 21)

    def test_the_window_closes(self):
        keys = run_pickup(without_batch6(R["runs"]), now=1794534508 + sp.WINDOW_DAYS * 86400 + 1)[0]
        self.assertEqual(keys, [])

    def test_too_few_runners(self):
        _, (key, ref, notes) = run_pickup(without_batch6(R["runs"]), free=bp.NEED_FREE - 1)
        self.assertIsNone(key)
        self.assertEqual(notes, [f"4 ready, {bp.NEED_FREE - 1} runners free of the {bp.NEED_FREE} needed: next run"])


class RealRecords(unittest.TestCase):
    def test_every_real_records_pull_request_gives_its_branch(self):
        n = 0
        for p in R["records_prs"]:
            for f in p["files"]:
                k = f.removeprefix("data/tentative/").removesuffix(".jsonl")
                if k not in R["sources"]:
                    continue
                n += 1
                src = R["sources"][k]
                own = set(sp.tentative_files(k, src))
                for rule in (sp.setup_holds, sp.holds):
                    self.assertEqual(sp.records_ref(k, src, set(), [p], TREE, rule)[0], p["branch"], k)
                    self.assertEqual(sp.records_ref(k, src, own, [p], TREE, rule)[0], "", k)  # main first
                    self.assertIsNone(sp.records_ref(k, src, set(), [dict(p, repo="someone/tengoku")], TREE, rule)[0], k)
                    self.assertIsNone(sp.records_ref(k, src, set(), [p, dict(p, number=p["number"] + 1)], TREE, rule)[0], k)
                    self.assertIsNone(sp.records_ref(k, src, set(), [], TREE, rule)[0], k)
        self.assertEqual(n, 25)

    def test_openai_math_listed_in_its_directory(self):
        p = next(p for p in R["records_prs"] if p["number"] == 612)  # openai-math lists openai-math/003.jsonl: a file of its directory
        self.assertEqual(sp.records_ref("openai-math", R["sources"]["openai-math"], set(), [p], TREE)[0], p["branch"])

    def test_merged_records_are_read_from_main(self):
        for k in ("abel-formalization", "etingofrepresentationtheory", "lean-operads"):  # competemath/tengoku#777, merged
            self.assertEqual(refs_for([k], prs=[])[k][0], "", k)
        for k in BATCH6:
            self.assertEqual(refs_for([k], prs=[])[k][0], None, k)

    def test_a_library_listing_several_files_needs_them_all(self):
        """flt-anthropic's real listing (three files outside its directory): a pull request with one of them, and main without the others, is not enough"""
        k, src = "flt-anthropic", R["sources"]["flt-anthropic"]
        files = sp.tentative_files(k, src)
        self.assertEqual(len(files), 3)
        p = {"number": 1, "branch": "content/x", "repo": TREE, "files": files[:1]}
        for rule in (sp.setup_holds, sp.holds):
            self.assertIsNone(sp.records_ref(k, src, set(), [p], TREE, rule)[0])
            self.assertEqual(sp.records_ref(k, src, set(files[1:]), [p], TREE, rule)[0], "content/x")  # the rest on main: the branch has them all

    def test_mutant_a_partial_set_is_caught(self):
        k, src = "flt-anthropic", R["sources"]["flt-anthropic"]
        files = sp.tentative_files(k, src)
        p = {"number": 1, "branch": "content/x", "repo": TREE, "files": files[:1]}
        partial = mutant("holds", "all(f in present for f in need)", "any(f in present for f in need)")
        self.assertIsNotNone(sp.records_ref(k, src, set(), [p], TREE, partial)[0])

    def test_mutant_a_fork_taken_is_caught(self):
        fork = dict(OPEN[0], repo="someone/tengoku")
        taken = mutant("records_ref", 'p["repo"] == tree and ', "")
        self.assertEqual(taken("nlalib", R["sources"]["nlalib"], set(), [fork], TREE)[0], OPEN[0]["branch"])
        self.assertIsNone(sp.records_ref("nlalib", R["sources"]["nlalib"], set(), [fork], TREE)[0])

    def test_a_branch_setup_auto_refuses_is_never_given(self):
        for bad in ("a b", "x;rm", "$(id)", "a`b", ""):
            p = dict(OPEN[0], branch=bad)
            self.assertIsNone(refs_for(["nlalib"], prs=[p])["nlalib"][0], bad)
            if bad:
                with self.assertRaises(ValueError):
                    sp.dispatch_args("nlalib", bad, "r/r")

    def test_the_rule_for_record_files_is_setup_autos(self):
        text = (WF / "setup-auto.yml").read_text()
        self.assertIn("print(' '.join('data/tentative/' + f for f in s.get('tentative', [os.environ['KEY'] + '.jsonl'])))", text)
        self.assertEqual(sp.tentative_files("tauceti", R["sources"]["tauceti"]), ["data/tentative/tauceti/project-001.jsonl", "data/tentative/tauceti/project-002.jsonl"])


class TheDirectory(unittest.TestCase):
    """cubic on #187: the bump also reads data/tentative/<key>/*.jsonl (tentative_files.globs), the setup does not (setup-auto's sparse checkout is the listed files)"""

    DIR_ONLY = {"number": 9, "branch": "content/d", "repo": TREE, "files": ["data/tentative/newlib/part-1.jsonl", "data/tentative/newlib/part-2.jsonl"]}

    def test_a_bump_takes_records_only_in_the_directory(self):
        self.assertEqual(sp.records_ref("newlib", {}, set(), [self.DIR_ONLY], TREE, sp.holds)[0], "content/d")
        self.assertEqual(sp.records_ref("newlib", {}, set(self.DIR_ONLY["files"]), [], TREE, sp.holds)[0], "")

    def test_a_setup_does_not(self):
        self.assertIsNone(sp.records_ref("newlib", {}, set(), [self.DIR_ONLY], TREE, sp.setup_holds)[0])

    def test_nested_and_other_files_are_not_the_directory(self):
        for f in ("data/tentative/newlib/a/b.jsonl", "data/tentative/newlib/x.json", "data/tentative/newlibx/a.jsonl", "data/tentative/newlib.json"):
            p = dict(self.DIR_ONLY, files=[f])
            self.assertIsNone(sp.records_ref("newlib", {}, set(), [p], TREE, sp.holds)[0], f)

    def test_a_listing_inside_the_directory_reads_the_directory(self):
        """tauceti's real listing (tauceti/project-00N.jsonl): the bump reads them through the directory's glob"""
        src = R["sources"]["tauceti"]
        p = dict(self.DIR_ONLY, files=["data/tentative/tauceti/project-001.jsonl"])
        self.assertEqual(sp.records_ref("tauceti", src, set(), [p], TREE, sp.holds)[0], "content/d")
        self.assertIsNone(sp.records_ref("tauceti", src, set(), [p], TREE, sp.setup_holds)[0])  # setup-auto reads both listed files

    def test_mutant_the_directory_ignored(self):
        blind = mutant("holds", "dir_files = any(in_directory(key, f) for f in present)", "dir_files = False")
        self.assertIsNone(sp.records_ref("newlib", {}, set(), [self.DIR_ONLY], TREE, blind)[0])


class SeveralStarts(unittest.TestCase):
    """plan: as many starts per run as keep bump_pickup.NEED_FREE runners free after PER_START for each, at most MAX_STARTS. The real case: batch 7
    (13 Nov 2026, seven libraries, about 16 runners free) started one library per run, twice an hour, over three and a half hours."""

    def real(self, free):
        reg = sp.registered(R["log"])
        keys = sp.pending(reg, R["sources"], set(R["set_up"]), sp.attempts(without_batch6(R["runs"])), sp.window_start(NOW))
        return sp.plan(keys, refs_for(keys), free)

    def test_batch6_by_free_runners(self):
        for free, n in ((20, 4), (19, 4), (16, 3), (13, 2), (12, 1), (10, 1), (9, 0), (0, 0)):
            starts, notes = self.real(free)
            self.assertEqual([k for k, _ in starts], BATCH6[:n], free)
            self.assertTrue(all(r == "content/fatex-libraries-batch-6" for _, r in starts))
            self.assertEqual(len(notes), 1 if n == 0 else 4 - n, (free, notes))

    def test_at_most_max_starts(self):
        keys = [f"l{i}" for i in range(9)]
        starts, notes = sp.plan(keys, {k: ("", "main") for k in keys}, 100)
        self.assertEqual(len(starts), sp.MAX_STARTS)
        self.assertEqual(notes, [f"l{i}: waits for the next run" for i in range(sp.MAX_STARTS, 9)])

    def test_5000_random_plans(self):
        rnd = random.Random(20261113)
        for _ in range(5000):
            keys = [f"l{i}" for i in range(rnd.randint(0, 9))]
            refs = {k: rnd.choice([(None, "x"), ("", "main"), ("content/b", "pr")]) for k in keys}
            free = rnd.randint(0, 20)
            starts, notes = sp.plan(keys, refs, free)
            ready = [k for k in keys if refs[k][0] is not None]
            want = 0 if free < bp.NEED_FREE else min(len(ready), sp.MAX_STARTS, (free - bp.NEED_FREE) // sp.PER_START + 1)
            self.assertEqual([k for k, _ in starts], ready[:want])
            for i in range(len(starts)):
                self.assertGreaterEqual(free - sp.PER_START * i, bp.NEED_FREE)
            mentioned = {n.split(":")[0] for n in notes if not n.endswith("needed: next run")}
            self.assertEqual(mentioned | {k for k, _ in starts}, set(keys) if (starts or not ready) else {k for k in keys if refs[k][0] is None})

    def test_mutant_no_margin_starts_everything(self):
        with mock.patch.object(sp, "PER_START", 0):
            self.assertEqual(len(self.real(10)[0]), 4)  # every ready library on the last ten free runners
        self.assertEqual(len(self.real(10)[0]), 1)

    def test_main_dispatches_each_start(self):
        """main() over the real registry, runs and records pull request, with 16 runners free: three setup-auto dispatches, each with the branch"""
        import os
        import tempfile

        calls = []

        def run(args, **k):
            if args[:2] == ["git", "log"]:
                return subprocess.CompletedProcess(args, 0, R["log"], "")
            calls.append(args)
            return subprocess.CompletedProcess(args, 0, "", "")

        with tempfile.TemporaryDirectory() as d:
            Path(d, "sources.json").write_text(json.dumps({"sources": R["sources"]}))
            for k in R["set_up"]:
                Path(d, "data", "exports", k).mkdir(parents=True)
                Path(d, "data", "exports", k, "setup.ci.json").write_text("{}")
            cwd = os.getcwd()
            os.chdir(d)
            try:
                with (
                    mock.patch.object(sp.subprocess, "run", run),
                    mock.patch.object(sp, "setup_runs", lambda repo, since: without_batch6(R["runs"])),
                    mock.patch.object(sp, "records_prs", lambda tree: OPEN),
                    mock.patch.object(sp, "main_files", lambda tree, k, s: set()),
                    mock.patch.object(sp.bp, "runners_in_use", lambda: 4),
                    mock.patch.object(sp.time, "time", lambda: NOW),
                    mock.patch.object(sys, "argv", ["setup_pickup.py"]),
                ):
                    sp.main()
            finally:
                os.chdir(cwd)
        self.assertEqual([c[c.index("-f") + 1] for c in calls], [f"key={k}" for k in BATCH6[:3]])
        self.assertTrue(all(c[-1] == "tengoku_ref=content/fatex-libraries-batch-6" for c in calls))


def oracle(reg, sources, set_up, runs, refs, free, now):
    since = max(sp.FIRST_REGISTER, now - sp.WINDOW_DAYS * 86400)
    tried = {}
    for r in runs:
        t = r["displayTitle"]
        if t.startswith("setup-auto ") and t.endswith(", dry run)"):
            continue
        k = t.split(" ")[1]
        tried.setdefault(k, []).append(sp._epoch(r["createdAt"]))
    eligible = [k for k in reg if reg[k] >= since and k in sources and k not in set_up and not any(w >= reg[k] for w in tried.get(k, []))]
    ready = [k for k in eligible if refs[k][0] is not None]
    if not ready or free < bp.NEED_FREE:
        return None, None
    k = min(ready, key=lambda k: (reg[k], k))
    return k, refs[k][0]


class Random(unittest.TestCase):
    def test_5000_states_against_the_oracle(self):
        rnd = random.Random(20261113)
        for _ in range(5000):
            keys = [f"lib{i}" for i in range(rnd.randint(0, 8))]
            now = sp.FIRST_REGISTER + rnd.randint(0, 30 * 86400)
            reg = {k: sp.FIRST_REGISTER + rnd.randint(-5 * 86400, 30 * 86400) for k in keys}
            reg = {k: min(w, now) for k, w in reg.items()}
            sources = {k: {} for k in keys if rnd.random() < 0.9}
            set_up = {k for k in keys if rnd.random() < 0.2}
            runs = []
            for k in keys:
                for _ in range(rnd.randint(0, 2)):
                    t = reg[k] + rnd.randint(-86400, 86400)
                    kind = rnd.choice(["auto", "auto-dry", "sharded"])
                    title = {"auto": f"setup-auto {k} (auto)", "auto-dry": f"setup-auto {k} (staged, dry run)", "sharded": f"setup-sharded {k} (round 1)"}[kind]
                    runs.append({"displayTitle": title, "createdAt": sp.time.strftime("%Y-%m-%dT%H:%M:%SZ", sp.time.gmtime(t))})
            refs = {k: rnd.choice([(None, "x"), ("", "main"), (f"content/b{rnd.randint(0, 9)}", "pr")]) for k in keys}
            free = rnd.randint(0, 20)
            since = sp.window_start(now)
            pend = sp.pending(reg, sources, set_up, sp.attempts(runs), since)
            key, ref, notes = sp.decide(pend, refs, free)
            self.assertEqual((key, ref), oracle(reg, sources, set_up, runs, refs, free, now))
            if key:
                self.assertTrue(reg[key] >= since and key in sources and key not in set_up)
                self.assertGreaterEqual(free, bp.NEED_FREE)
            mentioned = {n.split(":")[0] for n in notes if not n.endswith("needed: next run")}
            short = any(n.endswith("next run") and "ready" in n for n in notes)
            if key:
                self.assertEqual(mentioned, set(pend) - {key})
            elif short:
                self.assertEqual(mentioned, {k for k in pend if refs[k][0] is None})
            else:
                self.assertEqual(mentioned, set(pend))

class Network(unittest.TestCase):
    def test_main_files_reads_404_as_absent_and_stops_on_anything_else(self):
        def fake(answers):
            def run(args, **k):
                path = args[2].split("/contents/", 1)[1].split("?", 1)[0]
                code, out, err = answers.get(path, (1, "", "gh: Not Found (HTTP 404)"))
                return subprocess.CompletedProcess(args, code, out, err)

            return run

        src = {"tentative": ["lib-001.jsonl", "lib/x.jsonl"]}
        got = sp.main_files(TREE, "lib", src, run=fake({
            "data/tentative/lib-001.jsonl": (0, "data/tentative/lib-001.jsonl\n", ""),
            "data/tentative/lib": (0, "data/tentative/lib/x.jsonl\ndata/tentative/lib/y.jsonl\ndata/tentative/lib/notes.md\n", ""),
        }))
        self.assertEqual(got, {"data/tentative/lib-001.jsonl", "data/tentative/lib/x.jsonl", "data/tentative/lib/y.jsonl"})
        self.assertEqual(sp.main_files(TREE, "lib", {}, run=fake({})), set())
        with self.assertRaises(RuntimeError):
            sp.main_files(TREE, "lib", {}, run=fake({"data/tentative/lib.jsonl": (1, "", "gh: Bad credentials (HTTP 401)")}))

    def test_a_list_that_may_be_cut_stops_the_pickup(self):
        with self.assertRaises(RuntimeError):
            sp.setup_runs("r/r", NOW, gh=lambda *a: [{}] * bp.LIST_LIMIT)

    def test_records_prs_reads_the_files_of_each(self):
        calls = []
        real789 = [{"filename": f, "status": "added", "previous_filename": None} for f in OPEN[0]["files"][:4]] + [{"filename": "schemas/sources.json", "status": "modified", "previous_filename": None}]

        def gh(*a):
            calls.append(a)
            if "/files" in a[2]:
                return real789
            return [{"number": 789, "branch": "content/fatex-libraries-batch-6", "repo": TREE}]

        prs = sp.records_prs(TREE, gh=gh)
        self.assertEqual(prs[0]["files"], OPEN[0]["files"])  # the real files of #789, as GitHub listed them (13 Nov 2026)
        self.assertEqual(prs[0]["removed"], [])
        self.assertIn('startswith("records:")', calls[0][-1])
        self.assertEqual(calls[1][-1], ".[] | {filename, status, previous_filename}")

    def test_the_jq_is_the_one_gh_runs(self):
        """the filter of records_prs on a real-shaped answer, run through jq (gh's --jq takes the same language)"""
        answer = [{"filename": "data/tentative/nlalib.jsonl", "status": "added", "previous_filename": None, "additions": 9}, {"filename": "x", "status": "removed", "patch": "-"}]
        jq = sp.records_prs.__code__.co_consts
        expr = next(c for c in jq if isinstance(c, str) and c.startswith(".[] | {filename"))
        out = subprocess.run(["jq", "-c", expr], input=json.dumps(answer), capture_output=True, text=True, check=True).stdout.splitlines()
        self.assertEqual([json.loads(x) for x in out], [{"filename": "data/tentative/nlalib.jsonl", "status": "added", "previous_filename": None}, {"filename": "x", "status": "removed", "previous_filename": None}])


class RemovedFiles(unittest.TestCase):
    """cubic on #187: GitHub lists a file a pull request removes among its files; the branch does not have it"""

    def test_branch_changes(self):
        files, removed = sp.branch_changes([
            {"filename": "data/tentative/a.jsonl", "status": "added"}, {"filename": "data/tentative/b.jsonl", "status": "removed"},
            {"filename": "data/tentative/c.jsonl", "status": "renamed", "previous_filename": "data/tentative/old.jsonl"}, {"filename": "schemas/sources.json", "status": "modified"},
        ])
        self.assertEqual(files, ["data/tentative/a.jsonl", "data/tentative/c.jsonl", "schemas/sources.json"])
        self.assertEqual(removed, ["data/tentative/b.jsonl", "data/tentative/old.jsonl"])

    def test_a_pull_request_that_removes_the_records_is_not_their_branch(self):
        rec = "data/tentative/nlalib.jsonl"
        gone = {"number": 5, "branch": "content/rm", "repo": TREE, "files": ["schemas/sources.json"], "removed": [rec]}
        for rule in (sp.setup_holds, sp.holds):
            self.assertIsNone(sp.records_ref("nlalib", {}, set(), [gone], TREE, rule)[0])
            # on main, and a pull request takes it away: main is still what the job reads by default, and main has it
            self.assertEqual(sp.records_ref("nlalib", {}, {rec}, [gone], TREE, rule)[0], "")
        # one of flt-anthropic's three files on main, removed by the pull request that adds the other two: the branch lacks it
        files = sp.tentative_files("flt-anthropic", R["sources"]["flt-anthropic"])
        p = {"number": 6, "branch": "content/x", "repo": TREE, "files": files[1:], "removed": files[:1]}
        for rule in (sp.setup_holds, sp.holds):
            self.assertIsNone(sp.records_ref("flt-anthropic", R["sources"]["flt-anthropic"], set(files[:1]), [p], TREE, rule)[0])
            self.assertEqual(sp.records_ref("flt-anthropic", R["sources"]["flt-anthropic"], set(files[:1]), [dict(p, removed=[])], TREE, rule)[0], "content/x")

    def test_mutant_removed_files_counted_is_caught(self):
        files = sp.tentative_files("flt-anthropic", R["sources"]["flt-anthropic"])
        p = {"number": 6, "branch": "content/x", "repo": TREE, "files": files[1:], "removed": files[:1]}
        counted = mutant("records_ref", '(on_main - set(p.get("removed", [])))', "on_main")
        self.assertEqual(counted("flt-anthropic", R["sources"]["flt-anthropic"], set(files[:1]), [p], TREE)[0], "content/x")

class Workflow(unittest.TestCase):
    def setUp(self):
        self.text = (WF / "setup-pickup.yml").read_text()
        self.y = yaml.safe_load(self.text)

    def test_triggers_permissions_and_guard(self):
        on = self.y[True]
        self.assertEqual(on["push"], {"branches": ["main"], "paths": ["sources.json"]})
        self.assertEqual(on["workflow_dispatch"]["inputs"]["dry_run"]["default"], "true")
        self.assertIn("schedule", on)
        # the scheduler did not fire the cron in its first four hours on main (13 Nov 2026): every bump-pickup run starts this one too
        # and every time a long job ends and frees runners (the cron of bump-pickup itself fired 3 times in 16 hours: 20:47, 01:48 and 09:27)
        # only runs of main (cubic on #191): github.ref of a workflow_run is the default branch whatever branch the upstream run was on
        self.assertEqual(on["workflow_run"], {"workflows": ["bump-pickup", "setup-sharded", "bump-sharded"], "types": ["completed"], "branches": ["main"]})
        for wf in on["workflow_run"]["workflows"]:
            self.assertEqual(yaml.safe_load((WF / f"{wf}.yml").read_text())["name"], wf)
        # a dry run is never a trigger: none of the long workflows has a dry_run input, and bump-pickup's dispatched runs are skipped by the job's `if`
        for wf in ("setup-sharded", "bump-sharded"):
            self.assertNotIn("dry_run", yaml.safe_load((WF / f"{wf}.yml").read_text())[True]["workflow_dispatch"]["inputs"], wf)
        self.assertEqual(self.y["permissions"], {})
        job = self.y["jobs"]["pickup"]
        self.assertEqual(job["permissions"], {"actions": "write", "contents": "read"})
        for s in ("vars.LANE_ENABLED == 'true'", "github.ref == 'refs/heads/main'", "github.repository == 'competemath/emissary-archangel'",
                  # after a bump-pickup only on its schedule: a person's dry run of bump-pickup must not start setups (cubic on #190)
                  "(github.event_name != 'workflow_run' || github.event.workflow_run.name != 'bump-pickup' || github.event.workflow_run.event == 'schedule')"):
            self.assertIn(s, job["if"])
        run = "\n".join(s.get("run", "") for s in job["steps"])
        for p in ('"/scripts/bump/"', '"/sources.json"', '"/data/exports/*/setup.ci.json"'):
            self.assertIn(p, run)
        self.assertIn("python3 scripts/bump/setup_pickup.py", run)
        self.assertNotIn("${{", run)

    def test_setup_autos_run_name_marks_a_dry_run(self):
        name = yaml.safe_load((WF / "setup-auto.yml").read_text())["run-name"]
        self.assertEqual(name, "setup-auto ${{ inputs.key }} (${{ inputs.mode }}${{ inputs.dry_run == 'true' && ', dry run' || '' }})")
        for dry, counted in (("true", False), ("false", True)):
            title = name.replace("${{ inputs.key }}", "nlalib").replace("${{ inputs.mode }}", "auto")
            title = title.replace("${{ inputs.dry_run == 'true' && ', dry run' || '' }}", ", dry run" if dry == "true" else "")
            got = sp.attempts([{"displayTitle": title, "createdAt": "2026-11-13T03:00:00Z"}])
            self.assertEqual("nlalib" in got, counted, title)


if __name__ == "__main__":
    unittest.main()
