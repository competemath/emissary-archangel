"""Gate 2 in chunks under a memory guard (gate2_driver.py, gate2_guard.py).

2026-10-10: navier-stokes-euler's shards died in Gate 2 four times ('Killed', then 'The runner has received a shutdown signal'), three of them shards of only
38 to 249 modules: one Lean process over every declaration of the shard grows until the machine is gone. The driver cuts the declarations into chunks, runs each
under a memory limit, and splits a chunk that is killed until the module that kills Lean alone is known."""

import re
import sys
import time
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import gate2_driver as d  # noqa: E402
import gate2_guard as gd  # noqa: E402

WORKFLOWS = Path(__file__).resolve().parents[3] / ".github" / "workflows"


class Fake:
    """A library of modules m0..m(n-1) with 100 declarations each. `poison`: modules whose presence in a chunk kills Lean. `clash`: two modules that cannot be imported
    together (Lean says `import <the second> failed`); `importers`: modules that import the second one (left out with it)."""

    def __init__(self, n=10, poison=(), clash=None, importers=()):
        self.mods = [f"m{i}" for i in range(n)]
        self.poison, self.clash, self.importers = set(poison), clash, set(importers)
        self.runs, self.controls_seen, self.verdicts = [], [], []

    def gen(self, only, exclude, controls):
        keep = [m for m in self.mods if (not only or m in only)]
        left = []
        if exclude:
            left = [m for m in keep if m in set(exclude) or (set(exclude) and m in self.importers)]
            keep = [m for m in keep if m not in left]
        return {"plan_modules": [[m, 100] for m in keep], "excluded_modules": left, "modules_checked": len(keep), "declarations": 100 * len(keep), "controls": controls}

    def run(self, meta):
        mods = [m for m, _ in meta["plan_modules"]]
        self.runs.append(mods)
        self.controls_seen.append(meta["controls"])
        if self.poison & set(mods):
            return "memory", "partial output that must not be used\n"
        if self.clash and set(self.clash) <= set(mods):
            return "ok", f"import {self.clash[1]} failed\n"
        return "ok", "".join(f"V:{m}\n" for m in mods)

    def drive(self, controls=5, max_decls=300, **kw):
        logs, killed, last = d.drive([], self.gen, self.run, controls, max_decls, say=lambda s: None, **kw)
        got = [m for t in logs for m in re.findall(r"V:(\S+)", t)]
        return got, killed, last


class Chunks(unittest.TestCase):
    def test_modules_are_cut_into_chunks_of_at_most_the_limit(self):
        self.assertEqual(d.cut([["a", 100], ["b", 100], ["c", 100], ["d", 100]], 250), [["a", "b"], ["c", "d"]])
        self.assertEqual(d.cut([["a", 500], ["b", 10]], 250), [["a"], ["b"]])  # a module over the limit has a chunk of its own
        self.assertEqual(d.cut([], 250), [])

    def test_a_healthy_library_gets_each_module_checked_once(self):
        f = Fake(10)
        got, killed, _ = f.drive()
        self.assertEqual(sorted(got), sorted(f.mods))
        self.assertEqual(killed, [])
        self.assertGreater(len(f.runs), 1)  # chunks, not one process


class KilledChunks(unittest.TestCase):
    def test_the_module_that_kills_lean_alone_is_found_and_the_rest_is_checked(self):
        f = Fake(10, poison={"m6"})
        got, killed, _ = f.drive()
        self.assertEqual(killed, ["m6"])
        self.assertEqual(sorted(got), sorted(m for m in f.mods if m != "m6"))  # every other module has exactly one verdict
        self.assertNotIn("partial output", "".join(got))

    def test_two_poisoned_modules_are_both_found(self):
        f = Fake(12, poison={"m2", "m9"})
        got, killed, _ = f.drive()
        self.assertEqual(sorted(killed), ["m2", "m9"])
        self.assertEqual(sorted(got), sorted(m for m in f.mods if m not in ("m2", "m9")))

    def test_the_number_of_processes_stays_small(self):
        f = Fake(40, poison={"m17"})
        f.drive(max_decls=400)
        self.assertLess(len(f.runs), 40)  # splitting in halves, not one process per module

    def test_the_controls_run_once_even_when_the_first_chunk_is_split(self):
        f = Fake(10, poison={"m1"})
        f.drive(controls=5)
        self.assertEqual(sum(c for c, mods in zip(f.controls_seen, f.runs) if "m1" not in mods), 5)  # the processes that finished carried the controls exactly once

    def test_a_budget_that_runs_out_records_what_it_never_checked(self):
        f = Fake(10)
        t = iter(range(0, 1000, 10))
        got, killed, _ = f.drive(now=lambda: next(t), budget_s=35)
        self.assertTrue(killed)  # the later chunks got no time
        self.assertEqual(sorted(got + killed), sorted(f.mods))  # and nothing is lost between the two lists


class ImportClashes(unittest.TestCase):
    def test_a_clash_leaves_the_module_and_its_importers_to_a_later_round(self):
        f = Fake(6, clash=("m1", "m2"), importers={"m3"})  # m2 cannot be imported with m1; m3 imports m2
        got, killed, _ = f.drive(max_decls=1000)
        self.assertEqual(sorted(got), sorted(f.mods))  # everything is checked: the clashing pair in separate processes
        self.assertEqual(killed, [])


class Guard(unittest.TestCase):
    def run_py(self, code, **kw):
        import os
        import tempfile

        log = Path(tempfile.mkdtemp()) / "x.log"
        res = gd.run_guarded([sys.executable, "-c", code], ".", dict(os.environ), log, kw.pop("timeout_s", 20), kw.pop("rss_limit_kb", 10**9), poll_s=0.1)
        return res, log.read_text()

    def test_a_command_that_ends_by_itself_is_ok_whatever_its_exit_code(self):
        res, out = self.run_py("print('hi'); raise SystemExit(3)")
        self.assertEqual((res.kind, res.returncode), ("ok", 3))
        self.assertIn("hi", out)

    def test_a_command_over_the_memory_limit_is_killed(self):
        res, _ = self.run_py("import os, time\nx = os.urandom(300 * 1024 * 1024)\ntime.sleep(30)", rss_limit_kb=150 * 1024)
        self.assertEqual(res.kind, "memory")
        self.assertLess(res.seconds, 15)
        self.assertGreater(res.peak_kb, 150 * 1024)

    def test_a_command_over_the_time_limit_is_killed(self):
        res, _ = self.run_py("import time; time.sleep(30)", timeout_s=1)
        self.assertEqual(res.kind, "timeout")

    def test_what_the_command_started_is_killed_with_it(self):
        import os
        import subprocess
        import tempfile

        pidfile = Path(tempfile.mkdtemp()) / "child.pid"
        code = f"import subprocess,sys,time\nc = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(60)'])\nopen({str(pidfile)!r}, 'w').write(str(c.pid))\ntime.sleep(60)"
        res, _ = self.run_py(code, timeout_s=2)
        self.assertEqual(res.kind, "timeout")
        time.sleep(0.5)
        pid = int(pidfile.read_text())
        alive = subprocess.run(["ps", "-p", str(pid)], capture_output=True).returncode == 0
        if alive:
            os.kill(pid, 9)
        self.assertFalse(alive, "the child of the killed command is still running")

    def test_the_limit_is_a_share_of_the_machine(self):
        self.assertGreater(gd.mem_limit_kb(), 0)
        self.assertLessEqual(gd.mem_limit_kb(0.5), gd.mem_limit_kb(0.9))


class EndToEnd(unittest.TestCase):
    """The real command line: gate2_batch.generate for the plan, a stand-in `lean` that prints verdicts and eats memory when it imports Toy.Poison, the guard and the driver."""

    def setUp(self):
        import os
        import stat
        import tempfile
        import json

        self.d = Path(tempfile.mkdtemp())
        lib = self.d / "lib"
        for m in ("A", "B", "Poison"):
            (lib / "Toy").mkdir(parents=True, exist_ok=True)
            (lib / "Toy" / f"{m}.lean").write_text(f"theorem t_{m.lower()} : True := trivial\n")
            o = lib / ".lake" / "build" / "lib" / "lean" / "Toy"
            o.mkdir(parents=True, exist_ok=True)
            (o / f"{m}.olean").write_text("")
            ex = self.d / "exports"
            ex.mkdir(exist_ok=True)
            (ex / f"Toy.{m}.ndjson").write_text("")
            (ex / f"Toy.{m}.names.json").write_text(json.dumps({"names": [f"Toy.t_{m.lower()}"]}))
        sha = "a" * 40
        (self.d / "tent.jsonl").write_text("".join(json.dumps({"name": f"Toy.t_{m.lower()}", "library": "toy", "source_url": f"https://github.com/o/r/blob/{sha}/Toy/{m}.lean#L1"}) + "\n" for m in ("A", "B", "Poison")))
        bindir = self.d / "bin"
        bindir.mkdir()
        lean = bindir / "lean"
        lean.write_text(
            "#!%s\nimport re, sys, time\nt = open(sys.argv[1]).read()\n"
            "if 'import Toy.Poison' in t:\n    import os\n    x = os.urandom(300 * 1024 * 1024)\n    time.sleep(60)\n"
            "for names in re.findall(r'#gate2_batch \"([^\"]*)\"', t):\n    for n in names.split(','): print('GATE2B_PASS old=%%s new=%%s' %% (n, n))\n" % sys.executable
        )
        lean.chmod(lean.stat().st_mode | stat.S_IXUSR)
        self.env = {**os.environ, "PATH": f"{bindir}{os.pathsep}{os.environ['PATH']}"}

    def run_driver(self, max_decls):
        import json
        import os
        from unittest import mock

        with mock.patch.dict(os.environ, self.env):
            rc = d.main(["--key", "toy", "--lib", str(self.d / "lib"), "--exports", str(self.d / "exports"), "--ledger", str(self.d / "none.jsonl"), "--roots", "Toy",
                         "--lean-path", "", "--tentative", str(self.d / "tent.jsonl"), "--max-decls", str(max_decls), "--rss-limit-mb", "150",
                         "--log", str(self.d / "gate2.log"), "--killed", str(self.d / "killed.json"), "--plan", str(self.d / "plan.json")])
        return rc, (self.d / "gate2.log").read_text(), json.loads((self.d / "killed.json").read_text())

    def test_the_poisoned_module_is_found_in_one_chunk_or_in_many(self):
        for max_decls in (1, 10):
            rc, log, killed = self.run_driver(max_decls)
            self.assertEqual(rc, 0)
            self.assertEqual(killed, ["Toy.Poison"], max_decls)
            self.assertEqual(sorted(re.findall(r"old=(\S+)", log)), ["Toy.t_a", "Toy.t_b"], max_decls)  # the others have a verdict, exactly one


class Workflows(unittest.TestCase):
    """Both Gate 2 steps run the driver, not one unguarded Lean process over everything."""

    def test_the_two_workflows_use_the_driver(self):
        for name in ("bump-shard.yml", "bump-library.yml"):
            text = (WORKFLOWS / name).read_text()
            self.assertIn("scripts/bump/gate2_driver.py", text, name)
            self.assertNotRegex(text, r"timeout \d+m lean gate2-check\.lean", name)


if __name__ == "__main__":
    unittest.main()
