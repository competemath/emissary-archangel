"""A build-once hands its work from job to job (wave_pack.py, tolerant_build --own), on the jobs planned from flt-anthropic's real import graph (fixtures/real-flt-imports.json.gz).

Invariants: a job restores exactly the files of its closure, byte for byte, and nothing else; a module no pack knows stops the job; a module in two packs stops the job; a manifest cannot name a file outside
the library; a restored module is never built again and its errors never reach the repair rounds; a module whose job left no olean blocks what imports it."""

import argparse
import gzip
import json
import os
import shutil
import stat
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))

import build_waves as bw  # noqa: E402
import tolerant_build as tb  # noqa: E402
import wave_pack as wp  # noqa: E402

G = json.loads(gzip.open(HERE / "fixtures" / "real-flt-imports.json.gz").read())


def src(lib, m):
    return lib.joinpath(*tb.split_mod(m)).with_suffix(".lean")


def olean(lib, m):
    p = lib.joinpath(".lake/build/lib/lean", *tb.split_mod(m))
    return p.with_name(p.name + ".olean")


def write(lib, m, built=True):
    s = src(lib, m)
    s.parent.mkdir(parents=True, exist_ok=True)
    s.write_text(f"-- repaired {m}\n", encoding="utf-8")
    if built:
        o = olean(lib, m)
        o.parent.mkdir(parents=True, exist_ok=True)
        o.write_bytes(f"olean {m}".encode())
        c = lib / ".bump-cache"
        c.mkdir(exist_ok=True)
        (c / f"{m}.key").write_text("k")
        (c / f"{m}.log.json").write_text(json.dumps({"state": "clean", "errors": 0, "log": []}))


def slice_of_real_graph(n):
    """the n lowest modules of the real graph, with their real imports: closed under imports because lower depth comes first"""
    level = bw.depths(G["imports"])
    keep = sorted(G["imports"], key=lambda m: (level[m], m))[:n]
    inside = set(keep)
    return {m: [d for d in G["imports"][m] if d in inside] for m in keep}, level


class RealPlan(unittest.TestCase):
    def test_every_job_restores_exactly_its_closure(self):
        imports, _ = slice_of_real_graph(1500)
        lines = {m: G["lines"][m] for m in imports}
        waves = bw.plan(imports, lines, max(sum(lines.values()) // 12, 1), 6)
        self.assertGreater(len(waves), 1)
        jobs = sum(len(w["jobs"]) for w in waves)
        self.assertGreater(jobs, 3)
        with tempfile.TemporaryDirectory() as t:
            t = Path(t)
            packs = t / "packs"
            done = 0
            for w, wave in enumerate(waves):
                for j, job in enumerate(wave["jobs"]):
                    lib = t / f"build-{w}-{j}"
                    lib.mkdir()
                    closure, _ = bw.job_inputs(waves, imports, w, j)
                    if closure:
                        self.assertEqual(wp.restore(lib, packs, closure)["restored"], len(closure))
                        got = {str(p.relative_to(lib)) for p in lib.rglob("*") if p.is_file()}
                        want = {f for m in closure for f in wp.files_of(lib, m, str(src(lib, m).relative_to(lib)))}
                        self.assertEqual(got, want)
                        for m in closure:
                            self.assertEqual(olean(lib, m).read_bytes(), f"olean {m}".encode())
                            self.assertEqual(src(lib, m).read_text(encoding="utf-8"), f"-- repaired {m}\n")
                        done += 1
                    for m in job["modules"]:
                        write(lib, m)
                    wp.pack(lib, {m: src(lib, m) for m in job["modules"]}, job["modules"], packs / f"{w}-{j}")
            self.assertGreater(done, 0)


class Restore(unittest.TestCase):
    def setUp(self):
        self.d = tempfile.TemporaryDirectory()
        self.t = Path(self.d.name)
        self.lib = self.t / "lib"
        self.lib.mkdir()
        self.packs = self.t / "packs"

    def tearDown(self):
        self.d.cleanup()

    def packed(self, name, built=(), failed=()):
        for m in built:
            write(self.lib, m)
        for m in failed:
            write(self.lib, m, built=False)
        mods = [*built, *failed]
        return wp.pack(self.lib, {m: src(self.lib, m) for m in mods}, mods, self.packs / name)

    def fresh(self):
        n = self.t / "fresh"
        n.mkdir()
        return n

    def test_a_module_in_no_pack_stops_the_job(self):
        self.packed("a", ["A.B"])
        with self.assertRaisesRegex(ValueError, "in no pack"):
            wp.restore(self.fresh(), self.packs, ["A.B", "Lost.Module"])

    def test_a_module_in_two_packs_stops_the_job(self):
        self.packed("a", ["A.B"])
        self.packed("b", ["A.B"])
        with self.assertRaisesRegex(ValueError, "two packs"):
            wp.restore(self.fresh(), self.packs, ["A.B"])

    def test_a_manifest_cannot_name_a_file_outside_the_library(self):
        self.packed("a", ["A.B"])
        n = self.fresh()
        for evil in ["../evil", "/etc/evil", "a/../../evil"]:
            (self.packs / "a" / wp.MANIFEST).write_text(json.dumps({"A.B": [evil]}))
            with self.assertRaisesRegex(ValueError, "outside the library"):
                wp.restore(n, self.packs, ["A.B"])

    def test_a_module_that_left_no_olean_is_known_and_empty(self):
        m = self.packed("a", ["A.B"], ["A.Broken"])
        self.assertEqual(m["A.Broken"], [])
        n = self.fresh()
        self.assertEqual(wp.restore(n, self.packs, ["A.B", "A.Broken"]), {"restored": 1, "no_olean": 1})
        self.assertFalse(src(n, "A.Broken").exists())

    def test_a_job_with_nothing_built_still_leaves_a_manifest(self):
        self.packed("a", [], ["A.Broken"])
        self.assertFalse((self.packs / "a" / wp.ARCHIVE).exists())
        self.assertEqual(wp.restore(self.fresh(), self.packs, ["A.Broken"]), {"restored": 0, "no_olean": 1})

    def test_guillemets_and_a_space_in_a_name(self):
        m = "Foo.«1102.4662 v2».C"
        self.packed("a", [m])
        n = self.fresh()
        self.assertEqual(wp.restore(n, self.packs, [m])["restored"], 1)
        self.assertEqual(olean(n, m).read_bytes(), f"olean {m}".encode())

    def test_a_linked_source_travels_as_text(self):
        write(self.lib, "A.B")
        real = self.t / "elsewhere.lean"
        real.write_text("-- the text\n")
        src(self.lib, "A.B").unlink()
        src(self.lib, "A.B").symlink_to(real)
        wp.pack(self.lib, {"A.B": src(self.lib, "A.B")}, ["A.B"], self.packs / "a")
        n = self.fresh()
        wp.restore(n, self.packs, ["A.B"])
        self.assertFalse(src(n, "A.B").is_symlink())
        self.assertEqual(src(n, "A.B").read_text(), "-- the text\n")

    def test_an_unknown_module_cannot_be_packed(self):
        with self.assertRaisesRegex(ValueError, "not in the library"):
            wp.pack(self.lib, {}, ["Nope"], self.packs / "a")


class FetchAndPlace(unittest.TestCase):
    def setUp(self):
        self.d = tempfile.TemporaryDirectory()
        self.t = Path(self.d.name)
        self.lib = self.t / "built"
        self.lib.mkdir()
        for name, mods in {"1": ["A.B"], "2": ["A.C"], "3": ["A.D"]}.items():
            for m in mods:
                write(self.lib, m)
            wp.pack(self.lib, {m: src(self.lib, m) for m in mods}, mods, self.t / "uploaded" / name)
        self.seen = []
        self.on_disk = []

    def tearDown(self):
        self.d.cleanup()

    def download(self, shard, into):
        self.seen.append(shard)
        self.on_disk.append(len(list((self.t / "work").glob("*"))))
        for f in (self.t / "uploaded" / str(shard)).iterdir():
            shutil.copy2(f, into / f.name)

    def test_packs_come_one_at_a_time_and_are_deleted(self):
        got = wp.fetch_all(self.t / "restored", ["A.B", "A.C"], [1, 2], self.download, self.t / "work")
        self.assertEqual(got, {"restored": 2, "no_olean": 0})
        self.assertEqual(self.seen, [1, 2])
        self.assertEqual(self.on_disk, [1, 1])
        self.assertEqual(list((self.t / "work").glob("*")), [])

    def test_a_module_the_named_packs_do_not_hold_stops_the_job(self):
        with self.assertRaisesRegex(ValueError, "in no pack"):
            wp.fetch_all(self.t / "restored", ["A.B", "A.D"], [1, 2], self.download, self.t / "work")

    def test_a_download_is_tried_again_and_then_gives_up(self):
        answers = iter([1, 1, 0])
        calls, waits = [], []
        run = lambda cmd, check: (calls.append(cmd), type("R", (), {"returncode": next(answers)})())[1]  # noqa: E731
        wp.gh_download("o/r", "77", "flt", runner=run, sleep=waits.append)(5, self.t)
        self.assertEqual(len(calls), 3)
        self.assertEqual(waits, [30, 60])
        self.assertEqual(calls[0][:8], ["gh", "run", "download", "77", "-R", "o/r", "-n", "wave-flt-5"])
        never = lambda cmd, check: type("R", (), {"returncode": 1})()  # noqa: E731
        with self.assertRaisesRegex(RuntimeError, "could not be fetched"):
            wp.gh_download("o/r", "77", "flt", runner=never, sleep=lambda _: None)(5, self.t)

    def test_place_moves_files_and_replaces_what_is_there(self):
        restored = self.t / "restored"
        wp.fetch_all(restored, ["A.B"], [1], self.download, self.t / "work")
        lib = self.t / "lib"
        src(lib, "A.B").parent.mkdir(parents=True)
        src(lib, "A.B").write_text("-- the unrepaired text\n")
        n = wp.place(restored, lib)
        self.assertEqual(n, 4)
        self.assertEqual(src(lib, "A.B").read_text(encoding="utf-8"), "-- repaired A.B\n")
        self.assertEqual(olean(lib, "A.B").read_bytes(), b"olean A.B")
        self.assertEqual([p for p in restored.rglob("*") if p.is_file()], [])

    def test_place_replaces_a_link_instead_of_writing_through_it(self):
        restored = self.t / "r2"
        wp.fetch_all(restored, ["A.B"], [1], self.download, self.t / "work")
        lib = self.t / "lib2"
        src(lib, "A.B").parent.mkdir(parents=True)
        target = self.t / "upstream.lean"
        target.write_text("-- upstream\n")
        src(lib, "A.B").symlink_to(target)
        wp.place(restored, lib)
        self.assertFalse(src(lib, "A.B").is_symlink())
        self.assertEqual(target.read_text(), "-- upstream\n")


FAKE_LEAN = """#!/bin/sh
# lean --run DRIVER rel mod olean
echo "$4" >> "$FAKE_CALLS"
mkdir -p "$(dirname "$5")"
echo "built $4" > "$5"
case "$4" in *Err*) echo "$3:1:0: error: broken"; exit 2;; esac
"""


class OwnModules(unittest.TestCase):
    """tolerant_build --own against a stand-in for lean that records every call"""

    def setUp(self):
        self.d = tempfile.TemporaryDirectory()
        self.t = Path(self.d.name)
        self.lib = self.t / "lib"
        self.calls = self.t / "calls"
        (self.lib / "T").mkdir(parents=True)
        bin_dir = self.t / "bin"
        bin_dir.mkdir()
        lean = bin_dir / "lean"
        lean.write_text(FAKE_LEAN)
        lean.chmod(lean.stat().st_mode | stat.S_IEXEC)
        self.old = tb.lake_env
        env = {**os.environ, "PATH": f"{bin_dir}:{os.environ['PATH']}", "FAKE_CALLS": str(self.calls), "LEAN_PATH": ""}
        tb.lake_env = lambda _lib: env

    def tearDown(self):
        tb.lake_env = self.old
        self.d.cleanup()

    def source(self, m, *imports):
        src(self.lib, m).write_text("".join(f"import {d}\n" for d in imports) + "theorem x : True := trivial\n")

    def restored(self, m, log=()):
        o = olean(self.lib, m)
        o.parent.mkdir(parents=True, exist_ok=True)
        o.write_bytes(b"from an earlier job")
        c = self.lib / ".bump-cache"
        c.mkdir(exist_ok=True)
        (c / f"{m}.key").write_text("a key from another runner")
        (c / f"{m}.log.json").write_text(json.dumps({"state": "errors" if log else "clean", "errors": len(log), "log": list(log)}))

    def build(self, own):
        (self.t / "own.txt").write_text("\n".join(own) + "\n")
        b = tb.Builder(argparse.Namespace(lib=str(self.lib), roots="T", cache=str(self.lib / ".bump-cache"), timeout=1, jobs=2, modules="", own=str(self.t / "own.txt")))
        return b, b.run()

    def called(self):
        return self.calls.read_text().split() if self.calls.exists() else []

    def test_a_restored_module_is_not_built_though_its_key_is_from_another_runner(self):
        self.source("T.A")
        self.source("T.B", "T.A")
        self.restored("T.A")
        _, r = self.build(["T.B"])
        self.assertEqual(self.called(), ["T.B"])
        self.assertTrue(r["status"]["T.A"]["restored"])
        self.assertEqual(r["status"]["T.B"]["state"], "clean")
        self.assertEqual(olean(self.lib, "T.A").read_bytes(), b"from an earlier job")

    def test_the_log_of_a_restored_module_stays_out_of_the_build_log(self):
        self.source("T.A")
        self.source("T.ErrB", "T.A")
        self.restored("T.A", ["error: T/A.lean:1:0: from its own job"])
        b, r = self.build(["T.ErrB"])
        self.assertEqual(r["status"]["T.A"]["state"], "errors")
        self.assertFalse(any("from its own job" in ln for ln in b.log_lines))
        self.assertTrue(any("T/ErrB.lean" in ln for ln in b.log_lines))

    def test_a_module_whose_job_left_no_olean_blocks_its_importers_and_is_not_tried(self):
        self.source("T.A")
        self.source("T.B", "T.A")
        _, r = self.build(["T.B"])
        self.assertEqual(self.called(), [])
        self.assertEqual(r["status"]["T.A"]["state"], "blocked")
        self.assertEqual(r["status"]["T.B"]["state"], "blocked")

    def test_without_own_everything_is_built(self):
        self.source("T.A")
        self.source("T.B", "T.A")
        b = tb.Builder(argparse.Namespace(lib=str(self.lib), roots="T", cache=str(self.lib / ".bump-cache"), timeout=1, jobs=2, modules="", own=""))
        b.run()
        self.assertEqual(sorted(self.called()), ["T.A", "T.B"])


if __name__ == "__main__":
    unittest.main()
