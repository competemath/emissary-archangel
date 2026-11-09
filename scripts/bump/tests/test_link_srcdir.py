"""A library whose modules live under a source folder (`srcdir`, classfieldtheory-yamaguchi's `Lean4`): the roots are linked where the module names say.

Real case: 13,326 records of classfieldtheory-yamaguchi (Lean v4.34.0) were dropped because every path starts with `Lean4/`. Fixtures: real-cft-layout.json.gz, every .lean path of the
repository at its pinned commit and its real lakefile; real-seed-paths.json.gz, the source path of every record. Invariants: every record's module is found by the bump's own module
walk; the walk finds exactly the repository's modules under the roots; an edit through a link lands in the file Lake compiles; a second run changes nothing; the links are the
only change; a folder that leaves the project, or a root that is also at the top, stops the run; every job that clones the library makes the links."""

import gzip
import json
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))

import gate2_batch  # noqa: E402
import link_srcdir  # noqa: E402
import tolerant_build as tb  # noqa: E402

import yaml  # noqa: E402

FIXTURES = HERE / "fixtures"
REPO = HERE.parents[2]
ROOTS = ["ClassFieldTheory", "ValuedFieldTheory", "GaloisCohomology", "ProCGroups"]
LAYOUT = json.loads(gzip.open(FIXTURES / "real-cft-layout.json.gz").read())
RECORDS = json.loads(gzip.open(FIXTURES / "real-seed-paths.json.gz").read())["classfieldtheory-yamaguchi"]["paths"]


def materialise(d: Path) -> None:
    for p in LAYOUT["lean_files"]:
        f = d / p
        f.parent.mkdir(parents=True, exist_ok=True)
        f.write_text(f"-- {p}\n")
    (d / "lakefile.toml").write_text(LAYOUT["lakefile"])


class RealRepository(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.d = Path(self.tmp.name)
        materialise(self.d)

    def tearDown(self):
        self.tmp.cleanup()

    def test_the_cases_are_the_real_ones(self):
        self.assertEqual(sum(RECORDS.values()), 13326)
        self.assertGreater(len(LAYOUT["lean_files"]), 300)
        self.assertTrue(all(p.startswith("Lean4/") for p in RECORDS))
        self.assertIn('srcDir = "Lean4"', LAYOUT["lakefile"])

    def test_without_links_the_walk_finds_nothing(self):
        """the failure itself: this is what the setup and the bump saw"""
        self.assertEqual(tb._under_roots(self.d, ROOTS), {})

    def test_the_walk_finds_exactly_the_modules_under_the_roots(self):
        link_srcdir.link(self.d, "Lean4", ROOTS)
        found = tb._under_roots(self.d, ROOTS)
        want = {p[len("Lean4/") : -len(".lean")].replace("/", ".") for p in LAYOUT["lean_files"] if p.split("/")[1].removesuffix(".lean") in ROOTS}
        self.assertEqual(set(found), want)
        self.assertGreater(len(want), 300)

    def test_every_record_has_its_module(self):
        link_srcdir.link(self.d, "Lean4", ROOTS)
        found = tb._under_roots(self.d, ROOTS)
        missing = [p for p in RECORDS if p[len("Lean4/") : -len(".lean")].replace("/", ".") not in found]
        self.assertEqual(missing, [])

    def test_an_edit_through_a_link_lands_in_the_file_lake_compiles(self):
        """the import rewrite of the bump writes to the path a module name spells"""
        link_srcdir.link(self.d, "Lean4", ROOTS)
        name, path = sorted(tb._under_roots(self.d, ROOTS).items())[0]
        path.write_text("-- rewritten\n")
        self.assertEqual((self.d / "Lean4" / path.relative_to(self.d)).read_text(), "-- rewritten\n", name)

    def test_a_second_run_changes_nothing(self):
        a = link_srcdir.link(self.d, "Lean4", ROOTS)
        self.assertEqual(link_srcdir.link(self.d, "Lean4", ROOTS), a)

    def test_the_links_are_the_only_change(self):
        before = sorted(p.relative_to(self.d).as_posix() for p in self.d.rglob("*") if p.is_file() and not p.is_symlink())
        lake = (self.d / "lakefile.toml").read_bytes()
        made = link_srcdir.link(self.d, "Lean4", ROOTS)
        after = sorted(p.relative_to(self.d).as_posix() for p in self.d.rglob("*") if p.is_file() and not p.is_symlink())
        self.assertEqual(after, before)
        self.assertEqual((self.d / "lakefile.toml").read_bytes(), lake)
        self.assertEqual(sorted(p.name for p in self.d.iterdir() if p.is_symlink()), sorted(made))
        for name in made:
            self.assertFalse((self.d / name).readlink().is_absolute(), "a link that moves with the clone")


AINT = json.loads(gzip.open(FIXTURES / "real-aintlib-layout.json.gz").read())
AINT_SRC = json.loads((REPO / "sources.json").read_text())["sources"]["aintlib"]


class RealMonorepo(unittest.TestCase):
    """aintlib at its pinned commit: 11 Lake libraries with a source folder each. 30,137 of its 30,142 records were dropped because the registry knew one folder."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.d = Path(self.tmp.name)
        for p in AINT["lean_files"]:
            f = self.d / p
            f.parent.mkdir(parents=True, exist_ok=True)
            f.write_text(f"-- {p}\n")
        self.made = link_srcdir.link(self.d, link_srcdir.srcdirs_of(AINT_SRC), AINT_SRC["roots"])

    def tearDown(self):
        self.tmp.cleanup()

    def module(self, path):
        for d in sorted(link_srcdir.srcdirs_of(AINT_SRC), key=len, reverse=True):
            if path.startswith(d + "/"):
                return path[len(d) + 1 : -len(".lean")].replace("/", ".")
        return None

    def test_the_cases_are_the_real_ones(self):
        self.assertEqual((len(AINT["lean_files"]), sum(AINT["records"].values())), (2823, 30142))

    def test_every_record_of_a_root_has_its_module(self):
        found = tb._under_roots(self.d, AINT_SRC["roots"])
        kept = {p: n for p, n in AINT["records"].items() if self.module(p) and self.module(p).split(".")[0] in AINT_SRC["roots"]}
        self.assertEqual([p for p in kept if self.module(p) not in found], [])
        self.assertEqual(sum(kept.values()), 30124)  # 13 in a `.mathlib-quality` folder and the 5 of Common are no root's

    def test_every_lean_file_is_reachable_where_its_module_name_says(self):
        """an import of another project (LeanModularForms, Common) is followed by the path its name spells (tolerant_build.module_files)"""
        missing = []
        for p in AINT["lean_files"]:
            m = self.module(p)
            if m and not m.startswith(".") and not (self.d / (m.replace(".", "/") + ".lean")).is_file():
                missing.append(p)
        self.assertEqual(missing, [])

    def test_the_folder_named_after_its_module(self):
        self.assertTrue((self.d / "Common" / "Analysis").is_symlink())
        self.assertTrue((self.d / "Common.lean").is_symlink())
        self.assertEqual((self.d / "Common" / "Analysis" / "DirichletBounds.lean").read_text(), "-- Common/Common/Analysis/DirichletBounds.lean\n")

    def test_a_second_run_changes_nothing(self):
        self.assertEqual(link_srcdir.link(self.d, link_srcdir.srcdirs_of(AINT_SRC), AINT_SRC["roots"]), self.made)

    def test_an_edit_lands_in_the_real_file(self):
        (self.d / "HasseWeil" / "HasseBound.lean").write_text("-- edited\n")
        self.assertEqual((self.d / "projects/HasseWeil/HasseWeil/HasseBound.lean").read_text(), "-- edited\n")

    def test_gate2_reads_the_record_from_inside_its_project(self):
        with tempfile.TemporaryDirectory() as t:
            f = Path(t) / "r.jsonl"
            f.write_text(json.dumps({"name": "n", "library": "aintlib", "source_url": f"https://github.com/o/r/blob/{AINT['commit']}/projects/HasseWeil/HasseWeil/HasseBound.lean#L1"}) + "\n")
            self.assertEqual(gate2_batch.tentative_entries([str(f)])["n"]["sourcePath"], "HasseWeil/HasseBound.lean")

    def test_only_links_were_added(self):
        real = sorted(p.relative_to(self.d).as_posix() for p in self.d.rglob("*") if p.is_file() and not p.is_symlink())
        self.assertEqual(real, sorted(AINT["lean_files"]))


class Lists(unittest.TestCase):
    def test_a_name_in_two_source_folders_stops(self):
        with tempfile.TemporaryDirectory() as t:
            d = Path(t)
            for s in ("a", "b"):
                (d / s / "M").mkdir(parents=True)
                (d / s / "M" / "X.lean").write_text("--\n")
            with self.assertRaises(ValueError):
                link_srcdir.link(d, ["a", "b"], ["M"])

    def test_a_folder_without_lean_is_not_linked(self):
        with tempfile.TemporaryDirectory() as t:
            d = Path(t)
            (d / "a" / "M").mkdir(parents=True)
            (d / "a" / "M" / "X.lean").write_text("--\n")
            (d / "a" / "docs").mkdir()
            (d / "a" / "docs" / "r.md").write_text("x")
            (d / "docs").mkdir()  # the repository's own: no clash, it holds no Lean
            self.assertEqual(link_srcdir.link(d, ["a"], ["M"]), ["M"])

    def test_a_source_folder_the_project_does_not_have_stops(self):
        with tempfile.TemporaryDirectory() as t:
            d = Path(t)
            (d / "a" / "M").mkdir(parents=True)
            (d / "a" / "M" / "X.lean").write_text("--\n")
            with self.assertRaises(ValueError):
                link_srcdir.link(d, ["a", "gone"], ["M"])

    def test_every_root_must_be_found(self):
        with tempfile.TemporaryDirectory() as t:
            d = Path(t)
            (d / "a" / "M").mkdir(parents=True)
            (d / "a" / "M" / "X.lean").write_text("--\n")
            with self.assertRaises(ValueError):
                link_srcdir.link(d, ["a"], ["M", "Gone"])

    def test_a_root_named_after_its_source_folder_counts(self):
        """lean_lib Common, srcDir Common: the root is linked as its children"""
        with tempfile.TemporaryDirectory() as t:
            d = Path(t)
            (d / "Common" / "Common" / "A").mkdir(parents=True)
            (d / "Common" / "Common" / "A" / "X.lean").write_text("-- x\n")
            self.assertEqual(link_srcdir.link(d, ["Common"], ["Common"]), ["Common/A"])
            self.assertEqual((d / "Common" / "A" / "X.lean").read_text(), "-- x\n")

    def test_a_root_named_after_its_source_folder_with_no_lean_yet_counts(self):
        with tempfile.TemporaryDirectory() as t:
            d = Path(t)
            (d / "Common" / "Common").mkdir(parents=True)
            self.assertEqual(link_srcdir.link(d, ["Common"], ["Common"]), [])

    def test_srcdirs_of(self):
        self.assertEqual(link_srcdir.srcdirs_of({"srcdir": "x"}), ["x"])
        self.assertEqual(link_srcdir.srcdirs_of({"srcdir": ["x", "y"]}), ["x", "y"])
        self.assertEqual(link_srcdir.srcdirs_of({}), [])


class Refusals(unittest.TestCase):
    def test_a_folder_that_leaves_the_project(self):
        with tempfile.TemporaryDirectory() as t:
            for bad in ("../x", "a/../../b", "/etc", ""):
                with self.assertRaises(ValueError, msg=bad):
                    link_srcdir.link(Path(t), bad, ["A"])

    def test_a_root_that_is_also_at_the_top(self):
        with tempfile.TemporaryDirectory() as t:
            d = Path(t)
            (d / "src" / "A").mkdir(parents=True)
            (d / "A").mkdir()
            with self.assertRaises(ValueError):
                link_srcdir.link(d, "src", ["A"])

    def test_a_source_folder_that_is_a_link_out_of_the_project(self):
        with tempfile.TemporaryDirectory() as t, tempfile.TemporaryDirectory() as out:
            d = Path(t) / "p"
            d.mkdir()
            (Path(out) / "A").mkdir()
            (d / "src").symlink_to(out)
            with self.assertRaises(ValueError):
                link_srcdir.link(d, "src", ["A"])
            self.assertFalse((d / "A").exists())

    def test_a_root_under_the_folder_that_is_a_link_out_of_the_project(self):
        with tempfile.TemporaryDirectory() as t, tempfile.TemporaryDirectory() as out:
            d = Path(t) / "p"
            (d / "src").mkdir(parents=True)
            (Path(out) / "A.lean").write_text("-- outside\n")
            (d / "src" / "A.lean").symlink_to(Path(out) / "A.lean")
            with self.assertRaises(ValueError):
                link_srcdir.link(d, "src", ["A"])
            self.assertFalse((d / "A.lean").is_symlink())

    def test_a_root_that_is_not_one_name_at_the_top(self):
        for bad in ("../A", "a/../../A", "/abs", "..", ".", "", "x/y", "x\\y"):
            with tempfile.TemporaryDirectory() as t:
                d = Path(t) / "p"
                for present in ("src/a", "src/x/y", "A"):  # what each bad name would reach under the source folder, so that only the rule can refuse it
                    (d / present).mkdir(parents=True)
                with self.assertRaises(ValueError, msg=bad):
                    link_srcdir.link(d, "src", [bad])
                self.assertEqual(sorted(p.name for p in d.iterdir()), ["A", "src"], bad)
                self.assertEqual([p.name for p in d.parent.iterdir()], ["p"], bad)

    def test_every_root_of_the_registry_is_one_name(self):
        """the rule must not refuse a root the registry really has"""
        sources = json.loads((REPO / "sources.json").read_text())["sources"]
        for key, src in sources.items():
            for root in src.get("roots") or []:
                self.assertNotIn("/", root, key)
                self.assertNotIn(root, ("", ".", ".."), key)

    def test_a_link_inside_the_project_is_followed(self):
        with tempfile.TemporaryDirectory() as t:
            d = Path(t)
            (d / "real" / "A").mkdir(parents=True)
            (d / "src").symlink_to("real")
            self.assertEqual(link_srcdir.link(d, "src", ["A"]), ["A"])

    def test_no_root_under_the_folder(self):
        with tempfile.TemporaryDirectory() as t:
            (Path(t) / "src").mkdir()
            with self.assertRaises(ValueError):
                link_srcdir.link(Path(t), "src", ["A"])

    def test_a_root_that_is_one_file_under_the_folder(self):
        with tempfile.TemporaryDirectory() as t:
            d = Path(t)
            (d / "src").mkdir()
            (d / "src" / "A.lean").write_text("-- a\n")
            self.assertEqual(link_srcdir.link(d, "src", ["A"]), ["A.lean"])
            self.assertEqual((d / "A.lean").read_text(), "-- a\n")


class RepositoryLinks(unittest.TestCase):
    def test_a_record_of_a_source_folder_is_read_as_its_module(self):
        with tempfile.TemporaryDirectory() as t:
            f = Path(t) / "r.jsonl"
            p = next(iter(RECORDS))
            f.write_text(json.dumps({"name": "n", "library": "classfieldtheory-yamaguchi", "source_url": f"https://github.com/o/r/blob/2eb22d6485af45f29c5219de6c49f196a61c4f49/{p}#L1"}) + "\n")
            self.assertEqual(gate2_batch.tentative_entries([str(f)])["n"]["sourcePath"], p[len("Lean4/") :])

    def test_subdir_libraries_are_unchanged(self):
        s = gate2_batch.subdirs_of_libraries()
        self.assertEqual(s["openai-math"], ["lean"])
        self.assertEqual(s["fagin"], ["proofs"])
        self.assertEqual(s["classfieldtheory-yamaguchi"], ["Lean4"])
        self.assertEqual(len(s["aintlib"]), 11)

    def test_a_library_with_no_source_folder_is_left_alone(self):
        with tempfile.TemporaryDirectory() as t:
            r = subprocess.run([sys.executable, str(HERE.parent / "link_srcdir.py"), "prime-gaps-186", t], capture_output=True, text=True)
            self.assertEqual((r.returncode, list(Path(t).iterdir())), (0, []), r.stderr)

    def test_the_registry_entry_is_the_real_folder(self):
        src = json.loads((REPO / "sources.json").read_text())["sources"]["classfieldtheory-yamaguchi"]
        self.assertEqual((src["srcdir"], src["roots"]), ("Lean4", ROOTS))


class EveryCloneMakesTheLinks(unittest.TestCase):
    def test_every_job_that_clones_the_library(self):
        seen = 0
        for name in ("bump-library.yml", "bump-sharded.yml", "bump-shard.yml"):
            doc = yaml.safe_load((REPO / ".github" / "workflows" / name).read_text(encoding="utf-8"))
            for job, spec in doc["jobs"].items():
                for step in spec.get("steps", []):
                    run = step.get("run", "")
                    if isinstance(run, str) and 'git clone -q --filter=blob:none "$repo" lib' in run:
                        seen += 1
                        self.assertIn('python3 scripts/bump/link_srcdir.py "$KEY" lib', run, f"{name} {job}")
                        self.assertLess(run.index('ln -s "lib-repo/$sub" lib'), run.index("link_srcdir.py"), "the links go inside the Lake project")
        self.assertGreaterEqual(seen, 3)


if __name__ == "__main__":
    unittest.main()
