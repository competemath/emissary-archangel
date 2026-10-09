import json
import random
import re
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import bundle_layers as bl  # noqa: E402
import bundle_tar  # noqa: E402

NS = "Lib"


def mod_path(name: str) -> str:
    return name.replace(".", "/") + ".lean"


def make_bundle(deps: dict[str, list[str]], unlisted=(), extra_umbrella="", records=None) -> dict[str, bytes]:
    """A bundle whose modules are `Tengoku.Lib.<name>`, importing each other as `deps` says (and the seed through `Tengoku`)."""
    files: dict[str, bytes] = {}
    listed = []
    for name, ds in deps.items():
        full = f"Tengoku.{NS}.{name}"
        body = (
            "module\n\npublic import Tengoku\n"
            + "".join(f"public import Tengoku.{NS}.{d}\n" for d in ds)
            + f"\ntheorem {name.replace('.', '_')} : True := trivial\n"
        )
        files[mod_path(full)] = body.encode()
        if name not in unlisted:
            listed.append(full)
    files[f"Tengoku/{NS}.lean"] = (extra_umbrella + "".join(f"import {m}\n" for m in sorted(listed))).encode()
    recs = records if records is not None else [{"module": f"Tengoku.{NS}.{n}", "name": n, "library": "lib"} for n in deps if n not in unlisted]
    files["manifest.jsonl"] = ("".join(json.dumps(r) + "\n" for r in recs)).encode()
    files["report.json"] = json.dumps({"library": "lib", "lint_mode": "strict", "theorems": len(recs)}).encode()
    return files


def random_dag(rnd: random.Random, n: int) -> dict[str, list[str]]:
    names = [f"M{i:03d}" for i in range(n)]
    order = names[:]
    rnd.shuffle(order)  # the names say nothing about the dependencies
    deps = {m: [] for m in names}
    for i, m in enumerate(order):
        for d in rnd.sample(order[:i], min(i, rnd.randint(0, 3))):
            deps[m].append(d)
    return deps


class Order(unittest.TestCase):
    def test_a_module_comes_after_what_it_imports(self):
        g = {"c": ["b"], "b": ["a"], "a": [], "d": ["a", "c"]}
        order = bl.topological_order(g)
        self.assertEqual(order, ["a", "b", "c", "d"])

    def test_a_cycle_is_refused(self):
        with self.assertRaises(bl.BundleError) as cm:
            bl.topological_order({"a": ["b"], "b": ["c"], "c": ["a"]})
        self.assertIn("cycle", str(cm.exception))

    def test_a_module_that_imports_itself_is_a_cycle_only_if_the_graph_says_so(self):
        # import_graph drops the self-edge, so a stray self-import cannot stop a bundle
        files = make_bundle({"A": ["A"], "B": ["A"]})
        graph = bl.import_graph(files, bl.own_modules(files, NS))
        self.assertEqual(graph[f"Tengoku.{NS}.A"], [])

    def test_the_modules_named_first_come_first(self):
        g = {"a": [], "b": ["a"], "z": []}
        self.assertEqual(bl.topological_order(g, ("z",)), ["z", "a", "b"])
        self.assertEqual(bl.topological_order(g), ["a", "b", "z"])

    def test_the_order_is_deterministic_and_complete(self):
        rnd = random.Random(1)
        g = random_dag(rnd, 60)
        self.assertEqual(
            bl.topological_order(g),
            bl.topological_order(dict(reversed(list(g.items())))),
        )
        self.assertEqual(sorted(bl.topological_order(g)), sorted(g))


class Slices(unittest.TestCase):
    def test_equal_slices_none_over_the_limit(self):
        for n, mx in ((10, 3), (9, 3), (1, 5), (300, 300), (301, 300), (4186, 300)):
            cut = bl.slices([str(i) for i in range(n)], mx)
            self.assertLessEqual(max(map(len, cut)), mx, (n, mx))
            self.assertEqual(sum(map(len, cut)), n)
            self.assertEqual(len(cut), -(-n // mx))
            self.assertLessEqual(max(map(len, cut)) - min(map(len, cut)), 1)
            self.assertEqual([x for part in cut for x in part], [str(i) for i in range(n)])  # consecutive: the order is kept

    def test_nothing_gives_no_parts_and_zero_is_refused(self):
        self.assertEqual(bl.slices([], 5), [])
        with self.assertRaises(bl.BundleError):
            bl.slices(["a"], 0)


class Plan(unittest.TestCase):
    def test_every_part_imports_only_earlier_parts_in_random_bundles(self):
        rnd = random.Random(20261005)
        for trial in range(120):
            n = rnd.randint(1, 80)
            files = make_bundle(random_dag(rnd, n))
            mx = rnd.randint(1, 25)
            with self.subTest(trial=trial, n=n, mx=mx):
                parts = bl.plan(files, NS, mx)
                bl.check(parts, files, NS)
                self.assertEqual(sum(len(p.modules) for p in parts), n)
                self.assertTrue(all(len(p.modules) <= mx for p in parts))

    def test_the_umbrella_grows_by_the_parts_imports_in_the_original_order(self):
        files = make_bundle({"A": [], "B": ["A"], "C": ["B"], "D": []})
        parts = bl.plan(files, NS, 2)
        self.assertEqual(len(parts), 2)
        original = files[f"Tengoku/{NS}.lean"].decode().splitlines()
        first = parts[0].files[f"Tengoku/{NS}.lean"].decode().splitlines()
        both = parts[1].files[f"Tengoku/{NS}.lean"].decode().splitlines()
        self.assertEqual(both, original)  # the last part's umbrella is the bundle's
        self.assertEqual(first, [ln for ln in original if ln.split()[-1] in set(parts[0].modules)])
        self.assertLess(len(first), len(both))

    def test_an_unlisted_module_is_in_a_part_but_never_in_the_umbrella(self):
        files = make_bundle({"Deps": [], "A": [], "B": ["A"]}, unlisted={"Deps"})
        parts = bl.plan(files, NS, 10)
        self.assertIn(mod_path(f"Tengoku.{NS}.Deps"), parts[0].files)

    def test_the_marker_is_in_the_first_part_wherever_its_name_sorts(self):
        # `Deps` sorts after `Aa`, `Ab`, ...: the marker is still in part 1 (the intake PR carries it)
        files = make_bundle({"Aa": [], "Ab": ["Aa"], "Ac": ["Ab"], "Deps": [], "Zz": ["Ac"]}, unlisted={"Deps"})
        parts = bl.plan(files, NS, 2)
        self.assertGreater(len(parts), 1)
        self.assertIn(mod_path(f"Tengoku.{NS}.Deps"), parts[0].files)
        self.assertTrue(all(mod_path(f"Tengoku.{NS}.Deps") not in p.files for p in parts[1:]))
        self.assertNotIn("Deps", parts[0].files[f"Tengoku/{NS}.lean"].decode())

    def test_a_file_that_is_no_module_goes_with_the_first_part_only(self):
        files = make_bundle({"A": [], "B": ["A"]})
        files["notes/MARKER.txt"] = b"a marker"
        parts = bl.plan(files, NS, 1)
        self.assertEqual([("notes/MARKER.txt" in p.files) for p in parts], [True, False])

    def test_other_umbrella_lines_stay_where_they_are(self):
        files = make_bundle({"A": [], "B": ["A"]}, extra_umbrella="-- a note\n")
        parts = bl.plan(files, NS, 1)
        self.assertTrue(all(p.files[f"Tengoku/{NS}.lean"].decode().startswith("-- a note\n") for p in parts))

    def test_manifest_lines_follow_their_modules(self):
        files = make_bundle({"A": [], "B": ["A"], "C": ["B"]})
        parts = bl.plan(files, NS, 1)
        for p in parts:
            mods = {json.loads(ln)["module"] for ln in p.manifest_lines}
            self.assertEqual(mods, set(p.modules))
            self.assertEqual(p.files["manifest.jsonl"].decode().count("\n"), len(p.manifest_lines))

    def test_a_record_of_a_module_the_bundle_lacks_is_refused(self):
        files = make_bundle({"A": []}, records=[{"module": "Tengoku.Lib.Nope", "name": "x"}])
        with self.assertRaises(bl.BundleError):
            bl.plan(files, NS, 5)

    def test_no_umbrella_or_no_module_is_refused(self):
        files = make_bundle({"A": []})
        del files[f"Tengoku/{NS}.lean"]
        with self.assertRaises(bl.BundleError):
            bl.plan(files, NS, 5)
        with self.assertRaises(bl.BundleError):
            bl.plan({f"Tengoku/{NS}.lean": b""}, NS, 5)

    def test_the_report_carries_the_digest_of_the_whole_bundle(self):
        files = make_bundle({"A": [], "B": ["A"]})
        digests = {json.loads(p.files["report.json"])["bundle_sha256"] for p in bl.plan(files, NS, 1)}
        self.assertEqual(len(digests), 1)
        other = make_bundle({"A": [], "B": ["A"], "C": []})
        self.assertNotEqual(
            digests,
            {json.loads(p.files["report.json"])["bundle_sha256"] for p in bl.plan(other, NS, 1)},
        )

    def test_the_digest_covers_every_file_not_only_the_first(self):
        files = make_bundle({"A": [], "B": ["A"]})
        changed = dict(files)
        changed["Tengoku/Lib/B.lean"] = files["Tengoku/Lib/B.lean"] + b"-- one more line\n"
        changed2 = dict(files)
        changed2["report.json"] = files["report.json"] + b" "
        digest = lambda fs: json.loads(bl.plan(fs, NS, 5)[0].files["report.json"])["bundle_sha256"]  # noqa: E731
        self.assertEqual(len({digest(files), digest(changed), digest(changed2)}), 3)

    def test_the_same_bundle_gives_the_same_parts(self):
        rnd = random.Random(7)
        files = make_bundle(random_dag(rnd, 50))
        a, b = (
            bl.plan(files, NS, 8),
            bl.plan(dict(reversed(list(files.items()))), NS, 8),
        )
        self.assertEqual([(p.modules, p.files) for p in a], [(p.modules, p.files) for p in b])

    def test_imports_that_are_not_the_librarys_own_are_not_edges(self):
        files = make_bundle({"A": [], "B": []})
        files[mod_path(f"Tengoku.{NS}.B")] += b"\n-- public import Tengoku.Lib.A\n"  # a comment after the header, not an import
        graph = bl.import_graph(files, bl.own_modules(files, NS))
        self.assertEqual(graph[f"Tengoku.{NS}.B"], [])

    def test_header_forms_all_count_as_imports(self):
        files = make_bundle({"A": [], "B": []})
        files[mod_path(f"Tengoku.{NS}.B")] = b"/- a licence\n-/\nmodule\n\npublic import Tengoku\nimport all Tengoku.Lib.A\n\ntheorem b : True := trivial\n"
        graph = bl.import_graph(files, bl.own_modules(files, NS))
        self.assertEqual(graph[f"Tengoku.{NS}.B"], [f"Tengoku.{NS}.A"])


class Check(unittest.TestCase):
    def test_a_module_in_a_part_before_what_it_imports_is_caught(self):
        files = make_bundle({"A": [], "B": ["A"]})
        parts = bl.plan(files, NS, 1)
        parts[0].modules, parts[1].modules = parts[1].modules, parts[0].modules
        with self.assertRaises(bl.BundleError) as cm:
            bl.check(parts, files, NS)
        self.assertIn("a later one", str(cm.exception))

    def test_a_module_twice_or_missing_is_caught(self):
        files = make_bundle({"A": [], "B": ["A"]})
        parts = bl.plan(files, NS, 1)
        parts[1].modules = list(parts[0].modules)
        with self.assertRaises(bl.BundleError):
            bl.check(parts, files, NS)
        parts = bl.plan(files, NS, 1)
        parts[1].modules = []
        with self.assertRaises(bl.BundleError):
            bl.check(parts, files, NS)
        parts = bl.plan(files, NS, 1)
        parts[1].modules = parts[1].modules + parts[0].modules  # every module is there, one of them twice
        with self.assertRaises(bl.BundleError) as cm:
            bl.check(parts, files, NS)
        self.assertIn("is in parts", str(cm.exception))

    def test_manifest_lines_lost_are_caught(self):
        files = make_bundle({"A": [], "B": ["A"]})
        parts = bl.plan(files, NS, 1)
        parts[1].manifest_lines = []
        with self.assertRaises(bl.BundleError):
            bl.check(parts, files, NS)


class Output(unittest.TestCase):
    def test_parts_are_written_as_directories_and_archives(self):
        files = make_bundle({"A": [], "B": ["A"], "C": ["B"]})
        parts = bl.plan(files, NS, 2)
        with tempfile.TemporaryDirectory() as d:
            out = Path(d) / "out"
            summary = bl.write_parts(parts, out, tar=True)
            self.assertEqual((summary["modules"], summary["theorems"]), (3, 3))
            self.assertEqual(
                sorted(p.name for p in out.glob("part-*") if p.is_dir()),
                ["part-001", "part-002"],
            )
            self.assertTrue((out / "part-001" / f"Tengoku/{NS}.lean").is_file())
            # the archive of a part is the canonical one of its files: the same digest from the directory
            self.assertEqual(
                summary["parts"][0]["tar_sha256"],
                bundle_tar.write_tar(
                    bundle_tar.read_dir(str(out / "part-001")),
                    str(Path(d) / "again.tar"),
                ),
            )
            self.assertEqual(json.loads((out / "plan.json").read_text())["parts"][1]["part"], 2)

    def test_the_namespace_comes_from_the_one_umbrella(self):
        self.assertEqual(bl.namespace(make_bundle({"A": []})), NS)
        with self.assertRaises(bl.BundleError):
            bl.namespace({"Tengoku/A.lean": b"", "Tengoku/B.lean": b""})


class FromTheTree(unittest.TestCase):
    """2026-10-08: causalean and complexitylib were recut (a better pruner) after their part 1 had merged. Cut from scratch, the new order put merged modules in later
    parts and new ones in part 1. With `tree_umbrella` the parts hold only the modules the tree does not have, numbered from `start`, each umbrella the tree's plus the
    imports so far: what the extend gate (tengoku scripts/ci/intake_check.py) accepts."""

    TREE = "".join(f"import Tengoku.{NS}.{m}\n" for m in ("A", "B"))

    def bundle(self):
        return make_bundle({"A": [], "B": ["A"], "C": ["B"], "D": ["C"], "E": []})

    def test_only_the_modules_the_tree_lacks_are_cut_and_numbered_from_start(self):
        files = self.bundle()
        parts = bl.plan(files, NS, 2, self.TREE, 2)
        self.assertEqual([(p.index, p.modules) for p in parts], [(2, [f"Tengoku.{NS}.C", f"Tengoku.{NS}.D"]), (3, [f"Tengoku.{NS}.E"])])
        bl.check(parts, files, NS, self.TREE)

    def test_each_umbrella_is_the_trees_plus_the_imports_so_far(self):
        parts = bl.plan(self.bundle(), NS, 1, self.TREE, 2)
        got = [p.files[f"Tengoku/{NS}.lean"].decode() for p in parts]
        self.assertEqual(got[0], self.TREE + f"import Tengoku.{NS}.C\n")
        self.assertEqual(got[1], self.TREE + f"import Tengoku.{NS}.C\nimport Tengoku.{NS}.D\n")
        self.assertEqual(got[2], self.TREE + f"import Tengoku.{NS}.C\nimport Tengoku.{NS}.D\nimport Tengoku.{NS}.E\n")

    def test_the_extend_gate_accepts_each_umbrella_against_the_tree_before_it(self):
        """The two umbrella rules of intake_check.py, restated: the lines that are not the part's new imports are the tree's lines, in order, and every new module is imported once."""
        parts = bl.plan(self.bundle(), NS, 1, self.TREE, 2)
        base = self.TREE
        for part in parts:
            head = part.files[f"Tengoku/{NS}.lean"].decode()
            wanted = {f"import {m}" for m in part.modules}
            head_lines = head.rstrip("\n").split("\n")
            self.assertEqual(sorted(ln for ln in head_lines if ln in wanted), sorted(wanted))
            self.assertEqual([ln for ln in head_lines if ln not in wanted], base.rstrip("\n").split("\n"))
            base = head  # the next part is checked against the tree this one made

    def test_the_manifest_lines_are_the_new_modules_only(self):
        parts = bl.plan(self.bundle(), NS, 10, self.TREE, 2)
        self.assertEqual([json.loads(ln)["module"] for ln in parts[0].manifest_lines], [f"Tengoku.{NS}.{m}" for m in ("C", "D", "E")])

    def test_a_module_the_tree_has_and_the_bundle_no_longer_does_is_ignored(self):
        files = self.bundle()
        parts = bl.plan(files, NS, 10, self.TREE + f"import Tengoku.{NS}.Gone\n", 2)
        self.assertEqual(parts[0].modules, [f"Tengoku.{NS}.C", f"Tengoku.{NS}.D", f"Tengoku.{NS}.E"])
        bl.check(parts, files, NS, self.TREE + f"import Tengoku.{NS}.Gone\n")

    def test_without_the_tree_nothing_changes(self):
        files = self.bundle()
        parts = bl.plan(files, NS, 10)
        self.assertEqual([(p.index, len(p.modules)) for p in parts], [(1, 5)])

    def test_the_command_line_takes_the_tree_umbrella_and_the_start(self):
        d = Path(tempfile.mkdtemp())
        for path, data in self.bundle().items():
            (d / "bundle" / path).parent.mkdir(parents=True, exist_ok=True)
            (d / "bundle" / path).write_bytes(data)
        (d / "tree.lean").write_text(self.TREE)
        bl.main(["--bundle", str(d / "bundle"), "--out", str(d / "out"), "--max-modules", "2", "--tree-umbrella", str(d / "tree.lean"), "--start", "4"])
        self.assertEqual(sorted(x.name for x in (d / "out").iterdir() if x.name.startswith("part-")), ["part-004", "part-005"])
        rep = json.loads((d / "out" / "part-004" / "report.json").read_text())
        self.assertEqual((rep["part"], rep["modules"]), (4, 2))


class WorkflowsCutPartsFromTheTree(unittest.TestCase):
    """The `from_tree` input of bump-sharded.yml and bump-library.yml reaches bundle_layers.py: the library's umbrella is fetched from tengoku main, and the next part number
    is the highest data/intake/<key>/parts/NNN.json there plus one (2 when there is none: the intake PR was part 1)."""

    WORKFLOWS = Path(__file__).resolve().parents[3] / ".github" / "workflows"

    def test_both_workflows_pass_the_tree_umbrella_and_the_start(self):
        for name in ("bump-sharded.yml", "bump-library.yml"):
            text = (self.WORKFLOWS / name).read_text()
            self.assertRegex(text, r"\n      from_tree: \{ description:", name)
            self.assertIn('FROM_TREE: "${{ inputs.from_tree }}"', text, name)
            self.assertIn("--tree-umbrella tree-umbrella-$mode.lean --start $((last + 1))", text, name)
            self.assertIn("bundle_layers.py --bundle \"$dir\" --out \"parts-$mode\" --max-modules \"$PARTS\" --tar $from_tree", text, name)

    def test_the_next_part_number_is_read_from_the_trees_parts_folder(self):
        text = (self.WORKFLOWS / "bump-sharded.yml").read_text()
        code = re.search(r"last=\$\(curl [^\n]*? \| python3 -c '([^']*)'\)", text).group(1)

        def last(answer: str) -> str:
            return subprocess.run(["python3", "-c", code], input=answer, capture_output=True, text=True).stdout.strip()

        self.assertEqual(last('[{"name":"002.json"},{"name":"003.json"}]'), "3")
        self.assertEqual(last('{"message":"Not Found","status":"404"}'), "1")  # no parts folder yet: the next part is 2
        self.assertEqual(last('[{"name":"002.json"},{"name":"README.md"}]'), "2")


if __name__ == "__main__":
    unittest.main()
