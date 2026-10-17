"""deficient_tree.py finds the merged modules a corrected compose would extend, and the raze plan that follows; make_raze.py writes the files of that raze PR."""

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import deficient_tree  # noqa: E402
import make_raze  # noqa: E402

NS = "Fx"
P = "Tengoku.Fx."


def mod(text_imports: list[str], *theorems: str) -> bytes:
    imports = "".join(f"import {P}{i}\n" for i in text_imports)
    body = "".join(f"theorem {t} : True := trivial\n\n" for t in theorems)
    return f"import Tengoku\n{imports}\nnamespace Fx\n\n{body}end Fx\n".encode()


def files(modules: dict[str, bytes], umbrella: list[str] | None = None) -> dict[str, bytes]:
    out = {f"Tengoku/{NS}/{k}.lean": v for k, v in modules.items()}
    listed = list(modules) if umbrella is None else umbrella
    out[f"Tengoku/{NS}.lean"] = "".join(f"import {P}{k}\n" for k in listed).encode()
    return out


class Plan(unittest.TestCase):
    def tree(self):
        # A is deficient (the tree's version lacks `missing_lemma_a`), B imports A, C is fine, D is deficient but E (its importer) is not in the bundle, F imports C
        return files(
            {
                "A": mod([], "a_one"),
                "B": mod(["A"], "b_one"),
                "C": mod([], "c_one"),
                "D": mod([], "d_one"),
                "E": mod(["D"], "e_one"),
                "F": mod(["C"], "f_one"),
            }
        )

    def bundle(self):
        return files(
            {
                "A": mod([], "a_one", "missing_lemma_a"),
                "B": mod(["A"], "b_one"),
                "C": mod([], "c_one"),
                "D": mod([], "d_one", "missing_lemma_d"),
                "F": mod(["C"], "f_one"),
                "G": mod(["D"], "g_one"),  # not in the tree yet; names what D lacks below
                "H": mod(["A"], "h_one").replace(b"end Fx", b"theorem h_two : True := missing_lemma_a\n\nend Fx"),  # names what A lacks: A is razed and comes back, so H is fine
            }
        )

    def plan(self, tree=None, bundle=None):
        return deficient_tree.plan(bundle or self.bundle(), tree or self.tree(), NS)

    def test_a_module_is_deficient_when_the_bundle_declares_a_name_the_tree_does_not(self):
        p = self.plan()
        self.assertEqual(set(p["deficient"]), {P + "A", P + "D"})
        self.assertEqual(p["deficient"][P + "A"], ["Fx.missing_lemma_a"])

    def test_what_the_tree_has_and_the_bundle_lacks_is_not_a_deficiency(self):
        tree = self.tree()
        tree[f"Tengoku/{NS}/C.lean"] = mod([], "c_one", "only_in_tree")
        self.assertNotIn(P + "C", self.plan(tree=tree)["deficient"])

    def test_the_raze_is_the_fixable_modules_with_their_importers_and_nothing_a_cut_cannot_bring_back(self):
        p = self.plan()
        self.assertEqual(p["raze"], [P + "A", P + "B"])  # A, and B which imports it
        self.assertEqual(p["dependents"], [P + "B"])
        self.assertEqual(set(p["blocked"]), {P + "D"})  # E imports D and the bundle does not carry E
        self.assertEqual(p["blocked"][P + "D"], [P + "E"])
        self.assertEqual(p["lost"], [P + "E"])  # without the restraint E would go for good
        self.assertEqual(p["all"], [P + "A", P + "B", P + "D", P + "E"])

    def test_a_dependent_is_found_through_other_modules(self):
        tree = self.tree()
        tree[f"Tengoku/{NS}/F.lean"] = mod(["B"], "f_one")  # F -> B -> A
        bundle = self.bundle()
        bundle[f"Tengoku/{NS}/F.lean"] = mod(["B"], "f_one")
        self.assertIn(P + "F", self.plan(tree=tree, bundle=bundle)["raze"])

    def test_a_module_the_tree_does_not_list_is_not_in_the_tree(self):
        tree = files({"A": mod([], "a_one"), "C": mod([], "c_one")}, umbrella=["C"])  # A is a file no umbrella imports
        self.assertEqual(self.plan(tree=tree)["deficient"], {})

    def test_at_risk_modules_name_what_a_blocked_module_lacks(self):
        bundle = self.bundle()
        bundle[f"Tengoku/{NS}/G.lean"] = mod(["D"], "g_one").replace(b"end Fx", b"theorem g_two : True := missing_lemma_d\n\nend Fx")
        p = self.plan(bundle=bundle)
        self.assertEqual(p["at_risk"], [P + "G"])
        self.assertNotIn(P + "H", p["at_risk"])  # names what A lacks, and A is fixable: it comes back with the raze

    def test_a_library_that_is_not_in_the_tree_is_refused(self):
        with self.assertRaises(SystemExit):
            deficient_tree.plan(self.bundle(), {}, NS)


class MakeRaze(unittest.TestCase):
    def tree(self):
        root = Path(tempfile.mkdtemp())
        for k in ("A", "B", "C"):
            f = root / "Tengoku" / NS / f"{k}.lean"
            f.parent.mkdir(parents=True, exist_ok=True)
            f.write_text(f"import Tengoku\n-- {k}\n")
        g = root / "Tengoku" / NS / "E-F.lean"
        g.write_text("import Tengoku\n")
        (root / "Tengoku" / f"{NS}.lean").write_text(f"import {P}A\nimport {P}B\nimport {P}C\nimport {P}«E-F»\n")
        m = root / "data" / "intake" / "fx" / "manifest.jsonl"
        m.parent.mkdir(parents=True)
        m.write_text("".join(json.dumps({"name": f"n{k}", "module": P + k}) + "\n" for k in ("A", "B", "C", "«E-F»")))
        return root

    def run_make(self, root, modules):
        plan = {"raze": modules, "deficient": {modules[0]: ["Fx.x"]}}
        return make_raze.make(root, "fx", plan, "fx-1")

    def test_the_files_the_gate_expects(self):
        root = self.tree()
        r = self.run_make(root, [P + "A", P + "«E-F»"])
        self.assertEqual(r, {"modules": 2, "manifest_lines_removed": 2})
        self.assertFalse((root / "Tengoku" / NS / "A.lean").exists())
        self.assertFalse((root / "Tengoku" / NS / "E-F.lean").exists())  # a guillemet name is the file E-F.lean
        self.assertTrue((root / "Tengoku" / NS / "B.lean").exists())
        self.assertEqual((root / "Tengoku" / f"{NS}.lean").read_text(), f"import {P}B\nimport {P}C\n")
        kept = [json.loads(ln)["name"] for ln in (root / "data/intake/fx/manifest.jsonl").read_text().splitlines()]
        self.assertEqual(kept, ["nB", "nC"])
        marker = json.loads((root / "data/raze/fx-1.json").read_text())
        self.assertEqual((marker["library"], marker["modules"]), ("fx", [P + "A", P + "«E-F»"]))
        self.assertIn("lack declarations", marker["reason"])

    def test_a_plan_made_against_another_tree_is_refused_before_anything_is_written(self):
        root = self.tree()
        with self.assertRaises(SystemExit):
            self.run_make(root, [P + "B", P + "Nope"])
        self.assertFalse((root / "data" / "raze").exists())

    def test_an_empty_plan_is_refused(self):
        with self.assertRaises(SystemExit):
            make_raze.make(self.tree(), "fx", {"raze": [], "deficient": {}}, "fx-1")

    def test_the_cli_runs_over_a_plan_file(self):
        root = self.tree()
        plan = Path(tempfile.mkdtemp()) / "plan.json"
        plan.write_text(json.dumps({"raze": [P + "C"], "deficient": {P + "C": ["Fx.x"]}}))
        r = subprocess.run([sys.executable, str(HERE / "make_raze.py"), "--tree", str(root), "--lib", "fx", "--plan", str(plan), "--id", "fx-2"], capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertTrue((root / "data/raze/fx-2.json").exists())


if __name__ == "__main__":
    unittest.main()
