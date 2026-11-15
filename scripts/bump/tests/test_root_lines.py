"""A sharded bundle moves its root declarations to Tengoku.<Library> on the FIRST cut (bump-sharded.yml: root_lines.py, then scope_rewrite.py --roots-file --qualify-roots).

The real case: flt-anthropic parts 2 and 3 (tengoku #838, #839, 15 Nov 2026) shipped 26 written root names (`eisensteinScattering`, `CartierDual`, …) because bump-sharded qualified
roots only on a recut with `scope`; the tree fixed them afterwards (tengoku #841). The names below are theirs, and the declaration forms are the ones the tree's script had to learn
after the first version (tengoku #787, #834, #835): the factory now runs that script (roots_tree.py, a verbatim copy)."""

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import root_lines as rl  # noqa: E402

NS = "Tengoku.Toy"
A = """import Tengoku

/-- a class abbrev at the root -/
class abbrev CarriesDim (α : Type) := Inhabited α, Nonempty α

def eisensteinScattering (s : Nat) : Nat := s

alias scat := eisensteinScattering

structure Dimension where
  n : Nat

namespace Dimension
namespace Exponent
def one : Nat := 1
end Dimension.Exponent

structure CartierDual where
  n : Nat

def _root_.CartierDual.x : Nat := 2

instance : Inhabited Nat := ⟨0⟩

notation "ℝ²" => Nat × Nat
"""
B = """import Tengoku
import Tengoku.Toy.Toy.A

theorem uses : eisensteinScattering 1 = 1 := rfl
"""
C = "import Tengoku\n\nnamespace Quiet\ndef q : Nat := 1\nend Quiet\n"
SIDECAR_A = [
    ["CarriesDim", 4, 4],
    ["eisensteinScattering", 6, 6],
    ["scat", 8, 8],
    ["Dimension", 10, 11],
    ["Dimension.Exponent.one", 15, 15],
    ["CartierDual", 18, 19],
    ["CartierDual.x", 21, 21],
    ["instInhabitedNat", 23, 23],
    ["«termℝ²»", 25, 25],
    ["_example", 1, 1],
]


def layout(d: Path) -> None:
    b = d / "bundle" / "Tengoku" / "Toy" / "Toy"
    b.mkdir(parents=True)
    (b / "A.lean").write_text(A)
    (b / "B.lean").write_text(B)
    (b / "C.lean").write_text(C)
    rows = [
        {"name": "eisensteinScattering", "statement": "def eisensteinScattering (s : Nat) : Nat", "module": f"{NS}.Toy.A"},
        {"name": "uses", "statement": "theorem uses : eisensteinScattering 1 = 1", "module": f"{NS}.Toy.B"},
        {"name": "Quiet.q", "statement": "def Quiet.q : Nat", "module": f"{NS}.Toy.C"},
    ]
    (d / "bundle" / "manifest.jsonl").write_text("".join(json.dumps(r, ensure_ascii=False) + "\n" for r in rows))
    side = d / "merged" / ".lake" / "build" / "lib" / "lean" / "Toy"
    side.mkdir(parents=True)
    (side / "A.olean.ranges.json").write_text(json.dumps(SIDECAR_A, ensure_ascii=False))
    (side / "B.olean.ranges.json").write_text(json.dumps([["uses", 4, 4]]))
    (side / "C.olean.ranges.json").write_text(json.dumps([["Quiet.q", 4, 4]]))


def run(*argv: str, cwd: Path) -> subprocess.CompletedProcess:
    return subprocess.run([sys.executable, *argv], cwd=cwd, capture_output=True, text=True)


class Atomic(unittest.TestCase):
    def test_one_component_names(self):
        for name in ("X", "eisensteinScattering", "instAddFoo", "«termℝ²»", "«a.b»", "«term_ ∘ _»", "CartierDual", "f'", "ℓ₂"):
            self.assertTrue(rl.atomic(name), name)

    def test_dotted_internal_and_malformed_names_are_not_roots(self):
        for name in ("A.b", "CartierDual.x", "«a».b", "_example", "_private.M.0.foo", "", "a b", "«open", None, 3, ["X"]):
            self.assertFalse(rl.atomic(name), repr(name))


class RootsOf(unittest.TestCase):
    def test_the_names_of_every_sidecar_sorted_and_once(self):
        with tempfile.TemporaryDirectory() as t:
            d = Path(t)
            layout(d)
            (d / "merged" / ".lake" / "build" / "lib" / "lean" / "Toy" / "D.olean.ranges.json").write_text(json.dumps([["uses", 1, 1], ["Z", 2, 2]]))
            self.assertEqual(rl.roots_of(d / "merged"), ["CarriesDim", "CartierDual", "Dimension", "Z", "eisensteinScattering", "instInhabitedNat", "scat", "uses", "«termℝ²»"])

    def test_no_sidecars_is_no_roots(self):
        with tempfile.TemporaryDirectory() as t:
            self.assertEqual(rl.roots_of(Path(t)), [])

    def test_a_cut_sidecar_stops_the_step(self):
        with tempfile.TemporaryDirectory() as t:
            d = Path(t)
            layout(d)
            (d / "merged" / ".lake" / "build" / "lib" / "lean" / "Toy" / "A.olean.ranges.json").write_text('[["X", 1,')
            r = run(str(HERE.parent / "root_lines.py"), "--merged", "merged", "--out", "roots.scope", cwd=d)
            self.assertNotEqual(r.returncode, 0)
            self.assertIn("is not JSON", r.stderr)
            self.assertFalse((d / "roots.scope").exists())  # nothing that reads as "no roots"

    def test_a_sidecar_that_is_not_a_list_stops_the_step(self):
        with tempfile.TemporaryDirectory() as t:
            d = Path(t)
            layout(d)
            (d / "merged" / ".lake" / "build" / "lib" / "lean" / "Toy" / "A.olean.ranges.json").write_text('{"X": 1}')
            self.assertNotEqual(run(str(HERE.parent / "root_lines.py"), "--merged", "merged", "--out", "roots.scope", cwd=d).returncode, 0)

    def test_a_symlinked_sidecar_is_not_followed(self):
        with tempfile.TemporaryDirectory() as t:
            d = Path(t)
            layout(d)
            outside = d / "outside.json"
            outside.write_text(json.dumps([["Planted", 1, 1]]))
            (d / "merged" / ".lake" / "build" / "lib" / "lean" / "Toy" / "E.olean.ranges.json").symlink_to(outside)
            self.assertNotIn("Planted", rl.roots_of(d / "merged"))

    def test_the_file_is_written_even_when_empty(self):
        with tempfile.TemporaryDirectory() as t:
            d = Path(t)
            (d / "merged").mkdir()
            r = run(str(HERE.parent / "root_lines.py"), "--merged", "merged", "--out", "roots.scope", cwd=d)
            self.assertEqual(r.returncode, 0, r.stderr)
            self.assertEqual((d / "roots.scope").read_text(), "")


class FirstCut(unittest.TestCase):
    """the two commands of the bump-sharded step, as the step runs them (no `scope`: a first cut)"""

    def cut(self, d: Path) -> dict:
        self.assertEqual(run(str(HERE.parent / "root_lines.py"), "--merged", "merged", "--out", "roots.scope", cwd=d).returncode, 0)
        r = run(str(HERE.parent / "scope_rewrite.py"), "--bundle", "bundle", "--bundle", "bundle-proposed", "--bundle", "bundle-wide", "--reexport", "--leaks", "", "--roots-file", "roots.scope", "--qualify-roots", cwd=d)
        self.assertEqual(r.returncode, 0, r.stderr)
        line = next(x for x in r.stdout.splitlines() if x.startswith("bundle "))
        return json.loads(line[len("bundle ") :])

    def test_every_written_root_moves_and_the_generated_ones_are_reported(self):
        with tempfile.TemporaryDirectory() as t:
            d = Path(t)
            layout(d)
            rep = self.cut(d)["roots"]
            a = (d / "bundle" / "Tengoku" / "Toy" / "Toy" / "A.lean").read_text()
            self.assertIn(f"class abbrev _root_.{NS}.CarriesDim", a)  # tengoku #835
            self.assertIn(f"def _root_.{NS}.eisensteinScattering", a)
            self.assertIn(f"alias {NS}.scat := eisensteinScattering", a)  # tengoku #835
            self.assertIn(f"namespace {NS}.Dimension\nnamespace Exponent", a)
            self.assertIn(f"end {NS}.Dimension.Exponent", a)  # tengoku #834: the `end` that closes two scopes
            self.assertIn(f"structure _root_.{NS}.CartierDual where", a)
            self.assertIn(f"def _root_.{NS}.CartierDual.x", a)  # tengoku #787: a name spelled from the root
            self.assertEqual(rep["unresolved"], ["instInhabitedNat", "«termℝ²»"])  # nobody wrote them: the queue's scanner exempts them
            self.assertEqual(a.count("root names of this library moved to"), 1)

    def test_a_module_that_only_uses_a_root_opens_the_namespace_and_one_that_does_not_is_untouched(self):
        with tempfile.TemporaryDirectory() as t:
            d = Path(t)
            layout(d)
            self.cut(d)
            b = (d / "bundle" / "Tengoku" / "Toy" / "Toy" / "B.lean").read_text()
            self.assertIn(f"namespace {NS} end {NS} open {NS}\n", b)
            self.assertIn("eisensteinScattering 1 = 1", b)
            self.assertEqual((d / "bundle" / "Tengoku" / "Toy" / "Toy" / "C.lean").read_text(), C)

    def test_the_manifest_follows(self):
        with tempfile.TemporaryDirectory() as t:
            d = Path(t)
            layout(d)
            self.assertEqual(self.cut(d)["roots"]["manifest_records"], 2)
            rows = [json.loads(x) for x in (d / "bundle" / "manifest.jsonl").read_text().splitlines()]
            self.assertEqual([r["name"] for r in rows], [f"{NS}.eisensteinScattering", f"{NS}.uses", "Quiet.q"])

    def test_the_same_shards_give_the_same_bytes_twice(self):
        """compose and finish each cut the bundle: finish holds what it ships to the bytes verify built"""
        with tempfile.TemporaryDirectory() as t1, tempfile.TemporaryDirectory() as t2:
            out = []
            for t in (t1, t2):
                d = Path(t)
                layout(d)
                self.cut(d)
                out.append({p.relative_to(d).as_posix(): p.read_bytes() for p in sorted((d / "bundle").rglob("*")) if p.is_file()})
            self.assertEqual(out[0], out[1])

    def test_a_library_without_roots_is_left_byte_for_byte(self):
        with tempfile.TemporaryDirectory() as t:
            d = Path(t)
            b = d / "bundle" / "Tengoku" / "Toy" / "Toy"
            b.mkdir(parents=True)
            (b / "C.lean").write_text(C)
            side = d / "merged" / ".lake" / "build" / "lib" / "lean" / "Toy"
            side.mkdir(parents=True)
            (side / "C.olean.ranges.json").write_text(json.dumps([["Quiet.q", 4, 4]]))
            self.assertEqual(run(str(HERE.parent / "root_lines.py"), "--merged", "merged", "--out", "roots.scope", cwd=d).returncode, 0)
            self.assertEqual((d / "roots.scope").stat().st_size, 0)  # the step's `[ -s roots.scope ]` is false: scope_rewrite does not run
            self.assertEqual((b / "C.lean").read_text(), C)

    def test_three_thousand_names_fit_the_file_where_one_argument_would_not(self):
        with tempfile.TemporaryDirectory() as t:
            d = Path(t)
            layout(d)
            names = [f"aVeryLongRootDeclarationNameOfALargeLibraryNumber{i:05d}" for i in range(3000)]
            (d / "merged" / ".lake" / "build" / "lib" / "lean" / "Toy" / "Big.olean.ranges.json").write_text(json.dumps([[n, 1, 1] for n in names]))
            rep = self.cut(d)["roots"]
            self.assertGreater((d / "roots.scope").stat().st_size, 131072)  # more than Linux gives one argument (MAX_ARG_STRLEN)
            self.assertEqual(len(rep["unresolved"]), 3002)


class RootsFileOption(unittest.TestCase):
    def test_a_missing_file_is_no_roots_and_scope_lines_still_count(self):
        with tempfile.TemporaryDirectory() as t:
            d = Path(t)
            layout(d)
            r = run(str(HERE.parent / "scope_rewrite.py"), "--bundle", "bundle", "--leaks", "root: scat", "--roots-file", "absent.scope", "--qualify-roots", cwd=d)
            self.assertEqual(r.returncode, 0, r.stderr)
            a = (d / "bundle" / "Tengoku" / "Toy" / "Toy" / "A.lean").read_text()
            self.assertIn(f"alias {NS}.scat", a)
            self.assertIn("def eisensteinScattering", a)  # not asked for

    def test_the_file_is_not_read_without_qualify_roots(self):
        with tempfile.TemporaryDirectory() as t:
            d = Path(t)
            layout(d)
            (d / "roots.scope").write_text("root: scat\n")
            r = run(str(HERE.parent / "scope_rewrite.py"), "--bundle", "bundle", "--leaks", "", "--roots-file", "roots.scope", cwd=d)
            self.assertEqual(r.returncode, 0, r.stderr)
            self.assertEqual((d / "bundle" / "Tengoku" / "Toy" / "Toy" / "A.lean").read_text(), A)


if __name__ == "__main__":
    unittest.main()
