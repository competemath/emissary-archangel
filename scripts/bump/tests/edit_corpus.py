"""A corpus of Lean scoping constructs, and the metamorphic test of the factory's text edits on real Lean.

THE CLASS. The factory edits module text after Gate 2 and after the tree's build: it wraps a copy of a tree module and what imports it in a namespace (tree_dups.apply_fork_text), replaces an
import of a copy by imports of the tree's module and of what the copy imported (apply_alias_text + alias_keep), and gives declarations room (tree_repair). Each edit is supposed to leave the
MEANING of every declaration alone. Lean resolves names through namespaces, `open`s, `export`s, `variable`s, instances, scoped notation, dot notation and the import graph, so an edit that is right
for the cases its author thought of can silently change or break the others (Navier 2026-10-20/21: a bare name found through a re-opened namespace was lost after the wrap; `open _root_.X` was an
error for a namespace nothing imports; an aliased copy's own imports were lost for its importers). Reading the text cannot show it; building both texts can.

THE TEST. For every PATTERN below (a library of three modules Base <- X <- User exercising one construct) and every edit E:
    original library      Base, X, User           -> builds                      -> fingerprints F0
    E applied             (see below)             -> builds                      -> fingerprints F1
    the declarations of F1 are those of F0 (kinds and hashes of types and values; the fork's namespace is stripped by FP_STRIP).
  fork:   X and User are wrapped in `namespace ToyFork` (what choose_forks does with a copy and its importers); Base stays out.
  alias:  X is replaced by the tree's module T (an identical copy under another name), User imports T and what X imported (alias_keep).
A new construct is covered by appending a pattern; a new edit by writing its function of (pattern) -> files. Nothing else needs to change.

Run on real Lean:  python3 edit_corpus.py [--only NAME]   (from the gate2 directory of the repository, where `lake env lean` has the toolchain; CI: bundle-keep-tests.yml).
"""

from __future__ import annotations

import os
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import tree_dups as td  # noqa: E402

FORK_NS = "ToyFork"


@dataclass(frozen=True)
class Pattern:
    name: str
    why: str  # the construct, and the bug it stands for when there was one
    base: str
    x: str
    user: str
    module_system: bool = False


# `{lib}` is the library's module prefix. Proofs are `rfl`/`by decide`-free core Lean: the corpus must build in seconds and on any toolchain.
PATTERNS: list[Pattern] = [
    Pattern(
        "reopened_namespace_bare_name",
        "a bare name found through a re-opened namespace (Navier: `namespace EulerQuadraticSource` + `source`; wrapped, the namespace chain starts with the fork's)",
        "namespace ZzOne\ndef src : Nat := 1\ntheorem src_eq : src = 1 := rfl\nend ZzOne\n",
        "import Tengoku.{lib}.Base\n\nnamespace ZzOne\ndef foo : Nat := src\ntheorem foo_eq : foo = 1 := src_eq\nend ZzOne\n",
        "import Tengoku.{lib}.X\n\nnamespace ZzOne\ndef bar : Nat := foo + src\ntheorem bar_eq : bar = 2 := rfl\nend ZzOne\n",
    ),
    Pattern(
        "namespace_no_import_declares",
        "a namespace the file declares for the first time: `open _root_.X` alone is an error (Navier: Euler.QuadraticSourceLimit)",
        "def zzBase2 : Nat := 1\n",
        "import Tengoku.{lib}.Base\n\nnamespace ZzFresh\ndef f : Nat := zzBase2 + 1\nend ZzFresh\n",
        "import Tengoku.{lib}.X\n\nopen ZzFresh in\ndef zzG : Nat := f\n",
    ),
    Pattern(
        "dotted_namespace_parent_names",
        "`namespace A.B.C` sees the names of A.B and A, and a relative qualified name from the importer",
        "namespace ZzA.ZzB\ndef x : Nat := 1\nend ZzA.ZzB\n",
        "import Tengoku.{lib}.Base\n\nnamespace ZzA.ZzB.ZzC\ndef y : Nat := x + 1\nend ZzA.ZzB.ZzC\n",
        "import Tengoku.{lib}.X\n\nnamespace ZzA\ndef z : Nat := ZzB.ZzC.y\nend ZzA\n",
    ),
    Pattern(
        "open_namespace_command",
        "`open N` at the top of a file, N declared by an import",
        "namespace ZzFour\ndef src4 : Nat := 4\nend ZzFour\n",
        "import Tengoku.{lib}.Base\n\nopen ZzFour\ndef zzH : Nat := src4\n",
        "import Tengoku.{lib}.X\n\nopen ZzFour\ndef zzH2 : Nat := zzH + src4\n",
    ),
    Pattern(
        "open_in",
        "`open N in` in front of one declaration",
        "namespace ZzFive\ndef src5 : Nat := 5\nend ZzFive\n",
        "import Tengoku.{lib}.Base\n\nopen ZzFive in\ndef zzH5 : Nat := src5\n",
        "import Tengoku.{lib}.X\n\nopen ZzFive in\ndef zzH52 : Nat := zzH5 + src5\n",
    ),
    Pattern(
        "open_namespace_both_sides",
        "`open N` of a namespace whose names are declared by a wrapped module AND by one that is not: the original had one merged N (Navier: `open EulerCylinderSobolevSpace`; found by this corpus, "
        "wrapped, only the fork's N was opened and `srcD` was lost)",
        "namespace ZzDual\ndef srcD : Nat := 1\nend ZzDual\n",
        "import Tengoku.{lib}.Base\n\nnamespace ZzDual\ndef fooD : Nat := srcD + 1\nend ZzDual\n",
        "import Tengoku.{lib}.X\n\nopen ZzDual\ndef zzUserD : Nat := fooD + srcD\n",
    ),
    Pattern(
        "open_in_namespace_both_sides",
        "`open N in` over one declaration, N declared on both sides",
        "namespace ZzDualIn\ndef srcE : Nat := 1\nend ZzDualIn\n",
        "import Tengoku.{lib}.Base\n\nnamespace ZzDualIn\ndef fooE : Nat := srcE + 1\nend ZzDualIn\n",
        "import Tengoku.{lib}.X\n\nopen ZzDualIn in\ndef zzUserE : Nat := fooE + srcE\n",
    ),
    Pattern(
        "open_several_namespaces_and_dotted",
        "`open A B.C` with a dotted name and two namespaces, each declared on both sides",
        "namespace ZzM\ndef m0 : Nat := 1\nend ZzM\nnamespace ZzP.ZzQ\ndef q0 : Nat := 2\nend ZzP.ZzQ\n",
        "import Tengoku.{lib}.Base\n\nnamespace ZzM\ndef m1 : Nat := m0 + 1\nend ZzM\nnamespace ZzP.ZzQ\ndef q1 : Nat := q0 + 1\nend ZzP.ZzQ\n",
        "import Tengoku.{lib}.X\n\nopen ZzM ZzP.ZzQ\ndef zzUserM : Nat := m1 + m0 + q1 + q0\n",
    ),
    Pattern(
        "open_relative_namespace_inside_a_namespace",
        "`open B` inside `namespace A` meaning A.B, B declared by the base",
        "namespace ZzR.ZzS\ndef r0 : Nat := 1\nend ZzR.ZzS\n",
        "import Tengoku.{lib}.Base\n\nnamespace ZzR\nopen ZzS\ndef r1 : Nat := r0 + 1\nend ZzR\n",
        "import Tengoku.{lib}.X\n\nnamespace ZzR\nopen ZzS\ndef r2 : Nat := r1 + r0\nend ZzR\n",
    ),
    Pattern(
        "section_variable",
        "`variable` inside a section, an explicit binder added to the definitions",
        "def zzBase6 : Nat := 6\n",
        "import Tengoku.{lib}.Base\n\nsection\nvariable (n : Nat)\ndef zzAddn : Nat := n + zzBase6\ntheorem zzAddn_zero : zzAddn 0 = zzBase6 := rfl\nend\n",
        "import Tengoku.{lib}.X\n\ndef zzTwice : Nat := zzAddn 1 + zzAddn 2\n",
    ),
    Pattern(
        "structure_protected_dot_notation",
        "dot notation finds `ZzS.double` through the structure's name, a `protected` def is not found by its short name",
        "structure ZzS where\n  n : Nat\n\nprotected def ZzS.double (s : ZzS) : Nat := 2 * s.n\n",
        "import Tengoku.{lib}.Base\n\ndef zzUseS (s : ZzS) : Nat := s.double\n",
        "import Tengoku.{lib}.X\n\ntheorem zzUseS_three : zzUseS ⟨3⟩ = 6 := rfl\n",
    ),
    Pattern(
        "instances_across_modules",
        "a class and an instance in the base, a second instance in X, instance search in the importer (Navier recut 2026-10-21: the search is bigger in a bigger environment)",
        "class ZzC (α : Type) where\n  val : Nat\n\ninstance : ZzC Nat := ⟨7⟩\n",
        "import Tengoku.{lib}.Base\n\ndef zzV : Nat := ZzC.val Nat\ninstance : ZzC Bool := ⟨8⟩\n",
        "import Tengoku.{lib}.X\n\ndef zzW : Nat := ZzC.val Bool + zzV\ntheorem zzW_eq : zzW = 15 := rfl\n",
    ),
    Pattern(
        "scoped_notation",
        "a scoped notation opened where it is used",
        "namespace ZzN\nscoped notation \"⟪\" a \"⟫\" => a + 1\nend ZzN\n",
        "import Tengoku.{lib}.Base\n\nopen ZzN in\ndef zzK : Nat := ⟪2⟫\n",
        "import Tengoku.{lib}.X\n\nopen ZzN in\ndef zzK2 : Nat := ⟪zzK⟫\n",
    ),
    Pattern(
        "export_alias",
        "`export N (e)` makes `e` an alias at the root",
        "namespace ZzE\ndef e : Nat := 5\nend ZzE\nexport ZzE (e)\n",
        "import Tengoku.{lib}.Base\n\ndef zzU : Nat := e\n",
        "import Tengoku.{lib}.X\n\ndef zzU2 : Nat := zzU + e\n",
    ),
    Pattern(
        "private_definition",
        "a `private` def is mangled with its module's name and used inside it",
        "def zzBase11 : Nat := 1\n",
        "import Tengoku.{lib}.Base\n\nprivate def zzHid : Nat := zzBase11 + 2\ndef zzShows : Nat := zzHid\n",
        "import Tengoku.{lib}.X\n\ndef zzShows2 : Nat := zzShows + 1\n",
    ),
    Pattern(
        "simp_attribute_across_modules",
        "a `@[simp]` lemma of the base used by `simp` in X and in the importer",
        "def zzBase12 : Nat := 1\n@[simp] theorem zzBase12_eq : zzBase12 = 1 := rfl\n",
        "import Tengoku.{lib}.Base\n\ntheorem zzT12 : zzBase12 + 0 = 1 := by simp\n",
        "import Tengoku.{lib}.X\n\ntheorem zzT12b : zzBase12 + 1 = 2 := by simp\n",
    ),
    Pattern(
        "universe_and_implicit_variable",
        "`universe u` and an implicit `variable` of the file",
        "def zzBase13 : Nat := 1\n",
        "import Tengoku.{lib}.Base\n\nuniverse u\nvariable {α : Type u}\ndef zzIdf (a : α) : α := a\n",
        "import Tengoku.{lib}.X\n\ndef zzUseid : Nat := zzIdf zzBase13\n",
    ),
    Pattern(
        "inductive_and_match",
        "an inductive type with constructors resolved through the expected type in the importer",
        "inductive ZzT where\n  | a\n  | b\n\ndef zzBase14 : Nat := 1\n",
        "import Tengoku.{lib}.Base\n\ndef zzF : ZzT → Nat\n  | .a => 1\n  | .b => 2\n",
        "import Tengoku.{lib}.X\n\ntheorem zzF_b : zzF .b = 2 := rfl\n",
    ),
    Pattern(
        "scope_left_open_at_eof",
        "a namespace that the file never closes (Lean closes it at the end; 4,049 of lean-pool's 4,131 files leave a `public section` open)",
        "namespace ZzOpen\ndef o : Nat := 1\nend ZzOpen\n",
        "import Tengoku.{lib}.Base\n\nnamespace ZzOpen\ndef p : Nat := o + 1\n",
        "import Tengoku.{lib}.X\n\nnamespace ZzOpen\ndef q : Nat := p + 1\n",
    ),
    Pattern(
        "two_reopenings_in_one_file",
        "a namespace reopened twice in the file, each block using the names of the import",
        "namespace ZzTwo\ndef s1 : Nat := 1\ndef s2 : Nat := 2\nend ZzTwo\n",
        "import Tengoku.{lib}.Base\n\nnamespace ZzTwo\ndef a1 : Nat := s1\nend ZzTwo\n\ndef zzMid : Nat := ZzTwo.a1\n\nnamespace ZzTwo\ndef a2 : Nat := s2 + a1\nend ZzTwo\n",
        "import Tengoku.{lib}.X\n\nnamespace ZzTwo\ndef a3 : Nat := a2 + s1\nend ZzTwo\n",
    ),
    Pattern(
        "module_system",
        "Lean's module system (`module`, `public import`, `@[expose] public section`): 4,130 of lean-pool's 4,131 files",
        "module\n\n@[expose] public section\n\nnamespace ZzMod\ndef base_m : Nat := 1\nend ZzMod\n",
        "module\n\npublic import Tengoku.{lib}.Base\n\n@[expose] public section\n\nnamespace ZzMod\ndef m : Nat := base_m + 1\nend ZzMod\n",
        "module\n\npublic import Tengoku.{lib}.X\n\n@[expose] public section\n\nnamespace ZzMod\ndef n : Nat := m + base_m\nend ZzMod\n",
        module_system=True,
    ),
]


def files_for(p: Pattern, lib: str, *, user_imports: str | None = None) -> dict[str, str]:
    """module -> text, for the library prefix `lib` (Base, X, User)."""
    sub = lambda t: t.replace("{lib}", lib)  # noqa: E731
    user = sub(p.user)
    if user_imports:
        user = user.replace(f"Tengoku.{lib}.X", user_imports)
    return {"Base": sub(p.base), "X": sub(p.x), "User": user}


def fork_variant(p: Pattern) -> dict[str, str]:
    """X and User wrapped in the fork's namespace (what tree_dups.choose_forks does with a copy and what imports it); Base stays out. Modules live under `<lib>F`, importing each other there."""
    f = files_for(p, "E", user_imports="Tengoku.EF.X")
    base_imports = {"X": f["X"], "User": f["User"]}
    out = {}
    for m, text in base_imports.items():
        wrapped = td.apply_fork_text(text, FORK_NS)
        if wrapped is None:
            raise ValueError(f"{p.name}: {m} cannot be wrapped")
        out[m] = wrapped
    return out


def alias_variant(p: Pattern) -> tuple[dict[str, str], dict[str, str]]:
    """(the tree's module T: an identical copy of X under another name, the importer User as the alias edit leaves it: it imports T and what X imported)"""
    orig = files_for(p, "E")
    tree_x = orig["X"]
    aliases = {"Tengoku.E.X": ["Tengoku.ET.X"]}
    keep = td.alias_keep(aliases, {"Tengoku.E.X": orig["X"]})
    user = td.apply_alias_text(orig["User"], td.with_kept(aliases, keep))
    return {"X": tree_x}, {"User": user}


class Lean:
    """real Lean from the repository's gate2 project: `lake env lean`"""

    def __init__(self, project: Path):
        self.project = project
        self.d = Path(tempfile.mkdtemp())
        self.src, self.out = self.d / "src", self.d / "oleans"
        self.lp = f"{self.out}:{self.env('printenv', 'LEAN_PATH').stdout.strip()}"

    def env(self, *cmd: str, extra: dict | None = None) -> subprocess.CompletedProcess:
        return subprocess.run(["lake", "env", *cmd], cwd=self.project, capture_output=True, text=True, env={**os.environ, **(extra or {})})

    def put(self, module: str, text: str) -> None:
        f = self.src / (module.replace(".", "/") + ".lean")
        f.parent.mkdir(parents=True, exist_ok=True)
        f.write_text(text, encoding="utf-8")
        (self.out / (module.replace(".", "/") + ".olean")).parent.mkdir(parents=True, exist_ok=True)

    def build(self, module: str) -> subprocess.CompletedProcess:
        rel = module.replace(".", "/")
        return subprocess.run(["lake", "env", "env", f"LEAN_PATH={self.lp}", "lean", f"--root={self.src}", "-o", str(self.out / (rel + ".olean")), str(self.src / (rel + ".lean"))],
                              cwd=self.project, capture_output=True, text=True)

    def fingerprints(self, modules: list[str], strip: str = "") -> dict:
        lst = self.d / "list.txt"
        lst.write_text("".join(m + "\n" for m in modules))
        script = self.project.parent / "scripts" / "bump" / "ModuleFingerprint.lean"
        p = subprocess.run(["lake", "env", "env", f"LEAN_PATH={self.lp}", f"FP_STRIP={strip}", "lean", "--run", str(script), str(lst)], cwd=self.project, capture_output=True, text=True)
        parsed = td.parse_fp(p.stdout)
        if parsed.errors:
            raise AssertionError(f"fingerprint errors: {parsed.errors}\n{p.stderr[-800:]}")
        return parsed


def check_pattern(lean: Lean, p: Pattern) -> list[str]:
    """the problems found for one pattern, as sentences; [] when both edits leave every declaration as it was"""
    problems: list[str] = []
    orig = files_for(p, "E")
    for m, text in orig.items():
        lean.put(f"Tengoku.E.{m}", text)
    for m in ("Base", "X", "User"):
        r = lean.build(f"Tengoku.E.{m}")
        if r.returncode:
            return [f"{p.name}: the ORIGINAL does not build ({m}): the pattern is wrong, not the edit:\n{(r.stdout + r.stderr)[-700:]}"]
    f0 = lean.fingerprints([f"Tengoku.E.{m}" for m in ("X", "User")])
    for m in ("X", "User"):
        if not dict(f0[f"Tengoku.E.{m}"]):  # a comparison of two empty fingerprints proves nothing
            return [f"{p.name}: the fingerprint of the original {m} is empty: the pattern declares nothing, the comparison would be vacuous"]

    # fork
    for m, text in fork_variant(p).items():
        lean.put(f"Tengoku.EF.{m}", text)
    for m in ("X", "User"):
        r = lean.build(f"Tengoku.EF.{m}")
        if r.returncode:
            problems.append(f"{p.name} / fork: {m} does not build once wrapped in {FORK_NS}:\n{(r.stdout + r.stderr)[-700:]}")
            break
    else:
        f1 = lean.fingerprints(["Tengoku.EF.X", "Tengoku.EF.User"], strip=FORK_NS)
        for m, m1 in (("X", "EF.X"), ("User", "EF.User")):
            a, b = dict(f0[f"Tengoku.E.{m}"]), dict(f1[f"Tengoku.{m1}"])
            if a != b:
                problems.append(f"{p.name} / fork: {m} declares other things once wrapped: only before {sorted(set(a) - set(b))}, only after {sorted(set(b) - set(a))}, differing {sorted(k for k in set(a) & set(b) if a[k] != b[k])}")

    # alias
    tree, imp = alias_variant(p)
    for m, text in tree.items():
        lean.put(f"Tengoku.ET.{m}", text)
    r = lean.build("Tengoku.ET.X")
    if r.returncode:
        problems.append(f"{p.name} / alias: the tree's module does not build:\n{(r.stdout + r.stderr)[-500:]}")
    else:
        lean.put("Tengoku.EA.User", imp["User"])
        r = lean.build("Tengoku.EA.User")
        if r.returncode:
            problems.append(f"{p.name} / alias: the importer does not build on the tree's module:\n{(r.stdout + r.stderr)[-700:]}")
        else:
            f1 = lean.fingerprints(["Tengoku.EA.User"])
            a, b = dict(f0["Tengoku.E.User"]), dict(f1["Tengoku.EA.User"])
            if a != b:
                problems.append(f"{p.name} / alias: the importer declares other things on the tree's module: before-only {sorted(set(a) - set(b))}, after-only {sorted(set(b) - set(a))}, differing {sorted(k for k in set(a) & set(b) if a[k] != b[k])}")
    return problems


def main(argv: list[str]) -> int:
    only = argv[argv.index("--only") + 1] if "--only" in argv else ""
    lean = Lean(Path.cwd())
    bad: list[str] = []
    for p in PATTERNS:
        if only and p.name != only:
            continue
        found = check_pattern(lean, p)
        print(("OK   " if not found else "FAIL ") + p.name, flush=True)
        bad += found
    if bad:
        print("\n" + "\n\n".join(bad))
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
