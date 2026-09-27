/-
Copyright (c) 2026 Luka Opravš. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luka Opravš
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import LeanPool.PolyaEnumerationTheorem.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset


-- @@ L15-17 verbatim
/-!
# Numbers of distinct colorings for some concrete examples
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
universe u v


-- @@ L23-23 verbatim
namespace LeanPool.PolyaEnumerationTheorem


-- @@ L25-25 verbatim
open DistinctColorings


-- @@ L27-27 verbatim
namespace TrivialGroup


-- @@ L29-31 verbatim
/-!
## Trivial group
-/


-- @@ L33-54 verbatim
/-- When using the trivial group, every coloring is equivalent only to itself. The number of
    distinct colorings is equal to the number of functions.
    `⊥ : Subgroup (X ≃ X)` denotes the trivial subgroup of `X ≃ X`. -/
lemma numDistinctColoringsOfTrivialGroup (X : Type u) (Y : Type v) [Fintype X] [Fintype Y]
    [Fintype (Quotient (MulAction.orbitRel (⊥ : Subgroup (X ≃ X)) (X → Y)))] :
    numDistinctColorings X Y (⊥ : Subgroup (X ≃ X)) = (Fintype.card Y) ^ (Fintype.card X) := by
  classical
  rw [← Fintype.card_fun]
  exact Fintype.card_congr ⟨
    Quotient.lift id (by
      intro _ _ h
      rcases h with ⟨g, rfl⟩
      rw [Subsingleton.eq_one g]
      rfl),
    fun a ↦ ⟦a⟧,
    by
      intro f
      rcases Quotient.mk_surjective f with ⟨g, rfl⟩
      simp_all,
    by
      intro
      rfl⟩


-- @@ L56-56 verbatim
end TrivialGroup



-- @@ L59-59 verbatim
namespace Necklaces


-- @@ L61-71 verbatim
/-!
## Necklaces

We interpret the elements of `Fin n` as `n` beads of a necklace, where `x` is connected to `x + 1`
and `x - 1`, computed modulo `n`. Necklaces can be rotated, but not reflected. We use the additive
group `Fin n` with multiplicative notation, because our definitions require a group with
multiplicative notation. Elements of `Multiplicative (Fin n)` are rotations of the necklace, where
`i : Fin n` rotates the necklace by `2πi/n`. We define that there is a single coloring of a
necklace with `0` beads. This is defined separately because `Multiplicative (Fin 0)` is not a
group.
-/


-- @@ L73-76 verbatim
/-- Number of distinct colorings of a necklace with `n` beads and `m` colors. -/
def numDistinctColoringsOfNecklace : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n + 1, m => numDistinctColorings (Fin (n + 1)) (Fin m) (Multiplicative (Fin (n + 1)))


-- @@ L78-78 verbatim
end Necklaces



-- @@ L81-81 verbatim
namespace Bracelets


-- @@ L83-83 verbatim
open DihedralGroup


-- @@ L85-93 verbatim
/-!
## Bracelets

We interpret the elements of `ZMod n` as `n` beads of a bracelet, where `x` is connected to
`x + 1` and `x - 1`, computed modulo `n`. Bracelets can be rotated and reflected. We use the
`DihedralGroup n`, which contains elements `r i` that rotate the bracelet by `2πi/n` and `sr i`
that rotate the bracelet by `2πi/n` and then reflect it. We define that there is a single coloring
of a bracelet with `0` beads. This is defined separately because `ZMod 0` is `ℤ` by definition.
-/


-- @@ L95-115 verbatim
/-- Action of the dihedral group on `ZMod n`. Elements of `ZMod n` are interpreted as beads of a
    bracelet. The dihedral group contains elements `r i` that rotate the bracelet by `2πi/n`, and
    elements `sr i` that rotate the bracelet by `2πi/n` and then reflect it. -/
instance MulActionBracelet (n : ℕ) : MulAction (DihedralGroup n) (ZMod n) where
  smul := fun d x ↦ match d with
                    | r i  => x + i
                    | sr i => n - 1 - (x + i)
  one_smul := by
    intro x
    change x + (0 : ZMod n) = x
    ring
  mul_smul := by
    rintro (a | a) (b | b) x
    · change x + (a + b) = (x + b) + a
      ring
    · change ((↑n : ZMod n) - 1) - (x + (b - a)) = ((↑n : ZMod n) - 1 - (x + b)) + a
      ring
    · change ((↑n : ZMod n) - 1) - (x + (a + b)) = ((↑n : ZMod n) - 1) - ((x + b) + a)
      ring
    · change x + (b - a) = ((↑n : ZMod n) - 1) - (((↑n : ZMod n) - 1) - (x + b) + a)
      ring


-- @@ L117-120 verbatim
/-- Number of distinct colorings of a bracelet with `n` beads and `m` colors. -/
def numDistinctColoringsOfBracelet : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n + 1, m => numDistinctColorings (ZMod (n + 1)) (Fin m) (DihedralGroup (n + 1))


-- @@ L122-122 verbatim
end Bracelets



-- @@ L125-125 verbatim
namespace PermutationGroup


-- @@ L127-139 verbatim
/-!
## Permutation group

We interpret the elements of `Fin n` as `n` unordered, indistinguishable objects. We use the
group `Equiv.Perm (Fin n)`, which contains all permutations of `Fin n`. Its elements permute our
objects. Since we can permute the objects in any way and still obtain an equivalent
configuration, two colorings are equivalent if and only if they assign the same number of objects
to each color. Consequently, the number of distinct colorings of `n` unordered, indistinguishable
objects with `m` colors is equal to the number of ways to separate `n` objects into `m` ordered
sets (the number of weak compositions of `n` into `m` parts), which is equal to
`(n + m - 1).choose (m - 1)` when `m > 0`. There is exactly one coloring of `0` objects with `0`
colors, and no valid colorings of more than `0` objects with `0` colors.
-/


-- @@ L141-144 verbatim
/-- The number of distinct colorings of `n` unordered, indistinguishable objects with `m`
    colors. -/
abbrev numDistinctColoringsOfPerm (n m : ℕ) : ℕ :=
  numDistinctColorings (Fin n) (Fin m) (Equiv.Perm (Fin n))


-- @@ L146-151 verbatim
/-- The number of weak compositions of `n` into `m` parts. This represents the number of ways to
    separate `n` objects into `m` ordered sets. -/
def numWeakCompositions : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | _ + 1, 0 => 0
  | n, m + 1 => (n + m).choose m


-- @@ L153-153 verbatim
end PermutationGroup


-- @@ L155-155 verbatim
end LeanPool.PolyaEnumerationTheorem
