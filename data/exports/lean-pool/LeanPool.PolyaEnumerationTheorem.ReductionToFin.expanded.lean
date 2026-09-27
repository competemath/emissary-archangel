/-
Copyright (c) 2026 Luka Opravš. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luka Opravš
-/
module

public import Mathlib.Data.FinEnum
public import LeanPool.PolyaEnumerationTheorem.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset


-- @@ L15-22 verbatim
/-!
# Reduction to `Fin`

If we have a bijection `X → Fin n`, then the number of distinct colorings of `X` with colors in `Y`
under the group action of `G` on `X` is equal to the number of distinct colorings of `Fin n` with
colors in `Y` under the induced group action of `G` on `Fin n`. This allows us to use `Fin n`
instead of more complex types when working with numbers of distinct colorings.
-/


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-26 verbatim
universe u v w


-- @@ L28-28 verbatim
namespace LeanPool.PolyaEnumerationTheorem


-- @@ L30-30 verbatim
namespace ReductionToFin


-- @@ L32-32 verbatim
open DistinctColorings


-- @@ L34-34 verbatim
variable (X : Type u) (Y : Type v) (G : Type w) [enum : FinEnum X]


-- @@ L36-48 verbatim
/-- Given a bijection `enum.equiv : X → Fin enum.card` and a group action of `G` on `X`, construct
    a group action of `G` on `Fin enum.card` with `g • i ↦ enum.equiv (g • (enum.equiv⁻¹ i))`. -/
instance MulActionFin [Monoid G] [MulAction G X] : MulAction G (Fin (enum.card)) where
  smul := fun g i ↦ enum.equiv.1 (g • (enum.equiv.2 i))
  one_smul := by
    intro b
    change enum.equiv ((1 : G) • (enum.equiv.symm b)) = b
    rw [one_smul, enum.equiv.apply_symm_apply]
  mul_smul := by
    intro x y b
    change enum.equiv ((x * y) • enum.equiv.symm b) =
      enum.equiv (x • enum.equiv.symm (enum.equiv (y • enum.equiv.symm b)))
    rw [enum.equiv.symm_apply_apply, mul_smul]


-- @@ L50-50 verbatim
variable [Group G] [MulAction G X]


-- @@ L52-53 verbatim
private lemma smul_fin_eq (g : G) (i : Fin enum.card) :
    (g • i : Fin enum.card) = enum.equiv (g • enum.equiv.symm i) := rfl


-- @@ L55-57 verbatim
private lemma smul_inv_fin (g : G) (i : Fin enum.card) :
    enum.equiv.symm (g • i : Fin enum.card) = g • enum.equiv.symm i := by
  rw [smul_fin_eq, enum.equiv.symm_apply_apply]


-- @@ L59-60 verbatim
/-- Forward map: a coloring of `X` to a coloring of `Fin enum.card`. -/
def fwdColoring (f : X → Y) : Fin enum.card → Y := fun i => f (enum.equiv.symm i)


-- @@ L62-63 verbatim
/-- Inverse map: a coloring of `Fin enum.card` to a coloring of `X`. -/
def invColoring (f : Fin enum.card → Y) : X → Y := fun x => f (enum.equiv x)


-- @@ L65-67 verbatim
private lemma fwd_inv (f : X → Y) : invColoring X Y (fwdColoring X Y f) = f := by
  funext x
  simp [invColoring, fwdColoring]


-- @@ L69-71 verbatim
private lemma inv_fwd (f : Fin enum.card → Y) : fwdColoring X Y (invColoring X Y f) = f := by
  funext i
  simp [fwdColoring, invColoring]


-- @@ L73-79 verbatim
private lemma fwd_smul (g : G) (f : X → Y) :
    fwdColoring X Y (g • f) = g • fwdColoring X Y f := by
  funext i
  change (g • f) (enum.equiv.symm i) = (g • fwdColoring X Y f) i
  change f (g⁻¹ • enum.equiv.symm i) = (fwdColoring X Y f) (g⁻¹ • i : Fin enum.card)
  change f (g⁻¹ • enum.equiv.symm i) = f (enum.equiv.symm ((g⁻¹ • i) : Fin enum.card))
  rw [smul_inv_fin]


-- @@ L81-88 verbatim
private lemma inv_smul (g : G) (f : Fin enum.card → Y) :
    invColoring X Y (g • f) = g • invColoring X Y f := by
  funext x
  change (g • f) (enum.equiv x) = (g • invColoring X Y f) x
  change f (g⁻¹ • enum.equiv x : Fin enum.card) = (invColoring X Y f) (g⁻¹ • x)
  change f (g⁻¹ • enum.equiv x : Fin enum.card) = f (enum.equiv (g⁻¹ • x))
  change f (enum.equiv (g⁻¹ • enum.equiv.symm (enum.equiv x))) = f (enum.equiv (g⁻¹ • x))
  rw [enum.equiv.symm_apply_apply]


-- @@ L90-105 verbatim
/-- A bijection between the distinct colorings of `X` with colors in `Y` under the group action
    of `G` on `X` and the distinct colorings of `Fin enum.card` with colors in `Y` under the
    induced group action of `G` on `Fin enum.card`. -/
def equivOfQuotientOfQuotientFin :
    (Quotient (MulAction.orbitRel G (X → Y))) ≃
      (Quotient (MulAction.orbitRel G (Fin enum.card → Y))) where
  toFun := Quotient.map (fwdColoring X Y) (by
    rintro f₁ f₂ ⟨g, hg⟩
    refine ⟨g, ?_⟩
    rw [← hg, fwd_smul])
  invFun := Quotient.map (invColoring X Y) (by
    rintro f₁ f₂ ⟨g, hg⟩
    refine ⟨g, ?_⟩
    rw [← hg, inv_smul])
  left_inv := Quotient.ind fun f => by simp [fwd_inv]
  right_inv := Quotient.ind fun f => by simp [inv_fwd]


-- @@ L107-114 verbatim
/-- An instance of `Fintype` for the distinct colorings of `Fin enum.card` with colors in `Y` under
    the induced group action of `G` on `Fin enum.card`. Required by
    `numDistinctColorings_eq_numDistinctColorings_of_Fin`. -/
instance instFintypeQuotientForallFinCardOrbitRelOfForallLeanPool
    [Fintype (Quotient (MulAction.orbitRel G (X → Y)))] :
    Fintype (Quotient (MulAction.orbitRel G (Fin enum.card → Y))) :=
  Fintype.ofEquiv (Quotient (MulAction.orbitRel G (X → Y)))
    (equivOfQuotientOfQuotientFin X Y G)


-- @@ L116-122 verbatim
/-- The number of distinct colorings of `X` with colors in `Y` under the group action of `G` on
    `X` is equal to the number of distinct colorings of `Fin enum.card` with colors in `Y` under
    the induced group action of `G` on `Fin enum.card`. -/
lemma numDistinctColorings_eq_numDistinctColorings_of_Fin
    [Fintype (Quotient (MulAction.orbitRel G (X → Y)))] :
    numDistinctColorings X Y G = numDistinctColorings (Fin (enum.card)) Y G :=
  Fintype.card_congr (equivOfQuotientOfQuotientFin X Y G)


-- @@ L124-124 verbatim
end ReductionToFin


-- @@ L126-126 verbatim
end LeanPool.PolyaEnumerationTheorem
