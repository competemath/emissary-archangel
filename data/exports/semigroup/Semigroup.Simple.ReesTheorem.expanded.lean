/-
Copyright (c) 2026 Timothy Harvey and James Mitchell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timothy Harvey
-/
import Mathlib.Algebra.Group.Equiv.Defs
import Semigroup.Simple.Basic
import Semigroup.Simple.ReesMatrix
import Semigroup.ZeroSimple.ReesTheorem


-- @@ L11-49 verbatim
/-!
# The Rees Theorem for Completely Simple Semigroups

This file proves the Rees theorem for completely simple semigroups: every completely simple
semigroup is isomorphic to a Rees matrix semigroup `M(G; I, Λ; P)` over a group `G` with an
everywhere-defined sandwich matrix `P` (and no zero). The proof adjoins a zero: `WithZero S`
is completely 0-simple and has no zero divisors, so the `Option`-valued sandwich matrix of
the 0-simple Rees theorem (`Semigroup.ZeroSimple.ReesTheorem`) is everywhere defined and the
coordinates of `toRees` on the nonzero part land in the zero-free Rees matrix semigroup.

## Main definitions

* `simpleSandwich`: the everywhere-defined sandwich matrix, with entry `colRep l * rowRep i`
  at `(l, i)` viewed in the H-class of `e`.
* `toReesSimple`: the coordinate map from a completely simple semigroup `S` to its Rees
  matrix semigroup, given by the components of `toRees` on the nonzero part of `WithZero S`.

## Main results

* `sandwich_isGreenH_of_noZeroDivisors`: in a completely 0-simple semigroup without zero
  divisors, every corner product `colRep e l * rowRep e i` is H-related to `e`.
* `toReesSimple_mul`: `toReesSimple` is multiplicative.
* `toReesSimple_bijective`: `toReesSimple` is a bijection.
* `rees_theorem_simple`: **the Rees theorem for completely simple semigroups**: a completely
  simple semigroup is isomorphic, as a semigroup, to a zero-free Rees matrix semigroup over
  the H-class group of a primitive idempotent.
* `rees_theorem_simple_converse`: **the converse of the Rees theorem for completely simple
  semigroups**: every zero-free Rees matrix semigroup over a group is completely simple.

## References

* [J. M. Howie, *Fundamentals of Semigroup Theory*][howie1995]

The proofs formalized in this module closely follow the structure and logic
from lecture notes:

* J. D. Mitchell, *MT5863 Semigroup Theory* (lecture notes,
  University of St Andrews, 2026).
-/


-- @@ L51-51 verbatim
open scoped GreensRelations


-- @@ L53-53 verbatim
/-! ### Without zero divisors the sandwich matrix is total -/


-- @@ L55-55 verbatim
section TotalSandwich


-- @@ L57-57 verbatim
variable {S₀ : Type*} [SemigroupWithZero S₀] [NoZeroDivisors S₀]


-- @@ L59-69 expanded
/-- In a completely 0-simple semigroup without zero divisors, every corner
product `colRep * rowRep` is nonzero, hence H-related to `e`: the sandwich
matrix has no undefined entries. -/
theorem sandwich_isGreenH_of_noZeroDivisors (hS : IsCompletelyZeroSimple S₀) {e : S₀}
    (he : IsPrimitiveIdempotent e) (l : ReesLIndex e) (i : ReesRIndex e) :
    IsGreenH (colRep e l * rowRep e i) e :=
  by
  have h1 : colRep e l ≠ 0 := ne_zero_of_isGreenR (colRep_isGreenR e l) he.ne_zero
  have h2 : rowRep e i ≠ 0 := ne_zero_of_isGreenL (rowRep_isGreenL e i) he.ne_zero
  refine he.isGreenH_of_corner hS.isZeroSimple (mul_ne_zero h1 h2) ?_ ?_
  · rw [← mul_assoc, idem_mul_colRep he.isIdempotentElem]
  · rw [mul_assoc, rowRep_mul_idem he.isIdempotentElem]


-- @@ L71-76 verbatim
/-- The everywhere-defined sandwich matrix: the entry at `(l, i)` is
`colRep l * rowRep i`, as an element of the H-class of `e`. -/
noncomputable def simpleSandwich (hS : IsCompletelyZeroSimple S₀) {e : S₀}
    (he : IsPrimitiveIdempotent e) :
    ReesLIndex e → ReesRIndex e → IsGreenH.eqvClass e := fun l i =>
  ⟨colRep e l * rowRep e i, sandwich_isGreenH_of_noZeroDivisors hS he l i⟩


-- @@ L78-83 verbatim
/-- Without zero divisors the `Option`-valued sandwich matrix of the
0-simple Rees theorem is everywhere `some`. -/
theorem sandwichMatrix_eq_some (hS : IsCompletelyZeroSimple S₀) {e : S₀}
    (he : IsPrimitiveIdempotent e) (l : ReesLIndex e) (i : ReesRIndex e) :
    sandwichMatrix e l i = some (simpleSandwich hS he l i) :=
  dif_pos (sandwich_isGreenH_of_noZeroDivisors hS he l i)


-- @@ L85-85 verbatim
end TotalSandwich


-- @@ L87-87 verbatim
/-! ### The Rees theorem for completely simple semigroups -/


-- @@ L89-89 verbatim
section SimpleRees


-- @@ L91-91 verbatim
variable {S : Type*} [Semigroup S]


-- @@ L93-102 verbatim
/-- The coordinate map `S → M(G; I, Λ; P)`: the components of `toRees` on
the nonzero part of `S⁰`. -/
noncomputable def toReesSimple (hS : IsCompletelyZeroSimple (WithZero S))
    {e : WithZero S} (he : IsPrimitiveIdempotent e) (x : S) :
    ReesMatrixSimple (IsGreenH.eqvClass e) (ReesRIndex e) (ReesLIndex e)
      (simpleSandwich hS he) :=
  ⟨reesRIdxOf hS he (WithZero.coe_ne_zero (a := x)),
   ⟨(exists_hClass_coord hS he (WithZero.coe_ne_zero (a := x))).choose,
    (exists_hClass_coord hS he (WithZero.coe_ne_zero (a := x))).choose_spec.1⟩,
   reesLIdxOf hS he (WithZero.coe_ne_zero (a := x))⟩


-- @@ L104-110 verbatim
/-- On coerced elements, `toRees` is the triple of `toReesSimple`
coordinates. -/
theorem toRees_coe (hS : IsCompletelyZeroSimple (WithZero S))
    {e : WithZero S} (he : IsPrimitiveIdempotent e) (x : S) :
    toRees hS he ↑x = .elem (toReesSimple hS he x).row (toReesSimple hS he x).mid
      (toReesSimple hS he x).col :=
  toRees_of_ne_zero hS he WithZero.coe_ne_zero


-- @@ L112-126 verbatim
/-- **Multiplicativity** of `toReesSimple`, inherited from `toRees_mul`
(products of nonzero elements of `S⁰` are nonzero, so the zero cases of the
Rees matrix product never arise). -/
theorem toReesSimple_mul (hS : IsCompletelyZeroSimple (WithZero S))
    {e : WithZero S} (he : IsPrimitiveIdempotent e) (x y : S) :
    letI : Group (IsGreenH.eqvClass e) := he.isIdempotentElem.hClassGroup
    toReesSimple hS he (x * y) = toReesSimple hS he x * toReesSimple hS he y := by
  letI : Group (IsGreenH.eqvClass e) := he.isIdempotentElem.hClassGroup
  have hmul : toRees hS he (↑x * ↑y) = toRees hS he ↑x * toRees hS he ↑y :=
    toRees_mul hS he ↑x ↑y
  rw [← WithZero.coe_mul, toRees_coe hS he (x * y), toRees_coe hS he x,
    toRees_coe hS he y,
    ReesMatrix.elem_mul_of_some (sandwichMatrix_eq_some hS he _ _)] at hmul
  injection hmul with h1 h2 h3
  exact ReesMatrixSimple.ext h1 h2 h3


-- @@ L128-151 verbatim
/-- `toReesSimple` is a bijection, inherited from `toRees_bijective`. -/
theorem toReesSimple_bijective (hS : IsCompletelyZeroSimple (WithZero S))
    {e : WithZero S} (he : IsPrimitiveIdempotent e) :
    Function.Bijective (toReesSimple hS he) := by
  letI : Group (IsGreenH.eqvClass e) := he.isIdempotentElem.hClassGroup
  constructor
  · -- injectivity: equal coordinates force equal images under `toRees`
    intro a b hab
    have h : toRees hS he ↑a = toRees hS he ↑b := by
      rw [toRees_coe hS he a, toRees_coe hS he b, hab]
    exact WithZero.coe_inj.mp ((toRees_bijective hS he).1 h)
  · -- surjectivity: a preimage under `toRees` of a triple is nonzero
    rintro ⟨i, g, l⟩
    obtain ⟨z, hz⟩ := (toRees_bijective hS he).2 (ReesMatrix.elem i g l)
    have h0 : toRees hS he 0 = 0 := toRees_zero hS he
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [h0] at hz
      exact ReesMatrix.zero_ne_elem hz
    obtain ⟨x, rfl⟩ := WithZero.ne_zero_iff_exists.mp hz0
    refine ⟨x, ?_⟩
    have h := (toRees_coe hS he x).symm.trans hz
    injection h with h1 h2 h3
    exact ReesMatrixSimple.ext h1 h2 h3


-- @@ L153-171 verbatim
/-- **The Rees theorem for completely simple semigroups**: a completely
simple semigroup is isomorphic (as a semigroup) to a zero-free Rees matrix
semigroup over the H-class group of a primitive idempotent, with an
everywhere-defined sandwich matrix. -/
theorem rees_theorem_simple (hS : IsCompletelySimple S) {e : S}
    (he : IsSimplePrimitiveIdempotent e) :
    letI : Group (IsGreenH.eqvClass (e : WithZero S)) :=
      he.isPrimitiveIdempotent_withZero.isIdempotentElem.hClassGroup
    Nonempty (S ≃* ReesMatrixSimple (IsGreenH.eqvClass (e : WithZero S))
      (ReesRIndex (e : WithZero S)) (ReesLIndex (e : WithZero S))
      (simpleSandwich hS.isCompletelyZeroSimple_withZero
        he.isPrimitiveIdempotent_withZero)) := by
  letI : Group (IsGreenH.eqvClass (e : WithZero S)) :=
    he.isPrimitiveIdempotent_withZero.isIdempotentElem.hClassGroup
  refine ⟨⟨Equiv.ofBijective _
    (toReesSimple_bijective hS.isCompletelyZeroSimple_withZero
      he.isPrimitiveIdempotent_withZero), fun x y => ?_⟩⟩
  exact toReesSimple_mul hS.isCompletelyZeroSimple_withZero
    he.isPrimitiveIdempotent_withZero x y


-- @@ L173-173 verbatim
end SimpleRees


-- @@ L175-175 verbatim
/-! ### The converse of the Rees theorem for completely simple semigroups -/


-- @@ L177-177 verbatim
section SimpleConverse


-- @@ L179-179 verbatim
open ReesMatrixSimple


-- @@ L181-181 verbatim
variable {G : Type*} [Group G] {I Λ : Type*} {P : Λ → I → G}


-- @@ L183-206 verbatim
/-- A zero-free Rees matrix semigroup over a group is simple: every element is
recovered from any other by translations on both sides, since every sandwich
entry is invertible in `G`. -/
theorem reesMatrixSimple_isSimple [Nonempty I] [Nonempty Λ] :
    IsSimple (ReesMatrixSimple G I Λ P) := by
  obtain ⟨i₀⟩ := ‹Nonempty I›
  obtain ⟨l₀⟩ := ‹Nonempty Λ›
  refine ⟨⟨⟨i₀, 1, l₀⟩⟩, fun T hT => ?_⟩
  obtain ⟨⟨a, ha⟩, hcl⟩ := hT
  obtain ⟨i, g, l⟩ := a
  ext y
  obtain ⟨j, b, m⟩ := y
  simp only [Set.mem_univ, iff_true]
  -- `⟨j, b, m⟩` is recovered from the member `⟨i, g, l⟩` by two translations
  have h1 : (⟨j, b * (P l₀ i * g * P l j)⁻¹, l₀⟩ * ⟨i, g, l⟩ :
      ReesMatrixSimple G I Λ P) ∈ T :=
    (hcl _ ha _).1
  have h2 : (⟨j, b * (P l₀ i * g * P l j)⁻¹, l₀⟩ * ⟨i, g, l⟩ :
      ReesMatrixSimple G I Λ P) * ⟨j, 1, m⟩ ∈ T :=
    (hcl _ h1 _).2
  have heq : (⟨j, b * (P l₀ i * g * P l j)⁻¹, l₀⟩ * ⟨i, g, l⟩ :
      ReesMatrixSimple G I Λ P) * ⟨j, 1, m⟩ = ⟨j, b, m⟩ := by
    simp [mul_def, mul_assoc]
  rwa [heq] at h2


-- @@ L208-228 verbatim
/-- Every element `⟨i, (P l i)⁻¹, l⟩` is a primitive idempotent of the zero-free
Rees matrix semigroup. -/
theorem reesMatrixSimple_isSimplePrimitiveIdempotent (i : I) (l : Λ) :
    IsSimplePrimitiveIdempotent (⟨i, (P l i)⁻¹, l⟩ : ReesMatrixSimple G I Λ P) := by
  constructor
  · -- idempotency: the middle coordinate is `(P l i)⁻¹ * P l i * (P l i)⁻¹`
    have h : (⟨i, (P l i)⁻¹, l⟩ * ⟨i, (P l i)⁻¹, l⟩ : ReesMatrixSimple G I Λ P) =
        ⟨i, (P l i)⁻¹, l⟩ := by
      simp [mul_def]
    exact h
  · rintro ⟨j, b, m⟩ hf hef hfe
    -- `e * f = f` forces the row of `f` to be `i`; `f * e = f` forces its column to be `l`
    have h1 : i = j := congrArg ReesMatrixSimple.row hef
    subst h1
    have h3 : l = m := congrArg ReesMatrixSimple.col hfe
    subst h3
    -- idempotency of `f` pins its middle coordinate to `(P l i)⁻¹`
    have hmid : b * P l i * b = b := congrArg ReesMatrixSimple.mid hf
    have hpb : P l i * b = 1 :=
      mul_left_cancel (a := b) (by rw [← mul_assoc, hmid, mul_one])
    rw [(inv_eq_of_mul_eq_one_right hpb).symm]


-- @@ L230-237 verbatim
/-- **The converse of the Rees theorem for completely simple semigroups**: every
zero-free Rees matrix semigroup over a group is completely simple. -/
theorem rees_theorem_simple_converse [Nonempty I] [Nonempty Λ] :
    IsCompletelySimple (ReesMatrixSimple G I Λ P) := by
  obtain ⟨i⟩ := ‹Nonempty I›
  obtain ⟨l⟩ := ‹Nonempty Λ›
  exact ⟨reesMatrixSimple_isSimple,
    ⟨⟨i, (P l i)⁻¹, l⟩, reesMatrixSimple_isSimplePrimitiveIdempotent i l⟩⟩


-- @@ L239-239 verbatim
end SimpleConverse
