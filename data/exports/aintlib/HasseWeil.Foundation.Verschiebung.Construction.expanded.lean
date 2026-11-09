/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Foundation.Verschiebung.FieldTower


-- @@ L8-23 verbatim
/-!
# Verschiebung pullback construction

This file constructs the witness-parametric Verschiebung pullback from an
inclusion of the multiplication-by-cardinality pullback range into the
Frobenius pullback range.

## Main definitions

* `frobeniusIsog_rangeEquiv`: the Frobenius pullback as an equivalence onto
  its range.
* `mulByInt_q_pullback_restricted`: the multiplication-by-cardinality
  pullback restricted to the Frobenius range.
* `verschiebungPullback_of_witness`: the induced Verschiebung pullback.
* `mulByInt_q_factor_via_witness`: the resulting factorisation identity.
-/


-- @@ L25-25 verbatim
open WeierstrassCurve


-- @@ L27-27 verbatim
namespace HasseWeil


-- @@ L29-29 verbatim
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

-- @@ L30-30 verbatim
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]


-- @@ L32-37 verbatim
/-- The Frobenius pullback as an `AlgEquiv` onto its range. -/
noncomputable def frobeniusIsog_rangeEquiv :
    W.toAffine.FunctionField ≃ₐ[K]
      (frobeniusIsog W).pullback.range :=
  AlgEquiv.ofInjective (frobeniusIsog W).pullback
    (frobeniusIsog W).pullback.toRingHom.injective


-- @@ L39-44 verbatim
/-- Applying `frobeniusIsog_rangeEquiv` produces the Frobenius image
as an element of the range subalgebra. -/
@[simp] theorem frobeniusIsog_rangeEquiv_apply (z : W.toAffine.FunctionField) :
    ((frobeniusIsog_rangeEquiv W) z : W.toAffine.FunctionField) =
      (frobeniusIsog W).pullback z := by
  simp only [frobeniusIsog_rangeEquiv, AlgEquiv.ofInjective_apply]


-- @@ L46-54 verbatim
/-- Codomain restriction of `(mulByInt W q).pullback` to the Frobenius range. -/
noncomputable def mulByInt_q_pullback_restricted
    (h_subset :
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
        (frobeniusIsog W).pullback.range) :
    W.toAffine.FunctionField →ₐ[K] (frobeniusIsog W).pullback.range :=
  (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.codRestrict
    (frobeniusIsog W).pullback.range
    (fun z ↦ h_subset ⟨z, rfl⟩)


-- @@ L56-66 verbatim
/-- Coercion of `mulByInt_q_pullback_restricted` back to `K(E)` via the
range subalgebra inclusion gives `(mulByInt W q).pullback`. -/
@[simp] theorem mulByInt_q_pullback_restricted_coe
    (h_subset :
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
        (frobeniusIsog W).pullback.range)
    (z : W.toAffine.FunctionField) :
    ((mulByInt_q_pullback_restricted W h_subset z) :
        W.toAffine.FunctionField) =
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback z :=
  rfl


-- @@ L68-75 verbatim
/-- The Verschiebung pullback associated to the range-inclusion witness. -/
noncomputable def verschiebungPullback_of_witness
    (h_subset :
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
        (frobeniusIsog W).pullback.range) :
    W.toAffine.FunctionField →ₐ[K] W.toAffine.FunctionField :=
  ((frobeniusIsog_rangeEquiv W).symm.toAlgHom).comp
    (mulByInt_q_pullback_restricted W h_subset)


-- @@ L77-92 verbatim
/-- The multiplication-by-cardinality pullback factors through Frobenius. -/
theorem mulByInt_q_factor_via_witness
    (h_subset :
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
        (frobeniusIsog W).pullback.range) :
    (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback =
      (frobeniusIsog W).pullback.comp
        (verschiebungPullback_of_witness W h_subset) := by
  apply AlgHom.ext
  intro z
  change (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback z =
    (frobeniusIsog W).pullback
      ((frobeniusIsog_rangeEquiv W).symm
        (mulByInt_q_pullback_restricted W h_subset z))
  rw [← frobeniusIsog_rangeEquiv_apply, AlgEquiv.apply_symm_apply,
    mulByInt_q_pullback_restricted_coe]


-- @@ L94-94 verbatim
end HasseWeil
