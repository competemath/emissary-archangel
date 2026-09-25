/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.Operators.SpectralTheory.Symmetric

-- @@ L9-37 verbatim
/-!

# Spectral theory for self-adjoint operators

## i. Overview

In this module we develop the spectral theory for self-adjoint operators.

## ii. Key results

- `resolventSet_eq_regularityDomain` : The resolvent set and regularity domain coincide. That is,
    if `T - z • 1` has a continuous (equivalently, bounded) inverse then its range is all of `H`.
- `mem_resolventSet_of_im_ne_zero` : every non-real `z` lies in the resolvent set of a
    self-adjoint operator.
- `sub_smul_surjective` : A self-adjoint `T` has `T - z • 1` surjective for every non-real `z`
    (in particular `T ± i • 1` are onto).
- `spectrum_real` : The spectrum of a self-adjoint unbounded operator is real.
- `unitaryConj_isSelfAdjoint` : Unitary conjugation preserves self-adjointness.

## iii. Table of contents

- A. Resolvent set
- B. Spectrum
- C. Unitary conjugation

## iv. References

* None.
-/


-- @@ L39-39 verbatim
@[expose] public section


-- @@ L41-41 verbatim
namespace LinearPMap

-- @@ L42-42 verbatim
namespace IsSelfAdjoint


-- @@ L44-44 verbatim
open Complex

-- @@ L45-45 verbatim
open ComplexConjugate

-- @@ L46-46 verbatim
open Set


-- @@ L48-48 verbatim
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

-- @@ L49-49 verbatim
variable {T : H →ₗ.[ℂ] H} (hT : IsSelfAdjoint T)

-- @@ L50-50 verbatim
include hT


-- @@ L52-54 verbatim
/-!
## A. Resolvent set
-/


-- @@ L56-67 verbatim
lemma resolventSet_eq_regularityDomain : ρ T = T.regularityDomain := by
  refine Subset.antisymm T.resolventSet_subset_regularityDomain fun z hz ↦ ?_
  obtain ⟨h_ker, h_cont⟩ := mem_regularityDomain_iff.mp hz
  refine ⟨h_ker, ?_, h_cont⟩
  have h_ker' : (T - conj z • 1).toFun.ker = ⊥ := by
    by_cases hz' : conj z = z
    · exact hz'.symm ▸ h_ker
    · exact (mem_regularityDomain_iff.mp <| (isSymmetric hT).mem_regularityDomain_of_im_ne_zero
        (by simp_all [Complex.conj_eq_iff_im])).1
  have h_orthog := (isUnbounded hT).orthogonal_adjoint_sub_ker hz
  rw [isSelfAdjoint_def.mp hT, (isClosed hT).closure_eq, h_ker'] at h_orthog
  simp [← h_orthog]


-- @@ L69-72 verbatim
/-- Every non-real `z` lies in the resolvent set of a self-adjoint operator. -/
lemma mem_resolventSet_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) : z ∈ ρ T := by
  rw [resolventSet_eq_regularityDomain hT]
  exact (isSymmetric hT).mem_regularityDomain_of_im_ne_zero hz


-- @@ L74-77 verbatim
/-- A self-adjoint operator has `T - z • 1` surjective for every non-real `z`: off the real
axis a self-adjoint operator has `z` in its resolvent set, so `T - z • 1` has full range. -/
lemma sub_smul_surjective {z : ℂ} (hz : z.im ≠ 0) : Function.Surjective (T - z • 1).toFun :=
  LinearMap.range_eq_top.mp (mem_resolventSet_iff.mp (mem_resolventSet_of_im_ne_zero hT hz)).2.1


-- @@ L79-89 verbatim
/-- `(T - z • 1).range = ⊤` is a sufficient condition for `z ∈ ρ T`
  (and it is a necessary condition by definition of `ρ`). -/
lemma mem_resolventSet_of_range_eq_top {z : ℂ} (h : (T - z • 1).toFun.range = ⊤) : z ∈ ρ T := by
  by_cases hz_im : z.im = 0
  · rw [(isClosed hT).resolventSet_eq]
    refine ⟨?_, h⟩
    have h_orthog := (isUnbounded hT).orthogonal_closure_sub_range z
    rwa [isSelfAdjoint_def.mp hT, (isClosed hT).closure_eq, conj_eq_iff_im.mpr hz_im, h,
      Submodule.top_orthogonal_eq_bot, Eq.comm, ← LinearMap.le_ker_iff_map, Submodule.ker_subtype,
      le_bot_iff] at h_orthog
  · exact mem_resolventSet_of_im_ne_zero hT hz_im


-- @@ L91-93 verbatim
/-!
## B. Spectrum
-/


-- @@ L95-98 verbatim
/-- The spectrum of a self-adjoint operator is real. -/
lemma spectrum_real : σ T ⊆ range ofReal := by
  rw [spectrum_eq, resolventSet_eq_regularityDomain hT]
  exact compl_subset_comm.mp (isSymmetric hT).compl_ofReal_subset_regularityDomain


-- @@ L100-103 verbatim
/-- The residual spectrum of a self-adjoint operator is empty. -/
lemma residualSpectrum_eq_empty : σʳ T = ∅ :=
  eq_empty_iff_forall_notMem.mpr fun _ hz ↦ T.residualSpectrum_subset_spectrum hz
    (resolventSet_eq_regularityDomain hT ▸ T.residualSpectrum_subset_regularityDomain hz)


-- @@ L105-105 verbatim
end IsSelfAdjoint


-- @@ L107-109 verbatim
/-!
## C. Unitary conjugation
-/


-- @@ L111-111 verbatim
open Complex


-- @@ L113-115 verbatim
variable {H H' : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']


-- @@ L117-132 verbatim
/-- Unitary conjugation preserves self-adjointness: if `A` is a self-adjoint operator on `H` and
`u : H ≃ₗᵢ[ℂ] H'` is unitary, then `u A u⁻¹` is self-adjoint on `H'`. Symmetry, dense domain, and
the two deficiency surjectivities of `A` all transfer through `u`. -/
lemma unitaryConj_isSelfAdjoint (u : H ≃ₗᵢ[ℂ] H') {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (A.unitaryConj u) := by
  have hrange {z : ℂ} (hz : z.im ≠ 0) : (A.unitaryConj u - z • 1).toFun.range = ⊤ :=
    LinearMap.range_eq_top.mpr
      (unitaryConj_sub_smul_surjective (IsSelfAdjoint.sub_smul_surjective hA hz))
  refine IsSymmetric.isSelfAdjoint_of_range_eq_top
    (IsFormalAdjoint.unitaryConj (IsSelfAdjoint.isSymmetric hA))
    (HasDenseDomain.unitaryConj_dense_domain (IsSelfAdjoint.dense_domain hA)) ?_ ?_
  · have hI : A.unitaryConj u + I • 1 = A.unitaryConj u - (-I) • 1 :=
      LinearPMap.ext rfl fun x hf hg => by simp [sub_apply, add_apply, smul_apply, sub_neg_eq_add]
    rw [hI]
    exact hrange (by norm_num)
  · exact hrange (by norm_num)


-- @@ L134-134 verbatim
end LinearPMap
