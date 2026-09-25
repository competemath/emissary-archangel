/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import FLT.Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing


-- @@ L11-21 verbatim
/-!
# Uniformisers in adic completions

Choices of uniformisers in the adic completion `K_v` of a Dedekind domain
at a finite place `v`, together with the basic API.

## Main definitions

* `HeightOneSpectrum.adicCompletionUniformizer`: a chosen uniformiser of
  the adic completion at `v`.
-/


-- @@ L23-30 verbatim
@[expose] public section
/-

# Constructions of various "local" elements of adelic groups

For example ideles which are uniformisers at one finite place.

-/


-- @@ L32-32 verbatim
namespace IsDedekindDomain


-- @@ L34-35 verbatim
variable {A : Type*} [CommRing A] [IsDedekindDomain A] (K : Type*) [Field K] [Algebra A K]
    [IsFractionRing A K]


-- @@ L37-37 verbatim
namespace HeightOneSpectrum


-- @@ L39-42 verbatim
/-- A uniformiser associated to `v` in the completion `Kᵥ`. -/
noncomputable def adicCompletionUniformizer (v : HeightOneSpectrum A) :
    v.adicCompletion K :=
  algebraMap K (v.adicCompletion K) (v.valuation_exists_uniformizer K).choose


-- @@ L44-50 verbatim
@[simp]
lemma v_adicCompletionUniformizer (v : HeightOneSpectrum A) :
    Valued.v (v.adicCompletionUniformizer K) = (Multiplicative.ofAdd (-1 : ℤ)) := by
  let u := (v.valuation_exists_uniformizer K).choose
  have h : (valuation K v) u = (Multiplicative.ofAdd (-1 : ℤ)) :=
    (v.valuation_exists_uniformizer K).choose_spec
  rwa [← valuedAdicCompletion_eq_valuation' v u] at h


-- @@ L52-57 verbatim
/-- A uniformiser associated to `v` in the integers of the completion `Kᵥ`. -/
@[simps]
noncomputable def adicCompletionIntegersUniformizer (v : HeightOneSpectrum A) :
    v.adicCompletionIntegers K :=
  ⟨v.adicCompletionUniformizer K, by
    simp [mem_adicCompletionIntegers, inv_le_comm₀, ← Multiplicative.toAdd_le]⟩


-- @@ L59-64 verbatim
lemma adicCompletionUniformizer_ne_zero (v : HeightOneSpectrum A) :
    v.adicCompletionUniformizer K ≠ 0 := by
  intro h
  apply_fun Valued.v at h
  rw [v_adicCompletionUniformizer] at h
  simp at h


-- @@ L66-69 verbatim
/-- A uniformiser associated to `v` in the units of the completion `Kᵥ`. -/
noncomputable def adicCompletionUniformizerUnit (v : HeightOneSpectrum A) :
    (v.adicCompletion K)ˣ :=
  .mk0 (v.adicCompletionUniformizer K) <| v.adicCompletionUniformizer_ne_zero K


-- @@ L71-71 verbatim
end HeightOneSpectrum


-- @@ L73-73 verbatim
namespace FiniteAdeleRing


-- @@ L75-83 verbatim
/-- `localUniformiser v` is an adele which is 1 at all finite places except `v`, where
it is a uniformiser. -/
noncomputable def localUniformiser (v : HeightOneSpectrum A) [DecidableEq (HeightOneSpectrum A)] :
    FiniteAdeleRing A K :=
  ⟨Pi.mulSingle v (v.adicCompletionUniformizer K), by
    apply Set.Finite.subset (Set.finite_singleton v)
    rw [Set.compl_subset_comm]
    intro p hp
    simp [Pi.mulSingle_eq_of_ne hp]⟩


-- @@ L85-87 verbatim
@[simp] lemma localUniformiser_eval (v : HeightOneSpectrum A)
    [DecidableEq (HeightOneSpectrum A)] (w : HeightOneSpectrum A) :
    localUniformiser K v w = Pi.mulSingle v (v.adicCompletionUniformizer K) w := rfl


-- @@ L89-110 verbatim
set_option backward.isDefEq.respectTransparency.types false in
/-- `localUniformiser v` is an idele which is 1 at all finite places except `v`, where
it is a uniformiser. -/
noncomputable def localUniformiserUnit (v : HeightOneSpectrum A)
    [DecidableEq (HeightOneSpectrum A)] :
    (FiniteAdeleRing A K)ˣ :=
  ⟨localUniformiser K v,
    ⟨Pi.mulSingle v (v.adicCompletionUniformizer K)⁻¹, by
      apply Set.Finite.subset (Set.finite_singleton v)
      rw [Set.compl_subset_comm]
      intro w hw
      simp [Pi.mulSingle_eq_of_ne hw]⟩,
    by
      ext w
      obtain rfl | hw := eq_or_ne w v
      · simp [mul_inv_cancel₀ <| HeightOneSpectrum.adicCompletionUniformizer_ne_zero K w]
      · simp [hw],
    by
      ext w
      obtain rfl | hw := eq_or_ne w v
      · simp [inv_mul_cancel₀ <| HeightOneSpectrum.adicCompletionUniformizer_ne_zero K w]
      · simp [hw]⟩


-- @@ L112-137 verbatim
set_option backward.isDefEq.respectTransparency.types false in
/-- `localUnit K α` for `α : (v.adicCompletion K)ˣ`, is the finite idele which is `α` at
`v` and `1` elsewhere. -/
noncomputable def localUnit {v : HeightOneSpectrum A} (α : (v.adicCompletion K)ˣ)
    [DecidableEq (HeightOneSpectrum A)] :
    (FiniteAdeleRing A K)ˣ :=
  ⟨⟨Pi.mulSingle v α, by
      apply Set.Finite.subset (Set.finite_singleton v)
      rw [Set.compl_subset_comm]
      intro w hw
      simp [Pi.mulSingle_eq_of_ne hw]⟩,
  ⟨Pi.mulSingle v α⁻¹, by
      apply Set.Finite.subset (Set.finite_singleton v)
      rw [Set.compl_subset_comm]
      intro w hw
      simp [Pi.mulSingle_eq_of_ne hw]⟩,
    by
      ext w
      obtain rfl | hw := eq_or_ne w v
      · simp
      · simp [hw],
    by
      ext w
      obtain rfl | hw := eq_or_ne w v
      · simp
      · simp [hw]⟩


-- @@ L139-142 verbatim
lemma localUnit_eval_of_eq {v : HeightOneSpectrum A} (α : (v.adicCompletion K)ˣ)
    [DecidableEq (HeightOneSpectrum A)] :
    (localUnit K α).1 v = α := by
  simp [localUnit]


-- @@ L144-147 verbatim
lemma localUnit_eval_of_ne {v : HeightOneSpectrum A} (α : (v.adicCompletion K)ˣ)
    [DecidableEq (HeightOneSpectrum A)] (w : HeightOneSpectrum A) (hw : w ≠ v) :
    (localUnit K α).1 w = 1 := by
  simp [localUnit, hw]


-- @@ L149-149 verbatim
end FiniteAdeleRing


-- @@ L151-151 verbatim
end IsDedekindDomain
