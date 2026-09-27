/-
Copyright (c) 2026 PFR contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PFR contributors
-/

module

public import LeanPool.ZhangYeungInequality.PFR.Mathlib.Probability.Kernel.Composition.Comp
public import LeanPool.ZhangYeungInequality.PFR.ForMathlib.Entropy.Kernel.Basic


-- @@ L12-33 verbatim
/-!
# Mutual Information of kernels

## Main definitions

* `mutualInfo`: Mutual information of a kernel `κ` into a product space with respect to
  a
  measure `μ`. This is denoted by `Ik[κ, μ]` and is equal to
  `Hk[fst κ, μ] + Hk[snd κ, μ] - Hk[κ, μ]`.

## Main statements

* `mutualInfo_nonneg`: `Ik[κ, μ]` is nonnegative
* `entropy_condKernel_le_entropy_fst` and `entropy_condKernel_le_entropy_snd`:
  conditioning
  reduces entropy.

## Notations

* `Ik[κ, μ] = Kernel.entropy κ μ`

-/


-- @@ L35-35 verbatim
@[expose] public section


-- @@ L37-37 verbatim
open Function MeasureTheory Real

-- @@ L38-38 verbatim
open scoped ENNReal NNReal Topology ProbabilityTheory


-- @@ L40-40 verbatim
namespace ProbabilityTheory.Kernel


-- @@ L42-44 verbatim
variable {Ω S T U V : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U] [MeasurableSpace V]
  {κ : Kernel T S} {μ : Measure T} {X : Ω → S} {Y : Ω → U}


-- @@ L46-49 expanded
/-- Mutual information of a kernel into a product space with respect to a measure. -/
noncomputable def mutualInfo (κ : Kernel T (S × U)) (μ : Measure T) : ℝ :=
  ProbabilityTheory.Kernel.entropy (fst κ) μ + ProbabilityTheory.Kernel.entropy (snd κ) μ -
    ProbabilityTheory.Kernel.entropy κ μ


-- @@ L51-52 verbatim
/-- Mutual information of a kernel into a product space with respect to a measure. -/
notation3:100 "Ik[" κ " , " μ "]" => Kernel.mutualInfo κ μ


-- @@ L54-55 expanded
lemma mutualInfo_def (κ : Kernel T (S × U)) (μ : Measure T) :
    Kernel.mutualInfo κ μ =
      ProbabilityTheory.Kernel.entropy (fst κ) μ + ProbabilityTheory.Kernel.entropy (snd κ) μ -
        ProbabilityTheory.Kernel.entropy κ μ :=
  rfl


-- @@ L57-59 expanded
@[simp]
lemma mutualInfo_zero_measure (κ : Kernel T (S × U)) : Kernel.mutualInfo κ (0 : Measure T) = 0 := by
  simp [mutualInfo]


-- @@ L61-63 expanded
@[simp]
lemma mutualInfo_zero_kernel (μ : Measure T) : Kernel.mutualInfo (0 : Kernel T (S × U)) μ = 0 := by
  simp [mutualInfo]


-- @@ L65-74 expanded
lemma mutualInfo_congr {κ η : Kernel T (S × U)} {μ : Measure T} (h : κ =ᵐ[μ] η) :
    Kernel.mutualInfo κ μ = Kernel.mutualInfo η μ :=
  by
  rw [mutualInfo, mutualInfo]
  have h1 : fst κ =ᵐ[μ] fst η := by
    filter_upwards [h] with t ht
    rw [fst_apply, ht, fst_apply]
  have h2 : snd κ =ᵐ[μ] snd η := by
    filter_upwards [h] with t ht
    rw [snd_apply, ht, snd_apply]
  rw [entropy_congr h1, entropy_congr h2, entropy_congr h]


-- @@ L76-90 verbatim
lemma compProd_assoc' (ξ : Kernel T S) [IsSFiniteKernel ξ]
    (κ : Kernel (T × S) U) [IsSFiniteKernel κ] (η :
      Kernel (T × S × U) V) [IsSFiniteKernel η] :
    map ((ξ ⊗ₖ κ) ⊗ₖ η) MeasurableEquiv.prodAssoc
      = ξ ⊗ₖ
        (κ ⊗ₖ (comap η MeasurableEquiv.prodAssoc MeasurableEquiv.prodAssoc.measurable)) := by
  ext x s hs
  rw [map_apply' _ (by fun_prop) _ hs,
    compProd_apply (MeasurableEquiv.prodAssoc.measurable hs),
    compProd_apply hs, lintegral_compProd]
  swap; · exact measurable_kernel_prodMk_left' (MeasurableEquiv.prodAssoc.measurable hs) _
  congr with a
  rw [compProd_apply]
  swap; · exact measurable_prodMk_left hs
  congr


-- @@ L92-95 verbatim
lemma _root_.ProbabilityTheory.Kernel.Measure.compProd_compProd (μ : Measure T)
    (ξ : Kernel T S) (κ : Kernel (T × S) U) :
    μ ⊗ₘ (ξ ⊗ₖ κ) = (μ ⊗ₘ ξ ⊗ₘ κ).map MeasurableEquiv.prodAssoc := by
  simp_all


-- @@ L97-101 verbatim
lemma _root_.ProbabilityTheory.Kernel.Measure.compProd_compProd' (μ : Measure T)
    (ξ : Kernel T S) (κ : Kernel (T × S) U) :
    μ ⊗ₘ (ξ ⊗ₖ κ) = (μ ⊗ₘ ξ ⊗ₘ κ).comap
      (MeasurableEquiv.prodAssoc.symm : T × S × U ≃ᵐ (T × S) × U) := by
  rw [MeasurableEquiv.comap_symm, Measure.compProd_compProd]


-- @@ L103-110 verbatim
lemma _root_.ProbabilityTheory.Kernel.Measure.compProd_compProd'' (μ : Measure T)
    (ξ : Kernel T S) (κ : Kernel (T × S) U) :
    μ ⊗ₘ ξ ⊗ₘ κ = Measure.comap MeasurableEquiv.prodAssoc (μ ⊗ₘ (ξ ⊗ₖ κ)) :=
      by
  rw [Measure.compProd_compProd, ← MeasurableEquiv.map_symm, Measure.map_map]
  · simp
  · exact MeasurableEquiv.prodAssoc.symm.measurable
  · exact MeasurableEquiv.prodAssoc.measurable


-- @@ L112-112 verbatim
section


-- @@ L114-114 verbatim
variable [MeasurableSingletonClass S] [MeasurableSingletonClass U]


-- @@ L116-121 expanded
@[simp]
lemma mutualInfo_swapRight (κ : Kernel T (S × U)) (μ : Measure T) :
    Kernel.mutualInfo (swapRight κ) μ = Kernel.mutualInfo κ μ :=
  by
  rw [mutualInfo, fst_swapRight, snd_swapRight, entropy_swapRight, add_comm]
  rfl


-- @@ L123-123 verbatim
variable [MeasurableSingletonClass T]


-- @@ L125-133 expanded
lemma mutualInfo_nonneg' {κ : Kernel T (S × U)} {μ : Measure T} [IsFiniteMeasure μ]
    [FiniteSupport μ] (hκ : FiniteKernelSupport κ) : 0 ≤ Kernel.mutualInfo κ μ :=
  by
  simp_rw [mutualInfo, entropy, integral_eq_setIntegral (ae_mem_support μ),
    setIntegral_finset _ .finset, smul_eq_mul]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  simp_rw [← mul_add, ← mul_sub, fst_apply, snd_apply]
  have (x : T) : FiniteSupport (κ x) := ⟨hκ x⟩
  exact Finset.sum_nonneg fun x _ ↦ mul_nonneg ENNReal.toReal_nonneg measureMutualInfo_nonneg


-- @@ L135-139 expanded
lemma mutualInfo_nonneg [Countable T] {κ : Kernel T (S × U)} {μ : Measure T} [IsFiniteMeasure μ]
    [FiniteSupport μ] (hκ : AEFiniteKernelSupport κ μ) : 0 ≤ Kernel.mutualInfo κ μ :=
  by
  rw [mutualInfo_congr hκ.ae_eq_mk]
  exact mutualInfo_nonneg' hκ.finiteKernelSupport_mk


-- @@ L142-142 verbatim
variable [Countable S] [Countable T]


-- @@ L144-150 expanded
lemma mutualInfo_compProd {κ : Kernel T S} [IsZeroOrMarkovKernel κ] {η : Kernel (T × S) U}
    [IsMarkovKernel η] {μ : Measure T} [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) (hη : AEFiniteKernelSupport η (μ ⊗ₘ κ)) :
    Kernel.mutualInfo (κ ⊗ₖ η) μ =
      ProbabilityTheory.Kernel.entropy κ μ + ProbabilityTheory.Kernel.entropy (snd (κ ⊗ₖ η)) μ -
        ProbabilityTheory.Kernel.entropy (κ ⊗ₖ η) μ :=
  by rw [mutualInfo, entropy_compProd hκ hη, fst_compProd]


-- @@ L152-152 verbatim
variable [Countable U]


-- @@ L154-159 expanded
lemma mutualInfo_eq_fst_sub [Nonempty S] {κ : Kernel T (S × U)} [IsZeroOrMarkovKernel κ]
    {μ : Measure T} [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    Kernel.mutualInfo κ μ =
      ProbabilityTheory.Kernel.entropy (fst κ) μ -
        ProbabilityTheory.Kernel.entropy (condKernel (swapRight κ)) (μ ⊗ₘ (snd κ)) :=
  by
  rw [mutualInfo, chain_rule' hκ]
  ring


-- @@ L161-171 expanded
@[simp]
lemma mutualInfo_prod {κ : Kernel T S} {η : Kernel T U} [IsZeroOrMarkovKernel κ]
    [IsZeroOrMarkovKernel η] (μ : Measure T) [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) (hη : AEFiniteKernelSupport η μ) :
    Kernel.mutualInfo (κ ×ₖ η) μ = 0 :=
  by
  rcases eq_zero_or_isMarkovKernel κ with rfl | hκ'
  · simp
  rcases eq_zero_or_isMarkovKernel η with rfl | hη'
  · simp
  rw [mutualInfo, snd_prod, fst_prod, entropy_prod hκ hη, sub_self]


-- @@ L173-179 expanded
lemma mutualInfo_eq_snd_sub [Nonempty U] {κ : Kernel T (S × U)} [IsZeroOrMarkovKernel κ]
    {μ : Measure T} [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    Kernel.mutualInfo κ μ =
      ProbabilityTheory.Kernel.entropy (snd κ) μ -
        ProbabilityTheory.Kernel.entropy (condKernel κ) (μ ⊗ₘ (fst κ)) :=
  by
  rw [mutualInfo, chain_rule hκ]
  ring


-- @@ L181-187 expanded
lemma entropy_condKernel_le_entropy_fst [Nonempty S] (κ : Kernel T (S × U)) [IsZeroOrMarkovKernel κ]
    (μ : Measure T) [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    ProbabilityTheory.Kernel.entropy (condKernel (swapRight κ)) (μ ⊗ₘ (snd κ)) ≤
      ProbabilityTheory.Kernel.entropy (fst κ) μ :=
  by
  rw [← sub_nonneg, ← mutualInfo_eq_fst_sub hκ]
  exact mutualInfo_nonneg hκ


-- @@ L189-197 expanded
lemma entropy_condKernel_le_entropy_snd [Nonempty U] {κ : Kernel T (S × U)} [IsZeroOrMarkovKernel κ]
    {μ : Measure T} [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    ProbabilityTheory.Kernel.entropy (condKernel κ) (μ ⊗ₘ (fst κ)) ≤
      ProbabilityTheory.Kernel.entropy (snd κ) μ :=
  by
  rw [← sub_nonneg, ← mutualInfo_eq_snd_sub hκ]
  exact mutualInfo_nonneg hκ


-- @@ L198-230 expanded
lemma entropy_snd_sub_mutualInfo_le_entropy_map_of_injective {V : Type*} [Countable V]
    [MeasurableSpace V] [MeasurableSingletonClass V] (κ : Kernel T (S × U)) [IsZeroOrMarkovKernel κ]
    (μ : Measure T) [IsZeroOrProbabilityMeasure μ] (f : S × U → V)
    (hfi : ∀ x, Injective (fun y ↦ f (x, y))) [FiniteSupport μ] (hκ : AEFiniteKernelSupport κ μ) :
    ProbabilityTheory.Kernel.entropy (snd κ) μ - Kernel.mutualInfo κ μ ≤
      ProbabilityTheory.Kernel.entropy (map κ f) μ :=
  by
  rcases eq_zero_or_isMarkovKernel κ with rfl | hκ'
  · simp
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ'
  · simp
  have : Nonempty (S × U) := nonempty_of_isProbabilityMeasure_of_isMarkovKernel μ κ
  inhabit (S × U)
  have : Nonempty U := ⟨(default : S × U).2⟩
  have : Nonempty V := ⟨f default⟩
  rw [mutualInfo_eq_snd_sub hκ]
  have hf : Measurable f := by fun_prop
  ring_nf
  calc
    ProbabilityTheory.Kernel.entropy (condKernel κ) (μ ⊗ₘ fst κ) =
        ProbabilityTheory.Kernel.entropy
          (snd
            ((condKernel κ) ⊗ₖ (deterministic (fun x : (T × S) × U ↦ f (x.1.2, x.2)) .of_discrete)))
          (μ ⊗ₘ fst κ) :=
      by
      symm
      apply entropy_snd_compProd_deterministic_of_injective _ _ (fun t ↦ hfi t.2)
    _ = ProbabilityTheory.Kernel.entropy (condKernel (map κ (fun p ↦ (p.1, f p)))) (μ ⊗ₘ fst κ) :=
      (entropy_congr (condKernel_map_prodMk_left κ μ f).symm)
    _ =
        ProbabilityTheory.Kernel.entropy (condKernel (map κ (fun p ↦ (p.1, f p))))
          (μ ⊗ₘ fst (map κ (fun p ↦ (p.1, f p)))) :=
      by
      congr 2 with x
      rw [fst_map_prod _ hf, fst_apply, map_apply _ measurable_fst]
    _ ≤ ProbabilityTheory.Kernel.entropy (snd (map κ (fun p ↦ (p.1, f p)))) μ :=
      (entropy_condKernel_le_entropy_snd hκ.map)
    _ = ProbabilityTheory.Kernel.entropy (map κ f) μ := by rw [snd_map_prod _ measurable_fst]


-- @@ L232-232 verbatim
end


-- @@ L234-234 verbatim
section


-- @@ L236-239 verbatim
variable [Countable S] [MeasurableSingletonClass S]
  [Countable T] [MeasurableSingletonClass T]
  [Countable U] [MeasurableSingletonClass U]
  [Countable V] [MeasurableSingletonClass V]


-- @@ L241-254 expanded
lemma _root_.ProbabilityTheory.Kernel.entropy_reverse {κ : Kernel T (S × U × V)}
    [IsZeroOrMarkovKernel κ] {μ : Measure T} [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    ProbabilityTheory.Kernel.entropy (reverse κ) μ = ProbabilityTheory.Kernel.entropy κ μ :=
  by
  refine le_antisymm ?_ ?_
  · have h : reverse κ = map κ (fun p ↦ (p.2.2, p.2.1, p.1)) := reverse_eq κ
    have key := entropy_map_le (κ := κ) (μ := μ) (fun p ↦ (p.2.2, p.2.1, p.1)) hκ
    rwa [← h] at key
  · have hmap : map (reverse κ) (fun p ↦ (p.2.2, p.2.1, p.1)) = κ :=
      (reverse_eq (reverse κ)).symm.trans (reverse_reverse κ)
    have key := entropy_map_le (κ := reverse κ) (μ := μ) (fun p ↦ (p.2.2, p.2.1, p.1)) hκ.reverse
    rwa [hmap] at key


-- @@ L256-264 verbatim
instance _root_.ProbabilityTheory.Kernel.IsZeroOrProbabilityMeasure.compProd
    {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    (μ : Measure α) [IsZeroOrProbabilityMeasure μ] (κ : Kernel α β)
    [IsZeroOrMarkovKernel κ] : IsZeroOrProbabilityMeasure (μ ⊗ₘ κ) := by
  rcases eq_zero_or_isMarkovKernel κ with rfl | hκ
  · simp only [Measure.compProd_zero_right]; infer_instance
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp only [Measure.compProd_zero_left]; infer_instance
  infer_instance


-- @@ L266-275 expanded
lemma _root_.ProbabilityTheory.Kernel.entropy_condKernel_compProd_triple [Nonempty V]
    (ξ : Kernel T S) [IsZeroOrMarkovKernel ξ] (κ : Kernel (T × S) U) [IsMarkovKernel κ]
    (η : Kernel (T × S × U) V) [IsMarkovKernel η] (μ : Measure T) :
    ProbabilityTheory.Kernel.entropy (condKernel (ξ ⊗ₖ κ ⊗ₖ η)) (μ ⊗ₘ (ξ ⊗ₖ κ)) =
      ProbabilityTheory.Kernel.entropy η (μ ⊗ₘ (ξ ⊗ₖ κ)) :=
  entropy_congr
    (condKernel_compProd_ae_eq (ξ ⊗ₖ κ) η μ)
      -- from kernel (T × S × U) V; Measure (T × S × U)
      -- to kernel (T × S) V; Measure (T × S)


-- @@ L276-319 expanded
lemma _root_.ProbabilityTheory.Kernel.entropy_submodular_compProd {ξ : Kernel T S}
    [IsZeroOrMarkovKernel ξ] {κ : Kernel (T × S) U} [IsZeroOrMarkovKernel κ]
    {η : Kernel (T × S × U) V} [IsMarkovKernel η] {μ : Measure T} [IsZeroOrProbabilityMeasure μ]
    [FiniteSupport μ] (hκ : AEFiniteKernelSupport κ (μ ⊗ₘ ξ))
    (hη : AEFiniteKernelSupport η (μ ⊗ₘ (ξ ⊗ₖ κ))) (hξ : AEFiniteKernelSupport ξ μ) :
    ProbabilityTheory.Kernel.entropy η (μ ⊗ₘ (ξ ⊗ₖ κ)) ≤
      ProbabilityTheory.Kernel.entropy
        (snd (κ ⊗ₖ (comap η MeasurableEquiv.prodAssoc MeasurableEquiv.prodAssoc.measurable)))
        (μ ⊗ₘ ξ) :=
  by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  rcases eq_zero_or_isMarkovKernel ξ with rfl | hξ'
  · simp
  have : Nonempty S := nonempty_of_isProbabilityMeasure_of_isMarkovKernel μ ξ
  have : Nonempty T := μ.nonempty_of_neZero
  rcases eq_zero_or_isMarkovKernel κ with rfl | hκ'
  · simp
  have : Nonempty U := nonempty_of_isMarkovKernel κ
  rcases eq_zero_or_isMarkovKernel η with rfl | hκ'
  · simp
  have : Nonempty V := nonempty_of_isMarkovKernel η
  have h_meas := (MeasurableEquiv.prodAssoc.symm : T × S × U ≃ᵐ (T × S) × U).symm.measurable
  have : FiniteSupport (μ ⊗ₘ ξ) := finiteSupport_of_compProd hξ
  have : FiniteSupport (μ ⊗ₘ (ξ ⊗ₖ κ)) := finiteSupport_of_compProd (hξ.compProd hκ)
  let η' : Kernel ((T × S) × U) V := comap η MeasurableEquiv.prodAssoc h_meas
  let : IsMarkovKernel η' := IsMarkovKernel.comap η h_meas
  let : IsZeroOrMarkovKernel (κ ⊗ₖ η') := IsZeroOrMarkovKernel.compProd κ η'
  have h := entropy_condKernel_le_entropy_snd (κ := κ ⊗ₖ η') (μ := μ ⊗ₘ ξ) ?_
  · simp only [fst_compProd] at h
    have : condKernel (κ ⊗ₖ η') =ᵐ[μ ⊗ₘ ξ ⊗ₘ κ] η' := by
      exact condKernel_compProd_ae_eq κ η' (μ ⊗ₘ ξ)
    dsimp only [η'] at h ⊢
    rwa [entropy_congr this, Measure.compProd_compProd'', entropy_comap_equiv] at h
  · refine (hκ.compProd ?_)
    convert hη.comap_equiv MeasurableEquiv.prodAssoc
    exact
      Measure.compProd_compProd'' _ _
        _
          /- $$ H[X,Y,Z] + H[X] \leq H[Z,X] + H[Y,X].$$ -/


-- @@ L320-361 expanded
lemma _root_.ProbabilityTheory.Kernel.entropy_compProd_triple_add_entropy_le {ξ : Kernel T S}
    [IsZeroOrMarkovKernel ξ] {κ : Kernel (T × S) U} [IsMarkovKernel κ] {η : Kernel (T × S × U) V}
    [IsMarkovKernel η] {μ : Measure T} [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ (μ ⊗ₘ ξ)) (hη : AEFiniteKernelSupport η (μ ⊗ₘ (ξ ⊗ₖ κ)))
    (hξ : AEFiniteKernelSupport ξ μ) :
    ProbabilityTheory.Kernel.entropy ((ξ ⊗ₖ κ) ⊗ₖ η) μ + ProbabilityTheory.Kernel.entropy ξ μ ≤
      ProbabilityTheory.Kernel.entropy
          (ξ ⊗ₖ snd (κ ⊗ₖ comap η MeasurableEquiv.prodAssoc MeasurableEquiv.prodAssoc.measurable))
          μ +
        ProbabilityTheory.Kernel.entropy (ξ ⊗ₖ κ) μ :=
  by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  rcases eq_zero_or_isMarkovKernel ξ with rfl | hξ'
  · simp
  have : Nonempty S := nonempty_of_isProbabilityMeasure_of_isMarkovKernel μ ξ
  have : Nonempty T := μ.nonempty_of_neZero
  have : Nonempty U := nonempty_of_isMarkovKernel κ
  have : Nonempty V := nonempty_of_isMarkovKernel η
  rw [chain_rule,
    chain_rule (κ :=
      ξ ⊗ₖ snd (κ ⊗ₖ comap η MeasurableEquiv.prodAssoc MeasurableEquiv.prodAssoc.measurable))]
  · simp only [fst_compProd, entropy_condKernel_compProd_triple]
    calc
      ProbabilityTheory.Kernel.entropy (ξ ⊗ₖ κ) μ +
              ProbabilityTheory.Kernel.entropy η (μ ⊗ₘ (ξ ⊗ₖ κ)) +
            ProbabilityTheory.Kernel.entropy ξ μ =
          ProbabilityTheory.Kernel.entropy ξ μ + ProbabilityTheory.Kernel.entropy (ξ ⊗ₖ κ) μ +
            ProbabilityTheory.Kernel.entropy η (μ ⊗ₘ (ξ ⊗ₖ κ)) :=
        by abel
      _ ≤
          ProbabilityTheory.Kernel.entropy ξ μ + ProbabilityTheory.Kernel.entropy (ξ ⊗ₖ κ) μ +
            ProbabilityTheory.Kernel.entropy
              (condKernel (ξ ⊗ₖ snd (κ ⊗ₖ comap η MeasurableEquiv.prodAssoc _))) (μ ⊗ₘ ξ) :=
        by
        refine add_le_add le_rfl ?_
        refine (entropy_submodular_compProd hκ hη hξ).trans_eq ?_
        refine entropy_congr ?_
        exact (condKernel_compProd_ae_eq _ _ _).symm
      _ =
          ProbabilityTheory.Kernel.entropy ξ μ +
              ProbabilityTheory.Kernel.entropy
                (condKernel (ξ ⊗ₖ snd (κ ⊗ₖ comap η MeasurableEquiv.prodAssoc _))) (μ ⊗ₘ ξ) +
            ProbabilityTheory.Kernel.entropy (ξ ⊗ₖ κ) μ :=
        by abel
  · refine hξ.compProd ?_
    refine AEFiniteKernelSupport.snd ?_
    refine hκ.compProd ?_
    convert hη.comap_equiv MeasurableEquiv.prodAssoc
    exact Measure.compProd_compProd'' _ _ _
  · exact (hξ.compProd hκ).compProd hη


-- @@ L363-416 expanded
/-- The submodularity inequality:
$$ H[X,Y,Z] + H[X] \leq H[X,Z] + H[X,Y].$$ -/
lemma _root_.ProbabilityTheory.Kernel.entropy_triple_add_entropy_le' {κ : Kernel T (S × U × V)}
    [IsZeroOrMarkovKernel κ] {μ : Measure T} [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    ProbabilityTheory.Kernel.entropy κ μ + ProbabilityTheory.Kernel.entropy (fst κ) μ ≤
      ProbabilityTheory.Kernel.entropy (deleteMiddle κ) μ +
        ProbabilityTheory.Kernel.entropy (deleteRight κ) μ :=
  by
  rcases eq_zero_or_isMarkovKernel κ with rfl | hκ'
  · simp
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  have : Nonempty (S × U × V) := nonempty_of_isProbabilityMeasure_of_isMarkovKernel μ κ
  inhabit (S × U × V)
  have : Nonempty U := ⟨(default : S × U × V).2.1⟩
  have : Nonempty V := ⟨(default : S × U × V).2.2⟩
  set κ' := map κ MeasurableEquiv.prodAssoc.symm with hκ'_def
  set ξ := fst (fst κ') with ξ_def
  let κ'' := condKernel (fst κ')
  let η := condKernel κ'
  have hξ_eq : ξ = fst κ :=
    by
    rw [ξ_def, hκ'_def, fst_eq, MeasurableEquiv.prodAssoc, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk,
      fst_eq, map_map _ (by fun_prop) (by fun_prop), map_map _ (by fun_prop) (by fun_prop), fst_eq]
    rfl
  have h_compProd_eq : ξ ⊗ₖ κ'' = fst κ' := (disintegration (fst κ')).symm
  have h_compProd_triple_eq : (ξ ⊗ₖ κ'') ⊗ₖ η = κ' :=
    by
    rw [h_compProd_eq]
    exact (disintegration κ').symm
  have h_compProd_triple_eq' :
    ξ ⊗ₖ (κ'' ⊗ₖ comap η MeasurableEquiv.prodAssoc MeasurableEquiv.prodAssoc.measurable) = κ :=
    by
    rw [← compProd_assoc', h_compProd_triple_eq, hκ'_def, map_map _ (by fun_prop) (by fun_prop)]
    simp
  have h := entropy_compProd_triple_add_entropy_le (ξ := ξ) (κ := κ'') (η := η) (μ := μ) ?_ ?_ ?_
  rotate_left
  · exact aefiniteKernelSupport_of_cond _ hκ.map.fst
  · rw [h_compProd_eq]
    apply aefiniteKernelSupport_of_cond
    exact hκ.map
  · exact hκ.map.fst.fst
  rw [← hξ_eq]
  have h_right : deleteRight κ = fst κ' :=
    by
    rw [hκ'_def, deleteRight_eq, fst_eq, map_map _ (by fun_prop) (by fun_prop)]
    congr
  have h_middle :
    deleteMiddle κ =
      ξ ⊗ₖ snd (κ'' ⊗ₖ comap η MeasurableEquiv.prodAssoc MeasurableEquiv.prodAssoc.measurable) :=
    by rw [← deleteMiddle_compProd, h_compProd_triple_eq']
  have hκ : ProbabilityTheory.Kernel.entropy κ μ = ProbabilityTheory.Kernel.entropy κ' μ :=
    by
    rw [hκ'_def, entropy_map_of_injective _ _ _ (by fun_prop)]
    exact MeasurableEquiv.prodAssoc.symm.injective
  simp_all


-- @@ L418-435 expanded
/-- The submodularity inequality:
$$ H[X,Y,Z] + H[Z] \leq H[X,Z] + H[Y,Z].$$ -/
lemma _root_.ProbabilityTheory.Kernel.entropy_triple_add_entropy_le (κ : Kernel T (S × U × V))
    [IsZeroOrMarkovKernel κ] (μ : Measure T) [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    ProbabilityTheory.Kernel.entropy κ μ + ProbabilityTheory.Kernel.entropy (snd (snd κ)) μ ≤
      ProbabilityTheory.Kernel.entropy (deleteMiddle κ) μ +
        ProbabilityTheory.Kernel.entropy (snd κ) μ :=
  by
  have h2 : fst (reverse κ) = snd (snd κ) :=
    by
    rw [fst_eq, reverse_eq, snd_eq, map_map _ (by fun_prop) (by fun_prop), snd_eq,
      map_map _ (by fun_prop) (by fun_prop)]
    congr
  rw [← entropy_reverse hκ, ← h2]
  refine (entropy_triple_add_entropy_le' (κ := reverse κ) (μ := μ) hκ.reverse).trans ?_
  refine add_le_add ?_ ?_
  · rw [← entropy_swapRight]
    simp
  · rw [← entropy_swapRight]
    simp


-- @@ L437-437 verbatim
end


-- @@ L439-439 verbatim
end ProbabilityTheory.Kernel
