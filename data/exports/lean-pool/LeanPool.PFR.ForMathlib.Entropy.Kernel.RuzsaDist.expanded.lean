/-
Copyright (c) 2026 PFR contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PFR contributors
-/

module

public import LeanPool.ZhangYeungInequality.PFR.ForMathlib.Entropy.Kernel.Basic
import LeanPool.PFR.ForMathlib.Entropy.Kernel.Group
import LeanPool.ZhangYeungInequality.PFR.Mathlib.MeasureTheory.Measure.Prod
import LeanPool.ZhangYeungInequality.PFR.Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Integral.Prod


-- @@ L15-21 verbatim
/-!
# Ruzsa distance between kernels

## Notations

* `dk[κ; μ # η; ν] = `
-/


-- @@ L23-23 verbatim
public section


-- @@ L25-25 verbatim
open Real MeasureTheory

-- @@ L26-26 verbatim
open scoped ENNReal NNReal Topology ProbabilityTheory


-- @@ L28-28 verbatim
namespace ProbabilityTheory.Kernel


-- @@ L30-31 verbatim
variable {T T' T'' G : Type*} [MeasurableSpace T] [MeasurableSpace T'] [MeasurableSpace T'']
  [MeasurableSpace G] [AddCommGroup G]


-- @@ L33-38 expanded
/-- The Rusza distance between two measures, defined as `H[X - Y] - H[X]/2 - H[Y]/2` where `X`
and `Y` are independent variables distributed according to the two measures. -/
@[expose]
public noncomputable def rdistm (μ ν : Measure G) : ℝ :=
  measureEntropy ((μ.prod ν).map (fun x ↦ x.1 - x.2)) - measureEntropy μ / 2 - measureEntropy ν / 2


-- @@ L40-45 verbatim
/-- The Rusza distance between two kernels taking values in the same space, defined as the average
Rusza distance between the image measures. -/
@[expose]
public
noncomputable def rdist (κ : Kernel T G) (η : Kernel T' G) (μ : Measure T) (ν : Measure T') : ℝ :=
  (μ.prod ν)[fun p ↦ rdistm (κ p.1) (η p.2)]


-- @@ L47-49 verbatim
/-- The Rusza distance between two kernels taking values in the same space, defined as the average
Rusza distance between the image measures. -/
notation3:max "dk[" κ "; " μ " # " η "; " μ' "]" => rdist κ η μ μ'


-- @@ L51-55 expanded
@[simp]
public lemma rdist_zero_right (κ : Kernel T G) (η : Kernel T' G) (μ : Measure T) :
    rdist κ η μ 0 = 0 := by simp [rdist]


-- @@ L59-59 verbatim
section


-- @@ L61-61 verbatim
variable [Countable T] [MeasurableSingletonClass T] [Countable T'] [MeasurableSingletonClass T']


-- @@ L63-74 expanded
public lemma rdist_eq {κ : Kernel T G} {η : Kernel T' G} {μ : Measure T} {ν : Measure T'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [FiniteSupport μ] [FiniteSupport ν] :
    rdist κ η μ ν =
      (μ.prod ν)[fun p ↦ measureEntropy (((κ p.1).prod (η p.2)).map (fun x ↦ x.1 - x.2))] -
          ProbabilityTheory.Kernel.entropy κ μ / 2 -
        ProbabilityTheory.Kernel.entropy η ν / 2 :=
  by
  rw [rdist]
  simp_rw [rdistm]
  rw [integral_sub, integral_sub]
  · simp_rw [div_eq_mul_inv, integral_mul_const, integral_prod _ (integrable_of_finiteSupport _)]
    simp [entropy]
  all_goals { exact integrable_of_finiteSupport _
  }


-- @@ L76-76 verbatim
variable [MeasurableSingletonClass G] [Countable G]


-- @@ L78-89 expanded
public lemma rdist_eq' {κ : Kernel T G} {η : Kernel T' G} [IsFiniteKernel κ] [IsFiniteKernel η]
    {μ : Measure T} {ν : Measure T'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [FiniteSupport μ] [FiniteSupport ν] :
    rdist κ η μ ν =
      ProbabilityTheory.Kernel.entropy
            (map ((prodMkRight T' κ) ×ₖ (prodMkLeft T η)) (fun x ↦ x.1 - x.2)) (μ.prod ν) -
          ProbabilityTheory.Kernel.entropy κ μ / 2 -
        ProbabilityTheory.Kernel.entropy η ν / 2 :=
  by
  rw [rdist_eq]
  congr with p
  simp only
  rw [map_apply _ (by fun_prop), prod_apply, prodMkLeft_apply, prodMkRight_apply]


-- @@ L91-100 expanded
public lemma rdist_symm {κ : Kernel T G} {η : Kernel T' G} [IsFiniteKernel κ] [IsFiniteKernel η]
    {μ : Measure T} {ν : Measure T'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [FiniteSupport μ] [FiniteSupport ν] : rdist κ η μ ν = rdist η κ ν μ :=
  by
  rw [rdist_eq', rdist_eq', sub_sub, sub_sub, add_comm]
  congr 1
  rw [← entropy_comap_swap, comap_map_comm _ _ (by fun_prop), entropy_sub_comm, Measure.comap_swap,
    Measure.prod_swap, comap_prod_swap, map_map _ (by fun_prop) (by fun_prop)]
  congr


-- @@ L110-120 verbatim
public
lemma ruzsa_triangle_aux {T : Type*} [MeasurableSpace T] (κ : Kernel T (G × G)) (η : Kernel T G)
    [IsMarkovKernel κ] [IsMarkovKernel η] :
    map (κ ×ₖ η) (fun p ↦ p.2 - p.1.2)
      = map (η ×ₖ snd κ) (fun p ↦ p.1 - p.2) := by
  have : (fun p : G × G ↦ p.1 - p.2) = (fun p ↦ p.2 - p.1) ∘ Prod.swap := by ext1 p; simp
  rw [this, ← map_map _ measurable_swap .of_discrete, map_prod_swap]
  ext x s hs
  rw [map_apply' _ (by fun_prop) _ hs, map_apply' _ (by fun_prop) _ hs,
    prod_apply' _ _ _ .of_discrete, prod_apply' _ _ _ .of_discrete, lintegral_snd _ _ .of_discrete]
  congr


-- @@ L122-135 expanded
public lemma abs_sub_entropy_le_rdist {κ : Kernel T G} {η : Kernel T' G} [IsMarkovKernel κ]
    [IsMarkovKernel η] {μ : Measure T} {ν : Measure T'} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [FiniteSupport μ] [FiniteSupport ν] (hκ : AEFiniteKernelSupport κ μ)
    (hη : AEFiniteKernelSupport η ν) :
    |ProbabilityTheory.Kernel.entropy κ μ - ProbabilityTheory.Kernel.entropy η ν| ≤
      2 * rdist κ η μ ν :=
  by
  have h :=
    max_entropy_le_entropy_sub_prod (prodMkRight T' κ) (prodMkLeft T η) (μ.prod ν)
      (hκ.prodMkRight ν) (hη.prodMkLeft μ)
  rw [entropy_prodMkRight', entropy_prodMkLeft] at h
  rw [rdist_eq', abs_le]
  constructor
  ·
    linarith [le_max_right (ProbabilityTheory.Kernel.entropy κ μ)
        (ProbabilityTheory.Kernel.entropy η ν)]
  ·
    linarith [le_max_left (ProbabilityTheory.Kernel.entropy κ μ)
        (ProbabilityTheory.Kernel.entropy η ν)]


-- @@ L137-149 expanded
public lemma rdist_nonneg {κ : Kernel T G} {η : Kernel T' G} [IsMarkovKernel κ] [IsMarkovKernel η]
    {μ : Measure T} {ν : Measure T'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [FiniteSupport μ] [FiniteSupport ν] (hκ : AEFiniteKernelSupport κ μ)
    (hη : AEFiniteKernelSupport η ν) : 0 ≤ rdist κ η μ ν :=
  by
  suffices 0 ≤ 2 * rdist κ η μ ν by linarith
  calc
    0 ≤ |ProbabilityTheory.Kernel.entropy κ μ - ProbabilityTheory.Kernel.entropy η ν| :=
      abs_nonneg _
    _ ≤ 2 * rdist κ η μ ν := abs_sub_entropy_le_rdist hκ hη


-- @@ L150-246 expanded
/-- The **improved entropic Ruzsa triangle inequality**. -/
public lemma ent_of_diff_le (κ : Kernel T (G × G)) (η : Kernel T G) [IsMarkovKernel κ]
    [IsMarkovKernel η] (μ : Measure T) [IsProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : FiniteKernelSupport κ) (hη : FiniteKernelSupport η) :
    ProbabilityTheory.Kernel.entropy (map κ (fun p : G × G ↦ p.1 - p.2)) μ ≤
      ProbabilityTheory.Kernel.entropy (map ((fst κ) ×ₖ η) (fun p : G × G ↦ p.1 - p.2)) μ +
          ProbabilityTheory.Kernel.entropy (map (η ×ₖ (snd κ)) (fun p : G × G ↦ p.1 - p.2)) μ -
        ProbabilityTheory.Kernel.entropy η μ :=
  by
  have hκη := hκ.prod hη
  have h1 :
    ProbabilityTheory.Kernel.entropy (map (κ ×ₖ η) (fun p ↦ (p.1.1 - p.2, (p.1.2, p.1.1 - p.1.2))))
          μ +
        ProbabilityTheory.Kernel.entropy (map κ (fun p ↦ p.1 - p.2)) μ ≤
      ProbabilityTheory.Kernel.entropy (map (κ ×ₖ η) (fun p ↦ (p.1.1 - p.2, p.1.1 - p.1.2))) μ +
        ProbabilityTheory.Kernel.entropy (map κ (fun p ↦ (p.2, p.1 - p.2))) μ :=
    by
    have h :=
      entropy_triple_add_entropy_le (map (κ ×ₖ η) (fun p ↦ (p.1.1 - p.2, (p.1.2, p.1.1 - p.1.2)))) μ
    simp only [snd_map_prod _ .of_discrete] at h
    rw [deleteMiddle_map_prod _ .of_discrete] at h
    have : map (κ ×ₖ η) (fun x ↦ x.1.1 - x.1.2) = map κ (fun p ↦ p.1 - p.2) :=
      by
      have : (fun x : (G × G) × G ↦ x.1.1 - x.1.2) = (fun x ↦ x.1 - x.2) ∘ Prod.fst := by ext1 y;
        simp
      rw [this, ← map_map _ (by fun_prop) (by fun_prop), ← Kernel.fst_eq, fst_prod]
    rw [this] at h
    refine (h ?_).trans_eq ?_
    · apply FiniteKernelSupport.aefiniteKernelSupport
      apply FiniteKernelSupport.map
      exact hκ.prod hη
    congr 2
    have : (fun x : (G × G) × G ↦ (x.1.2, x.1.1 - x.1.2)) = (fun x ↦ (x.2, x.1 - x.2)) ∘ Prod.fst :=
      by ext1 y; simp
    rw [this, ← map_map _ (by fun_prop) (by fun_prop), ← Kernel.fst_eq, fst_prod]
  have h2 :
    ProbabilityTheory.Kernel.entropy (map (κ ×ₖ η) (fun p ↦ (p.1.1 - p.2, p.1.1 - p.1.2))) μ ≤
      ProbabilityTheory.Kernel.entropy (map (κ ×ₖ η) (fun p ↦ p.1.1 - p.2)) μ +
        ProbabilityTheory.Kernel.entropy (map (κ ×ₖ η) (fun p ↦ p.1.2 - p.2)) μ :=
    by
    calc
      ProbabilityTheory.Kernel.entropy (map (κ ×ₖ η) (fun p ↦ (p.1.1 - p.2, p.1.1 - p.1.2))) μ ≤
          ProbabilityTheory.Kernel.entropy (map (κ ×ₖ η) (fun p ↦ (p.1.1 - p.2, p.1.2 - p.2))) μ :=
        by
        have :
          (fun p : (G × G) × G ↦ (p.1.1 - p.2, p.1.1 - p.1.2)) =
            (fun p ↦ (p.1, p.1 - p.2)) ∘ (fun p ↦ (p.1.1 - p.2, p.1.2 - p.2)) :=
          by ext1; simp
        rw [this, ← map_map _ (by fun_prop) (by fun_prop)]
        apply entropy_map_le _ _
        apply FiniteKernelSupport.aefiniteKernelSupport
        apply hκη.map
      _ ≤
          ProbabilityTheory.Kernel.entropy (map (κ ×ₖ η) (fun p ↦ p.1.1 - p.2)) μ +
            ProbabilityTheory.Kernel.entropy (map (κ ×ₖ η) (fun p ↦ p.1.2 - p.2)) μ :=
        by
        have h :
          0 ≤
            ProbabilityTheory.Kernel.entropy (map (κ ×ₖ η) (fun p ↦ p.1.1 - p.2)) μ +
                ProbabilityTheory.Kernel.entropy (map (κ ×ₖ η) (fun p ↦ p.1.2 - p.2)) μ -
              ProbabilityTheory.Kernel.entropy (map (κ ×ₖ η) (fun p ↦ (p.1.1 - p.2, p.1.2 - p.2)))
                μ :=
          by
          have h' :=
            mutualInfo_nonneg (κ := map (κ ×ₖ η) (fun p ↦ (p.1.1 - p.2, p.1.2 - p.2))) (μ := μ) ?_
          · rwa [mutualInfo, fst_map_prod _ .of_discrete, snd_map_prod _ .of_discrete] at h'
          apply FiniteKernelSupport.aefiniteKernelSupport
          apply hκη.map
        linarith
  have h3 :
    ProbabilityTheory.Kernel.entropy (map κ (fun p : G × G ↦ (p.2, p.1 - p.2))) μ ≤
      ProbabilityTheory.Kernel.entropy κ μ :=
    by exact entropy_map_le _ (hκ.aefiniteKernelSupport _)
  have h4 :
    ProbabilityTheory.Kernel.entropy (map (κ ×ₖ η) (fun p ↦ (p.1.1 - p.2, (p.1.2, p.1.1 - p.1.2))))
        μ =
      ProbabilityTheory.Kernel.entropy (κ ×ₖ η) μ :=
    by
    refine
      entropy_of_map_eq_of_map (fun p : G × G × G ↦ ((p.2.2 + p.2.1, p.2.1), -p.1 + p.2.2 + p.2.1))
        (fun p : (G × G) × G ↦ (p.1.1 - p.2, (p.1.2, p.1.1 - p.1.2))) ?_ ?_ ?_
        (hκη.aefiniteKernelSupport _)
    · rw [map_map _ (by fun_prop) (by fun_prop)]
      suffices
        ((fun p : G × G × G ↦ ((p.2.2 + p.2.1, p.2.1), -p.1 + p.2.2 + p.2.1)) ∘ fun p ↦
            (p.1.1 - p.2, p.1.2, p.1.1 - p.1.2)) =
          id
        by simp_rw [this, map_id]
      ext1 p
      simp
    · rfl
    apply FiniteKernelSupport.aefiniteKernelSupport
    apply hκη.map
  have h5 :
    ProbabilityTheory.Kernel.entropy (κ ×ₖ η) μ =
      ProbabilityTheory.Kernel.entropy κ μ + ProbabilityTheory.Kernel.entropy η μ :=
    by rw [entropy_prod (hκ.aefiniteKernelSupport _) (hη.aefiniteKernelSupport _)]
  rw [h4, h5] at h1
  calc
    ProbabilityTheory.Kernel.entropy (map κ (fun p : G × G ↦ p.1 - p.2)) μ ≤
        ProbabilityTheory.Kernel.entropy (map (κ ×ₖ η) (fun p ↦ p.1.1 - p.2)) μ +
            ProbabilityTheory.Kernel.entropy (map (κ ×ₖ η) (fun p ↦ p.1.2 - p.2)) μ -
          ProbabilityTheory.Kernel.entropy η μ :=
      by linarith
    _ =
        ProbabilityTheory.Kernel.entropy (map (κ ×ₖ η) (fun p ↦ p.1.1 - p.2)) μ +
            ProbabilityTheory.Kernel.entropy (map (κ ×ₖ η) (fun p ↦ p.2 - p.1.2)) μ -
          ProbabilityTheory.Kernel.entropy η μ :=
      by
      congr 2
      rw [← entropy_neg, map_map _ (by fun_prop) (by fun_prop)]
      congr with p
      simp
    _ =
        ProbabilityTheory.Kernel.entropy (map ((fst κ) ×ₖ η) (fun p : G × G ↦ p.1 - p.2)) μ +
            ProbabilityTheory.Kernel.entropy (map (η ×ₖ (snd κ)) (fun p : G × G ↦ p.1 - p.2)) μ -
          ProbabilityTheory.Kernel.entropy η μ :=
      by
      congr 3
      · ext x s hs
        rw [map_apply' _ (by fun_prop) _ hs, map_apply' _ (by fun_prop) _ hs, prod_apply',
          prod_apply', lintegral_fst]
        · congr with x
        · exact .of_discrete
        · exact measurable_sub hs
        · exact .of_discrete
      · exact ruzsa_triangle_aux κ η


-- @@ L248-250 verbatim
end

-- note : Measure.prod should be made to use dot notation in the infoview


-- @@ L252-252 verbatim
variable [MeasurableSingletonClass T] [MeasurableSingletonClass T'] [MeasurableSingletonClass T'']

-- @@ L253-253 verbatim
variable [MeasurableSingletonClass G] [Countable G]


-- @@ L255-288 expanded
public lemma rdist_triangle_aux1 (κ : Kernel T G) (η : Kernel T' G) [IsMarkovKernel κ]
    [IsMarkovKernel η] (μ : Measure T) (μ' : Measure T') (μ'' : Measure T'')
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] [IsProbabilityMeasure μ''] [FiniteSupport μ]
    [FiniteSupport μ'] [FiniteSupport μ''] :
    ProbabilityTheory.Kernel.entropy
        (map (prodMkRight T' (prodMkRight T'' κ) ×ₖ prodMkLeft (T × T'') η) (fun p ↦ p.1 - p.2))
        ((μ.prod μ'').prod μ') =
      ProbabilityTheory.Kernel.entropy
        (map (prodMkRight T' κ ×ₖ prodMkLeft T η) (fun x ↦ x.1 - x.2)) (μ.prod μ') :=
  by
  have hAB :
    ∀ᵐ x ∂(μ.prod μ'),
      x ∈ ((μ.finiteSupport ×ˢ μ'.finiteSupport : Finset (T × T')) : Set (T × T')) :=
    Measure.prod_of_full_measure_finset (measure_compl_support μ) (measure_compl_support μ')
  have hAC :
    (μ.prod μ'') ((μ.finiteSupport ×ˢ μ''.finiteSupport : Finset (T × T'')) : Set (T × T''))ᶜ = 0 :=
    Measure.prod_of_full_measure_finset (measure_compl_support μ) (measure_compl_support μ'')
  have hACB :
    ∀ᵐ x ∂(μ.prod μ'').prod μ',
      x ∈
        (((μ.finiteSupport ×ˢ μ''.finiteSupport) ×ˢ μ'.finiteSupport : Finset ((T × T'') × T')) :
          Set ((T × T'') × T')) :=
    Measure.prod_of_full_measure_finset hAC (measure_compl_support μ')
  simp_rw [entropy, integral_eq_setIntegral hAB, integral_eq_setIntegral hACB,
    setIntegral_finset _ .finset, smul_eq_mul, Measure.prod_real_singleton, Finset.sum_product,
    mul_assoc, ← Finset.mul_sum]
  congr with x
  have :
    ∀ z y,
      map (prodMkRight T' (prodMkRight T'' κ) ×ₖ prodMkLeft (T × T'') η) (fun p ↦ p.1 - p.2)
          ((x, z), y) =
        map (prodMkRight T' κ ×ₖ prodMkLeft T η) (fun p ↦ p.1 - p.2) (x, y) :=
    by
    intro z y
    ext s hs
    rw [map_apply' _ (by fun_prop) _ hs, map_apply' _ (by fun_prop) _ hs, prod_apply, prod_apply]
    simp
  simp_rw [this, ← Finset.sum_mul, sum_measureReal_singleton, Measure.real,
    measure_of_measure_compl_eq_zero (measure_compl_support μ'')]
  simp


-- @@ L290-330 expanded
public lemma rdist_triangle_aux2 (η : Kernel T' G) (ξ : Kernel T'' G) [IsMarkovKernel η]
    [IsMarkovKernel ξ] (μ : Measure T) (μ' : Measure T') (μ'' : Measure T'')
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] [IsProbabilityMeasure μ''] [FiniteSupport μ]
    [FiniteSupport μ'] [FiniteSupport μ''] :
    ProbabilityTheory.Kernel.entropy
        (map (prodMkLeft (T × T'') η ×ₖ prodMkRight T' (prodMkLeft T ξ)) (fun p ↦ p.1 - p.2))
        ((μ.prod μ'').prod μ') =
      ProbabilityTheory.Kernel.entropy
        (map (prodMkRight T'' η ×ₖ prodMkLeft T' ξ) (fun x ↦ x.1 - x.2)) (μ'.prod μ'') :=
  by
  have hBC :
    ∀ᵐ x ∂(μ'.prod μ''),
      x ∈ ((μ'.finiteSupport ×ˢ μ''.finiteSupport : Finset (T' × T'')) : Set (T' × T'')) :=
    Measure.prod_of_full_measure_finset (measure_compl_support μ') (measure_compl_support μ'')
  have hAC :
    (μ.prod μ'') ((μ.finiteSupport ×ˢ μ''.finiteSupport : Finset (T × T'')) : Set (T × T''))ᶜ = 0 :=
    Measure.prod_of_full_measure_finset (measure_compl_support μ) (measure_compl_support μ'')
  have hACB :
    ∀ᵐ x ∂(μ.prod μ'').prod μ',
      x ∈
        (((μ.finiteSupport ×ˢ μ''.finiteSupport) ×ˢ μ'.finiteSupport : Finset ((T × T'') × T')) :
          Set ((T × T'') × T')) :=
    Measure.prod_of_full_measure_finset hAC (measure_compl_support μ')
  simp_rw [entropy, integral_eq_setIntegral hACB, integral_eq_setIntegral hBC,
    setIntegral_finset _ .finset, smul_eq_mul, Measure.prod_real_singleton]
  conv_rhs => rw [Finset.sum_product_right]
  conv_lhs => rw [Finset.sum_product, Finset.sum_product_right]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  congr with z
  have :
    ∀ x y,
      map (prodMkLeft (T × T'') η ×ₖ prodMkRight T' (prodMkLeft T ξ)) (fun p ↦ p.1 - p.2)
          ((x, z), y) =
        map (prodMkLeft T'' η ×ₖ prodMkRight T' ξ) (fun p ↦ p.1 - p.2) (z, y) :=
    by
    intro x y
    ext s hs
    rw [map_apply' _ (by fun_prop) _ hs, map_apply' _ (by fun_prop) _ hs, prod_apply, prod_apply]
    simp
  simp_rw [this, ← Finset.sum_mul, sum_measureReal_singleton, Measure.real,
    measure_of_measure_compl_eq_zero (measure_compl_support μ), measure_univ, ENNReal.toReal_one,
    one_mul, ← mul_assoc, mul_comm _ (μ'' { z }).toReal, mul_assoc, ← Finset.mul_sum]
  congr with y
  congr 2 with s _hs
  rw [map_apply _ (by fun_prop), map_apply _ (by fun_prop), prod_apply, prod_apply]
  simp


-- @@ L332-332 verbatim
variable [Countable T] [Countable T'] [Countable T'']


-- @@ L334-376 expanded
public lemma rdist_triangle (κ : Kernel T G) (η : Kernel T' G) (ξ : Kernel T'' G) [IsMarkovKernel κ]
    [IsMarkovKernel η] [IsMarkovKernel ξ] (μ : Measure T) (μ' : Measure T') (μ'' : Measure T'')
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] [IsProbabilityMeasure μ''] [FiniteSupport μ]
    [FiniteSupport μ'] [FiniteSupport μ''] (hκ : FiniteKernelSupport κ) (hη : FiniteKernelSupport η)
    (hξ : FiniteKernelSupport ξ) : rdist κ ξ μ μ'' ≤ rdist κ η μ μ' + rdist η ξ μ' μ'' :=
  by
  rw [rdist_eq', rdist_eq', rdist_eq']
  have h :=
    ent_of_diff_le (prodMkRight T' (prodMkRight T'' κ ×ₖ prodMkLeft T ξ)) (prodMkLeft (T × T'') η)
      ((μ.prod μ'').prod μ') ?_ ?_
  rotate_left
  · apply FiniteKernelSupport.prodMkRight
    apply hκ.prodMkRight.prod hξ.prodMkLeft
  · apply Kernel.FiniteKernelSupport.prodMkLeft hη
  have h1 :
    ProbabilityTheory.Kernel.entropy
        (map (prodMkRight T' (prodMkRight T'' κ ×ₖ prodMkLeft T ξ)) (fun p ↦ p.1 - p.2))
        ((μ.prod μ'').prod μ') =
      ProbabilityTheory.Kernel.entropy
        (map (prodMkRight T'' κ ×ₖ prodMkLeft T ξ) (fun x ↦ x.1 - x.2)) (μ.prod μ'') :=
    by rw [map_prodMkRight, entropy_prodMkRight']
  have h2 :
    ProbabilityTheory.Kernel.entropy
        (map (fst (prodMkRight T' (prodMkRight T'' κ ×ₖ prodMkLeft T ξ)) ×ₖ prodMkLeft (T × T'') η)
          (fun p ↦ p.1 - p.2))
        ((μ.prod μ'').prod μ') =
      ProbabilityTheory.Kernel.entropy
        (map (prodMkRight T' κ ×ₖ prodMkLeft T η) (fun x ↦ x.1 - x.2)) (μ.prod μ') :=
    by
    rw [fst_prodMkRight, fst_prod]
    exact rdist_triangle_aux1 _ _ _ _ _
  have h3 :
    ProbabilityTheory.Kernel.entropy
        (map (prodMkLeft (T × T'') η ×ₖ snd (prodMkRight T' (prodMkRight T'' κ ×ₖ prodMkLeft T ξ)))
          (fun p ↦ p.1 - p.2))
        ((μ.prod μ'').prod μ') =
      ProbabilityTheory.Kernel.entropy
        (map (prodMkRight T'' η ×ₖ prodMkLeft T' ξ) (fun x ↦ x.1 - x.2)) (μ'.prod μ'') :=
    by
    rw [snd_prodMkRight, snd_prod]
    exact rdist_triangle_aux2 _ _ _ _ _
  have h4 :
    ProbabilityTheory.Kernel.entropy (prodMkLeft (T × T'') η) ((μ.prod μ'').prod μ') =
      ProbabilityTheory.Kernel.entropy η μ' :=
    entropy_prodMkLeft
  rw [h1, h2, h3, h4] at h
  calc
    ProbabilityTheory.Kernel.entropy (map (prodMkRight T'' κ ×ₖ prodMkLeft T ξ) (fun x ↦ x.1 - x.2))
              (μ.prod μ'') -
            ProbabilityTheory.Kernel.entropy κ μ / 2 -
          ProbabilityTheory.Kernel.entropy ξ μ'' / 2 ≤
        ProbabilityTheory.Kernel.entropy
                  (map (prodMkRight T' κ ×ₖ prodMkLeft T η) (fun x ↦ x.1 - x.2)) (μ.prod μ') +
                ProbabilityTheory.Kernel.entropy
                  (map (prodMkRight T'' η ×ₖ prodMkLeft T' ξ) (fun x ↦ x.1 - x.2)) (μ'.prod μ'') -
              ProbabilityTheory.Kernel.entropy η μ' -
            ProbabilityTheory.Kernel.entropy κ μ / 2 -
          ProbabilityTheory.Kernel.entropy ξ μ'' / 2 :=
      by gcongr
    _ =
        ProbabilityTheory.Kernel.entropy
                (map (prodMkRight T' κ ×ₖ prodMkLeft T η) (fun x ↦ x.1 - x.2)) (μ.prod μ') -
              ProbabilityTheory.Kernel.entropy κ μ / 2 -
            ProbabilityTheory.Kernel.entropy η μ' / 2 +
          (ProbabilityTheory.Kernel.entropy
                (map (prodMkRight T'' η ×ₖ prodMkLeft T' ξ) (fun x ↦ x.1 - x.2)) (μ'.prod μ'') -
              ProbabilityTheory.Kernel.entropy η μ' / 2 -
            ProbabilityTheory.Kernel.entropy ξ μ'' / 2) :=
      by ring


-- @@ L378-378 verbatim
end ProbabilityTheory.Kernel
