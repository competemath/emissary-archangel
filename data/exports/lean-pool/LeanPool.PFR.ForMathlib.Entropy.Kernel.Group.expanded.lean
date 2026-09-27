/-
Copyright (c) 2026 PFR contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PFR contributors
-/

module

public import LeanPool.ZhangYeungInequality.PFR.ForMathlib.Entropy.Kernel.MutualInfo


-- @@ L11-18 verbatim
/-!
# Kernel entropy and mutual information in a commutative group

## Main definitions

## Main results

-/



-- @@ L21-21 verbatim
open MeasureTheory ProbabilityTheory


-- @@ L23-26 verbatim
variable {Ω Ω' Ω'' Ω''' G T : Type*}
  [MeasurableSpace T]
  [MeasurableSpace G] [MeasurableSingletonClass G] [Group G] [Countable G]
  {κ : Kernel T G} {μ : Measure T}






-- @@ L32-32 verbatim
namespace ProbabilityTheory.Kernel


-- @@ L34-37 expanded
@[to_additive]
public lemma entropy_inv (κ : Kernel T G) (μ : Measure T) :
    ProbabilityTheory.Kernel.entropy (map κ (·⁻¹)) μ = ProbabilityTheory.Kernel.entropy κ μ :=
  entropy_map_of_injective κ μ inv_injective measurable_inv


-- @@ L39-46 expanded
@[to_additive]
public lemma entropy_div_comm (κ : Kernel T (G × G)) (μ : Measure T) :
    ProbabilityTheory.Kernel.entropy (map κ (fun p ↦ p.1 / p.2)) μ =
      ProbabilityTheory.Kernel.entropy (map κ (fun p ↦ p.2 / p.1)) μ :=
  by
  rw [← entropy_inv, Kernel.map_map _ (by fun_prop) (by fun_prop)]
  congr with x
  simp


-- @@ L48-48 verbatim
variable [Countable T] [MeasurableSingletonClass T]


-- @@ L50-56 expanded
@[to_additive]
public lemma entropy_snd_sub_mutualInfo_le_entropy_map_mul (κ : Kernel T (G × G))
    [IsZeroOrMarkovKernel κ] (μ : Measure T) [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    ProbabilityTheory.Kernel.entropy (snd κ) μ - Kernel.mutualInfo κ μ ≤
      ProbabilityTheory.Kernel.entropy (map κ (fun p ↦ p.1 * p.2)) μ :=
  entropy_snd_sub_mutualInfo_le_entropy_map_of_injective κ μ _ mul_right_injective hκ


-- @@ L58-64 expanded
@[to_additive]
public lemma entropy_snd_sub_mutualInfo_le_entropy_map_mul' (κ : Kernel T (G × G))
    [IsZeroOrMarkovKernel κ] (μ : Measure T) [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    ProbabilityTheory.Kernel.entropy (snd κ) μ - Kernel.mutualInfo κ μ ≤
      ProbabilityTheory.Kernel.entropy (map κ (fun p ↦ p.2 * p.1)) μ :=
  entropy_snd_sub_mutualInfo_le_entropy_map_of_injective κ μ _ mul_left_injective hκ


-- @@ L66-76 expanded
@[to_additive]
public lemma entropy_fst_sub_mutualInfo_le_entropy_map_mul (κ : Kernel T (G × G))
    [IsZeroOrMarkovKernel κ] (μ : Measure T) [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    ProbabilityTheory.Kernel.entropy (fst κ) μ - Kernel.mutualInfo κ μ ≤
      ProbabilityTheory.Kernel.entropy (map κ (fun p ↦ p.1 * p.2)) μ :=
  by
  have h := entropy_snd_sub_mutualInfo_le_entropy_map_mul' (swapRight κ) μ hκ.swapRight
  simp only [snd_swapRight, mutualInfo_swapRight, map_swapRight] at h
  refine h.trans_eq ?_
  have : (fun p : G × G ↦ p.2 * p.1) ∘ Prod.swap = (fun p ↦ p.1 * p.2) := rfl
  simp_rw [this]


-- @@ L80-86 expanded
@[to_additive]
public lemma entropy_snd_sub_mutualInfo_le_entropy_map_div (κ : Kernel T (G × G))
    [IsZeroOrMarkovKernel κ] (μ : Measure T) [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    ProbabilityTheory.Kernel.entropy (snd κ) μ - Kernel.mutualInfo κ μ ≤
      ProbabilityTheory.Kernel.entropy (map κ (fun p ↦ p.1 / p.2)) μ :=
  entropy_snd_sub_mutualInfo_le_entropy_map_of_injective κ μ _ (fun _ ↦ div_right_injective) hκ


-- @@ L88-99 expanded
@[to_additive]
public lemma entropy_fst_sub_mutualInfo_le_entropy_map_div (κ : Kernel T (G × G))
    [IsZeroOrMarkovKernel κ] (μ : Measure T) [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    ProbabilityTheory.Kernel.entropy (fst κ) μ - Kernel.mutualInfo κ μ ≤
      ProbabilityTheory.Kernel.entropy (map κ (fun p ↦ p.1 / p.2)) μ :=
  by
  have h := entropy_snd_sub_mutualInfo_le_entropy_map_div (swapRight κ) μ hκ.swapRight
  simp only [snd_swapRight, mutualInfo_swapRight, map_swapRight] at h
  refine h.trans_eq ?_
  have : (fun p : G × G ↦ p.1 / p.2) ∘ Prod.swap = (fun p ↦ p.2 / p.1) := rfl
  simp_rw [this]
  rw [← entropy_div_comm]


-- @@ L101-110 expanded
@[to_additive]
public lemma max_entropy_sub_mutualInfo_le_entropy_mul (κ : Kernel T (G × G))
    [IsZeroOrMarkovKernel κ] (μ : Measure T) [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    max (ProbabilityTheory.Kernel.entropy (fst κ) μ) (ProbabilityTheory.Kernel.entropy (snd κ) μ) -
        Kernel.mutualInfo κ μ ≤
      ProbabilityTheory.Kernel.entropy (map κ (fun p ↦ p.1 * p.2)) μ :=
  by
  rw [← max_sub_sub_right, max_le_iff]
  exact
    ⟨entropy_fst_sub_mutualInfo_le_entropy_map_mul _ _ hκ,
      entropy_snd_sub_mutualInfo_le_entropy_map_mul _ _ hκ⟩


-- @@ L114-123 expanded
@[to_additive]
public lemma max_entropy_sub_mutualInfo_le_entropy_div (κ : Kernel T (G × G))
    [IsZeroOrMarkovKernel κ] (μ : Measure T) [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    max (ProbabilityTheory.Kernel.entropy (fst κ) μ) (ProbabilityTheory.Kernel.entropy (snd κ) μ) -
        Kernel.mutualInfo κ μ ≤
      ProbabilityTheory.Kernel.entropy (map κ (fun p ↦ p.1 / p.2)) μ :=
  by
  rw [← max_sub_sub_right, max_le_iff]
  exact
    ⟨entropy_fst_sub_mutualInfo_le_entropy_map_div _ _ hκ,
      entropy_snd_sub_mutualInfo_le_entropy_map_div _ _ hκ⟩


-- @@ L127-140 expanded
@[to_additive max_entropy_le_entropy_sub_prod]
public lemma max_entropy_le_entropy_div_prod (κ : Kernel T G) [IsMarkovKernel κ] (η : Kernel T G)
    [IsMarkovKernel η] (μ : Measure T) [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) (hη : AEFiniteKernelSupport η μ) :
    max (ProbabilityTheory.Kernel.entropy κ μ) (ProbabilityTheory.Kernel.entropy η μ) ≤
      ProbabilityTheory.Kernel.entropy (map (κ ×ₖ η) (fun p ↦ p.1 / p.2)) μ :=
  by
  calc
    max (ProbabilityTheory.Kernel.entropy κ μ) (ProbabilityTheory.Kernel.entropy η μ) =
        max (ProbabilityTheory.Kernel.entropy κ μ) (ProbabilityTheory.Kernel.entropy η μ) -
          Kernel.mutualInfo (κ ×ₖ η) μ :=
      by rw [mutualInfo_prod _ hκ hη, sub_zero]
    _ ≤ ProbabilityTheory.Kernel.entropy (map (κ ×ₖ η) (fun p ↦ p.1 / p.2)) μ :=
      by
      convert max_entropy_sub_mutualInfo_le_entropy_div (κ ×ₖ η) μ (hκ.prod hη)
      · simp
      · simp


-- @@ L142-142 verbatim
end ProbabilityTheory.Kernel
