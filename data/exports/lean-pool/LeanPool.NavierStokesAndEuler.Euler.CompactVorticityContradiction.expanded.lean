/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerMaximal
public import LeanPool.NavierStokesAndEuler.Euler.SolutionDefinitions
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerBKM
public import LeanPool.NavierStokesAndEuler.Euler.MeanCutoffCurlBound
import LeanPool.NavierStokesAndEuler.Euler.ClassicalBridge
import LeanPool.NavierStokesAndEuler.Euler.CurlTimeDerivative
import Mathlib.Analysis.Calculus.TangentCone.Prod


-- @@ L16-18 verbatim
/-! A classical comparison field with uniformly confined vorticity cannot
agree with the maximal ordinary solution throughout a finite lifespan.
The contradiction uses the proved Beale--Kato--Majda integral criterion. -/


-- @@ L20-20 verbatim
section


-- @@ L22-23 verbatim
/-! Joint smoothness in the reference bounds spatial derivatives on every fixed
compact spatial set and closed finite time interval, including time zero. -/


-- @@ L25-25 verbatim
@[expose] public section


-- @@ L27-27 verbatim
noncomputable section


-- @@ L29-29 verbatim
open Set Filter MeasureTheory ContinuousLinearMap

-- @@ L30-30 verbatim
open scoped ContDiff Topology


-- @@ L32-32 verbatim
namespace Euler.EulerExistenceAndSmoothnessR3


-- @@ L34-34 verbatim
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)


-- @@ L36-37 verbatim
variable {u₀ : ℝ³ → ℝ³} {v : ℝ³ → ℝ → ℝ³} {p : ℝ³ → ℝ → ℝ}
  (h : EulerExistenceAndSmoothnessR3 u₀ v p)


-- @@ L39-39 verbatim
include h


-- @@ L41-49 verbatim
theorem spatial_fderiv_eq_within (x : ℝ³) (t : ℝ) (ht : 0 ≤ t) :
    fderiv ℝ (v · t) x =
      (fderivWithin ℝ (Function.uncurry v) (univ ×ˢ Ici 0) (x, t)).comp
        (inl ℝ ℝ³ ℝ) := by
  have hd := (h.velocity_smooth.differentiableOn (by simp) (x, t)
    ⟨mem_univ x, ht⟩).hasFDerivWithinAt
  exact (hd.comp_hasFDerivAt (f := fun y : ℝ³ => (y, t)) x
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t)
    (Eventually.of_forall (fun y => ⟨mem_univ y, ht⟩))).fderiv


-- @@ L51-58 verbatim
theorem spatial_fderiv_continuousOn :
    ContinuousOn (fun z : ℝ³ × ℝ => fderiv ℝ (v · z.2) z.1)
      (univ ×ˢ Ici 0) := by
  have hc := h.velocity_smooth.continuousOn_fderivWithin
    (uniqueDiffOn_univ.prod (uniqueDiffOn_Ici 0)) (by simp)
  apply (hc.clm_comp (continuousOn_const (c := inl ℝ ℝ³ ℝ))).congr
  intro z hz
  exact h.spatial_fderiv_eq_within z.1 z.2 hz.2


-- @@ L60-67 verbatim
theorem spatial_fderiv_bounded_on_compact (K : Set ℝ³) (hK : IsCompact K)
    (T : ℝ) : ∃ C : ℝ, ∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) T,
      ‖fderiv ℝ (v · t) x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (hK.prod isCompact_Icc).exists_bound_of_continuousOn
    (h.spatial_fderiv_continuousOn.mono
      (show K ×ˢ Icc (0 : ℝ) T ⊆ univ ×ˢ Ici 0 from
        fun _ hz => ⟨mem_univ _, hz.2.1⟩))
  exact ⟨C, fun x hx t ht => hC (x, t) ⟨hx, ht⟩⟩


-- @@ L69-69 verbatim
end Euler.EulerExistenceAndSmoothnessR3


-- @@ L71-71 verbatim
end

-- @@ L72-72 verbatim
end


-- @@ L74-74 verbatim
end


-- @@ L76-76 verbatim
section


-- @@ L78-79 verbatim
/-! Joint smoothness bounds the actual spatial vorticity on every fixed
compact spatial set and every closed finite time interval. -/


-- @@ L81-81 verbatim
@[expose] public section


-- @@ L83-83 verbatim
noncomputable section


-- @@ L85-85 verbatim
open Set EulerSmoothLimit EulerMeanBoundary EulerMeanCutoffCurl


-- @@ L87-87 verbatim
namespace Euler.EulerExistenceAndSmoothnessR3


-- @@ L89-90 verbatim
variable {u₀ : Space → Space} {v : Space → ℝ → Space} {p : Space → ℝ → ℝ}
  (h : EulerExistenceAndSmoothnessR3 u₀ v p)


-- @@ L92-92 verbatim
include h


-- @@ L94-105 verbatim
theorem vorticity_bounded_on_compact (K : Set Space) (hK : IsCompact K) (T : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      ‖vectorCurl (v · t) x‖ ≤ M := by
  obtain ⟨C, hC⟩ := h.spatial_fderiv_bounded_on_compact K hK T
  refine ⟨‖ComparatorBridge.curlMatrixCLM‖ * max C 0,
    mul_nonneg (norm_nonneg ComparatorBridge.curlMatrixCLM) (le_max_right _ _), ?_⟩
  intro t ht x hx
  rw [vectorCurl_eq_matrix _ x ((h.velocity_contDiff t ht.1).differentiable (by simp) x)]
  change ‖ComparatorBridge.curlMatrixCLM (fderiv ℝ (v · t) x)‖ ≤ _
  exact (ComparatorBridge.curlMatrixCLM.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left ((hC x hx t ht).trans (le_max_left _ _))
      (norm_nonneg ComparatorBridge.curlMatrixCLM))


-- @@ L107-107 verbatim
end Euler.EulerExistenceAndSmoothnessR3


-- @@ L109-109 verbatim
end

-- @@ L110-110 verbatim
end


-- @@ L112-112 verbatim
end


-- @@ L114-114 verbatim
@[expose] public section


-- @@ L116-116 verbatim
noncomputable section


-- @@ L118-119 verbatim
open Set EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerOrdinarySobolev EulerVectorCalculus EulerMeanBoundary EulerMeanCutoffCurl


-- @@ L121-121 verbatim
namespace Euler.ComparatorBridge


-- @@ L123-124 verbatim
variable {A : SmoothL2Field Space} (L : FiniteLifespan A)
  {v : Space → ℝ → Space} {p : Space → ℝ → ℝ}


-- @@ L126-147 verbatim
theorem finiteLifespan_contradiction_of_compact_vorticity
    (h : EulerExistenceAndSmoothnessR3 A.field v p)
    (K : Set Space) (hK : IsCompact K)
    (hmatch : ∀ t : L.Time, L.maximalVelocity t = (v · (t : ℝ)))
    (hsupport : ∀ (t : L.Time) x, x ∉ K →
      vectorCurl (L.maximalVelocity t) x = 0) : False := by
  obtain ⟨M, hM, hbound⟩ := h.vorticity_bounded_on_compact K hK L.duration
  have hcurl : ∀ (t : L.Time) x, ‖vectorCurl (L.maximalVelocity t) x‖ ≤ M := by
    intro t x
    by_cases hx : x ∈ K
    · rw [hmatch t]
      exact hbound t ⟨t.property.1, t.property.2.le⟩ x hx
    · rw [hsupport t x hx, norm_zero]
      exact hM
  obtain ⟨S, hS, hSL, t, hlarge⟩ := L.vorticityIntegral_unbounded (M * L.duration)
  have hbound : ∀ s x, ‖vectorCurl ((L.evolution S hS hSL).velocity s).field x‖ ≤ M := by
    intro s x
    rw [← L.maximalVelocity_eq_evolution S hS hSL s]
    exact hcurl _ x
  have hupper := (L.evolution S hS hSL).vorticityIntegral_le_const M hbound t
  have ht : (t : ℝ) ≤ L.duration := t.property.2.trans hSL.le
  exact (not_lt_of_ge (hupper.trans (mul_le_mul_of_nonneg_left ht hM))) hlarge


-- @@ L149-149 verbatim
end Euler.ComparatorBridge
