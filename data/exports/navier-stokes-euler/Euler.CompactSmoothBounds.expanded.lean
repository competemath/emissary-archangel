import Euler.ClassicalBridge
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.Normed.Group.Bounded


-- @@ L5-6 verbatim
/-! Joint smoothness in the reference bounds spatial derivatives on every fixed
compact spatial set and closed finite time interval, including time zero. -/


-- @@ L8-8 verbatim
noncomputable section


-- @@ L10-10 verbatim
open Set Filter MeasureTheory ContinuousLinearMap

-- @@ L11-11 verbatim
open scoped ContDiff Topology


-- @@ L13-13 verbatim
namespace Euler.EulerExistenceAndSmoothnessR3


-- @@ L15-15 verbatim
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)


-- @@ L17-18 verbatim
variable {u₀ : ℝ³ → ℝ³} {v : ℝ³ → ℝ → ℝ³} {p : ℝ³ → ℝ → ℝ}
  (h : EulerExistenceAndSmoothnessR3 u₀ v p)


-- @@ L20-20 verbatim
include h


-- @@ L22-30 verbatim
theorem spatial_fderiv_eq_within (x : ℝ³) (t : ℝ) (ht : 0 ≤ t) :
    fderiv ℝ (v · t) x =
      (fderivWithin ℝ (Function.uncurry v) (univ ×ˢ Ici 0) (x, t)).comp
        (inl ℝ ℝ³ ℝ) := by
  have hd := (h.velocity_smooth.differentiableOn (by simp) (x, t)
    ⟨mem_univ x, ht⟩).hasFDerivWithinAt
  exact (hd.comp_hasFDerivAt (f := fun y : ℝ³ => (y, t)) x
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t)
    (Eventually.of_forall (fun y => ⟨mem_univ y, ht⟩))).fderiv


-- @@ L32-39 verbatim
theorem spatial_fderiv_continuousOn :
    ContinuousOn (fun z : ℝ³ × ℝ => fderiv ℝ (v · z.2) z.1)
      (univ ×ˢ Ici 0) := by
  have hc := h.velocity_smooth.continuousOn_fderivWithin
    (uniqueDiffOn_univ.prod (uniqueDiffOn_Ici 0)) (by simp)
  apply (hc.clm_comp (continuousOn_const (c := inl ℝ ℝ³ ℝ))).congr
  intro z hz
  exact h.spatial_fderiv_eq_within z.1 z.2 hz.2


-- @@ L41-48 verbatim
theorem spatial_fderiv_bounded_on_compact (K : Set ℝ³) (hK : IsCompact K)
    (T : ℝ) : ∃ C : ℝ, ∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) T,
      ‖fderiv ℝ (v · t) x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (hK.prod isCompact_Icc).exists_bound_of_continuousOn
    (h.spatial_fderiv_continuousOn.mono
      (show K ×ˢ Icc (0 : ℝ) T ⊆ univ ×ˢ Ici 0 from
        fun _ hz => ⟨mem_univ _, hz.2.1⟩))
  exact ⟨C, fun x hx t ht => hC (x, t) ⟨hx, ht⟩⟩


-- @@ L50-50 verbatim
end Euler.EulerExistenceAndSmoothnessR3
