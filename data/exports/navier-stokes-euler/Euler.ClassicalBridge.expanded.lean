import Euler.SolutionDefinitions
import Mathlib.Analysis.Calculus.ContDiff.Operations


-- @@ L4-5 verbatim
/-! Ordinary spatial smoothness, finite energy, and the pointwise time equation
follow from the independent Comparator solution class. -/


-- @@ L7-7 verbatim
noncomputable section


-- @@ L9-9 verbatim
open Set MeasureTheory

-- @@ L10-10 verbatim
open scoped ContDiff Topology


-- @@ L12-12 verbatim
namespace Euler.EulerExistenceAndSmoothnessR3


-- @@ L14-14 verbatim
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)


-- @@ L16-17 verbatim
variable {u₀ : ℝ³ → ℝ³} {v : ℝ³ → ℝ → ℝ³} {p : ℝ³ → ℝ → ℝ}
  (h : EulerExistenceAndSmoothnessR3 u₀ v p)


-- @@ L19-19 verbatim
include h


-- @@ L21-23 verbatim
theorem velocity_contDiff (t : ℝ) (ht : 0 ≤ t) : ContDiff ℝ ∞ (v · t) := by
  exact h.velocity_smooth.comp_contDiff (contDiff_id.prodMk contDiff_const)
    (fun x => ⟨mem_univ x, ht⟩)


-- @@ L25-27 verbatim
theorem pressure_contDiff (t : ℝ) (ht : 0 ≤ t) : ContDiff ℝ ∞ (p · t) := by
  exact h.pressure_smooth.comp_contDiff (contDiff_id.prodMk contDiff_const)
    (fun x => ⟨mem_univ x, ht⟩)


-- @@ L29-31 verbatim
theorem velocity_memLp (t : ℝ) (ht : 0 ≤ t) : MemLp (v · t) 2 volume := by
  exact (memLp_norm_iff (h.velocity_contDiff t ht).continuous.aestronglyMeasurable).mp
    (h.integrable t ht)


-- @@ L33-47 verbatim
theorem pointwise_euler (x : ℝ³) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (v x ·)
      (-fderiv ℝ (v · t) x (v x t) - gradient (p · t) x) t := by
  have hs : ContDiffOn ℝ ∞ (v x ·) (Ici 0) :=
    h.velocity_smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun r hr => ⟨mem_univ x, hr⟩)
  have hd : DifferentiableAt ℝ (v x ·) t :=
    (hs.differentiableOn (by simp) t ht.le).differentiableAt (Ici_mem_nhds ht)
  have he := h.euler x t ht.le
  rw [derivWithin_of_mem_nhds (Ici_mem_nhds ht)] at he
  have he' : deriv (v x ·) t =
      -fderiv ℝ (v · t) x (v x t) - gradient (p · t) x := by
    simpa only [sub_eq_add_neg, add_comm] using eq_sub_of_add_eq he
  rw [← he']
  exact hd.hasDerivAt


-- @@ L49-49 verbatim
end Euler.EulerExistenceAndSmoothnessR3
