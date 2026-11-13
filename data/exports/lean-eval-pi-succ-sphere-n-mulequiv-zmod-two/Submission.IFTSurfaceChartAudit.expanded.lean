import Mathlib
import Submission.MorseGenericity2D


-- @@ L4-14 verbatim
/-!
# Audit of the global IFT surface-chart interface

The former global `IFTSurfaceChart` API parametrized the entire two-dimensional
Euclidean plane into a fiber whose spatial projection is uniformly bounded,
while ambient linear covectors recover both parameters exactly.  Since only
the one-dimensional time direction can be unbounded, these requirements are
inconsistent.  `GlobalIFTSurfaceChartContract` records that former interface
verbatim so the contradiction remains checkable after the production API is
localized.
-/


-- @@ L16-16 verbatim
noncomputable section


-- @@ L18-18 verbatim
open Set Function Metric

-- @@ L19-19 verbatim
open scoped RealInnerProductSpace ContDiff


-- @@ L21-21 verbatim
namespace Submission


-- @@ L23-23 verbatim
variable {n : ℕ}


-- @@ L25-25 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

-- @@ L26-26 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))


-- @@ L28-39 verbatim
/-- A verbatim copy of the inconsistent, globally quantified fields of the
former `IFTSurfaceChart`.  Smoothness and the value at zero are retained even
though the contradiction needs only `param_fiber` and `lift_param`. -/
structure GlobalIFTSurfaceChartContract (C : FramedLevelCobordism n) where
  center : E'
  param : E₂ → E'
  param_smooth : ContDiff ℝ ∞ param
  param_zero : param 0 = center
  param_fiber : ∀ u, C.G (param u) = 0
  liftCovector : E₂ →ₗ[ℝ] (E' →L[ℝ] ℝ)
  lift_param : ∀ q u,
    liftCovector q (param u - center) = (innerSL ℝ q) u


-- @@ L41-41 verbatim
namespace GlobalIFTSurfaceChartContract


-- @@ L43-43 verbatim
variable {C : FramedLevelCobordism n}


-- @@ L45-45 verbatim
private def auditE0 : E₂ := EuclideanSpace.single 0 1

-- @@ L46-46 verbatim
private def auditE1 : E₂ := EuclideanSpace.single 1 1


-- @@ L48-49 verbatim
@[simp] private theorem auditE0_zero : (auditE0 : E₂) 0 = 1 := by
  simp [auditE0]


-- @@ L51-52 verbatim
@[simp] private theorem auditE0_one : (auditE0 : E₂) 1 = 0 := by
  simp [auditE0]


-- @@ L54-55 verbatim
@[simp] private theorem auditE1_zero : (auditE1 : E₂) 0 = 0 := by
  simp [auditE1]


-- @@ L57-58 verbatim
@[simp] private theorem auditE1_one : (auditE1 : E₂) 1 = 1 := by
  simp [auditE1]


-- @@ L60-66 verbatim
/-- The coefficient with which a lifted chart covector sees the unique
unbounded ambient time direction. -/
def timeCoefficient (P : GlobalIFTSurfaceChartContract (n := n) C) :
    E₂ →ₗ[ℝ] ℝ where
  toFun q := P.liftCovector q (timeVec (n := n))
  map_add' q r := by simp
  map_smul' c q := by simp


-- @@ L68-87 verbatim
/-- A nonzero chart covector which kills the ambient time direction.  It exists
because chart covectors have dimension two while time has dimension one. -/
theorem exists_ne_zero_timeCoefficient_eq_zero
    (P : GlobalIFTSurfaceChartContract (n := n) C) :
    ∃ q : E₂, q ≠ 0 ∧ P.timeCoefficient q = 0 := by
  let a : ℝ := P.timeCoefficient auditE0
  let b : ℝ := P.timeCoefficient auditE1
  by_cases ha : a = 0
  · exact ⟨auditE0, by
      intro h
      have h0 := congrArg (fun q : E₂ => q 0) h
      simp at h0, ha⟩
  · let q : E₂ := b • auditE0 - a • auditE1
    refine ⟨q, ?_, ?_⟩
    · intro h
      have h1 := congrArg (fun q : E₂ => q 1) h
      simp [q] at h1
      exact ha h1
    · simp [q, a, b]
      ring


-- @@ L89-153 verbatim
/-- The globally quantified surface-chart contract is inconsistent with the
spatial boundedness required of every level cobordism. -/
theorem false_of_global_chart
    (P : GlobalIFTSurfaceChartContract (n := n) C) : False := by
  obtain ⟨R, hR⟩ := C.spatial_bounded
  have hR_nonneg : 0 ≤ R := by
    exact le_trans (norm_nonneg (spacePart (P.param 0)))
      (hR (P.param 0) (P.param_fiber 0))
  obtain ⟨q, hq, hqtime⟩ := P.exists_ne_zero_timeCoefficient_eq_zero
  let K : ℝ := ‖P.liftCovector q‖ * (R + ‖spacePart P.center‖)
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hqnorm : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  have hqnorm_sq : ‖q‖ ^ 2 ≠ 0 := pow_ne_zero 2 hqnorm
  let r : ℝ := (K + 1) / ‖q‖ ^ 2
  let u : E₂ := r • q
  let w : E' := P.param u - P.center
  have hw_decomp : w =
      spaceInclL (spacePart w) + tcoord w • timeVec := by
    rw [← spaceTime_eq, spaceTime_spacePart]
  have hw_value : P.liftCovector q w =
      P.liftCovector q (spaceInclL (spacePart w)) := by
    calc
      P.liftCovector q w = P.liftCovector q
          (spaceInclL (spacePart w) + tcoord w • timeVec) :=
        congrArg (P.liftCovector q) hw_decomp
      _ = P.liftCovector q (spaceInclL (spacePart w)) := by
        rw [map_add, map_smul]
        change P.liftCovector q (spaceInclL (spacePart w)) +
          tcoord w * P.timeCoefficient q = _
        rw [hqtime, mul_zero, add_zero]
  have hw_spatial : ‖spacePart w‖ ≤ R + ‖spacePart P.center‖ := by
    have hp_bound : ‖spacePart (P.param u)‖ ≤ R := by
      simpa [spacePart, initCLM, initLM] using
        hR (P.param u) (P.param_fiber u)
    calc
      ‖spacePart w‖ = ‖spacePart (P.param u) - spacePart P.center‖ := rfl
      _ ≤ ‖spacePart (P.param u)‖ + ‖spacePart P.center‖ := norm_sub_le _ _
      _ ≤ R + ‖spacePart P.center‖ := by
        simpa [add_comm] using
          add_le_add_right hp_bound ‖spacePart P.center‖
  have hw_bound : ‖P.liftCovector q w‖ ≤ K := by
    rw [hw_value]
    calc
      ‖P.liftCovector q (spaceInclL (spacePart w))‖ ≤
          ‖P.liftCovector q‖ * ‖spaceInclL (spacePart w)‖ :=
        (P.liftCovector q).le_opNorm _
      _ = ‖P.liftCovector q‖ * ‖spacePart w‖ := by
        rw [norm_spaceInclL]
      _ ≤ ‖P.liftCovector q‖ * (R + ‖spacePart P.center‖) :=
        mul_le_mul_of_nonneg_left hw_spatial (norm_nonneg _)
      _ = K := rfl
  have hrecover : P.liftCovector q w = r * ‖q‖ ^ 2 := by
    rw [P.lift_param]
    change inner ℝ q (r • q) = r * ‖q‖ ^ 2
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hr : r * ‖q‖ ^ 2 = K + 1 := by
    dsimp [r]
    exact div_mul_cancel₀ (K + 1) hqnorm_sq
  have hlarge : ‖P.liftCovector q w‖ = K + 1 := by
    rw [hrecover, hr, Real.norm_eq_abs, abs_of_nonneg]
    linarith
  rw [hlarge] at hw_bound
  linarith


-- @@ L155-159 verbatim
/-- In particular, no object of the current global chart structure exists. -/
theorem not_nonempty_global_chart (C : FramedLevelCobordism n) :
    ¬ Nonempty (GlobalIFTSurfaceChartContract C) := by
  rintro ⟨P⟩
  exact P.false_of_global_chart


-- @@ L161-161 verbatim
end GlobalIFTSurfaceChartContract


-- @@ L163-163 verbatim
end Submission
