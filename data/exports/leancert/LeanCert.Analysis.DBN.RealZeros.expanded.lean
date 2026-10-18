import LeanCert.Analysis.DBN.ShiftLimit
import LeanCert.Analysis.DBN.HeatLimit


-- @@ L4-12 verbatim
/-!
# Real zeros at time one half

The unconditional endpoint theorem for the actual DBN heat integral. The proof
uses symmetric polynomial approximation, finite imaginary-shift contraction,
and two zero-preserving locally uniform limits. No finite-height certificate
or assumed approximation theorem is involved. This is not yet a definition or
bound for a real-valued de Bruijn–Newman constant.
-/

-- @@ L13-13 verbatim
namespace LeanCert.Analysis.DBN

-- @@ L14-14 verbatim
open Complex Set Filter

-- @@ L15-15 verbatim
open scoped Topology


-- @@ L17-18 verbatim
theorem unitShift_real (n : ℕ) {z : ℂ} (hz : unitShift n z = 0) : z.im = 0 :=
  shiftIter_H_unit_real (n+1) (Nat.succ_pos n) hz


-- @@ L20-27 verbatim
/-- Every zero of the actual heat-flow function at time `1/2` is real. -/
theorem H_half_real_zeros (z : ℂ) (hz : H (1/2) z = 0) : z.im = 0 := by
  apply H_zero_stripApproximation.heat_limit_real (H_entire 0) (H_entire (1/2))
    (a := fun k => Real.sqrt (1 / ((k+1 : ℕ) : ℝ))) (n := fun k => k+1)
    (fun k => Real.sqrt_pos.mpr (by positivity))
    (fun k => by simpa using (unitShift_budget k).ge)
    (fun k => ⟨0, shiftIter_H_ne_zero 0 _ _⟩)
    ⟨0, H_zero_ne_zero (1/2)⟩ unitShift_convergence hz


-- @@ L29-30 verbatim
theorem H_half_ne_zero_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) : H (1/2) z ≠ 0 :=
  fun h => hz (H_half_real_zeros z h)


-- @@ L32-32 verbatim
end LeanCert.Analysis.DBN
