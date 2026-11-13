import Mathlib
import Submission.FlatConfigurationAssembly
import Submission.FiberSign


-- @@ L5-15 verbatim
/-!
# Spatial flatness of every bridge presentation

The plateaued representative used by `BridgeData` is the south pole on the
closed ambient collar.  Consequently its horizontal part vanishes there and
the bridge defining map is the literal constant `-B.y` outside one explicit
ball.  This file packages that observation as a `FlatSignedConfiguration`.

This is the bridge-side input needed by the separated-support compact Morse
calculus: no extra flattening homotopy is required at spatial infinity.
-/


-- @@ L17-17 verbatim
set_option autoImplicit false


-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
open Set Function Metric

-- @@ L22-22 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L24-24 verbatim
namespace Submission

-- @@ L25-25 verbatim
namespace BridgeData


-- @@ L27-27 verbatim
variable {n : ℕ}

-- @@ L28-28 verbatim
variable {z : StableSpherePi n}


-- @@ L30-30 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L32-64 verbatim
/-- A point outside the explicit bridge ball lies in the closed ambient
collar on which the plateaued representative is constant. -/
theorem mem_closedAmbientCollar_of_bridgeRadius_le_norm
    (_B : BridgeData n z) {x : E}
    (hx : (n + 2 : ℝ) ≤ ‖x‖) :
    WithLp.ofLp x ∈ closedAmbientCollar (Fin (n + 1)) := by
  by_contra hnc
  have hcoord : ∀ i, |x i| ≤ 1 := by
    intro i
    have hnot : ¬(x i ≤ 1 / 5 ∨ 4 / 5 ≤ x i) := fun h =>
      hnc ⟨i, h⟩
    rw [not_or, not_le, not_le] at hnot
    exact abs_le.mpr ⟨by linarith [hnot.1], by linarith [hnot.2]⟩
  have hnorm : ‖x‖ ≤ n + 1 := by
    have hsq : ‖x‖ ^ 2 = ∑ i, x i ^ 2 := norm_sq_eq_sum x
    have hsum : (∑ i, x i ^ 2) ≤ ∑ _i : Fin (n + 1), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have hi := hcoord i
      nlinarith [abs_nonneg (x i), sq_abs (x i)]
    have hone : (∑ _i : Fin (n + 1), (1 : ℝ)) = n + 1 := by
      simp
    have hsq' : ‖x‖ ^ 2 ≤ ((n : ℝ) + 1) ^ 2 := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hn1 : (n : ℝ) + 1 ≤ ((n : ℝ) + 1) ^ 2 := by
        nlinarith
      calc
        ‖x‖ ^ 2 = ∑ i, x i ^ 2 := hsq
        _ ≤ n + 1 := hsum.trans_eq hone
        _ ≤ ((n : ℝ) + 1) ^ 2 := hn1
    nlinarith [norm_nonneg x]
  have hgap : (n + 1 : ℝ) < n + 2 := by norm_num
  exact (not_lt_of_ge hnorm) (hgap.trans_le hx)


-- @@ L66-78 verbatim
/-- Every bridge defining map is exactly its native nonzero background `-y`
outside the explicit radius `n + 2`. -/
theorem fls_flatOutside (B : BridgeData n z) :
    B.fls.FlatOutside (-B.y) 0 (n + 2) := by
  intro x hx
  rw [dist_zero_right] at hx
  have hcollar := B.mem_closedAmbientCollar_of_bridgeRadius_le_norm hx
  change bridgeHMapE B.approx x - B.y = -B.y
  have hzero : bridgeHMapE B.approx x = 0 := by
    change bridgeHMap B.approx (WithLp.ofLp x) = 0
    exact bridgeHMap_of_mem_collar B.approx hcollar
  rw [hzero]
  exact zero_sub B.y


-- @@ L80-82 verbatim
/-- The native background of a bridge is nonzero. -/
theorem nativeBackground_ne_zero (B : BridgeData n z) : -B.y ≠ 0 :=
  neg_ne_zero.mpr B.y_ne_zero


-- @@ L84-93 verbatim
/-- A bridge presentation, its canonical north/south sign, and the explicit
spatial-flatness certificate as one object. -/
def flatSignedConfiguration (B : BridgeData n z) :
    FlatSignedConfiguration n (-B.y) where
  X := B.fls
  sign := B.fiberSign
  center := 0
  radius := n + 2
  radius_nonneg := by positivity
  flatOutside := B.fls_flatOutside


-- @@ L95-96 verbatim
@[simp] theorem flatSignedConfiguration_X (B : BridgeData n z) :
    B.flatSignedConfiguration.X = B.fls := rfl


-- @@ L98-99 verbatim
@[simp] theorem flatSignedConfiguration_sign (B : BridgeData n z) :
    B.flatSignedConfiguration.sign = B.fiberSign := rfl


-- @@ L101-102 verbatim
@[simp] theorem flatSignedConfiguration_center (B : BridgeData n z) :
    B.flatSignedConfiguration.center = 0 := rfl


-- @@ L104-105 verbatim
@[simp] theorem flatSignedConfiguration_radius (B : BridgeData n z) :
    B.flatSignedConfiguration.radius = n + 2 := rfl


-- @@ L107-107 verbatim
end BridgeData

-- @@ L108-108 verbatim
end Submission
