/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInverseFlowGevrey
public import LeanPool.NavierStokesAndEuler.Euler.CylinderPhysicalTensor
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder


-- @@ L14-16 verbatim
/-! Physical reconstruction preserves the small amplitude of a lifted
correction. All spatial derivatives are actual derivatives of κF e
evaluated on the phase graph and pulled through the inverse parent flow. -/


-- @@ L18-18 verbatim
@[expose] public section



-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
namespace EulerCylinderPhysicalTensor


-- @@ L25-25 verbatim
open EulerLiftedGradientSpace EulerMetricTransport EulerCylinderSobolev EulerGevrey

-- @@ L26-26 verbatim
open scoped ContDiff


-- @@ L28-36 verbatim
theorem physicalField_gevrey (P k : ℝ) (m : Vector3) (e : LiftDomain P → Vector3)
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift P e x)) (A S : ℝ)
    (hb : ∀ n x, (∑ w : Fin n → Fin 4, ‖iteratedFieldDerivative P w e x‖) ≤
      A * S ^ n * (n.factorial : ℝ) ^ 2) (n : ℕ) (x : Vector3) :
    ‖iteratedFDeriv ℝ n (physicalField P k m e) x‖ ≤
      A*majorant (frequencyFactor k m*S) 0 n := by
  exact ((physicalTensor_norm_le P k m e he n x).trans
    (mul_le_mul_of_nonneg_left (hb n _) (pow_nonneg (frequencyFactor_nonneg k m) n))).trans_eq
    (by simp only [majorant,Nat.add_zero,mul_pow]; ring)


-- @@ L38-38 verbatim
end EulerCylinderPhysicalTensor


-- @@ L40-40 verbatim
namespace EulerPacketPhysicalGevrey


-- @@ L42-44 verbatim
open Set EulerSmoothLimit EulerLiftedGradientSpace EulerMetricTransport EulerCylinderSobolev
  EulerCylinderPhysicalTensor EulerPacketInverseFlowGevrey EulerPacketPiola
  EulerOperatorGevreyCalculus EulerGevrey

-- @@ L45-45 verbatim
open scoped ContDiff


-- @@ L47-50 verbatim
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U) (P κ k : ℝ)
  (e : Icc (0 : ℝ) D.T → LiftDomain P → Space)
  (he : ∀ t x, ContDiff ℝ ∞ (localFieldLift P (e t) x))


-- @@ L52-54 verbatim
/-- Graph reconstruction, given by `κ • D.F.field t x (physicalField P k D.m₀ (e t) x)`. -/
def graphReconstruction (t : Icc (0 : ℝ) D.T) (x : Space) : Space :=
  κ • D.F.field t x (physicalField P k D.m₀ (e t) x)


-- @@ L56-59 verbatim
include he in
theorem graphReconstruction_contDiff (t : Icc (0 : ℝ) D.T) :
    ContDiff ℝ ∞ (graphReconstruction D P κ k e t) :=
  ((D.F.smooth t).clm_apply (physicalField_contDiff P k D.m₀ (e t) (he t))).const_smul κ


-- @@ L61-65 verbatim
variable (R C A S : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) (hA : 0 ≤ A) (hS : 0 ≤ S)
  (hF : ∀ n t x,
    ‖iteratedFDeriv ℝ n (D.F.field t : Space → (Space →L[ℝ] Space)) x‖ ≤ C * majorant R 0 n)
  (hb : ∀ n t x, (∑ w : Fin n → Fin 4, ‖iteratedFieldDerivative P w (e t) x‖) ≤
    A * S ^ n * (n.factorial : ℝ) ^ 2)


-- @@ L67-89 verbatim
include he hR hC hA hS hF hb in
theorem graphReconstruction_gevrey (n : ℕ) (t : Icc (0 : ℝ) D.T) (x : Space) :
    ‖iteratedFDeriv ℝ n (graphReconstruction D P κ k e t) x‖ ≤
      (|κ| *3*C*A)*majorant (R+frequencyFactor k D.m₀*S) 0 n := by
  let Rg := R+frequencyFactor k D.m₀*S
  have hRg : 0 ≤ Rg := add_nonneg hR (mul_nonneg (frequencyFactor_nonneg k D.m₀) hS)
  have hFR : ∀ n x, ‖iteratedFDeriv ℝ n (D.F.field t : Space → (Space →L[ℝ] Space)) x‖ ≤
      C*majorant Rg 0 n := fun n x => (hF n t x).trans
    (mul_le_mul_of_nonneg_left (majorant_radius_mono R Rg hR
      (le_add_of_nonneg_right (mul_nonneg (frequencyFactor_nonneg k D.m₀) hS)) 0 n) hC)
  have heR : ∀ n x, ‖iteratedFDeriv ℝ n (physicalField P k D.m₀ (e t)) x‖ ≤
      A*majorant Rg 0 n := fun n x =>
    (physicalField_gevrey P k D.m₀ (e t) (he t) A S (fun n x => hb n t x) n x).trans
      (mul_le_mul_of_nonneg_left (majorant_radius_mono (frequencyFactor k D.m₀*S) Rg
        (mul_nonneg (frequencyFactor_nonneg k D.m₀) hS) (le_add_of_nonneg_left hR) 0 n) hA)
  have hprod := clm_apply_bound (D.F.field t) (physicalField P k D.m₀ (e t))
    (D.F.smooth t) (physicalField_contDiff P k D.m₀ (e t) (he t)) Rg C A hRg hC hA 0 0 hFR heR n x
  change ‖iteratedFDeriv ℝ n (fun y => κ • (D.F.field t y (physicalField P k D.m₀ (e t) y))) x‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply'
    (((D.F.smooth t).clm_apply (physicalField_contDiff P k D.m₀ (e t) (he t))).contDiffAt.of_le
      (by simp : (n : ℕ∞ω) ≤ ∞)),norm_smul,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left hprod (abs_nonneg κ)).trans_eq (by
      simp only [Nat.zero_add]; ring)


-- @@ L91-95 verbatim
variable (X Y : Icc (0 : ℝ) D.T → Space → Space)
  (hX : ∀ t x, HasFDerivAt (X t) (D.F.field t x) x)
  (hY : ∀ t, Differentiable ℝ (Y t))
  (hXY : ∀ t x, X t (Y t x) = x)
  (hdet : ∀ t x, (operatorMatrix (D.F.field t x)).det = 1)


-- @@ L97-99 verbatim
/-- Physical reconstruction, given by `graphReconstruction D P κ k e t (Y t x)`. -/
def physicalReconstruction (t : Icc (0 : ℝ) D.T) (x : Space) : Space :=
  graphReconstruction D P κ k e t (Y t x)


-- @@ L101-103 verbatim
/-- Physical radius, given by `sourceInverseRadius C R*(9*C^2*(R+frequencyFactor k D.m₀*S)+2)`. -/
def physicalRadius : ℝ :=
  sourceInverseRadius C R*(9*C^2*(R+frequencyFactor k D.m₀*S)+2)


-- @@ L105-115 verbatim
include he hR hC hA hS hF hb hX hY hXY hdet in
theorem physicalReconstruction_gevrey (n : ℕ) (t : Icc (0 : ℝ) D.T) (x : Space) :
    ‖iteratedFDeriv ℝ n (physicalReconstruction D P κ k e Y t) x‖ ≤
      (|κ| *3*C*A)*(physicalRadius D k R C S)^n*(n.factorial : ℝ)^2 := by
  apply pullback_gevrey D X Y hX hY hXY R C hR hC hdet hF
    (graphReconstruction D P κ k e) (graphReconstruction_contDiff D P κ k e he)
    (|κ| *3*C*A) (R+frequencyFactor k D.m₀*S) (by positivity)
    (add_nonneg hR (mul_nonneg (frequencyFactor_nonneg k D.m₀) hS)) _ n t x
  intro j s y
  simpa only [majorant,Nat.add_zero,mul_assoc] using
    graphReconstruction_gevrey D P κ k e he R C A S hR hC hA hS hF hb j s y


-- @@ L117-117 verbatim
end EulerPacketPhysicalGevrey
