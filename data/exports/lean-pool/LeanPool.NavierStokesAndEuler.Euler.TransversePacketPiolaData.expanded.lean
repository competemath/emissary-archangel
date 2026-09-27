/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketData
public import LeanPool.NavierStokesAndEuler.Euler.PacketPeriodicPotential


-- @@ L11-12 verbatim
/-! The given inverse deformation defines the exact equivalences used by the Piola packet
construction. -/


-- @@ L14-14 verbatim
section


-- @@ L16-16 verbatim
/-! The actual high/corrector pair, with all potential regularity derived from the high field. -/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-22 verbatim
namespace EulerPacketConstructedPiola


-- @@ L24-26 verbatim
open EulerSmoothLimit EulerPacketPiola EulerPacketPeriodicPotential EulerPacketCrossProduct
  EulerLiftedGradientSpace EulerMetricTransport EulerTransportDerivatives
  Set MeasureTheory InnerProductSpace

-- @@ L27-27 verbatim
open scoped ContDiff


-- @@ L29-31 verbatim
/-- Normal, given by `(F y).symm.toContinuousLinearMap.adjoint m₀`. -/
def normal (F : Space → Space ≃L[ℝ] Space) (m₀ : Space) (y : Space) : Space :=
  (F y).symm.toContinuousLinearMap.adjoint m₀


-- @@ L33-41 verbatim
theorem normal_ne_zero (F : Space → Space ≃L[ℝ] Space) (m₀ : Space) (hm₀ : m₀ ≠ 0)
    (y : Space) : normal F m₀ y ≠ 0 := by
  intro hz
  have he := congrArg (fun v : Space => ⟪v,F y m₀⟫_ℝ) hz
  change ⟪(F y).symm.toContinuousLinearMap.adjoint m₀,F y m₀⟫_ℝ = ⟪0,F y m₀⟫_ℝ at he
  rw [ContinuousLinearMap.adjoint_inner_left] at he
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply,
      inner_zero_left] at he
  exact hm₀ (inner_self_eq_zero.mp he)


-- @@ L43-43 verbatim
variable (P : ℝ) [Fact (0 < P)]


-- @@ L45-47 verbatim
/-- Corrector, given by `liftedSlowCurl P F (field P (normal F m₀) A)`. -/
def corrector (F : Space → Space ≃L[ℝ] Space) (m₀ : Space) (A : LiftDomain P → Space) :
    LiftDomain P → Space := liftedSlowCurl P F (field P (normal F m₀) A)


-- @@ L49-54 verbatim
variable (κ : ℝ) (m₀ : Space) (Ξ : Space → Space) (A : LiftDomain P → Space)
  (hΞ : ContDiff ℝ ∞ Ξ) (hAc : HasCompactSupport A)
  (F : Space → Space ≃L[ℝ] Space)
  (hN : ContDiff ℝ ∞ (normal F m₀)) (hm₀ : m₀ ≠ 0)
  (hA : ∀ x, ContDiff ℝ ∞ (localFieldLift P A x))
  (hmean : ∀ y, (∫ θ in (0 : ℝ)..P, A (y, (θ : AddCircle P))) = 0)


-- @@ L56-60 verbatim
/-- Pair Lᵖ, constructed using `piolaPairLp`. -/
def pairLp (p : ℕ) : LiftL2 P :=
  piolaPairLp P κ m₀ Ξ (field P (normal F m₀) A) hΞ
    (field_compact P (normal F m₀) A hAc)
    (field_smooth P (normal F m₀) A hN (normal_ne_zero F m₀ hm₀) hA hmean) p


-- @@ L62-66 verbatim
theorem pairLp_mem (p : ℕ) :
    pairLp P κ m₀ Ξ A hΞ hAc F hN hm₀ hA hmean p ∈ divergenceFreeSpace P κ m₀ :=
  piolaPairLp_mem P κ m₀ Ξ (field P (normal F m₀) A) hΞ
    (field_compact P (normal F m₀) A hAc)
    (field_smooth P (normal F m₀) A hN (normal_ne_zero F m₀ hm₀) hA hmean) p


-- @@ L68-79 verbatim
/-- The entire pair is the literal source formula, as an actual divergence-free L² field. -/
theorem pairLp_ae
    (hF : ∀ y, fderiv ℝ Ξ y = (F y).toContinuousLinearMap)
    (hdet : ∀ y, (operatorMatrix (F y).toContinuousLinearMap).det = 1)
    (htan : ∀ x, ⟪normal F m₀ x.1, A x⟫_ℝ = 0) (p : ℕ) :
    (pairLp P κ m₀ Ξ A hΞ hAc F hN hm₀ hA hmean p : LiftDomain P → Space) =ᵐ[liftMeasure P]
      fun x => (F x.1).symm (κ^p • A x+κ^(p+1) • corrector P F m₀ A x) :=
  piolaPairLp_ae P κ m₀ Ξ A (field P (normal F m₀) A) hΞ
    (field_compact P (normal F m₀) A hAc)
    (field_smooth P (normal F m₀) A hN (normal_ne_zero F m₀ hm₀) hA hmean)
    F hF hdet (normal_ne_zero F m₀ hm₀) htan
    (field_angle_derivative P (normal F m₀) A hN (normal_ne_zero F m₀ hm₀) hA hmean) p


-- @@ L81-81 verbatim
end EulerPacketConstructedPiola


-- @@ L83-83 verbatim
end

-- @@ L84-84 verbatim
end


-- @@ L86-86 verbatim
end


-- @@ L88-88 verbatim
@[expose] public section


-- @@ L90-90 verbatim
noncomputable section


-- @@ L92-92 verbatim
namespace EulerTransversePacketProvider.Data


-- @@ L94-95 verbatim
open Set EulerSmoothLimit
  EulerLiftedGradientSpace EulerPacketConstructedPiola


-- @@ L97-98 verbatim
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : Data U)


-- @@ L100-104 verbatim
/-- Deformation equiv, given by `ContinuousLinearEquiv.equivOfInverse (D.F.field t x)
(D.FInv.field t x) (D.inverse_left t x) (D.inverse_right t x)`. -/
def deformationEquiv (t : Icc (0 : ℝ) D.T) (x : Space) : Space ≃L[ℝ] Space :=
  ContinuousLinearEquiv.equivOfInverse (D.F.field t x) (D.FInv.field t x)
    (D.inverse_left t x) (D.inverse_right t x)


-- @@ L106-107 verbatim
@[simp] theorem deformationEquiv_coe (t : Icc (0 : ℝ) D.T) (x : Space) :
    (D.deformationEquiv t x).toContinuousLinearMap = D.F.field t x := rfl


-- @@ L109-110 verbatim
@[simp] theorem deformationEquiv_symm_coe (t : Icc (0 : ℝ) D.T) (x : Space) :
    (D.deformationEquiv t x).symm.toContinuousLinearMap = D.FInv.field t x := rfl


-- @@ L112-113 verbatim
@[simp] theorem deformationEquiv_normal (t : Icc (0 : ℝ) D.T) :
    EulerPacketConstructedPiola.normal (D.deformationEquiv t) D.m₀ = D.normal.field t := rfl


-- @@ L115-119 verbatim
theorem initialNormal_ne_zero : D.m₀ ≠ 0 := by
  intro h
  have hn := D.m₀_unit
  rw [h,norm_zero] at hn
  exact zero_ne_one hn


-- @@ L121-121 verbatim
end EulerTransversePacketProvider.Data
