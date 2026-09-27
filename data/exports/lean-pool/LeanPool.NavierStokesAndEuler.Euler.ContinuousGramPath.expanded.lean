/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ContinuousPathComposition
public import LeanPool.NavierStokesAndEuler.Euler.TransverseGramPath
import LeanPool.NavierStokesAndEuler.Euler.ContinuousPathCalculus
import LeanPool.NavierStokesAndEuler.Euler.TransverseStrongEstimates
import Mathlib.Analysis.Calculus.ContDiff.Operations


-- @@ L15-22 verbatim
/-!
# Genuine inverse Gram calculus in the uniform time norm

The previously constructed continuous Gram inverse is an actual inverse in
the Banach algebra of continuous operator paths. Its external-parameter
smoothness follows from inversion at units of that algebra. No smoothness
of a pre-existing inverse is assumed.
-/


-- @@ L24-24 verbatim
@[expose] public section



-- @@ L27-27 verbatim
noncomputable section


-- @@ L29-29 verbatim
namespace EulerContinuousGramPath


-- @@ L31-33 verbatim
open Set ContinuousLinearMap EulerContinuousTimeIntegral EulerContinuousPathCalculus
  EulerContinuousPathComposition EulerTransverseGramInverse EulerTransverseGramPath
  EulerTransverseStrongEstimates  EulerGevrey

-- @@ L34-34 verbatim
open scoped ContDiff


-- @@ L36-38 verbatim
variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]


-- @@ L40-41 verbatim
variable (T : ℝ) (Q : C(Icc (0 : ℝ) T, U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t v, c * ‖v‖ ^ 2 ≤ ‖Q t v‖ ^ 2)


-- @@ L43-58 verbatim
/-- The actual Gram path and its actual continuous inverse form a unit. -/
def gramPathUnit : (C(Icc (0 : ℝ) T,U →L[ℝ] U))ˣ where
  val := gramPath T Q
  inv := gramInversePath T Q c hc hQ
  val_inv := by
    apply ContinuousMap.ext
    intro t
    apply ContinuousLinearMap.ext
    intro v
    exact gram_inverse_apply (Q t) c hc (hQ t) v
  inv_val := by
    apply ContinuousMap.ext
    intro t
    apply ContinuousLinearMap.ext
    intro v
    exact inverse_gram_apply (Q t) c hc (hQ t) v


-- @@ L60-63 verbatim
/-- The constructed path is exactly Banach-algebra inversion of the Gram coefficient. -/
theorem gramInversePath_eq_ringInverse :
    gramInversePath T Q c hc hQ = Ring.inverse (gramPath T Q) :=
  (Ring.inverse_unit (M₀ := C(Icc (0 : ℝ) T,U →L[ℝ] U)) (gramPathUnit T Q c hc hQ)).symm


-- @@ L65-67 verbatim
/-- The actual inverse acting on continuous forcing paths. -/
def solve : C(Icc (0 : ℝ) T,U) →L[ℝ] C(Icc (0 : ℝ) T,U) :=
  multiplier (gramInversePath T Q c hc hQ)


-- @@ L69-74 verbatim
/-- The continuous solution satisfies the actual coefficient equation. -/
theorem solve_equation (f : C(Icc (0 : ℝ) T, U)) :
    multiplier (gramPath T Q) (solve T Q c hc hQ f) = f := by
  apply ContinuousMap.ext
  intro t
  exact gram_inverse_apply (Q t) c hc (hQ t) (f t)


-- @@ L76-81 verbatim
/-- The constructed inverse is also a left inverse in the uniform path space. -/
theorem solve_left_inverse (f : C(Icc (0 : ℝ) T, U)) :
    solve T Q c hc hQ (multiplier (gramPath T Q) f) = f := by
  apply ContinuousMap.ext
  intro t
  exact inverse_gram_apply (Q t) c hc (hQ t) (f t)


-- @@ L83-85 verbatim
/-- The uniform-in-time inverse has the same genuine coercive bound. -/
theorem solve_norm : ‖solve T Q c hc hQ‖ ≤ c⁻¹ :=
  (multiplier_norm (gramInversePath T Q c hc hQ)).trans (gramInversePath_norm T Q c hc hQ)


-- @@ L87-87 verbatim
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]


-- @@ L89-92 verbatim
/-- The actual Gram path is smoothly parameterized in the uniform time norm. -/
theorem gramPath_contDiff (Qp : P → C(Icc (0 : ℝ) T, U →L[ℝ] E)) {n : ℕ∞ω}
    (hQp : ContDiff ℝ n Qp) : ContDiff ℝ n (fun x => gramPath T (Qp x)) :=
  contDiff_compose (fun x => adjointMap (Qp x)) Qp (contDiff_adjoint Qp hQp) hQp


-- @@ L94-106 verbatim
/-- Actual inverse-path regularity follows from the constructed Banach-algebra unit. -/
theorem gramInversePath_contDiff (Qp : P → C(Icc (0 : ℝ) T, U →L[ℝ] E))
    (hLower : ∀ x t v, c * ‖v‖ ^ 2 ≤ ‖Qp x t v‖ ^ 2) {n : ℕ∞ω}
    (hQp : ContDiff ℝ n Qp) :
    ContDiff ℝ n (fun x => gramInversePath T (Qp x) c hc (hLower x)) := by
  have heq : (fun x => gramInversePath T (Qp x) c hc (hLower x)) =
      Ring.inverse ∘ (fun x => gramPath T (Qp x)) :=
    funext (fun x => gramInversePath_eq_ringInverse T (Qp x) c hc (hLower x))
  rw [heq, contDiff_iff_contDiffAt]
  intro x
  exact (contDiffAt_ringInverse ℝ (R := C(Icc (0 : ℝ) T,U →L[ℝ] U))
    (gramPathUnit T (Qp x) c hc (hLower x))).comp x
    (gramPath_contDiff T Qp hQp).contDiffAt


-- @@ L108-114 verbatim
/-- The genuinely constructed uniform-time solution is smoothly parameterized. -/
theorem solve_contDiff (Qp : P → C(Icc (0 : ℝ) T, U →L[ℝ] E))
    (hLower : ∀ x t v, c * ‖v‖ ^ 2 ≤ ‖Qp x t v‖ ^ 2) (f : P → C(Icc (0 : ℝ) T, U))
    {n : ℕ∞ω} (hQp : ContDiff ℝ n Qp) (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun x => solve T (Qp x) c hc (hLower x) (f x)) :=
  contDiff_apply (fun x => gramInversePath T (Qp x) c hc (hLower x)) f
    (gramInversePath_contDiff T c hc Qp hLower hQp) hf


-- @@ L116-133 verbatim
/-- The actual Gram coefficient has the uniform factorial product bound. -/
theorem gramPath_bound (Qp : P → C(Icc (0 : ℝ) T, U →L[ℝ] E)) (hQp : ContDiff ℝ ∞ Qp)
    (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hb : ∀ n x, ‖iteratedFDeriv ℝ n Qp x‖ ≤ C * majorant R 0 n) (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => gramPath T (Qp y)) x‖ ≤ (3*C^2)*majorant R 0 n := by
  have h := compose_bound (fun y => adjointMap (Qp y)) Qp
    (contDiff_adjoint Qp hQp) hQp R C C hR hC hC 0 0
    (EulerContinuousPathComposition.adjoint_bound Qp hQp R C hR hC 0 hb) hb n x
  have he : 3*C*C = 3*C^2 := by ring
  have hfun : (fun y => gramPath T (Qp y)) =
      fun y => compose (adjointMap (Qp y)) (Qp y) := by
    funext y
    apply ContinuousMap.ext
    intro t
    rfl
  exact (congrArg (fun g : P → C(Icc (0 : ℝ) T,U →L[ℝ] U) =>
    ‖iteratedFDeriv ℝ n g x‖) hfun).trans_le
      (by simpa only [Nat.add_zero, he] using h)


-- @@ L135-135 verbatim
end EulerContinuousGramPath
