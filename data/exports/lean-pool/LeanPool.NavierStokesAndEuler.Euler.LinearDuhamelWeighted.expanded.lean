/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LinearDuhamelOperator
public import LeanPool.NavierStokesAndEuler.Euler.ContinuousTimeWeight


-- @@ L12-19 verbatim
/-!
# Duhamel operators in the source's time profile

The bounded Green operator in the normalized continuous-path space inherits
its constant directly from the relative homogeneous propagator bound. The
frozen-coefficient identity is exact and will be differentiated for quantitative
parameter estimates; no norm of the weighted primitive is used.
-/


-- @@ L21-21 verbatim
@[expose] public section



-- @@ L24-24 verbatim
noncomputable section



-- @@ L27-27 verbatim
namespace EulerLinearDuhamel


-- @@ L29-30 verbatim
open Set ContinuousLinearMap EulerVolterraConvolution EulerContinuousTimeIntegral
  EulerContinuousTimeWeight


-- @@ L32-32 verbatim
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

-- @@ L33-33 verbatim
variable {T : ℝ} {hT : 0 ≤ T} {B : C(Icc (0 : ℝ) T, E →L[ℝ] E)}


-- @@ L35-35 verbatim
namespace Evolution


-- @@ L37-37 verbatim
variable (U : Evolution T hT B) (g : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t)


-- @@ L39-41 verbatim
/-- The actual homogeneous data map, normalized by the profile. -/
def weightedInitial : E →L[ℝ] C(Icc (0 : ℝ) T,E) :=
  (normalize g hg).comp U.initialOperator


-- @@ L43-45 verbatim
/-- The actual Green map for forcing measured in the source profile. -/
def weightedForcing : C(Icc (0 : ℝ) T,E) →L[ℝ] C(Icc (0 : ℝ) T,E) :=
  (normalize g hg).comp (U.forcingOperator.comp (weight g))


-- @@ L47-56 verbatim
omit [CompleteSpace E] in
/-- The initial-data norm uses just the relative propagator constant. -/
theorem weightedInitial_norm (hg₀ : g ⟨0, le_rfl, hT⟩ = 1) (C : ℝ) (hC : 0 ≤ C)
    (hU : ∀ t s : Icc (0 : ℝ) T, s ≤ t → ‖U.propagator t s‖ ≤ C*g t/g s) :
    ‖U.weightedInitial g hg‖ ≤ C := by
  apply opNorm_le_bound _ hC
  intro a₀
  apply normalize_norm_le g hg (U.initialOperator a₀) (C*‖a₀‖) (mul_nonneg hC (norm_nonneg a₀))
  intro t
  exact (U.initialOperator_profile_bound a₀ g hg₀ C hU t).trans_eq (by ring)


-- @@ L58-72 verbatim
/-- The Green-operator norm is interval length times the relative propagator
constant. Neither the maximum nor minimum of the profile appears. -/
theorem weightedForcing_norm (hg₀ : g ⟨0, le_rfl, hT⟩ = 1) (C : ℝ) (hC : 0 ≤ C)
    (hU : ∀ t s : Icc (0 : ℝ) T, s ≤ t → ‖U.propagator t s‖ ≤ C*g t/g s) :
    ‖U.weightedForcing g hg‖ ≤ C*T := by
  apply opNorm_le_bound _ (mul_nonneg hC hT)
  intro f
  apply normalize_norm_le g hg (U.forcingOperator (weight g f)) (C*T*‖f‖)
    (mul_nonneg (mul_nonneg hC hT) (norm_nonneg f))
  intro t
  have hp := U.forcingOperator_profile_bound (weight g f) g hg hg₀ C ‖f‖ hC hU
    (fun s => (weight_pointwise_bound g (fun s => (hg s).le) f s).trans_eq (mul_comm _ _)) t
  have ht := mul_le_mul_of_nonneg_right t.property.2
    (mul_nonneg (mul_nonneg hC (hg t).le) (norm_nonneg f))
  nlinarith


-- @@ L74-76 verbatim
/-- The normalized constructed path, with normalized forcing as input. -/
def weightedSolution (f : C(Icc (0 : ℝ) T, E)) (a₀ : E) : C(Icc (0 : ℝ) T,E) :=
  normalize g hg (U.solution (weight g f) a₀)


-- @@ L78-83 verbatim
/-- The normalized solution is still exactly the two actual data maps. -/
theorem weightedSolution_eq (f : C(Icc (0 : ℝ) T, E)) (a₀ : E) :
    U.weightedSolution g hg f a₀ = U.weightedInitial g hg a₀ + U.weightedForcing g hg f := by
  unfold weightedSolution
  rw [U.solution_eq_operators, map_add]
  rfl


-- @@ L85-85 verbatim
variable {D : C(Icc (0 : ℝ) T, E →L[ℝ] E)} (V : Evolution T hT D)


-- @@ L87-100 verbatim
/-- Freezing the coefficient is an actual identity of constructed solutions. -/
theorem frozen_solution (f : C(Icc (0 : ℝ) T, E)) (a₀ : E) :
    V.solution f a₀ = U.initialOperator a₀ +
      U.forcingOperator (f + multiplier (D-B) (V.solution f a₀)) := by
  rw [← U.solution_eq_operators]
  ext t
  apply U.solution_unique _ a₀ (V.solutionReal f a₀) _ (V.solution_initial f a₀) t
  intro s
  have hd := V.solution_derivative f a₀ s
  convert hd using 1
  change B s (V.solution f a₀ s) +
    (f s + (D s-B s) (V.solution f a₀ s)) = D s (V.solution f a₀ s) + f s
  rw [sub_apply]
  abel


-- @@ L102-117 verbatim
/-- The exact frozen identity in the fixed profile-normalized path space. -/
theorem weighted_frozen_solution (f : C(Icc (0 : ℝ) T, E)) (a₀ : E) :
    V.weightedSolution g hg f a₀ = U.weightedInitial g hg a₀ +
      U.weightedForcing g hg (f + multiplier (D-B) (V.weightedSolution g hg f a₀)) := by
  have he := U.frozen_solution V (weight g f) a₀
  have hw : weight g (f + multiplier (D-B) (V.weightedSolution g hg f a₀)) =
      weight g f + multiplier (D-B) (V.solution (weight g f) a₀) := by
    rw [map_add, weight_multiplier]
    change _ + multiplier (D-B) (weight g (normalize g hg (V.solution (weight g f) a₀))) = _
    rw [weight_normalize]
  change normalize g hg (V.solution (weight g f) a₀) =
    normalize g hg (U.initialOperator a₀) +
      normalize g hg (U.forcingOperator (weight g (f + multiplier (D-B) (V.weightedSolution g hg f
          a₀))))
  rw [hw]
  simpa only [map_add] using congrArg (normalize g hg) he


-- @@ L119-119 verbatim
end Evolution


-- @@ L121-121 verbatim
end EulerLinearDuhamel
