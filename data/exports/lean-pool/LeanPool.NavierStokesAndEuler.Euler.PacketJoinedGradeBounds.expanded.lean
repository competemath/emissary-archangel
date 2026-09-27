/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldWeight
public import LeanPool.NavierStokesAndEuler.Euler.PacketShiftArithmetic
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderProfileChange
import LeanPool.NavierStokesAndEuler.Euler.PacketLinearCostAbsorption
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketParity
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketNormalBudget
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJoinedCorrector
import LeanPool.NavierStokesAndEuler.Euler.PacketMajorantShift
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJoinedPressure
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketBudget
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJoinedPaths
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketHomogeneity
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketHistory
import LeanPool.NavierStokesAndEuler.Euler.ElapsedTimePathWeight
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevScaling
import LeanPool.NavierStokesAndEuler.Euler.CylinderSlowCurlWeight
import LeanPool.NavierStokesAndEuler.Euler.CylinderPotentialWeight
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketForwardBounds
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketHistoryBounds


-- @@ L28-30 verbatim
/-! A single source budget closes every forced transverse grade.  The actual
profile is retained, its positive scalar factor cancels exactly, and one
spare derivative shift pays the fixed operator constants. -/


-- @@ L32-32 verbatim
section


-- @@ L34-41 verbatim
/-!
# The complete quantitative forced transverse provider

Source-only budgets fixed before the forcing give actual A, A_t, π, dπ,
Q, Q_t, C and C_t bounds linear in its amplitude. All eight outputs use the
same external radius and fixed mixed Sobolev order. They spend at most four
derivative shifts, within the manuscript's ten-shift allowance.
-/


-- @@ L43-43 verbatim
section


-- @@ L45-51 verbatim
/-!
# Unit-amplitude bounds for the complete actual transverse inverse

One source-only budget controls the history trace, forward solve and their
joined physical velocity and genuine time derivative. The input and output
use the same fixed mixed-word Sobolev order and the same external radius.
-/


-- @@ L53-53 verbatim
@[expose] public section


-- @@ L55-55 verbatim
noncomputable section


-- @@ L57-57 verbatim
namespace EulerTransversePacketJoin.Budget


-- @@ L59-63 verbatim
open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerTransversePacketProvider
  EulerLiftedGradientSpace EulerGevrey EulerParameterWordGevrey EulerFixedEvolutionSobolev
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerContinuousTimeWeight
      EulerTimeIntervalRestriction
  EulerElapsedTimePathGluing EulerPacketProfileRecursion

-- @@ L64-64 verbatim
open scoped ContDiff BoundedContinuousFunction


-- @@ L66-74 verbatim
variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T}
  {B : HistoryData (D.initial τ hτ hτT.le)} {ι : Type*} [Fintype ι] {q : ℕ}
  (L : Budget D τ hτ hτT B ι q) {raw : VectorField} (G : Forcing P D raw)
  (directions : ι → LiftTangent) (hdir : ∀ i, ‖directions i‖ ≤ 1)
  (d : ℕ)
  (hforce : ∀ n, block directions q (fun a => pathTranslate P a
    (normalize L.fullProfile L.fullProfile_pos (HistoryData.forcingPath G))) n 0 ≤ majorant L.R d n)


-- @@ L76-76 verbatim
include hforce


-- @@ L78-89 verbatim
theorem history_forcing_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a
      (HistoryData.forcingPath (G.initial τ hτ hτT.le))) n 0 ≤ majorant L.R d n := by
  have he : (normalize L.fullProfile L.fullProfile_pos (HistoryData.forcingPath G)).comp
      (initialInclusion D.T τ hτT.le) = HistoryData.forcingPath (G.initial τ hτ hτT.le) :=
    normalize_initial D.T τ hτ.le hτT.le L.g L.initial_one L.positive (HistoryData.forcingPath G)
  have hb := timeComp_block_le P directions q
    (normalize L.fullProfile L.fullProfile_pos (HistoryData.forcingPath G))
    (normalize_orbit_contDiff P L.fullProfile L.fullProfile_pos _ G.path_orbit)
    (initialInclusion D.T τ hτT.le) n 0
  rw [he] at hb
  exact hb.trans (hforce n)


-- @@ L91-104 verbatim
theorem forward_forcing_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a
      (normalize L.g L.positive (HistoryData.forcingPath (G.tail τ hτ.le hτT)))) n 0 ≤ majorant L.R
          d n := by
  have he : (normalize L.fullProfile L.fullProfile_pos (HistoryData.forcingPath G)).comp
      (tailInclusion D.T τ hτ.le) =
        normalize L.g L.positive (HistoryData.forcingPath (G.tail τ hτ.le hτT)) :=
    normalize_tail D.T τ hτ.le hτT.le L.g L.initial_one L.positive (HistoryData.forcingPath G)
  have hb := timeComp_block_le P directions q
    (normalize L.fullProfile L.fullProfile_pos (HistoryData.forcingPath G))
    (normalize_orbit_contDiff P L.fullProfile L.fullProfile_pos _ G.path_orbit)
    (tailInclusion D.T τ hτ.le) n 0
  rw [he] at hb
  exact hb.trans (hforce n)


-- @@ L106-106 verbatim
include hdir


-- @@ L108-118 verbatim
/-- This is the actual datum passed to the forward solution, not a new hypothesis. -/
theorem terminal_bound (n : ℕ) :
    block directions q (fun a => translate P a
      ((forwardInitial τ hτ hτT B G).value : CylinderL2 P U)) n 0 ≤
        traceCost τ*majorant L.R (d+2) n := by
  exact B.source_terminal_bound (G.initial τ hτ hτT.le) directions hdir q
    L.Rc L.C₀ L.C₁ L.CH 1 L.R L.Rc_nonneg L.C₀_nonneg L.C₁_nonneg L.CH_nonneg zero_le_one
    (fun j t x => L.frame_bound j (initialInclusion D.T τ hτT.le t) x)
    (fun j t x => L.frameDerivative_bound j (initialInclusion D.T τ hτT.le t) x)
    L.hessian_bound L.history_weak L.history_strong L.history_length d
    (fun j => by simpa only [one_mul] using L.history_forcing_bound G directions d hforce j) n


-- @@ L120-128 verbatim
theorem past_velocity_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a (pastVelocity τ hτ hτT B G)) n 0 ≤
      (3*sobolevCoefficientAmplitude ι q L.Rc L.C₀*traceCost τ)*majorant L.R (d+2) n := by
  exact B.source_velocity_bound (G.initial τ hτ hτT.le) directions hdir q
    L.Rc L.C₀ L.C₁ L.CH 1 L.R L.Rc_nonneg L.C₀_nonneg L.C₁_nonneg L.CH_nonneg zero_le_one
    (fun j t x => L.frame_bound j (initialInclusion D.T τ hτT.le t) x)
    (fun j t x => L.frameDerivative_bound j (initialInclusion D.T τ hτT.le t) x)
    L.hessian_bound L.history_weak L.history_strong L.history_length d
    (fun j => by simpa only [one_mul] using L.history_forcing_bound G directions d hforce j) n


-- @@ L130-140 verbatim
theorem past_derivative_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a (pastDerivative τ hτ hτT B G)) n 0 ≤
      (3*sobolevCoefficientAmplitude ι q L.Rc L.C₁*traceCost τ +
        3*sobolevCoefficientAmplitude ι q L.Rc L.C₀)*majorant L.R (d+3) n := by
  exact B.source_derivative_bound (G.initial τ hτ hτT.le) directions hdir q
    L.Rc L.C₀ L.C₁ L.CH 1 L.R L.Rc_nonneg L.C₀_nonneg L.C₁_nonneg L.CH_nonneg zero_le_one
    (fun j t x => L.frame_bound j (initialInclusion D.T τ hτT.le t) x)
    (fun j t x => L.frameDerivative_bound j (initialInclusion D.T τ hτT.le t) x)
    L.hessian_bound L.history_weak L.history_strong L.history_length d
    (fun j => by simpa only [one_mul] using L.history_forcing_bound G directions d hforce j)
    L.history_uniform n


-- @@ L142-163 verbatim
theorem future_velocity_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a
      (normalize L.g L.positive (futureVelocity τ hτ hτT B G))) n 0 ≤
        (3*sobolevCoefficientAmplitude ι q L.Rc L.C₀)*majorant L.R (d+3) n := by
  have hf (j : ℕ) : block directions q (fun a => pathTranslate P a
      (normalize L.g L.positive (HistoryData.forcingPath (G.tail τ hτ.le hτT)))) j 0 ≤
        1*majorant L.R (d+2) j := by
    simpa only [one_mul] using (L.forward_forcing_bound G directions d hforce j).trans
      (majorant_mono_shift L.R L.radius_bounds.1 d (d+2) j (by omega))
  dsimp only [futureVelocity]
  rw [show d+3=d+2+1 by omega]
  exact
    (G.tail τ hτ.le hτT).source_velocity_normalized_bound (forwardInitial τ hτ hτT B G)
      L.g L.positive directions hdir q L.neighborhood L.neighborhood_measurable L.neighborhood_open
      L.support_subset L.neighborhood_halfball L.initial_one
      L.C (traceCost τ) 1 L.Rc L.C₀ L.C₁ L.Ri L.R
      L.C_nonneg (traceCost_nonneg τ hτ.le) zero_le_one L.Rc_nonneg L.C₀_nonneg L.C₁_nonneg
      L.forward_inverse
      (fun j t x => L.frame_bound j (tailInclusion D.T τ hτ.le t) x)
      (fun j t x => L.frameDerivative_bound j (tailInclusion D.T τ hτ.le t) x)
      L.forcing_radius L.forward_radius L.propagator (d+2) hf
      (L.terminal_bound G directions hdir d hforce) L.radius_bounds.2 n


-- @@ L165-186 verbatim
theorem future_derivative_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a
      (normalize L.g L.positive (futureDerivative τ hτ hτT B G))) n 0 ≤
        EulerSourceCylinderTimeBounds.physicalCost ι q L.Ri L.C₀ L.C₁ 1 1*majorant L.R (d+3) n := by
  have hf (j : ℕ) : block directions q (fun a => pathTranslate P a
      (normalize L.g L.positive (HistoryData.forcingPath (G.tail τ hτ.le hτT)))) j 0 ≤
        1*majorant L.R (d+2) j := by
    simpa only [one_mul] using (L.forward_forcing_bound G directions d hforce j).trans
      (majorant_mono_shift L.R L.radius_bounds.1 d (d+2) j (by omega))
  dsimp only [futureDerivative]
  rw [show d+3=d+2+1 by omega]
  exact
    (G.tail τ hτ.le hτT).source_derivative_normalized_bound (forwardInitial τ hτ hτT B G)
      L.g L.positive directions hdir q L.neighborhood L.neighborhood_measurable L.neighborhood_open
      L.support_subset L.neighborhood_halfball L.initial_one
      L.C (traceCost τ) 1 L.Rc L.C₀ L.C₁ L.Ri L.R
      L.C_nonneg (traceCost_nonneg τ hτ.le) zero_le_one L.Rc_nonneg L.C₀_nonneg L.C₁_nonneg
      L.forward_inverse
      (fun j t x => L.frame_bound j (tailInclusion D.T τ hτ.le t) x)
      (fun j t x => L.frameDerivative_bound j (tailInclusion D.T τ hτ.le t) x)
      L.forcing_radius L.forward_radius L.propagator (d+2) hf
      (L.terminal_bound G directions hdir d hforce) L.radius_bounds.1 n


-- @@ L188-204 verbatim
/-- The entire constructed A/g, with the input's original external radius. -/
theorem velocity_unit_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (velocityPath τ hτ hτT B G))) n 0 ≤
        L.velocityCost*majorant L.R (d+3) n := by
  have hb := normalized_join_block P D.T τ hτ.le hτT.le L.g L.positive L.initial_one
    (pastVelocity τ hτ hτT B G) (futureVelocity τ hτ hτT B G) (velocity_match τ hτ hτT B G)
    (pastVelocity_orbit τ hτ hτT B G) (futureVelocity_orbit τ hτ hτT B G) directions q n 0
  have ha : 0 ≤ 3*sobolevCoefficientAmplitude ι q L.Rc L.C₀*traceCost τ :=
    mul_nonneg (mul_nonneg (by norm_num) (sobolevCoefficientAmplitude_nonneg q L.Rc L.C₀
      L.Rc_nonneg L.C₀_nonneg)) (traceCost_nonneg τ hτ.le)
  have hp := (L.past_velocity_bound G directions hdir d hforce n).trans
    (mul_le_mul_of_nonneg_left
      (majorant_mono_shift L.R L.radius_bounds.1 (d+2) (d+3) n (by omega)) ha)
  exact hb.trans (by
    simpa only [velocityCost,add_mul] using
      add_le_add hp (L.future_velocity_bound G directions hdir d hforce n))


-- @@ L206-217 verbatim
/-- The entire actual A_t/g. The profile itself is never differentiated. -/
theorem derivative_unit_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (derivativePath τ hτ hτT B G))) n 0 ≤
        L.derivativeCost*majorant L.R (d+3) n := by
  have hb := normalized_join_block P D.T τ hτ.le hτT.le L.g L.positive L.initial_one
    (pastDerivative τ hτ hτT B G) (futureDerivative τ hτ hτT B G) (derivative_match τ hτ hτT B G)
    (pastDerivative_orbit τ hτ hτT B G) (futureDerivative_orbit τ hτ hτT B G) directions q n 0
  exact hb.trans (by
    simpa only [derivativeCost,add_mul] using
      add_le_add (L.past_derivative_bound G directions hdir d hforce n)
        (L.future_derivative_bound G directions hdir d hforce n))


-- @@ L219-219 verbatim
end EulerTransversePacketJoin.Budget


-- @@ L221-221 verbatim
end

-- @@ L222-222 verbatim
end


-- @@ L224-224 verbatim
end


-- @@ L226-226 verbatim
section


-- @@ L228-228 verbatim
/-! Same-radius estimates for the actual corrector, divided by the prescribed time profile. -/


-- @@ L230-230 verbatim
@[expose] public section


-- @@ L232-232 verbatim
noncomputable section


-- @@ L234-234 verbatim
namespace EulerTransversePacketJoin


-- @@ L236-239 verbatim
open Set EulerTransversePacketProvider EulerSmoothLimit EulerLiftedGradientSpace
    EulerMeanCoefficients EulerGevrey
  EulerPacketProfileRecursion EulerCylinderSobolev EulerParameterWordGevrey
  EulerCylinderSmoothOrbit EulerLpCylinderTranslation EulerContinuousTimeWeight

-- @@ L240-240 verbatim
open scoped ContDiff


-- @@ L242-243 verbatim
private theorem direction_norm_bound (i : Fin 4) : ‖standardDirection i‖ ≤ 1 := by
  cases i using Fin.cases <;> simp [Prod.norm_def]


-- @@ L245-265 verbatim
variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) {raw : VectorField} (G : Forcing P D raw)
  (g : C(Icc (0 : ℝ) D.T, ℝ)) (hg : ∀ t, 0 < g t)
  (q : ℕ) (Rc C R A : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (hA : 0 ≤ A)
  (hR : sobolevCoefficientRadius (Fin 4) Rc ≤ R) (d : ℕ)
  (hbA : ∀ n, block standardDirection q
    (fun a : LiftTangent => pathTranslate P a (normalize g hg (velocityPath τ hτ hτT B G))) n 0 ≤
      A * majorant R d n)
  (hbAt : ∀ n, block standardDirection q
    (fun a : LiftTangent => pathTranslate P a (normalize g hg (derivativePath τ hτ hτT B G))) n 0 ≤
      A * majorant R d n)
  (hbK : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.potentialCoefficientPath) a‖ ≤
    C * majorant Rc 0 n)
  (hbKt : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.potentialDerivative) a‖ ≤
    C * majorant Rc 0 n)
  (hbI : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.FInv.field) a‖ ≤ C * majorant Rc 0
      n)
  (hbIt : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.inverseDerivative) a‖ ≤
    C * majorant Rc 0 n)


-- @@ L267-276 verbatim
include hRc hC hA hR hbA hbK in
theorem potentialPath_normalized_bound (n : ℕ) :
    block standardDirection q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg (potentialPath τ hτ hτT B G))) n 0 ≤
      (3*sobolevCoefficientAmplitude (Fin 4) q Rc C*(P*A))*majorant R d n :=
  EulerCylinderPotential.normalized_potentialPath_block_bound P g (velocityPath τ hτ hτT B G)
    D.potentialCoefficientPath hg D.potentialCoefficientPath_orbit
    (EulerCylinderPotential.weighted_orbit P (reciprocal g hg) (velocityPath τ hτ hτT B G)
        (velocityPath_orbit τ hτ hτT B G))
    standardDirection direction_norm_bound q Rc C R A hRc hC hA hR hbK d hbA n


-- @@ L278-289 verbatim
include hRc hC hA hR hbA hbAt hbK hbKt in
theorem potentialTimePath_normalized_bound (n : ℕ) :
    block standardDirection q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg (potentialTimePath τ hτ hτT B G)))
          n 0 ≤
      (6*sobolevCoefficientAmplitude (Fin 4) q Rc C*(P*A))*majorant R d n :=
  EulerCylinderPotential.normalized_potentialDerivative_block_bound P D.T
    D.potentialCoefficientPath D.potentialDerivative D.potentialCoefficientPath_orbit
        D.potentialDerivative_orbit
    (velocityPath τ hτ hτT B G) (derivativePath τ hτ hτT B G) (velocityPath_orbit τ hτ hτT B G)
        (derivativePath_orbit τ hτ hτT B G)
    g hg standardDirection direction_norm_bound q Rc C R A hRc hC hA hR hbK hbKt d hbA hbAt n


-- @@ L291-302 verbatim
include hRc hC hA hR hbA hbK hbI in
theorem correctorPath_normalized_bound (n : ℕ) :
    block standardDirection q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg (correctorPath τ hτ hτT B G))) n 0 ≤
      (27*(sobolevCoefficientAmplitude (Fin 4) q Rc C)^2*(P*A))*majorant R (d+1) n := by
  have hp : 0 ≤ P := (Fact.out : 0 < P).le
  have ha := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) q Rc C hRc hC
  have h := EulerCylinderSlowCurl.normalized_path_block_bound P g D.FInv.field
    (potentialPath τ hτ hτT B G) (potentialPath_orbit τ hτ hτT B G) hg D.FInv.translation_contDiff
    q Rc C R (3*sobolevCoefficientAmplitude (Fin 4) q Rc C*(P*A)) hRc hC (by positivity) hR hbI d
    (potentialPath_normalized_bound τ hτ hτT B G g hg q Rc C R A hRc hC hA hR d hbA hbK) n
  exact h.trans_eq (by ring)


-- @@ L304-329 verbatim
include hRc hC hA hR hbA hbAt hbK hbKt hbI hbIt in
theorem correctorTimePath_normalized_bound (n : ℕ) :
    block standardDirection q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg (correctorTimePath τ hτ hτT B G)))
          n 0 ≤
      (108*(sobolevCoefficientAmplitude (Fin 4) q Rc C)^2*(P*A))*majorant R (d+1) n := by
  have hp : 0 ≤ P := (Fact.out : 0 < P).le
  have ha := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) q Rc C hRc hC
  have hRn : 0 ≤ R := (sobolevCoefficientRadius_nonneg (ι := Fin 4) Rc hRc).trans hR
  have hQ (j : ℕ) : block standardDirection q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg (potentialPath τ hτ hτT B G))) j 0 ≤
        (6*sobolevCoefficientAmplitude (Fin 4) q Rc C*(P*A))*majorant R d j := by
    apply (potentialPath_normalized_bound τ hτ hτT B G g hg q Rc C R A hRc hC hA hR d hbA hbK
        j).trans
    have hn := mul_nonneg
      (show 0 ≤ sobolevCoefficientAmplitude (Fin 4) q Rc C*(P*A) by positivity)
      (majorant_nonneg R hRn d j)
    nlinarith
  have h := EulerCylinderSlowCurl.normalized_derivative_block_bound P D.T g hg
    D.FInv.field D.inverseDerivative (potentialPath τ hτ hτT B G) (potentialTimePath τ hτ hτT B G)
    (potentialPath_orbit τ hτ hτT B G) (potentialTimePath_orbit τ hτ hτT B G)
        D.FInv.translation_contDiff D.inverseDerivative_orbit
    q Rc C R (6*sobolevCoefficientAmplitude (Fin 4) q Rc C*(P*A)) hRc hC (by positivity) hR
    hbI hbIt d hQ (potentialTimePath_normalized_bound τ hτ hτT B G g hg q Rc C R A hRc hC hA hR d
        hbA hbAt hbK hbKt) n
  exact h.trans_eq (by ring)


-- @@ L331-331 verbatim
end EulerTransversePacketJoin


-- @@ L333-333 verbatim
end

-- @@ L334-334 verbatim
end


-- @@ L336-336 verbatim
end


-- @@ L338-338 verbatim
section


-- @@ L340-340 verbatim
/-! Restoring arbitrary forcing amplitudes by actual scalar homogeneity. -/


-- @@ L342-342 verbatim
@[expose] public section


-- @@ L344-344 verbatim
noncomputable section


-- @@ L346-346 verbatim
namespace EulerTransversePacketProvider


-- @@ L348-350 verbatim
open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace EulerLpCylinderTranslation
  EulerLpCylinderPaths EulerPacketProfileRecursion EulerContinuousTimeWeight
  EulerParameterWordGevrey EulerGevrey

-- @@ L351-351 verbatim
open scoped ContDiff


-- @@ L353-355 verbatim
variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  {D : Data U} {ι : Type*} [Fintype ι]


-- @@ L357-427 verbatim
/-- A genuine homogeneous operator's unit-amplitude bound extends to every
nonnegative amplitude without changing its radius or its derivative shifts. -/
theorem amplitude_bound
    (S : ∀ {r : VectorField}, Forcing P D r → C(Icc (0 : ℝ) D.T, LiftL2 P))
    (hs : ∀ {r} (G : Forcing P D r), ContDiff ℝ ∞ (fun a => pathTranslate P a (S G)))
    (hm : ∀ {r r'} (G : Forcing P D r) (H : Forcing P D r') (a : ℝ),
      H.path = a • G.path → S H = a • S G)
    (g : C(Icc (0 : ℝ) D.T, ℝ)) (hg : ∀ t, 0 < g t)
    (directions : ι → LiftTangent) (q : ℕ) (R C : ℝ) (d e : ℕ)
    (hunit : ∀ {r} (G : Forcing P D r),
      (∀ n, block directions q (fun a => pathTranslate P a
        (normalize g hg (HistoryData.forcingPath G))) n 0 ≤ majorant R d n) →
      ∀ n, block directions q (fun a => pathTranslate P a (normalize g hg (S G))) n 0 ≤ C * majorant
          R e n)
    {r : VectorField} (G : Forcing P D r) (A : ℝ) (hA : 0 ≤ A)
    (hb : ∀ n, block directions q (fun a => pathTranslate P a
      (normalize g hg (HistoryData.forcingPath G))) n 0 ≤ A * majorant R d n)
    (n : ℕ) :
    block directions q (fun a => pathTranslate P a (normalize g hg (S G))) n 0 ≤
      (C*A)*majorant R e n := by
  by_cases hz : A = 0
  · have hf := value_zero_of_block_zero_bound directions q
      (fun a => pathTranslate P a (normalize g hg (HistoryData.forcingPath G))) 0
      (by simpa only [hz,zero_mul] using hb 0)
    have ht : pathTranslate P 0 (normalize g hg (HistoryData.forcingPath G)) =
        normalize g hg (HistoryData.forcingPath G) := by
      apply ContinuousMap.ext
      intro t
      exact translate_zero P _
    rw [ht] at hf
    have hfull : HistoryData.forcingPath G = 0 := by
      have he := congrArg (weight g) hf
      rw [weight_normalize,map_zero] at he
      exact he
    have hp : G.path = 0 := by
      have he := congrArg (projectPath P D.support D.support_measurable) hfull
      rw [project_include,map_zero] at he
      exact he
    have hS : S G = 0 := by
      have he := hm G G 0 (hp.trans (zero_smul ℝ G.path).symm)
      simpa only [zero_smul] using he
    simp only [hS,map_zero,block_zero_function,hz,mul_zero,zero_mul,le_refl]
  · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hz)
    let H := G.smul A⁻¹
    let normalizedTranslation (a : LiftTangent) :
        C(Icc (0 : ℝ) D.T, LiftL2 P) →L[ℝ] C(Icc (0 : ℝ) D.T, LiftL2 P) :=
      (pathTranslate P a).comp (normalize g hg)
    have hinput : HistoryData.forcingPath H = A⁻¹ • HistoryData.forcingPath G := by
      change includePath P D.support D.support_measurable (A⁻¹ • G.path) = _
      rw [map_smul]
    have hH (j : ℕ) : block directions q (fun a => pathTranslate P a
        (normalize g hg (HistoryData.forcingPath H))) j 0 ≤ majorant R d j := by
      have he : (fun a => pathTranslate P a (normalize g hg (HistoryData.forcingPath H))) =
          fun a => A⁻¹ • pathTranslate P a (normalize g hg (HistoryData.forcingPath G)) := by
        funext a
        exact (congrArg (normalizedTranslation a) hinput).trans
          (map_smul (normalizedTranslation a) A⁻¹ _)
      rw [he]
      simpa only [one_mul] using block_normalize_bound directions q
        (fun a => pathTranslate P a (normalize g hg (HistoryData.forcingPath G)))
        (normalize_orbit_contDiff P g hg _ G.path_orbit) A hApos R 1 d j 0
        (by simpa only [one_mul] using hb j)
    have hrestore : S G = A • S H := by
      rw [hm G H A⁻¹ rfl,smul_smul,mul_inv_cancel₀ hz,one_smul]
    have hresult := block_restore_bound directions q
      (fun a => pathTranslate P a (normalize g hg (S H)))
      (fun a => pathTranslate P a (normalize g hg (S G)))
      (normalize_orbit_contDiff P g hg (S H) (hs H)) A hA
      (fun a => (congrArg (normalizedTranslation a) hrestore).trans
        (map_smul (normalizedTranslation a) A (S H))) R C e n 0 (hunit H hH n)
    exact hresult.trans_eq (by ring)


-- @@ L429-429 verbatim
end EulerTransversePacketProvider


-- @@ L431-431 verbatim
end

-- @@ L432-432 verbatim
end


-- @@ L434-434 verbatim
end


-- @@ L436-436 verbatim
section


-- @@ L438-441 verbatim
/-!
The actual complete transverse inverse has one source-only radius budget.
Its bounds are linear in the forcing amplitude and independent of grade.
-/


-- @@ L443-443 verbatim
@[expose] public section


-- @@ L445-445 verbatim
noncomputable section


-- @@ L447-447 verbatim
namespace EulerTransversePacketJoin.Budget


-- @@ L449-451 verbatim
open Set ContinuousLinearMap EulerSmoothLimit EulerTransversePacketProvider
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerPacketProfileRecursion
  EulerParameterWordGevrey EulerGevrey EulerContinuousTimeWeight

-- @@ L452-452 verbatim
open scoped ContDiff


-- @@ L454-464 verbatim
variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T}
  {B : HistoryData (D.initial τ hτ hτT.le)} {ι : Type*} [Fintype ι] {q : ℕ}
  (L : Budget D τ hτ hτT B ι q) {raw : VectorField} (G : Forcing P D raw)
  (directions : ι → LiftTangent) (hdir : ∀ i, ‖directions i‖ ≤ 1)
  (A : ℝ) (hA : 0 ≤ A) (d : ℕ)
  (hforce : ∀ n, block directions q (fun a => pathTranslate P a
    (normalize L.fullProfile L.fullProfile_pos (HistoryData.forcingPath G))) n 0 ≤ A * majorant L.R
        d
        n)


-- @@ L466-466 verbatim
include hdir hA hforce


-- @@ L468-477 verbatim
/-- The genuine joined velocity divided by its actual piecewise profile. -/
theorem velocity_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (velocityPath τ hτ hτT B G))) n 0 ≤
        (L.velocityCost*A)*majorant L.R (d+3) n :=
  amplitude_bound (fun {r} H => velocityPath τ hτ hτT B (H : Forcing P D r))
    (fun H => velocityPath_orbit τ hτ hτT B H)
    (fun H J a he => velocityPath_eq_smul τ hτ hτT B H J a he)
    L.fullProfile L.fullProfile_pos directions q L.R L.velocityCost d (d+3)
    (fun H he => L.velocity_unit_bound H directions hdir d he) G A hA hforce n


-- @@ L479-488 verbatim
/-- The genuine time derivative divided by the same profile, with no g derivative. -/
theorem derivative_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (derivativePath τ hτ hτT B G))) n 0 ≤
        (L.derivativeCost*A)*majorant L.R (d+3) n :=
  amplitude_bound (fun {r} H => derivativePath τ hτ hτT B (H : Forcing P D r))
    (fun H => derivativePath_orbit τ hτ hτT B H)
    (fun H J a he => derivativePath_eq_smul τ hτ hτT B H J a he)
    L.fullProfile L.fullProfile_pos directions q L.R L.derivativeCost d (d+3)
    (fun H he => L.derivative_unit_bound H directions hdir d he) G A hA hforce n


-- @@ L490-490 verbatim
end EulerTransversePacketJoin.Budget


-- @@ L492-492 verbatim
end

-- @@ L493-493 verbatim
end


-- @@ L495-495 verbatim
end


-- @@ L497-497 verbatim
@[expose] public section


-- @@ L499-499 verbatim
noncomputable section


-- @@ L501-501 verbatim
namespace EulerTransversePacketJoin.Budget


-- @@ L503-506 verbatim
open Set ContinuousLinearMap EulerSmoothLimit EulerTransversePacketProvider
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerPacketProfileRecursion
  EulerParameterWordGevrey EulerGevrey EulerContinuousTimeWeight EulerCylinderSobolev
  EulerSourceNormalResidualBounds

-- @@ L507-507 verbatim
open scoped ContDiff


-- @@ L509-510 verbatim
private theorem standard_norm (i : Fin 4) : ‖standardDirection i‖ ≤ 1 := by
  cases i using Fin.cases <;> simp [Prod.norm_def]


-- @@ L512-516 verbatim
variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T}
  {B : HistoryData (D.initial τ hτ hτT.le)} {q : ℕ}
  (L : Budget D τ hτ hτT B (Fin 4) q) (N : NormalBudget D q L.R)


-- @@ L518-519 verbatim
/-- Pressure amplitude, given by `P*pressureCost (Fin 4) q N.Ri N.C N.C 1 L.commonCost`. -/
def pressureAmplitude : ℝ := P*pressureCost (Fin 4) q N.Ri N.C N.C 1 L.commonCost

-- @@ L520-521 verbatim
/-- Potential amplitude, given by `3*N.blockAmplitude*(P*L.commonCost)`. -/
def potentialAmplitude : ℝ := 3*N.blockAmplitude*(P*L.commonCost)

-- @@ L522-523 verbatim
/-- Potential time amplitude, given by `6*N.blockAmplitude*(P*L.commonCost)`. -/
def potentialTimeAmplitude : ℝ := 6*N.blockAmplitude*(P*L.commonCost)

-- @@ L524-525 verbatim
/-- Corrector amplitude, given by `27*N.blockAmplitude^2*(P*L.commonCost)`. -/
def correctorAmplitude : ℝ := 27*N.blockAmplitude^2*(P*L.commonCost)

-- @@ L526-527 verbatim
/-- Corrector time amplitude, given by `108*N.blockAmplitude^2*(P*L.commonCost)`. -/
def correctorTimeAmplitude : ℝ := 108*N.blockAmplitude^2*(P*L.commonCost)


-- @@ L529-533 verbatim
variable {raw : VectorField} (G : Forcing P D raw) (A : ℝ) (hA : 0 ≤ A) (d : ℕ)
  (hforce : ∀ n, block standardDirection q (fun a => pathTranslate P a
    (normalize L.fullProfile L.fullProfile_pos (HistoryData.forcingPath G))) n 0 ≤ A * majorant L.R
        d
        n)


-- @@ L535-535 verbatim
include hA hforce


-- @@ L537-543 verbatim
theorem velocity_common_bound (n : ℕ) :
    block standardDirection q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (velocityPath τ hτ hτT B G))) n 0 ≤
        (L.commonCost*A)*majorant L.R (d+3) n :=
  (L.velocity_bound G standardDirection standard_norm A hA d hforce n).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right L.velocityCost_le_common hA)
      (majorant_nonneg L.R (zero_le_one.trans L.radius_bounds.1) (d+3) n))


-- @@ L545-551 verbatim
theorem derivative_common_bound (n : ℕ) :
    block standardDirection q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (derivativePath τ hτ hτT B G))) n 0 ≤
        (L.commonCost*A)*majorant L.R (d+3) n :=
  (L.derivative_bound G standardDirection standard_norm A hA d hforce n).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right L.derivativeCost_le_common hA)
      (majorant_nonneg L.R (zero_le_one.trans L.radius_bounds.1) (d+3) n))


-- @@ L553-567 verbatim
theorem pressure_bound (n : ℕ) :
    block standardDirection q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (pressurePath τ hτ hτT B G))) n 0 ≤
        (L.pressureAmplitude (P := P) N*A)*majorant L.R (d+3) n := by
  have hf (j : ℕ) : block standardDirection q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (HistoryData.forcingPath G))) j 0 ≤ A*majorant L.R
          (d+3) j :=
    (hforce j).trans (mul_le_mul_of_nonneg_left
      (majorant_mono_shift L.R L.radius_bounds.1 d (d+3) j (by omega)) hA)
  have h := source_pressure_bound τ hτ hτT B G L.fullProfile L.fullProfile_pos
    standardDirection standard_norm q N.Rc N.C N.C N.Ri L.R A (L.commonCost*A)
    N.Rc_nonneg N.C_nonneg N.C_nonneg hA (mul_nonneg L.commonCost_nonneg hA)
    N.inverse_radius N.pressure_radius N.normal_bound N.strain_bound (d+3) hf
    (L.velocity_common_bound G A hA d hforce) n
  exact h.trans_eq (by unfold pressureAmplitude pressureCost; ring)


-- @@ L569-575 verbatim
theorem pressure_gradient_bound (n : ℕ) :
    block standardDirection q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (scalarGradientField τ hτ hτT B G).path)) n 0 ≤
        (3*L.pressureAmplitude (P := P) N*A)*majorant L.R (d+4) n := by
  have h := scalarGradientField_normalized_bound τ hτ hτT B G L.fullProfile L.fullProfile_pos
    q L.R (L.pressureAmplitude (P := P) N*A) (d+3) (L.pressure_bound N G A hA d hforce) n
  simpa only [show d+3+1=d+4 by omega,mul_assoc] using h


-- @@ L577-586 verbatim
theorem potential_bound (n : ℕ) :
    block standardDirection q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (potentialPath τ hτ hτT B G))) n 0 ≤
        (L.potentialAmplitude (P := P) N*A)*majorant L.R (d+3) n := by
  have hc := N.coefficient_bounds
  have h := potentialPath_normalized_bound τ hτ hτT B G L.fullProfile L.fullProfile_pos
    q N.coefficientRadius N.coefficientAmplitude L.R (L.commonCost*A)
    hc.1 hc.2.1 (mul_nonneg L.commonCost_nonneg hA) N.radius (d+3)
    (L.velocity_common_bound G A hA d hforce) (fun j a => (hc.2.2 j a).2.2.1) n
  exact h.trans_eq (by unfold potentialAmplitude NormalBudget.blockAmplitude; ring)


-- @@ L588-598 verbatim
theorem potential_time_bound (n : ℕ) :
    block standardDirection q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (potentialTimePath τ hτ hτT B G))) n 0 ≤
        (L.potentialTimeAmplitude (P := P) N*A)*majorant L.R (d+3) n := by
  have hc := N.coefficient_bounds
  have h := potentialTimePath_normalized_bound τ hτ hτT B G L.fullProfile L.fullProfile_pos
    q N.coefficientRadius N.coefficientAmplitude L.R (L.commonCost*A)
    hc.1 hc.2.1 (mul_nonneg L.commonCost_nonneg hA) N.radius (d+3)
    (L.velocity_common_bound G A hA d hforce) (L.derivative_common_bound G A hA d hforce)
    (fun j a => (hc.2.2 j a).2.2.1) (fun j a => (hc.2.2 j a).2.2.2) n
  exact h.trans_eq (by unfold potentialTimeAmplitude NormalBudget.blockAmplitude; ring)


-- @@ L600-611 verbatim
theorem corrector_bound (n : ℕ) :
    block standardDirection q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (correctorPath τ hτ hτT B G))) n 0 ≤
        (L.correctorAmplitude (P := P) N*A)*majorant L.R (d+4) n := by
  have hc := N.coefficient_bounds
  have h := correctorPath_normalized_bound τ hτ hτT B G L.fullProfile L.fullProfile_pos
    q N.coefficientRadius N.coefficientAmplitude L.R (L.commonCost*A)
    hc.1 hc.2.1 (mul_nonneg L.commonCost_nonneg hA) N.radius (d+3)
    (L.velocity_common_bound G A hA d hforce)
    (fun j a => (hc.2.2 j a).2.2.1) (fun j a => (hc.2.2 j a).1) n
  rw [show d+3+1=d+4 by omega] at h
  exact h.trans_eq (by unfold correctorAmplitude NormalBudget.blockAmplitude; ring)


-- @@ L613-625 verbatim
theorem corrector_time_bound (n : ℕ) :
    block standardDirection q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (correctorTimePath τ hτ hτT B G))) n 0 ≤
        (L.correctorTimeAmplitude (P := P) N*A)*majorant L.R (d+4) n := by
  have hc := N.coefficient_bounds
  have h := correctorTimePath_normalized_bound τ hτ hτT B G L.fullProfile L.fullProfile_pos
    q N.coefficientRadius N.coefficientAmplitude L.R (L.commonCost*A)
    hc.1 hc.2.1 (mul_nonneg L.commonCost_nonneg hA) N.radius (d+3)
    (L.velocity_common_bound G A hA d hforce) (L.derivative_common_bound G A hA d hforce)
    (fun j a => (hc.2.2 j a).2.2.1) (fun j a => (hc.2.2 j a).2.2.2)
    (fun j a => (hc.2.2 j a).1) (fun j a => (hc.2.2 j a).2.1) n
  rw [show d+3+1=d+4 by omega] at h
  exact h.trans_eq (by unfold correctorTimeAmplitude NormalBudget.blockAmplitude; ring)


-- @@ L627-627 verbatim
end EulerTransversePacketJoin.Budget


-- @@ L629-629 verbatim
end

-- @@ L630-630 verbatim
end


-- @@ L632-632 verbatim
end


-- @@ L634-634 verbatim
@[expose] public section


-- @@ L636-636 verbatim
noncomputable section


-- @@ L638-638 verbatim
namespace EulerPacketCylinderField


-- @@ L640-640 verbatim
open Set EulerPacketProfileRecursion


-- @@ L642-644 verbatim
theorem smul_profile_pos {K : Type*} [TopologicalSpace K]
    (g : C(K, ℝ)) (hg : ∀ t, 0 < g t) (c : ℝ) (hc : 0 < c) (t : K) :
    0 < (c • g) t := mul_pos hc (hg t)


-- @@ L646-646 verbatim
namespace Field


-- @@ L648-650 verbatim
variable {P T : ℝ} [Fact (0 < P)] {raw : VectorField} {G : Field P T raw}
  (hT : 0 ≤ T) (g : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t)
  (c : ℝ) (hc : 0 < c) {q d : ℕ} {R A : ℝ}


-- @@ L652-655 verbatim
theorem WordBound.unscale_profile
    (hG : (G.normalized hT (c • g) (smul_profile_pos g hg c hc)).WordBound q R A d) :
    (G.normalized hT g hg).WordBound q R (c*A) d :=
  hG.changeProfile hT g hg c hc.le (fun _ => le_rfl)


-- @@ L657-665 verbatim
theorem WordBound.scale_profile
    (hG : (G.normalized hT g hg).WordBound q R (A * c) d) :
    (G.normalized hT (c • g) (smul_profile_pos g hg c hc)).WordBound q R A d := by
  have hh := hG.changeProfile hT (c • g) (smul_profile_pos g hg c hc) c⁻¹
    (inv_nonneg.mpr hc.le) (fun t => by
      change g t ≤ c⁻¹*(c*g t)
      rw [← mul_assoc,inv_mul_cancel₀ hc.ne',one_mul])
  have he : c⁻¹*(A*c) = A := by field_simp
  simpa only [he] using hh


-- @@ L667-667 verbatim
end Field

-- @@ L668-668 verbatim
end EulerPacketCylinderField


-- @@ L670-670 verbatim
namespace EulerTransversePacketJoin.Budget


-- @@ L672-674 verbatim
open Set EulerSmoothLimit EulerTransversePacketProvider EulerPacketCylinderField
  EulerPacketProfileRecursion EulerPacketShiftArithmetic EulerContinuousTimeWeight
  EulerParameterWordGevrey EulerGevrey EulerSourceNormalResidualBounds

-- @@ L675-675 verbatim
open scoped ContDiff


-- @@ L677-681 verbatim
variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T}
  {B : HistoryData (D.initial τ hτ hτT.le)}
  (L : Budget D τ hτ hτT B (Fin 4) 6) (N : NormalBudget D 6 L.R)


-- @@ L683-693 verbatim
theorem pressureAmplitude_nonneg : 0 ≤ L.pressureAmplitude (P := P) N := by
  have hRi := N.Ri_nonneg
  have hC := N.C_nonneg
  have hL := L.commonCost_nonneg
  have hP := (Fact.out : 0 < P).le
  have hm := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) 6 (4*N.Ri) (3*N.Ri*N.C)
    (by positivity) (by positivity)
  have hM := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) 6 (4*N.Ri) N.C
    (by positivity) hC
  unfold pressureAmplitude pressureCost
  positivity


-- @@ L695-699 verbatim
theorem correctorAmplitude_nonneg : 0 ≤ L.correctorAmplitude (P := P) N := by
  have hL := L.commonCost_nonneg
  have hP := (Fact.out : 0 < P).le
  unfold correctorAmplitude
  positivity


-- @@ L701-705 verbatim
theorem correctorTimeAmplitude_nonneg : 0 ≤ L.correctorTimeAmplitude (P := P) N := by
  have hL := L.commonCost_nonneg
  have hP := (Fact.out : 0 < P).le
  unfold correctorTimeAmplitude
  positivity


-- @@ L707-713 verbatim
/-- These four numerical guards depend only on the source data and the fixed
external radius.  They are chosen before the forcing, its amplitude or grade. -/
structure GradeGuards : Prop where
  common : L.commonCost ≤ L.R
  corrector : L.correctorAmplitude (P := P) N ≤ L.R
  correctorTime : L.correctorTimeAmplitude (P := P) N ≤ L.R
  pressureGradient : 3*L.pressureAmplitude (P := P) N ≤ L.R


-- @@ L715-718 verbatim
private theorem grade_shift_room (p : ℕ) (hp : 2 ≤ p) :
    highForceShift p+3+1 ≤ highShift p ∧ highForceShift p+4+1 ≤ highShift p := by
  simp only [highForceShift,highShift]
  omega


-- @@ L720-724 verbatim
variable (W : GradeGuards (P := P) L N) {raw : VectorField}
  (G : Forcing P D raw) (F : Field P D.T raw) (c : ℝ) (hc : 0 < c)
  (p : ℕ) (hp : 2 ≤ p)
  (hforce : (F.normalized D.T_pos.le (c • L.fullProfile)
    (smul_profile_pos L.fullProfile L.fullProfile_pos c hc)).WordBound 6 L.R 1 (highForceShift p))


-- @@ L726-726 verbatim
include N W hp hforce


-- @@ L728-776 verbatim
/-- Actual A, A_t, curl corrector, its time derivative, and the literal scalar
pressure gradient satisfy the unit grade budget with the same time profile. -/
theorem grade_bounds :
    ((vectorField τ hτ hτT B G).normalized D.T_pos.le (c • L.fullProfile)
      (smul_profile_pos L.fullProfile L.fullProfile_pos c hc)).WordBound 6 L.R 1 (highShift p) ∧
    ((vectorDerivativeField τ hτ hτT B G).normalized D.T_pos.le (c • L.fullProfile)
      (smul_profile_pos L.fullProfile L.fullProfile_pos c hc)).WordBound 6 L.R 1 (highShift p) ∧
    ((correctorField τ hτ hτT B G).normalized D.T_pos.le (c • L.fullProfile)
      (smul_profile_pos L.fullProfile L.fullProfile_pos c hc)).WordBound 6 L.R 1 (highShift p) ∧
    ((correctorDerivativeField τ hτ hτT B G).normalized D.T_pos.le (c • L.fullProfile)
      (smul_profile_pos L.fullProfile L.fullProfile_pos c hc)).WordBound 6 L.R 1 (highShift p) ∧
    ((scalarGradientField τ hτ hτT B G).normalized D.T_pos.le (c • L.fullProfile)
      (smul_profile_pos L.fullProfile L.fullProfile_pos c hc)).WordBound 6 L.R 1 (highShift p) := by
  have hf : (G.forcingField.normalized D.T_pos.le L.fullProfile L.fullProfile_pos).WordBound
      6 L.R c (highForceShift p) := by
    have hh := hforce.unscale_profile D.T_pos.le L.fullProfile L.fullProfile_pos c hc
    have hh' : (F.normalized D.T_pos.le L.fullProfile L.fullProfile_pos).WordBound
        6 L.R c (highForceShift p) := by simpa only [mul_one] using hh
    exact hh'.transfer _
  have hv : ((vectorField τ hτ hτT B G).normalized D.T_pos.le L.fullProfile
      L.fullProfile_pos).WordBound 6 L.R (L.commonCost*c) (highForceShift p+3) :=
    L.velocity_common_bound G c hc.le (highForceShift p) hf
  have ht : ((vectorDerivativeField τ hτ hτT B G).normalized D.T_pos.le L.fullProfile
      L.fullProfile_pos).WordBound 6 L.R (L.commonCost*c) (highForceShift p+3) :=
    L.derivative_common_bound G c hc.le (highForceShift p) hf
  have hC : ((correctorField τ hτ hτT B G).normalized D.T_pos.le L.fullProfile
      L.fullProfile_pos).WordBound 6 L.R (L.correctorAmplitude (P := P) N*c) (highForceShift p+4) :=
    L.corrector_bound N G c hc.le (highForceShift p) hf
  have hCt : ((correctorDerivativeField τ hτ hτT B G).normalized D.T_pos.le L.fullProfile
      L.fullProfile_pos).WordBound 6 L.R (L.correctorTimeAmplitude (P := P) N*c) (highForceShift
          p+4) :=
    L.corrector_time_bound N G c hc.le (highForceShift p) hf
  have hπ : ((scalarGradientField τ hτ hτT B G).normalized D.T_pos.le L.fullProfile
      L.fullProfile_pos).WordBound 6 L.R ((3*L.pressureAmplitude (P := P) N)*c) (highForceShift
          p+4) :=
    L.pressure_gradient_bound N G c hc.le (highForceShift p) hf
  have hroom := grade_shift_room p hp
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact (hv.scale_profile D.T_pos.le L.fullProfile L.fullProfile_pos c hc).absorb_amplitude_to
      L.radius_bounds.1 L.commonCost_nonneg W.common hroom.1
  · exact (ht.scale_profile D.T_pos.le L.fullProfile L.fullProfile_pos c hc).absorb_amplitude_to
      L.radius_bounds.1 L.commonCost_nonneg W.common hroom.1
  · exact (hC.scale_profile D.T_pos.le L.fullProfile L.fullProfile_pos c hc).absorb_amplitude_to
      L.radius_bounds.1 (L.correctorAmplitude_nonneg N) W.corrector hroom.2
  · exact (hCt.scale_profile D.T_pos.le L.fullProfile L.fullProfile_pos c hc).absorb_amplitude_to
      L.radius_bounds.1 (L.correctorTimeAmplitude_nonneg N) W.correctorTime hroom.2
  · exact (hπ.scale_profile D.T_pos.le L.fullProfile L.fullProfile_pos c hc).absorb_amplitude_to
      L.radius_bounds.1 (mul_nonneg (by
          norm_num) (L.pressureAmplitude_nonneg N)) W.pressureGradient hroom.2


-- @@ L778-781 verbatim
theorem vector_grade_bound :
    ((vectorField τ hτ hτT B G).normalized D.T_pos.le (c • L.fullProfile)
      (smul_profile_pos L.fullProfile L.fullProfile_pos c hc)).WordBound 6 L.R 1 (highShift p) :=
  (L.grade_bounds N W G F c hc p hp hforce).1


-- @@ L783-786 verbatim
theorem derivative_grade_bound :
    ((vectorDerivativeField τ hτ hτT B G).normalized D.T_pos.le (c • L.fullProfile)
      (smul_profile_pos L.fullProfile L.fullProfile_pos c hc)).WordBound 6 L.R 1 (highShift p) :=
  (L.grade_bounds N W G F c hc p hp hforce).2.1


-- @@ L788-791 verbatim
theorem corrector_grade_bound :
    ((correctorField τ hτ hτT B G).normalized D.T_pos.le (c • L.fullProfile)
      (smul_profile_pos L.fullProfile L.fullProfile_pos c hc)).WordBound 6 L.R 1 (highShift p) :=
  (L.grade_bounds N W G F c hc p hp hforce).2.2.1


-- @@ L793-796 verbatim
theorem corrector_derivative_grade_bound :
    ((correctorDerivativeField τ hτ hτT B G).normalized D.T_pos.le (c • L.fullProfile)
      (smul_profile_pos L.fullProfile L.fullProfile_pos c hc)).WordBound 6 L.R 1 (highShift p) :=
  (L.grade_bounds N W G F c hc p hp hforce).2.2.2.1


-- @@ L798-801 verbatim
theorem pressure_gradient_grade_bound :
    ((scalarGradientField τ hτ hτT B G).normalized D.T_pos.le (c • L.fullProfile)
      (smul_profile_pos L.fullProfile L.fullProfile_pos c hc)).WordBound 6 L.R 1 (highShift p) :=
  (L.grade_bounds N W G F c hc p hp hforce).2.2.2.2


-- @@ L803-803 verbatim
end EulerTransversePacketJoin.Budget
