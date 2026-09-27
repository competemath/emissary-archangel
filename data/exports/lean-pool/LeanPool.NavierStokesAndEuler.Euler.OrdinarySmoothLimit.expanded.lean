/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinarySobolevTower
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryCauchyInterpolation


-- @@ L12-15 verbatim
/-! A Cauchy sequence of genuine smooth L² paths with uniform bounds at
every Sobolev order has a single genuine smooth limit path. All its
tensor jets are continuous in time and are the strong limits of the
corresponding jets of the sequence. -/


-- @@ L17-17 verbatim
@[expose] public section



-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-22 verbatim
namespace EulerOrdinarySobolev


-- @@ L24-27 verbatim
open Set Filter MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal EulerMeanOrdinaryLift
  EulerMeanSmoothRepresentative EulerSmoothFieldSobolevTime EulerLiftedGradientSpace
  EulerCylinderSobolevSpace

-- @@ L28-28 verbatim
open scoped ContDiff Topology


-- @@ L30-30 verbatim
local instance instOrdinarySmoothLimit1 : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩


-- @@ L32-32 verbatim
variable {T : ℝ}


-- @@ L34-38 verbatim
/-- Jet path, given by `⟨fun t => (A t).jetLp n,hA n⟩`. -/
def jetPath (A : Icc (0 : ℝ) T → SmoothL2Field Space)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) (n : ℕ) :
    C(Icc (0 : ℝ) T,Lp (Space [×n]→L[ℝ] Space) 2 (volume : Measure Space)) :=
  ⟨fun t => (A t).jetLp n,hA n⟩


-- @@ L40-47 verbatim
/-- Smooth limit data, collecting `tower`, `value_convergence`, `sobolev_convergence`. -/
structure SmoothLimitData (A : ℕ → Icc (0 : ℝ) T → SmoothL2Field Space)
    (hA : ∀ k n, Continuous (fun t => (A k t).jetLp n)) where
  /-- Tower of `SmoothLimitData`, of type `SobolevTower T`. -/
  tower : SobolevTower T
  value_convergence : Tendsto (fun k => fieldPath (A k) (hA k)) atTop (𝓝 tower.field)
  sobolev_convergence : ∀ q,
    Tendsto (fun k => sobolevPath (A k) (hA k) q) atTop (𝓝 (tower.realization q))


-- @@ L49-75 verbatim
theorem nonempty_smoothLimitData (hT : 0 ≤ T)
    (A : ℕ → Icc (0 : ℝ) T → SmoothL2Field Space)
    (hA : ∀ k n, Continuous (fun t => (A k t).jetLp n))
    (hb : ∀ q, ∃ M : ℝ, ∀ k t, tensorNorm q (A k t) ≤ M)
    (h0 : CauchySeq (fun k => fieldPath (A k) (hA k))) : Nonempty (SmoothLimitData A hA) := by
  obtain ⟨u,hu⟩ := cauchySeq_tendsto_of_complete h0
  choose v hv using exists_sobolevPath_limit hT A hA hb h0
  have he (q : ℕ) : (valueOperator 1 q).compLeftContinuous ℝ (Icc (0 : ℝ) T) (v q) =
      ordinaryLift.toContinuousLinearMap.compLeftContinuous ℝ (Icc (0 : ℝ) T) u := by
    let L := (valueOperator 1 q).compLeftContinuous ℝ (Icc (0 : ℝ) T)
    let R := ordinaryLift.toContinuousLinearMap.compLeftContinuous ℝ (Icc (0 : ℝ) T)
    have hleft := (L.continuous.tendsto (v q)).comp (hv q)
    have hright := (R.continuous.tendsto u).comp hu
    have heq : (fun k => L (sobolevPath (A k) (hA k) q)) =
        fun k => R (fieldPath (A k) (hA k)) := by
      funext k
      apply ContinuousMap.ext
      intro t
      exact ordinarySobolev_value q (A k t).toLp (A k t).translation_contDiff
    simp only [Function.comp_def] at hleft
    rw [heq] at hleft
    exact tendsto_nhds_unique hleft hright
  let B : SobolevTower T := {
    field := u
    realization := v
    value_eq := fun q t => congrArg (fun p : C(Icc (0 : ℝ) T,LiftL2 1) => p t) (he q) }
  exact ⟨⟨B,hu,hv⟩⟩


-- @@ L77-83 verbatim
/-- Smooth limit data, given by `Classical.choice (nonempty_smoothLimitData hT A hA hb h0)`. -/
def smoothLimitData (hT : 0 ≤ T)
    (A : ℕ → Icc (0 : ℝ) T → SmoothL2Field Space)
    (hA : ∀ k n, Continuous (fun t => (A k t).jetLp n))
    (hb : ∀ q, ∃ M : ℝ, ∀ k t, tensorNorm q (A k t) ≤ M)
    (h0 : CauchySeq (fun k => fieldPath (A k) (hA k))) : SmoothLimitData A hA :=
  Classical.choice (nonempty_smoothLimitData hT A hA hb h0)


-- @@ L85-85 verbatim
namespace SmoothLimitData


-- @@ L87-88 verbatim
variable {A : ℕ → Icc (0 : ℝ) T → SmoothL2Field Space}
  {hA : ∀ k n, Continuous (fun t => (A k t).jetLp n)} (L : SmoothLimitData A hA)


-- @@ L90-91 verbatim
/-- Field: an abbreviation for `L.tower.smoothField t`. -/
abbrev field (t : Icc (0 : ℝ) T) : SmoothL2Field Space := L.tower.smoothField t


-- @@ L93-94 verbatim
theorem field_continuous (n : ℕ) : Continuous (fun t => (L.field t).jetLp n) :=
  L.tower.smoothField_jet_continuous n


-- @@ L96-98 verbatim
theorem fieldPath_eq : fieldPath L.field L.field_continuous=L.tower.field := by
  apply ContinuousMap.ext
  exact L.tower.smoothField_toLp


-- @@ L100-103 verbatim
theorem fieldPath_convergence :
    Tendsto (fun k => fieldPath (A k) (hA k)) atTop (𝓝 (fieldPath L.field L.field_continuous)) := by
  rw [L.fieldPath_eq]
  exact L.value_convergence


-- @@ L105-116 verbatim
theorem jetPath_convergence (n : ℕ) :
    Tendsto (fun k => jetPath (A k) (hA k) n) atTop (𝓝 (jetPath L.field L.field_continuous n)) := by
  let C := (ordinaryTensorOperator n).compLeftContinuous ℝ (Icc (0 : ℝ) T)
  have h := (C.continuous.tendsto (L.tower.realization n)).comp (L.sobolev_convergence n)
  have ha (k : ℕ) : C (sobolevPath (A k) (hA k) n)=jetPath (A k) (hA k) n := by
    apply ContinuousMap.ext
    intro t
    exact ordinaryTensorOperator_apply (A k t) n
  have hb : C (L.tower.realization n)=jetPath L.field L.field_continuous n := by
    apply ContinuousMap.ext
    exact L.tower.tensorOperator_realization n
  simpa only [Function.comp_def,ha,hb] using h


-- @@ L118-120 verbatim
theorem jet_convergence (n : ℕ) (t : Icc (0 : ℝ) T) :
    Tendsto (fun k => (A k t).jetLp n) atTop (𝓝 ((L.field t).jetLp n)) :=
  ((ContinuousMap.evalCLM ℝ t).continuous.tendsto _).comp (L.jetPath_convergence n)


-- @@ L122-124 verbatim
theorem toLp_convergence (t : Icc (0 : ℝ) T) :
    Tendsto (fun k => (A k t).toLp) atTop (𝓝 ((L.field t).toLp)) :=
  ((ContinuousMap.evalCLM ℝ t).continuous.tendsto _).comp L.fieldPath_convergence


-- @@ L126-128 verbatim
theorem tensorNorm_convergence (q : ℕ) (t : Icc (0 : ℝ) T) :
    Tendsto (fun k => tensorNorm q (A k t)) atTop (𝓝 (tensorNorm q (L.field t))) :=
  tendsto_finsetSum _ (fun n _ => (L.jet_convergence n t).norm)


-- @@ L130-133 verbatim
theorem tensorNorm_bound (q : ℕ) (M : ℝ)
    (hb : ∀ k t, tensorNorm q (A k t) ≤ M) (t : Icc (0 : ℝ) T) :
    tensorNorm q (L.field t) ≤ M :=
  le_of_tendsto (L.tensorNorm_convergence q t) (Eventually.of_forall (fun k => hb k t))


-- @@ L135-135 verbatim
end SmoothLimitData

-- @@ L136-136 verbatim
end EulerOrdinarySobolev
