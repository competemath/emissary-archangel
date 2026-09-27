/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryGradeBounds
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPrimaryBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketCommonRadius


-- @@ L12-14 verbatim
/-! The primary grade imposes only finitely many fixed lower bounds on the
external radius.  Enlarging it leaves the time profile and every source cost
unchanged, including the terminal amplitude before its scalar multiplier. -/


-- @@ L16-16 verbatim
section


-- @@ L18-23 verbatim
/-!
The additional primary guards can be met by one explicit enlargement of
the common external radius. Neither source coefficients nor profile costs
are changed. The extra lower bound can include the actual terminal-wave
radius, before the recursive solve begins.
-/


-- @@ L25-25 verbatim
@[expose] public section


-- @@ L27-27 verbatim
noncomputable section


-- @@ L29-29 verbatim
namespace EulerTransversePacketPrimary


-- @@ L31-33 verbatim
open EulerTransversePacketProvider EulerParameterWordGevrey EulerTransverseFixedSobolev
  EulerTimeLpGramSobolev  EulerFixedEvolutionSobolev
  EulerCylinderDirichlet.Coefficients EulerSourceCylinderForwardSobolev EulerLinearDuhamel


-- @@ L35-38 verbatim
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T}
  {B : HistoryData (D.initial τ hτ hτT.le)} {ι : Type*} [Fintype ι] {q : ℕ}
  (L : EulerTransversePacketJoin.Budget D τ hτ hτT B ι q)


-- @@ L40-43 verbatim
/-- Weak radius as an element of `ℝ`. -/
def weakRadius : ℝ :=
  2*blockCost ι q τ L.Rc L.C₀ L.C₁ L.CH (D.initial τ hτ hτT.le).frameLower
    (endpointForcingCost ι q τ L.Rc L.C₁)*(sobolevCoefficientRadius ι L.Rc+1)


-- @@ L45-49 verbatim
/-- Strong radius as an element of `ℝ`. -/
def strongRadius : ℝ :=
  2*gramBlockCost ι q (D.initial τ hτ hτT.le).frameLower L.Rc L.C₀
    (accelerationBlockAmplitude ι q L.Rc L.C₀ L.C₁ (endpointForcingCost ι q τ L.Rc L.C₁) 1) *
      (sobolevCoefficientRadius ι L.Rc+1)


-- @@ L51-56 verbatim
/-- Uniform radius as an element of `ℝ`. -/
def uniformRadius : ℝ :=
  2*gramBlockCost ι q (D.initial τ hτ hτT.le).frameLower L.Rc L.C₀
    (accelerationBlockAmplitude ι q L.Rc L.C₀ L.C₁ (endpointForcingCost ι q τ L.Rc L.C₁) (traceCost
        τ)) *
      (sobolevCoefficientRadius ι L.Rc+1)


-- @@ L58-62 verbatim
/-- Forward radius as an element of `ℝ`. -/
def forwardRadius : ℝ :=
  2*forwardSobolevCost ι q (D.T-τ) L.C (τ⁻¹+traceCost τ)
    (forcingCost ι q L.Ri L.C₀*0) (18*L.Ri*L.C₀*L.C₁) (4*L.Ri) *
      (sobolevCoefficientRadius ι (4*L.Ri)+1)


-- @@ L64-68 verbatim
/-- Required radius, given by `max extra (max L.R (max (weakRadius L) (max (strongRadius L) (max
(uniformRadius L) (forwardRadius L)))))`. -/
def requiredRadius (extra : ℝ) : ℝ :=
  max extra (max L.R (max (weakRadius L) (max (strongRadius L) (max (uniformRadius L)
      (forwardRadius L)))))


-- @@ L70-71 verbatim
theorem le_requiredRadius (extra : ℝ) : L.R ≤ requiredRadius L extra :=
  (le_max_left _ _).trans (le_max_right _ _)


-- @@ L73-73 verbatim
theorem extra_le_requiredRadius (extra : ℝ) : extra ≤ requiredRadius L extra := le_max_left _ _


-- @@ L75-78 verbatim
/-- Enlarge for primary, given by `L.enlargeRadius (requiredRadius L extra) (le_requiredRadius L
extra)`. -/
def enlargeForPrimary (extra : ℝ) : EulerTransversePacketJoin.Budget D τ hτ hτT B ι q :=
  L.enlargeRadius (requiredRadius L extra) (le_requiredRadius L extra)


-- @@ L80-87 verbatim
theorem requiredBudget (extra : ℝ) : Budget (enlargeForPrimary L extra) := {
  history_weak := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  history_strong := (le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _)))
  history_uniform := (le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
  forward_radius := (le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))) }


-- @@ L89-89 verbatim
namespace Budget


-- @@ L91-91 verbatim
variable {L} (H : Budget L) (R' : ℝ) (hR : L.R ≤ R')


-- @@ L93-98 verbatim
include H in
theorem enlargeRadius : Budget (L.enlargeRadius R' hR) := {
  history_weak := H.history_weak.trans hR
  history_strong := H.history_strong.trans hR
  history_uniform := H.history_uniform.trans hR
  forward_radius := H.forward_radius.trans hR }


-- @@ L100-101 verbatim
@[simp] theorem enlargeRadius_velocityCost : (H.enlargeRadius R' hR).velocityCost = H.velocityCost
    := rfl


-- @@ L103-104 verbatim
@[simp] theorem enlargeRadius_derivativeCost : (H.enlargeRadius R' hR).derivativeCost =
    H.derivativeCost := rfl


-- @@ L106-106 verbatim
end Budget

-- @@ L107-107 verbatim
end EulerTransversePacketPrimary


-- @@ L109-109 verbatim
end

-- @@ L110-110 verbatim
end


-- @@ L112-112 verbatim
end


-- @@ L114-114 verbatim
@[expose] public section


-- @@ L116-116 verbatim
noncomputable section


-- @@ L118-118 verbatim
namespace EulerTransversePacketPrimary.Budget


-- @@ L120-120 verbatim
open EulerTransversePacketProvider


-- @@ L122-128 verbatim
variable {P : ℝ}
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T}
  {B : HistoryData (D.initial τ hτ hτT.le)}
  {L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6}
  (H : Budget L) (N : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  (C : ℝ)


-- @@ L130-133 verbatim
/-- Grade radius, constructed using `max`. -/
def gradeRadius : ℝ :=
  max L.R (max (H.commonCost*C) (max (H.correctorAmplitude (P := P) N*C)
    (max (H.correctorTimeAmplitude (P := P) N*C) (3*H.pressureAmplitude (P := P) N*C))))


-- @@ L135-147 verbatim
theorem gradeRadius_bounds :
    L.R ≤ H.gradeRadius (P := P) N C ∧
    H.commonCost*C ≤ H.gradeRadius (P := P) N C ∧
    H.correctorAmplitude (P := P) N*C ≤ H.gradeRadius (P := P) N C ∧
    H.correctorTimeAmplitude (P := P) N*C ≤ H.gradeRadius (P := P) N C ∧
    3*H.pressureAmplitude (P := P) N*C ≤ H.gradeRadius (P := P) N C := by
  unfold gradeRadius
  exact ⟨le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)),
    (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _))),
    (le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))⟩


-- @@ L149-156 verbatim
theorem gradeRadius_guards (hC : 0 ≤ C) (R' : ℝ)
    (hR : H.gradeRadius (P := P) N C ≤ R') :
    ∃ h : L.R ≤ R', GradeGuards (P := P) (H.enlargeRadius R' h)
      (N.enlargeRadius R' h) C := by
  have hb := H.gradeRadius_bounds (P := P) N C
  refine ⟨hb.1.trans hR, ?_⟩
  exact ⟨hC, hb.2.1.trans hR, hb.2.2.1.trans hR,
    hb.2.2.2.1.trans hR, hb.2.2.2.2.trans hR⟩


-- @@ L158-164 verbatim
/-- An arbitrary extra requirement can be included without changing any
source cost or the primary time profile. -/
theorem exists_grade_radius (hC : 0 ≤ C) (extra : ℝ) :
    ∃ R' : ℝ, extra ≤ R' ∧ ∃ h : L.R ≤ R',
      GradeGuards (P := P) (H.enlargeRadius R' h) (N.enlargeRadius R' h) C :=
  ⟨max extra (H.gradeRadius (P := P) N C), le_max_left _ _,
    H.gradeRadius_guards N C hC _ (le_max_right _ _)⟩


-- @@ L166-166 verbatim
namespace GradeGuards


-- @@ L168-168 verbatim
variable {H N C}


-- @@ L170-173 verbatim
theorem enlargeRadius (W : GradeGuards (P := P) H N C) (R' : ℝ) (h : L.R ≤ R') :
    GradeGuards (P := P) (H.enlargeRadius R' h) (N.enlargeRadius R' h) C :=
  ⟨W.terminal_nonneg, W.common.trans h, W.corrector.trans h,
    W.correctorTime.trans h, W.pressureGradient.trans h⟩


-- @@ L175-175 verbatim
end GradeGuards

-- @@ L176-176 verbatim
end EulerTransversePacketPrimary.Budget
