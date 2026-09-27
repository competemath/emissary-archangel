/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderCoefficientData
public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketProvider
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketCorrectorOperator


-- @@ L13-13 verbatim
/-! Literal packet operators and coefficient witnesses from the given analytic source data. -/


-- @@ L15-15 verbatim
@[expose] public section



-- @@ L18-18 verbatim
noncomputable section


-- @@ L20-20 verbatim
namespace EulerPacketCylinderField


-- @@ L22-22 verbatim
open Set EulerSmoothLimit EulerMeanCoefficients EulerPacketPointJets EulerPacketProfileRecursion


-- @@ L24-26 verbatim
/-- Change time, given by `h ▸ G`. -/
def MatrixCoefficient.changeTime {T T' : ℝ} {raw : Domain → Space →L[ℝ] Space}
    (G : MatrixCoefficient T raw) (h : T = T') : MatrixCoefficient T' raw := h ▸ G


-- @@ L28-30 verbatim
/-- Change time, given by `h ▸ G`. -/
def VectorCoefficient.changeTime {T T' : ℝ} {raw : VectorField}
    (G : VectorCoefficient T raw) (h : T = T') : VectorCoefficient T' raw := h ▸ G


-- @@ L32-34 verbatim
variable (P : ℝ) [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : EulerTransversePacketProvider.Data U) (I : EulerTransversePacketProvider.InitialData P D)


-- @@ L36-45 verbatim
/-- Every linear solve and the curl corrector is the concrete source construction. -/
def sourceOperators : Operators where
  interval := Icc (0 : ℝ) M.T
  period := P
  inverseFrame z := D.FInv.field (D.clamp z.1) z.2.1
  strain := D.strain
  normal := D.normalField
  meanSolve := EulerMeanPacketProvider.meanSolve M
  highSolve := EulerTransversePacketProvider.highSolve P D I
  curlCorrector := D.curlCorrector P


-- @@ L47-69 verbatim
/-- No regularity of a solved field or abstract operator family is an input here. -/
def sourceCoefficientData (hT : M.T = D.T) : CoefficientData P M.T (sourceOperators P M D I) where
  period_eq := rfl
  interval_eq := rfl
  inverse := (show MatrixCoefficient D.T (fun z => D.FInv.field (D.clamp z.1) z.2.1) from {
    path := D.FInv.field
    orbit := D.FInv.translation_contDiff
    raw_eq := fun t _ _ => by rw [EulerTransversePacketProvider.Data.clamp_coe]
  }).changeTime hT.symm
  strain := (show MatrixCoefficient D.T D.strain from {
    path := D.M.field
    orbit := D.M.translation_contDiff
    raw_eq := fun t _ _ => by
      simp only [EulerTransversePacketProvider.Data.strain,
          EulerTransversePacketProvider.Data.clamp_coe]
  }).changeTime hT.symm
  normal := (show VectorCoefficient D.T D.normalField from {
    path := D.normal.field
    orbit := D.normal.translation_contDiff
    raw_eq := fun t _ _ => by
      simp only [EulerTransversePacketProvider.Data.normalField,
          EulerTransversePacketProvider.Data.clamp_coe]
  }).changeTime hT.symm


-- @@ L71-71 verbatim
end EulerPacketCylinderField
