/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.KrausGauge
import TNLean.MPS.Defs


-- @@ L9-14 verbatim
/-!
# MPS bridges for Kraus gauges

This file records the genuine `GaugeEquiv` and `SameMPV` consequences of the
generic TP and unital gauge constructions.
-/


-- @@ L16-16 verbatim
open scoped Matrix ComplexOrder MatrixOrder BigOperators


-- @@ L18-18 verbatim
namespace MPSTensor


-- @@ L20-20 verbatim
variable {d D : ℕ}


-- @@ L22-32 verbatim
/-- The TP-gauged family is gauge-equivalent to the original tensor. -/
theorem gaugeEquiv_tpGauge
    (A : MPSTensor d D) (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    GaugeEquiv A (Kraus.tpGauge A ρ) := by
  classical
  let X : GL (Fin D) ℂ :=
    Matrix.GeneralLinearGroup.mk'' (CFC.sqrt ρ) (by
      simpa using Matrix.PosDef.isUnit_det_cfc_sqrt hρ)
  refine ⟨X, ?_⟩
  intro i
  simp [Kraus.tpGauge, X]


-- @@ L34-44 verbatim
/-- The unital-gauged family is gauge-equivalent to the original tensor. -/
theorem gaugeEquiv_unitalGauge
    (A : MPSTensor d D) (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    GaugeEquiv A (Kraus.unitalGauge A ρ) := by
  classical
  let X : GL (Fin D) ℂ :=
    Matrix.GeneralLinearGroup.mk'' (CFC.sqrt ρ) (by
      simpa using Matrix.PosDef.isUnit_det_cfc_sqrt hρ)
  refine ⟨X⁻¹, ?_⟩
  intro i
  simp [Kraus.unitalGauge, X]


-- @@ L46-50 verbatim
/-- Unital gauging preserves finite-ring MPV coefficients. -/
theorem sameMPV_unitalGauge
    (A : MPSTensor d D) (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    SameMPV A (Kraus.unitalGauge A ρ) :=
  GaugeEquiv.sameMPV (gaugeEquiv_unitalGauge A ρ hρ)


-- @@ L52-52 verbatim
end MPSTensor
