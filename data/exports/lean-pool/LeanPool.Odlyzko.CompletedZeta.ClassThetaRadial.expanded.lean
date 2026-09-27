/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.ShapeMellinTranslation
import Mathlib.Tactic.ArithMult.Init


-- @@ L11-11 verbatim
/-! TODO: Add doc-string. -/


-- @@ L13-13 verbatim
@[expose] public section


-- @@ L15-15 verbatim
noncomputable section


-- @@ L17-18 verbatim
open Complex MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units
  NumberField.Units.dirichletUnitTheorem

-- @@ L19-19 verbatim
open scoped nonZeroDivisors


-- @@ L21-21 verbatim
namespace NumberField.Odlyzko


-- @@ L23-23 verbatim
open mixedEmbedding mixedEmbedding.fundamentalCone


-- @@ L25-25 verbatim
variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]


-- @@ L27-32 verbatim
open Classical in
/-- A nonzero shape theta mellin kernel used in the Odlyzko-bound argument. -/
noncomputable def nonzeroShapeThetaMellinKernel
    (J : (Ideal (𝓞 K))⁰) (s : ℂ)
    (y : mixedEmbedding.realSpace K) : ℂ :=
  logarithmicMellinWeight K s y * nonzeroIdealShapeTheta K J y


-- @@ L34-41 verbatim
open Classical in
/-- A nonzero fractional shape theta mellin kernel used in the Odlyzko-bound argument. -/
noncomputable def nonzeroFractionalShapeThetaMellinKernel
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ)
    (y : mixedEmbedding.realSpace K) : ℂ :=
  logarithmicMellinWeight K s y *
    (fractionalShapeIdealTheta K I (expMapBasis y)
      (fun w ↦ (expMapBasis_pos y w).ne') - 1)


-- @@ L43-52 verbatim
open Classical in
theorem integrableOn_nonzeroShapeThetaMellinKernel
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (nonzeroShapeThetaMellinKernel K J s)
      (unitFundamentalParamSet K) := by
  apply IntegrableOn.congr_fun
    (integrableOn_logarithmicMellinWeight_mul_nonzeroIdealShapeTheta K J hs)
    _ measurableSet_unitFundamentalParamSet
  intro y _
  rw [nonzeroShapeThetaMellinKernel, logarithmicMellinWeight]


-- @@ L54-54 verbatim
end NumberField.Odlyzko
