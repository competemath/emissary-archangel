/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.H1
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Measure.Real


-- @@ L12-26 verbatim
/-!
# `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Translation`

Translation utilities for the Euclidean Sobolev model spaces.

This file is intentionally “pre-Rellich”: it provides the algebraic/measure-theoretic translation
operators and their interaction with the `C¹_c` graph embedding used to define `H¹`.

## Main results

- `translateC1c`: translation as a linear endomorphism of `C¹_c`.
- `translateL2`: translation as a linear isometry of `L²` (under an invariant measure).
- `translateL2_toL2` / `translateL2_toL2Grad`: translation commutes with `toL2` / `toL2Grad`.
- `grad_translate`: the Euclidean gradient commutes with translation.
-/


-- @@ L28-28 verbatim
@[expose] public section


-- @@ L30-30 verbatim
namespace RellichKondrachov

-- @@ L31-31 verbatim
namespace Analysis

-- @@ L32-32 verbatim
namespace FunctionalSpaces

-- @@ L33-33 verbatim
namespace Sobolev

-- @@ L34-34 verbatim
namespace Euclidean


-- @@ L36-36 verbatim
open scoped ENNReal MeasureTheory Topology

-- @@ L37-37 verbatim
open MeasureTheory


-- @@ L39-39 verbatim
section Topology


-- @@ L41-41 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]


-- @@ L43-45 verbatim
/-- Translate a function by `a` (right translation): `x ↦ f (x + a)`. -/
def translate {F : Type*} (a : E) (f : E → F) : E → F :=
  fun x => f (x + a)


-- @@ L47-51 verbatim
omit [CompleteSpace E] in
lemma contDiff_translate {f : E → ℝ} (hf : ContDiff ℝ 1 f) (a : E) :
    ContDiff ℝ 1 (translate (E := E) a f) := by
  -- `x ↦ x + a` is `C^∞`; compose.
  exact hf.comp (contDiff_id.add contDiff_const)


-- @@ L53-56 verbatim
omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma hasCompactSupport_translate {F : Type*} [Zero F] {f : E → F}
    (hf : HasCompactSupport f) (a : E) : HasCompactSupport (translate (E := E) a f) := by
  exact hf.comp_homeomorph (Homeomorph.addRight a)


-- @@ L58-65 verbatim
lemma grad_translate (a : E) (f : E → ℝ) (x : E) :
    grad (E := E) (translate (E := E) a f) x = grad (E := E) f (x + a) := by
  classical
  -- `fderiv` commutes with translation, hence so does `grad`.
  -- Reduce to the standard `fderiv` translation lemma, applied under the Riesz dual map.
  have hfderiv : fderiv ℝ (translate (E := E) a f) x = fderiv ℝ f (x + a) :=
    fderiv_comp_add_right (𝕜 := ℝ) (f := f) (x := x) a
  simp only [grad, hfderiv]


-- @@ L67-70 verbatim
omit [CompleteSpace E] in
lemma mem_C1c_translate {f : E → ℝ} (hf : f ∈ C1c (E := E)) (a : E) :
    translate (E := E) a f ∈ C1c (E := E) :=
  ⟨contDiff_translate (E := E) hf.1 a, hasCompactSupport_translate (E := E) hf.2 a⟩


-- @@ L72-80 verbatim
/-- Translation as a linear endomorphism of `C¹_c`. -/
noncomputable def translateC1c (a : E) : ↥(C1c (E := E)) →ₗ[ℝ] ↥(C1c (E := E)) where
  toFun f := ⟨translate (E := E) a f.1, mem_C1c_translate (E := E) (f := f.1) f.2 a⟩
  map_add' f g := by
    ext x
    simp [translate]
  map_smul' c f := by
    ext x
    simp [translate]


-- @@ L82-82 verbatim
end Topology


-- @@ L84-84 verbatim
section Measure


-- @@ L86-86 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]


-- @@ L88-89 verbatim
/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceTranslation : MeasurableSpace E := borel E

-- @@ L90-90 verbatim
local instance instBorelSpaceTranslation : BorelSpace E := ⟨rfl⟩

-- @@ L91-92 verbatim
local instance instOpensMeasurableSpaceTranslation : OpensMeasurableSpace E := by
  infer_instance

-- @@ L93-94 verbatim
local instance instMeasurableAddTranslation : MeasurableAdd E := by
  infer_instance


-- @@ L96-96 verbatim
variable (μ : Measure E) [μ.IsAddRightInvariant]


-- @@ L98-104 verbatim
/-- Translation on `L²` as a linear isometry, under an additive right-invariant measure. -/
noncomputable def translateL2 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (a : E) :
    (E →₂[μ] F) →ₗᵢ[ℝ] (E →₂[μ] F) := by
  classical
  simpa using
    (MeasureTheory.Lp.compMeasurePreservingₗᵢ (𝕜 := ℝ) (E := F) (p := (2 : ENNReal))
      (μ := μ) (μb := μ) (f := fun x : E => x + a) (MeasureTheory.measurePreserving_add_right μ a))


-- @@ L106-114 verbatim
omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma translateL2_ae_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (a : E)
    (g : E →₂[μ] F) :
    (translateL2 (μ := μ) (F := F) a g : E → F) =ᵐ[μ] fun x => (g : E → F) (x + a) := by
  classical
  -- Reduce to `Lp.coeFn_compMeasurePreserving`.
  exact
    (MeasureTheory.Lp.coeFn_compMeasurePreserving (g := (g : MeasureTheory.Lp F (2 : ENNReal) μ))
      (hf := MeasureTheory.measurePreserving_add_right μ a))


-- @@ L116-116 verbatim
variable [IsFiniteMeasureOnCompacts μ]


-- @@ L118-141 verbatim
omit [CompleteSpace E] in
lemma translateL2_toL2 (a : E) (f : ↥(C1c (E := E))) :
    translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) =
      toL2 (μ := μ) (E := E) (translateC1c (E := E) a f) := by
  apply Lp.ext
  have h₁ :
      (translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) : E → ℝ) =ᵐ[μ]
        fun x => f.1 (x + a) := by
    have hf : (toL2 (μ := μ) (E := E) f : E → ℝ) =ᵐ[μ] f.1 :=
      (memLp_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
    have hf' :
        (fun x => (toL2 (μ := μ) (E := E) f : E → ℝ) (x + a)) =ᵐ[μ] fun x => f.1 (x + a) := by
      -- Move the a.e. equality through a measure-preserving map.
      exact
        (Measure.QuasiMeasurePreserving.ae_eq_comp
          (MeasureTheory.measurePreserving_add_right μ a).quasiMeasurePreserving hf)
    exact (translateL2_ae_eq (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f)).trans hf'
  have h₂ :
      (toL2 (μ := μ) (E := E) (translateC1c (E := E) a f) : E → ℝ) =ᵐ[μ]
        fun x => f.1 (x + a) := by
    -- `toL2` agrees a.e. with the underlying translated function.
    exact
      (memLp_of_mem_C1c (μ := μ) (E := E) (translateC1c (E := E) a f).2).coeFn_toLp
  exact h₁.trans h₂.symm


-- @@ L143-173 verbatim
lemma translateL2_toL2Grad (a : E) (f : ↥(C1c (E := E))) :
    translateL2 (μ := μ) (F := E) a (toL2Grad (μ := μ) (E := E) f) =
      toL2Grad (μ := μ) (E := E) (translateC1c (E := E) a f) := by
  apply Lp.ext
  have h₁ :
      (translateL2 (μ := μ) (F := E) a (toL2Grad (μ := μ) (E := E) f) : E → E) =ᵐ[μ]
        fun x => grad (E := E) f.1 (x + a) := by
    have hf :
        (toL2Grad (μ := μ) (E := E) f : E → E) =ᵐ[μ] grad (E := E) f.1 :=
      (memLp_grad_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
    have hf' :
        (fun x => (toL2Grad (μ := μ) (E := E) f : E → E) (x + a)) =ᵐ[μ]
          fun x => grad (E := E) f.1 (x + a) := by
      exact
        (Measure.QuasiMeasurePreserving.ae_eq_comp
          (MeasureTheory.measurePreserving_add_right μ a).quasiMeasurePreserving hf)
    exact
      (translateL2_ae_eq (μ := μ) (F := E) a (toL2Grad (μ := μ) (E := E) f)).trans hf'
  have h₂ :
      (toL2Grad (μ := μ) (E := E) (translateC1c (E := E) a f) : E → E) =ᵐ[μ]
        fun x => grad (E := E) f.1 (x + a) := by
    have hTo :
        (toL2Grad (μ := μ) (E := E) (translateC1c (E := E) a f) : E → E) =ᵐ[μ]
          grad (E := E) (translate (E := E) a f.1) :=
      (memLp_grad_of_mem_C1c (μ := μ) (E := E) (translateC1c (E := E) a f).2).coeFn_toLp
    have hGrad :
        grad (E := E) (translate (E := E) a f.1) = fun x => grad (E := E) f.1 (x + a) := by
      funext x
      simpa [translate] using grad_translate (E := E) a f.1 x
    exact hTo.trans (by simp [hGrad])
  exact h₁.trans h₂.symm


-- @@ L175-175 verbatim
end Measure


-- @@ L177-177 verbatim
end Euclidean

-- @@ L178-178 verbatim
end Sobolev

-- @@ L179-179 verbatim
end FunctionalSpaces

-- @@ L180-180 verbatim
end Analysis

-- @@ L181-181 verbatim
end RellichKondrachov
