/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal


-- @@ L10-14 verbatim
/-!
# LeanPool.QuasiBorelSpaces.MeasureTheory.Pack

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.MeasureTheory.Pack`.
-/


-- @@ L16-16 verbatim
@[expose] public section



-- @@ L19-19 verbatim
namespace MeasureTheory


-- @@ L21-21 verbatim
variable {A : Type*} [MeasurableSpace A] [StandardBorelSpace A]


-- @@ L23-28 verbatim
/-- Packs a natural number and a real number into a single real number. -/
noncomputable def pack : A → ℝ :=
  open Classical in
  if h : Countable A
  then MeasureTheory.embeddingReal _
  else PolishSpace.measurableEquivOfNotCountable h not_countable


-- @@ L30-35 verbatim
/-- Unpacks a natural number and a real number from a single real number. -/
noncomputable def unpack [Nonempty A] : ℝ → A :=
  open Classical in
  if h : Countable A
  then (MeasureTheory.measurableEmbedding_embeddingReal _).invFun
  else (PolishSpace.measurableEquivOfNotCountable h not_countable).symm


-- @@ L37-43 verbatim
@[simp]
lemma unpack_pack [Nonempty A] (x : A) : unpack (pack x) = x := by
  simp only [unpack, pack]
  by_cases h : Countable A
  · simp only [h, ↓reduceDIte]
    apply MeasurableEmbedding.leftInverse_invFun
  · simp only [h, ↓reduceDIte, MeasurableEquiv.symm_apply_apply]


-- @@ L45-47 verbatim
@[simp]
lemma pack_unpack [Nonempty A] (h : ¬Countable A) (x : ℝ) : pack (unpack (A := A) x) = x :=by
  simp only [pack, h, ↓reduceDIte, unpack, MeasurableEquiv.apply_symm_apply]


-- @@ L49-56 verbatim
@[simp, fun_prop]
lemma measurable_pack : Measurable (pack (A := A)) := by
  unfold pack
  by_cases h : Countable A
  · simp only [h, ↓reduceDIte]
    fun_prop
  · simp only [h, ↓reduceDIte]
    fun_prop


-- @@ L58-65 verbatim
@[simp, fun_prop]
lemma measurable_unpack [Nonempty A] : Measurable (unpack (A := A)) := by
  unfold unpack
  by_cases h : Countable A
  · simp only [h, ↓reduceDIte]
    fun_prop
  · simp only [h, ↓reduceDIte]
    fun_prop


-- @@ L67-67 verbatim
end MeasureTheory
