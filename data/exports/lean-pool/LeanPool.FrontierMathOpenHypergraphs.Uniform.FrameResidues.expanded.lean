/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
module

public import LeanPool.FrontierMathOpenHypergraphs.Uniform.FrameDefs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow


-- @@ L16-18 verbatim
/-!
# Residue-gadget validations
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
namespace HypergraphLowerBound


-- @@ L24-26 verbatim
private theorem residueGadget_0_valid :
    (residueGadgets.get ⟨0, by decide⟩).IsValid := by
  exact (residueGadgets.get ⟨0, by decide⟩).checkComplementValid_sound (by decide +kernel)


-- @@ L28-30 verbatim
private theorem residueGadget_1_valid :
    (residueGadgets.get ⟨1, by decide⟩).IsValid := by
  exact (residueGadgets.get ⟨1, by decide⟩).checkComplementValid_sound (by decide +kernel)


-- @@ L32-34 verbatim
private theorem residueGadget_2_valid :
    (residueGadgets.get ⟨2, by decide⟩).IsValid := by
  exact (residueGadgets.get ⟨2, by decide⟩).checkComplementValid_sound (by decide +kernel)


-- @@ L36-38 verbatim
private theorem residueGadget_3_valid :
    (residueGadgets.get ⟨3, by decide⟩).IsValid := by
  exact (residueGadgets.get ⟨3, by decide⟩).checkComplementValid_sound (by decide +kernel)


-- @@ L40-42 verbatim
private theorem residueGadget_4_valid :
    (residueGadgets.get ⟨4, by decide⟩).IsValid := by
  exact (residueGadgets.get ⟨4, by decide⟩).checkComplementValid_sound (by decide +kernel)


-- @@ L44-46 verbatim
private theorem residueGadget_5_valid :
    (residueGadgets.get ⟨5, by decide⟩).IsValid := by
  exact (residueGadgets.get ⟨5, by decide⟩).checkComplementValid_sound (by decide +kernel)


-- @@ L48-50 verbatim
private theorem residueGadget_6_valid :
    (residueGadgets.get ⟨6, by decide⟩).IsValid := by
  exact (residueGadgets.get ⟨6, by decide⟩).checkComplementValid_sound (by decide +kernel)


-- @@ L52-54 verbatim
private theorem residueGadget_7_valid :
    (residueGadgets.get ⟨7, by decide⟩).IsValid := by
  exact (residueGadgets.get ⟨7, by decide⟩).checkComplementValid_sound (by decide +kernel)


-- @@ L56-58 verbatim
private theorem residueGadget_8_valid :
    (residueGadgets.get ⟨8, by decide⟩).IsValid := by
  exact (residueGadgets.get ⟨8, by decide⟩).checkComplementValid_sound (by decide +kernel)


-- @@ L60-62 verbatim
private theorem residueGadget_9_valid :
    (residueGadgets.get ⟨9, by decide⟩).IsValid := by
  exact (residueGadgets.get ⟨9, by decide⟩).checkComplementValid_sound (by decide +kernel)


-- @@ L64-66 verbatim
private theorem residueGadget_10_valid :
    (residueGadgets.get ⟨10, by decide⟩).IsValid := by
  exact (residueGadgets.get ⟨10, by decide⟩).checkComplementValid_sound (by decide +kernel)


-- @@ L68-70 verbatim
private theorem residueGadget_11_valid :
    (residueGadgets.get ⟨11, by decide⟩).IsValid := by
  exact (residueGadgets.get ⟨11, by decide⟩).checkComplementValid_sound (by decide +kernel)


-- @@ L72-88 verbatim
theorem residueGadgets_valid :
    ∀ spec ∈ residueGadgets, spec.IsValid := by
  intro spec hs
  obtain ⟨i, rfl⟩ := List.get_of_mem hs
  fin_cases i
  · exact residueGadget_0_valid
  · exact residueGadget_1_valid
  · exact residueGadget_2_valid
  · exact residueGadget_3_valid
  · exact residueGadget_4_valid
  · exact residueGadget_5_valid
  · exact residueGadget_6_valid
  · exact residueGadget_7_valid
  · exact residueGadget_8_valid
  · exact residueGadget_9_valid
  · exact residueGadget_10_valid
  · exact residueGadget_11_valid



-- @@ L91-91 verbatim
end HypergraphLowerBound
