/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.RingTheory.Length
import RepresentationTheory.Alignment.Attribute


-- @@ L10-10 verbatim
/-! # Lengths of composition series -/


-- @@ L12-12 verbatim
open Order


-- @@ L14-14 verbatim
namespace RepresentationTheory.Module.CompositionSeriesLength


-- @@ L16-16 verbatim
variable (A : Type*) (V : Type*) [Ring A] [AddCommGroup V] [Module A V]


-- @@ L18-33 verbatim
/-- The length of a composition series running from the bottom submodule to the top submodule is
greatest among the lengths of composition series. -/
@[source_ref "Chapter3/Discussion_after_Theorem3.7.1" (role := supporting)]
theorem compositionSeries_length_isGreatest
    (s : CompositionSeries (Submodule A V)) (hbot : s.head = ⊥) (htop : s.last = ⊤) :
    IsGreatest (Set.range fun l : LTSeries (Submodule A V) => (l.length : ℕ∞))
      (s.length : ℕ∞) := by
  constructor
  · refine ⟨s.map ⟨id, fun h => h.1⟩, ?_⟩
    simp only [RelSeries.map_length]
  · rintro _ ⟨l, rfl⟩
    have hkrull : (l.length : ℕ∞) ≤ Module.length A V := by
      have h1 := LTSeries.length_le_krullDim l
      rw [← Module.coe_length] at h1
      exact_mod_cast h1
    rwa [Module.length_compositionSeries s hbot htop]


-- @@ L35-35 verbatim
end RepresentationTheory.Module.CompositionSeriesLength
