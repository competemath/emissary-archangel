/-
Copyright (c) 2026 Rémy Degenne, Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
module

public import Mathlib.MeasureTheory.SetSemiring


-- @@ L10-16 verbatim
/-! # Semirings of sets

A semi-ring of sets `C` is a family of sets containing `∅`, stable by intersection and such that
for all `s, t ∈ C`, `t \ s` is equal to a disjoint union of finitely many sets in `C`.

THIS FILE IS NOT USED FOR THE MAIN RESULT
-/


-- @@ L18-18 verbatim
@[expose] public section



-- @@ L21-21 verbatim
variable {α : Type*} {C : Set (Set α)} {s t : Set α} {J : Finset (Set α)}


-- @@ L23-23 verbatim
open Finset Set


-- @@ L25-25 verbatim
namespace MeasureTheory


-- @@ L27-31 verbatim
/-- A field of sets is a family of sets which is stable under union, difference, and contains
the empty set and the whole space.
-/
structure IsSetField (C : Set (Set α)) : Prop extends IsSetRing C where
  univ_mem : Set.univ ∈ C


-- @@ L33-33 verbatim
namespace IsSetField


-- @@ L35-36 verbatim
theorem inter_mem (hC : IsSetField C) (hs : s ∈ C) (ht : t ∈ C) : s ∩ t ∈ C :=
  hC.toIsSetRing.inter_mem hs ht


-- @@ L38-39 verbatim
theorem compl_mem (hC : IsSetField C) (hs : s ∈ C) : sᶜ ∈ C := by
  rw [compl_eq_univ_sdiff]; exact hC.sdiff_mem hC.univ_mem hs


-- @@ L41-42 verbatim
theorem toIsSetSemiring (hC : IsSetField C) : IsSetSemiring C :=
  hC.toIsSetRing.isSetSemiring


-- @@ L44-45 verbatim
theorem iUnion_le_mem (hC : IsSetField C) {s : ℕ → Set α} (hs : ∀ n, s n ∈ C) (n : ℕ) :
    (⋃ i ≤ n, s i) ∈ C := hC.toIsSetRing.iUnion_le_mem hs n


-- @@ L47-48 verbatim
theorem iInter_le_mem (hC : IsSetField C) {s : ℕ → Set α} (hs : ∀ n, s n ∈ C) (n : ℕ) :
    (⋂ i ≤ n, s i) ∈ C := hC.toIsSetRing.iInter_le_mem hs n


-- @@ L50-51 verbatim
theorem partialSups_mem (hC : IsSetField C) {s : ℕ → Set α} (hs : ∀ n, s n ∈ C) (n : ℕ) :
    partialSups s n ∈ C := hC.toIsSetRing.partialSups_mem hs n


-- @@ L53-54 verbatim
theorem disjointed_mem (hC : IsSetField C) {s : ℕ → Set α} (hs : ∀ n, s n ∈ C) (n : ℕ) :
    disjointed s n ∈ C := hC.toIsSetRing.disjointed_mem hs n


-- @@ L56-56 verbatim
end IsSetField


-- @@ L58-58 verbatim
end MeasureTheory
