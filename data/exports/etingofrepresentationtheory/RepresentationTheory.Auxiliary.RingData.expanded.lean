/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Ring.Opposite
import RepresentationTheory.Alignment.Attribute


-- @@ L12-12 verbatim
universe u


-- @@ L14-14 verbatim
namespace RepresentationTheory.Auxiliary.RingData


-- @@ L16-18 verbatim
/-- An auxiliary property of a ring indexed by a natural number. -/
def auxiliaryRingNatProperty (R : Type u) [Ring R] (d : ℕ) : Prop :=
  ∀ (M : ModuleCat.{u} R), CategoryTheory.HasProjectiveDimensionLE M d


-- @@ L20-22 verbatim
/-- An auxiliary extended-natural-valued invariant of a ring. -/
noncomputable def auxiliaryRingENatInvariant (R : Type u) [Ring R] : ℕ∞ :=
  ⨅ (d : ℕ) (_ : auxiliaryRingNatProperty R d), (d : ℕ∞)


-- @@ L24-26 verbatim
/-- A second auxiliary property of a ring indexed by a natural number. -/
abbrev auxiliaryRingNatPropertyAux (R : Type u) [Ring R] (d : ℕ) : Prop :=
  auxiliaryRingNatProperty R d


-- @@ L28-30 verbatim
/-- A second auxiliary extended-natural-valued invariant of a ring. -/
noncomputable abbrev auxiliaryRingENatInvariantAux (R : Type u) [Ring R] : ℕ∞ :=
  auxiliaryRingENatInvariant R


-- @@ L32-34 verbatim
/-- A third auxiliary property of a ring indexed by a natural number. -/
def auxiliaryRingNatPropertyThird (R : Type u) [Ring R] (d : ℕ) : Prop :=
  auxiliaryRingNatProperty Rᵐᵒᵖ d


-- @@ L36-38 verbatim
/-- A third auxiliary extended-natural-valued invariant of a ring. -/
noncomputable def auxiliaryRingENatInvariantThird (R : Type u) [Ring R] : ℕ∞ :=
  auxiliaryRingENatInvariant Rᵐᵒᵖ


-- @@ L40-45 verbatim
/-- The third auxiliary natural-number-indexed ring property is equivalent to the second one for
the opposite ring. -/
@[simp]
theorem auxiliaryRingNatPropertyThird_opposite_iff (R : Type u) [Ring R] (d : ℕ) :
    auxiliaryRingNatPropertyThird R d ↔ auxiliaryRingNatPropertyAux Rᵐᵒᵖ d :=
  Iff.rfl


-- @@ L47-52 verbatim
/-- The third auxiliary extended-natural-valued ring invariant equals the second one for the
opposite ring. -/
@[simp]
theorem auxiliaryRingENatInvariantThird_opposite (R : Type u) [Ring R] :
    auxiliaryRingENatInvariantThird R = auxiliaryRingENatInvariantAux Rᵐᵒᵖ :=
  rfl


-- @@ L54-56 verbatim
end RepresentationTheory.Auxiliary.RingData

-- Recovered exact-module book alignment.

-- @@ L57-57 verbatim
attribute [source_ref "Chapter9/Definition9.4.3" (role := primary)] _root_.RepresentationTheory.Auxiliary.RingData.auxiliaryRingENatInvariant

-- @@ L58-58 verbatim
attribute [source_ref "Chapter9/Definition9.4.3" (role := primary)] _root_.RepresentationTheory.Auxiliary.RingData.auxiliaryRingENatInvariantAux

-- @@ L59-59 verbatim
attribute [source_ref "Chapter9/Definition9.4.3" (role := primary)] _root_.RepresentationTheory.Auxiliary.RingData.auxiliaryRingENatInvariantThird

-- @@ L60-60 verbatim
attribute [source_ref "Chapter9/Definition9.4.3" (role := supporting)] _root_.RepresentationTheory.Auxiliary.RingData.auxiliaryRingENatInvariantThird_opposite

-- @@ L61-61 verbatim
attribute [source_ref "Chapter9/Definition9.4.3" (role := supporting)] _root_.RepresentationTheory.Auxiliary.RingData.auxiliaryRingNatProperty

-- @@ L62-62 verbatim
attribute [source_ref "Chapter9/Definition9.4.3" (role := supporting)] _root_.RepresentationTheory.Auxiliary.RingData.auxiliaryRingNatPropertyAux

-- @@ L63-63 verbatim
attribute [source_ref "Chapter9/Definition9.4.3" (role := supporting)] _root_.RepresentationTheory.Auxiliary.RingData.auxiliaryRingNatPropertyThird

-- @@ L64-64 verbatim
attribute [source_ref "Chapter9/Definition9.4.3" (role := supporting)] _root_.RepresentationTheory.Auxiliary.RingData.auxiliaryRingNatPropertyThird_opposite_iff
