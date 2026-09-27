/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.IntProp.Hilbert.WellKnown
public import LeanPool.Incompleteness.Foundation.IntProp.Kripke.Basic
import LeanPool.Incompleteness.Foundation.IntProp.Kripke.Hilbert.Cl.Basic


-- @@ L12-12 verbatim
/-! # Classical -/


-- @@ L14-14 verbatim
@[expose] public section



-- @@ L17-17 verbatim
namespace LO

-- @@ L18-18 verbatim
namespace IntProp


-- @@ L20-20 verbatim
open Kripke

-- @@ L21-21 verbatim
open Formula.Kripke



-- @@ L24-24 verbatim
namespace Kripke


-- @@ L26-27 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev ClassicalValuation := ℕ → Prop


-- @@ L29-29 verbatim
end Kripke



-- @@ L32-32 verbatim
namespace Formula

-- @@ L33-33 verbatim
namespace Kripke


-- @@ L35-35 verbatim
open IntProp.Kripke


-- @@ L37-40 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev ClassicalSatisfies (V : ClassicalValuation) (φ : Formula ℕ) :
    Prop :=
  Satisfies (⟨pointFrame, ⟨fun _ => V, by tauto⟩⟩) () φ


-- @@ L42-42 verbatim
namespace ClassicalSatisfies


-- @@ L44-44 verbatim
instance : Semantics (Formula ℕ) (ClassicalValuation) := ⟨ClassicalSatisfies⟩


-- @@ L46-46 verbatim
variable {V : ClassicalValuation} {a : ℕ}


-- @@ L48-48 expanded
@[simp]
lemma atom_def : Realize V (atom a) ↔ V a := by simp only [Semantics.Realize, Satisfies]


-- @@ L50-56 verbatim
instance : Semantics.Tarski (ClassicalValuation) where
  realize_top := by simp [Semantics.Realize, ClassicalSatisfies, Satisfies];
  realize_bot := by simp [Semantics.Realize, ClassicalSatisfies, Satisfies];
  realize_or  := by simp [Semantics.Realize, ClassicalSatisfies, Satisfies];
  realize_and := by simp [Semantics.Realize, ClassicalSatisfies, Satisfies];
  realize_imp := by simp [Semantics.Realize]; tauto;
  realize_not := by simp [Semantics.Realize]; tauto;


-- @@ L58-58 verbatim
end ClassicalSatisfies


-- @@ L60-60 verbatim
end Kripke

-- @@ L61-61 verbatim
end Formula



-- @@ L64-64 verbatim
namespace Hilbert

-- @@ L65-65 verbatim
namespace Cl


-- @@ L67-70 expanded
lemma classical_sound : Provable (Hilbert.Cl) φ → (∀ V : ClassicalValuation, Realize V φ) := by
  intro h V; apply Hilbert.Cl.Kripke.sound.sound h Kripke.pointFrame; simp [Euclidean];


-- @@ L72-76 expanded
lemma unprovable_of_exists_classicalValuation :
    (∃ V : ClassicalValuation, ¬(Realize V φ)) → Unprovable (Hilbert.Cl) φ := by contrapose;
  simp only [not_exists, not_not]; apply classical_sound;


-- @@ L78-78 verbatim
end Cl

-- @@ L79-79 verbatim
end Hilbert



-- @@ L82-82 verbatim
end IntProp

-- @@ L83-83 verbatim
end LO
