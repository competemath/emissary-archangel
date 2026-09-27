/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.Kripke.Basic


-- @@ L10-10 verbatim
/-! # FiniteFrame -/


-- @@ L12-12 verbatim
@[expose] public section



-- @@ L15-15 verbatim
namespace LO

-- @@ L16-16 verbatim
namespace Modal


-- @@ L18-18 verbatim
namespace Kripke


-- @@ L20-22 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
structure FiniteFrame extends Frame where
  [world_finite : Finite toFrame.World]


-- @@ L24-24 verbatim
instance {F : FiniteFrame} : Finite F.World := F.world_finite



-- @@ L27-29 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Modal.Kripke.Frame.toFinite (F : Frame) [Finite F.World] : FiniteFrame where
  toFrame := F



-- @@ L32-33 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev FiniteFrameClass := Set FiniteFrame


-- @@ L35-37 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Modal.Kripke.FrameClass.restrictFinite (C : FrameClass) : FiniteFrameClass := { F :
    FiniteFrame | F.toFrame ∈ C }


-- @@ L39-42 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Modal.Kripke.FiniteFrameClass.toFrameClass (C : FiniteFrameClass) :
    FrameClass :=
  C.image (·.toFrame)


-- @@ L44-44 verbatim
instance : Coe (FiniteFrameClass) (FrameClass) := ⟨FiniteFrameClass.toFrameClass⟩



-- @@ L47-50 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev reflexivePointFrame : FiniteFrame where
  World := Unit
  Rel := fun _ _ => True


-- @@ L52-55 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev irreflexivePointFrame : FiniteFrame where
  World := Unit
  Rel := fun _ _ => False


-- @@ L57-57 verbatim
end Kripke



-- @@ L60-60 verbatim
namespace Formula

-- @@ L61-61 verbatim
namespace Kripke


-- @@ L63-64 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def ValidOnFiniteFrame (F : Kripke.FiniteFrame) (φ : Formula ℕ) :=
  Realize F.toFrame φ


-- @@ L66-66 verbatim
namespace ValidOnFiniteFrame


-- @@ L68-70 verbatim
instance semantics :
    Semantics (Formula ℕ) (Kripke.FiniteFrame) :=
  ⟨fun F ↦ Formula.Kripke.ValidOnFiniteFrame F⟩


-- @@ L72-72 verbatim
variable {F : Kripke.FiniteFrame}


-- @@ L74-74 expanded
@[simp]
protected lemma models_iff : Realize F φ ↔ Kripke.ValidOnFiniteFrame F φ :=
  iff_of_eq rfl


-- @@ L76-76 expanded
lemma models_set_iff : RealizeSet F Φ ↔ ∀ φ ∈ Φ, Realize F φ := by simp [Semantics.realizeSet_iff];


-- @@ L78-78 expanded
protected lemma top_def : Realize F ⊤ := by simp [ValidOnFiniteFrame];


-- @@ L80-80 expanded
protected lemma bot_def : ¬Realize F ⊥ := by simp [ValidOnFiniteFrame];


-- @@ L82-83 verbatim
instance : Semantics.Top (Kripke.FiniteFrame) where
  realize_top _ := ValidOnFrame.top_def;


-- @@ L85-86 verbatim
instance : Semantics.Bot (Kripke.FiniteFrame) where
  realize_bot _ := ValidOnFrame.bot_def


-- @@ L88-90 expanded
lemma iff_not_exists_valuation :
    (¬Realize F φ) ↔
      (∃ V : Kripke.Valuation F.toFrame, ¬Realize (⟨F.toFrame, V⟩ : Kripke.Model) φ) :=
  ValidOnFrame.iff_not_exists_valuation


-- @@ L92-92 verbatim
alias ⟨exists_valuation_of_not, not_of_exists_valuation⟩ := iff_not_exists_valuation


-- @@ L94-97 expanded
lemma iff_not_exists_valuation_world :
    (¬Realize F φ) ↔
      (∃ V : Kripke.Valuation F.toFrame,
        ∃ x : (⟨F.toFrame, V⟩ : Kripke.Model).World, ¬Satisfies _ x φ) :=
  ValidOnFrame.iff_not_exists_valuation_world


-- @@ L99-100 verbatim
alias ⟨exists_valuation_world_of_not, not_of_exists_valuation_world⟩ :=
  iff_not_exists_valuation_world


-- @@ L102-102 verbatim
end ValidOnFiniteFrame



-- @@ L105-106 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def ValidOnFiniteFrameClass (C : Kripke.FiniteFrameClass) (φ : Formula ℕ) :=
  Realize C.toFrameClass φ


-- @@ L108-108 verbatim
namespace ValidOnFiniteFrameClass


-- @@ L110-112 verbatim
protected instance semantics :
    Semantics (Formula ℕ) (Kripke.FiniteFrameClass) :=
  ⟨fun C ↦ Kripke.ValidOnFrameClass C⟩


-- @@ L114-114 verbatim
variable {C : Kripke.FiniteFrameClass}


-- @@ L116-116 expanded
@[simp]
protected lemma models_iff : Realize C φ ↔ Formula.Kripke.ValidOnFrameClass C φ :=
  iff_of_eq rfl


-- @@ L118-121 expanded
lemma iff_not_exists_frame : (¬Realize C φ) ↔ (∃ F ∈ C, ¬Realize F φ) := by
  have h := ValidOnFrameClass.iff_not_exists_frame (φ := φ) (C := C.toFrameClass);
  rw [show (¬Realize C φ) = (¬Realize C.toFrameClass φ) from rfl, h];
  simp [Kripke.FiniteFrameClass.toFrameClass, ValidOnFiniteFrame];


-- @@ L123-123 verbatim
alias ⟨exists_frame_of_not, not_of_exists_frame⟩ := iff_not_exists_frame


-- @@ L125-125 verbatim
end ValidOnFiniteFrameClass


-- @@ L127-127 verbatim
end Kripke

-- @@ L128-128 verbatim
end Formula




-- @@ L132-132 verbatim
namespace Kripke


-- @@ L134-134 verbatim
namespace FiniteFrameClass


-- @@ L136-138 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class DefinedBy (C : Kripke.FiniteFrameClass) (Γ : Set (Formula ℕ)) where
  defines : ∀ F, F ∈ C ↔ (∀ φ ∈ Γ, Realize F φ)


-- @@ L140-142 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class FiniteDefinedBy (C Γ) extends FiniteFrameClass.DefinedBy C Γ where
  finite : Set.Finite Γ


-- @@ L144-145 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev DefinedByFormula (C) (φ : Formula ℕ) := FiniteFrameClass.DefinedBy C {φ}


-- @@ L147-149 expanded
lemma definedByFormula_of_iff_mem_validate (h : ∀ F, F ∈ C ↔ Realize F φ) : DefinedByFormula C φ :=
  by constructor; simpa;


-- @@ L151-167 verbatim
instance definedBy_inter
  (C₁ Γ₁) [h₁ : DefinedBy C₁ Γ₁]
  (C₂ Γ₂) [h₂ : DefinedBy C₂ Γ₂]
  : DefinedBy (C₁ ∩ C₂) (Γ₁ ∪ Γ₂) := ⟨by
  rintro F;
  constructor
  · rintro ⟨hF₁, hF₂⟩;
    rintro φ (hφ₁ | hφ₂);
    · exact h₁.defines F |>.mp hF₁ _ hφ₁;
    · exact h₂.defines F |>.mp hF₂ _ hφ₂;
  · intro h;
    constructor;
    · apply h₁.defines F |>.mpr;
      simp_all
    · apply h₂.defines F |>.mpr;
      simp_all
⟩


-- @@ L169-171 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class IsNonempty (C : Kripke.FiniteFrameClass) where
  nonempty : Nonempty C


-- @@ L173-173 verbatim
end FiniteFrameClass



-- @@ L176-177 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev AllFiniteFrameClass : FiniteFrameClass := Set.univ


-- @@ L179-184 verbatim
instance _root_.LO.Modal.Kripke.AllFiniteFrameClass.DefinedBy :
    AllFiniteFrameClass.DefinedByFormula (Axioms.K (.atom 0) (.atom 1)) :=
  FiniteFrameClass.definedByFormula_of_iff_mem_validate <| by
    simp only [Set.mem_univ, true_iff];
    intro F;
    exact Formula.Kripke.ValidOnFrame.axiomK;


-- @@ L186-189 verbatim
instance _root_.LO.Modal.Kripke.AllFiniteFrameClass.IsNonempty :
    AllFiniteFrameClass.IsNonempty := by
  use ⟨Unit, fun _ _ => True⟩;
  simp;



-- @@ L192-192 verbatim
namespace FiniteFrameClass


-- @@ L194-194 verbatim
variable {C : Kripke.FiniteFrameClass}


-- @@ L196-200 verbatim
lemma definedBy_with_axiomK (defines : C.DefinedBy Γ) :
    DefinedBy C (insert (Axioms.K (.atom 0) (.atom 1)) Γ) := by
  convert FiniteFrameClass.definedBy_inter AllFiniteFrameClass
      {Axioms.K (.atom 0) (.atom 1)} C Γ <;>
    simp [AllFiniteFrameClass, Set.singleton_union];


-- @@ L202-202 verbatim
end FiniteFrameClass


-- @@ L204-204 verbatim
end Kripke


-- @@ L206-206 verbatim
end Modal

-- @@ L207-207 verbatim
end LO
