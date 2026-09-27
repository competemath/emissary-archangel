/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.Axioms
public import LeanPool.Incompleteness.Foundation.Modal.Substitution


-- @@ L11-11 verbatim
/-! # Basic -/


-- @@ L13-13 verbatim
@[expose] public section



-- @@ L16-16 verbatim
namespace LO

-- @@ L17-17 verbatim
namespace Modal


-- @@ L19-19 verbatim
open Entailment



-- @@ L22-22 verbatim
namespace Kripke



-- @@ L25-31 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
structure Frame where
  /-- Imported declaration from the Incompleteness formalization. -/
  World : Type
  /-- Imported declaration from the Incompleteness formalization. -/
  Rel : Rel World World
  [world_nonempty : Nonempty World]


-- @@ L33-33 verbatim
instance : CoeSort Frame (Type) := ⟨Frame.World⟩

-- @@ L34-34 verbatim
instance : CoeFun Frame (fun F => F.World → F.World → Prop) := ⟨Frame.Rel⟩

-- @@ L35-35 verbatim
instance {F : Frame} : Nonempty F.World := F.world_nonempty


-- @@ L37-38 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.Frame.Rel' {F : Frame} (x y : F.World) := F.Rel x y

-- @@ L39-40 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infix:45 " ≺ " => Frame.Rel'


-- @@ L42-43 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev _root_.LO.Modal.Kripke.Frame.RelItr' {F : Frame} (n : ℕ) := F.Rel.iterate n

-- @@ L44-45 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation x:45 " ≺^[" n "] " y:46 => Frame.RelItr' n x y



-- @@ L48-49 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev FrameClass := Set Frame


-- @@ L51-52 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.FrameClass.nonempty (C : FrameClass) := ∃ F, F ∈ C




-- @@ L56-57 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev Valuation (F : Frame) := F.World → ℕ → Prop


-- @@ L59-62 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
structure Model extends Frame where
  /-- Imported declaration from the Incompleteness formalization. -/
  Val : Valuation toFrame

-- @@ L63-63 verbatim
instance : CoeFun (Model) (fun M => M.World → ℕ → Prop) := ⟨fun m => m.Val⟩


-- @@ L65-65 verbatim
end Kripke



-- @@ L68-68 verbatim
namespace Formula

-- @@ L69-69 verbatim
namespace Kripke


-- @@ L71-76 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def Satisfies (M : Kripke.Model) (x : M.World) : Formula ℕ → Prop
  | atom a => M x a
  | ⊥ => False
  | Arrow.arrow φ ψ => Arrow.arrow (Satisfies M x φ) (Satisfies M x ψ)
  | Box.box φ => ∀ y, Frame.Rel' x y → (Satisfies M y φ)


-- @@ L78-78 verbatim
namespace Satisfies


-- @@ L80-82 verbatim
protected instance semantics {M : Kripke.Model} :
    Semantics (Formula ℕ) (M.World) :=
  ⟨fun x ↦ Formula.Kripke.Satisfies M x⟩


-- @@ L84-84 verbatim
variable {M : Kripke.Model} {x : M.World} {φ ψ : Formula ℕ}


-- @@ L86-86 expanded
@[simp 1100]
protected lemma iff_models : Realize x φ ↔ Kripke.Satisfies M x φ :=
  iff_of_eq rfl


-- @@ L88-88 verbatim
@[simp 1100] lemma atom_def : Kripke.Satisfies M x (atom a) ↔ M x a := by simp [Satisfies];


-- @@ L90-90 expanded
protected lemma bot_def : ¬Realize x ⊥ := by simp [Satisfies];


-- @@ L92-92 expanded
protected lemma imp_def : Realize x (Arrow.arrow φ ψ) ↔ (Realize x φ) → (Realize x ψ) := by tauto;


-- @@ L94-94 expanded
protected lemma imp_def₂ : Realize x (Arrow.arrow φ ψ) ↔ ¬Realize x φ ∨ Realize x ψ := by tauto;


-- @@ L96-96 expanded
protected lemma or_def : Realize x (Vee.vee φ ψ) ↔ Realize x φ ∨ Realize x ψ := by simp [Satisfies];
  tauto;


-- @@ L98-98 expanded
protected lemma and_def : Realize x (Wedge.wedge φ ψ) ↔ Realize x φ ∧ Realize x ψ := by
  simp [Satisfies];


-- @@ L100-100 expanded
protected lemma not_def : Realize x (Tilde.tilde φ) ↔ ¬(Realize x φ) := by simp [Satisfies];


-- @@ L102-102 expanded
protected lemma top_def : Realize x ⊤ := by simp [Satisfies];


-- @@ L104-106 expanded
@[simp 1100]
protected lemma box_def : Kripke.Satisfies M x (Box.box φ) ↔ ∀ y, Frame.Rel' x y → Realize y φ := by
  simp [Satisfies];


-- @@ L108-110 expanded
@[simp 1100]
protected lemma dia_def : Kripke.Satisfies M x (Dia.dia φ) ↔ ∃ y, Frame.Rel' x y ∧ Realize y φ := by
  simp [Satisfies];


-- @@ L112-118 verbatim
protected instance : Semantics.Tarski (M.World) where
  realize_top := fun _ => Satisfies.top_def;
  realize_bot := fun _ => Satisfies.bot_def;
  realize_imp := Satisfies.imp_def;
  realize_not := Satisfies.not_def;
  realize_or := Satisfies.or_def;
  realize_and := Satisfies.and_def;


-- @@ L120-122 expanded
lemma iff_def : Realize x (LogicalConnective.iff φ ψ) ↔ (Realize x φ ↔ Realize x ψ) :=
  by
  simp [Satisfies]
  tauto


-- @@ L124-126 expanded
@[simp 1100]
lemma negneg_def : Kripke.Satisfies M x (Tilde.tilde (Tilde.tilde φ)) ↔ Realize x φ := by
  classical simp [Satisfies]


-- @@ L128-140 expanded
lemma multibox_def : Realize x (multibox n φ) ↔ ∀ {y}, Frame.RelItr' n x y → Realize y φ := by
  induction n generalizing x with
  | zero => simp;
  | succ n ih =>
    constructor;
    · rintro h y ⟨z, Rxz, Rzy⟩;
      replace h : ∀ y, Frame.Rel' x y → Realize y (multibox n φ) :=
        Satisfies.box_def.mp <| by simpa using h;
      exact (ih.mp <| h _ Rxz) Rzy;
    · suffices
        (∀ {y z}, Frame.Rel' x z → Frame.RelItr' n z y → Satisfies M y φ) →
          Realize x (Box.box (multibox n φ))
        by simpa;
      intro h y Rxy; apply ih.mpr; intro z Ryz; exact h Rxy Ryz;


-- @@ L142-154 expanded
lemma multidia_def : Realize x (multidia n φ) ↔ ∃ y, Frame.RelItr' n x y ∧ Realize y φ := by
  induction n generalizing x with
  | zero => simp;
  | succ n ih =>
    constructor;
    · intro h; replace h : Realize x (Dia.dia (multidia n φ)) := by simpa using h;
      obtain ⟨y, Rxy, hv⟩ := Satisfies.dia_def.mp h; obtain ⟨x, Ryx, hx⟩ := ih.mp hv;
      exact ⟨x, ⟨y, Rxy, Ryx⟩, hx⟩;
    · rintro ⟨y, ⟨z, Rxz, Rzy⟩, hy⟩; suffices Realize x (Dia.dia (multidia n φ)) by simpa;
      exact Satisfies.dia_def.mpr ⟨z, Rxz, ih.mpr ⟨y, Rzy, hy⟩⟩;


-- @@ L156-157 expanded
lemma trans (hpq : Realize x (Arrow.arrow φ ψ)) (hqr : Realize x (Arrow.arrow ψ χ)) :
    Realize x (Arrow.arrow φ χ) :=
  Satisfies.imp_def.mpr fun hφ => Satisfies.imp_def.mp hqr (Satisfies.imp_def.mp hpq hφ)


-- @@ L159-159 expanded
lemma mdp (hpq : Realize x (Arrow.arrow φ ψ)) (hp : Realize x φ) : Realize x ψ :=
  Satisfies.imp_def.mp hpq hp


-- @@ L161-161 expanded
lemma diaDual : Realize x (Dia.dia φ) ↔ Realize x (Tilde.tilde (Box.box (Tilde.tilde φ))) := by
  simp [Satisfies];


-- @@ L163-163 expanded
lemma box_dual : Realize x (Box.box φ) ↔ Realize x (Tilde.tilde (Dia.dia (Tilde.tilde φ))) := by
  simp [Satisfies];


-- @@ L165-165 expanded
lemma not_imp : ¬(Realize x (Arrow.arrow φ ψ)) ↔ Realize x (Wedge.wedge φ (Tilde.tilde ψ)) := by
  simp [Satisfies];


-- @@ L167-180 expanded
lemma iff_subst_self {x : F.World} (s) :
    letI U : Kripke.Valuation F := fun w a => Satisfies ⟨F, V⟩ w (Formula.subst s (.atom a));
    Satisfies ⟨F, U⟩ x φ ↔ Satisfies ⟨F, V⟩ x (Formula.subst s φ) :=
  by
  induction φ using Formula.rec' generalizing x with
  | hatom a => simp [Satisfies];
  | hfalsum => simp [Satisfies];
  | hbox φ ih =>
    constructor; · exact fun hbφ y Rxy => ih.mp <| hbφ y Rxy;
    · exact fun hbφ y Rxy => ih.mpr <| hbφ y Rxy;
  | himp φ ψ ihφ ihψ =>
    constructor; · exact fun hφψ hφ => ihψ.mp <| hφψ <| ihφ.mpr hφ;
    · exact fun hφψs hφ => ihψ.mpr <| hφψs <| ihφ.mp hφ;


-- @@ L182-182 verbatim
end Satisfies



-- @@ L185-186 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def ValidOnModel (M : Kripke.Model) (φ : Formula ℕ) :=
  ∀ x : M.World, Realize x φ


-- @@ L188-188 verbatim
namespace ValidOnModel


-- @@ L190-190 verbatim
instance semantics : Semantics (Formula ℕ) (Kripke.Model) := ⟨fun M ↦ Formula.Kripke.ValidOnModel M⟩


-- @@ L192-194 expanded
@[simp]
protected lemma iff_models {M : Kripke.Model} : Realize M f ↔ Kripke.ValidOnModel M f :=
  iff_of_eq rfl


-- @@ L196-196 verbatim
variable {M : Kripke.Model} {φ ψ χ : Formula ℕ}


-- @@ L198-201 expanded
protected lemma bot_def : ¬Realize M ⊥ := by
  intro h
  obtain ⟨x⟩ := M.world_nonempty
  exact Satisfies.bot_def (h x)


-- @@ L203-205 expanded
protected lemma top_def : Realize M ⊤ := by
  intro x
  exact Satisfies.top_def


-- @@ L207-208 verbatim
instance : Semantics.Bot (Kripke.Model) where
  realize_bot := fun _ => ValidOnModel.bot_def;


-- @@ L210-211 verbatim
instance : Semantics.Top (Kripke.Model) where
  realize_top := fun _ => ValidOnModel.top_def;



-- @@ L214-217 expanded
lemma iff_not_exists_world {M : Kripke.Model} : (¬Realize M φ) ↔ (∃ x : M.World, ¬Realize x φ) := by
  apply not_iff_not.mp; push Not; tauto;


-- @@ L219-219 verbatim
alias ⟨exists_world_of_not, not_of_exists_world⟩ := iff_not_exists_world



-- @@ L222-224 expanded
protected lemma mdp (hpq : Realize M (Arrow.arrow φ ψ)) (hp : Realize M φ) : Realize M ψ := by
  intro x; exact (Satisfies.imp_def.mp <| hpq x) (hp x);


-- @@ L226-228 expanded
protected lemma nec (h : Realize M φ) : Realize M (Box.box φ) := by intro x y _; exact h y;


-- @@ L230-230 expanded
protected lemma imply₁ : Realize M (Axioms.Imply₁ φ ψ) := by simp [ValidOnModel]; tauto;


-- @@ L232-232 expanded
protected lemma imply₂ : Realize M (Axioms.Imply₂ φ ψ χ) := by simp [ValidOnModel]; tauto;


-- @@ L234-236 expanded
protected lemma elimContra : Realize M (Axioms.ElimContra φ ψ) := by simp [ValidOnModel, Satisfies];
  tauto;


-- @@ L238-245 expanded
protected lemma axiomK : Realize M (Axioms.K φ ψ) := by intro V; apply Satisfies.imp_def.mpr;
  intro hpq; apply Satisfies.imp_def.mpr; intro hp x Rxy;
  replace hpq := Satisfies.imp_def.mp <| hpq x Rxy; simp_all


-- @@ L247-247 verbatim
end ValidOnModel



-- @@ L250-251 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def ValidOnFrame (F : Kripke.Frame) (φ : Formula ℕ) :=
  ∀ V, Realize (⟨F, V⟩ : Kripke.Model) φ


-- @@ L253-253 verbatim
namespace ValidOnFrame


-- @@ L255-255 verbatim
instance semantics : Semantics (Formula ℕ) (Kripke.Frame) := ⟨fun F ↦ Formula.Kripke.ValidOnFrame F⟩


-- @@ L257-257 verbatim
variable {F : Kripke.Frame}


-- @@ L259-259 expanded
@[simp]
protected lemma models_iff : Realize F φ ↔ Kripke.ValidOnFrame F φ :=
  iff_of_eq rfl


-- @@ L261-261 expanded
lemma models_set_iff : RealizeSet F Φ ↔ ∀ φ ∈ Φ, Realize F φ := by simp [Semantics.realizeSet_iff];


-- @@ L263-263 expanded
protected lemma top_def : Realize F ⊤ := by simp [ValidOnFrame];


-- @@ L265-265 expanded
protected lemma bot_def : ¬Realize F ⊥ := by simp [ValidOnFrame];


-- @@ L267-268 verbatim
instance : Semantics.Top (Kripke.Frame) where
  realize_top _ := ValidOnFrame.top_def;


-- @@ L270-271 verbatim
instance : Semantics.Bot (Kripke.Frame) where
  realize_bot _ := ValidOnFrame.bot_def


-- @@ L273-275 expanded
lemma iff_not_exists_valuation :
    (¬Realize F φ) ↔ (∃ V : Kripke.Valuation F, ¬Realize (⟨F, V⟩ : Kripke.Model) φ) := by
  simp [ValidOnFrame];


-- @@ L277-277 verbatim
alias ⟨exists_valuation_of_not, not_of_exists_valuation⟩ := iff_not_exists_valuation


-- @@ L279-281 expanded
lemma iff_not_exists_valuation_world :
    (¬Realize F φ) ↔
      (∃ V : Kripke.Valuation F, ∃ x : (⟨F, V⟩ : Kripke.Model).World, ¬Satisfies _ x φ) :=
  by simp [ValidOnFrame, ValidOnModel, Semantics.Realize];


-- @@ L283-284 verbatim
alias ⟨exists_valuation_world_of_not, not_of_exists_valuation_world⟩ :=
  iff_not_exists_valuation_world


-- @@ L286-294 expanded
lemma iff_not_exists_model_world :
    (¬Realize F φ) ↔ (∃ M : Kripke.Model, ∃ x : M.World, M.toFrame = F ∧ ¬(Realize x φ)) :=
  by
  constructor;
  · intro h; obtain ⟨V, x, h⟩ := iff_not_exists_valuation_world.mp h; use ⟨F, V⟩, x; tauto;
  · rintro ⟨M, x, rfl, h⟩; exact iff_not_exists_valuation_world.mpr ⟨M.Val, x, h⟩;


-- @@ L296-296 verbatim
alias ⟨exists_model_world_of_not, not_of_exists_model_world⟩ := iff_not_exists_model_world



-- @@ L299-301 expanded
protected lemma mdp (hpq : Realize F (Arrow.arrow φ ψ)) (hp : Realize F φ) : Realize F ψ := by
  intro V x; exact (hpq V x) (hp V x);


-- @@ L303-305 expanded
protected lemma nec (h : Realize F φ) : Realize F (Box.box φ) := by intro V x y _; exact h V y;


-- @@ L307-312 expanded
protected lemma subst (h : Realize F φ) : Realize F (Formula.subst s φ) := by by_contra hC;
  replace hC := iff_not_exists_valuation_world.mp hC; obtain ⟨V, ⟨x, hx⟩⟩ := hC;
  apply Satisfies.iff_subst_self s |>.not.mpr hx;
  exact h (fun w a => Satisfies ⟨F, V⟩ w (Formula.subst s (atom a))) x;


-- @@ L314-316 expanded
protected lemma imply₁ : Realize F (Axioms.Imply₁ φ ψ) := by intro V;
  exact ValidOnModel.imply₁ (M := ⟨F, V⟩);


-- @@ L318-320 expanded
protected lemma imply₂ : Realize F (Axioms.Imply₂ φ ψ χ) := by intro V;
  exact ValidOnModel.imply₂ (M := ⟨F, V⟩);


-- @@ L322-324 expanded
protected lemma elimContra : Realize F (Axioms.ElimContra φ ψ) := by intro V;
  exact ValidOnModel.elimContra (M := ⟨F, V⟩);


-- @@ L326-326 expanded
protected lemma axiomK : Realize F (Axioms.K φ ψ) := by intro V;
  exact ValidOnModel.axiomK (M := ⟨F, V⟩);


-- @@ L328-328 verbatim
end ValidOnFrame



-- @@ L331-332 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def ValidOnFrameClass (C : Kripke.FrameClass) (φ : Formula ℕ) :=
  ∀ {F}, F ∈ C → Realize F φ


-- @@ L334-334 verbatim
namespace ValidOnFrameClass


-- @@ L336-338 verbatim
protected instance semantics :
    Semantics (Formula ℕ) (Kripke.FrameClass) :=
  ⟨fun C ↦ Kripke.ValidOnFrameClass C⟩


-- @@ L340-340 verbatim
variable {C : Kripke.FrameClass}


-- @@ L342-342 expanded
@[simp]
protected lemma models_iff : Realize C φ ↔ Formula.Kripke.ValidOnFrameClass C φ :=
  iff_of_eq rfl


-- @@ L345-345 expanded
protected lemma top_def : Realize C ⊤ := by simp [ValidOnFrameClass];


-- @@ L347-348 verbatim
instance : Semantics.Top (Kripke.FrameClass) where
  realize_top := fun _ => ValidOnFrameClass.top_def


-- @@ L350-350 expanded
protected lemma bot_def (h : Set.Nonempty C) : ¬Realize C ⊥ := by simpa [ValidOnFrameClass];


-- @@ L353-356 expanded
lemma iff_not_exists_frame {C : Kripke.FrameClass} : (¬Realize C φ) ↔ (∃ F ∈ C, ¬Realize F φ) := by
  apply not_iff_not.mp; push Not; tauto;


-- @@ L358-358 verbatim
alias ⟨exists_frame_of_not, not_of_exists_frame⟩ := iff_not_exists_frame


-- @@ L360-364 expanded
lemma iff_not_exists_model {C : Kripke.FrameClass} :
    (¬Realize C φ) ↔ (∃ M : Kripke.Model, M.toFrame ∈ C ∧ ¬Realize M φ) := by apply not_iff_not.mp;
  push Not; tauto;


-- @@ L366-366 verbatim
alias ⟨exists_model_of_not, not_of_exists_model⟩ := iff_not_exists_model



-- @@ L369-373 expanded
lemma iff_not_exists_model_world {C : Kripke.FrameClass} :
    (¬Realize C φ) ↔ (∃ M : Kripke.Model, ∃ x : M.World, M.toFrame ∈ C ∧ ¬(Realize x φ)) := by
  apply not_iff_not.mp; push Not; tauto;


-- @@ L375-375 verbatim
alias ⟨exists_model_world_of_not, not_of_exists_model_world⟩ := iff_not_exists_model_world


-- @@ L377-377 verbatim
end ValidOnFrameClass


-- @@ L379-379 verbatim
end Kripke

-- @@ L380-380 verbatim
end Formula



-- @@ L383-383 verbatim
namespace Kripke


-- @@ L385-385 verbatim
namespace FrameClass


-- @@ L387-389 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class DefinedBy (C : Kripke.FrameClass) (Γ : Set (Formula ℕ)) where
  defines : ∀ F, F ∈ C ↔ (∀ φ ∈ Γ, Realize F φ)


-- @@ L391-393 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class FiniteDefinedBy (C Γ) extends FrameClass.DefinedBy C Γ where
  finite : Set.Finite Γ


-- @@ L395-396 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev DefinedByFormula (C : Kripke.FrameClass) (φ : Formula ℕ) := FrameClass.DefinedBy C {φ}


-- @@ L398-400 expanded
lemma definedByFormula_of_iff_mem_validate (h : ∀ F, F ∈ C ↔ Realize F φ) : DefinedByFormula C φ :=
  by constructor; simpa;


-- @@ L402-418 verbatim
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


-- @@ L420-423 verbatim
instance definedByFormula_inter
  (C₁ φ₁) [DefinedByFormula C₁ φ₁]
  (C₂ φ₂) [DefinedByFormula C₂ φ₂]
  : DefinedBy (C₁ ∩ C₂) {φ₁, φ₂} := definedBy_inter C₁ {φ₁} C₂ {φ₂}


-- @@ L425-429 verbatim
lemma definedBy_triinter
  (C₁ Γ₁) [DefinedBy C₁ Γ₁]
  (C₂ Γ₂) [DefinedBy C₂ Γ₂]
  (C₃ Γ₃) [DefinedBy C₃ Γ₃]
  : DefinedBy (C₁ ∩ C₂ ∩ C₃) (Γ₁ ∪ Γ₂ ∪ Γ₃) := definedBy_inter (C₁ ∩ C₂) (Γ₁ ∪ Γ₂) C₃ Γ₃


-- @@ L431-437 verbatim
lemma definedByFormula_triinter
  (C₁ φ₁) [DefinedByFormula C₁ φ₁]
  (C₂ φ₂) [DefinedByFormula C₂ φ₂]
  (C₃ φ₃) [DefinedByFormula C₃ φ₃]
  : DefinedBy (C₁ ∩ C₂ ∩ C₃) {φ₁, φ₂, φ₃} := by
  simpa [show ({φ₁, φ₂, φ₃} : Set (Formula ℕ)) = {φ₁} ∪ {φ₂} ∪ {φ₃} by aesop]
  using definedBy_triinter C₁ {φ₁} C₂ {φ₂} C₃ {φ₃}


-- @@ L439-441 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class IsNonempty (C : Kripke.FrameClass) : Prop where
  nonempty : Nonempty C


-- @@ L443-443 verbatim
end FrameClass



-- @@ L446-447 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev AllFrameClass : FrameClass := Set.univ


-- @@ L449-454 verbatim
instance _root_.LO.Modal.Kripke.AllFrameClass.DefinedBy :
    AllFrameClass.DefinedByFormula (Axioms.K (.atom 0) (.atom 1)) :=
  FrameClass.definedByFormula_of_iff_mem_validate <| by
    simp only [Set.mem_univ, true_iff];
    intro F;
    exact Formula.Kripke.ValidOnFrame.axiomK;


-- @@ L456-458 verbatim
instance _root_.LO.Modal.Kripke.AllFrameClass.IsNonempty : AllFrameClass.IsNonempty := by
  use ⟨Unit, fun _ _ => True⟩;
  simp;


-- @@ L460-460 verbatim
namespace FrameClass


-- @@ L462-462 verbatim
variable {C : Kripke.FrameClass}


-- @@ L464-467 verbatim
lemma definedBy_with_axiomK (defines : C.DefinedBy Γ) :
    DefinedBy C (insert (Axioms.K (.atom 0) (.atom 1)) Γ) := by
  convert definedBy_inter AllFrameClass {Axioms.K (.atom 0) (.atom 1)} C Γ <;>
    simp [AllFrameClass, Set.singleton_union];


-- @@ L469-469 verbatim
end FrameClass




-- @@ L473-473 verbatim
end Kripke


-- @@ L475-475 verbatim
end Modal

-- @@ L476-476 verbatim
end LO
