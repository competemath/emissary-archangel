/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Vorspiel.BinaryRelations
public import LeanPool.Incompleteness.Foundation.IntProp.Substitution
public import LeanPool.Incompleteness.Foundation.Logic.Axioms
public import LeanPool.Incompleteness.Foundation.Logic.Semantics
import Mathlib.Tactic.Bound.Init


-- @@ L14-14 verbatim
/-! # Basic -/


-- @@ L16-16 verbatim
@[expose] public section



-- @@ L19-19 verbatim
namespace LO

-- @@ L20-20 verbatim
namespace IntProp




-- @@ L24-24 verbatim
namespace Kripke


-- @@ L26-34 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
structure Frame where
  /-- Imported declaration from the Incompleteness formalization. -/
  World : Type
  [world_nonempty : Nonempty World]
  /-- Imported declaration from the Incompleteness formalization. -/
  Rel : Rel World World
  rel_refl : Std.Refl Rel
  rel_trans : IsTrans World Rel


-- @@ L36-36 verbatim
instance : CoeSort Frame (Type) := ⟨Frame.World⟩

-- @@ L37-37 verbatim
instance : CoeFun Frame (fun F => F.World → F.World → Prop) := ⟨Frame.Rel⟩

-- @@ L38-39 verbatim
instance {F : Frame} : Nonempty F.World := F.world_nonempty
-- instance {F : Frame} : IsPartialOrder _ F.Rel := F.rel_po


-- @@ L41-42 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.IntProp.Kripke.Frame.Rel' {F : Frame} (x y : F.World) := F.Rel x y

-- @@ L43-44 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infix:45 " ≺ " => Frame.Rel'


-- @@ L46-46 verbatim
namespace Frame


-- @@ L48-48 verbatim
variable {F : Frame} {x y z : F.World}


-- @@ L50-50 expanded
@[refl, simp]
lemma rel_refl' : Frame.Rel' x x :=
  F.rel_refl.refl x


-- @@ L52-53 expanded
@[trans]
lemma rel_trans' : Frame.Rel' x y → Frame.Rel' y z → Frame.Rel' x z :=
  F.rel_trans.trans x y z


-- @@ L55-55 verbatim
end Frame



-- @@ L58-63 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev pointFrame : Frame where
  World := Unit
  Rel := fun _ _ => True
  rel_refl := ⟨fun _ => trivial⟩
  rel_trans := ⟨fun _ _ _ _ _ => trivial⟩



-- @@ L66-67 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev FrameClass := Set (Frame)



-- @@ L70-74 expanded
/-- Imported declaration from the Incompleteness formalization. -/
structure Valuation (F : Frame) where
  /-- Imported declaration from the Incompleteness formalization. -/
  Val : F.World → ℕ → Prop
  hereditary : ∀ {w₁ w₂ : F.World}, (Frame.Rel' w₁ w₂) → ∀ {a}, (Val w₁ a) → (Val w₂ a)


-- @@ L75-75 verbatim
instance {F : Frame} : CoeFun (Valuation F) (fun _ => F.World → ℕ → Prop) := ⟨Valuation.Val⟩


-- @@ L77-80 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
structure Model extends Frame where
  /-- Imported declaration from the Incompleteness formalization. -/
  Val : Valuation toFrame

-- @@ L81-81 verbatim
instance : CoeFun (Model) (fun M => M.World → ℕ → Prop) := ⟨fun m => m.Val⟩


-- @@ L83-83 verbatim
end Kripke



-- @@ L86-86 verbatim
open Kripke



-- @@ L89-89 verbatim
open Formula


-- @@ L91-91 verbatim
namespace Formula

-- @@ L92-92 verbatim
namespace Kripke


-- @@ L94-100 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def Satisfies (M : Kripke.Model) (w : M.World) : Formula ℕ → Prop
  | atom a => M w a
  | ⊥ => False
  | Wedge.wedge φ ψ => Satisfies M w φ ∧ Satisfies M w ψ
  | Vee.vee φ ψ => Satisfies M w φ ∨ Satisfies M w ψ
  | Arrow.arrow φ ψ => ∀ {w' : M.World}, (Frame.Rel' w w') → (Satisfies M w' φ → Satisfies M w' ψ)


-- @@ L102-102 verbatim
namespace Satisfies


-- @@ L104-105 verbatim
instance semantics (M : Kripke.Model) : Semantics (Formula ℕ) (M.World) :=
  ⟨fun w ↦ Formula.Kripke.Satisfies M w⟩


-- @@ L107-107 verbatim
variable {M : Kripke.Model} {w w' : M.World} {a : ℕ} {φ ψ χ : Formula ℕ}


-- @@ L109-109 expanded
@[simp 1100]
protected lemma iff_models : Realize w φ ↔ Formula.Kripke.Satisfies M w φ :=
  iff_of_eq rfl


-- @@ L111-111 verbatim
@[simp 1100] lemma atom_def : Formula.Kripke.Satisfies M w (atom a) ↔ M w a := by simp [Satisfies];


-- @@ L113-113 verbatim
@[simp 1100] lemma top_def : Formula.Kripke.Satisfies M w ⊤ ↔ True := by simp [Satisfies];


-- @@ L115-115 verbatim
@[simp 1100] lemma bot_def : Formula.Kripke.Satisfies M w ⊥ ↔ False := by simp [Satisfies];


-- @@ L117-119 expanded
@[simp 1100]
lemma and_def : Formula.Kripke.Satisfies M w (Wedge.wedge φ ψ) ↔ Realize w φ ∧ Realize w ψ := by
  simp [Satisfies];


-- @@ L121-123 expanded
@[simp 1100]
lemma or_def : Formula.Kripke.Satisfies M w (Vee.vee φ ψ) ↔ Realize w φ ∨ Realize w ψ := by
  simp [Satisfies];


-- @@ L125-127 expanded
@[simp 1100]
lemma imp_def :
    Formula.Kripke.Satisfies M w (Arrow.arrow φ ψ) ↔
      ∀ {w' : M.World}, (Frame.Rel' w w') → (Realize w' φ → Realize w' ψ) :=
  by simp [Satisfies, imp_iff_not_or];


-- @@ L129-131 expanded
@[simp 1100]
lemma neg_def :
    Formula.Kripke.Satisfies M w (Tilde.tilde φ) ↔
      ∀ {w' : M.World}, (Frame.Rel' w w') → ¬(Realize w' φ) :=
  by simp [Satisfies];


-- @@ L133-134 verbatim
instance : Semantics.Top M.World where
  realize_top := by simp [Satisfies];


-- @@ L136-137 verbatim
instance : Semantics.Bot M.World where
  realize_bot := by simp [Satisfies];


-- @@ L139-140 verbatim
instance : Semantics.And M.World where
  realize_and := by simp [Satisfies];


-- @@ L142-143 verbatim
instance : Semantics.Or M.World where
  realize_or := by simp [Satisfies];


-- @@ L145-153 expanded
lemma formula_hereditary (hw : Frame.Rel' w w') : Realize w φ → Realize w' φ := by
  induction φ using Formula.rec' with
  | hatom => apply M.Val.hereditary hw;
  | himp => intro hpq v hv; exact hpq <| M.rel_trans.trans _ _ _ hw hv;
  | hor => simp_all [Satisfies]; tauto;
  | _ => simp_all [Satisfies];


-- @@ L155-155 expanded
lemma negEquiv : Realize w (Tilde.tilde φ) ↔ Realize w (Arrow.arrow φ ⊥) := by simp_all [Satisfies];


-- @@ L157-189 expanded
lemma iff_subst_self {F : Frame} {V : Valuation F} {x : F.World} (s) :
    letI U : Kripke.Valuation F :=
      ⟨fun w a => Satisfies ⟨F, V⟩ w (Formula.subst s (.atom a)), fun {_ _} Rwv {_} =>
        formula_hereditary Rwv⟩;
    Satisfies ⟨F, U⟩ x φ ↔ Satisfies ⟨F, V⟩ x (Formula.subst s φ) :=
  by
  induction φ using Formula.rec' generalizing x with
  | hatom a => simp [Satisfies];
  | hfalsum => simp [Satisfies];
  | himp φ ψ ihφ ihψ =>
    constructor; · intro hφψ y Rxy hφs; apply ihψ.mp; apply hφψ Rxy; apply ihφ.mpr hφs;
    · intro hφψs y Rxy hφ; apply ihψ.mpr; apply hφψs Rxy; apply ihφ.mp hφ;
  | hand φ ψ ihφ ihψ =>
    constructor; · rintro ⟨hφ, hψ⟩; exact ⟨ihφ.mp hφ, ihψ.mp hψ⟩
    · rintro ⟨hφ, hψ⟩; exact ⟨ihφ.mpr hφ, ihψ.mpr hψ⟩
  | hor φ ψ ihφ ihψ =>
    constructor;
    · rintro (hφ | hψ)
      · exact .inl <| ihφ.mp hφ
      · exact .inr <| ihψ.mp hψ
    · rintro (hφ | hψ)
      · exact .inl <| ihφ.mpr hφ
      · exact .inr <| ihψ.mpr hψ


-- @@ L191-191 verbatim
end Satisfies



-- @@ L194-194 verbatim
open Satisfies


-- @@ L196-197 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def ValidOnModel (M : Kripke.Model) (φ : Formula ℕ) :=
  ∀ w : M.World, Realize w φ


-- @@ L199-199 verbatim
namespace ValidOnModel


-- @@ L201-201 verbatim
instance semantics : Semantics (Formula ℕ) (Model) := ⟨fun M ↦ Formula.Kripke.ValidOnModel M⟩


-- @@ L203-203 verbatim
variable {M : Model} {φ ψ χ : Formula ℕ}


-- @@ L205-205 expanded
@[simp]
protected lemma iff_models : Realize M φ ↔ Formula.Kripke.ValidOnModel M φ :=
  iff_of_eq rfl


-- @@ L208-208 expanded
protected lemma verum : Realize M ⊤ := by simp [ValidOnModel, Satisfies];


-- @@ L210-210 verbatim
instance : Semantics.Top (Model) := ⟨fun _ => ValidOnModel.verum⟩



-- @@ L213-213 expanded
protected lemma bot : ¬Realize M ⊥ := by simp [ValidOnModel, Satisfies];


-- @@ L215-215 verbatim
instance : Semantics.Bot (Model) := ⟨fun _ => ValidOnModel.bot⟩



-- @@ L218-221 expanded
lemma iff_not_exists_world {M : Kripke.Model} : (¬Realize M φ) ↔ (∃ x : M.World, ¬Realize x φ) := by
  apply not_iff_not.mp; push Not; tauto;


-- @@ L223-223 verbatim
alias ⟨exists_world_of_not, not_of_exists_world⟩ := iff_not_exists_world


-- @@ L225-225 expanded
protected lemma andElim₁ : Realize M (Arrow.arrow (Wedge.wedge φ ψ) φ) := by
  simp_all [ValidOnModel, Satisfies];


-- @@ L227-227 expanded
protected lemma andElim₂ : Realize M (Arrow.arrow (Wedge.wedge φ ψ) ψ) := by
  simp_all [ValidOnModel, Satisfies];


-- @@ L229-232 expanded
protected lemma andInst₃ : Realize M (Arrow.arrow φ (Arrow.arrow ψ (Wedge.wedge φ ψ))) := by
  intro x y _ hp z Ryz hq; replace hp : Satisfies M z φ := formula_hereditary Ryz hp;
  exact ⟨hp, hq⟩;


-- @@ L234-234 expanded
protected lemma orInst₁ : Realize M (Arrow.arrow φ (Vee.vee φ ψ)) := by
  simp_all [ValidOnModel, Satisfies];


-- @@ L236-236 expanded
protected lemma orInst₂ : Realize M (Arrow.arrow ψ (Vee.vee φ ψ)) := by
  simp_all [ValidOnModel, Satisfies];


-- @@ L238-242 expanded
protected lemma orElim :
    Realize M
      (Arrow.arrow (Arrow.arrow φ χ)
        (Arrow.arrow (Arrow.arrow ψ χ) (Arrow.arrow (Vee.vee φ ψ) χ))) :=
  by intro w₁ w₂ _ hpr w₃ hw₂₃ hqr w₄ hw₃₄ hpq;
  cases hpq with
  | inl hp => exact hpr (M.rel_trans.trans _ _ _ hw₂₃ hw₃₄) hp;
  | inr hq => exact hqr hw₃₄ hq;


-- @@ L244-246 expanded
protected lemma imply₁ : Realize M (Arrow.arrow φ (Arrow.arrow ψ φ)) := by intro x y _ hp z Ryz _;
  exact formula_hereditary Ryz hp;


-- @@ L248-252 expanded
protected lemma imply₂ :
    Realize M
      (Arrow.arrow (Arrow.arrow φ (Arrow.arrow ψ χ))
        (Arrow.arrow (Arrow.arrow φ ψ) (Arrow.arrow φ χ))) :=
  by intro x y _ hpqr z Ryz hpq w Rzw hp; have Ryw : Frame.Rel' y w := Frame.rel_trans' Ryz Rzw;
  have Rww : Frame.Rel' w w := Frame.rel_refl'; exact hpqr Ryw hp Rww (hpq Rzw hp);


-- @@ L254-256 expanded
protected lemma mdp (hpq : Realize M (Arrow.arrow φ ψ)) (hp : Realize M φ) : Realize M ψ := by
  intro w; exact hpq w Frame.rel_refl' <| hp w;


-- @@ L258-258 expanded
protected lemma efq : Realize M (Axioms.EFQ φ) := by simp [ValidOnModel, Satisfies];


-- @@ L260-271 expanded
protected lemma lem : IsSymmetric M.Rel → Realize M (Axioms.LEM φ) :=
  by
  unfold IsSymmetric Axioms.LEM; contrapose; push Not; intro h;
  obtain ⟨x, ⟨hnxφ, ⟨y, Rxy, hyφ⟩⟩⟩ := by simpa [Satisfies] using exists_world_of_not h;
  use x, y; constructor; · assumption;
  · by_contra Ryx; have : Realize x φ := formula_hereditary Ryx hyφ; contradiction;


-- @@ L273-287 expanded
protected lemma dum : Connected M.Rel → Realize M (Axioms.Dummett φ ψ) :=
  by
  unfold Connected Axioms.Dummett; contrapose; push Not; intro h;
  obtain ⟨x, ⟨y, Rxy, hyφ, nhyψ⟩, ⟨z, Ryz, hzψ, nhyφ⟩⟩ := by
    simpa [Satisfies] using exists_world_of_not h;
  use x, y, z; refine ⟨⟨Rxy, Ryz⟩, ?_, ?_⟩;
  · by_contra Ryz; have : Realize z φ := formula_hereditary Ryz hyφ; contradiction;
  · by_contra Rzy; have : Realize y ψ := formula_hereditary Rzy hzψ; contradiction;


-- @@ L289-301 expanded
protected lemma wlem : Confluent M.Rel → Realize M (Axioms.WeakLEM φ) :=
  by
  unfold Confluent Axioms.WeakLEM; contrapose; push Not; intro h;
  obtain ⟨x, ⟨y, Rxy, hyφ⟩, ⟨z, Rxz, hz⟩⟩ := by simpa [Satisfies] using exists_world_of_not h;
  use x, y, z; refine ⟨⟨Rxy, Rxz⟩, ?_⟩;
  · rintro w Ryw; by_contra Rzw; have : Realize w φ := formula_hereditary Ryw hyφ; simp_all


-- @@ L303-303 verbatim
end ValidOnModel



-- @@ L306-307 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def ValidOnFrame (F : Frame) (φ : Formula ℕ) :=
  ∀ V, Realize (⟨F, V⟩ : Kripke.Model) φ


-- @@ L310-310 verbatim
namespace ValidOnFrame


-- @@ L312-312 verbatim
instance semantics : Semantics (Formula ℕ) (Frame) := ⟨fun F ↦ Formula.Kripke.ValidOnFrame F⟩


-- @@ L314-314 verbatim
variable {F : Frame} {φ ψ χ : Formula ℕ}


-- @@ L316-316 expanded
@[simp]
protected lemma models_iff : Realize F φ ↔ ValidOnFrame F φ :=
  iff_of_eq rfl


-- @@ L318-318 expanded
protected lemma top : Realize F ⊤ := by tauto;


-- @@ L319-319 verbatim
instance : Semantics.Top (Frame) := ⟨fun _ => ValidOnFrame.top⟩


-- @@ L321-323 expanded
protected lemma bot : ¬Realize F ⊥ := by
  intro h
  exact ValidOnModel.bot (h ⟨fun _ _ => True, by tauto⟩)


-- @@ L324-324 verbatim
instance : Semantics.Bot (Frame) := ⟨fun _ => ValidOnFrame.bot⟩



-- @@ L327-329 expanded
lemma iff_not_exists_valuation :
    (¬Realize F φ) ↔ (∃ V : Kripke.Valuation F, ¬Realize (⟨F, V⟩ : Kripke.Model) φ) := by
  simp [ValidOnFrame];


-- @@ L331-331 verbatim
alias ⟨exists_valuation_of_not, not_of_exists_valuation⟩ := iff_not_exists_valuation



-- @@ L334-336 expanded
lemma iff_not_exists_valuation_world :
    (¬Realize F φ) ↔
      (∃ V : Kripke.Valuation F, ∃ x : (⟨F, V⟩ : Kripke.Model).World, ¬Satisfies _ x φ) :=
  by simp [ValidOnFrame, ValidOnModel, Semantics.Realize];


-- @@ L338-339 verbatim
alias ⟨exists_valuation_world_of_not, not_of_exists_valuation_world⟩ :=
  iff_not_exists_valuation_world



-- @@ L342-350 expanded
lemma iff_not_exists_model_world :
    (¬Realize F φ) ↔ (∃ M : Kripke.Model, ∃ x : M.World, M.toFrame = F ∧ ¬(Realize x φ)) :=
  by
  constructor;
  · intro h; obtain ⟨V, x, h⟩ := iff_not_exists_valuation_world.mp h; use ⟨F, V⟩, x; tauto;
  · rintro ⟨M, x, rfl, h⟩; exact iff_not_exists_valuation_world.mpr ⟨M.Val, x, h⟩;


-- @@ L352-352 verbatim
alias ⟨exists_model_world_of_not, not_of_exists_model_world⟩ := iff_not_exists_model_world



-- @@ L355-359 expanded
protected lemma subst (h : Realize F φ) : Realize F (Formula.subst s φ) := by by_contra hC;
  obtain ⟨V, ⟨x, hx⟩⟩ := exists_valuation_world_of_not hC;
  apply Satisfies.iff_subst_self s |>.not.mpr hx; apply h;


-- @@ L361-361 expanded
protected lemma andElim₁ : Realize F (Arrow.arrow (Wedge.wedge φ ψ) φ) := fun _ =>
  ValidOnModel.andElim₁


-- @@ L363-363 expanded
protected lemma andElim₂ : Realize F (Arrow.arrow (Wedge.wedge φ ψ) ψ) := fun _ =>
  ValidOnModel.andElim₂


-- @@ L365-365 expanded
protected lemma andInst₃ : Realize F (Arrow.arrow φ (Arrow.arrow ψ (Wedge.wedge φ ψ))) := fun _ =>
  ValidOnModel.andInst₃


-- @@ L367-367 expanded
protected lemma orInst₁ : Realize F (Arrow.arrow φ (Vee.vee φ ψ)) := fun _ => ValidOnModel.orInst₁


-- @@ L369-369 expanded
protected lemma orInst₂ : Realize F (Arrow.arrow ψ (Vee.vee φ ψ)) := fun _ => ValidOnModel.orInst₂


-- @@ L371-372 expanded
protected lemma orElim :
    Realize F
      (Arrow.arrow (Arrow.arrow φ χ)
        (Arrow.arrow (Arrow.arrow ψ χ) (Arrow.arrow (Vee.vee φ ψ) χ))) :=
  fun _ => ValidOnModel.orElim


-- @@ L374-374 expanded
protected lemma imply₁ : Realize F (Arrow.arrow φ (Arrow.arrow ψ φ)) := fun _ => ValidOnModel.imply₁


-- @@ L376-377 expanded
protected lemma imply₂ :
    Realize F
      (Arrow.arrow (Arrow.arrow φ (Arrow.arrow ψ χ))
        (Arrow.arrow (Arrow.arrow φ ψ) (Arrow.arrow φ χ))) :=
  fun _ => ValidOnModel.imply₂


-- @@ L379-380 expanded
protected lemma mdp (hpq : Realize F (Arrow.arrow φ ψ)) (hp : Realize F φ) : Realize F ψ :=
  fun V x => ValidOnModel.mdp (hpq V) (hp V) x


-- @@ L382-382 expanded
protected lemma efq : Realize F (Axioms.EFQ φ) := fun _ => ValidOnModel.efq


-- @@ L384-385 expanded
protected lemma lem (F_symm : IsSymmetric F.Rel) : Realize F (Axioms.LEM φ) := fun _ =>
  ValidOnModel.lem F_symm


-- @@ L387-388 expanded
protected lemma dum (F_conn : Connected F.Rel) : Realize F (Axioms.Dummett φ ψ) := fun _ =>
  ValidOnModel.dum F_conn


-- @@ L390-391 expanded
protected lemma wlem (F_conf : Confluent F.Rel) : Realize F (Axioms.WeakLEM φ) := fun _ =>
  ValidOnModel.wlem F_conf


-- @@ L393-393 verbatim
end ValidOnFrame



-- @@ L396-397 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def ValidOnFrameClass (C : FrameClass) (φ : Formula ℕ) :=
  ∀ F, F ∈ C → Realize F φ


-- @@ L399-399 verbatim
namespace ValidOnFrameClass


-- @@ L401-401 verbatim
variable {C : FrameClass} {φ ψ χ : Formula ℕ}


-- @@ L403-403 verbatim
instance semantics : Semantics (Formula ℕ) (FrameClass) := ⟨fun C ↦ Kripke.ValidOnFrameClass C⟩


-- @@ L405-405 expanded
@[simp]
protected lemma models_iff : Realize C φ ↔ Formula.Kripke.ValidOnFrameClass C φ :=
  iff_of_eq rfl


-- @@ L407-410 expanded
protected lemma bot (h_nonempty : C.Nonempty) : ¬Realize C ⊥ := by
  simp only [ValidOnFrameClass.models_iff, ValidOnFrameClass, Semantics.Bot.realize_bot, imp_false,
    not_forall, not_not];
  exact h_nonempty;


-- @@ L412-415 expanded
lemma iff_not_exists_frame {C : Kripke.FrameClass} : (¬Realize C φ) ↔ (∃ F ∈ C, ¬Realize F φ) := by
  apply not_iff_not.mp; push Not; tauto;


-- @@ L417-417 verbatim
alias ⟨exists_frame_of_not, not_of_exists_frame⟩ := iff_not_exists_frame


-- @@ L419-423 expanded
lemma iff_not_exists_model {C : Kripke.FrameClass} :
    (¬Realize C φ) ↔ (∃ M : Kripke.Model, M.toFrame ∈ C ∧ ¬Realize M φ) := by apply not_iff_not.mp;
  push Not; tauto;


-- @@ L425-425 verbatim
alias ⟨exists_model_of_not, not_of_exists_model⟩ := iff_not_exists_model



-- @@ L428-432 expanded
lemma iff_not_exists_model_world {C : Kripke.FrameClass} :
    (¬Realize C φ) ↔ (∃ M : Kripke.Model, ∃ x : M.World, M.toFrame ∈ C ∧ ¬(Realize x φ)) := by
  apply not_iff_not.mp; push Not; tauto;


-- @@ L434-434 verbatim
alias ⟨exists_model_world_of_not, not_of_exists_model_world⟩ := iff_not_exists_model_world


-- @@ L436-436 verbatim
end ValidOnFrameClass


-- @@ L438-438 verbatim
end Kripke

-- @@ L439-439 verbatim
end Formula




-- @@ L443-443 verbatim
namespace Kripke


-- @@ L445-445 verbatim
namespace FrameClass


-- @@ L447-447 verbatim
variable {C : FrameClass} {φ ψ χ : Formula ℕ}


-- @@ L449-451 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class DefinedBy (C : Kripke.FrameClass) (Γ : Set (Formula ℕ)) where
  defines : ∀ F, F ∈ C ↔ (∀ φ ∈ Γ, Realize F φ)


-- @@ L453-455 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class FiniteDefinedBy (C Γ) extends FrameClass.DefinedBy C Γ where
  finite : Set.Finite Γ


-- @@ L457-458 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev DefinedByFormula (C : Kripke.FrameClass) (φ : Formula ℕ) := FrameClass.DefinedBy C {φ}


-- @@ L460-462 expanded
lemma definedByFormula_of_iff_mem_validate (h : ∀ F, F ∈ C ↔ Realize F φ) : DefinedByFormula C φ :=
  by constructor; simpa;


-- @@ L464-476 verbatim
instance definedBy_inter
  (C₁ Γ₁) [h₁ : DefinedBy C₁ Γ₁]
  (C₂ Γ₂) [h₂ : DefinedBy C₂ Γ₂]
  : DefinedBy (C₁ ∩ C₂) (Γ₁ ∪ Γ₂) := ⟨by
  rintro F;
  constructor
  · rintro ⟨hF₁, hF₂⟩ φ (hφ₁ | hφ₂)
    · exact h₁.defines F |>.mp hF₁ _ hφ₁
    · exact h₂.defines F |>.mp hF₂ _ hφ₂
  · intro h
    exact ⟨h₁.defines F |>.mpr fun φ hφ => h _ (.inl hφ),
      h₂.defines F |>.mpr fun φ hφ => h _ (.inr hφ)⟩
⟩


-- @@ L478-481 verbatim
instance definedByFormula_inter
  (C₁ φ₁) [DefinedByFormula C₁ φ₁]
  (C₂ φ₂) [DefinedByFormula C₂ φ₂]
  : DefinedBy (C₁ ∩ C₂) {φ₁, φ₂} := definedBy_inter C₁ {φ₁} C₂ {φ₂}



-- @@ L484-486 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class IsNonempty (C : Kripke.FrameClass) : Prop where
  nonempty : Nonempty C


-- @@ L488-488 verbatim
end FrameClass



-- @@ L491-492 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev AllFrameClass : FrameClass := Set.univ


-- @@ L494-499 verbatim
instance _root_.LO.IntProp.Kripke.AllFrameClass.DefinedBy :
    AllFrameClass.DefinedByFormula (Axioms.EFQ (.atom 0)) :=
  FrameClass.definedByFormula_of_iff_mem_validate <| by
    simp only [Set.mem_univ, true_iff];
    intro F;
    exact Formula.Kripke.ValidOnFrame.efq;


-- @@ L501-503 verbatim
instance _root_.LO.IntProp.Kripke.AllFrameClass.IsNonempty : AllFrameClass.IsNonempty := by
  use pointFrame;
  trivial;



-- @@ L506-506 verbatim
namespace FrameClass


-- @@ L508-508 verbatim
variable {C : Kripke.FrameClass} {Γ : Set (Formula ℕ)}


-- @@ L510-513 verbatim
lemma definedBy_with_axiomEFQ (defines : C.DefinedBy Γ) :
    DefinedBy C (insert (Axioms.EFQ (.atom 0)) Γ) := by
  convert definedBy_inter AllFrameClass {Axioms.EFQ (.atom 0)} C Γ <;>
    simp [AllFrameClass, Set.singleton_union];


-- @@ L515-515 verbatim
end FrameClass


-- @@ L517-517 verbatim
end Kripke


-- @@ L519-519 verbatim
end IntProp

-- @@ L520-520 verbatim
end LO
