/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.Kripke.Preservation
public import LeanPool.Incompleteness.Foundation.Modal.Kripke.FiniteFrame
import LeanPool.Incompleteness.Foundation.Vorspiel.Chain


-- @@ L12-12 verbatim
/-! # Tree -/


-- @@ L14-14 verbatim
@[expose] public section


-- @@ L16-16 verbatim
namespace LO

-- @@ L17-17 verbatim
namespace Modal



-- @@ L20-24 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
structure _root_.LO.Modal.Kripke.FiniteTransitiveTree extends Kripke.FiniteFrame,
  Kripke.RootedFrame where
  rel_assymetric : Assymetric Rel
  rel_transitive : IsTrans World Rel


-- @@ L26-27 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
add_decl_doc LO.Modal.Kripke.FiniteTransitiveTree.toRootedFrame


-- @@ L29-29 verbatim
namespace Kripke

-- @@ L30-30 verbatim
namespace FiniteTransitiveTree


-- @@ L32-34 verbatim
lemma rel_irreflexive (T : FiniteTransitiveTree) :
    Std.Irrefl T.Rel :=
  ⟨irreflexive_of_assymetric <| T.rel_assymetric⟩


-- @@ L36-36 verbatim
end FiniteTransitiveTree

-- @@ L37-37 verbatim
end Kripke



-- @@ L40-44 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Modal.Formula.Kripke.ValidOnFiniteTransitiveTreeFrame
    (T : Kripke.FiniteTransitiveTree) (φ : Formula ℕ) :=
  Realize T.toFrame φ


-- @@ L46-46 verbatim
namespace ValidOnFiniteTransitiveTreeFrame


-- @@ L48-50 verbatim
instance semantics :
    Semantics (Formula ℕ) (Kripke.FiniteFrame) :=
  ⟨fun F ↦ Formula.Kripke.ValidOnFiniteFrame F⟩


-- @@ L52-52 verbatim
end ValidOnFiniteTransitiveTreeFrame



-- @@ L55-55 verbatim
namespace Kripke


-- @@ L57-57 verbatim
open Relation (TransGen)


-- @@ L59-60 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
structure FiniteTransitiveTreeModel extends FiniteTransitiveTree, Model where


-- @@ L62-63 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
add_decl_doc FiniteTransitiveTreeModel.toModel


-- @@ L65-65 verbatim
variable {F : Frame} {r : F.World}


-- @@ L67-71 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Modal.Kripke.Frame.TreeUnravelling (F : Frame) (r : F.World) : Kripke.Frame where
  World := { c : List F.World | [r] <+: c ∧ c.IsChain F.Rel }
  Rel cx cy := ∃ z, cx.1 ++ [z] = cy.1
  world_nonempty := ⟨[r], (by simp)⟩


-- @@ L73-73 verbatim
namespace Frame

-- @@ L74-74 verbatim
namespace TreeUnravelling


-- @@ L76-80 verbatim
@[simp 1100]
lemma not_nil {c : (F.TreeUnravelling r).World} : c.1 ≠ [] := by
  have := c.2.1;
  by_contra;
  simp_all;


-- @@ L82-85 expanded
lemma rel_length {x y : (F.TreeUnravelling r).World} (h : Frame.Rel' x y) :
    x.1.length < y.1.length := by obtain ⟨z, hz⟩ := h; rw [← hz]; simp;


-- @@ L87-90 verbatim
lemma irreflexive : Std.Irrefl (F.TreeUnravelling r).Rel := by
  constructor
  intro x
  simp [TreeUnravelling];


-- @@ L92-97 verbatim
lemma assymetric : Assymetric (F.TreeUnravelling r).Rel := by
  rintro x y hxy;
  by_contra hyx;
  replace hxy := rel_length hxy;
  replace hyx := rel_length hyx;
  omega;


-- @@ L99-131 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def PMorphism (F : Frame) (r : F) : Frame.PseudoEpimorphism (F.TreeUnravelling r) F
    where
  toFun c := c.1.getLast (by simp)
  forth {cx cy}
    h := by
    obtain ⟨z, hz⟩ := h;
    have hchain : (cx.1 ++ [z]).IsChain F.Rel :=
      by
      rw [hz]
      exact cy.2.2
    have h := (List.isChain_append.mp hchain).2.2
    have hx : cx.1.getLast (by aesop) ∈ cx.1.getLast? :=
      List.getLast?_eq_getLast_of_ne_nil (by simp)
    have hy : z ∈ ([z] : List F.World).head? := by simp
    have hlast? : cy.1.getLast? = some z := by
      rw [← hz]
      simp
    have hcy := List.getLast?_eq_getLast_of_ne_nil (l := cy.1) (by aesop)
    simp_all
  back {cx y}
    h := by
    simp_all only [Set.mem_ofPred_eq]; use ⟨cx.1 ++ [y], ?_⟩;
    · constructor; · simp;
      · use y;
    · constructor; · obtain ⟨i, hi⟩ := cx.2.1; use (i ++ [y]); simp_rw [← List.append_assoc, hi];
      · apply List.IsChain.append; · exact cx.2.2;
        · simp;
        · intro z hz; simp only [List.head?_cons, Option.mem_def, Option.some.injEq, forall_eq'];
          convert h; exact List.mem_getLast?_eq_getLast hz |>.2;


-- @@ L133-133 verbatim
end TreeUnravelling

-- @@ L134-134 verbatim
end Frame



-- @@ L137-140 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.Frame.TransitiveTreeUnravelling (F : Frame) (r : F.World) :=
  Frame.TransitiveClosure (F.TreeUnravelling r)


-- @@ L142-142 verbatim
namespace Frame

-- @@ L143-143 verbatim
namespace TransitiveTreeUnravelling


-- @@ L145-146 verbatim
lemma not_nil {c : (F.TransitiveTreeUnravelling r).World} : c.1 ≠ [] := by
  simp_all


-- @@ L148-152 expanded
lemma rel_length {x y : (F.TransitiveTreeUnravelling r).World} (Rxy : Frame.Rel' x y) :
    x.1.length < y.1.length := by
  induction Rxy with
  | single Rxy => exact TreeUnravelling.rel_length Rxy;
  | tail _ h ih => have := TreeUnravelling.rel_length h; omega;


-- @@ L154-157 verbatim
lemma rel_transitive :
    IsTrans (F.TransitiveTreeUnravelling r).World
      (F.TransitiveTreeUnravelling r).Rel :=
  TransitiveClosure.rel_transitive


-- @@ L159-164 verbatim
lemma rel_asymmetric : Assymetric (F.TransitiveTreeUnravelling r).Rel := by
  rintro x y hxy;
  by_contra hyx;
  replace hxy := rel_length hxy;
  replace hyx := rel_length hyx;
  omega;


-- @@ L166-207 expanded
lemma rel_def {x y : (F.TransitiveTreeUnravelling r).World} :
    Frame.Rel' x y ↔ (x.1.length < y.1.length ∧ x.1 <+: y.1) :=
  by
  constructor;
  · intro Rxy;
    induction Rxy with
    | single Rxy =>
      obtain ⟨z, hz⟩ := Rxy; rw [← hz]; constructor; · simp;
      · use [z];
    | tail _ h ih =>
      obtain ⟨w, hw⟩ := h; obtain ⟨_, ⟨zs, hzs⟩⟩ := ih; rw [← hw, ← hzs]; constructor; · simp;
      · use zs ++ [w]; simp [List.append_assoc];
  · replace ⟨xs, ⟨ws, hw⟩, hx₂⟩ := x; replace ⟨ys, ⟨vs, hv⟩, hy₂⟩ := y; subst hw hv;
    rintro ⟨hl, ⟨zs, hzs⟩⟩; simp only [List.cons_append, List.nil_append] at hzs;
    induction zs using List.induction_with_singleton generalizing ws vs with
    | hnil => simp_all;
    | hsingle z => apply TransGen.single; use z; simp_all only [List.cons_append, List.nil_append];
    | hcons z zs h
      ih =>
      simp_all only [Set.mem_ofPred_eq, List.cons_append, List.nil_append];
      refine TransGen.head ?h₁ <| ih (ws ++ [z]) vs ?h₂ ?h₃ ?h₄ ?h₅; · use z; simp;
      · apply List.IsChain.prefix hy₂; use zs; simp_all;
      · exact hy₂;
      · rw [← hzs];
        simp only [List.length_cons, List.length_append, List.length_nil, zero_add,
          add_lt_add_iff_right, add_lt_add_iff_left, lt_add_iff_pos_left];
        by_contra hC; simp_all;
      · simp_all;


-- @@ L209-220 verbatim
lemma rooted : (F.TransitiveTreeUnravelling r).isRooted ⟨[r], by tauto⟩ := by
  intro x ha;
  apply rel_def.mpr;
  obtain ⟨zs, hzs⟩ := x.2.1;
  constructor;
  · rw [←hzs];
    by_contra hC;
    simp at hC;
    apply ha;
    apply Subtype.ext;
    simpa [hC] using hzs.symm;
  · use zs;


-- @@ L222-225 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev pMorphism (F : Frame) (F_trans : IsTrans F.World F.Rel) (r : F) :
    Frame.PseudoEpimorphism (F.TransitiveTreeUnravelling r) F :=
  (Frame.TreeUnravelling.PMorphism F r).TransitiveClosure F_trans


-- @@ L227-227 verbatim
end TransitiveTreeUnravelling

-- @@ L228-228 verbatim
end Frame



-- @@ L231-235 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Modal.Kripke.Model.TreeUnravelling (M : Kripke.Model) (r : M.World) :
    Kripke.Model where
  toFrame := M.toFrame.TreeUnravelling r
  Val c a := M.Val (c.1.getLast (by simp)) a


-- @@ L237-237 verbatim
namespace Model

-- @@ L238-238 verbatim
namespace TreeUnravelling


-- @@ L240-240 verbatim
variable {M : Kripke.Model} {r : M.World}


-- @@ L242-244 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def pMorphism (M : Kripke.Model) (r : M.World) : Frame.PseudoEpimorphism (M.TreeUnravelling r) M :=
  PseudoEpimorphism.ofAtomic (Frame.TreeUnravelling.PMorphism M.toFrame r) <| by aesop;


-- @@ L246-246 verbatim
end TreeUnravelling

-- @@ L247-247 verbatim
end Model



-- @@ L250-254 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Modal.Kripke.Model.TransitiveTreeUnravelling (M : Kripke.Model) (r : M.World) :
    Kripke.Model where
  toFrame := M.toFrame.TransitiveTreeUnravelling r
  Val c a := M.Val (c.1.getLast (by simp)) a


-- @@ L256-256 verbatim
namespace Model

-- @@ L257-257 verbatim
namespace TransitiveTreeUnravelling


-- @@ L259-263 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev pMorphism (M : Kripke.Model) (M_trans : IsTrans M.World M.Rel) (r : M.World) :
    Frame.PseudoEpimorphism (M.TransitiveTreeUnravelling r) M :=
  PseudoEpimorphism.ofAtomic (Frame.TransitiveTreeUnravelling.pMorphism M.toFrame M_trans r) <| by
    aesop;


-- @@ L265-269 verbatim
lemma modal_equivalence_at_root (M : Kripke.Model) (M_trans : IsTrans M.World M.Rel) (r : M.World)
  : ModalEquivalent (M₁ := M.TransitiveTreeUnravelling r) (M₂ := M) ⟨[r], by simp⟩ r
  :=
    Model.PseudoEpimorphism.modal_equivalence
      (Model.TransitiveTreeUnravelling.pMorphism M M_trans r) (⟨[r], by simp⟩)


-- @@ L271-271 verbatim
end TransitiveTreeUnravelling

-- @@ L272-272 verbatim
end Model



-- @@ L275-279 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.Model.FiniteTransitiveTreeUnravelling (M : Kripke.Model)
    (r : M.World) : Kripke.Model :=
  (Frame.PointGenerated M r).TransitiveTreeUnravelling ⟨r, by tauto⟩


-- @@ L281-306 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.FiniteFrame.FiniteTransitiveTreeUnravelling (F : FiniteFrame)
    (F_trans : IsTrans F.World F.Rel) (F_irrefl : Std.Irrefl F.toFrame) (r : F.World) :
    FiniteTransitiveTree :=
  letI T := (Frame.PointGenerated F.toFrame r).TransitiveTreeUnravelling ⟨r, by tauto⟩
  { World := T.World
    Rel := T.Rel
    root := ⟨[⟨r, by tauto⟩], by tauto⟩
    rel_transitive := Frame.TransitiveTreeUnravelling.rel_transitive
    rel_assymetric := Frame.TransitiveTreeUnravelling.rel_asymmetric
    root_rooted := Frame.TransitiveTreeUnravelling.rooted
    world_finite :=
      by
      suffices h : Finite { x // List.IsChain (F.PointGenerated r).Rel x } by
        exact
          Finite.of_injective (β := { x // List.IsChain (F.PointGenerated r).Rel x })
            (fun x => ⟨x.1, x.2.2⟩)
            (by intro x y hxy; apply Subtype.ext; exact congrArg (fun z => z.1) hxy);
      exact
        List.chains_finite (Frame.PointGenerated.rel_transitive (F := F.toFrame) (r := r) F_trans)
          (Frame.PointGenerated.rel_irreflexive (F := F.toFrame) (r := r) F_irrefl) }


-- @@ L308-308 verbatim
end Kripke


-- @@ L310-310 verbatim
end Modal

-- @@ L311-311 verbatim
end LO
