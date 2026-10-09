import OAI.ModelTheory.Categoricity.Collapse


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u v w


-- @@ L7-7 verbatim
noncomputable section


-- @@ L9-9 verbatim
namespace CHObstruction


-- @@ L11-11 verbatim
open Cardinal Ordinal Order


-- @@ L13-13 verbatim
namespace Diagrams


-- @@ L15-15 verbatim
abbrev Tag := (ω_ (1 : Ordinal.{u})).ToType


-- @@ L17-17 verbatim
def tagOrdinal (t : Tag.{u}) : Ordinal.{u} := t.toOrd.val


-- @@ L19-19 verbatim
theorem tag_lt (t : Tag.{u}) : tagOrdinal t < ω_ 1 := t.toOrd.property


-- @@ L21-21 verbatim
abbrev Label (A : Type v) := {J : Finset A // J.Nonempty} × ℕ


-- @@ L23-23 verbatim
namespace Label


-- @@ L25-26 verbatim
def map {A : Type v} {B : Type w} (e : A ↪ B) (l : Label A) : Label B :=
  (⟨l.1.val.map e, l.1.property.map⟩, l.2)


-- @@ L28-28 verbatim
def root {A : Type v} (a : A) : Label A := (⟨{a}, Finset.singleton_nonempty a⟩, 0)


-- @@ L30-33 verbatim
@[simp] theorem map_refl {A : Type v} (l : Label A) :
    map (Function.Embedding.refl A) l = l := by
  rcases l with ⟨⟨J, hJ⟩, i⟩
  simp [map]


-- @@ L35-38 verbatim
@[simp] theorem map_comp {A : Type u} {B : Type v} {C : Type w}
    (e : A ↪ B) (f : B ↪ C) (l : Label A) :
    map f (map e l) = map (e.trans f) l := by
  simp only [map, Finset.map_map]


-- @@ L40-42 verbatim
@[simp] theorem map_root {A : Type v} {B : Type w} (e : A ↪ B) (a : A) :
    map e (root a) = root (e a) := by
  simp [map, root]


-- @@ L44-56 verbatim
def congr {A : Type v} {B : Type w} (e : A ≃ B) : Label A ≃ Label B where
  toFun := map e.toEmbedding
  invFun := map e.symm.toEmbedding
  left_inv l := by
    rw [map_comp]
    have he : e.toEmbedding.trans e.symm.toEmbedding = Function.Embedding.refl A := by
      ext a; exact e.symm_apply_apply a
    rw [he, map_refl]
  right_inv l := by
    rw [map_comp]
    have he : e.symm.toEmbedding.trans e.toEmbedding = Function.Embedding.refl B := by
      ext b; exact e.apply_symm_apply b
    rw [he, map_refl]


-- @@ L58-58 verbatim
end Label


-- @@ L60-63 verbatim
structure Diagram (A : Type v) where
  eqv : Label A → Label A → Prop
  rel : Label A → Label A → Prop
  tag : Label A → Tag.{u}


-- @@ L65-65 verbatim
namespace Diagram


-- @@ L67-67 verbatim
variable {A : Type v} {B : Type w}


-- @@ L69-75 verbatim
structure Valid (D : Diagram.{u} A) : Prop where
  equivalence : Equivalence D.eqv
  rel_congr : ∀ a a' b b', D.eqv a a' → D.eqv b b' → (D.rel a b ↔ D.rel a' b')
  tag_congr : ∀ a a', D.eqv a a' → D.tag a = D.tag a'
  decreases : ∀ a b, D.rel a b → tagOrdinal (D.tag a) < tagOrdinal (D.tag b)
  extensional : ∀ a b, (∀ z, D.rel z a ↔ D.rel z b) → D.eqv a b
  roots : ∀ a b, D.eqv (Label.root a) (Label.root b) → a = b


-- @@ L77-80 verbatim
def restrict (D : Diagram.{u} B) (e : A ↪ B) : Diagram.{u} A where
  eqv a b := D.eqv (Label.map e a) (Label.map e b)
  rel a b := D.rel (Label.map e a) (Label.map e b)
  tag a := D.tag (Label.map e a)


-- @@ L82-85 verbatim
@[simp] theorem restrict_refl (D : Diagram.{u} A) :
    D.restrict (Function.Embedding.refl A) = D := by
  cases D
  simp [restrict]


-- @@ L87-89 verbatim
theorem restrict_comp {C : Type*} (D : Diagram.{u} C) (e : A ↪ B) (f : B ↪ C) :
    (D.restrict f).restrict e = D.restrict (e.trans f) := by
  simp only [restrict, Label.map_comp]


-- @@ L91-110 verbatim
theorem valid_restrict_equiv (D : Diagram.{u} B) (hD : D.Valid) (e : A ≃ B) :
    (D.restrict e.toEmbedding).Valid := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨fun a => hD.equivalence.refl _, fun h => hD.equivalence.symm h,
      fun h h' => hD.equivalence.trans h h'⟩
  · intro a a' b b' h h'
    exact hD.rel_congr _ _ _ _ h h'
  · intro a a' h
    exact hD.tag_congr _ _ h
  · intro a b h
    exact hD.decreases _ _ h
  · intro a b h
    apply hD.extensional
    intro z
    obtain ⟨z', rfl⟩ := (Label.congr e).surjective z
    exact h z'
  · intro a b h
    apply e.injective
    apply hD.roots
    simpa only [restrict, Label.map_root, Equiv.toEmbedding_apply] using h


-- @@ L112-114 verbatim
def setoid (D : Diagram.{u} A) (hD : D.Valid) : Setoid (Label A) where
  r := D.eqv
  iseqv := hD.equivalence


-- @@ L116-116 verbatim
abbrev Q (D : Diagram.{u} A) (hD : D.Valid) := Quotient (D.setoid hD)


-- @@ L118-119 verbatim
def qRel (D : Diagram.{u} A) (hD : D.Valid) : D.Q hD → D.Q hD → Prop :=
  Quotient.lift₂ D.rel (fun a b a' b' h h' => propext (hD.rel_congr a a' b b' h h'))


-- @@ L121-123 verbatim
def qTag (D : Diagram.{u} A) (hD : D.Valid) : D.Q hD → Ordinal.{u} :=
  Quotient.lift (fun a => tagOrdinal (D.tag a))
    (fun a b h => congrArg tagOrdinal (hD.tag_congr a b h))


-- @@ L125-131 verbatim
theorem q_extensional (D : Diagram.{u} A) (hD : D.Valid) :
    ∀ x y, (∀ z, D.qRel hD z x ↔ D.qRel hD z y) → x = y := by
  intro x y
  induction x, y using Quotient.inductionOn₂ with
  | h a b =>
    intro h
    exact Quotient.sound (hD.extensional a b (fun z => h ⟦z⟧))


-- @@ L133-137 verbatim
theorem q_decreases (D : Diagram.{u} A) (hD : D.Valid) :
    ∀ x y, D.qRel hD y x → D.qTag hD y < D.qTag hD x := by
  intro x y
  induction x, y using Quotient.inductionOn₂ with
  | h a b => exact hD.decreases b a


-- @@ L139-143 verbatim
theorem q_bound (D : Diagram.{u} A) (hD : D.Valid) :
    ∀ x, D.qTag hD x < ω_ 1 := by
  intro x
  induction x using Quotient.inductionOn with
  | h a => exact tag_lt (D.tag a)


-- @@ L145-161 verbatim
def qMap (D : Diagram.{u} A) (E : Diagram.{u} B) (hD : D.Valid) (hE : E.Valid)
    (e : A ↪ B) (h : D = E.restrict e) : D.Q hD ↪ E.Q hE where
  toFun := Quotient.map' (Label.map e) (fun a b hh => by
    change D.eqv a b at hh
    change E.eqv (Label.map e a) (Label.map e b)
    rw [h] at hh
    exact hh)
  inj' := by
    intro x y hxy
    induction x, y using Quotient.inductionOn₂ with
    | h a b =>
      apply Quotient.sound
      have hh := Quotient.exact hxy
      change E.eqv (Label.map e a) (Label.map e b) at hh
      change D.eqv a b
      rw [h]
      exact hh


-- @@ L163-165 verbatim
theorem qMap_mk (D : Diagram.{u} A) (E : Diagram.{u} B) (hD : D.Valid) (hE : E.Valid)
    (e : A ↪ B) (h : D = E.restrict e) (x : Label A) :
    qMap D E hD hE e h ⟦x⟧ = ⟦Label.map e x⟧ := rfl


-- @@ L167-167 verbatim
end Diagram


-- @@ L169-169 verbatim
end Diagrams


-- @@ L171-171 verbatim
namespace NoPattern


-- @@ L173-173 verbatim
open Diagrams


-- @@ L175-177 verbatim
variable (d : ∀ k : ℕ, Diagram.{u} (Fin k))
  (valid : ∀ k, (d k).Valid)
  (coherent : ∀ m n (e : Fin m ↪o Fin n), d m = (d n).restrict e.toEmbedding)


-- @@ L179-179 verbatim
section FiniteStages


-- @@ L181-181 verbatim
variable {J : Type u} [LinearOrder J]


-- @@ L183-186 verbatim
def inclusion (X Y : Finset J) (h : X ⊆ Y) : X ↪o Y where
  toFun x := ⟨x.val, h x.property⟩
  inj' _x _y hxy := Subtype.ext (congrArg (fun z : Y => z.val) hxy)
  map_rel_iff' := Iff.rfl


-- @@ L188-190 verbatim
def positions (X Y : Finset J) (h : X ⊆ Y) : Fin X.card ↪o Fin Y.card :=
  ((X.orderIsoOfFin rfl).toOrderEmbedding.comp (inclusion X Y h)).comp
    (Y.orderIsoOfFin rfl).symm.toOrderEmbedding


-- @@ L192-193 verbatim
def stage (X : Finset J) : Diagram.{u} X :=
  (d X.card).restrict (X.orderIsoOfFin rfl).symm.toEquiv.toEmbedding


-- @@ L195-197 verbatim
include valid in
theorem stage_valid (X : Finset J) : (stage d X).Valid :=
  (d X.card).valid_restrict_equiv (valid X.card) (X.orderIsoOfFin rfl).symm.toEquiv


-- @@ L199-208 verbatim
include coherent in
theorem stage_restrict (X Y : Finset J) (h : X ⊆ Y) :
    stage d X = (stage d Y).restrict (inclusion X Y h).toEmbedding := by
  unfold stage
  rw [coherent X.card Y.card (positions X Y h), Diagram.restrict_comp,
    Diagram.restrict_comp]
  congr 1
  ext x
  exact congrArg (fun y => ((Y.orderIsoOfFin rfl).symm (inclusion X Y h y)).val)
    ((X.orderIsoOfFin rfl).apply_symm_apply x)


-- @@ L210-210 verbatim
abbrev F (X : Finset J) := (stage d X).Q (stage_valid d valid X)


-- @@ L212-214 verbatim
def transition (X Y : Finset J) (h : X ≤ Y) : F d valid X ↪ F d valid Y :=
  Diagram.qMap _ _ (stage_valid d valid X) (stage_valid d valid Y)
    (inclusion X Y h).toEmbedding (stage_restrict d coherent X Y h)


-- @@ L216-231 verbatim
instance directedSystem : DirectedSystem (F d valid (J := J))
    (fun X Y h => transition d valid coherent X Y h) where
  map_self := by
    intro X x
    induction x using Quotient.inductionOn with
    | h a =>
      rw [transition, Diagram.qMap_mk]
      have he : (inclusion X X le_rfl).toEmbedding = Function.Embedding.refl X := by
        ext x; rfl
      rw [he, Label.map_refl]
  map_map := by
    intro Z Y X hXY hYZ x
    induction x using Quotient.inductionOn with
    | h a =>
      simp only [transition, Diagram.qMap_mk, Label.map_comp]
      rfl


-- @@ L233-234 verbatim
def stageRelation (X : Finset J) : F d valid X → F d valid X → Prop :=
  (stage d X).qRel (stage_valid d valid X)


-- @@ L236-237 verbatim
def stageTag (X : Finset J) : F d valid X → Ordinal.{u} :=
  (stage d X).qTag (stage_valid d valid X)


-- @@ L239-248 verbatim
theorem relation_compatible (X Y : Finset J) (h : X ≤ Y) (x y : F d valid X) :
    stageRelation d valid X x y ↔ stageRelation d valid Y
      (transition d valid coherent X Y h x) (transition d valid coherent X Y h y) := by
  induction x, y using Quotient.inductionOn₂ with
  | h a b =>
    change (stage d X).rel a b ↔
      (stage d Y).rel (Label.map (inclusion X Y h).toEmbedding a)
        (Label.map (inclusion X Y h).toEmbedding b)
    rw [stage_restrict d coherent X Y h]
    rfl


-- @@ L250-257 verbatim
theorem tag_compatible (X Y : Finset J) (h : X ≤ Y) (x : F d valid X) :
    stageTag d valid X x = stageTag d valid Y (transition d valid coherent X Y h x) := by
  induction x using Quotient.inductionOn with
  | h a =>
    change tagOrdinal ((stage d X).tag a) =
      tagOrdinal ((stage d Y).tag (Label.map (inclusion X Y h).toEmbedding a))
    rw [stage_restrict d coherent X Y h]
    rfl


-- @@ L259-259 verbatim
abbrev Limit := DirectLimit (F d valid (J := J)) (transition d valid coherent)


-- @@ L261-262 verbatim
def root (x : J) : Limit d valid coherent (J := J) :=
  ⟦⟨{x}, Quotient.mk _ (Label.root (⟨x, Finset.mem_singleton_self x⟩ : ({x} : Finset J)))⟩⟧


-- @@ L264-270 verbatim
theorem root_injective : Function.Injective (root d valid coherent (J := J)) := by
  intro x y h
  obtain ⟨Z, hxZ, hyZ, heq⟩ := Quotient.exact h
  simp only [transition, Diagram.qMap_mk, Label.map_root] at heq
  have hrel := Quotient.exact heq
  have hxy := (stage_valid d valid Z).roots _ _ hrel
  exact congrArg Subtype.val hxy


-- @@ L272-279 verbatim
def rootsEmbedding : J ↪ ZFSet.vonNeumann (ω_ (1 : Ordinal.{u})) :=
  (⟨root d valid coherent, root_injective d valid coherent⟩ : J ↪ Limit d valid coherent).trans
    (TaggedLimit.embedding (F d valid) (transition d valid coherent)
      (stageRelation d valid) (relation_compatible d valid coherent)
      (stageTag d valid) (tag_compatible d valid coherent)
      (fun X => (stage d X).q_extensional (stage_valid d valid X))
      (fun X => (stage d X).q_decreases (stage_valid d valid X))
      (ω_ 1) (fun X => (stage d X).q_bound (stage_valid d valid X)))


-- @@ L281-281 verbatim
end FiniteStages


-- @@ L283-293 verbatim
include d valid coherent in

theorem impossible : False := by
  let V := ZFSet.vonNeumann (ω_ (1 : Ordinal.{u}))
  let J := (succ V.card).ord.ToType
  let e : J ↪ Shrink.{u} V :=
    (rootsEmbedding d valid coherent (J := J)).trans (equivShrink V).toEmbedding
  have hle : succ V.card ≤ V.card := by
    simpa only [J, Cardinal.mk_toType, Cardinal.card_ord, ZFSet.card]
      using Cardinal.mk_le_of_injective e.injective
  exact (lt_succ V.card).not_ge hle


-- @@ L295-295 verbatim
end NoPattern


-- @@ L297-297 verbatim
end CHObstruction


-- @@ L299-299 verbatim
end


-- @@ L301-301 verbatim
end OAI
