/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Basic
public import PolyFun.PFunctor.Equiv.Basic
import Batteries.Tactic.Lint


-- @@ L12-14 verbatim
/-!
# More properties about lenses between polynomial functors
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
universe u v uA uB uA₁ uB₁ uA₂ uB₂ uA₃ uB₃ uA₄ uB₄ uA₅ uB₅ uA₆ uB₆


-- @@ L20-20 verbatim
section find_home


-- @@ L22-22 verbatim
variable {α : Sort u} {β : α → Sort v} {γ : α → Sort v}


-- @@ L24-28 verbatim
lemma heq_forall_iff (h : ∀ a, β a = γ a) {f : (a : α) → β a} {g : (a : α) → γ a} :
    f ≍ g ↔ ∀ a, (f a) ≍ (g a) := by
  have := funext h
  subst this
  aesop


-- @@ L30-30 verbatim
end find_home


-- @@ L32-32 verbatim
namespace PFunctor


-- @@ L34-34 verbatim
namespace Lens


-- @@ L36-45 verbatim
@[ext (iff := false)]
theorem ext {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} (l₁ l₂ : Lens P Q)
    (h₁ : ∀ a, l₁.toFunA a = l₂.toFunA a) (h₂ : ∀ a, l₁.toFunB a = (h₁ a) ▸ l₂.toFunB a) :
    l₁ = l₂ := by
  rcases l₁ with ⟨toFunA₁, _⟩
  rcases l₂ with ⟨toFunA₂, _⟩
  have h : toFunA₁ = toFunA₂ := funext h₁
  subst h
  simp_all only [mk.injEq, heq_eq_eq, true_and]
  simpa using funext h₂


-- @@ L47-59 verbatim
/-- Heterogeneous extensionality for lenses: equal position maps and
heterogeneously equal direction maps identify two lenses. Useful when the
direction families are equal only after rewriting along the position map. -/
theorem ext_heq {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} (l₁ l₂ : Lens P Q)
    (hA : l₁.toFunA = l₂.toFunA) (hB : l₁.toFunB ≍ l₂.toFunB) : l₁ = l₂ := by
  cases l₁ with
  | mk a₁ b₁ =>
    cases l₂ with
    | mk a₂ b₂ =>
      dsimp only [Lens.toFunA, Lens.toFunB] at hA hB
      cases hA
      cases eq_of_heq hB
      rfl


-- @@ L61-65 verbatim
/-- The identity lens -/
@[implicit_reducible]
protected def id (P : PFunctor.{uA, uB}) : Lens P P where
  toFunA := id
  toFunB := fun _ => id


-- @@ L67-71 verbatim
/-- Composition of lenses -/
def comp {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    (l : Lens Q R) (l' : Lens P Q) : Lens P R where
  toFunA := l.toFunA ∘ l'.toFunA
  toFunB := fun i => (l'.toFunB i) ∘ l.toFunB (l'.toFunA i)


-- @@ L73-73 verbatim
@[inherit_doc] infixl:75 " ∘ₗ " => comp


-- @@ L75-80 verbatim
/-- Apply a polynomial lens to an element of the source polynomial's
extension. The position is sent forward and the payload is pulled back along
the lens's direction map. -/
def mapObj {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}
    (l : Lens P Q) {α : Type v} (x : P.Obj α) : Q.Obj α :=
  ⟨l.toFunA x.1, x.2 ∘ l.toFunB x.1⟩


-- @@ L82-85 verbatim
@[simp]
theorem mapObj_id {P : PFunctor.{uA, uB}} {α : Type v}
    (x : P.Obj α) : mapObj (Lens.id P) x = x :=
  rfl


-- @@ L87-92 expanded
@[simp]
theorem mapObj_comp {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    (g : Lens Q R) (f : Lens P Q) {α : Type v} (x : P.Obj α) :
    mapObj (comp g f) x = mapObj g (mapObj f x) :=
  rfl


-- @@ L94-108 verbatim
/-- Two lenses are equal when they act equally on every source position
equipped with its identity direction labelling. This packages the dependent
position equality and direction-map transport needed by `Lens.ext`. -/
theorem ext_mapObj {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} (l₁ l₂ : Lens P Q)
    (h : ∀ a, mapObj l₁ (⟨a, id⟩ : P.Obj (P.B a)) = mapObj l₂ ⟨a, id⟩) : l₁ = l₂ := by
  let hA : ∀ a, l₁.toFunA a = l₂.toFunA a :=
    fun a => congrArg Sigma.fst (h a)
  refine Lens.ext _ _ hA ?_
  intro a
  apply eq_of_heq
  have hraw : l₁.toFunB a ≍ l₂.toFunB a :=
    (Sigma.ext_iff.mp (h a)).2
  have hcast : (hA a ▸ l₂.toFunB a) ≍ l₂.toFunB a :=
    eqRec_heq_self _ _
  exact hraw.trans hcast.symm


-- @@ L110-114 verbatim
/-- Diagrammatic composition of lenses: `l₁ ⨟ l₂` applies `l₁` first and `l₂`
second, the book's left-to-right composition order, so `l₁ ⨟ l₂ = l₂ ∘ₗ l₁`.
This is the same `⨟` used for machine sequential composition and throughout
`docs/reading`. -/
notation:75 l₁:75 " ⨟ " l₂:76 => Lens.comp l₂ l₁


-- @@ L116-118 expanded
@[simp]
theorem id_comp {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} (f : Lens P Q) :
    comp (Lens.id Q) f = f :=
  rfl


-- @@ L120-122 expanded
@[simp]
theorem comp_id {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} (f : Lens P Q) :
    comp f (Lens.id P) = f :=
  rfl


-- @@ L124-126 expanded
theorem comp_assoc {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    {S : PFunctor.{uA₄, uB₄}} (l : Lens R S) (l' : Lens Q R) (l'' : Lens P Q) :
    comp (comp l l') l'' = comp l (comp l' l'') :=
  rfl


-- @@ L128-137 verbatim
/-- An equivalence between two polynomial functors `P` and `Q`, using lenses.
    This corresponds to an isomorphism in the category `PFunctor` with `Lens` morphisms. -/
@[ext]
structure Equiv (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) where
  /-- The forward lens of the equivalence, from `P` to `Q`. -/
  toLens : Lens P Q
  /-- The backward lens of the equivalence, from `Q` to `P`. -/
  invLens : Lens Q P
  left_inv : comp invLens toLens = Lens.id P := by simp
  right_inv : comp toLens invLens = Lens.id Q := by simp


-- @@ L139-139 verbatim
@[inherit_doc] infix:50 " ≃ₗ " => Equiv


-- @@ L141-141 verbatim
namespace Equiv


-- @@ L143-146 expanded
/-- The identity equivalence on `P`, built from the identity lens in both directions. -/
@[refl]
def refl (P : PFunctor.{uA, uB}) : Equiv P P :=
  ⟨Lens.id P, Lens.id P, rfl, rfl⟩


-- @@ L148-151 expanded
/-- The inverse equivalence, swapping the forward and backward lenses of `e`. -/
@[symm]
def symm {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} (e : Equiv P Q) : Equiv Q P :=
  ⟨e.invLens, e.toLens, e.right_inv, e.left_inv⟩


-- @@ L153-165 expanded
/-- The composite equivalence `P ≃ₗ R` obtained by chaining `e₁ : P ≃ₗ Q` and `e₂ : Q ≃ₗ R`. -/
@[trans]
def trans {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    (e₁ : Equiv P Q) (e₂ : Equiv Q R) : Equiv P R :=
  ⟨comp e₂.toLens e₁.toLens, comp e₁.invLens e₂.invLens,
    by
    rw [comp_assoc]
    rw (occs := [2]) [← comp_assoc]
    simp [e₁.left_inv, e₂.left_inv], by
    rw [comp_assoc]
    rw (occs := [2]) [← comp_assoc]
    simp [e₁.right_inv, e₂.right_inv]⟩


-- @@ L167-167 verbatim
end Equiv


-- @@ L169-177 expanded
/-- Cancel postcomposition with the forward lens of a lens equivalence. -/
theorem cancel_toLens {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    (e : Equiv P Q) {f g : Lens R P} (h : comp e.toLens f = comp e.toLens g) : f = g := by
  calc
    f = comp e.invLens (comp e.toLens f) := by rw [← comp_assoc, e.left_inv, id_comp]
    _ = comp e.invLens (comp e.toLens g) := (congrArg (comp e.invLens ·) h)
    _ = g := by rw [← comp_assoc, e.left_inv, id_comp]


-- @@ L179-181 expanded
/-- The (unique) initial lens from the zero functor to any functor `P`. -/
def initial {P : PFunctor.{uA, uB}} : Lens 0 P :=
  Lens.mk PEmpty.elim fun a => PEmpty.elim a


-- @@ L183-185 expanded
/-- The (unique) terminal lens from any functor `P` to the unit functor `1`. -/
def terminal {P : PFunctor.{uA, uB}} : Lens P 1 :=
  Lens.mk (fun _ => PUnit.unit) fun _ => PEmpty.elim


-- @@ L187-187 verbatim
alias fromZero := initial

-- @@ L188-188 verbatim
alias toOne := terminal


-- @@ L190-193 expanded
/-- Construct a lens from the variable polynomial by selecting a position. The
backward map is uniquely determined by the unit direction of `y`. -/
def fromY {P : PFunctor.{uA, uB}} (a : P.A) : Lens y.{uA₁, uB₁} P :=
  Lens.mk (fun _ => a) fun _ _ => PUnit.unit


-- @@ L195-196 verbatim
@[simp] theorem fromY_toFunA {P : PFunctor.{uA, uB}} (a : P.A) (u : PUnit) :
    (fromY a : Lens y.{uA₁, uB₁} P).toFunA u = a := rfl


-- @@ L198-200 verbatim
@[simp] theorem fromY_toFunB {P : PFunctor.{uA, uB}} (a : P.A) (u : PUnit)
    (d : P.B a) :
    (fromY a : Lens y.{uA₁, uB₁} P).toFunB u d = PUnit.unit := rfl


-- @@ L202-202 verbatim
@[deprecated (since := "2026-08-17")] alias fromX := fromY

-- @@ L203-203 verbatim
@[deprecated (since := "2026-08-17")] alias fromX_toFunA := fromY_toFunA

-- @@ L204-204 verbatim
@[deprecated (since := "2026-08-17")] alias fromX_toFunB := fromY_toFunB


-- @@ L206-210 expanded
/-- Construct a lens into a constant polynomial from its position map. The
backward map is uniquely determined by the empty direction type. -/
def toConst {P : PFunctor.{uA, uB}} {A : Type uA₂} (f : P.A → A) :
    Lens P (C A : PFunctor.{uA₂, uB₁}) :=
  Lens.mk f fun _ => PEmpty.elim


-- @@ L212-214 verbatim
@[simp] theorem toConst_toFunA {P : PFunctor.{uA, uB}} {A : Type uA₂}
    (f : P.A → A) (a : P.A) :
    (toConst f : Lens P (C A : PFunctor.{uA₂, uB₁})).toFunA a = f a := rfl


-- @@ L216-221 expanded
/-- Construct a lens into a linear polynomial from a position map and a choice
of source direction over every position. -/
def toLinear {P : PFunctor.{uA, uB}} {A : Type uA₂} (f : P.A → A) (choose : (a : P.A) → P.B a) :
    Lens P (linear A : PFunctor.{uA₂, uB₁}) :=
  Lens.mk f fun a _ => choose a


-- @@ L223-225 verbatim
@[simp] theorem toLinear_toFunA {P : PFunctor.{uA, uB}} {A : Type uA₂}
    (f : P.A → A) (choose : (a : P.A) → P.B a) (a : P.A) :
    (toLinear f choose : Lens P (linear A : PFunctor.{uA₂, uB₁})).toFunA a = f a := rfl


-- @@ L227-229 verbatim
@[simp] theorem toLinear_toFunB {P : PFunctor.{uA, uB}} {A : Type uA₂}
    (f : P.A → A) (choose : (a : P.A) → P.B a) (a : P.A) (u : PUnit) :
    (toLinear f choose : Lens P (linear A : PFunctor.{uA₂, uB₁})).toFunB a u = choose a := rfl


-- @@ L231-234 expanded
/-- Left injection lens `inl : P → P + Q` -/
def inl {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}} :
    Lens.{uA₁, uB, max uA₁ uA₂, uB} P (P + Q) :=
  Lens.mk Sum.inl fun _ => id


-- @@ L236-239 expanded
/-- Right injection lens `inr : Q → P + Q` -/
def inr {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}} :
    Lens.{uA₂, uB, max uA₁ uA₂, uB} Q (P + Q) :=
  Lens.mk Sum.inr fun _ => id


-- @@ L241-247 expanded
/-- Copairing of lenses `[l₁, l₂]ₗ : P + Q → R` -/
def sumPair {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}} {R : PFunctor.{uA₃, uB₃}}
    (l₁ : Lens P R) (l₂ : Lens Q R) : Lens.{max uA₁ uA₂, uB, uA₃, uB₃} (P + Q) R :=
  Lens.mk (Sum.elim l₁.toFunA l₂.toFunA) fun
    | .inl pa => l₁.toFunB pa
    | .inr qa => l₂.toFunB qa


-- @@ L249-255 expanded
/-- Parallel application of lenses for coproduct `l₁ ⊎ l₂ : P + Q → R + W` -/
def sumMap {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₁}} {R : PFunctor.{uA₃, uB₃}}
    {W : PFunctor.{uA₄, uB₃}} (l₁ : Lens P R) (l₂ : Lens Q W) :
    Lens.{max uA₁ uA₂, uB₁, max uA₃ uA₄, uB₃} (P + Q) (R + W) :=
  Lens.mk (Sum.map l₁.toFunA l₂.toFunA) fun
    | .inl pa => l₁.toFunB pa
    | .inr qa => l₂.toFunB qa


-- @@ L257-262 expanded
/-- Dependent copairing of lenses over `sigma`: `Σ i, F i → R`. -/
def sigmaExists {I : Type v} {F : I → PFunctor.{uA₁, uB₁}} {R : PFunctor.{uA₂, uB₂}}
    (l : ∀ i, Lens (F i) R) : Lens (sigma F) R :=
  Lens.mk (fun ⟨i, fa⟩ => (l i).toFunA fa) (fun ⟨i, fa⟩ => (l i).toFunB fa)


-- @@ L264-269 expanded
/-- Pointwise mapping of lenses over `sigma`. -/
def sigmaMap {I : Type v} {F : I → PFunctor.{uA₁, uB₁}} {G : I → PFunctor.{uA₂, uB₂}}
    (l : ∀ i, Lens (F i) (G i)) : Lens (sigma F) (sigma G) :=
  Lens.mk (fun ⟨i, fa⟩ => ⟨i, (l i).toFunA fa⟩) (fun ⟨i, fa⟩ => (l i).toFunB fa)


-- @@ L271-274 expanded
/-- Projection lens `fst : P * Q → P` -/
def fst {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} :
    Lens.{max uA₁ uA₂, max uB₁ uB₂, uA₁, uB₁} (P * Q) P :=
  Lens.mk Prod.fst fun _ => Sum.inl


-- @@ L276-279 expanded
/-- Projection lens `snd : P * Q → Q` -/
def snd {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} :
    Lens.{max uA₁ uA₂, max uB₁ uB₂, uA₂, uB₂} (P * Q) Q :=
  Lens.mk Prod.snd fun _ => Sum.inr


-- @@ L281-286 expanded
/-- Pairing of lenses `⟨l₁, l₂⟩ₗ : P → Q * R` -/
def prodPair {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    (l₁ : Lens P Q) (l₂ : Lens P R) : Lens.{uA₁, uB₁, max uA₂ uA₃, max uB₂ uB₃} P (Q * R) :=
  Lens.mk (fun p => (l₁.toFunA p, l₂.toFunA p)) (fun p => Sum.elim (l₁.toFunB p) (l₂.toFunB p))


-- @@ L288-293 expanded
/-- Parallel application of lenses for product `l₁ ×ₗ l₂ : P * Q → R * W` -/
def prodMap {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    {W : PFunctor.{uA₄, uB₄}} (l₁ : Lens P R) (l₂ : Lens Q W) :
    Lens.{max uA₁ uA₂, max uB₁ uB₂, max uA₃ uA₄, max uB₃ uB₄} (P * Q) (R * W) :=
  Lens.mk (fun pq => (l₁.toFunA pq.1, l₂.toFunA pq.2))
    (fun pq => Sum.elim (Sum.inl ∘ l₁.toFunB pq.1) (Sum.inr ∘ l₂.toFunB pq.2))


-- @@ L295-300 expanded
/-- Dependent pairing of lenses into a `pi`: `P → ∀ i, F i`. -/
def piForall {I : Type v} {P : PFunctor.{uA₁, uB₁}} {F : I → PFunctor.{uA₂, uB₂}}
    (l : ∀ i, Lens P (F i)) : Lens P (pi F) :=
  Lens.mk (fun pa i => (l i).toFunA pa) (fun pa ⟨i, fb⟩ => (l i).toFunB pa fb)


-- @@ L302-307 expanded
/-- Pointwise mapping of lenses over `pi`. -/
def piMap {I : Type v} {F : I → PFunctor.{uA₁, uB₁}} {G : I → PFunctor.{uA₂, uB₂}}
    (l : ∀ i, Lens (F i) (G i)) : Lens (pi F) (pi G) :=
  Lens.mk (fun fa i => (l i).toFunA (fa i)) (fun fa ⟨i, gb⟩ => ⟨i, (l i).toFunB (fa i) gb⟩)


-- @@ L309-317 expanded
/-- Apply lenses to both sides of a composition: `l₁ ◃ₗ l₂ : (P ◃ Q ⇆ R ◃ W)` -/
def compMap {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    {W : PFunctor.{uA₄, uB₄}} (l₁ : Lens P R) (l₂ : Lens Q W) :
    Lens.{max uA₁ uA₂ uB₁, max uB₁ uB₂, max uA₃ uA₄ uB₃, max uB₃ uB₄} (P ◃ Q) (R ◃ W) :=
  Lens.mk (fun ⟨pa, pq⟩ => ⟨l₁.toFunA pa, fun rb' => l₂.toFunA (pq (l₁.toFunB pa rb'))⟩)
    (fun ⟨pa, pq⟩ ⟨rb, wc⟩ =>
      let pb := l₁.toFunB pa rb
      let qc := l₂.toFunB (pq pb) wc
      ⟨pb, qc⟩)


-- @@ L319-325 expanded
/-- Apply lenses to both sides of a tensor / parallel product: `l₁ ⊗ₗ l₂ : (P ⊗ Q ⇆ R ⊗ W)` -/
@[implicit_reducible]
def tensorMap {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    {W : PFunctor.{uA₄, uB₄}} (l₁ : Lens P R) (l₂ : Lens Q W) :
    Lens.{max uA₁ uA₂, max uB₁ uB₂, max uA₃ uA₄, max uB₃ uB₄} (P ⊗ Q) (R ⊗ W) :=
  Lens.mk (Prod.map l₁.toFunA l₂.toFunA) fun (pa, qa) => Prod.map (l₁.toFunB pa) (l₂.toFunB qa)


-- @@ L327-329 expanded
/-- Lens to introduce `y` on the right: `P → P ◃ y` -/
def tildeR {P : PFunctor.{uA, uB}} : Lens P (P ◃ y) :=
  Lens.mk (fun a => ⟨a, fun _ => PUnit.unit⟩) (fun _a => fun ⟨b, _⟩ => b)


-- @@ L331-333 expanded
/-- Lens to introduce `y` on the left: `P → y ◃ P` -/
def tildeL {P : PFunctor.{uA, uB}} : Lens P (y ◃ P) :=
  Lens.mk (fun a => ⟨PUnit.unit, fun _ => a⟩) (fun _a => fun ⟨_, b⟩ => b)


-- @@ L335-337 expanded
/-- Lens from `P ◃ y` to `P` -/
def invTildeR {P : PFunctor.{uA, uB}} : Lens (P ◃ y) P :=
  Lens.mk (fun a => a.1) (fun _ b => ⟨b, PUnit.unit⟩)


-- @@ L339-341 expanded
/-- Lens from `y ◃ P` to `P` -/
def invTildeL {P : PFunctor.{uA, uB}} : Lens (y ◃ P) P :=
  Lens.mk (fun ⟨_, f⟩ => f PUnit.unit) (fun _ b => ⟨PUnit.unit, b⟩)


-- @@ L343-343 verbatim
@[inherit_doc] infixl:75 " ◃ₗ " => compMap

-- @@ L344-344 verbatim
@[inherit_doc] infixl:75 " ×ₗ " => prodMap

-- @@ L345-345 verbatim
@[inherit_doc] infixl:75 " ⊎ₗ " => sumMap

-- @@ L346-346 verbatim
@[inherit_doc] infixl:75 " ⊗ₗ " => tensorMap

-- @@ L347-348 verbatim
/-- Notation for the copairing `sumPair l₁ l₂` of two lenses out of a sum. -/
notation "[" l₁ "," l₂ "]ₗ" => sumPair l₁ l₂

-- @@ L349-350 verbatim
/-- Notation for the pairing `prodPair l₁ l₂` of two lenses into a product. -/
notation "⟨" l₁ "," l₂ "⟩ₗ" => prodPair l₁ l₂


-- @@ L352-357 verbatim
set_option linter.checkUnivs false in
/-- The type of lenses from a polynomial functor `P` to `y` -/
-- `Lens.enclose`'s two universe pairs are the independent domain (`uA`/`uB`) and
-- codomain (`uA₁`/`uB₁`) position/direction universes, kept independent.
def enclose (P : PFunctor.{uA, uB}) : Type max uA uA₁ uB uB₁ :=
  Lens P y.{uA₁, uB₁}


-- @@ L359-365 expanded
/-- The transition lens `δ : Sy^S ⇆ Sy^S ◃ Sy^S` on the self-monomial state
polynomial (Spivak–Niu Example 6.44): `δ = (id, tgt, run)` remembers the start
state, relabels each direction by the state it targets, and composes two hops
into one. It is the comultiplication of the state comonoid `stateComonoid S`, and
the helper behind `speedup`. -/
def fixState {S : Type u} : Lens (selfMonomial S) (selfMonomial S ◃ selfMonomial S) :=
  Lens.mk (fun s₀ => ⟨s₀, fun s₁ => s₁⟩) (fun _s₀ => fun ⟨_s₁, s₂⟩ => s₂)


-- @@ L367-370 expanded
/-- The `speedup` lens operation: `Lens (S y^S) P → Lens (S y^S) (P ◃ P)` -/
def speedup {S : Type u} {P : PFunctor.{uA, uB}} (l : Lens (selfMonomial S) P) :
    Lens (selfMonomial S) (P ◃ P) :=
  comp (compMap l l) fixState


-- @@ L372-374 verbatim
section Coprod

-- Note the universe levels for `uB` in order to apply coproduct / sum

-- @@ L375-376 verbatim
variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₁}}
  {R : PFunctor.{uA₃, uB₃}} {W : PFunctor.{uA₄, uB₃}} {V : PFunctor.{uA₅, uB₅}}


-- @@ L378-380 expanded
@[simp]
theorem sumMap_comp_inl (l₁ : Lens P R) (l₂ : Lens Q W) :
    (comp (sumMap l₁ l₂) Lens.inl) = (comp Lens.inl l₁) :=
  rfl


-- @@ L382-384 expanded
@[simp]
theorem sumMap_comp_inr (l₁ : Lens P R) (l₂ : Lens Q W) :
    (comp (sumMap l₁ l₂) Lens.inr) = (comp Lens.inr l₂) :=
  rfl


-- @@ L386-388 expanded
theorem sumPair_comp_sumMap (l₁ : Lens P R) (l₂ : Lens Q W) (f : Lens R V) (g : Lens W V) :
    comp (Lens.sumPair f g) (sumMap l₁ l₂) = Lens.sumPair (comp f l₁) (comp g l₂) := by
  ext a <;> rcases a with a | a <;> rfl


-- @@ L390-392 expanded
@[simp]
theorem sumPair_comp_inl (f : Lens P R) (g : Lens Q R) : comp (Lens.sumPair f g) Lens.inl = f :=
  rfl


-- @@ L394-396 expanded
@[simp]
theorem sumPair_comp_inr (f : Lens P R) (g : Lens Q R) : comp (Lens.sumPair f g) Lens.inr = g :=
  rfl


-- @@ L398-400 expanded
theorem comp_inl_inr (h : Lens.{max uA₁ uA₂, uB₁, uA₃, uB₃} (P + Q) R) :
    Lens.sumPair (comp h Lens.inl) (comp h Lens.inr) = h := by ext a <;> rcases a <;> rfl


-- @@ L402-405 verbatim
@[simp]
theorem sumMap_id :
    Lens.sumMap (Lens.id P) (Lens.id Q) = Lens.id.{max uA₁ uA₂, uB₁} (P + Q) := by
  ext a <;> rcases a <;> rfl


-- @@ L407-410 verbatim
@[simp]
theorem sumPair_inl_inr :
    Lens.sumPair Lens.inl Lens.inr = Lens.id.{max uA₁ uA₂, uB₁} (P + Q) := by
  ext a <;> rcases a <;> rfl


-- @@ L412-412 verbatim
namespace Equiv


-- @@ L414-422 verbatim
/-- Commutativity of coproduct -/
def sumComm (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) :
    Lens.Equiv.{max uA₁ uA₂, uB, max uA₁ uA₂, uB} (P + Q) (Q + P) where
  toLens := Lens.sumPair Lens.inr Lens.inl
  invLens := Lens.sumPair Lens.inr Lens.inl
  left_inv := by
    ext a <;> rcases a with a | a <;> rfl
  right_inv := by
    ext a <;> rcases a with a | a <;> rfl


-- @@ L424-424 verbatim
variable {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}} {R : PFunctor.{uA₃, uB}}


-- @@ L426-428 verbatim
@[simp]
theorem sumComm_symm :
    (sumComm P Q).symm = sumComm Q P := rfl


-- @@ L430-450 expanded
/-- Associativity of coproduct -/
def sumAssoc : Lens.Equiv.{max uA₁ uA₂ uA₃, uB, max uA₁ uA₂ uA₃, uB} ((P + Q) + R) (P + (Q + R))
    where
  toLens := -- Maps (P + Q) + R to P + (Q + R)
    Lens.sumPair
      (Lens.sumPair
        (Lens.inl) -- Maps P to P + (Q + R) via Sum.inl
          
        (comp Lens.inr Lens.inl) -- Maps Q to P + (Q + R) via Sum.inr ∘ Sum.inl
          )
      (comp Lens.inr Lens.inr) -- Maps R to P + (Q + R) via Sum.inr ∘ Sum.inr
        
  invLens := -- Maps P + (Q + R) to (P + Q) + R
    Lens.sumPair
      (comp Lens.inl Lens.inl) -- Maps P to (P + Q) + R via Sum.inl ∘ Sum.inl
        
      (Lens.sumPair
        (comp Lens.inl Lens.inr) -- Maps Q to (P + Q) + R via Sum.inl ∘ Sum.inr
          
        (Lens.inr) -- Maps R to (P + Q) + R via Sum.inr
          )
  left_inv := by ext a <;> rcases a with (a | a) | a <;> rfl
  right_inv := by ext a <;> rcases a with a | a | a <;> rfl


-- @@ L452-464 verbatim
/-- Coproduct with `0` is identity (right) -/
def sumZero :
    Lens.Equiv.{max uA uA₁, uB, uA₁, uB} (P + (0 : PFunctor.{uA, uB})) P where
  toLens := Lens.sumPair (Lens.id P) Lens.initial
  invLens := Lens.inl
  left_inv := by
    ext a <;> rcases a with a | a
    · rfl
    · exact PEmpty.elim a
    · rfl
    · exact PEmpty.elim a
  right_inv := by
    ext <;> rfl


-- @@ L466-478 verbatim
/-- Coproduct with `0` is identity (left) -/
def zeroCoprod :
    Lens.Equiv.{max uA uA₁, uB, uA₁, uB} ((0 : PFunctor.{uA, uB}) + P) P where
  toLens := Lens.sumPair Lens.initial (Lens.id P)
  invLens := Lens.inr
  left_inv := by
    ext a <;> rcases a with a | a
    · exact PEmpty.elim a
    · rfl
    · exact PEmpty.elim a
    · rfl
  right_inv := by
    ext <;> rfl


-- @@ L480-480 verbatim
end Equiv


-- @@ L482-482 verbatim
end Coprod


-- @@ L484-484 verbatim
section Prod


-- @@ L486-487 verbatim
variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
  {W : PFunctor.{uA₄, uB₄}} {V : PFunctor.{uA₅, uB₅}}


-- @@ L489-491 expanded
@[simp]
theorem fst_comp_prodMap (l₁ : Lens P R) (l₂ : Lens Q W) :
    comp Lens.fst (prodMap l₁ l₂) = comp l₁ Lens.fst :=
  rfl


-- @@ L493-495 expanded
@[simp]
theorem snd_comp_prodMap (l₁ : Lens P R) (l₂ : Lens Q W) :
    comp Lens.snd (prodMap l₁ l₂) = comp l₂ Lens.snd :=
  rfl


-- @@ L497-501 expanded
theorem prodMap_comp_prodPair (l₁ : Lens Q W) (l₂ : Lens R V) (f : Lens P Q) (g : Lens P R) :
    comp (prodMap l₁ l₂) (Lens.prodPair f g) = Lens.prodPair (comp l₁ f) (comp l₂ g) :=
  by
  ext a x
  · rfl
  · cases x <;> rfl


-- @@ L503-505 expanded
@[simp]
theorem fst_comp_prodPair (f : Lens P Q) (g : Lens P R) : comp Lens.fst (Lens.prodPair f g) = f :=
  rfl


-- @@ L507-509 expanded
@[simp]
theorem snd_comp_prodPair (f : Lens P Q) (g : Lens P R) : comp Lens.snd (Lens.prodPair f g) = g :=
  rfl


-- @@ L511-515 expanded
theorem comp_fst_snd (h : Lens.{uA₁, uB₁, max uA₂ uA₃, max uB₂ uB₃} P (Q * R)) :
    Lens.prodPair (comp Lens.fst h) (comp Lens.snd h) = h :=
  by
  ext a x
  · rfl
  · cases x <;> rfl


-- @@ L517-522 verbatim
@[simp]
theorem prodMap_id :
    Lens.prodMap (Lens.id P) (Lens.id Q) = Lens.id.{max uA₁ uA₂, max uB₁ uB₂} (P * Q) := by
  ext a x
  · rfl
  · cases x <;> rfl


-- @@ L524-529 verbatim
@[simp]
theorem prodPair_fst_snd :
    Lens.prodPair Lens.fst Lens.snd = Lens.id.{max uA₁ uA₂, max uB₁ uB₂} (P * Q) := by
  ext a x
  · rfl
  · cases x <;> rfl


-- @@ L531-531 verbatim
namespace Equiv


-- @@ L533-545 expanded
/-- Commutativity of product -/
def prodComm (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) :
    Lens.Equiv.{max uA₁ uA₂, max uB₁ uB₂, max uA₁ uA₂, max uB₁ uB₂} (P * Q) (Q * P)
    where
  toLens := Lens.mk Prod.swap fun _ => Sum.elim Sum.inr Sum.inl
  invLens := Lens.mk Prod.swap fun _ => Sum.elim Sum.inr Sum.inl
  left_inv := by
    ext _ b
    · rfl
    · cases b <;> rfl
  right_inv := by
    ext _ b
    · rfl
    · cases b <;> rfl


-- @@ L547-548 verbatim
@[simp]
theorem prodComm_symm : (prodComm P Q).symm = prodComm Q P := rfl


-- @@ L550-550 verbatim
variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}


-- @@ L552-570 expanded
/-- Associativity of product -/
def prodAssoc :
    Lens.Equiv.{max uA₁ uA₂ uA₃, max uB₁ uB₂ uB₃, max uA₁ uA₂ uA₃, max uB₁ uB₂ uB₃} ((P * Q) * R)
      (P * (Q * R))
    where
  toLens :=
    Lens.mk (_root_.Equiv.prodAssoc P.A Q.A R.A).toFun
      (fun _ => (_root_.Equiv.sumAssoc _ _ _).invFun)
  invLens :=
    Lens.mk (_root_.Equiv.prodAssoc P.A Q.A R.A).invFun (fun _ => _root_.Equiv.sumAssoc _ _ _)
  left_inv := by
    ext _ b
    · rfl
    · rcases b with b | _
      · cases b <;> rfl
      · rfl
  right_inv := by
    ext _ b
    · rfl
    · rcases b with _ | b
      · rfl
      · cases b <;> rfl


-- @@ L572-584 expanded
/-- Product with `1` is identity (right) -/
def prodOne : Lens.Equiv.{max uA₁ uA₂, max uB₁ uB₂, uA₁, uB₁} (P * (1 : PFunctor.{uA₂, uB₂})) P
    where
  toLens := Lens.mk Prod.fst fun _ => Sum.inl
  invLens := Lens.mk (·, PUnit.unit) fun _ => Sum.elim id PEmpty.elim
  left_inv := by
    ext _ b
    · rfl
    · rcases b with _ | b
      · rfl
      · cases b
  right_inv := by ext <;> rfl


-- @@ L586-598 expanded
/-- Product with `1` is identity (left) -/
def oneProd : Lens.Equiv.{max uA₁ uA₂, max uB₁ uB₂, uA₁, uB₁} ((1 : PFunctor.{uA₂, uB₂}) * P) P
    where
  toLens := Lens.mk Prod.snd fun _ => Sum.inr
  invLens := Lens.mk (PUnit.unit, ·) fun _ => Sum.elim PEmpty.elim id
  left_inv := by
    ext _ b
    · rfl
    · rcases b with b | _
      · cases b
      · rfl
  right_inv := by ext <;> rfl


-- @@ L600-608 expanded
/-- Product with `0` is zero (right) -/
def prodZero : Lens.Equiv.{max uA₁ uA₂, max uB₁ uB₂, uA₁, uB₁} (P * (0 : PFunctor.{uA₂, uB₂})) 0
    where
  toLens := Lens.mk (fun a => PEmpty.elim a.2) fun _ => PEmpty.elim
  invLens := Lens.mk PEmpty.elim fun pe => PEmpty.elim pe
  left_inv := by ext ⟨_, a⟩ _ <;> exact PEmpty.elim a
  right_inv := by ext ⟨_, _⟩


-- @@ L610-618 expanded
/-- Product with `0` is zero (left) -/
def zeroProd : Lens.Equiv.{max uA₁ uA₂, max uB₁ uB₂, uA₁, uB₁} ((0 : PFunctor.{uA₂, uB₂}) * P) 0
    where
  toLens := Lens.mk (fun (pa, _) => PEmpty.elim pa) fun _ => PEmpty.elim
  invLens := Lens.mk PEmpty.elim fun pe => PEmpty.elim pe
  left_inv := by ext ⟨a, _⟩ <;> exact PEmpty.elim a
  right_inv := by ext ⟨_, _⟩


-- @@ L620-620 verbatim
variable {R : PFunctor.{uA₃, uB₂}}


-- @@ L622-631 expanded
/-- Left distributive law for product over coproduct -/
def prodCoprodDistrib :
    Lens.Equiv.{max uA₁ uA₂ uA₃, max uB₁ uB₂, max uA₁ uA₂ uA₃, max uB₁ uB₂} (P * (Q + R))
      ((P * Q) + (P * R))
    where
  toLens :=
    Lens.mk (fun (p, qr) => qr.map (p, ·) (p, ·))
      (fun
        | ⟨_, .inl _⟩ | ⟨_, .inr _⟩ => id)
  invLens :=
    Lens.mk (Sum.elim (Prod.map id Sum.inl) (Prod.map id Sum.inr))
      (fun
        | .inl _ | .inr _ => id)
  left_inv := by ext ⟨_, qr⟩ <;> cases qr <;> rfl
  right_inv := by ext pqpr <;> cases pqpr <;> rfl


-- @@ L633-642 expanded
/-- Right distributive law for coproduct over product -/
def sumProdDistrib :
    Lens.Equiv.{max uA₁ uA₂ uA₃, max uB₁ uB₂, max uA₁ uA₂ uA₃, max uB₁ uB₂} ((Q + R) * P)
      ((Q * P) + (R * P))
    where
  toLens :=
    Lens.mk (fun (qr, p) => qr.map (·, p) (·, p))
      (fun
        | ⟨.inl _, _⟩ | ⟨.inr _, _⟩ => id)
  invLens :=
    Lens.mk (Sum.elim (Prod.map Sum.inl id) (Prod.map Sum.inr id))
      (fun
        | .inl _ | .inr _ => id)
  left_inv := by ext ⟨qr, _⟩ <;> cases qr <;> rfl
  right_inv := by ext qprp <;> cases qprp <;> rfl


-- @@ L644-644 verbatim
end Equiv


-- @@ L646-646 verbatim
end Prod


-- @@ L648-648 verbatim
section Comp


-- @@ L650-650 verbatim
variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}


-- @@ L652-655 expanded
@[simp]
theorem compMap_id : compMap (Lens.id P) (Lens.id Q) = Lens.id (P ◃ Q) := by
  ext ⟨_, _⟩ ⟨_, _⟩ <;> rfl


-- @@ L657-660 expanded
theorem compMap_comp {P' : PFunctor.{uA₄, uB₄}} {Q' : PFunctor.{uA₅, uB₅}}
    {R' : PFunctor.{uA₆, uB₆}} (l₁ : Lens P P') (l₂ : Lens Q Q') (l₁' : Lens P' R)
    (l₂' : Lens Q' R') :
    compMap (comp l₁' l₁) (comp l₂' l₂) = comp (compMap l₁' l₂') (compMap l₁ l₂) :=
  rfl


-- @@ L662-662 verbatim
namespace Equiv


-- @@ L664-671 expanded
/-- Associativity of composition -/
def compAssoc : Equiv ((P ◃ Q) ◃ R) (P ◃ (Q ◃ R))
    where
  toLens :=
    Lens.mk (fun ⟨⟨pa, qf⟩, rf⟩ => ⟨pa, fun pb => ⟨qf pb, fun qb => rf ⟨pb, qb⟩⟩⟩)
      (fun _ ⟨pb, ⟨qb, rb⟩⟩ => ⟨⟨pb, qb⟩, rb⟩)
  invLens :=
    Lens.mk (fun ⟨pa, g⟩ => ⟨⟨pa, fun pb => (g pb).1⟩, fun ⟨pb, qb⟩ => (g pb).2 qb⟩)
      (fun _ ⟨⟨pb, qb⟩, rb⟩ => ⟨pb, ⟨qb, rb⟩⟩)
  left_inv := rfl
  right_inv := rfl


-- @@ L673-678 expanded
/-- Composition with `y` is identity (right) -/
def compY : Equiv (P ◃ y) P where
  toLens := invTildeR
  invLens := tildeR
  left_inv := rfl
  right_inv := rfl


-- @@ L680-685 expanded
/-- Composition with `y` is identity (left) -/
def yComp : Equiv (y ◃ P) P where
  toLens := invTildeL
  invLens := tildeL
  left_inv := rfl
  right_inv := rfl


-- @@ L687-687 verbatim
@[deprecated (since := "2026-08-17")] alias compX := compY

-- @@ L688-688 verbatim
@[deprecated (since := "2026-08-17")] alias XComp := yComp


-- @@ L690-703 expanded
/-- Distributivity of composition over coproduct on the right -/
def sumCompDistrib {R : PFunctor.{uA₃, uB₂}} :
    Lens.Equiv.{max uA₁ uA₂ uA₃ uB₂, max uB₁ uB₂, max uA₁ uA₂ uA₃ uB₂, max uB₁ uB₂}
      ((Q + R : PFunctor.{max uA₂ uA₃, uB₂}) ◃ P) ((Q ◃ P) + (R ◃ P))
    where
  toLens :=
    Lens.mk
      (fun
        | ⟨.inl qa, pf⟩ => .inl ⟨qa, pf⟩
        | ⟨.inr ra, pf⟩ => .inr ⟨ra, pf⟩)
      (fun
        | ⟨.inl _, _⟩ | ⟨.inr _, _⟩ => id)
  invLens :=
    Lens.mk
      (fun
        | .inl ⟨qa, pf⟩ => ⟨.inl qa, pf⟩
        | .inr ⟨ra, pf⟩ => ⟨.inr ra, pf⟩)
      (fun
        | .inl _ | .inr _ => id)
  left_inv := by ext ⟨qr, _⟩ <;> cases qr <;> rfl
  right_inv := by ext qprp <;> cases qprp <;> rfl


-- @@ L705-705 verbatim
end Equiv


-- @@ L707-707 verbatim
end Comp


-- @@ L709-709 verbatim
section Tensor


-- @@ L711-711 verbatim
variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}


-- @@ L713-715 expanded
@[simp]
theorem tensorMap_id : tensorMap (Lens.id P) (Lens.id Q) = Lens.id (P ⊗ Q) :=
  rfl


-- @@ L717-720 expanded
theorem tensorMap_comp {P' : PFunctor.{uA₄, uB₄}} {Q' : PFunctor.{uA₅, uB₅}}
    {R' : PFunctor.{uA₆, uB₆}} (l₁ : Lens P P') (l₂ : Lens Q Q') (l₁' : Lens P' R)
    (l₂' : Lens Q' R') :
    tensorMap (comp l₁' l₁) (comp l₂' l₂) = comp (tensorMap l₁' l₂') (tensorMap l₁ l₂) :=
  rfl


-- @@ L722-722 verbatim
namespace Equiv


-- @@ L724-729 expanded
/-- Commutativity of tensor product -/
def tensorComm (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) : Equiv (P ⊗ Q) (Q ⊗ P)
    where
  toLens := Lens.mk Prod.swap (fun _ => Prod.swap)
  invLens := Lens.mk Prod.swap (fun _ => Prod.swap)
  left_inv := rfl
  right_inv := rfl


-- @@ L731-738 expanded
/-- Associativity of tensor product -/
def tensorAssoc : Equiv ((P ⊗ Q) ⊗ R) (P ⊗ (Q ⊗ R))
    where
  toLens :=
    Lens.mk (_root_.Equiv.prodAssoc _ _ _).toFun (fun _ => (_root_.Equiv.prodAssoc _ _ _).invFun)
  invLens :=
    Lens.mk (_root_.Equiv.prodAssoc _ _ _).invFun (fun _ => (_root_.Equiv.prodAssoc _ _ _).toFun)
  left_inv := rfl
  right_inv := rfl


-- @@ L740-744 verbatim
@[simp]
theorem tensorAssoc_toFunA (position : ((P ⊗ Q) ⊗ R).A) :
    (tensorAssoc (P := P) (Q := Q) (R := R)).toLens.toFunA position =
      (position.1.1, (position.1.2, position.2)) :=
  rfl


-- @@ L746-753 verbatim
@[simp]
theorem tensorAssoc_toFunB (position : ((P ⊗ Q) ⊗ R).A)
    (direction : (P ⊗ (Q ⊗ R)).B
      ((tensorAssoc (P := P) (Q := Q) (R := R)).toLens.toFunA position)) :
    (tensorAssoc (P := P) (Q := Q) (R := R)).toLens.toFunB
        position direction =
      ((direction.1, direction.2.1), direction.2.2) :=
  rfl


-- @@ L755-760 expanded
/-- Tensor product with `y` is identity (right) -/
def tensorY : Equiv (P ⊗ y) P
    where
  toLens := Lens.mk Prod.fst fun _ => (·, PUnit.unit)
  invLens := Lens.mk (·, PUnit.unit) fun _ => Prod.fst
  left_inv := rfl
  right_inv := rfl


-- @@ L762-767 expanded
/-- Tensor product with `y` is identity (left) -/
def yTensor : Equiv (y ⊗ P) P
    where
  toLens := Lens.mk Prod.snd fun _ => (PUnit.unit, ·)
  invLens := Lens.mk (PUnit.unit, ·) fun _ => Prod.snd
  left_inv := rfl
  right_inv := rfl


-- @@ L769-769 verbatim
@[deprecated (since := "2026-08-17")] alias tensorX := tensorY

-- @@ L770-770 verbatim
@[deprecated (since := "2026-08-17")] alias xTensor := yTensor


-- @@ L772-779 expanded
/-- Tensor product with `0` is zero (left) -/
def zeroTensor : Equiv (0 ⊗ P) 0
    where
  toLens := Lens.mk (fun a => PEmpty.elim a.1) fun _ => PEmpty.elim
  invLens := Lens.mk PEmpty.elim fun a => PEmpty.elim a
  left_inv := by ext ⟨a, _⟩ <;> exact PEmpty.elim a
  right_inv := by ext a <;> exact PEmpty.elim a


-- @@ L781-788 expanded
/-- Tensor product with `0` is zero (right) -/
def tensorZero : Equiv (P ⊗ 0) 0
    where
  toLens := Lens.mk (fun a => PEmpty.elim a.2) fun _ => PEmpty.elim
  invLens := Lens.mk PEmpty.elim fun a => PEmpty.elim a
  left_inv := by ext ⟨_, b⟩ <;> exact PEmpty.elim b
  right_inv := by ext a <;> exact PEmpty.elim a


-- @@ L790-790 verbatim
variable {R : PFunctor.{uA₃, uB₂}}


-- @@ L792-801 expanded
/-- Left distributivity of tensor product over coproduct -/
def tensorCoprodDistrib :
    Lens.Equiv.{max uA₁ uA₂ uA₃, max uB₁ uB₂, max uA₁ uA₂ uA₃, max uB₁ uB₂}
      (P ⊗ (Q + R : PFunctor.{max uA₂ uA₃, uB₂})) ((P ⊗ Q) + (P ⊗ R))
    where
  toLens :=
    Lens.mk (fun (p, qr) => qr.map (p, ·) (p, ·))
      (fun
        | ⟨_, .inl _⟩ | ⟨_, .inr _⟩ => id)
  invLens :=
    Lens.mk (Sum.elim (Prod.map id Sum.inl) (Prod.map id Sum.inr))
      (fun
        | .inl _ | .inr _ => id)
  left_inv := by ext ⟨_, qr⟩ <;> cases qr <;> rfl
  right_inv := by ext pqpr <;> cases pqpr <;> rfl


-- @@ L803-812 expanded
/-- Right distributivity of tensor product over coproduct -/
def sumTensorDistrib :
    Equiv ((Q + R : PFunctor.{max uA₂ uA₃, uB₂}) ⊗ P)
      ((Q ⊗ P) + (R ⊗ P) : PFunctor.{max uA₁ uA₂ uA₃, max uB₁ uB₂})
    where
  toLens :=
    Lens.mk (fun (qr, p) => qr.map (·, p) (·, p))
      (fun
        | ⟨.inl _, _⟩ | ⟨.inr _, _⟩ => id)
  invLens :=
    Lens.mk (Sum.elim (Prod.map Sum.inl id) (Prod.map Sum.inr id))
      (fun
        | .inl _ | .inr _ => id)
  left_inv := by ext ⟨qr, _⟩ <;> cases qr <;> rfl
  right_inv := by ext qprp <;> cases qprp <;> rfl


-- @@ L814-814 verbatim
end Equiv


-- @@ L816-819 verbatim
/-- The unique comparison between two possibly differently instantiated
copies of the common tensor/composition unit `y`. -/
def unitComparison : Lens y.{uA₁, uB₁} y.{uA₂, uB₂} :=
  Lens.fromY PUnit.unit


-- @@ L821-830 expanded
/-- Naturality of the left tensor unitor. The unit component is the canonical
comparison between the independently instantiated source and target copies of
`y`. -/
theorem yTensor_natural {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} (f : Lens P Q) :
    comp f (Equiv.yTensor (P := P)).toLens =
      comp (Equiv.yTensor (P := Q)).toLens
        (tensorMap (unitComparison : Lens y.{uA₁, uB₁} y.{uA₂, uB₂}) f) :=
  by rfl


-- @@ L832-842 expanded
/-- Naturality of the right tensor unitor. The unit component is the canonical
comparison between the independently instantiated source and target copies of
`y`. -/
theorem tensorY_natural {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} (f : Lens P Q) :
    comp f (Equiv.tensorY (P := P)).toLens =
      comp (Equiv.tensorY (P := Q)).toLens
        (tensorMap f (unitComparison : Lens y.{uA₁, uB₁} y.{uA₂, uB₂})) :=
  by rfl


-- @@ L844-844 verbatim
@[deprecated (since := "2026-08-17")] alias xTensor_natural := yTensor_natural

-- @@ L845-845 verbatim
@[deprecated (since := "2026-08-17")] alias tensorX_natural := tensorY_natural


-- @@ L847-858 expanded
/-- Naturality of the tensor associator across lenses whose source and target
polynomials may occupy six independent universe pairs. -/
theorem tensorAssoc_natural {P₁ : PFunctor.{uA₁, uB₁}} {P₂ : PFunctor.{uA₂, uB₂}}
    {Q₁ : PFunctor.{uA₃, uB₃}} {Q₂ : PFunctor.{uA₄, uB₄}} {R₁ : PFunctor.{uA₅, uB₅}}
    {R₂ : PFunctor.{uA₆, uB₆}} (f : Lens P₁ P₂) (g : Lens Q₁ Q₂) (h : Lens R₁ R₂) :
    comp (tensorMap f (tensorMap g h)) (Equiv.tensorAssoc (P := P₁) (Q := Q₁) (R := R₁)).toLens =
      comp (Equiv.tensorAssoc (P := P₂) (Q := Q₂) (R := R₂)).toLens (tensorMap (tensorMap f g) h) :=
  by rfl


-- @@ L860-860 verbatim
end Tensor


-- @@ L862-862 verbatim
end Lens


-- @@ L864-864 verbatim
namespace Equiv


-- @@ L866-866 verbatim
variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}


-- @@ L868-898 expanded
/-- Convert an equivalence between two polynomial functors `P` and `Q` to a lens. -/
def toLensEquiv (e : P ≃ₚ Q) : Equiv P Q
    where
  toLens := Lens.mk e.equivA (fun a => (e.equivB a).symm)
  invLens := Lens.mk e.symm.equivA (fun a => (e.symm.equivB a).symm)
  left_inv := by
    simp only [Lens.comp, Lens.id]
    ext a b
    · simp [PFunctor.Equiv.symm]
    · simp only [Function.comp_apply, id_eq]
      have hb :
        (e.equivB a).symm ((e.symm.equivB (e.equivA a)).symm b) =
          _root_.cast (congrArg P.B (e.equivA.symm_apply_apply a)) b :=
        by
        simp only [PFunctor.Equiv.symm]
        exact (equivB_symm_apply (e := e) (a := a) (b := b))
      have h0 : a = e.equivA.symm (e.equivA a) := (e.equivA.symm_apply_apply a).symm
      have hr := eqRec_id_apply (β := P.B) (h := h0) (x := b)
      exact hb.trans hr.symm
  right_inv := by
    simp only [Lens.comp, Lens.id]
    ext a b
    · simp [PFunctor.Equiv.symm]
    · simp only [Function.comp_apply, id_eq]
      have hb :
        (e.symm.equivB a).symm ((e.equivB (e.symm.equivA a)).symm b) =
          _root_.cast (congrArg Q.B (e.equivA.apply_symm_apply a)) b :=
        by
        simp only [PFunctor.Equiv.symm]
        exact (symm_equivB_symm_apply (e := e) (a := a) (b := b))
      have h0 : a = e.equivA (e.equivA.symm a) := (_root_.Equiv.symm_apply_eq e.equivA).mp rfl
      have hr := eqRec_id_apply (β := Q.B) (h := h0) (x := b)
      exact hb.trans hr.symm


-- @@ L900-900 verbatim
end Equiv


-- @@ L902-902 verbatim
namespace Lens


-- @@ L904-904 verbatim
section Sigma


-- @@ L906-906 verbatim
variable {I : Type v}


-- @@ L908-909 verbatim
instance [IsEmpty I] {F : I → PFunctor.{u}} : IsEmpty (sigma F).A := by
  simp [sigma]

-- @@ L910-911 verbatim
instance [IsEmpty I] {F : I → PFunctor.{u}} {a : (sigma F).A} : IsEmpty ((sigma F).B a) :=
  isEmptyElim a


-- @@ L913-915 expanded
/-- Sigma of an empty family is the zero functor. -/
def sigmaEmpty [IsEmpty I] {F : I → PFunctor.{uA, uB}} : Equiv (sigma F) 0 :=
  PFunctor.Equiv.toLensEquiv (PFunctor.Equiv.emptySigma (F := F))


-- @@ L917-922 expanded
/-- Sigma of a `PUnit`-indexed family is equivalent to the functor itself (up to `ulift`). -/
def sigmaUnit {F : PUnit → PFunctor.{uA, uB}} : Equiv (sigma F) (F PUnit.unit).ulift :=
  PFunctor.Equiv.toLensEquiv
    (PFunctor.Equiv.trans (PFunctor.Equiv.punitSigma (F := F))
      (PFunctor.Equiv.uliftEquiv (P := F PUnit.unit)))


-- @@ L924-929 expanded
/-- Sigma of a unique-indexed family is equivalent to the default fiber (up to `ulift`). -/
def sigmaOfUnique [Unique I] {F : I → PFunctor.{uA, uB}} : Equiv (sigma F) (F default).ulift :=
  PFunctor.Equiv.toLensEquiv
    (PFunctor.Equiv.trans (PFunctor.Equiv.uniqueSigma (F := F))
      (PFunctor.Equiv.uliftEquiv (P := F default)))


-- @@ L931-936 expanded
/-- Left distributivity of product over sigma. -/
def prodSigmaDistrib {P : PFunctor.{uA₁, uB₁}} {F : I → PFunctor.{uA₂, uB₂}} :
    Equiv (P * sigma F : PFunctor.{max uA₁ uA₂ v, max uB₁ uB₂})
      (sigma (fun i => (P * F i : PFunctor.{max uA₁ uA₂, max uB₁ uB₂})) :
        PFunctor.{max uA₁ uA₂ v, max uB₁ uB₂}) :=
  PFunctor.Equiv.toLensEquiv (PFunctor.Equiv.prodSigmaDistrib (P := P) (F := F))


-- @@ L938-943 expanded
/-- Right distributivity of product over sigma. -/
def sigmaProdDistrib {P : PFunctor.{uA₁, uB₁}} {F : I → PFunctor.{uA₂, uB₂}} :
    Equiv (sigma F * P : PFunctor.{max uA₁ uA₂ v, max uB₁ uB₂})
      (sigma (fun i => (F i * P : PFunctor.{max uA₁ uA₂, max uB₁ uB₂})) :
        PFunctor.{max uA₁ uA₂ v, max uB₁ uB₂}) :=
  PFunctor.Equiv.toLensEquiv (PFunctor.Equiv.sigmaProdDistrib (P := P) (F := F))


-- @@ L945-948 expanded
/-- Left distributivity of tensor product over sigma. -/
def tensorSigmaDistrib {P : PFunctor.{uA₁, uB₁}} {F : I → PFunctor.{uA₂, uB₂}} :
    Equiv (P ⊗ sigma F) (sigma (fun i => P ⊗ F i)) :=
  PFunctor.Equiv.toLensEquiv (PFunctor.Equiv.tensorSigmaDistrib (P := P) (F := F))


-- @@ L950-953 expanded
/-- Right distributivity of tensor product over sigma. -/
def sigmaTensorDistrib {P : PFunctor.{uA₂, uB₂}} {F : I → PFunctor.{uA₁, uB₁}} :
    Equiv (sigma F ⊗ P) (sigma (fun i => F i ⊗ P)) :=
  PFunctor.Equiv.toLensEquiv (PFunctor.Equiv.sigmaTensorDistrib (F := F) (P := P))


-- @@ L955-958 expanded
/-- Right distributivity of composition over sigma. -/
def sigmaCompDistrib {P : PFunctor.{uA₂, uB₂}} {F : I → PFunctor.{uA₁, uB₁}} :
    Equiv (sigma F ◃ P) (sigma (fun i => F i ◃ P)) :=
  PFunctor.Equiv.toLensEquiv (PFunctor.Equiv.sigmaCompDistrib (F := F) (P := P))


-- @@ L960-960 verbatim
end Sigma


-- @@ L962-962 verbatim
section Pi


-- @@ L964-964 verbatim
variable {I : Type v}


-- @@ L966-971 expanded
/-- Pi over a `PUnit`-indexed family is equivalent to the functor itself. -/
def piUnit {P : PFunctor.{u}} : Equiv (pi (fun (_ : PUnit) => P)) P
    where
  toLens := Lens.mk (fun f => f PUnit.unit) (fun _ pb => ⟨PUnit.unit, pb⟩)
  invLens := Lens.mk (fun pa _ => pa) (fun _ spb => spb.2)
  left_inv := rfl
  right_inv := rfl


-- @@ L973-987 expanded
/-- Pi of a family of zero functors over an inhabited type is the zero functor. -/
def piZero [Inhabited I] {F : I → PFunctor.{uA, uB}} (F_zero : ∀ i, F i = 0) : Equiv (pi F) 0 :=
  by
  have : IsEmpty (pi F).A := by
    refine ⟨fun f => ?_⟩
    have hf : (F default).A := f default
    rw [F_zero (default : I)] at hf
    exact hf.elim
  refine
    { toLens := Lens.mk isEmptyElim fun a => isEmptyElim a
      invLens := Lens.mk PEmpty.elim fun a => PEmpty.elim a
      left_inv := by ext a <;> exact isEmptyElim a
      right_inv := by ext a <;> exact PEmpty.elim a }


-- @@ L989-989 verbatim
end Pi


-- @@ L991-991 verbatim
namespace Equiv


-- @@ L993-998 expanded
/-- ULift equivalence for lenses -/
def ulift {P : PFunctor.{uA, uB}} : Equiv P.ulift P
    where
  toLens := Lens.mk ULift.down fun _ => ULift.up
  invLens := Lens.mk ULift.up fun _ => ULift.down
  left_inv := rfl
  right_inv := rfl


-- @@ L1000-1000 verbatim
end Equiv


-- @@ L1002-1002 verbatim
end Lens


-- @@ L1004-1004 verbatim
end PFunctor
