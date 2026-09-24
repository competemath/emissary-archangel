module

public import Foundation.SecondOrder.Syntax.Rew


-- @@ L5-5 verbatim
@[expose] public section


-- @@ L7-11 verbatim
/-!
# A set-theoretic semantics of second-order logic

- TODO: Align with https://github.com/FormalizedFormalLogic/Foundation/pull/794
-/


-- @@ L13-13 verbatim
namespace FFL.SecondOrder


-- @@ L15-15 verbatim
open FirstOrder


-- @@ L17-17 verbatim
variable {L : Language}


-- @@ L19-20 verbatim
structure Struc₂ (L : Language) extends FirstOrder.Struc L where
  sets : Set (Set Dom)


-- @@ L22-22 verbatim
abbrev SmallStruc (L : Language.{u}) := Struc.{u, u} L


-- @@ L24-24 verbatim
namespace Struc₂


-- @@ L26-26 verbatim
instance (𝓈 : Struc₂ L) : Nonempty 𝓈.Dom := 𝓈.nonempty


-- @@ L28-28 verbatim
instance (𝓈 : Struc₂ L) : Structure L 𝓈.Dom := inferInstance


-- @@ L30-30 verbatim
end Struc₂


-- @@ L32-32 verbatim
namespace Semiformula


-- @@ L34-34 verbatim
variable {M : Type w} [𝓈 : Structure L M]


-- @@ L36-52 verbatim
def EvalAux
    (𝕊 : Set (Set M))
    (F : Ξ → Set M) (f : ξ → M) (E : Fin N → Set M) (e : Fin n → M) : Semiformula L Ξ ξ N n → Prop
  |  rel R v => 𝓈.rel R (Semiterm.val e f ∘ v)
  | nrel R v => ¬𝓈.rel R (Semiterm.val e f ∘ v)
  |   t ∈& X => t.val e f ∈ F X
  |   t ∉& X => t.val e f ∉ F X
  |   t ∈# X => t.val e f ∈ E X
  |   t ∉# X => t.val e f ∉ E X
  |        ⊤ => True
  |        ⊥ => False
  |    φ ⋏ ψ => φ.EvalAux 𝕊 F f E e ∧ ψ.EvalAux 𝕊 F f E e
  |    φ ⋎ ψ => φ.EvalAux 𝕊 F f E e ∨ ψ.EvalAux 𝕊 F f E e
  |     ∀¹ φ => ∀ x, φ.EvalAux 𝕊 F f E (x :> e)
  |     ∃¹ φ => ∃ x, φ.EvalAux 𝕊 F f E (x :> e)
  |     ∀² φ => ∀ X ∈ 𝕊, φ.EvalAux 𝕊 F f (X :> E) e
  |     ∃² φ => ∃ X ∈ 𝕊, φ.EvalAux 𝕊 F f (X :> E) e


-- @@ L54-54 verbatim
variable {𝕊 : Set (Set M)} {F : Ξ → Set M} {f : ξ → M} {E : Fin N → Set M} {e : Fin n → M}


-- @@ L56-58 verbatim
@[simp] lemma EvalAux_neg (φ : Semiformula L Ξ ξ N n) :
    EvalAux 𝕊 F f E e (∼φ) ↔ ¬EvalAux 𝕊 F f E e φ := by
  induction φ using rec' <;> simp [*, EvalAux, or_iff_not_imp_left]


-- @@ L60-67 verbatim
def Eval (𝕊 : Set (Set M)) (F : Ξ → Set M) (f : ξ → M) (E : Fin N → Set M) (e : Fin n → M) : Semiformula L Ξ ξ N n →ˡᶜ Prop where
  toTr := EvalAux 𝕊 F f E e
  map_top' := rfl
  map_bot' := rfl
  map_and' := by simp [EvalAux]
  map_or' := by simp [EvalAux]
  map_neg' := by simp [EvalAux_neg]
  map_imply' := by simp [LogicalConnective.DeMorgan.imply, EvalAux_neg, EvalAux]


-- @@ L69-70 verbatim
@[simp] lemma eval_rel {k} {R : L.Rel k} {v} :
    (rel R v).Eval 𝕊 F f E e ↔ 𝓈.rel R (Semiterm.val e f ∘ v) := by rfl


-- @@ L72-73 verbatim
@[simp] lemma eval_nrel {k} {R : L.Rel k} {v} :
    (nrel R v).Eval 𝕊 F f E e ↔ ¬𝓈.rel R (Semiterm.val e f ∘ v) := by rfl


-- @@ L75-76 verbatim
@[simp] lemma eval_fvar {X : Ξ} {t : Semiterm L ξ n} :
    (t ∈& X).Eval 𝕊 F f E e ↔ t.val e f ∈ F X := by rfl


-- @@ L78-79 verbatim
@[simp] lemma eval_nfvar {X : Ξ} {t : Semiterm L ξ n} :
    (t ∉& X).Eval 𝕊 F f E e ↔ t.val e f ∉ F X := by rfl


-- @@ L81-82 verbatim
@[simp] lemma eval_bvar {X : Fin N} {t : Semiterm L ξ n} :
    (t ∈# X).Eval 𝕊 F f E e ↔ t.val e f ∈ E X := by rfl


-- @@ L84-85 verbatim
@[simp] lemma eval_nbvar {X : Fin N} {t : Semiterm L ξ n} :
    (t ∉# X).Eval 𝕊 F f E e ↔ t.val e f ∉ E X := by rfl


-- @@ L87-88 verbatim
@[simp] lemma eval_fal₀ {φ : Semiformula L Ξ ξ N (n + 1)} :
    (∀¹ φ).Eval 𝕊 F f E e ↔ ∀ x, φ.Eval 𝕊 F f E (x :> e) := by rfl


-- @@ L90-91 verbatim
@[simp] lemma eval_exs₀ {φ : Semiformula L Ξ ξ N (n + 1)} :
    (∃¹ φ).Eval 𝕊 F f E e ↔ ∃ x, φ.Eval 𝕊 F f E (x :> e) := by rfl


-- @@ L93-94 verbatim
@[simp] lemma eval_fal₁ {φ : Semiformula L Ξ ξ (N + 1) n} :
    (∀² φ).Eval 𝕊 F f E e ↔ ∀ X ∈ 𝕊, φ.Eval 𝕊 F f (X :> E) e := by rfl


-- @@ L96-97 verbatim
@[simp] lemma eval_exs₁ {φ : Semiformula L Ξ ξ (N + 1) n} :
    (∃² φ).Eval 𝕊 F f E e ↔ ∃ X ∈ 𝕊, φ.Eval 𝕊 F f (X :> E) e := by rfl


-- @@ L99-99 verbatim
end Semiformula


-- @@ L101-101 verbatim
def Struc₂.of {M : Type*} [Nonempty M] (𝕊 : Set (Set M)) (L : Language) [𝓈 : Structure L M] : Struc₂ L := ⟨𝓈.toStruc, 𝕊⟩


-- @@ L103-103 verbatim
notation:max 𝕊 "↓[" L "]" => Struc₂.of 𝕊 L


-- @@ L105-112 verbatim
instance : Semantics (Struc₂ L) (Sentence L) where
  Models 𝓈 σ := σ.Eval 𝓈.sets Empty.elim Empty.elim ![] ![]

lemma models_def {𝓈 : Struc₂ L} {σ : Sentence L} :
    𝓈 ⊧ σ ↔ σ.Eval 𝓈.sets Empty.elim Empty.elim ![] ![] := by rfl

lemma models_iff [Nonempty M] [Structure L M] {𝕊 : Set (Set M)} {σ : Sentence L} :
    𝕊↓[L] ⊧ σ ↔ σ.Eval 𝕊 Empty.elim Empty.elim ![] ![] := by rfl


-- @@ L114-120 verbatim
instance : Semantics.Tarski (Struc₂ L) where
  models_verum _ := by simp [models_def]
  models_falsum _ := by simp [models_def]
  models_and := by simp [models_def]
  models_or := by simp [models_def]
  models_imply := by simp [models_def]
  models_not := by simp [models_def]


-- @@ L122-122 verbatim
end FFL.SecondOrder
