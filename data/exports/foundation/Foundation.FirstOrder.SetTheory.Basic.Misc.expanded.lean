module

public import Foundation.FirstOrder.Completeness.CounterModel
public import Mathlib.SetTheory.Cardinal.Basic


-- @@ L6-6 verbatim
@[expose] public section

-- @@ L7-13 verbatim
/-! # Preperations for set theory

- *NOTE*:
  To avoid the duplicate definitions of `Structure ℒₛₑₜ` for models,
  we basically use `SetStructure`, and generated `standardStructure` instead of `Structure ℒₛₑₜ` itself.
  If you wish to use a type with `Structure ℒₛₑₜ`, use `QuotNormalize`.
-/


-- @@ L15-15 verbatim
namespace FFL.FirstOrder


-- @@ L17-17 verbatim
namespace Language


-- @@ L19-19 verbatim
namespace Set


-- @@ L21-21 verbatim
abbrev Func : ℕ → Type := fun _ ↦ Empty


-- @@ L23-25 verbatim
inductive Rel : ℕ → Type
  | eq : Rel 2
  | mem : Rel 2


-- @@ L27-27 verbatim
end Set


-- @@ L29-33 verbatim
/-- Language of set theory -/
@[reducible]
def set : Language where
  Func := Set.Func
  Rel := Set.Rel


-- @@ L35-35 verbatim
notation "ℒₛₑₜ" => set


-- @@ L37-37 verbatim
namespace Set


-- @@ L39-39 verbatim
instance (k) : DecidableEq (Set.Func k) := inferInstance


-- @@ L41-43 verbatim
instance (k) : DecidableEq (Set.Rel k) := fun a b => by
  rcases a <;> rcases b <;>
  simp only [reduceCtorEq] <;> try {exact instDecidableTrue} <;> try {exact instDecidableFalse}


-- @@ L45-45 verbatim
instance (k) : Encodable (Set.Func k) := inferInstance


-- @@ L47-57 verbatim
instance (k) : Encodable (Set.Rel k) where
  encode := fun x =>
    match x with
    | Rel.eq => 0
    | Rel.mem => 1
  decode := fun e =>
    match k, e with
    | 2, 0 => some Rel.eq
    | 2, 1 => some Rel.mem
    | _, _ => none
  encodek := fun x => by rcases x <;> simp


-- @@ L59-59 verbatim
instance : (ℒₛₑₜ).DecidableEq := ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩


-- @@ L61-61 verbatim
instance : (ℒₛₑₜ).Encodable := ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩


-- @@ L63-63 verbatim
instance : (ℒₛₑₜ).Eq := ⟨Rel.eq⟩


-- @@ L65-70 verbatim
instance : (ℒₛₑₜ).Mem := ⟨Rel.mem⟩

lemma rel_eq_eq_or_mem (R : (ℒₛₑₜ).Rel k) : k = 2 ∧ (R ≍ (Eq.eq : (ℒₛₑₜ).Rel 2) ∨ R ≍ (Mem.mem : (ℒₛₑₜ).Rel 2)) :=
  match R with
  | Rel.eq => ⟨rfl, Or.inl <| by rfl⟩
  | Rel.mem => ⟨by rfl, Or.inr <| by rfl⟩


-- @@ L72-72 verbatim
end Set


-- @@ L74-74 verbatim
end Language


-- @@ L76-76 verbatim
abbrev SetTheory := Theory ℒₛₑₜ


-- @@ L78-78 verbatim
abbrev SetTheorySemiterm (ξ : Type*) (n : ℕ) := Semiterm ℒₛₑₜ ξ n


-- @@ L80-80 verbatim
abbrev SetTheoryTerm (ξ : Type*) := Term ℒₛₑₜ ξ


-- @@ L82-82 verbatim
abbrev SetTheorySemiformula (ξ : Type*) (n : ℕ) := Semiformula ℒₛₑₜ ξ n


-- @@ L84-84 verbatim
abbrev SetTheoryFormula (ξ : Type*) := Formula ℒₛₑₜ ξ


-- @@ L86-86 verbatim
abbrev SetTheorySemisentence (n : ℕ) := Semisentence ℒₛₑₜ n


-- @@ L88-88 verbatim
abbrev SetTheorySentence := Sentence ℒₛₑₜ


-- @@ L90-90 verbatim
abbrev SetTheorySemiproposition (n : ℕ) := Semiproposition ℒₛₑₜ n


-- @@ L92-92 verbatim
abbrev SetTheoryProposition := Proposition ℒₛₑₜ


-- @@ L94-94 verbatim
variable [ToString ξ]


-- @@ L96-98 verbatim
def Semiterm.toStringSet : SetTheorySemiterm ξ n → String
  | #x => "x_{" ++ toString (n - 1 - (x : ℕ)) ++ "}"
  | &x => "a_{" ++ toString x ++ "}"


-- @@ L100-100 verbatim
instance : Repr (SetTheorySemiterm ξ n) := ⟨fun t _ ↦ t.toStringSet⟩


-- @@ L102-102 verbatim
instance : ToString (SetTheorySemiterm ξ n) := ⟨fun t ↦ t.toStringSet⟩


-- @@ L104-116 verbatim
def Semiformula.toStringSet : ∀ {n}, SetTheorySemiformula ξ n → String
  | _,                               ⊤ => "⊤"
  | _,                               ⊥ => "⊥"
  | _,            .rel Language.Eq.eq v => s!"{(v 0).toStringSet} = {(v 1).toStringSet}"
  | _,          .rel Language.Mem.mem v => s!"{(v 0).toStringSet} ∈ {(v 1).toStringSet}"
  | _,           .nrel Language.Eq.eq v => s!"{(v 0).toStringSet} ≠ {(v 1).toStringSet}"
  | _,         .nrel Language.Mem.mem v => s!"{(v 0).toStringSet} ∉ {(v 1).toStringSet}"
  | _,                           φ ⋏ ψ => s!"[{φ.toStringSet}] ∧ [{ψ.toStringSet}]"
  | _,                           φ ⋎ ψ => s!"[{φ.toStringSet}] ∨ [{ψ.toStringSet}]"
  | n, ∀¹ (rel Language.Mem.mem v 🡒 φ) => s!"(∀ x{toString n} ∈ {(v 1).toStringSet}) [{φ.toStringSet}]"
  | n, ∃¹ (rel Language.Mem.mem v ⋏ φ) => s!"(∃ x{toString n} ∈ {(v 1).toStringSet}) [{φ.toStringSet}]"
  | n,                            ∀¹ φ => s!"(∀ x{toString n}) [{φ.toStringSet}]"
  | n,                            ∃¹ φ => s!"(∃ x{toString n}) [{φ.toStringSet}]"


-- @@ L118-118 verbatim
instance : Repr (SetTheorySemiformula ξ n) := ⟨fun φ _ ↦ φ.toStringSet⟩


-- @@ L120-120 verbatim
instance : ToString (SetTheorySemiformula ξ n) := ⟨fun φ ↦ φ.toStringSet⟩


-- @@ L122-122 verbatim
abbrev _root_.FFL.SetStructure (V : Type*) := Membership V V


-- @@ L124-124 verbatim
class Structure.Set (M : Type w) [SetStructure M] [Structure ℒₛₑₜ M] extends Structure.Eq ℒₛₑₜ M, Structure.Mem ℒₛₑₜ M


-- @@ L126-126 verbatim
attribute [instance] Structure.Set.mk


-- @@ L128-128 verbatim
namespace SetTheory


-- @@ L130-140 verbatim
private lemma consequence_of_aux (T : SetTheory) [𝗘𝗤 _ ⪯ T] (φ : SetTheorySentence)
    (H : ∀ (M : Type w)
           [SetStructure M]
           [Structure ℒₛₑₜ M]
           [Structure.Set M]
           [Nonempty M]
           [M↓[ℒₛₑₜ] ⊧* T],
           M↓[ℒₛₑₜ] ⊧ φ) :
    T ⊨ φ := Theory.consequence_iff_consequence.{_, w}.mp <| consequence_iff_eq.mpr fun M _ _ _ hT =>
  letI : (Structure.Model ℒₛₑₜ M)↓[ℒₛₑₜ] ⊧* T := Structure.ElementaryEquiv.modelsTheory.mp hT
  Structure.ElementaryEquiv.models.mpr (H (Structure.Model ℒₛₑₜ M))

-- @@ L141-141 verbatim
section semantics


-- @@ L143-143 verbatim
variable (M : Type*) [SetStructure M]


-- @@ L145-150 verbatim
instance (priority := 100) standardStructure : Structure ℒₛₑₜ M where
  func := fun _ f ↦ Empty.elim f
  rel := fun _ r ↦
    match r with
    | Language.Set.Rel.eq => fun v ↦ v 0 = v 1
    | Language.Set.Rel.mem => fun v ↦ v 0 ∈ v 1


-- @@ L152-152 verbatim
instance : Structure.Eq ℒₛₑₜ M := ⟨fun _ _ ↦ iff_of_eq rfl⟩


-- @@ L154-168 verbatim
instance : Structure.Mem ℒₛₑₜ M := ⟨fun _ _ ↦ iff_of_eq rfl⟩

lemma standardStructure_unique' (s : Structure ℒₛₑₜ M)
    (hEq : Structure.Eq ℒₛₑₜ M) (hMem : Structure.Mem ℒₛₑₜ M) : s = standardStructure M := Structure.ext
  (funext₃ fun k f ↦ Empty.elim f)
  (funext₃ fun k r _ =>
    match k, r with
    | _, Language.Eq.eq => by simp
    | _, Language.Mem.mem => by simp)

lemma standardStructure_unique (s : Structure ℒₛₑₜ M) [hEq : Structure.Eq ℒₛₑₜ M] [hMem : Structure.Mem ℒₛₑₜ M] : s = standardStructure M :=
  standardStructure_unique' M s hEq hMem


/- ### Normalization -/


-- @@ L170-172 verbatim
/-- Normalize model without =-isomorphic. -/
structure QuotNormalize (M : Type*) [Structure ℒₛₑₜ M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* (𝗘𝗤 _ : SetTheory)] : Type _ where
  toQuot : Structure.Model ℒₛₑₜ (Structure.Eq.QuotEq ℒₛₑₜ M)


-- @@ L174-174 verbatim
namespace QuotNormalize


-- @@ L176-176 verbatim
variable {M : Type*} [s : Structure ℒₛₑₜ M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* (𝗘𝗤 _ : SetTheory)]


-- @@ L178-180 verbatim
def equiv : QuotNormalize M ≃ Structure.Model ℒₛₑₜ (Structure.Eq.QuotEq ℒₛₑₜ M) where
  toFun x := x.toQuot
  invFun x := ⟨x⟩


-- @@ L182-183 verbatim
def equiv' : QuotNormalize M ≃ Structure.Eq.QuotEq ℒₛₑₜ M :=
  equiv.trans (Structure.Model.equiv ℒₛₑₜ (Structure.Eq.QuotEq ℒₛₑₜ M)).symm


-- @@ L185-187 verbatim
instance : Nonempty (QuotNormalize M) :=
  have : Nonempty (Structure.Model ℒₛₑₜ (Structure.Eq.QuotEq ℒₛₑₜ M)) := inferInstance
  ⟨equiv.symm this.some⟩


-- @@ L189-192 verbatim
instance : SetStructure (QuotNormalize M) where
  mem y x := equiv x ∈ equiv y

lemma mem_def (x y : QuotNormalize M) : x ∈ y ↔ equiv x ∈ equiv y := by rfl


-- @@ L194-194 verbatim
open Structure


-- @@ L196-211 verbatim
instance elementary_equiv : QuotNormalize M ≡ₑ[ℒₛₑₜ] M :=
  have h₁ : QuotNormalize M ≡ₑ[ℒₛₑₜ] Structure.Model ℒₛₑₜ (Structure.Eq.QuotEq ℒₛₑₜ M) := by
    apply ElementaryEquiv.of_equiv equiv
    · intro k R v₁ v₂ h
      rcases Language.Set.rel_eq_eq_or_mem R with ⟨rfl, (rfl | rfl)⟩
      · simp only [eq_lang, Fin.isValue]
        rw [←(equiv (M := M)).apply_eq_iff_eq]
        simp only [h]
      · simp [mem_def, h]
    · intro _ f
      exact IsEmpty.elim' inferInstance f
  have h₂ : Structure.Model ℒₛₑₜ (Structure.Eq.QuotEq ℒₛₑₜ M) ≡ₑ[ℒₛₑₜ] M :=
    Structure.ElementaryEquiv.trans
      (Structure.Model.elementaryEquiv ℒₛₑₜ (Structure.Eq.QuotEq ℒₛₑₜ M)).symm
      (Structure.Eq.QuotEq.elementaryEquiv ℒₛₑₜ M)
  h₁.trans h₂


-- @@ L213-213 verbatim
open Cardinal


-- @@ L215-224 verbatim
variable (M)

lemma card_le : #(QuotNormalize M) ≤ #M := calc
  #(QuotNormalize M) = #(Structure.Eq.QuotEq ℒₛₑₜ M) := by
    simpa using Cardinal.mk_congr_lift equiv'
  _  ≤ #M := Cardinal.mk_quotient_le

lemma countable_of_countable [c : Countable M] : Countable (QuotNormalize M) :=
  have : #M ≤ ℵ₀ := mk_le_aleph0_iff.mpr c
  mk_le_aleph0_iff.mp <| le_trans (card_le M) this


-- @@ L226-226 verbatim
end QuotNormalize


-- @@ L228-236 verbatim
end semantics

lemma consequence_of_models (T : SetTheory) [𝗘𝗤 _ ⪯ T] (φ : SetTheorySentence) (H : ∀ (M : Type*) [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* T], M↓[ℒₛₑₜ] ⊧ φ) :
    T ⊨ φ := consequence_of_aux T φ fun M _ s _ _ ↦ by
  rcases standardStructure_unique M s
  exact H M

lemma provable_of_models (T : SetTheory) [𝗘𝗤 _ ⪯ T] (φ : SetTheorySentence) (H : ∀ (M : Type*) [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* T], M↓[ℒₛₑₜ] ⊧ φ) :
    T ⊢ φ := Theory.Proof.complete <| consequence_of_models _ _ H


-- @@ L238-238 verbatim
end SetTheory


-- @@ L240-240 verbatim
namespace SetTheory


-- @@ L242-242 verbatim
end FFL.FirstOrder.SetTheory
