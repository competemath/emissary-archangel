module

public import Foundation.Logic.LogicSymbol


-- @@ L5-5 verbatim
@[expose] public section


-- @@ L7-7 verbatim
namespace FFL.Propositional


-- @@ L9-15 verbatim
inductive NNFormula (α : Type u) : Type u where
  | verum  : NNFormula α
  | falsum : NNFormula α
  | atom   : α → NNFormula α
  | natom  : α → NNFormula α
  | and    : NNFormula α → NNFormula α → NNFormula α
  | or     : NNFormula α → NNFormula α → NNFormula α


-- @@ L17-17 verbatim
namespace NNFormula


-- @@ L19-19 verbatim
variable {α : Type u} {α₁ : Type u₁} {α₂ : Type u₂} {α₃ : Type u₃}


-- @@ L21-30 verbatim
def neg : NNFormula α → NNFormula α
  | verum   => falsum
  | falsum  => verum
  | atom a  => natom a
  | natom a => atom a
  | and φ ψ => or (neg φ) (neg ψ)
  | or φ ψ  => and (neg φ) (neg ψ)

lemma neg_neg (φ : NNFormula α) : neg (neg φ) = φ :=
  by induction φ <;> simp [*, neg]


-- @@ L32-36 verbatim
instance : LogicalConnective (NNFormula α) where
  arrow := fun φ ψ => or (neg φ) ψ
  wedge := and
  vee := or
  tilde := neg


-- @@ L38-40 verbatim
instance : LogicalNeutral (NNFormula α) where
  top := verum
  bot := falsum


-- @@ L42-42 verbatim
section ToString


-- @@ L44-44 verbatim
variable [ToString α]


-- @@ L46-52 verbatim
def toStr : NNFormula α → String
  | ⊤       => "\\top"
  | ⊥       => "\\bot"
  | atom a  => "{" ++ toString a ++ "}"
  | natom a => "\\lnot {" ++ toString a ++ "}"
  | φ ⋏ ψ   => "\\left(" ++ toStr φ ++ " \\land " ++ toStr ψ ++ "\\right)"
  | φ ⋎ ψ   => "\\left(" ++ toStr φ ++ " \\lor "  ++ toStr ψ ++ "\\right)"


-- @@ L54-54 verbatim
instance : Repr (NNFormula α) := ⟨fun t _ => toStr t⟩


-- @@ L56-56 verbatim
instance : ToString (NNFormula α) := ⟨toStr⟩


-- @@ L58-58 verbatim
end ToString


-- @@ L60-60 verbatim
@[simp] lemma neg_top : ∼(⊤ : NNFormula α) = ⊥ := rfl


-- @@ L62-62 verbatim
@[simp] lemma neg_bot : ∼(⊥ : NNFormula α) = ⊤ := rfl


-- @@ L64-64 verbatim
@[simp] lemma neg_atom (a : α) : ∼(atom a) = natom a := rfl


-- @@ L66-66 verbatim
@[simp] lemma neg_natom (a : α) : ∼(natom a) = atom a := rfl


-- @@ L68-68 verbatim
@[simp] lemma neg_and (φ ψ : NNFormula α) : ∼(φ ⋏ ψ) = ∼φ ⋎ ∼ψ := rfl


-- @@ L70-70 verbatim
@[simp] lemma neg_or (φ ψ : NNFormula α) : ∼(φ ⋎ ψ) = ∼φ ⋏ ∼ψ := rfl


-- @@ L72-72 verbatim
@[simp] lemma neg_neg' (φ : NNFormula α) : ∼∼φ = φ := neg_neg φ


-- @@ L74-83 verbatim
@[simp] lemma neg_inj (φ ψ : NNFormula α) : ∼φ = ∼ψ ↔ φ = ψ := by
  constructor
  · intro h; simpa using congr_arg (∼·) h
  · exact congr_arg _

lemma neg_eq (φ : NNFormula α) : ∼φ = neg φ := rfl

lemma imp_eq (φ ψ : NNFormula α) : φ 🡒 ψ = ∼φ ⋎ ψ := rfl

lemma iff_eq (φ ψ : NNFormula α) : φ 🡘 ψ = (∼φ ⋎ ψ) ⋏ (∼ψ ⋎ φ) := rfl


-- @@ L85-86 verbatim
@[simp] lemma and_inj (φ₁ ψ₁ φ₂ ψ₂ : NNFormula α) : φ₁ ⋏ φ₂ = ψ₁ ⋏ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ :=
  Iff.of_eq <| and.injEq _ _ _ _


-- @@ L88-89 verbatim
@[simp] lemma or_inj (φ₁ ψ₁ φ₂ ψ₂ : NNFormula α) : φ₁ ⋎ φ₂ = ψ₁ ⋎ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ :=
  Iff.of_eq <| or.injEq _ _ _ _


-- @@ L91-92 verbatim
instance : TildeInvolutive (NNFormula α) where
  tilde_involutive := neg_neg


-- @@ L94-97 verbatim
instance : LogicalConnective.DeMorgan (NNFormula α) where
  and := by simp
  or := by simp
  imply := by simp [imp_eq]


-- @@ L99-101 verbatim
instance : LogicalNeutral.DeMorgan (NNFormula α) where
  verum := rfl
  falsum := rfl


-- @@ L103-109 verbatim
def complexity : NNFormula α → ℕ
| ⊤       => 0
| ⊥       => 0
| atom _  => 0
| natom _ => 0
| φ ⋏ ψ   => max φ.complexity ψ.complexity + 1
| φ ⋎ ψ   => max φ.complexity ψ.complexity + 1


-- @@ L111-111 verbatim
@[simp] lemma complexity_top : complexity (⊤ : NNFormula α) = 0 := rfl


-- @@ L113-113 verbatim
@[simp] lemma complexity_bot : complexity (⊥ : NNFormula α) = 0 := rfl


-- @@ L115-115 verbatim
@[simp] lemma complexity_atom (a : α) : complexity (atom a) = 0 := rfl


-- @@ L117-117 verbatim
@[simp] lemma complexity_natom (a : α) : complexity (natom a) = 0 := rfl


-- @@ L119-119 verbatim
@[simp] lemma complexity_and (φ ψ : NNFormula α) : complexity (φ ⋏ ψ) = max φ.complexity ψ.complexity + 1 := rfl

-- @@ L120-120 verbatim
@[simp] lemma complexity_and' (φ ψ : NNFormula α) : complexity (and φ ψ) = max φ.complexity ψ.complexity + 1 := rfl


-- @@ L122-122 verbatim
@[simp] lemma complexity_or (φ ψ : NNFormula α) : complexity (φ ⋎ ψ) = max φ.complexity ψ.complexity + 1 := rfl

-- @@ L123-123 verbatim
@[simp] lemma complexity_or' (φ ψ : NNFormula α) : complexity (or φ ψ) = max φ.complexity ψ.complexity + 1 := rfl


-- @@ L125-138 verbatim
@[elab_as_elim]
def cases' {C : NNFormula α → Sort w}
    (hverum  : C ⊤)
    (hfalsum : C ⊥)
    (hatom   : ∀ a : α, C (atom a))
    (hnatom  : ∀ a : α, C (natom a))
    (hand    : ∀ (φ ψ : NNFormula α), C (φ ⋏ ψ))
    (hor     : ∀ (φ ψ : NNFormula α), C (φ ⋎ ψ)) : (φ : NNFormula α) → C φ
  | ⊤       => hverum
  | ⊥       => hfalsum
  | atom a  => hatom a
  | natom a => hnatom a
  | φ ⋏ ψ   => hand φ ψ
  | φ ⋎ ψ   => hor φ ψ


-- @@ L140-153 verbatim
@[elab_as_elim]
def rec' {C : NNFormula α → Sort w}
  (hverum  : C ⊤)
  (hfalsum : C ⊥)
  (hatom   : ∀ a : α, C (atom a))
  (hnatom  : ∀ a : α, C (natom a))
  (hand    : ∀ (φ ψ : NNFormula α), C φ → C ψ → C (φ ⋏ ψ))
  (hor     : ∀ (φ ψ : NNFormula α), C φ → C ψ → C (φ ⋎ ψ)) : (φ : NNFormula α) → C φ
  | ⊤       => hverum
  | ⊥       => hfalsum
  | atom a  => hatom a
  | natom a => hnatom a
  | φ ⋏ ψ   => hand φ ψ (rec' hverum hfalsum hatom hnatom hand hor φ) (rec' hverum hfalsum hatom hnatom hand hor ψ)
  | φ ⋎ ψ   => hor φ ψ (rec' hverum hfalsum hatom hnatom hand hor φ) (rec' hverum hfalsum hatom hnatom hand hor ψ)


-- @@ L155-156 verbatim
@[simp] lemma complexity_neg (φ : NNFormula α) : complexity (∼φ) = complexity φ :=
  by induction φ using rec' <;> simp [*]


-- @@ L158-158 verbatim
section Decidable


-- @@ L160-160 verbatim
variable [DecidableEq α]


-- @@ L162-190 verbatim
def hasDecEq : (φ ψ : NNFormula α) → Decidable (φ = ψ)
  | ⊤,       ψ => by cases ψ using cases' <;>
      { simp only [reduceCtorEq]; try { exact isFalse not_false }; try { exact isTrue trivial } }
  | ⊥,       ψ => by cases ψ using cases' <;>
      { simp only [reduceCtorEq]; try { exact isFalse not_false }; try { exact isTrue trivial } }
  | atom a,  ψ => by
      cases ψ using cases' <;> try { simp only [reduceCtorEq]; exact isFalse not_false }
      simp only [atom.injEq]; exact decEq _ _
  | natom a, ψ => by
      cases ψ using cases' <;> try { simp only [reduceCtorEq]; exact isFalse not_false }
      simp only [natom.injEq]; exact decEq _ _
  | φ ⋏ ψ,   χ => by
      cases χ using cases' <;> try { simp only [reduceCtorEq]; exact isFalse not_false }
      case hand φ' ψ' =>
        exact match hasDecEq φ φ' with
        | isTrue hp =>
          match hasDecEq ψ ψ' with
          | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
          | isFalse hq => isFalse (by simp [hp, hq])
        | isFalse hp => isFalse (by simp [hp])
  | φ ⋎ ψ,   χ => by
      cases χ using cases' <;> try { simp only [reduceCtorEq]; exact isFalse not_false }
      case hor φ' ψ' =>
        exact match hasDecEq φ φ' with
        | isTrue hp =>
          match hasDecEq ψ ψ' with
          | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
          | isFalse hq => isFalse (by simp [hp, hq])
        | isFalse hp => isFalse (by simp [hp])


-- @@ L192-192 verbatim
instance : DecidableEq (NNFormula α) := hasDecEq


-- @@ L194-197 verbatim
end Decidable

lemma ne_of_ne_complexity {φ ψ : NNFormula α} (h : φ.complexity ≠ ψ.complexity) : φ ≠ ψ :=
  by rintro rfl; contradiction


-- @@ L199-199 verbatim
end NNFormula


-- @@ L201-201 verbatim
abbrev Theory (α : Type*) := Set (NNFormula α)


-- @@ L203-203 verbatim
end FFL.Propositional

-- @@ L204-204 verbatim
end
