/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Logic.HilbertStyle.Lukasiewicz
public import LeanPool.Incompleteness.Foundation.Modal.LogicSymbol


-- @@ L11-11 verbatim
/-! # Formula -/


-- @@ L13-13 verbatim
@[expose] public section



-- @@ L16-16 verbatim
namespace LO

-- @@ L17-17 verbatim
namespace Modal


-- @@ L19-25 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
inductive Formula (α : Type u) : Type u where
  | atom   : α → Formula α
  | falsum : Formula α
  | imp    : Formula α → Formula α → Formula α
  | box    : Formula α → Formula α
  deriving DecidableEq


-- @@ L27-27 verbatim
namespace Formula


-- @@ L29-30 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev neg (φ : Formula α) : Formula α := imp φ falsum


-- @@ L32-33 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev verum : Formula α := imp falsum falsum


-- @@ L35-36 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev top : Formula α := imp falsum falsum


-- @@ L38-39 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev or (φ ψ : Formula α) : Formula α := imp (neg φ) ψ


-- @@ L41-42 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev and (φ ψ : Formula α) : Formula α := neg (imp φ (neg ψ))


-- @@ L44-45 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev dia (φ : Formula α) : Formula α := neg (box (neg φ))


-- @@ L47-47 verbatim
variable {α : Type u}


-- @@ L49-57 verbatim
instance : BasicModalLogicalConnective (Formula α) where
  tilde := neg
  arrow := imp
  wedge := and
  vee := or
  top := verum
  bot := falsum
  box := box
  dia := dia


-- @@ L59-63 verbatim
instance : LukasiewiczAbbrev (Formula α) where
  top := rfl
  neg := rfl
  or := rfl
  and := rfl

-- @@ L64-64 verbatim
instance : DiaAbbrev (Formula α) := ⟨rfl⟩


-- @@ L66-66 verbatim
section «lp_section_1»


-- @@ L68-68 verbatim
variable [ToString α]


-- @@ L70-79 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def toStr : Formula α → String
  | ⊥ => "\\bot"
  | atom a => "{" ++ toString a ++ "}"
  | Box.box φ => "\\Box " ++ toStr φ
  | Arrow.arrow φ ψ =>
    "\\left(" ++ toStr φ ++ " \\to " ++ toStr ψ ++
      "\\right)"
        -- | φ ⋏ ψ   => "\\left(" ++ toStr φ ++ " \\land " ++ toStr ψ ++ "\\right)"
          -- | φ ⋎ ψ   => "\\left(" ++ toStr φ ++ " \\lor "   ++ toStr ψ ++ "\\right)"


-- @@ L81-81 verbatim
instance : Repr (Formula α) := ⟨fun t _ => toStr t⟩


-- @@ L83-83 verbatim
instance : ToString (Formula α) := ⟨toStr⟩


-- @@ L85-85 verbatim
instance : Coe α (Formula α) := ⟨atom⟩


-- @@ L87-87 verbatim
end «lp_section_1»


-- @@ L89-89 expanded
@[simp]
lemma neg_bot : Tilde.tilde (⊥ : Formula α) = ⊤ :=
  rfl


-- @@ L91-91 expanded
lemma or_eq (φ ψ : Formula α) : or φ ψ = Vee.vee φ ψ :=
  rfl


-- @@ L93-93 expanded
lemma and_eq (φ ψ : Formula α) : and φ ψ = Wedge.wedge φ ψ :=
  rfl


-- @@ L95-95 expanded
lemma imp_eq (φ ψ : Formula α) : imp φ ψ = Arrow.arrow φ ψ :=
  rfl


-- @@ L97-97 expanded
lemma neg_eq (φ : Formula α) : neg φ = Tilde.tilde φ :=
  rfl


-- @@ L99-99 expanded
lemma box_eq (φ : Formula α) : box φ = Box.box φ :=
  rfl


-- @@ L101-101 expanded
lemma dia_eq (φ : Formula α) : dia φ = Dia.dia φ :=
  rfl


-- @@ L103-103 expanded
lemma iff_eq (φ ψ : Formula α) :
    LogicalConnective.iff φ ψ = Wedge.wedge (Arrow.arrow φ ψ) (Arrow.arrow ψ φ) :=
  rfl


-- @@ L105-105 verbatim
lemma falsum_eq : (falsum : Formula α) = ⊥ := rfl


-- @@ L107-109 expanded
@[simp]
lemma and_inj (φ₁ ψ₁ φ₂ ψ₂ : Formula α) :
    Wedge.wedge φ₁ φ₂ = Wedge.wedge ψ₁ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp [Wedge.wedge]


-- @@ L111-113 expanded
@[simp]
lemma or_inj (φ₁ ψ₁ φ₂ ψ₂ : Formula α) : Vee.vee φ₁ φ₂ = Vee.vee ψ₁ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by
  simp [Vee.vee]


-- @@ L115-117 expanded
@[simp]
lemma imp_inj (φ₁ ψ₁ φ₂ ψ₂ : Formula α) :
    Arrow.arrow φ₁ φ₂ = Arrow.arrow ψ₁ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp [Arrow.arrow]


-- @@ L119-131 expanded
@[simp]
lemma neg_inj (φ ψ : Formula α) : Tilde.tilde φ = Tilde.tilde ψ ↔ φ = ψ := by simp [NegAbbrev.neg];
  /-
  instance : ModalDeMorgan (Formula α) where
    verum := rfl
    falsum := rfl
    and := by simp
    or := by simp
    imply := by simp[imp_eq]
    neg := by simp
    dia := by simp
    box := by simp
  -/


-- @@ L133-138 expanded
/-- Formula complexity -/
def complexity : Formula α → ℕ
  | atom _ => 0
  | ⊥ => 0
  | Arrow.arrow φ ψ => max φ.complexity ψ.complexity + 1
  | Box.box φ => φ.complexity + 1


-- @@ L140-145 expanded
/-- Max numbers of `□` -/
def degree : Formula α → Nat
  | atom _ => 0
  | ⊥ => 0
  | Arrow.arrow φ ψ => max φ.degree ψ.degree
  | Box.box φ => φ.degree + 1


-- @@ L147-149 expanded
@[simp]
lemma degree_neg (φ : Formula α) : degree (Tilde.tilde φ) = degree φ := by
  induction φ <;> simp_all [degree]


-- @@ L150-152 expanded
@[simp]
lemma degree_imp (φ ψ : Formula α) : degree (Arrow.arrow φ ψ) = max (degree φ) (degree ψ) := by
  simp [degree]


-- @@ L154-165 expanded
/-- Imported declaration from the Incompleteness formalization. -/
@[elab_as_elim]
def cases' {C : Formula α → Sort w} (hfalsum : C ⊥) (hatom : ∀ a : α, C (atom a))
    (himp : ∀ (φ ψ : Formula α), C (Arrow.arrow φ ψ)) (hbox : ∀ (φ : Formula α), C (Box.box φ)) :
    (φ : Formula α) → C φ
  | ⊥ => hfalsum
  | atom a => hatom a
  | Box.box φ => hbox φ
  | Arrow.arrow φ ψ => himp φ ψ


-- @@ L167-178 expanded
/-- Imported declaration from the Incompleteness formalization. -/
@[elab_as_elim]
def rec' {C : Formula α → Sort w} (hfalsum : C ⊥) (hatom : ∀ a : α, C (atom a))
    (himp : ∀ (φ ψ : Formula α), C φ → C ψ → C (Arrow.arrow φ ψ))
    (hbox : ∀ (φ : Formula α), C φ → C (Box.box φ)) : (φ : Formula α) → C φ
  | ⊥ => hfalsum
  | atom a => hatom a
  | Arrow.arrow φ ψ => himp φ ψ (rec' hfalsum hatom himp hbox φ) (rec' hfalsum hatom himp hbox ψ)
  | Box.box φ => hbox φ (rec' hfalsum hatom himp hbox φ)


-- @@ L180-180 verbatim
section «lp_section_2»


-- @@ L182-182 verbatim
variable [DecidableEq α]


-- @@ L184-185 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def hasDecEq : (φ ψ : Formula α) → Decidable (φ = ψ) := fun _ _ => inferInstance

-- @@ L186-186 verbatim
instance : DecidableEq (Formula α) := hasDecEq


-- @@ L188-188 verbatim
end «lp_section_2»



-- @@ L191-194 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def isBox : Formula α → Bool
  | box _ => true
  | _  => false


-- @@ L196-196 verbatim
end Formula



-- @@ L199-200 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev FormulaSet (α) := Set (Formula α)


-- @@ L202-203 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev FormulaFinset (α) := Finset (Formula α)



-- @@ L206-206 verbatim
namespace Formula


-- @@ L208-208 verbatim
variable {φ ψ χ : Formula α}


-- @@ L210-223 expanded
/-- Imported declaration from the Incompleteness formalization. -/
@[elab_as_elim]
def casesNeg [DecidableEq α] {C : Formula α → Sort w} (hfalsum : C ⊥) (hatom : ∀ a : α, C (atom a))
    (hneg : ∀ φ : Formula α, C (Tilde.tilde φ))
    (himp : ∀ (φ ψ : Formula α), ψ ≠ ⊥ → C (Arrow.arrow φ ψ))
    (hbox : ∀ (φ : Formula α), C (Box.box φ)) : (φ : Formula α) → C φ
  | ⊥ => hfalsum
  | atom a => hatom a
  | Box.box φ => hbox φ
  | Tilde.tilde φ => hneg φ
  | Arrow.arrow φ ψ => if e : ψ = ⊥ then e ▸ hneg φ else himp φ ψ e


-- @@ L225-242 expanded
/-- Imported declaration from the Incompleteness formalization. -/
@[elab_as_elim]
def recNeg [DecidableEq α] {C : Formula α → Sort w} (hfalsum : C ⊥) (hatom : ∀ a : α, C (atom a))
    (hneg : ∀ φ : Formula α, C (φ) → C (Tilde.tilde φ))
    (himp : ∀ (φ ψ : Formula α), ψ ≠ ⊥ → C φ → C ψ → C (Arrow.arrow φ ψ))
    (hbox : ∀ (φ : Formula α), C (φ) → C (Box.box φ)) : (φ : Formula α) → C φ
  | ⊥ => hfalsum
  | atom a => hatom a
  | Box.box φ => hbox φ (recNeg hfalsum hatom hneg himp hbox φ)
  | Tilde.tilde φ => hneg φ (recNeg hfalsum hatom hneg himp hbox φ)
  | Arrow.arrow φ ψ =>
    if e : ψ = ⊥ then e ▸ hneg φ (recNeg hfalsum hatom hneg himp hbox φ)
    else himp φ ψ e (recNeg hfalsum hatom hneg himp hbox φ) (recNeg hfalsum hatom hneg himp hbox ψ)


-- @@ L245-245 verbatim
section «lp_section_3»


-- @@ L247-250 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def negated : Formula α → Bool
  | Tilde.tilde _ => True
  | _ => False


-- @@ L252-252 expanded
@[simp]
lemma negated_def : (Tilde.tilde φ).negated := by simp [negated]


-- @@ L254-259 expanded
@[simp]
lemma negated_imp : (Arrow.arrow φ ψ).negated ↔ (ψ = ⊥) :=
  by
  simp [negated]; split; · simp_all [Formula.imp_eq]; rfl;
  · simp_all [Formula.imp_eq]; simpa;


-- @@ L261-265 expanded
lemma negated_iff : φ.negated ↔ ∃ ψ, φ = Tilde.tilde ψ := by
  classical
    induction φ using Formula.casesNeg with
  | himp => simp [negated_imp, NegAbbrev.neg];
  | _ => simp [negated]


-- @@ L267-271 expanded
lemma not_negated_iff : ¬φ.negated ↔ ∀ ψ, φ ≠ Tilde.tilde ψ := by
  classical
    induction φ using Formula.casesNeg with
  | himp => simp [negated_imp, NegAbbrev.neg];
  | _ => simp [negated]


-- @@ L273-291 expanded
/-- Imported declaration from the Incompleteness formalization. -/
@[elab_as_elim]
def recNegated [DecidableEq α] {C : Formula α → Sort w} (hfalsum : C ⊥)
    (hatom : ∀ a : α, C (atom a)) (hneg : ∀ φ : Formula α, C (φ) → C (Tilde.tilde φ))
    (himp : ∀ (φ ψ : Formula α), ¬(Arrow.arrow φ ψ).negated → C φ → C ψ → C (Arrow.arrow φ ψ))
    (hbox : ∀ (φ : Formula α), C (φ) → C (Box.box φ)) : (φ : Formula α) → C φ
  | ⊥ => hfalsum
  | atom a => hatom a
  | Box.box φ => hbox φ (recNegated hfalsum hatom hneg himp hbox φ)
  | Tilde.tilde φ => hneg φ (recNegated hfalsum hatom hneg himp hbox φ)
  | Arrow.arrow φ ψ => by
    by_cases e : ψ = ⊥
    · exact e ▸ hneg φ (recNegated hfalsum hatom hneg himp hbox φ)
    · refine
        himp φ ψ ?_ (recNegated hfalsum hatom hneg himp hbox φ)
          (recNegated hfalsum hatom hneg himp hbox ψ)
      · simpa [negated_imp]


-- @@ L293-293 verbatim
end «lp_section_3»


-- @@ L295-295 verbatim
section «lp_section_4»


-- @@ L297-297 verbatim
variable [Encodable α]

-- @@ L298-298 verbatim
open Encodable


-- @@ L300-305 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def toNat : Formula α → ℕ
  | atom a => (Nat.pair 0 <| encode a) + 1
  | ⊥ => (Nat.pair 1 0) + 1
  | Box.box φ => (Nat.pair 2 <| φ.toNat) + 1
  | Arrow.arrow φ ψ => (Nat.pair 3 <| φ.toNat.pair ψ.toNat) + 1


-- @@ L307-329 expanded
def ofNat : ℕ → Option (Formula α)
  | 0 => none
  | e + 1 =>
    let idx := e.unpair.1
    let c := e.unpair.2
    match idx with
    | 0 => (decode c).map Formula.atom
    | 1 => some ⊥
    | 2 =>
      have : c < e + 1 := Nat.lt_succ_iff.mpr <| Nat.unpair_right_le _
      do
      let φ ← ofNat c
      return Box.box φ
    | 3 =>
      have : c.unpair.1 < e + 1 :=
        Nat.lt_succ_iff.mpr <| le_trans (Nat.unpair_left_le _) <| Nat.unpair_right_le _
      have : c.unpair.2 < e + 1 :=
        Nat.lt_succ_iff.mpr <| le_trans (Nat.unpair_right_le _) <| Nat.unpair_right_le _
      do
      let φ ← ofNat c.unpair.1
      let ψ ← ofNat c.unpair.2
      return Arrow.arrow φ ψ
    | _ => none


-- @@ L331-335 expanded
lemma ofNat_toNat : ∀ (φ : Formula α), ofNat (toNat φ) = some φ
  | atom a => by simp [toNat, ofNat, Nat.unpair_pair, encodek, Option.map_some];
  | ⊥ => by simp [toNat, ofNat]
  | Box.box φ => by simp [toNat, ofNat, ofNat_toNat φ]
  | Arrow.arrow φ ψ => by simp [toNat, ofNat, ofNat_toNat φ, ofNat_toNat ψ]


-- @@ L337-340 verbatim
instance : Encodable (Formula α) where
  encode := toNat
  decode := ofNat
  encodek := ofNat_toNat


-- @@ L342-342 verbatim
end «lp_section_4»


-- @@ L344-344 verbatim
end Formula


-- @@ L346-346 verbatim
end Modal

-- @@ L347-347 verbatim
end LO
