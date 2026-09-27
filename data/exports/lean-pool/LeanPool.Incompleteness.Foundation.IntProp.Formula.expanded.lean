/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Logic.LogicSymbol
import Mathlib.Tactic.Bound.Init


-- @@ L11-11 verbatim
/-! # Formula -/


-- @@ L13-13 verbatim
@[expose] public section



-- @@ L16-16 verbatim
namespace LO

-- @@ L17-17 verbatim
namespace IntProp


-- @@ L19-26 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
inductive Formula (α : Type u) : Type u
  | atom   : α → Formula α
  | falsum : Formula α
  | and    : Formula α → Formula α → Formula α
  | or     : Formula α → Formula α → Formula α
  | imp    : Formula α → Formula α → Formula α
  deriving DecidableEq


-- @@ L28-28 verbatim
namespace Formula


-- @@ L30-31 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev neg {α : Type u} (φ : Formula α) : Formula α := imp φ falsum


-- @@ L33-34 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev verum {α : Type u} : Formula α := imp falsum falsum


-- @@ L36-42 verbatim
instance : LogicalConnective (Formula α) where
  tilde := neg
  arrow := imp
  wedge := and
  vee := or
  top := verum
  bot := falsum


-- @@ L44-44 verbatim
instance : LO.NegAbbrev (Formula α) := by tauto;


-- @@ L46-46 verbatim
section «lp_section_1»


-- @@ L48-48 verbatim
variable [ToString α]


-- @@ L50-58 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def toStr : Formula α → String
  | ⊤ => "\\top"
  | ⊥ => "\\bot"
  | atom a => "{" ++ toString a ++ "}"
  | Tilde.tilde φ => "\\lnot " ++ toStr φ
  | Wedge.wedge φ ψ => "\\left(" ++ toStr φ ++ " \\land " ++ toStr ψ ++ "\\right)"
  | Vee.vee φ ψ => "\\left(" ++ toStr φ ++ " \\lor " ++ toStr ψ ++ "\\right)"
  | Arrow.arrow φ ψ => "\\left(" ++ toStr φ ++ " \\rightarrow " ++ toStr ψ ++ "\\right)"


-- @@ L60-60 verbatim
instance : Repr (Formula α) := ⟨fun t _ => toStr t⟩

-- @@ L61-61 verbatim
instance : ToString (Formula α) := ⟨toStr⟩


-- @@ L63-63 verbatim
end «lp_section_1»


-- @@ L65-66 expanded
@[simp]
lemma and_inj (φ₁ ψ₁ φ₂ ψ₂ : Formula α) :
    Wedge.wedge φ₁ φ₂ = Wedge.wedge ψ₁ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp [Wedge.wedge]


-- @@ L68-69 expanded
@[simp]
lemma or_inj (φ₁ ψ₁ φ₂ ψ₂ : Formula α) : Vee.vee φ₁ φ₂ = Vee.vee ψ₁ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by
  simp [Vee.vee]


-- @@ L71-72 expanded
@[simp]
lemma imp_inj (φ₁ ψ₁ φ₂ ψ₂ : Formula α) :
    Arrow.arrow φ₁ φ₂ = Arrow.arrow ψ₁ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp [Arrow.arrow]


-- @@ L74-74 expanded
@[simp]
lemma neg_inj (φ ψ : Formula α) : Tilde.tilde φ = Tilde.tilde ψ ↔ φ = ψ := by simp [Tilde.tilde]


-- @@ L77-77 expanded
lemma neg_def (φ : Formula α) : Tilde.tilde φ = Arrow.arrow φ ⊥ :=
  rfl


-- @@ L79-79 expanded
lemma top_def : (⊤ : Formula α) = Arrow.arrow ⊥ ⊥ :=
  rfl


-- @@ L82-82 expanded
lemma iff_def (φ ψ : Formula α) :
    LogicalConnective.iff φ ψ = Wedge.wedge (Arrow.arrow φ ψ) (Arrow.arrow ψ φ) := by rfl


-- @@ L84-90 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def complexity : Formula α → ℕ
  | atom _ => 0
  | ⊥ => 0
  | Arrow.arrow φ ψ => max φ.complexity ψ.complexity + 1
  | Wedge.wedge φ ψ => max φ.complexity ψ.complexity + 1
  | Vee.vee φ ψ => max φ.complexity ψ.complexity + 1


-- @@ L92-92 verbatim
@[simp] lemma complexity_bot : complexity (⊥ : Formula α) = 0 := rfl


-- @@ L94-94 verbatim
@[simp] lemma complexity_atom (a : α) : complexity (atom a) = 0 := rfl


-- @@ L96-98 expanded
@[simp]
lemma complexity_imp (φ ψ : Formula α) :
    complexity (Arrow.arrow φ ψ) = max φ.complexity ψ.complexity + 1 :=
  rfl


-- @@ L99-101 verbatim
@[simp] lemma complexity_imp' (φ ψ : Formula α) :
    complexity (imp φ ψ) = max φ.complexity ψ.complexity + 1 :=
  rfl


-- @@ L103-105 expanded
@[simp]
lemma complexity_and (φ ψ : Formula α) :
    complexity (Wedge.wedge φ ψ) = max φ.complexity ψ.complexity + 1 :=
  rfl


-- @@ L106-108 verbatim
@[simp] lemma complexity_and' (φ ψ : Formula α) :
    complexity (and φ ψ) = max φ.complexity ψ.complexity + 1 :=
  rfl


-- @@ L110-112 expanded
@[simp]
lemma complexity_or (φ ψ : Formula α) :
    complexity (Vee.vee φ ψ) = max φ.complexity ψ.complexity + 1 :=
  rfl


-- @@ L113-115 verbatim
@[simp] lemma complexity_or' (φ ψ : Formula α) :
    complexity (or φ ψ) = max φ.complexity ψ.complexity + 1 :=
  rfl


-- @@ L117-130 expanded
/-- Imported declaration from the Incompleteness formalization. -/
@[elab_as_elim]
def cases' {C : Formula α → Sort w} (hfalsum : C ⊥) (hatom : ∀ a : α, C (atom a))
    (himp : ∀ (φ ψ : Formula α), C (Arrow.arrow φ ψ))
    (hand : ∀ (φ ψ : Formula α), C (Wedge.wedge φ ψ)) (hor : ∀ (φ ψ : Formula α), C (Vee.vee φ ψ)) :
    (φ : Formula α) → C φ
  | ⊥ => hfalsum
  | atom a => hatom a
  | Arrow.arrow φ ψ => himp φ ψ
  | Wedge.wedge φ ψ => hand φ ψ
  | Vee.vee φ ψ => hor φ ψ


-- @@ L132-145 expanded
/-- Imported declaration from the Incompleteness formalization. -/
@[elab_as_elim]
def rec' {C : Formula α → Sort w} (hfalsum : C ⊥) (hatom : ∀ a : α, C (atom a))
    (himp : ∀ (φ ψ : Formula α), C φ → C ψ → C (Arrow.arrow φ ψ))
    (hand : ∀ (φ ψ : Formula α), C φ → C ψ → C (Wedge.wedge φ ψ))
    (hor : ∀ (φ ψ : Formula α), C φ → C ψ → C (Vee.vee φ ψ)) : (φ : Formula α) → C φ
  | ⊥ => hfalsum
  | atom a => hatom a
  | Arrow.arrow φ ψ =>
    himp φ ψ (rec' hfalsum hatom himp hand hor φ) (rec' hfalsum hatom himp hand hor ψ)
  | Wedge.wedge φ ψ =>
    hand φ ψ (rec' hfalsum hatom himp hand hor φ) (rec' hfalsum hatom himp hand hor ψ)
  | Vee.vee φ ψ => hor φ ψ (rec' hfalsum hatom himp hand hor φ) (rec' hfalsum hatom himp hand hor ψ)


-- @@ L147-147 verbatim
section «lp_section_2»


-- @@ L149-149 verbatim
variable [DecidableEq α]


-- @@ L151-152 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def hasDecEq : (φ ψ : Formula α) → Decidable (φ = ψ) := fun _ _ => inferInstance


-- @@ L154-154 verbatim
instance : DecidableEq (Formula α) := hasDecEq


-- @@ L156-156 verbatim
end «lp_section_2»


-- @@ L158-158 verbatim
section «lp_section_3»


-- @@ L160-160 verbatim
variable [Encodable α]

-- @@ L161-161 verbatim
open Encodable


-- @@ L163-169 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def toNat : Formula α → ℕ
  | ⊥ => (Nat.pair 0 0) + 1
  | atom a => (Nat.pair 1 <| encode a) + 1
  | Arrow.arrow φ ψ => (Nat.pair 2 <| φ.toNat.pair ψ.toNat) + 1
  | Wedge.wedge φ ψ => (Nat.pair 3 <| φ.toNat.pair ψ.toNat) + 1
  | Vee.vee φ ψ => (Nat.pair 4 <| φ.toNat.pair ψ.toNat) + 1


-- @@ L171-206 expanded
def ofNat : ℕ → Option (Formula α)
  | 0 => none
  | e + 1 =>
    let idx := e.unpair.1
    let c := e.unpair.2
    match idx with
    | 0 => some ⊥
    | 1 => (decode c).map Formula.atom
    | 2 =>
      have : c.unpair.1 < e + 1 :=
        Nat.lt_succ_iff.mpr <| le_trans (Nat.unpair_left_le _) <| Nat.unpair_right_le _
      have : c.unpair.2 < e + 1 :=
        Nat.lt_succ_iff.mpr <| le_trans (Nat.unpair_right_le _) <| Nat.unpair_right_le _
      do
      let φ ← ofNat c.unpair.1
      let ψ ← ofNat c.unpair.2
      return Arrow.arrow φ ψ
    | 3 =>
      have : c.unpair.1 < e + 1 :=
        Nat.lt_succ_iff.mpr <| le_trans (Nat.unpair_left_le _) <| Nat.unpair_right_le _
      have : c.unpair.2 < e + 1 :=
        Nat.lt_succ_iff.mpr <| le_trans (Nat.unpair_right_le _) <| Nat.unpair_right_le _
      do
      let φ ← ofNat c.unpair.1
      let ψ ← ofNat c.unpair.2
      return Wedge.wedge φ ψ
    | 4 =>
      have : c.unpair.1 < e + 1 :=
        Nat.lt_succ_iff.mpr <| le_trans (Nat.unpair_left_le _) <| Nat.unpair_right_le _
      have : c.unpair.2 < e + 1 :=
        Nat.lt_succ_iff.mpr <| le_trans (Nat.unpair_right_le _) <| Nat.unpair_right_le _
      do
      let φ ← ofNat c.unpair.1
      let ψ ← ofNat c.unpair.2
      return Vee.vee φ ψ
    | _ => none


-- @@ L208-213 expanded
lemma ofNat_toNat : ∀ (φ : Formula α), ofNat (toNat φ) = some φ
  | atom a => by simp [toNat, ofNat, Nat.unpair_pair, encodek, Option.map_some];
  | ⊥ => by simp [toNat, ofNat]
  | Arrow.arrow φ ψ => by simp [toNat, ofNat, ofNat_toNat φ, ofNat_toNat ψ]
  | Wedge.wedge φ ψ => by simp [toNat, ofNat, ofNat_toNat φ, ofNat_toNat ψ]
  | Vee.vee φ ψ => by simp [toNat, ofNat, ofNat_toNat φ, ofNat_toNat ψ]


-- @@ L215-218 verbatim
instance : Encodable (Formula α) where
  encode := toNat
  decode := ofNat
  encodek := ofNat_toNat


-- @@ L220-220 verbatim
end «lp_section_3»


-- @@ L222-222 verbatim
end Formula



-- @@ L225-226 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev FormulaSet (α : Type u) := Set (Formula α)


-- @@ L228-229 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev FormulaFinset (α : Type u) := Finset (Formula α)


-- @@ L231-231 verbatim
end IntProp

-- @@ L232-232 verbatim
end LO
