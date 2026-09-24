module

public import Foundation.FirstOrder.Order.Le


-- @@ L5-5 verbatim
@[expose] public section

-- @@ L6-11 verbatim
/-! # Preperations for arithmetic

- *NOTE*:
  To avoid the duplicate definitions of `Structure ℒₒᵣ` for models,
  we basically use `ORingStructure`, and generated `standardStructure` instead of `Structure ℒₒᵣ` itself.
-/


-- @@ L13-13 verbatim
namespace FFL


-- @@ L15-15 verbatim
class ORingStructure (α : Type*) extends Zero α, One α, Add α, Mul α, LT α


-- @@ L17-17 verbatim
instance [Zero α] [One α] [Add α] [Mul α] [LT α] : ORingStructure α where


-- @@ L19-19 verbatim
namespace ORingStructure


-- @@ L21-21 verbatim
variable {α : Type*} [ORingStructure α]


-- @@ L23-26 verbatim
def numeral : ℕ → α
  |     0 => 0
  |     1 => 1
  | n + 2 => numeral (n + 1) + 1

 
-- @@ L28-28 verbatim
@[simp] lemma zero_eq_zero : (numeral 0 : α) = 0 := rfl

 
-- @@ L30-30 verbatim
@[simp] lemma one_eq_one : (numeral 1 : α) = 1 := rfl


-- @@ L32-32 verbatim
end ORingStructure


-- @@ L34-37 verbatim
@[simp] lemma Nat.numeral_eq : (n : ℕ) → ORingStructure.numeral n = n
  |     0 => rfl
  |     1 => rfl
  | n + 2 => by simp [ORingStructure.numeral, Nat.numeral_eq (n + 1)]


-- @@ L39-39 verbatim
namespace FirstOrder


-- @@ L41-41 verbatim
abbrev ArithmeticTheory := Theory ℒₒᵣ


-- @@ L43-43 verbatim
abbrev ArithmeticSemiterm (ξ : Type*) (n : ℕ) := Semiterm ℒₒᵣ ξ n


-- @@ L45-45 verbatim
abbrev ArithmeticTerm (ξ : Type*) := Term ℒₒᵣ ξ


-- @@ L47-47 verbatim
abbrev ArithmeticSemiformula (ξ : Type*) (n : ℕ) := Semiformula ℒₒᵣ ξ n


-- @@ L49-49 verbatim
abbrev ArithmeticFormula (ξ : Type*) := Formula ℒₒᵣ ξ


-- @@ L51-51 verbatim
abbrev ArithmeticSemisentence (n : ℕ) := Semisentence ℒₒᵣ n


-- @@ L53-53 verbatim
abbrev ArithmeticSentence := Sentence ℒₒᵣ


-- @@ L55-55 verbatim
abbrev ArithmeticSemiproposition (n : ℕ) := Semiproposition ℒₒᵣ n


-- @@ L57-57 verbatim
abbrev ArithmeticProposition := Proposition ℒₒᵣ


-- @@ L59-59 verbatim
section ToString


-- @@ L61-61 verbatim
variable {L : Language} [L.ORing]


-- @@ L63-63 verbatim
variable [ToString ξ]


-- @@ L65-71 verbatim
def Semiterm.toStringORing : ArithmeticSemiterm ξ n → String
  |                        #x => "x_{" ++ toString (n - 1 - (x : ℕ)) ++ "}"
  |                        &x => "a_{" ++ toString x ++ "}"
  | func Language.Zero.zero _ => "0"
  |   func Language.One.one _ => "1"
  |   func Language.Add.add v => "(" ++ toStringORing (v 0) ++ " + " ++ toStringORing (v 1) ++ ")"
  |   func Language.Mul.mul v => "(" ++ toStringORing (v 0) ++ " \\cdot " ++ toStringORing (v 1) ++ ")"


-- @@ L73-73 verbatim
instance : Repr (ArithmeticSemiterm ξ n) := ⟨fun t _ ↦ t.toStringORing⟩


-- @@ L75-75 verbatim
instance : ToString (ArithmeticSemiterm ξ n) := ⟨Semiterm.toStringORing⟩


-- @@ L77-89 verbatim
def Semiformula.toStringORing : ∀ {n}, ArithmeticSemiformula ξ n → String
  | _,                             ⊤ => "\\top"
  | _,                             ⊥ => "\\bot"
  | _,          rel Language.Eq.eq v => (v 0).toStringORing ++ " = " ++ (v 1).toStringORing
  | _,          rel Language.LT.lt v => (v 0).toStringORing ++ " < " ++ (v 1).toStringORing
  | _,         nrel Language.Eq.eq v => (v 0).toStringORing ++ " \\not = " ++ (v 1).toStringORing
  | _,         nrel Language.LT.lt v => (v 0).toStringORing ++ " \\not < " ++ (v 1).toStringORing
  | _,                         φ ⋏ ψ => "[" ++ φ.toStringORing ++ "]" ++ " \\land " ++ "[" ++ ψ.toStringORing ++ "]"
  | _,                         φ ⋎ ψ => "[" ++ φ.toStringORing ++ "]" ++ " \\lor "  ++ "[" ++ ψ.toStringORing ++ "]"
  | n, ∀¹ (rel Language.LT.lt v 🡒 φ) => "(\\forall x_{" ++ toString n ++ "} < " ++ (v 1).toStringORing ++ ") " ++ "[" ++ φ.toStringORing ++ "]"
  | n, ∃¹ (rel Language.LT.lt v ⋏ φ) => "(\\exists x_{" ++ toString n ++ "} < " ++ (v 1).toStringORing ++ ") " ++ "[" ++ φ.toStringORing ++ "]"
  | n,                          ∀¹ φ => "(\\forall x_{" ++ toString n ++ "}) " ++ "[" ++ φ.toStringORing ++ "]"
  | n,                          ∃¹ φ => "(\\exists x_{" ++ toString n ++ "}) " ++ "[" ++ φ.toStringORing ++ "]"


-- @@ L91-91 verbatim
instance : Repr (ArithmeticSemiformula ξ n) := ⟨fun φ _ ↦ φ.toStringORing⟩


-- @@ L93-93 verbatim
instance : ToString (ArithmeticSemiformula ξ n) := ⟨Semiformula.toStringORing⟩


-- @@ L95-95 verbatim
end ToString


-- @@ L97-97 verbatim
namespace Arithmetic


-- @@ L99-99 verbatim
open Encodable Semiterm.Operator.GödelNumber


-- @@ L101-101 verbatim
variable {α} [Encodable α]


-- @@ L103-113 verbatim
instance : Semiterm.Operator.GödelNumber ℒₒᵣ α :=
  Semiterm.Operator.GödelNumber.ofEncodable

lemma gödelNumber_def (a : α) :
  gödelNumber a = Semiterm.Operator.encode ℒₒᵣ a := rfl

lemma gödelNumber'_def (a : α) :
  (⌜a⌝ : ArithmeticSemiterm ξ n) = Semiterm.Operator.encode ℒₒᵣ a := rfl

lemma gödelNumber'_eq_coe_encode (a : α) :
  (⌜a⌝ : ArithmeticSemiterm ξ n) = ↑(Encodable.encode a) := rfl


-- @@ L115-116 verbatim
@[simp] lemma encode_encode_eq (a : α) :
    (gödelNumber (encode a) : Semiterm.Const ℒₒᵣ) = gödelNumber a := by simp [Semiterm.Operator.encode, gödelNumber_def]


-- @@ L118-120 verbatim
@[simp] lemma rew_gödelNumber' (ω : Rew ℒₒᵣ ξ₁ n₁ ξ₂ n₂) (a : α) :
    ω ⌜a⌝ = ⌜a⌝ := by
  simp [gödelNumber'_def]


-- @@ L122-122 verbatim
end Arithmetic


-- @@ L124-124 verbatim
/-! ### Semantics of arithmetic  -/


-- @@ L126-127 verbatim
class Structure.ORing (L : Language) [L.ORing] (M : Type w) [ORingStructure M] [Structure L M] extends
  Structure.Zero L M, Structure.One L M, Structure.Add L M, Structure.Mul L M, Structure.Eq L M, Structure.LT L M


-- @@ L129-129 verbatim
attribute [instance] Structure.ORing.mk


-- @@ L131-131 verbatim
namespace Structure


-- @@ L133-133 verbatim
open Semiterm Semiformula


-- @@ L135-136 verbatim
variable [Operator.Zero L] [Operator.One L] [Operator.Add L] {M : Type u} [ORingStructure M]
  [Structure L M] [Structure.Zero L M] [Structure.One L M] [Structure.Add L M]


-- @@ L138-142 verbatim
@[simp] lemma numeral_eq_numeral : (z : ℕ) → (Semiterm.Operator.numeral L z).val ![] = (ORingStructure.numeral z : M)
  | 0     => by simp [ORingStructure.numeral, Semiterm.Operator.numeral_zero]
  | 1     => by simp [ORingStructure.numeral, Semiterm.Operator.numeral_one]
  | z + 2 => by simp [ORingStructure.numeral, Semiterm.Operator.numeral_add_two,
                  Semiterm.Operator.val_comp, Matrix.fun_eq_vec_two, numeral_eq_numeral (z + 1)]


-- @@ L144-144 verbatim
end Structure


-- @@ L146-146 verbatim
namespace Semiformula


-- @@ L148-148 verbatim
variable {L : Language} [L.LT] [L.Zero] [L.One] [L.Add]


-- @@ L150-150 verbatim
def ballLTSucc (t : Semiterm L ξ n) (φ : Semiformula L ξ (n + 1)) : Semiformula L ξ n := φ.ballLT ‘!!t + 1’


-- @@ L152-152 verbatim
def bexsLTSucc (t : Semiterm L ξ n) (φ : Semiformula L ξ (n + 1)) : Semiformula L ξ n := φ.bexsLT ‘!!t + 1’


-- @@ L154-162 verbatim
variable {M : Type*} {s : Structure L M} [LT M] [One M] [Add M] [Structure.LT L M] [Structure.One L M] [Structure.Add L M]

lemma eval_ballLTSucc {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ n} {fv bv} :
    (φ.ballLTSucc t).Eval (M := M) fv bv ↔ ∀ x < t.val (M := M) fv bv + 1, φ.Eval (M := M) (x :> fv) bv := by
  simp [ballLTSucc, Semiterm.Operator.numeral]

lemma eval_bexsLTSucc {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ n} {fv bv} :
    (φ.bexsLTSucc t).Eval (M := M) fv bv ↔ ∃ x < t.val (M := M) fv bv + 1, φ.Eval (M := M) (x :> fv) bv := by
  simp [bexsLTSucc, Semiterm.Operator.numeral]


-- @@ L164-164 verbatim
end Semiformula


-- @@ L166-166 verbatim
namespace BinderNotation


-- @@ L168-168 verbatim
open Lean PrettyPrinter Delaborator SubExpr


-- @@ L170-170 verbatim
syntax:max "∀ " ident " <⁺ " first_order_term ", " first_order_formula:0 : first_order_formula


-- @@ L172-172 verbatim
syntax:max "∃ " ident " <⁺ " first_order_term ", " first_order_formula:0 : first_order_formula


-- @@ L174-182 verbatim
macro_rules
  | `(⤫formula(lit)[ $binders* | $fbinders* | ∀ $x <⁺ $t, $φ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    let binders' := binders.insertIdx 0 x
    `(Semiformula.ballLTSucc ⤫term(lit)[ $binders* | $fbinders* | $t ] ⤫formula(lit)[ $binders'* | $fbinders* | $φ ])
  | `(⤫formula(lit)[ $binders* | $fbinders* | ∃ $x <⁺ $t, $φ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    let binders' := binders.insertIdx 0 x
    `(Semiformula.bexsLTSucc ⤫term(lit)[ $binders* | $fbinders* | $t ] ⤫formula(lit)[ $binders'* | $fbinders* | $φ ])


-- @@ L184-184 verbatim
end BinderNotation


-- @@ L186-186 verbatim
end FirstOrder


-- @@ L188-188 verbatim
end FFL
