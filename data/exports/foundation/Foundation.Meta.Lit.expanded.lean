module

public import Foundation.Meta.Qq
public import Foundation.Logic.LogicSymbol


-- @@ L6-6 verbatim
public section


-- @@ L8-8 verbatim
namespace FFL.Meta


-- @@ L10-10 verbatim
open Mathlib Qq Lean Elab Meta Tactic


-- @@ L12-20 verbatim
inductive Litform (α : Type*) : Type _
  | atom (a : α)  : Litform α
  | verum         : Litform α
  | falsum        : Litform α
  | and           : Litform α → Litform α → Litform α
  | or            : Litform α → Litform α → Litform α
  | neg           : Litform α → Litform α
  | imply         : Litform α → Litform α → Litform α
  | iff           : Litform α → Litform α → Litform α


-- @@ L22-22 verbatim
namespace Litform


-- @@ L24-28 verbatim
instance : LogicalConnective (Litform α) where
  wedge := Litform.and
  vee   := Litform.or
  arrow := Litform.imply
  tilde := Litform.neg


-- @@ L30-32 verbatim
instance : LogicalNeutral (Litform α) where
  top := Litform.verum
  bot := Litform.falsum


-- @@ L34-34 verbatim
section ToString


-- @@ L36-44 verbatim
def toStr [ToString α] : Litform α → String
  |       ⊤ => "⊤"
  |       ⊥ => "⊥"
  |  atom a => s!"atom {toString a}"
  |      ∼φ => "(¬" ++ toStr φ ++ ")"
  |   φ ⋏ ψ => "(" ++ toStr φ ++ " ∧ " ++ toStr ψ ++ ")"
  |   φ ⋎ ψ => "(" ++ toStr φ ++ " ∨ "  ++ toStr ψ ++ ")"
  |   φ 🡒 ψ => "(" ++ toStr φ ++ " → "  ++ toStr ψ ++ ")"
  | iff φ ψ => "(" ++ toStr φ ++ " ↔ "  ++ toStr ψ ++ ")"


-- @@ L46-46 verbatim
instance [ToString α] : ToString (Litform α) := ⟨toStr⟩



-- @@ L49-57 verbatim
def format [Repr α] : Litform α → Format
  |       ⊤ => s!"⊤"
  |       ⊥ => s!"⊥"
  |  atom a => repr a
  |      ∼φ => s!"(¬{format φ})"
  |   φ ⋏ ψ => s!"({format φ} ∧ {format ψ})"
  |   φ ⋎ ψ => s!"({format φ} ∨ {format ψ})"
  |   φ 🡒 ψ => s!"({format φ} → {format ψ})"
  | iff φ ψ => s!"({format φ} ↔ {format ψ})"


-- @@ L59-59 verbatim
instance [Repr α] : Repr (Litform α) := ⟨fun t _ ↦ format t⟩


-- @@ L61-61 verbatim
end ToString


-- @@ L63-63 verbatim
variable (F : Q(Type*)) (ls : Q(LogicalConnective $F)) (ln : Q(LogicalNeutral $F))


-- @@ L65-65 verbatim
abbrev _root_.FFL.Meta.Lit := Litform Expr


-- @@ L67-67 verbatim
variable {F}


-- @@ L69-77 verbatim
abbrev toExpr : Lit → Q($F)
  |  atom e => e
  |       ⊤ => q(⊤)
  |       ⊥ => q(⊥)
  |   φ ⋏ ψ => q($(toExpr φ) ⋏ $(toExpr ψ))
  |   φ ⋎ ψ => q($(toExpr φ) ⋎ $(toExpr ψ))
  |      ∼φ => q(∼$(toExpr φ))
  |   φ 🡒 ψ => q($(toExpr φ) 🡒 $(toExpr ψ))
  | iff φ ψ => q($(toExpr φ) 🡘 $(toExpr ψ))


-- @@ L79-82 verbatim
partial def summands {α : Q(Type $u)} (inst : Q(Add $α)) :
    Q($α) → MetaM (List Q($α))
  | ~q($x + $y) => return (← summands inst x) ++ (← summands inst y)
  | n => return [n]


-- @@ L84-92 verbatim
partial def denote : Q($F) → MetaM Lit
  |       ~q(⊤) => return ⊤
  |       ~q(⊥) => return ⊥
  | ~q($φ ⋏ $ψ) => return (←denote φ) ⋏ (←denote ψ)
  | ~q($φ ⋎ $ψ) => return (←denote φ) ⋎ (←denote ψ)
  | ~q($φ 🡒 $ψ) => return (←denote φ) 🡒 (←denote ψ)
  | ~q($φ 🡘 $ψ) => return iff (←denote φ) (←denote ψ)
  |     ~q(∼$φ) => return ∼(←denote φ)
  |      ~q($e) => return atom e


-- @@ L94-102 verbatim
@[simp] def complexity : Litform α → ℕ
  |  atom _ => 0
  |       ⊤ => 0
  |       ⊥ => 0
  |   φ ⋏ ψ => max φ.complexity ψ.complexity + 1
  |   φ ⋎ ψ => max φ.complexity ψ.complexity + 1
  |      ∼φ => φ.complexity + 1
  |   φ 🡒 ψ => max φ.complexity ψ.complexity + 1
  | iff φ ψ => max φ.complexity ψ.complexity + 1


-- @@ L104-104 verbatim
end Litform


-- @@ L106-106 verbatim
namespace Lit


-- @@ L108-117 verbatim
def DEq : Lit → Lit → MetaM Bool
  |    .atom e,   .atom e' => Lean.Meta.isDefEq e e'
  |          ⊤,          ⊤ => return true
  |          ⊥,          ⊥ => return true
  |         ∼φ,         ∼ψ => return (← DEq φ ψ)
  |    φ₁ ⋏ ψ₁,    φ₂ ⋏ ψ₂ => return (← DEq φ₁ φ₂) && (← DEq ψ₁ ψ₂)
  |    φ₁ ⋎ ψ₁,    φ₂ ⋎ ψ₂ => return (← DEq φ₁ φ₂) && (← DEq ψ₁ ψ₂)
  |    φ₁ 🡒 ψ₁,    φ₂ 🡒 ψ₂ => return (← DEq φ₁ φ₂) && (← DEq ψ₁ ψ₂)
  | .iff φ₁ ψ₁, .iff φ₂ ψ₂ => return (← DEq φ₁ φ₂) && (← DEq ψ₁ ψ₂)
  |          _,          _ => return false


-- @@ L119-120 verbatim
def dMem (φ : Lit) (Δ : List Lit) : MetaM Bool :=
  Δ.foldrM (fun ψ ih ↦ return (←DEq φ ψ) || ih) false


-- @@ L122-125 verbatim
def dSubsetList (Γ Δ : List Lit) : MetaM Bool := do
  match Γ with
  |     [] => return true
  | φ :: Γ => return (←φ.dMem Γ) && (←dSubsetList Γ Δ)


-- @@ L127-127 verbatim
end Lit


-- @@ L129-129 verbatim
end FFL.Meta


-- @@ L131-131 verbatim
end
