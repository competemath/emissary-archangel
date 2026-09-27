/-
Copyright (c) 2025 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Data.Fintype.OfMap
public import Mathlib.Algebra.Group.Defs


-- @@ L11-13 verbatim
/-!
Misere combinatorial games.
-/


-- @@ L15-15 verbatim
namespace MisereGames


-- @@ L17-17 verbatim
public section


-- @@ L19-26 verbatim
/-- Either the Left or Right player. -/
@[aesop safe cases]
inductive Player where
  /-- The Left player. -/
  | left  : Player
  /-- The Right player. -/
  | right : Player
deriving DecidableEq, Inhabited


-- @@ L28-31 verbatim
instance : Fintype Player :=
  Fintype.ofList [Player.left, Player.right] (by
    intro player
    cases player <;> simp)


-- @@ L33-33 verbatim
namespace Player


-- @@ L35-39 verbatim
/-- Specify a function `Player → α` from its two outputs. -/
@[simp]
abbrev cases {α : Sort*} (l r : α) : Player → α
  | .left => l
  | .right => r


-- @@ L41-43 verbatim
lemma apply_cases {α β : Sort*} (f : α → β) (l r : α) (p : Player) :
    f (cases l r p) = cases (f l) (f r) p := by
  cases p <;> rfl


-- @@ L45-48 verbatim
@[simp]
theorem cases_inj {α : Sort*} {l₁ r₁ l₂ r₂ : α} :
    cases l₁ r₁ = cases l₂ r₂ ↔ l₁ = l₂ ∧ r₁ = r₂ :=
  ⟨fun h ↦ ⟨congr($h left), congr($h right)⟩, fun ⟨hl, hr⟩ ↦ hl ▸ hr ▸ rfl⟩


-- @@ L50-54 verbatim
theorem const_of_left_eq_right {α : Sort*} {f : Player → α} (hf : f left = f right) :
    ∀ p q, f p = f q
  | left, left | right, right => rfl
  | left, right => hf
  | right, left => hf.symm


-- @@ L56-57 verbatim
theorem const_of_left_eq_right' {f : Player → Prop} (hf : f left ↔ f right) (p q) : f p ↔ f q :=
  (const_of_left_eq_right hf.eq ..).to_iff


-- @@ L59-62 verbatim
@[simp low]
protected lemma «forall» {p : Player → Prop} :
    (∀ x, p x) ↔ p left ∧ p right :=
  ⟨fun h ↦ ⟨h left, h right⟩, fun ⟨hl, hr⟩ ↦ fun | left => hl | right => hr⟩


-- @@ L64-67 verbatim
@[simp low]
protected lemma «exists» {p : Player → Prop} :
    (∃ x, p x) ↔ p left ∨ p right :=
  ⟨fun | ⟨left, h⟩ => .inl h | ⟨right, h⟩ => .inr h, fun | .inl h | .inr h => ⟨_, h⟩⟩


-- @@ L69-70 verbatim
instance : Neg Player where
  neg := cases right left


-- @@ L72-72 verbatim
@[simp] lemma neg_left : -left = right := rfl

-- @@ L73-73 verbatim
@[simp] lemma neg_right : -right = left := rfl


-- @@ L75-78 verbatim
instance : InvolutiveNeg Player where
  neg_neg := by
    intro player
    cases player <;> rfl


-- @@ L80-82 verbatim
@[simp]
theorem ne_iff_eq_neg {a b : Player} : (a ≠ b ↔ a = -b) := by
  cases a <;> cases b <;> simp


-- @@ L84-86 verbatim
protected theorem absurd {p q : Player} (h1 : p = q) (h2 : p = -q) : False := by
  subst h1
  cases p <;> simp at h2


-- @@ L88-89 verbatim
instance : LE Player where
  le lhs rhs := (lhs = .right) ∨ (lhs = .left ∧ rhs = .left)


-- @@ L91-93 verbatim
instance : DecidableLE Player := by
  simp only [DecidableLE, DecidableRel, LE.le]
  infer_instance


-- @@ L95-97 verbatim
theorem le_right_eq (p : Player) (h1 : p ≤ .right) : p = .right := by
  simp only [LE.le, reduceCtorEq, and_false, or_false] at h1
  exact h1


-- @@ L99-104 verbatim
@[simp]
theorem le_right_iff (p : Player) : p ≤ .right ↔ p = .right :=
  ⟨le_right_eq p, by
    intro h
    subst p
    exact Or.inl rfl⟩


-- @@ L106-108 verbatim
theorem le_left_eq (p : Player) (h1 : .left ≤ p) : p = .left := by
  simp only [LE.le, reduceCtorEq, true_and, false_or] at h1
  exact h1


-- @@ L110-115 verbatim
@[simp]
theorem left_le_iff (p : Player) : .left ≤ p ↔ p = .left :=
  ⟨le_left_eq p, by
    intro h
    subst p
    exact Or.inr ⟨rfl, rfl⟩⟩


-- @@ L117-119 verbatim
@[simp]
theorem right_le (p : Player) : .right ≤ p := by
  simp only [LE.le, reduceCtorEq, or_false, false_and]


-- @@ L121-123 verbatim
@[simp]
theorem le_left (p : Player) : p ≤ .left := by
  cases p <;> simp only [LE.le, reduceCtorEq, and_self, or_false, or_true, and_true]


-- @@ L125-126 verbatim
theorem left_le_right (h1 : Player.left ≤ Player.right) : False := by
  simp only [LE.le, reduceCtorEq, and_false, or_self] at h1


-- @@ L128-129 verbatim
theorem not_left_le_right : ¬ Player.left ≤ Player.right :=
  left_le_right


-- @@ L131-131 verbatim
end Player


-- @@ L133-133 verbatim
end


-- @@ L135-135 verbatim
end MisereGames
