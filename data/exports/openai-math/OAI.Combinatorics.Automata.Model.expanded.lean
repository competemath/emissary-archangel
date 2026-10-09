import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace OneWayLiveness


-- @@ L7-8 verbatim
@[ext] structure BRel (H : Type*) where
  holds : H → H → Prop

-- @@ L9-9 verbatim
namespace BRel

-- @@ L10-10 verbatim
variable {H : Type*}

-- @@ L11-11 verbatim
instance : One (BRel H) := ⟨⟨Eq⟩⟩

-- @@ L12-12 verbatim
instance : Mul (BRel H) := ⟨fun a b => ⟨fun x z => ∃ y, a.holds x y ∧ b.holds y z⟩⟩

-- @@ L13-13 verbatim
instance : Zero (BRel H) := ⟨⟨fun _ _ => False⟩⟩

-- @@ L14-14 verbatim
@[simp] theorem one_holds (x y : H) : (1 : BRel H).holds x y ↔ x = y := Iff.rfl

-- @@ L15-16 verbatim
@[simp] theorem mul_holds (a b : BRel H) (x z : H) :
    (a * b).holds x z ↔ ∃ y, a.holds x y ∧ b.holds y z := Iff.rfl

-- @@ L17-17 verbatim
@[simp] theorem zero_holds (x y : H) : ¬ (0 : BRel H).holds x y := id

-- @@ L18-25 verbatim
instance : Monoid (BRel H) where
  mul_assoc a b c := by
    ext x z
    change (∃ y, (∃ w, a.holds x w ∧ b.holds w y) ∧ c.holds y z) ↔
      ∃ w, a.holds x w ∧ ∃ y, b.holds w y ∧ c.holds y z
    aesop
  one_mul a := by ext x z; change (∃ y, x = y ∧ a.holds y z) ↔ a.holds x z; simp
  mul_one a := by ext x z; change (∃ y, a.holds x y ∧ y = z) ↔ a.holds x z; simp


-- @@ L27-27 verbatim
def restrictedId (F : Set H) : BRel H := ⟨fun x y => x = y ∧ x ∈ F⟩

-- @@ L28-28 verbatim
def live (w : List (BRel H)) : Prop := ∃ x y, w.prod.holds x y

-- @@ L29-29 verbatim
instance [Finite H] : Finite (BRel H) := Finite.of_injective BRel.holds (fun _ _ h => BRel.ext h)


-- @@ L31-31 verbatim
end BRel


-- @@ L33-33 verbatim
abbrev Alphabet (h : ℕ) := BRel (Fin h)

-- @@ L34-34 verbatim
def OWL (h : ℕ) : Set (List (Alphabet h)) := {w | BRel.live w}


-- @@ L36-39 verbatim
inductive Symbol (Alpha : Type*) where
  | left : Symbol Alpha
  | letter : Alpha → Symbol Alpha
  | right : Symbol Alpha


-- @@ L41-43 verbatim
inductive Move where
  | left | stay | right
  deriving DecidableEq


-- @@ L45-48 verbatim
def Move.Rel : Move → ℕ → ℕ → Prop
  | .left, i, j => j + 1 = i
  | .stay, i, j => j = i
  | .right, i, j => j = i + 1


-- @@ L50-54 verbatim
/-- The finite word including both endmarkers. -/
def scanned {Alpha : Type*} (w : List Alpha) (i : Fin (w.length + 2)) : Symbol Alpha :=
  if h0 : i.val = 0 then .left
  else if hi : i.val < w.length + 1 then .letter (w[i.val - 1]'(by omega))
  else .right


-- @@ L56-56 verbatim
abbrev Configuration {Alpha : Type*} (w : List Alpha) (n : ℕ) := Fin (w.length + 2) × Fin n


-- @@ L58-63 verbatim
structure DMachine (Alpha : Type*) (s : ℕ) where
  initial : Fin s
  accepting : Set (Fin s)
  transition : Fin s → Symbol Alpha → Option (Fin s × Move)
  left_boundary : ∀ q q', transition q .left ≠ some (q', .left)
  right_boundary : ∀ q q', transition q .right ≠ some (q', .right)


-- @@ L65-70 verbatim
structure NMachine (Alpha : Type*) (n : ℕ) where
  initial : Fin n
  accepting : Set (Fin n)
  transition : Fin n → Symbol Alpha → Set (Fin n × Move)
  left_boundary : ∀ q q', (q', .left) ∉ transition q .left
  right_boundary : ∀ q q', (q', .right) ∉ transition q .right


-- @@ L72-74 verbatim
def DMachine.Step {Alpha : Type*} {s : ℕ} (M : DMachine Alpha s) (w : List Alpha)
    (c c' : Configuration w s) : Prop :=
  ∃ d, M.transition c.2 (scanned w c.1) = some (c'.2, d) ∧ d.Rel c.1.val c'.1.val


-- @@ L76-78 verbatim
def NMachine.Step {Alpha : Type*} {n : ℕ} (M : NMachine Alpha n) (w : List Alpha)
    (c c' : Configuration w n) : Prop :=
  ∃ d, (c'.2, d) ∈ M.transition c.2 (scanned w c.1) ∧ d.Rel c.1.val c'.1.val


-- @@ L80-82 verbatim
/-- The positive convention explicitly excludes a length-zero computation. -/
def FiniteRun {C : Type*} (positive : Bool) (step : C → C → Prop) (c c' : C) : Prop :=
  if positive then Relation.TransGen step c c' else Relation.ReflTransGen step c c'


-- @@ L84-86 verbatim
def DMachine.Accepts {Alpha : Type*} {s : ℕ} (M : DMachine Alpha s)
    (positive : Bool) (w : List Alpha) : Prop :=
  ∃ c, FiniteRun positive (M.Step w) (⟨0, by omega⟩, M.initial) c ∧ c.2 ∈ M.accepting


-- @@ L88-90 verbatim
def NMachine.Accepts {Alpha : Type*} {n : ℕ} (M : NMachine Alpha n)
    (positive : Bool) (w : List Alpha) : Prop :=
  ∃ c, FiniteRun positive (M.Step w) (⟨0, by omega⟩, M.initial) c ∧ c.2 ∈ M.accepting


-- @@ L92-93 verbatim
def NMachine.NoLeft {Alpha : Type*} {n : ℕ} (M : NMachine Alpha n) : Prop :=
  ∀ q a q', (q', Move.left) ∉ M.transition q a


-- @@ L95-96 verbatim
def NMachine.Recognizes {Alpha : Type*} {n : ℕ} (M : NMachine Alpha n)
    (positive : Bool) (L : Set (List Alpha)) : Prop := ∀ w, M.Accepts positive w ↔ w ∈ L


-- @@ L98-99 verbatim
def DMachine.Recognizes {Alpha : Type*} {s : ℕ} (M : DMachine Alpha s)
    (positive : Bool) (L : Set (List Alpha)) : Prop := ∀ w, M.Accepts positive w ↔ w ∈ L


-- @@ L101-107 verbatim
/-- An alphabet-independent polynomial bound for deterministic simulation. -/
def PolynomialSimulation (positive : Bool) : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (Alpha : Type) (_ : Fintype Alpha) (n : ℕ) (N : NMachine Alpha n),
    ∃ (s : ℕ) (D : DMachine Alpha s),
      (s : ℝ) ≤ C * (n : ℝ) ^ c ∧
      ∀ w, D.Accepts positive w ↔ N.Accepts positive w


-- @@ L109-109 verbatim
end OneWayLiveness


-- @@ L111-111 verbatim
end OAI
