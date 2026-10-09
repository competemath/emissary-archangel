import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-6 verbatim
/-! Literal Boolean flips and ordinary sensitivity measures.
All maxima range over the actual finite input or block-family space. -/


-- @@ L8-8 verbatim
noncomputable section

-- @@ L9-9 verbatim
open scoped Classical


-- @@ L11-11 verbatim
namespace Paper320


-- @@ L13-15 verbatim
/-- Flip exactly the coordinates belonging to the specified block. -/
def flip {I : Type} (x : I → Bool) (B : Finset I) : I → Bool :=
  fun i => if i ∈ B then !(x i) else x i


-- @@ L17-20 verbatim
/-- The ordinary number of sensitive individual input coordinates. -/
def sensitivityAt {I : Type} [Fintype I]
    (f : (I → Bool) → Bool) (x : I → Bool) : ℕ :=
  (Finset.univ.filter fun i => f (flip x {i}) ≠ f x).card


-- @@ L22-24 verbatim
/-- Maximum ordinary sensitivity over all Boolean inputs. -/
def sensitivity {I : Type} [Fintype I] (f : (I → Bool) → Bool) : ℕ :=
  Finset.univ.sup (sensitivityAt f)


-- @@ L26-33 verbatim
/-- Maximum size of a family of disjoint nonempty sensitive blocks at an input.
The empty family is allowed and contributes zero. Invalid families contribute zero. -/
def blockSensitivityAt {I : Type} [Fintype I]
    (f : (I → Bool) → Bool) (x : I → Bool) : ℕ :=
  Finset.univ.sup fun blocks : Finset (Finset I) =>
    if (∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → Disjoint A B) ∧
        (∀ B ∈ blocks, B.Nonempty ∧ f (flip x B) ≠ f x)
    then blocks.card else 0


-- @@ L35-37 verbatim
/-- Maximum block sensitivity over all Boolean inputs. -/
def blockSensitivity {I : Type} [Fintype I] (f : (I → Bool) → Bool) : ℕ :=
  Finset.univ.sup (blockSensitivityAt f)


-- @@ L39-39 verbatim
end Paper320


-- @@ L41-41 verbatim
end


-- @@ L43-43 verbatim
end OAI
