/-
Copyright (c) 2026 ruplet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ruplet
-/
module

public import LeanPool.FormalizationOfBoundedArithmetic.LanguagePeano


-- @@ L10-12 verbatim
/-!
# LeanPool.FormalizationOfBoundedArithmetic.BasicSingleSorted
-/


-- @@ L14-14 verbatim
@[expose] public section


-- @@ L16-16 verbatim
open FirstOrder FirstOrder.Language


-- @@ L18-22 verbatim
universe u

-- Section 3.1 Peano Arithmetic; draft page 34 (45 of pdf)
-- semi-bundled design! inspired by mathlib Ring
-- extending peano.Structure instead of One, Add, ... is needed to .Realize

-- @@ L23-36 verbatim
/-- Single-sorted models of the BASIC arithmetic axioms. -/
class BASICModel (num : Type u) extends
  peano.Structure.{u} num
where
  B1 : ∀ {x : num}, (x + 1) ≠ 0
  B2 : ∀ x y : num, (x + 1) = (y + 1) -> x = y
  B3 : ∀ x : num, x + 0 = x
  B4 : ∀ {x y : num}, x + (y + 1) = (x + y) + 1
  B5 : ∀ {x : num}, x * 0 = 0
  B6 : ∀ {x y : num}, x * (y + 1) = x * y + x
  -- le_antisymm
  B7 : ∀ {x y : num}, x <= y -> y <= x -> x = y
  -- le_self_add
  B8 : ∀ {x y : num}, x <= x + y



-- @@ L39-63 verbatim
/-- BASIC models with the additional axiom `(0 : num) + 1 = 1`. -/
class BASICModelExt (num : Type u) extends BASICModel num where
-- skip this axiom by default
-- we will use induction anyway for IDelta0, and it is problematic
-- when defining 2-BASIC axioms and V^i later on

-- it is interesting because BASICModelExt alone implies all
-- true quantifier-free sentences over `peano` language!
-- (source: Logical Foundations, release, p. 40 (p. 58 of PDF))
  C : (0 : num) + 1 = 1

-- instance (M : Type*) [BASICModel M] : Zero M where
--   zero := 0

-- instance (M : Type*) [BASICModel M] : Add M where
--   add x y := x + y

-- instance (M : Type*) [BASICModel M] : Mul M where
--   mul x y := x * y

-- instance (M : Type*) [BASICModel M] : LE M where
--   le x y := x <= y

-- instance (M : Type*) [BASICModel M] : LT M where
--   lt x y := x <= y ∧ x ≠ y


-- @@ L65-65 verbatim
variable {M} [BASICModel M]


-- @@ L67-71 verbatim
/-- Interpret natural-number literals in a BASIC model by iterating successor. -/
def natToM : Nat -> M
| 0 => 0
| 1 => 1
| n + 1 => natToM n + 1


-- @@ L73-74 verbatim
instance instOfNatLeanPool (n) : OfNat M n where
  ofNat := natToM n


-- @@ L76-77 verbatim
/-- Pairing function used to encode two numbers as one number. -/
def pair (x y : M) := (x + y) * (x + y + 1) + (1 + 1) * y


-- @@ L79-80 verbatim
/-- Pairing notation for two numbers. -/
notation "⟨" i "," j "⟩" => pair i j


-- @@ L82-83 verbatim
/-- Pairing notation for three numbers. -/
notation "⟨" i "," j "," k "⟩" => pair (pair i j) k


-- @@ L85-85 verbatim
namespace BASICModel


-- @@ L87-89 verbatim
variable {M : Type u} [iopen : BASICModel M]

-- this is axctually O9. x ≤ x from Logical Foundations

-- @@ L90-93 verbatim
theorem le_refl : ∀ a : M, a <= a := by
  intro x
  conv => right; rw [<- B3 x]
  apply B8


-- @@ L95-95 verbatim
theorem zero_ne_add_one : ∀ x : M, x + 1 ≠ 0 := by apply B1

-- @@ L96-96 verbatim
theorem one_add_right_regular : IsAddRightRegular (1 : M) := by apply B2



-- @@ L99-99 verbatim
end BASICModel
