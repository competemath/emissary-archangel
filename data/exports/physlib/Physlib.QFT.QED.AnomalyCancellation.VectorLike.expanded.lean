/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.QED.AnomalyCancellation.Sorts

-- @@ L9-14 verbatim
/-!
# Vector like charges

For the `n`-even case we define the property of a charge assignment being vector like.

-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
open Nat

-- @@ L19-19 verbatim
open Finset

-- @@ L20-20 verbatim
open BigOperators


-- @@ L22-22 verbatim
namespace PureU1


-- @@ L24-24 verbatim
variable {n : ℕ}


-- @@ L26-29 verbatim
/--
  Given a natural number `n`, this lemma proves that `n + n` is equal to `2 * n`.
-/
lemma split_equal (n : ℕ) : n + n = 2 * n := (Nat.two_mul n).symm


-- @@ L31-31 verbatim
lemma split_odd (n : ℕ) : n + 1 + n = 2 * n + 1 := by omega


-- @@ L33-37 verbatim
/-- A charge configuration for n even is vector like if when sorted the `i`th element
is equal to the negative of the `n + i`th element. -/
def VectorLikeEven (S : (PureU1 (2 * n)).Charges) : Prop :=
  ∀ (i : Fin n), (sort S) (Fin.cast (split_equal n) (Fin.castAdd n i))
  = - (sort S) (Fin.cast (split_equal n) (Fin.natAdd n i))


-- @@ L39-39 verbatim
end PureU1
