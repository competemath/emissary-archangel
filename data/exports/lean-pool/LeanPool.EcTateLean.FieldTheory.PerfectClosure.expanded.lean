/-
Copyright (c) 2023 Alex J. Best and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
module


public import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset


-- @@ L17-21 verbatim
/-!
# LeanPool.EcTateLean.FieldTheory.PerfectClosure

Imported Lean Pool material for `LeanPool.EcTateLean.FieldTheory.PerfectClosure`.
-/


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-25 verbatim
namespace ECTate

-- @@ L26-34 verbatim
/-- A perfect ring is one where raising to the power of the ring characteristic is a bijection
  or a ring of char zero.

  Note this is distinct from the mathlib version in that we allow char 0
-/
class PerfectRing (R : Type _) [CommSemiring R] where
  -- TODO maybe refactor to be [Char R p] bijective pth power
  -- TODO maybe make this follow from mathlib perfect, via instance
  pth_power_bijective : ringChar R = 0 ∨ Function.Bijective (fun x : R => x ^ (ringChar R))


-- @@ L36-36 verbatim
namespace PerfectRing

-- @@ L37-37 verbatim
variable {R : Type _} [CommSemiring R]


-- @@ L39-40 verbatim
lemma pth_power_bijective_of_char_nonzero [PerfectRing R] (h : ringChar R ≠ 0) :
  Function.Bijective (fun x : R => x ^ (ringChar R)) := Or.resolve_left pth_power_bijective h


-- @@ L42-46 verbatim
/-- The inverse of the `p`-th power map on a perfect ring (the identity in
characteristic zero). -/
noncomputable
def pthRoot [PerfectRing R] : R → R :=
if h : ringChar R = 0 then id else Function.surjInv (pth_power_bijective_of_char_nonzero h).2


-- @@ L48-51 verbatim
lemma pthRoot_pow_char [PerfectRing R] (h : ringChar R ≠ 0) (x : R) :
  pthRoot x ^ (ringChar R) = x := by
  simp only [pthRoot, h, dite_false]
  exact Function.rightInverse_surjInv (pth_power_bijective_of_char_nonzero h).2 x


-- @@ L53-60 verbatim
lemma pthRoot_pow_eq [PerfectRing R] (x : R) :
  pthRoot x ^ n = x ^ (n / ringChar R) * pthRoot x ^ (n % ringChar R) := by
  by_cases h : ringChar R = 0
  · simp [h]
  conv =>
    lhs
    rw [← Nat.mod_add_div n (ringChar R)]
  rw [pow_add, pow_mul, pthRoot_pow_char h, mul_comm]



-- @@ L63-73 verbatim
@[simp]
lemma pthRoot_zero [PerfectRing R] : pthRoot (0 : R) = 0 := by
  rw [pthRoot]
  split
  · simp
  · apply_fun (fun x : R => x ^ ringChar R)
    · dsimp only
      rw [Function.surjInv_eq
            (pth_power_bijective_of_char_nonzero (by assumption)).surjective,
          zero_pow (by assumption)]
    · exact (pth_power_bijective_of_char_nonzero (by assumption)).injective


-- @@ L75-75 verbatim
end PerfectRing


-- @@ L77-77 verbatim
end ECTate
