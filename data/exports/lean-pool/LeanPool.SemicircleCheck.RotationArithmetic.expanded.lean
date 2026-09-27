/-
Copyright (c) 2026 Wondermonger-daydreaming. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wondermonger-daydreaming
-/
module

public import Mathlib.Algebra.Group.End
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD


-- @@ L13-17 verbatim
/-!
  Group-theoretic helpers used with rotation normalization.

  The `finRotate` arithmetic lemmas live in `SemicircleCheck.FinRotateLemmas`.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
open Equiv Equiv.Perm


-- @@ L23-23 verbatim
variable {n : ℕ}


-- @@ L25-25 verbatim
/-! ## The group-theoretic layer -/


-- @@ L27-30 verbatim
section GroupTheory

-- Parameterize on explicit Fin values to avoid (0 : Fin m) instance issues.
-- The group theory doesn't care what the target values are.

-- @@ L31-31 verbatim
variable {m : ℕ} {π ρ : Perm (Fin m)}

-- @@ L32-32 verbatim
variable {i γi a b : Fin m}


-- @@ L34-36 verbatim
/-- If ρ sends a to b, then ρ⁻¹ sends b back to a. Pure injectivity. -/
lemma inv_apply_of_apply (h : ρ a = b) : ρ⁻¹ b = a := by
  subst h; exact ρ.symm_apply_apply a


-- @@ L38-45 verbatim
/-- The involution gives us the reverse map.
    If π² = 1 and π(i) = γi, then π(γi) = i. -/
lemma involution_reverse (hsq : π ^ 2 = 1) (hadj : π i = γi) :
    π γi = i := by
  have h2 : π * π = 1 := by rwa [← sq]
  have h3 : π (π i) = i := by
    change (π * π) i = i; simp [h2]
  rwa [hadj] at h3


-- @@ L47-54 verbatim
/-- Conjugation sends a to b when ρ, π, and the adjacency align.

    calc: (ρ * π * ρ⁻¹)(a) = ρ(π(ρ⁻¹(a))) = ρ(π(i)) = ρ(γi) = b -/
lemma conjugate_sends
    (hρi : ρ i = a) (hργi : ρ γi = b) (hadj : π i = γi) :
    (ρ * π * ρ⁻¹) a = b := by
  simp only [mul_apply]
  rw [inv_apply_of_apply hρi, hadj, hργi]


-- @@ L56-64 verbatim
/-- Conjugation sends b to a (the reverse direction via involution).

    calc: (ρ * π * ρ⁻¹)(b) = ρ(π(ρ⁻¹(b))) = ρ(π(γi)) = ρ(i) = a -/
lemma conjugate_sends_back
    (hρi : ρ i = a) (hργi : ρ γi = b)
    (hsq : π ^ 2 = 1) (hadj : π i = γi) :
    (ρ * π * ρ⁻¹) b = a := by
  simp only [mul_apply]
  rw [inv_apply_of_apply hργi, involution_reverse hsq hadj, hρi]


-- @@ L66-66 verbatim
end GroupTheory
