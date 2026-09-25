module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.Defs
public import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.Defs
public import Mathlib.Data.Finset.Basic
public import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Ring


-- @@ L8-15 verbatim
/-!
# Odd-degree vanishing for antipodal sets

For any antipodal finite set `C` on the unit sphere and any *odd* `k`,
`gegenbauerDoubleSum24 k C = 0`.

This is used to upgrade vanishing for `k=1..10` into vanishing for `k=1..11` (since `11` is odd).
-/


-- @@ L17-17 verbatim
namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14.BuildSteps

-- @@ L18-18 verbatim
open Finset


-- @@ L20-22 verbatim
/-- Antipodality predicate for finsets: closed under negation. -/
@[expose] public def IsAntipodalFinset {α : Type*} [Neg α] (C : Finset α) : Prop :=
  ∀ u ∈ C, -u ∈ C


-- @@ L24-24 verbatim
end SpherePacking.Dim24.Uniqueness.BS81.Thm14.BuildSteps



-- @@ L27-27 verbatim
namespace SpherePacking.Dim24


-- @@ L29-29 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)


-- @@ L31-31 verbatim
namespace Uniqueness.BS81.LP

-- @@ L32-32 verbatim
noncomputable section


-- @@ L34-34 verbatim
open Polynomial


-- @@ L36-45 verbatim
lemma gegenbauerVal_neg (lam : ℝ) :
    ∀ n x, gegenbauerVal lam n (-x) = ((-1 : ℝ) ^ n) * gegenbauerVal lam n x
  | 0, x => by
      simp [gegenbauerVal]
  | 1, x => by
      simp [gegenbauerVal]
  | n + 2, x => by
      simp [gegenbauerVal, gegenbauerVal_neg lam n x, gegenbauerVal_neg lam (n + 1) x,
        pow_succ, sub_eq_add_neg, div_eq_mul_inv]
      ring


-- @@ L47-50 verbatim
lemma Gegenbauer24Val_neg (n : ℕ) (x : ℝ) :
    Gegenbauer24Val n (-x) = ((-1 : ℝ) ^ n) * Gegenbauer24Val n x := by
  -- Normalization divides by the constant `C_n(1)`, so parity is unchanged.
  simp [Gegenbauer24Val, gegenbauerVal_neg, mul_assoc, mul_comm]


-- @@ L52-55 verbatim
/-- Parity of `Gegenbauer24`: evaluation at `-x` picks up the factor `(-1)^n`. -/
public lemma Gegenbauer24_eval_neg (n : ℕ) (x : ℝ) :
    (Gegenbauer24 n).eval (-x) = ((-1 : ℝ) ^ n) * (Gegenbauer24 n).eval x := by
  simp [Gegenbauer24_eval_eq, Gegenbauer24Val_neg]


-- @@ L57-60 verbatim
lemma Gegenbauer24_eval_neg_11 (x : ℝ) :
    (Gegenbauer24 11).eval (-x) = - (Gegenbauer24 11).eval x := by
  have hodd : Odd (11 : ℕ) := by decide
  simpa [hodd.neg_one_pow] using (Gegenbauer24_eval_neg (n := 11) (x := x))


-- @@ L62-62 verbatim
end


-- @@ L64-64 verbatim
end Uniqueness.BS81.LP


-- @@ L66-66 verbatim
namespace Uniqueness.BS81.Thm14.BuildSteps.Design11


-- @@ L68-68 verbatim
noncomputable section


-- @@ L70-70 verbatim
open scoped RealInnerProductSpace BigOperators


-- @@ L72-72 verbatim
open Finset

-- @@ L73-73 verbatim
open Uniqueness.BS81.Thm14


-- @@ L75-75 verbatim
open Uniqueness.BS81.LP


-- @@ L77-79 verbatim
lemma gegenbauer24_eval_neg_of_odd (k : ℕ) (hk : Odd k) (x : ℝ) :
    (Gegenbauer24 k).eval (-x) = - (Gegenbauer24 k).eval x := by
  simp [Gegenbauer24_eval_neg, hk.neg_one_pow]


-- @@ L81-84 verbatim
lemma gegenbauer24_eval_inner_neg_right_of_odd (k : ℕ) (hk : Odd k) (u v : ℝ²⁴) :
    (Gegenbauer24 k).eval (⟪u, -v⟫ : ℝ) = - (Gegenbauer24 k).eval (⟪u, v⟫ : ℝ) := by
  simpa [inner_neg_right] using
    (gegenbauer24_eval_neg_of_odd (k := k) hk (x := (⟪u, v⟫ : ℝ)))


-- @@ L86-106 verbatim
lemma sum_gegenbauer24_eval_inner_eq_zero_of_antipodal_of_odd
    (k : ℕ) (hk : Odd k) (C : Finset ℝ²⁴) (hanti : IsAntipodalFinset C) (u : ℝ²⁴) :
    C.sum (fun v => (Gegenbauer24 k).eval (⟪u, v⟫ : ℝ)) = 0 := by
  have hpair (v : ℝ²⁴) :
      (Gegenbauer24 k).eval (⟪u, v⟫ : ℝ) + (Gegenbauer24 k).eval (⟪u, -v⟫ : ℝ) = 0 := by
    rw [gegenbauer24_eval_inner_neg_right_of_odd (k := k) hk (u := u) (v := v)]
    simp
  -- Pair terms in the sum over `v ∈ C` using the involution `v ↦ -v`.
  simpa using
    (Finset.sum_involution (s := C)
      (f := fun v => (Gegenbauer24 k).eval (⟪u, v⟫ : ℝ))
      (g := fun v _hv => -v)
      (hg₁ := fun v _hv => by
        simpa using hpair v)
      (hg₃ := fun v _hv hv0 => by
        -- If `-v = v`, then the cancellation identity forces the term to be zero.
        intro hvfix
        apply hv0
        exact add_self_eq_zero.mp (by simpa [hvfix] using hpair v))
      (g_mem := fun v hv => hanti v hv)
      (hg₄ := fun v _hv => by simp))


-- @@ L108-113 verbatim
/-- If `C` is antipodal and `k` is odd, then `gegenbauerDoubleSum24 k C = 0`. -/
public theorem gegenbauerDoubleSum24_eq_zero_of_antipodal_of_odd
    (k : ℕ) (hk : Odd k) (C : Finset ℝ²⁴) (hanti : IsAntipodalFinset C) :
    gegenbauerDoubleSum24 k C = 0 := by
  simp [gegenbauerDoubleSum24,
    sum_gegenbauer24_eval_inner_eq_zero_of_antipodal_of_odd (k := k) hk (C := C) hanti]


-- @@ L115-115 verbatim
end


-- @@ L117-117 verbatim
end SpherePacking.Dim24.Uniqueness.BS81.Thm14.BuildSteps.Design11
