/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.Algebra.Bezout
import LeanCert.Engine.Algebra.CubicCount
import LeanCert.Engine.AD.Correctness


-- @@ L10-16 verbatim
/-!
# Exact rational cubics and isolation data

This module contains the executable algebraic representation and the generic
set-theoretic machinery used by complete cubic isolation.  It deliberately
does not import LeanCert's Validity layer.
-/


-- @@ L18-18 verbatim
namespace LeanCert.Engine


-- @@ L20-20 verbatim
open LeanCert.Core

-- @@ L21-21 verbatim
open LeanCert.Engine.Algebra


-- @@ L23-29 verbatim
/-- An executable exact rational cubic `a*x^3 + b*x^2 + c*x + d`. -/
structure QCubic where
  a : ℚ
  b : ℚ
  c : ℚ
  d : ℚ
  deriving Repr, DecidableEq, Inhabited


-- @@ L31-34 verbatim
/-- Exact rational discriminant. -/
def QCubic.discr (P : QCubic) : ℚ :=
  P.b ^ 2 * P.c ^ 2 - 4 * P.a * P.c ^ 3 - 4 * P.b ^ 3 * P.d -
    27 * P.a ^ 2 * P.d ^ 2 + 18 * P.a * P.b * P.c * P.d


-- @@ L36-38 verbatim
/-- The corresponding Mathlib rational cubic. -/
def QCubic.toCubicRat (P : QCubic) : Cubic ℚ :=
  ⟨P.a, P.b, P.c, P.d⟩


-- @@ L40-42 verbatim
/-- Semantic real cubic. -/
def QCubic.toReal (P : QCubic) : Cubic ℝ :=
  ⟨P.a, P.b, P.c, P.d⟩


-- @@ L44-46 verbatim
/-- Exact executable polynomial in ascending coefficient order. -/
def QCubic.toQPoly (P : QCubic) : QPoly :=
  ⟨#[P.d, P.c, P.b, P.a]⟩


-- @@ L48-51 verbatim
/-- Horner expression in variable zero. -/
def QCubic.toExpr (P : QCubic) : Expr :=
  .add (.mul (.add (.mul (.add (.mul (.const P.a) (.var 0)) (.const P.b)) (.var 0))
    (.const P.c)) (.var 0)) (.const P.d)


-- @@ L53-57 verbatim
@[simp] theorem QCubic.eval_toExpr (P : QCubic) (x : ℝ) :
    Expr.eval (fun _ => x) P.toExpr =
      (P.a : ℝ) * x ^ 3 + (P.b : ℝ) * x ^ 2 + (P.c : ℝ) * x + P.d := by
  simp [QCubic.toExpr]
  ring


-- @@ L59-61 verbatim
@[simp] theorem QCubic.toReal_discr (P : QCubic) :
    P.toReal.discr = P.discr := by
  simp [QCubic.toReal, QCubic.discr, Cubic.discr]


-- @@ L63-65 verbatim
@[simp] theorem QCubic.toCubicRat_discr (P : QCubic) :
    P.toCubicRat.discr = P.discr := by
  simp [QCubic.toCubicRat, QCubic.discr, Cubic.discr]


-- @@ L67-69 verbatim
theorem QCubic.toExpr_supported (P : QCubic) : ADSupported P.toExpr := by
  rw [← Expr.checkADSupported_eq_true_iff]
  rfl


-- @@ L71-73 verbatim
theorem QCubic.toExpr_usesOnlyVar0 (P : QCubic) : UsesOnlyVar0 P.toExpr := by
  rw [← Expr.usesOnlyVar0_iff_UsesOnlyVar0]
  rfl


-- @@ L75-82 verbatim
theorem QCubic.toExpr_continuous (P : QCubic) :
    Continuous (fun x : ℝ => Expr.eval (fun _ => x) P.toExpr) := by
  have hpoly : Continuous (fun x : ℝ =>
      (P.a : ℝ) * x ^ 3 + (P.b : ℝ) * x ^ 2 + (P.c : ℝ) * x + P.d) := by
    fun_prop
  convert hpoly using 1
  funext x
  exact P.eval_toExpr x


-- @@ L84-86 verbatim
/-- Exact checker for three distinct real roots. -/
def QCubic.threeRootCountCheck (P : QCubic) : Bool :=
  decide (P.a ≠ 0) && decide (0 < P.discr)


-- @@ L88-96 verbatim
theorem QCubic.threeRootCountCheck_sound (P : QCubic)
    (h : P.threeRootCountCheck = true) :
    (cubicZeroSet P.toReal).ncard = 3 := by
  simp only [QCubic.threeRootCountCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  apply cubicZeroSet_ncard_eq_three_of_discr_pos P.toReal
  · simp only [QCubic.toReal]
    exact_mod_cast h.1
  · rw [QCubic.toReal_discr]
    exact_mod_cast h.2


-- @@ L98-98 verbatim
/-! ### Generic exhaustion -/


-- @@ L100-116 verbatim
/-- Three distinct members exhaust a set of cardinality three. -/
theorem three_mem_exhaust_ncard {α : Type*} {S : Set α} {x₁ x₂ x₃ : α}
    (hcard : S.ncard = 3) (h₁ : x₁ ∈ S) (h₂ : x₂ ∈ S) (h₃ : x₃ ∈ S)
    (h₁₂ : x₁ ≠ x₂) (h₁₃ : x₁ ≠ x₃) (h₂₃ : x₂ ≠ x₃) :
    S = {x₁, x₂, x₃} := by
  have hfinite : S.Finite := Set.finite_of_ncard_ne_zero (by omega)
  have hsub : {x₁, x₂, x₃} ⊆ S := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact h₁
    · exact h₂
    · exact h₃
  have heq : {x₁, x₂, x₃} = S := by
    exact Set.eq_of_subset_of_ncard_le (ht := hfinite) hsub (by
      simp [hcard, h₁₂, h₁₃, h₂₃])
  exact heq.symm


-- @@ L118-147 verbatim
/-- Three roots in pairwise-disjoint regions exhaust a three-element root set. -/
theorem three_unique_roots_exhaust {S I₁ I₂ I₃ : Set ℝ}
    (hcard : S.ncard = 3)
    (h₁ : ∃! x, x ∈ I₁ ∧ x ∈ S) (h₂ : ∃! x, x ∈ I₂ ∧ x ∈ S)
    (h₃ : ∃! x, x ∈ I₃ ∧ x ∈ S)
    (h₁₂ : Disjoint I₁ I₂) (h₁₃ : Disjoint I₁ I₃) (h₂₃ : Disjoint I₂ I₃) :
    S ⊆ I₁ ∪ I₂ ∪ I₃ := by
  obtain ⟨x₁, hx₁, -⟩ := h₁
  obtain ⟨x₂, hx₂, -⟩ := h₂
  obtain ⟨x₃, hx₃, -⟩ := h₃
  have hx₁₂ : x₁ ≠ x₂ := by
    intro h
    subst x₂
    exact Set.disjoint_left.1 h₁₂ hx₁.1 hx₂.1
  have hx₁₃ : x₁ ≠ x₃ := by
    intro h
    subst x₃
    exact Set.disjoint_left.1 h₁₃ hx₁.1 hx₃.1
  have hx₂₃ : x₂ ≠ x₃ := by
    intro h
    subst x₃
    exact Set.disjoint_left.1 h₂₃ hx₂.1 hx₃.1
  have hS := three_mem_exhaust_ncard hcard hx₁.2 hx₂.2 hx₃.2 hx₁₂ hx₁₃ hx₂₃
  rw [hS]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact Set.mem_union_left _ (Set.mem_union_left _ hx₁.1)
  · exact Set.mem_union_left _ (Set.mem_union_right _ hx₂.1)
  · exact Set.mem_union_right _ hx₃.1


-- @@ L149-149 verbatim
/-! ### Isolation data -/


-- @@ L151-158 verbatim
/-- Three rational intervals, ordered from left to right, with one Newton
configuration shared by their local uniqueness checks. -/
structure CubicIsolationCert where
  left : IntervalRat
  middle : IntervalRat
  right : IntervalRat
  cfg : EvalConfig := {}
  deriving Repr, DecidableEq


-- @@ L160-162 verbatim
/-- Strict ordering implies pairwise disjointness, including at endpoints. -/
def CubicIsolationCert.intervalsOrdered (cert : CubicIsolationCert) : Bool :=
  decide (cert.left.hi < cert.middle.lo) && decide (cert.middle.hi < cert.right.lo)


-- @@ L164-165 verbatim
/-- The real set represented by a rational interval. -/
def intervalSet (I : IntervalRat) : Set ℝ := Set.Icc I.lo I.hi


-- @@ L167-168 verbatim
theorem mem_intervalSet_iff (I : IntervalRat) (x : ℝ) :
    x ∈ intervalSet I ↔ x ∈ I := by rfl


-- @@ L170-184 verbatim
theorem CubicIsolationCert.ordered_disjoint (cert : CubicIsolationCert)
    (h : cert.intervalsOrdered = true) :
    Disjoint (intervalSet cert.left) (intervalSet cert.middle) ∧
      Disjoint (intervalSet cert.left) (intervalSet cert.right) ∧
      Disjoint (intervalSet cert.middle) (intervalSet cert.right) := by
  simp only [CubicIsolationCert.intervalsOrdered, Bool.and_eq_true, decide_eq_true_eq] at h
  have disjoint_of_lt {I J : IntervalRat} (hlt : I.hi < J.lo) :
      Disjoint (intervalSet I) (intervalSet J) := by
    rw [Set.disjoint_left]
    intro x hxI hxJ
    simp only [intervalSet, Set.mem_Icc] at hxI hxJ
    have hltR : (I.hi : ℝ) < J.lo := by exact_mod_cast hlt
    linarith
  exact ⟨disjoint_of_lt h.1,
    disjoint_of_lt ((h.1.trans_le cert.middle.le).trans h.2), disjoint_of_lt h.2⟩


-- @@ L186-186 verbatim
end LeanCert.Engine
