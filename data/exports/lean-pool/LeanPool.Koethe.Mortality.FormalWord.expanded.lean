/-
Copyright (c) 2026 Tom Adamczewski and Epoch AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GPT-6 Astra, Tom Adamczewski
-/
module

public import LeanPool.Koethe.Mortality.Homogeneous
import LeanPool.Koethe.Mortality.Degree
import LeanPool.Koethe.Mortality.Minors
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded


-- @@ L18-24 verbatim
/-!
# Formal letters, specialization, and one scalar minor equation

A formal letter is either a fixed vector or an independently indexed hole.
The common-zero theorem is applied to the coefficients of a single pivot
minor.  Its equation count is the full word length plus one.
-/


-- @@ L26-26 verbatim
@[expose] public section


-- @@ L28-28 verbatim
noncomputable section


-- @@ L30-30 verbatim
open scoped BigOperators

-- @@ L31-31 verbatim
open KoetheMultiProjective


-- @@ L33-33 verbatim
namespace KoetheCounterexample.Mortality


-- @@ L35-36 verbatim
/-- A formal letter: a fixed letter vector, or a hole indexed by one of `N` variable blocks. -/
abbrev FormalLetter (k : Type*) (N : ℕ) := Triple k ⊕ Fin N


-- @@ L38-38 verbatim
section FormalLetters


-- @@ L40-40 verbatim
variable {k : Type*} {N d r : ℕ}


-- @@ L42-45 verbatim
/-- The three coefficients of a formal letter, as elements of the hole ring. -/
def letterCoeffs [Field k] : FormalLetter k N → Fin 3 → HoleRing k N
  | .inl a => fun j => MvPolynomial.C (a j)
  | .inr b => fun j => MvPolynomial.X (b, j)


-- @@ L47-51 verbatim
/-- The multidegree of a formal letter: zero for a fixed letter, one unit of its block for a
hole. -/
def letterDegree : FormalLetter k N → Fin N → ℕ
  | .inl _ => 0
  | .inr b => blockUnit b


-- @@ L53-56 verbatim
/-- Specialize a formal letter at an assignment of the hole variables. -/
def specializeLetter (x : (Fin N × Fin 3) → k) : FormalLetter k N → Triple k
  | .inl a => a
  | .inr b => fun j => x (b, j)


-- @@ L58-61 verbatim
/-- The forward product of the pencil lifted along a formal word. -/
def formalProd [Field k] (P : Pencil k d) (w : List (FormalLetter k N)) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) (Polynomial (HoleRing k N)) :=
  (w.map (fun a => P.lift (letterCoeffs a))).prod


-- @@ L63-64 verbatim
@[simp] theorem specializeLetter_inl (x : (Fin N × Fin 3) → k) (a : Triple k) :
    specializeLetter x (.inl a) = a := rfl


-- @@ L66-67 verbatim
@[simp] theorem letterDegree_inl (a : Triple k) :
    letterDegree (N := N) (.inl a) = 0 := rfl


-- @@ L69-70 verbatim
@[simp] theorem letterDegree_inr (b : Fin N) :
    letterDegree (k := k) (.inr b) = blockUnit b := rfl


-- @@ L72-74 verbatim
theorem constantWord_degree (w : List (Triple k)) :
    ((w.map (Sum.inl : Triple k → FormalLetter k N)).map letterDegree).sum = 0 := by
  simp only [List.map_map, Function.comp_def, letterDegree_inl, List.sum_map_zero]


-- @@ L76-79 verbatim
theorem specialize_constantWord (x : (Fin N × Fin 3) → k)
    (w : List (Triple k)) :
    (w.map (Sum.inl : Triple k → FormalLetter k N)).map (specializeLetter x) = w := by
  simp [Function.comp_def]


-- @@ L81-81 verbatim
variable [Field k]


-- @@ L83-87 verbatim
theorem letterCoeffs_hom (a : FormalLetter k N) (j : Fin 3) :
    IsMultiHomogeneous (letterCoeffs a j) (letterDegree a) := by
  cases a with
  | inl a => exact multiHom_C (a j)
  | inr b => exact multiHom_X b j


-- @@ L89-92 verbatim
theorem formalProd_hom (P : Pencil k d) (w : List (FormalLetter k N)) :
    MatrixCoeffHom (formalProd P w) (w.map letterDegree).sum :=
  matrixCoeffHom_prod w _ _
    (fun a _ => lift_coeffHom P (letterCoeffs a) (letterDegree a) (letterCoeffs_hom a))


-- @@ L94-98 verbatim
theorem formalMinor_natDegree_le (P : Pencil k d) (w : List (FormalLetter k N))
    (I J : Fin r → Fin (d + 1)) (hI : Function.Injective I) :
    (((formalProd P w).submatrix I J).det).natDegree ≤ w.length := by
  simpa only [formalProd, List.map_map, Function.comp_def, List.length_map] using
    det_liftWord_natDegree_le P (w.map letterCoeffs) I J hI


-- @@ L100-111 verbatim
theorem specialize_lift (P : Pencil k d) (a : FormalLetter k N)
    (x : (Fin N × Fin 3) → k) :
    (P.lift (letterCoeffs a)).map (Polynomial.mapRingHom (MvPolynomial.eval x)) =
      P.eval (specializeLetter x a) := by
  apply Matrix.ext
  intro i j
  change Polynomial.map (MvPolynomial.eval x) (P.lift (letterCoeffs a) i j) = _
  cases a <;>
    simp only [Pencil.lift, Pencil.eval, letterCoeffs, specializeLetter,
      MvPolynomial.algebraMap_eq, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_X, Polynomial.map_sum, map_sum, map_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_X, mul_comm]


-- @@ L113-125 verbatim
theorem specialize_formalProd (P : Pencil k d) (w : List (FormalLetter k N))
    (x : (Fin N × Fin 3) → k) :
    (formalProd P w).map (Polynomial.mapRingHom (MvPolynomial.eval x)) =
      P.wordProd (w.map (specializeLetter x)) := by
  classical
  induction w with
  | nil =>
    simp only [formalProd, List.map_nil, List.prod_nil, Pencil.wordProd_nil]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  | cons a w ih =>
    simp only [formalProd, List.map_cons, List.prod_cons] at ih ⊢
    rw [Matrix.map_mul, specialize_lift, ih]
    rfl


-- @@ L127-158 verbatim
/-- A formal word in which every hole block occurs once has a specialization
with no zero block that kills any specified minor, provided the number of
coefficient equations is at most twice the number of blocks. -/
theorem exists_specialization_minor_zero [IsAlgClosed k]
    (P : Pencil k d) (w : List (FormalLetter k N))
    (I J : Fin r → Fin (d + 1)) (hI : Function.Injective I)
    (hN : 0 < N) (hr : 0 < r) (hsize : w.length + 1 ≤ 2 * N)
    (hdegree : (w.map letterDegree).sum = fun _ => 1) :
    ∃ x : (Fin N × Fin 3) → k,
      (∀ b : Fin N, (fun j : Fin 3 => x (b, j)) ≠ 0) ∧
      ((P.wordProd (w.map (specializeLetter x))).submatrix I J).det = 0 := by
  classical
  let F := ((formalProd P w).submatrix I J).det
  have hFdegree : F.natDegree ≤ w.length := formalMinor_natDegree_le P w I J hI
  have hFhom : CoeffHom F (fun _ => r) := by
    have h := formalProd_hom P w
    rw [hdegree] at h
    have hminor : MatrixCoeffHom ((formalProd P w).submatrix I J) (fun _ => 1) :=
      fun i j => h (I i) (J j)
    simpa only [Nat.mul_one] using hminor.det
  obtain ⟨x, hx, hzero⟩ := exists_common_zero_of_coeff
    (fun i : Fin (w.length + 1) => F.coeff i.val) hN hr hsize
    (fun i e he b => hFhom i.val e he b)
  refine ⟨x, hx, ?_⟩
  have hmap : Polynomial.map (MvPolynomial.eval x) F = 0 := by
    ext j
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    by_cases hj : j < w.length + 1
    · exact hzero ⟨j, hj⟩
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]
  rw [← specialize_formalProd P w x, Matrix.submatrix_map, det_map]
  exact hmap


-- @@ L160-160 verbatim
end FormalLetters


-- @@ L162-162 verbatim
end KoetheCounterexample.Mortality


-- @@ L164-164 verbatim
end
