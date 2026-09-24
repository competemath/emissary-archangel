/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Defs


-- @@ L8-28 verbatim
/-!
# Physical-index rotation of a tensor

An on-site map \(\Lambda\) on the physical space \(\mathbb C^d\) acts on a tensor by mixing
its physical matrices, \(A^i \mapsto \sum_j \Lambda_{ij} A^j\).  This is the physical
perturbation \(A^i \to \sum_j \Lambda_{ij} A^j\) of arXiv:2011.12127, lines 2260--2262, and
the on-site twist used for symmetric matrix product states.

## Main definitions

* `MPSTensor.rotatePhysical` — the rotated tensor \((\Lambda A)^i = \sum_j \Lambda_{ij} A^j\).

## Main results

* `MPSTensor.evalWord_rotatePhysical_ofFn` — word evaluation of the rotated tensor expands
  over the words of the original tensor with sitewise matrix coefficients.
* `MPSTensor.mpv_rotatePhysical` — the matrix product vector of the rotated tensor is the
  sitewise action of \(\Lambda\) on the original matrix product vector, the identity
  \(\ket{\psi'} = \Lambda^{\otimes N}\ket{\psi}\) of arXiv:2011.12127, line 2036.
* `MPSTensor.rotatePhysical_rotatePhysical` — rotations compose multiplicatively.
-/


-- @@ L30-30 verbatim
open scoped Matrix BigOperators


-- @@ L32-32 verbatim
namespace MPSTensor


-- @@ L34-34 verbatim
noncomputable section


-- @@ L36-36 verbatim
variable {d D : ℕ}


-- @@ L38-43 verbatim
/-- Physical-index rotation of a tensor by a matrix `M` on the physical leg:

`(rotatePhysical M A) i = ∑ j, M i j • A j`.
-/
def rotatePhysical (M : Matrix (Fin d) (Fin d) ℂ) (A : MPSTensor d D) : MPSTensor d D :=
  fun i => ∑ j : Fin d, M i j • A j


-- @@ L45-47 verbatim
@[simp] lemma rotatePhysical_apply
    (M : Matrix (Fin d) (Fin d) ℂ) (A : MPSTensor d D) (i : Fin d) :
    rotatePhysical M A i = ∑ j : Fin d, M i j • A j := rfl


-- @@ L49-53 verbatim
/-- Rotating by the identity on the physical index leaves the tensor unchanged. -/
@[simp] lemma rotatePhysical_one (A : MPSTensor d D) :
    rotatePhysical (1 : Matrix (Fin d) (Fin d) ℂ) A = A := by
  funext i
  simp [rotatePhysical, Matrix.one_apply]


-- @@ L55-66 verbatim
/-- Two successive physical-index rotations compose to the rotation by the product:
\(M (M' A) = (M M') A\). -/
lemma rotatePhysical_rotatePhysical (M M' : Matrix (Fin d) (Fin d) ℂ) (A : MPSTensor d D) :
    rotatePhysical M (rotatePhysical M' A) = rotatePhysical (M * M') A := by
  funext i
  calc
    rotatePhysical M (rotatePhysical M' A) i
        = ∑ j : Fin d, ∑ k : Fin d, (M i j * M' j k) • A k := by
          simp [rotatePhysical, Finset.smul_sum, smul_smul]
    _ = ∑ k : Fin d, ∑ j : Fin d, (M i j * M' j k) • A k := Finset.sum_comm
    _ = rotatePhysical (M * M') A i := by
          simp [rotatePhysical, Matrix.mul_apply, Finset.sum_smul]


-- @@ L68-115 verbatim
/-- Expanding a word of a physically rotated tensor gives the sitewise matrix
coefficients multiplying the corresponding unrotated words. -/
theorem evalWord_rotatePhysical_ofFn
    (M : Matrix (Fin d) (Fin d) ℂ) (A : MPSTensor d D) :
    ∀ (N : ℕ) (s : Fin N → Fin d),
      Kraus.evalWord (rotatePhysical M A) (List.ofFn s) =
        ∑ t : Fin N → Fin d,
          (∏ n : Fin N, M (s n) (t n)) • Kraus.evalWord A (List.ofFn t) := by
  intro N
  induction N with
  | zero =>
      intro s
      classical
      simp
  | succ N ih =>
      intro s
      classical
      rw [List.ofFn_succ, Kraus.evalWord_cons, rotatePhysical_apply]
      rw [ih (fun n : Fin N => s n.succ)]
      rw [Finset.sum_mul_sum]
      let e : (Fin d × (Fin N → Fin d)) ≃ (Fin (N + 1) → Fin d) :=
        Fin.consEquiv (fun _ => Fin d)
      have hreindex :
          (∑ t : Fin (N + 1) → Fin d,
              (∏ n : Fin (N + 1), M (s n) (t n)) •
                Kraus.evalWord A (List.ofFn t)) =
            ∑ p : Fin d × (Fin N → Fin d),
              (∏ n : Fin (N + 1), M (s n) (e p n)) •
                Kraus.evalWord A (List.ofFn (e p)) :=
        (Fintype.sum_equiv e
          (f := fun p : Fin d × (Fin N → Fin d) =>
            (∏ n : Fin (N + 1), M (s n) (e p n)) •
              Kraus.evalWord A (List.ofFn (e p)))
          (g := fun t : Fin (N + 1) → Fin d =>
            (∏ n : Fin (N + 1), M (s n) (t n)) •
              Kraus.evalWord A (List.ofFn t))
          (by intro p; rfl)).symm
      rw [hreindex, ← Fintype.sum_prod_type']
      refine Finset.sum_congr rfl ?_
      rintro ⟨i, t⟩ _
      have hprod :
          (∏ n : Fin (N + 1), M (s n) (e (i, t) n)) =
            M (s 0) i * ∏ n : Fin N, M (s n.succ) (t n) := by
        rw [Fin.prod_univ_succ]
        simp [e, Fin.consEquiv]
      have hlist : List.ofFn (e (i, t)) = i :: List.ofFn t := by
        simp [e, Fin.consEquiv]
      rw [hprod, hlist, Kraus.evalWord_cons, smul_mul_smul_comm]


-- @@ L117-124 verbatim
/-- The matrix product vector of a physical-index rotation is the sitewise
matrix action on the original matrix product vector. -/
theorem mpv_rotatePhysical (M : Matrix (Fin d) (Fin d) ℂ)
    (A : MPSTensor d D) {N : ℕ} (s : Fin N → Fin d) :
    mpv (rotatePhysical M A) s =
      ∑ t : Fin N → Fin d, (∏ n : Fin N, M (s n) (t n)) * mpv A t := by
  rw [mpv, coeff, evalWord_rotatePhysical_ofFn, Matrix.trace_sum]
  simp only [Matrix.trace_smul, smul_eq_mul, mpv, coeff]


-- @@ L126-126 verbatim
end


-- @@ L128-128 verbatim
end MPSTensor
