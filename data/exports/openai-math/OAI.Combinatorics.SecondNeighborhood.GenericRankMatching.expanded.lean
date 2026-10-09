import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.Rank


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
namespace SeymourSecondNeighborhood


-- @@ L8-8 verbatim
open MvPolynomial


-- @@ L10-10 verbatim
variable {R σ m n κ β : Type*}


-- @@ L12-16 verbatim
noncomputable def supportedVariableMatrix [CommSemiring R]
    (support : m → n → Prop) (label : m → n → σ) :
    Matrix m n (MvPolynomial σ R) := by
  classical
  exact fun i j => if support i j then X (label i j) else 0


-- @@ L18-25 verbatim
theorem supportedVariableMatrix_submatrix [CommSemiring R]
    (support : m → n → Prop) (label : m → n → σ)
    (row : κ → m) (col : κ → n) :
    (supportedVariableMatrix (R := R) support label).submatrix row col =
      supportedVariableMatrix (R := R) (fun i j => support (row i) (col j))
        (fun i j => label (row i) (col j)) := by
  classical
  rfl


-- @@ L27-52 verbatim
theorem exists_eval_supportedVariables_eq_one
    [Fintype κ] [DecidableEq κ] [CommSemiring R]
    (support : κ → κ → Prop) (label : κ → κ → σ)
    (hdiag : ∀ i, support i i)
    (hlabel : ∀ i j k l, support i j → support k l →
      label i j = label k l → i = k ∧ j = l) :
    ∃ v : σ → R, (MvPolynomial.eval v).mapMatrix
      (supportedVariableMatrix (R := R) support label) = 1 := by
  classical
  let v : σ → R := fun s => if ∃ k, label k k = s then 1 else 0
  refine ⟨v, ?_⟩
  ext i j
  change MvPolynomial.eval v
    (if support i j then X (label i j) else 0) = (1 : Matrix κ κ R) i j
  rw [Matrix.one_apply]
  by_cases hij : i = j
  · subst j
    have hw : ∃ k, label k k = label i i := ⟨i, rfl⟩
    simp [hdiag i, v, hw]
  · by_cases hs : support i j
    · have hw : ¬ ∃ k, label k k = label i j := by
        rintro ⟨k, hk⟩
        obtain ⟨hki, hkj⟩ := hlabel k k i j (hdiag k) hs hk
        exact hij (hki.symm.trans hkj)
      simp [hs, hij, v, hw]
    · simp [hs, hij]


-- @@ L54-66 verbatim
theorem det_supportedVariables_ne_zero
    [Fintype κ] [DecidableEq κ] [CommRing R] [Nontrivial R]
    (support : κ → κ → Prop) (label : κ → κ → σ)
    (hdiag : ∀ i, support i i)
    (hlabel : ∀ i j k l, support i j → support k l →
      label i j = label k l → i = k ∧ j = l) :
    (supportedVariableMatrix (R := R) support label).det ≠ 0 := by
  obtain ⟨v, hv⟩ := exists_eval_supportedVariables_eq_one
    (R := R) support label hdiag hlabel
  intro hzero
  have h := congrArg Matrix.det hv
  rw [Matrix.det_one, ← RingHom.map_det, hzero, map_zero] at h
  exact zero_ne_one h


-- @@ L68-77 verbatim
theorem det_matchingMinor_ne_zero
    [Fintype κ] [DecidableEq κ] [CommRing R] [Nontrivial R]
    (support : m → n → Prop) (label : m → n → σ)
    (row : κ → m) (col : κ → n)
    (hmatched : ∀ i, support (row i) (col i))
    (hlabel : ∀ i j k l, support (row i) (col j) → support (row k) (col l) →
      label (row i) (col j) = label (row k) (col l) → i = k ∧ j = l) :
    ((supportedVariableMatrix (R := R) support label).submatrix row col).det ≠ 0 := by
  rw [supportedVariableMatrix_submatrix]
  exact det_supportedVariables_ne_zero _ _ hmatched hlabel


-- @@ L79-109 verbatim
theorem det_blockSupportedVariables_ne_zero
    [Fintype κ] [DecidableEq κ] [Fintype β] [LinearOrder β]
    [CommRing R] [IsDomain R]
    (support : κ → κ → Prop) (label : κ → κ → σ) (block : κ → β)
    (hdiag : ∀ i, support i i)
    (hblock : ∀ i j, support i j → block i = block j)
    (hlabel : ∀ i j k l, support i j → support k l → block i = block k →
      label i j = label k l → i = k ∧ j = l) :
    (supportedVariableMatrix (R := R) support label).det ≠ 0 := by
  classical
  let M := supportedVariableMatrix (R := R) support label
  have htri : M.BlockTriangular block := by
    intro i j hji
    have hs : ¬ support i j := by
      intro hs
      exact (ne_of_lt hji) (hblock i j hs).symm
    simp [M, supportedVariableMatrix, hs]
  change M.det ≠ 0
  rw [htri.det_fintype]
  apply Finset.prod_ne_zero_iff.mpr
  intro b _
  change (supportedVariableMatrix (R := R)
    (fun i j : { a // block a = b } => support i.val j.val)
    (fun i j : { a // block a = b } => label i.val j.val)).det ≠ 0
  apply det_supportedVariables_ne_zero
  · intro i
    exact hdiag i.val
  · intro i j k l hij hkl heq
    obtain ⟨hik, hjl⟩ := hlabel i.val j.val k.val l.val hij hkl
      (i.property.trans k.property.symm) heq
    exact ⟨Subtype.ext hik, Subtype.ext hjl⟩


-- @@ L111-111 verbatim
end SeymourSecondNeighborhood


-- @@ L113-113 verbatim
end OAI
