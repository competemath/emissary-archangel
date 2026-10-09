import OAI.InformationTheory.AmplitudeDamping.OutputConvexity


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u_1 u_2 u_3 u_4


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open scoped BigOperators Matrix.Norms.Elementwise

-- @@ L9-9 verbatim
open Matrix

-- @@ L10-10 verbatim
open scoped BigOperators ComplexOrder MatrixOrder

-- @@ L11-11 verbatim
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder

-- @@ L12-12 verbatim
open Matrix Set

-- @@ L13-13 verbatim
open scoped ComplexOrder MatrixOrder

-- @@ L14-14 verbatim
open scoped BigOperators Topology

-- @@ L15-15 verbatim
open Filter Set

-- @@ L16-16 verbatim
open scoped BigOperators ComplexOrder MatrixOrder Topology

-- @@ L17-17 verbatim
open scoped BigOperators ComplexOrder

-- @@ L18-18 verbatim
open scoped BigOperators

-- @@ L19-19 verbatim
open Set Filter Topology


-- @@ L21-21 verbatim
open scoped BigOperators ComplexOrder MatrixOrder CStarAlgebra

-- @@ L22-22 verbatim
open Matrix

-- @@ L23-23 verbatim
namespace GAD

-- @@ L24-24 verbatim
variable {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]


-- @@ L26-29 verbatim
omit [Fintype κ] [DecidableEq κ] in
noncomputable def diagonalStarAlgHom : (ι → ℂ) →⋆ₐ[ℂ] Matrix ι ι ℂ :=
  { Matrix.diagonalAlgHom ℂ with
    map_star' := by intro x; ext i j; simp [Matrix.star_apply, Matrix.diagonal_apply]; split_ifs <;> simp_all }


-- @@ L31-53 verbatim
omit [Fintype κ] [DecidableEq κ] in
theorem entropy_diagonal (p : ι → ℝ) :
    entropy (Matrix.diagonal (fun i ↦ (p i : ℂ))) = ∑ i, Real.negMulLog (p i) := by
  classical
  cases isEmpty_or_nonempty ι
  · simp [entropy, Matrix.trace]
  let : ContinuousFunctionalCalculus ℝ (ι → ℂ) IsSelfAdjoint := IsSelfAdjoint.instContinuousFunctionalCalculus
  let φ := diagonalStarAlgHom (ι := ι)
  have hp : IsSelfAdjoint (fun i ↦ (p i : ℂ)) := by ext i; simp
  have hd : (Matrix.diagonal (fun i ↦ (p i : ℂ))).IsHermitian := by
    exact Matrix.isHermitian_diagonal_iff.mpr (fun i ↦ by simp [IsSelfAdjoint])
  have hm := StarAlgHomClass.map_cfc (S := ℂ) φ Real.negMulLog (fun i ↦ (p i : ℂ))
    Real.continuous_negMulLog.continuousOn
    (show Continuous φ by change Continuous (Matrix.diagonal : (ι → ℂ) → Matrix ι ι ℂ); fun_prop) hp hd
  have he : cfc Real.negMulLog (fun i ↦ (p i : ℂ)) = fun i ↦ (Real.negMulLog (p i) : ℂ) := by
    rw [cfc_map_pi (S := ℂ) Real.negMulLog _ Real.continuous_negMulLog.continuousOn hp (fun i ↦ by simp [IsSelfAdjoint])]
    ext i
    exact cfc_algebraMap (A := ℂ) (p i) Real.negMulLog
  unfold entropy
  change (cfc Real.negMulLog (φ (fun i ↦ (p i : ℂ)))).trace.re = _
  calc
    _ = (φ (cfc Real.negMulLog (fun i ↦ (p i : ℂ)))).trace.re := congrArg (fun A : Matrix ι ι ℂ ↦ A.trace.re) hm.symm
    _ = _ := by rw [he]; simp [φ, diagonalStarAlgHom, Matrix.trace_diagonal]


-- @@ L55-58 verbatim
noncomputable def reindexStarAlgEquiv (e : ι ≃ κ) : Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix κ κ ℂ :=
  { Matrix.reindexAlgEquiv ℂ ℂ e with
    map_star' := by intro A; ext i j; rfl
    map_smul' := by intro r A; rfl }


-- @@ L60-63 verbatim
omit [DecidableEq ι] [DecidableEq κ] in
theorem trace_reindex (e : ι ≃ κ) (A : Matrix ι ι ℂ) :
    (Matrix.reindex e e A).trace = A.trace := by
  exact Fintype.sum_equiv e.symm _ _ (fun _ ↦ rfl)


-- @@ L65-78 verbatim
theorem entropy_reindex (e : ι ≃ κ) {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    entropy (Matrix.reindex e e A) = entropy A := by
  let φ := reindexStarAlgEquiv e
  have hφA : (φ A).IsHermitian := hA.submatrix e.symm
  have hm := StarAlgHomClass.map_cfc (S := ℂ) φ Real.negMulLog A
    Real.continuous_negMulLog.continuousOn
    (show Continuous φ by
      change Continuous (fun A : Matrix ι ι ℂ ↦ A.submatrix e.symm e.symm)
      fun_prop) hA hφA
  unfold entropy
  change (cfc Real.negMulLog (φ A)).trace.re = _
  calc
    _ = (φ (cfc Real.negMulLog A)).trace.re := congrArg (fun B : Matrix κ κ ℂ ↦ B.trace.re) hm.symm
    _ = _ := congrArg Complex.re (trace_reindex e _)


-- @@ L80-80 verbatim
end GAD

-- @@ L81-81 verbatim
open scoped BigOperators ComplexOrder MatrixOrder Kronecker

-- @@ L82-82 verbatim
open Matrix

-- @@ L83-83 verbatim
namespace GAD

-- @@ L84-84 verbatim
variable {ι : Type u_3} {κ : Type u_4} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]


-- @@ L86-88 verbatim
def tensorUnitary (U : Matrix.unitaryGroup ι ℂ) (V : Matrix.unitaryGroup κ ℂ) :
    Matrix.unitaryGroup (ι × κ) ℂ :=
  ⟨(U : Matrix ι ι ℂ) ⊗ₖ (V : Matrix κ κ ℂ), Matrix.kronecker_mem_unitary U.prop V.prop⟩


-- @@ L90-115 verbatim
theorem entropy_kronecker {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    entropy (A ⊗ₖ B) = B.trace.re * entropy A + A.trace.re * entropy B := by
  let U := hA.eigenvectorUnitary
  let V := hB.eigenvectorUnitary
  let W := tensorUnitary U V
  let p := hA.eigenvalues
  let q := hB.eigenvalues
  have he : A ⊗ₖ B = Unitary.conjStarAlgAut ℂ _ W
      (Matrix.diagonal (fun ij : ι × κ ↦ ((p ij.1*q ij.2 : ℝ):ℂ))) := by
    conv_lhs => rw [hA.spectral_theorem, hB.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
    change _ = ((U : Matrix ι ι ℂ) ⊗ₖ (V : Matrix κ κ ℂ)) * _ *
      (((U : Matrix ι ι ℂ) ⊗ₖ (V : Matrix κ κ ℂ)).conjTranspose)
    rw [Matrix.conjTranspose_kronecker, Matrix.mul_kronecker_mul,
      Matrix.mul_kronecker_mul, Matrix.diagonal_kronecker_diagonal]
    congr 2
    simp [p,q]
  have hd : (Matrix.diagonal (fun ij : ι × κ ↦ ((p ij.1*q ij.2 : ℝ):ℂ))).IsHermitian :=
    Matrix.isHermitian_diagonal_iff.mpr (fun _ ↦ by simp [IsSelfAdjoint])
  rw [he, entropy_unitary_conj W hd, entropy_diagonal, Fintype.sum_prod_type]
  simp_rw [Real.negMulLog_mul, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  have htrA : A.trace.re = ∑ i, p i := by simpa [p] using congrArg Complex.re hA.trace_eq_sum_eigenvalues
  have htrB : B.trace.re = ∑ j, q j := by simpa [q] using congrArg Complex.re hB.trace_eq_sum_eigenvalues
  rw [htrA,htrB,entropy_eq_sum hA,entropy_eq_sum hB]
  simp [p, q, ← Finset.mul_sum]


-- @@ L117-120 verbatim
theorem entropy_kronecker_state {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ}
    (hA : IsState A) (hB : IsState B) : entropy (A ⊗ₖ B) = entropy A + entropy B := by
  rw [entropy_kronecker hA.1.isHermitian hB.1.isHermitian, hA.2, hB.2]
  simp


-- @@ L122-122 verbatim
end GAD


-- @@ L124-124 verbatim
end


-- @@ L126-126 verbatim
end OAI
