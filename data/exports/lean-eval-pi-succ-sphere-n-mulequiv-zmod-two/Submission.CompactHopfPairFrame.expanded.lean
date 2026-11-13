import Mathlib
import Submission.CompactHopfPairFiber
import Submission.ConcreteZeroPairCassiniCoefficientSO


-- @@ L5-12 verbatim
/-!
# The two zero-class frames of the compact Hopf pair

Along either coordinate circle the polynomial Hopf equation has an
orthonormal derivative frame.  In both cases the full oriented frame is the
product of two simultaneous planar turns.  Thus its stable class is
`1 + 1 = 0`.
-/


-- @@ L14-14 verbatim
set_option autoImplicit false

-- @@ L15-15 verbatim
set_option maxHeartbeats 1600000

-- @@ L16-16 verbatim
set_option maxRecDepth 4000

-- @@ L17-17 verbatim
set_option linter.unusedSimpArgs false


-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
namespace Submission

-- @@ L22-22 verbatim
namespace CompactHopfPairConfiguration


-- @@ L24-24 verbatim
open Set Function Matrix InnerProductSpace

-- @@ L25-25 verbatim
open scoped Topology Matrix RealInnerProductSpace unitInterval


-- @@ L27-27 verbatim
/-! ## A simultaneous turn in the first two coordinate planes -/


-- @@ L29-38 verbatim
/-- Two identical planar rotation blocks, followed by identity blocks.  The
parameter `k` counts the coordinates after the leading four. -/
def doubleRotMat : (k : ℕ) → ℝ →
    Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ
  | 0, theta =>
      !![Real.cos theta, -Real.sin theta, 0, 0;
         Real.sin theta,  Real.cos theta, 0, 0;
         0, 0, Real.cos theta, -Real.sin theta;
         0, 0, Real.sin theta,  Real.cos theta]
  | k + 1, theta => incMatrix (doubleRotMat k theta)


-- @@ L40-50 verbatim
theorem doubleRotMat_mul_transpose : ∀ k theta,
    doubleRotMat k theta * (doubleRotMat k theta)ᵀ = 1
  | 0, theta => by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [doubleRotMat, Matrix.mul_apply, Fin.sum_univ_four,
          Matrix.transpose_apply, Matrix.one_apply] <;>
        nlinarith [Real.sin_sq_add_cos_sq theta]
  | k + 1, theta => by
      rw [doubleRotMat, incMatrix_transpose, incMatrix_mul,
        doubleRotMat_mul_transpose k theta, incMatrix_one]


-- @@ L52-90 verbatim
theorem doubleRotMat_det : ∀ k theta, (doubleRotMat k theta).det = 1
  | 0, theta => by
      let A : Matrix (Fin 2) (Fin 2) ℝ :=
        !![Real.cos theta, -Real.sin theta;
           Real.sin theta,  Real.cos theta]
      have hA : A.det = 1 := by
        rw [Matrix.det_fin_two_of]
        simp [A]
        nlinarith [Real.sin_sq_add_cos_sq theta]
      let B : Matrix (Fin 4) (Fin 4) ℝ :=
        (Matrix.fromBlocks A 0 0 A).submatrix
          (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4).symm
          (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4).symm
      have h0 : (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4).symm 0 =
          Sum.inl 0 := by
        simpa using (finSumFinEquiv_symm_apply_castAdd
          (n := 2) (0 : Fin 2))
      have h1 : (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4).symm 1 =
          Sum.inl 1 := by
        simpa using (finSumFinEquiv_symm_apply_castAdd
          (n := 2) (1 : Fin 2))
      have h2 : (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4).symm 2 =
          Sum.inr 0 := by
        simpa using (finSumFinEquiv_symm_apply_natAdd
          (m := 2) (0 : Fin 2))
      have h3 : (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4).symm 3 =
          Sum.inr 1 := by
        simpa using (finSumFinEquiv_symm_apply_natAdd
          (m := 2) (1 : Fin 2))
      have hblock : doubleRotMat 0 theta = B := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [doubleRotMat, B, A, h0, h1, h2, h3, rotBlock]
      rw [hblock]
      dsimp [B]
      rw [Matrix.det_submatrix_equiv_self,
        Matrix.det_fromBlocks_zero₂₁, hA, mul_one]
  | k + 1, theta => by
      rw [doubleRotMat, incMatrix_det, doubleRotMat_det k theta]


-- @@ L92-97 verbatim
theorem doubleRotMat_mem (k : ℕ) (theta : ℝ) :
    doubleRotMat k theta ∈
      Matrix.specialOrthogonalGroup (Fin (k + 4)) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  exact ⟨(Matrix.mem_orthogonalGroup_iff _ _).mpr
      (doubleRotMat_mul_transpose k theta), doubleRotMat_det k theta⟩


-- @@ L99-100 verbatim
def doubleRotSO (k : ℕ) (theta : ℝ) : SOGroup (k + 4) :=
  ⟨doubleRotMat k theta, doubleRotMat_mem k theta⟩


-- @@ L102-112 verbatim
theorem continuous_doubleRotMat (k : ℕ) : Continuous (doubleRotMat k) := by
  induction k with
  | zero =>
      apply continuous_matrix
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [doubleRotMat] <;> fun_prop
  | succ k ih =>
      show Continuous fun theta => incMatrix (doubleRotMat k theta)
      exact (ih.matrix_fromBlocks continuous_const continuous_const
        continuous_const).matrix_submatrix _ _


-- @@ L114-192 verbatim
lemma doubleRotMat_apply (k : ℕ) (theta : ℝ)
    (i j : Fin (k + 4)) :
    doubleRotMat k theta i j =
      if i = 0 then
        (if j = 0 then Real.cos theta
          else if j = 1 then -Real.sin theta else 0)
      else if i = 1 then
        (if j = 0 then Real.sin theta
          else if j = 1 then Real.cos theta else 0)
      else if i = 2 then
        (if j = 2 then Real.cos theta
          else if j = 3 then -Real.sin theta else 0)
      else if i = 3 then
        (if j = 2 then Real.sin theta
          else if j = 3 then Real.cos theta else 0)
      else if j = i then 1 else 0 := by
  induction k with
  | zero =>
      fin_cases i <;> fin_cases j <;> simp [doubleRotMat]
  | succ k ih =>
      rw [doubleRotMat]
      have hcast0 : ((0 : Fin (k + 4)).castSucc : Fin (k + 5)) = 0 := rfl
      have hcast1 : ((1 : Fin (k + 4)).castSucc : Fin (k + 5)) = 1 := by
        apply Fin.ext
        simp [Nat.mod_eq_of_lt (by omega : 1 < k + 5)]
      have hcast2 : ((2 : Fin (k + 4)).castSucc : Fin (k + 5)) = 2 := by
        apply Fin.ext
        simp [Nat.mod_eq_of_lt (by omega : 2 < k + 5)]
      have hcast3 : ((3 : Fin (k + 4)).castSucc : Fin (k + 5)) = 3 := by
        apply Fin.ext
        simp [Nat.mod_eq_of_lt (by omega : 3 < k + 5)]
      have hEq0 (x : Fin (k + 4)) :
          x.castSucc = (0 : Fin (k + 5)) ↔ x = 0 := by
        rw [← hcast0]
        exact Fin.castSucc_inj
      have hEq1 (x : Fin (k + 4)) :
          x.castSucc = (1 : Fin (k + 5)) ↔ x = 1 := by
        rw [← hcast1]
        exact Fin.castSucc_inj
      have hEq2 (x : Fin (k + 4)) :
          x.castSucc = (2 : Fin (k + 5)) ↔ x = 2 := by
        rw [← hcast2]
        exact Fin.castSucc_inj
      have hEq3 (x : Fin (k + 4)) :
          x.castSucc = (3 : Fin (k + 5)) ↔ x = 3 := by
        rw [← hcast3]
        exact Fin.castSucc_inj
      have hlast0 : Fin.last (k + 4) ≠ (0 : Fin (k + 5)) := by
        rw [← hcast0]
        exact Ne.symm (Fin.castSucc_ne_last 0)
      have hlast1 : Fin.last (k + 4) ≠ (1 : Fin (k + 5)) := by
        rw [← hcast1]
        exact Ne.symm (Fin.castSucc_ne_last 1)
      have hlast2 : Fin.last (k + 4) ≠ (2 : Fin (k + 5)) := by
        rw [← hcast2]
        exact Ne.symm (Fin.castSucc_ne_last 2)
      have hlast3 : Fin.last (k + 4) ≠ (3 : Fin (k + 5)) := by
        rw [← hcast3]
        exact Ne.symm (Fin.castSucc_ne_last 3)
      induction i using Fin.lastCases with
      | last =>
          induction j using Fin.lastCases with
          | last =>
              rw [incMatrix_apply_last_last]
              simp [hlast0, hlast1, hlast2, hlast3,
                Fin.castSucc_ne_last, eq_comm]
          | cast j =>
              rw [incMatrix_apply_last_castSucc]
              simp [hlast0, hlast1, hlast2, hlast3, hEq0, hEq1,
                hEq2, hEq3, Fin.castSucc_ne_last, eq_comm]
      | cast i =>
          induction j using Fin.lastCases with
          | last =>
              rw [incMatrix_apply_castSucc_last]
              simp [hlast0, hlast1, hlast2, hlast3, hEq0, hEq1,
                hEq2, hEq3, Fin.castSucc_ne_last, eq_comm]
          | cast j =>
              rw [incMatrix_apply_castSucc_castSucc, ih]
              simp [hEq0, hEq1, hEq2, hEq3, eq_comm]


-- @@ L194-195 verbatim
theorem continuous_doubleRotSO (k : ℕ) : Continuous (doubleRotSO k) := by
  exact Continuous.subtype_mk (continuous_doubleRotMat k) _


-- @@ L197-200 verbatim
/-- The even permutation exchanging the first and second coordinate planes in
dimension four. -/
def planeSwapPerm : Equiv.Perm (Fin 4) :=
  Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3


-- @@ L202-203 verbatim
def planeSwapMat : Matrix (Fin 4) (Fin 4) ℝ :=
  planeSwapPerm.permMatrix ℝ


-- @@ L205-208 verbatim
lemma planeSwapMat_mul_transpose :
    planeSwapMat * planeSwapMatᵀ = 1 := by
  rw [planeSwapMat, Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul]
  simp


-- @@ L210-212 verbatim
lemma planeSwapMat_det : planeSwapMat.det = 1 := by
  rw [planeSwapMat, Matrix.det_permutation]
  simp [planeSwapPerm, Equiv.Perm.sign_swap]


-- @@ L214-218 verbatim
lemma planeSwapMat_mem :
    planeSwapMat ∈ Matrix.specialOrthogonalGroup (Fin 4) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  exact ⟨(Matrix.mem_orthogonalGroup_iff _ _).mpr
      planeSwapMat_mul_transpose, planeSwapMat_det⟩


-- @@ L220-220 verbatim
def planeSwapSO : SOGroup 4 := ⟨planeSwapMat, planeSwapMat_mem⟩


-- @@ L222-237 verbatim
lemma planeSwap_conj_apply
    (A : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 4) :
    (planeSwapMat * A * planeSwapMatᵀ) i j =
      A (planeSwapPerm i) (planeSwapPerm j) := by
  have hright := congrFun
    (Matrix.vecMul_permMatrix (R := ℝ) (planeSwapPerm⁻¹)
      (v := fun x => (planeSwapMat * A) i x)) j
  have hleft := congrFun
    (Matrix.permMatrix_mulVec (R := ℝ) planeSwapPerm
      (v := fun x => A x (planeSwapPerm j))) i
  change ((fun x => (planeSwapMat * A) i x) ᵥ* planeSwapMatᵀ) j = _
  rw [show planeSwapMatᵀ = (planeSwapPerm⁻¹).permMatrix ℝ by
    simp [planeSwapMat]]
  rw [hright]
  change (planeSwapMat *ᵥ (fun x => A x (planeSwapPerm j))) i = _
  exact hleft


-- @@ L239-240 verbatim
lemma planeSwapPerm_apply_zero : planeSwapPerm (0 : Fin 4) = 2 := by
  decide


-- @@ L242-243 verbatim
lemma planeSwapPerm_apply_one : planeSwapPerm (1 : Fin 4) = 3 := by
  decide


-- @@ L245-246 verbatim
lemma planeSwapPerm_apply_two : planeSwapPerm (2 : Fin 4) = 0 := by
  decide


-- @@ L248-249 verbatim
lemma planeSwapPerm_apply_three : planeSwapPerm (3 : Fin 4) = 1 := by
  decide


-- @@ L251-264 verbatim
/-- In dimension four, the simultaneous rotation is the product of the
standard first-plane rotation and its plane-exchanged conjugate. -/
lemma doubleRotMat_zero_factor (theta : ℝ) :
    doubleRotMat 0 theta =
      rotBlock 4 theta *
        (planeSwapMat * rotBlock 4 theta * planeSwapMatᵀ) := by
  ext i j
  rw [Matrix.mul_apply]
  simp_rw [planeSwap_conj_apply]
  fin_cases i <;> fin_cases j <;>
    simp [doubleRotMat, rotBlock_eq_rotAmbient, rotAmbient_apply,
      planeSwapPerm_apply_zero, planeSwapPerm_apply_one,
      planeSwapPerm_apply_two, planeSwapPerm_apply_three,
      Fin.sum_univ_four] <;> ring


-- @@ L266-273 verbatim
/-- The simultaneous two-plane loop, defined by stabilization from dimension
four.  This recursive presentation makes stability of its class immediate. -/
def doubleRotLoop : (k : ℕ) → (z : ℤ) → C(I, SOGroup (k + 4))
  | 0, z =>
      so2Loop 4 (linearAngle z) *
        ((ContinuousMap.const I planeSwapSO * so2Loop 4 (linearAngle z)) *
          ContinuousMap.const I planeSwapSO⁻¹)
  | k + 1, z => incLoop (doubleRotLoop k z)


-- @@ L275-281 verbatim
theorem doubleRotLoop_closed : ∀ k z,
    doubleRotLoop k z 0 = doubleRotLoop k z 1
  | 0, z => by
      simp only [doubleRotLoop, ContinuousMap.mul_apply,
        ContinuousMap.const_apply]
      rw [so2Loop_linearAngle_closed z]
  | k + 1, z => incLoop_closed (doubleRotLoop_closed k z)


-- @@ L283-308 verbatim
theorem doubleRotLoop_apply : ∀ k z (u : I),
    ((doubleRotLoop k z u : SOGroup (k + 4)) :
        Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ) =
      doubleRotMat k (linearAngle z u)
  | 0, z, u => by
      change rotBlock 4 (linearAngle z u) *
          (planeSwapMat * rotBlock 4 (linearAngle z u) *
            (((planeSwapSO)⁻¹ : SOGroup 4) : Matrix (Fin 4) (Fin 4) ℝ)) = _
      have hinv : (((planeSwapSO)⁻¹ : SOGroup 4) :
          Matrix (Fin 4) (Fin 4) ℝ) = planeSwapMatᵀ := by
        have hmul : planeSwapSO * ⟨planeSwapMatᵀ, by
            rw [Matrix.mem_specialOrthogonalGroup_iff]
            exact ⟨(Matrix.mem_orthogonalGroup_iff _ _).mpr
              (by
                rw [Matrix.transpose_transpose]
                exact mul_eq_one_comm.mp planeSwapMat_mul_transpose), by
                rw [Matrix.det_transpose, planeSwapMat_det]⟩⟩ = 1 :=
          Subtype.ext planeSwapMat_mul_transpose
        exact congrArg Subtype.val (eq_inv_of_mul_eq_one_right hmul).symm
      rw [hinv, ← doubleRotMat_zero_factor]
  | k + 1, z, u => by
      change incMatrix
          (((doubleRotLoop k z u : SOGroup (k + 4)) :
            Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ)) = _
      rw [doubleRotLoop_apply k z u]
      rfl


-- @@ L310-329 verbatim
theorem doubleRotLoop_class_zero : ∀ k z,
    loopClassZ2 (doubleRotLoop k z) (doubleRotLoop_closed k z) = 0
  | 0, z => by
      let γ := so2Loop 4 (linearAngle z)
      let δ := (ContinuousMap.const I planeSwapSO * γ) *
        ContinuousMap.const I planeSwapSO⁻¹
      have hγ : γ 0 = γ 1 := so2Loop_linearAngle_closed z
      have hδ : δ 0 = δ 1 := by
        change (planeSwapSO * γ 0) * planeSwapSO⁻¹ =
          (planeSwapSO * γ 1) * planeSwapSO⁻¹
        rw [hγ]
      change loopClassZ2 (γ * δ) _ = 0
      rw [loopClassZ2_mul γ δ hγ hδ]
      rw [show loopClassZ2 δ hδ = loopClassZ2 γ hγ by
        exact loopClassZ2_const_conj planeSwapSO γ hγ]
      exact ZModModule.add_self _
  | k + 1, z => by
      exact (loopClassZ2_stable (m := k + 4) (by omega)
        (doubleRotLoop k z) (doubleRotLoop_closed k z)).trans
          (doubleRotLoop_class_zero k z)


-- @@ L331-331 verbatim
/-! ## Constant gauges for the two Hopf circles -/


-- @@ L333-333 verbatim
variable (k : ℕ)


-- @@ L335-335 verbatim
local notation "Ek" => EuclideanSpace ℝ (Fin (k + 4))

-- @@ L336-336 verbatim
local notation "Fk" => EuclideanSpace ℝ (Fin (k + 3))


-- @@ L338-341 verbatim
private lemma fin_zero_ne_one : (0 : Fin (k + 4)) ≠ 1 := by
  intro h
  have hv := congrArg Fin.val h
  norm_num [Nat.mod_eq_of_lt (by omega : 1 < k + 4)] at hv


-- @@ L343-346 verbatim
private lemma fin_zero_ne_two : (0 : Fin (k + 4)) ≠ 2 := by
  intro h
  have hv := congrArg Fin.val h
  norm_num [Nat.mod_eq_of_lt (by omega : 2 < k + 4)] at hv


-- @@ L348-351 verbatim
private lemma fin_zero_ne_three : (0 : Fin (k + 4)) ≠ 3 := by
  intro h
  have hv := congrArg Fin.val h
  norm_num [Nat.mod_eq_of_lt (by omega : 3 < k + 4)] at hv


-- @@ L353-357 verbatim
private lemma fin_one_ne_two : (1 : Fin (k + 4)) ≠ 2 := by
  intro h
  have hv := congrArg Fin.val h
  norm_num [Nat.mod_eq_of_lt (by omega : 1 < k + 4),
    Nat.mod_eq_of_lt (by omega : 2 < k + 4)] at hv


-- @@ L359-363 verbatim
private lemma fin_one_ne_three : (1 : Fin (k + 4)) ≠ 3 := by
  intro h
  have hv := congrArg Fin.val h
  norm_num [Nat.mod_eq_of_lt (by omega : 1 < k + 4),
    Nat.mod_eq_of_lt (by omega : 3 < k + 4)] at hv


-- @@ L365-369 verbatim
private lemma fin_two_ne_three : (2 : Fin (k + 4)) ≠ 3 := by
  intro h
  have hv := congrArg Fin.val h
  norm_num [Nat.mod_eq_of_lt (by omega : 2 < k + 4),
    Nat.mod_eq_of_lt (by omega : 3 < k + 4)] at hv


-- @@ L371-372 verbatim
def planeSwapPermN : Equiv.Perm (Fin (k + 4)) :=
  Equiv.swap (0 : Fin (k + 4)) 2 * Equiv.swap (1 : Fin (k + 4)) 3


-- @@ L374-375 verbatim
def planeSwapMatN : Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ :=
  (planeSwapPermN k).permMatrix ℝ


-- @@ L377-380 verbatim
lemma planeSwapMatN_mul_transpose :
    planeSwapMatN k * (planeSwapMatN k)ᵀ = 1 := by
  rw [planeSwapMatN, Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul]
  simp


-- @@ L382-387 verbatim
lemma planeSwapMatN_det : (planeSwapMatN k).det = 1 := by
  rw [planeSwapMatN, Matrix.det_permutation]
  rw [planeSwapPermN, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_swap (fin_zero_ne_two k),
    Equiv.Perm.sign_swap (fin_one_ne_three k)]
  norm_num


-- @@ L389-394 verbatim
lemma planeSwapMatN_mem :
    planeSwapMatN k ∈
      Matrix.specialOrthogonalGroup (Fin (k + 4)) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  exact ⟨(Matrix.mem_orthogonalGroup_iff _ _).mpr
      (planeSwapMatN_mul_transpose k), planeSwapMatN_det k⟩


-- @@ L396-397 verbatim
def planeSwapSON : SOGroup (k + 4) :=
  ⟨planeSwapMatN k, planeSwapMatN_mem k⟩


-- @@ L399-406 verbatim
lemma mul_planeSwapMatN_apply
    (A : Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ)
    (i j : Fin (k + 4)) :
    (A * planeSwapMatN k) i j = A i ((planeSwapPermN k).symm j) := by
  have hv := congrFun
    (Matrix.vecMul_permMatrix (R := ℝ) (planeSwapPermN k) (v := A i)) j
  change ((A i) ᵥ* planeSwapMatN k) j = _
  simpa only [planeSwapMatN, Function.comp_apply] using hv


-- @@ L408-414 verbatim
lemma planeSwapPermN_apply_zero : planeSwapPermN k (0 : Fin (k + 4)) = 2 := by
  simp [planeSwapPermN, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
    fin_zero_ne_one k, fin_zero_ne_two k, fin_zero_ne_three k,
    fin_one_ne_two k, fin_one_ne_three k, fin_two_ne_three k,
    Ne.symm (fin_zero_ne_one k), Ne.symm (fin_zero_ne_two k),
    Ne.symm (fin_zero_ne_three k), Ne.symm (fin_one_ne_two k),
    Ne.symm (fin_one_ne_three k), Ne.symm (fin_two_ne_three k)]


-- @@ L416-422 verbatim
lemma planeSwapPermN_apply_one : planeSwapPermN k (1 : Fin (k + 4)) = 3 := by
  simp [planeSwapPermN, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
    fin_zero_ne_one k, fin_zero_ne_two k, fin_zero_ne_three k,
    fin_one_ne_two k, fin_one_ne_three k, fin_two_ne_three k,
    Ne.symm (fin_zero_ne_one k), Ne.symm (fin_zero_ne_two k),
    Ne.symm (fin_zero_ne_three k), Ne.symm (fin_one_ne_two k),
    Ne.symm (fin_one_ne_three k), Ne.symm (fin_two_ne_three k)]


-- @@ L424-430 verbatim
lemma planeSwapPermN_apply_two : planeSwapPermN k (2 : Fin (k + 4)) = 0 := by
  simp [planeSwapPermN, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
    fin_zero_ne_one k, fin_zero_ne_two k, fin_zero_ne_three k,
    fin_one_ne_two k, fin_one_ne_three k, fin_two_ne_three k,
    Ne.symm (fin_zero_ne_one k), Ne.symm (fin_zero_ne_two k),
    Ne.symm (fin_zero_ne_three k), Ne.symm (fin_one_ne_two k),
    Ne.symm (fin_one_ne_three k), Ne.symm (fin_two_ne_three k)]


-- @@ L432-438 verbatim
lemma planeSwapPermN_apply_three : planeSwapPermN k (3 : Fin (k + 4)) = 1 := by
  simp [planeSwapPermN, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
    fin_zero_ne_one k, fin_zero_ne_two k, fin_zero_ne_three k,
    fin_one_ne_two k, fin_one_ne_three k, fin_two_ne_three k,
    Ne.symm (fin_zero_ne_one k), Ne.symm (fin_zero_ne_two k),
    Ne.symm (fin_zero_ne_three k), Ne.symm (fin_one_ne_two k),
    Ne.symm (fin_one_ne_three k), Ne.symm (fin_two_ne_three k)]


-- @@ L440-445 verbatim
lemma planeSwapPermN_apply_other {j : Fin (k + 4)}
    (hj0 : j ≠ 0) (hj1 : j ≠ 1) (hj2 : j ≠ 2) (hj3 : j ≠ 3) :
    planeSwapPermN k j = j := by
  simp [planeSwapPermN, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
    hj0, hj1, hj2, hj3, Ne.symm hj0, Ne.symm hj1,
    Ne.symm hj2, Ne.symm hj3]


-- @@ L447-450 verbatim
lemma planeSwapPermN_symm_apply_zero :
    (planeSwapPermN k).symm (0 : Fin (k + 4)) = 2 := by
  rw [Equiv.symm_apply_eq]
  exact planeSwapPermN_apply_two k


-- @@ L452-455 verbatim
lemma planeSwapPermN_symm_apply_one :
    (planeSwapPermN k).symm (1 : Fin (k + 4)) = 3 := by
  rw [Equiv.symm_apply_eq]
  exact planeSwapPermN_apply_three k


-- @@ L457-460 verbatim
lemma planeSwapPermN_symm_apply_two :
    (planeSwapPermN k).symm (2 : Fin (k + 4)) = 0 := by
  rw [Equiv.symm_apply_eq]
  exact planeSwapPermN_apply_zero k


-- @@ L462-465 verbatim
lemma planeSwapPermN_symm_apply_three :
    (planeSwapPermN k).symm (3 : Fin (k + 4)) = 1 := by
  rw [Equiv.symm_apply_eq]
  exact planeSwapPermN_apply_one k


-- @@ L467-471 verbatim
lemma planeSwapPermN_symm_apply_other {j : Fin (k + 4)}
    (hj0 : j ≠ 0) (hj1 : j ≠ 1) (hj2 : j ≠ 2) (hj3 : j ≠ 3) :
    (planeSwapPermN k).symm j = j := by
  rw [Equiv.symm_apply_eq]
  exact (planeSwapPermN_apply_other k hj0 hj1 hj2 hj3).symm


-- @@ L473-475 verbatim
/-- The angle-zero first-circle frame: `[e₁,e₀,e₂,-e₃,…]`. -/
def firstInitialSO : SOGroup (k + 4) :=
  doubleSignSO (2 : Fin (k + 3)) * tubeInitialSO (k + 1)


-- @@ L477-479 verbatim
/-- The angle-zero second-circle frame: `[-e₃,e₂,e₀,e₁,…]`. -/
def secondInitialSO : SOGroup (k + 4) :=
  tubeInitialSO (k + 1) * planeSwapSON k


-- @@ L481-508 verbatim
lemma firstInitialSO_apply (i j : Fin (k + 4)) :
    ((firstInitialSO k : SOGroup (k + 4)) :
        Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ) i j =
      if i = 0 then (if j = 1 then 1 else 0)
      else if i = 1 then (if j = 0 then 1 else 0)
      else if i = 2 then (if j = 2 then 1 else 0)
      else if i = 3 then (if j = 3 then -1 else 0)
      else if j = i then 1 else 0 := by
  change (doubleSignMatrix (2 : Fin (k + 3)) *
      (tubeInitialSO (k + 1) :
        Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ)) i j = _
  rw [doubleSignMatrix, Matrix.diagonal_mul]
  have h01 := fin_zero_ne_one k
  have h02 := fin_zero_ne_two k
  have h03 := fin_zero_ne_three k
  have h12 := fin_one_ne_two k
  have h13 := fin_one_ne_three k
  have h23 := fin_two_ne_three k
  have hs : ((2 : Fin (k + 3)).succ : Fin (k + 4)) = 3 := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (by omega : 2 < k + 3),
      Nat.mod_eq_of_lt (by omega : 3 < k + 4)]
  by_cases hi0 : i = 0 <;> by_cases hi1 : i = 1 <;>
    by_cases hi2 : i = 2 <;> by_cases hi3 : i = 3 <;>
    by_cases hj0 : j = 0 <;> by_cases hj1 : j = 1 <;>
    by_cases hj2 : j = 2 <;> by_cases hj3 : j = 3 <;>
    by_cases hji : j = i <;>
    simp_all [doubleSignCoeff, hs, tubeInitialSO_apply]


-- @@ L510-535 verbatim
lemma secondInitialSO_apply (i j : Fin (k + 4)) :
    ((secondInitialSO k : SOGroup (k + 4)) :
        Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ) i j =
      if i = 0 then (if j = 3 then -1 else 0)
      else if i = 1 then (if j = 2 then 1 else 0)
      else if i = 2 then (if j = 0 then 1 else 0)
      else if i = 3 then (if j = 1 then 1 else 0)
      else if j = i then 1 else 0 := by
  change ((tubeInitialSO (k + 1) :
      Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ) * planeSwapMatN k) i j = _
  rw [mul_planeSwapMatN_apply, tubeInitialSO_apply]
  have h01 := fin_zero_ne_one k
  have h02 := fin_zero_ne_two k
  have h03 := fin_zero_ne_three k
  have h12 := fin_one_ne_two k
  have h13 := fin_one_ne_three k
  have h23 := fin_two_ne_three k
  by_cases hi0 : i = 0 <;> by_cases hi1 : i = 1 <;>
    by_cases hi2 : i = 2 <;> by_cases hi3 : i = 3 <;>
    by_cases hj0 : j = 0 <;> by_cases hj1 : j = 1 <;>
    by_cases hj2 : j = 2 <;> by_cases hj3 : j = 3 <;>
    by_cases hji : j = i <;>
    simp_all [planeSwapPermN_symm_apply_zero,
      planeSwapPermN_symm_apply_one, planeSwapPermN_symm_apply_two,
      planeSwapPermN_symm_apply_three, planeSwapPermN_symm_apply_other,
      eq_comm]


-- @@ L537-539 verbatim
/-- The two explicit oriented SO frames along the coordinate circles. -/
def firstHopfSO (theta : ℝ) : SOGroup (k + 4) :=
  doubleRotSO k theta * firstInitialSO k


-- @@ L541-542 verbatim
def secondHopfSO (theta : ℝ) : SOGroup (k + 4) :=
  doubleRotSO k (-theta) * secondInitialSO k


-- @@ L544-599 verbatim
lemma mul_firstInitialSO_apply
    (A : Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ)
    (i j : Fin (k + 4)) :
    (A * ((firstInitialSO k : SOGroup (k + 4)) :
      Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ)) i j =
      if j = 0 then A i 1 else if j = 1 then A i 0
      else if j = 2 then A i 2 else if j = 3 then -A i 3 else A i j := by
  rw [Matrix.mul_apply]
  have h01 := fin_zero_ne_one k
  have h02 := fin_zero_ne_two k
  have h03 := fin_zero_ne_three k
  have h12 := fin_one_ne_two k
  have h13 := fin_one_ne_three k
  have h23 := fin_two_ne_three k
  by_cases hj0 : j = 0
  · subst j
    rw [Finset.sum_eq_single (1 : Fin (k + 4))]
    · simp [firstInitialSO_apply, h01, h02, h03, h12, h13, h23,
        eq_comm]
    · intro c _ hc
      simp [firstInitialSO_apply, hc, h01, h02, h03, h12, h13, h23,
        eq_comm] <;> aesop
    · exact fun h => absurd (Finset.mem_univ _) h
  · by_cases hj1 : j = 1
    · subst j
      rw [Finset.sum_eq_single (0 : Fin (k + 4))]
      · simp [firstInitialSO_apply, h01, h02, h03, h12, h13, h23,
          eq_comm]
      · intro c _ hc
        simp [firstInitialSO_apply, hc, h01, h02, h03, h12, h13, h23,
          eq_comm] <;> aesop
      · exact fun h => absurd (Finset.mem_univ _) h
    · by_cases hj2 : j = 2
      · subst j
        rw [Finset.sum_eq_single (2 : Fin (k + 4))]
        · simp [firstInitialSO_apply, h01, h02, h03, h12, h13, h23,
            eq_comm]
        · intro c _ hc
          simp [firstInitialSO_apply, hc, h01, h02, h03, h12, h13, h23,
            eq_comm] <;> aesop
        · exact fun h => absurd (Finset.mem_univ _) h
      · by_cases hj3 : j = 3
        · subst j
          rw [Finset.sum_eq_single (3 : Fin (k + 4))]
          · simp [firstInitialSO_apply, h01, h02, h03, h12, h13, h23,
              eq_comm]
          · intro c _ hc
            simp [firstInitialSO_apply, hc, h01, h02, h03, h12, h13, h23,
              eq_comm] <;> aesop
          · exact fun h => absurd (Finset.mem_univ _) h
        · rw [Finset.sum_eq_single j]
          · simp [firstInitialSO_apply, hj0, hj1, hj2, hj3, eq_comm]
          · intro c _ hc
            simp [firstInitialSO_apply, hj0, hj1, hj2, hj3, hc, eq_comm] <;>
              aesop
          · exact fun h => absurd (Finset.mem_univ _) h


-- @@ L601-633 verbatim
lemma firstHopfSO_apply (theta : ℝ) (i j : Fin (k + 4)) :
    ((firstHopfSO k theta : SOGroup (k + 4)) :
        Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ) i j =
      if i = 0 then
        (if j = 0 then -Real.sin theta
          else if j = 1 then Real.cos theta else 0)
      else if i = 1 then
        (if j = 0 then Real.cos theta
          else if j = 1 then Real.sin theta else 0)
      else if i = 2 then
        (if j = 2 then Real.cos theta
          else if j = 3 then Real.sin theta else 0)
      else if i = 3 then
        (if j = 2 then Real.sin theta
          else if j = 3 then -Real.cos theta else 0)
      else if j = i then 1 else 0 := by
  change (doubleRotMat k theta *
    ((firstInitialSO k : SOGroup (k + 4)) :
      Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ)) i j = _
  rw [mul_firstInitialSO_apply]
  simp_rw [doubleRotMat_apply]
  have h01 := fin_zero_ne_one k
  have h02 := fin_zero_ne_two k
  have h03 := fin_zero_ne_three k
  have h12 := fin_one_ne_two k
  have h13 := fin_one_ne_three k
  have h23 := fin_two_ne_three k
  by_cases hi0 : i = 0 <;> by_cases hi1 : i = 1 <;>
    by_cases hi2 : i = 2 <;> by_cases hi3 : i = 3 <;>
    by_cases hj0 : j = 0 <;> by_cases hj1 : j = 1 <;>
    by_cases hj2 : j = 2 <;> by_cases hj3 : j = 3 <;>
    by_cases hji : j = i <;>
    simp_all [eq_comm]


-- @@ L635-690 verbatim
lemma mul_secondInitialSO_apply
    (A : Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ)
    (i j : Fin (k + 4)) :
    (A * ((secondInitialSO k : SOGroup (k + 4)) :
      Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ)) i j =
      if j = 0 then A i 2 else if j = 1 then A i 3
      else if j = 2 then A i 1 else if j = 3 then -A i 0 else A i j := by
  rw [Matrix.mul_apply]
  have h01 := fin_zero_ne_one k
  have h02 := fin_zero_ne_two k
  have h03 := fin_zero_ne_three k
  have h12 := fin_one_ne_two k
  have h13 := fin_one_ne_three k
  have h23 := fin_two_ne_three k
  by_cases hj0 : j = 0
  · subst j
    rw [Finset.sum_eq_single (2 : Fin (k + 4))]
    · simp [secondInitialSO_apply, h01, h02, h03, h12, h13, h23,
        eq_comm]
    · intro c _ hc
      simp [secondInitialSO_apply, hc, h01, h02, h03, h12, h13, h23,
        eq_comm] <;> aesop
    · exact fun h => absurd (Finset.mem_univ _) h
  · by_cases hj1 : j = 1
    · subst j
      rw [Finset.sum_eq_single (3 : Fin (k + 4))]
      · simp [secondInitialSO_apply, h01, h02, h03, h12, h13, h23,
          eq_comm]
      · intro c _ hc
        simp [secondInitialSO_apply, hc, h01, h02, h03, h12, h13, h23,
          eq_comm] <;> aesop
      · exact fun h => absurd (Finset.mem_univ _) h
    · by_cases hj2 : j = 2
      · subst j
        rw [Finset.sum_eq_single (1 : Fin (k + 4))]
        · simp [secondInitialSO_apply, h01, h02, h03, h12, h13, h23,
            eq_comm]
        · intro c _ hc
          simp [secondInitialSO_apply, hc, h01, h02, h03, h12, h13, h23,
            eq_comm] <;> aesop
        · exact fun h => absurd (Finset.mem_univ _) h
      · by_cases hj3 : j = 3
        · subst j
          rw [Finset.sum_eq_single (0 : Fin (k + 4))]
          · simp [secondInitialSO_apply, h01, h02, h03, h12, h13, h23,
              eq_comm]
          · intro c _ hc
            simp [secondInitialSO_apply, hc, h01, h02, h03, h12, h13, h23,
              eq_comm] <;> aesop
          · exact fun h => absurd (Finset.mem_univ _) h
        · rw [Finset.sum_eq_single j]
          · simp [secondInitialSO_apply, hj0, hj1, hj2, hj3, eq_comm]
          · intro c _ hc
            simp [secondInitialSO_apply, hj0, hj1, hj2, hj3, hc, eq_comm] <;>
              aesop
          · exact fun h => absurd (Finset.mem_univ _) h


-- @@ L692-724 verbatim
lemma secondHopfSO_apply (theta : ℝ) (i j : Fin (k + 4)) :
    ((secondHopfSO k theta : SOGroup (k + 4)) :
        Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ) i j =
      if i = 0 then
        (if j = 2 then Real.sin theta
          else if j = 3 then -Real.cos theta else 0)
      else if i = 1 then
        (if j = 2 then Real.cos theta
          else if j = 3 then Real.sin theta else 0)
      else if i = 2 then
        (if j = 0 then Real.cos theta
          else if j = 1 then Real.sin theta else 0)
      else if i = 3 then
        (if j = 0 then -Real.sin theta
          else if j = 1 then Real.cos theta else 0)
      else if j = i then 1 else 0 := by
  change (doubleRotMat k (-theta) *
    ((secondInitialSO k : SOGroup (k + 4)) :
      Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ)) i j = _
  rw [mul_secondInitialSO_apply]
  simp_rw [doubleRotMat_apply]
  have h01 := fin_zero_ne_one k
  have h02 := fin_zero_ne_two k
  have h03 := fin_zero_ne_three k
  have h12 := fin_one_ne_two k
  have h13 := fin_one_ne_three k
  have h23 := fin_two_ne_three k
  by_cases hi0 : i = 0 <;> by_cases hi1 : i = 1 <;>
    by_cases hi2 : i = 2 <;> by_cases hi3 : i = 3 <;>
    by_cases hj0 : j = 0 <;> by_cases hj1 : j = 1 <;>
    by_cases hj2 : j = 2 <;> by_cases hj3 : j = 3 <;>
    by_cases hji : j = i <;>
    simp_all [eq_comm, Real.sin_neg, Real.cos_neg]


-- @@ L726-726 verbatim
end CompactHopfPairConfiguration

-- @@ L727-727 verbatim
end Submission
