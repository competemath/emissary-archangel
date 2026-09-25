/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.ForMathlib.HermitianMat.Order
public import QuantumInfo.ForMathlib.Isometry


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
noncomputable section


-- @@ L15-15 verbatim
namespace Matrix


-- @@ L17-17 verbatim
variable {d R S F 𝕜 : Type*} [Fintype d] [DecidableEq d]

-- @@ L18-18 verbatim
variable [CommSemiring R] [Semiring S] [Algebra R S] [Field F] [RCLike 𝕜]


-- @@ L20-25 verbatim
theorem isUnit_smul {c : R} (hA : IsUnit c) {M : Matrix d d S} (hM : IsUnit M) :
    IsUnit (c • M : Matrix d d S) := by
  obtain ⟨d, rfl⟩ := hA
  obtain ⟨M', rfl⟩ := hM
  use d • M'
  rfl


-- @@ L27-28 verbatim
theorem isUnit_natCast {n : ℕ} (hn : n ≠ 0) [CharZero F] : IsUnit (n : Matrix d d F) := by
  exact (IsUnit.mk0 (n : F) (mod_cast hn)).map (algebraMap F _)


-- @@ L30-32 verbatim
theorem isUnit_real_smul {r : ℝ} (hr : r ≠ 0) {M : Matrix d d 𝕜} (hM : IsUnit M) :
    IsUnit (r • M : Matrix d d 𝕜) :=
  isUnit_smul hr.isUnit hM


-- @@ L34-35 verbatim
theorem isUnit_real_cast {r : ℝ} (hr : r ≠ 0) : IsUnit (r • 1 : Matrix d d 𝕜) := by
  exact isUnit_real_smul hr isUnit_one


-- @@ L37-37 verbatim
end Matrix


-- @@ L39-39 verbatim
namespace HermitianMat


-- @@ L41-41 verbatim
variable {n m R 𝕜 : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

-- @@ L42-42 verbatim
variable [CommRing R] [StarRing R] [RCLike 𝕜]

-- @@ L43-43 verbatim
variable (A : HermitianMat n R) (B : HermitianMat m R)


-- @@ L45-46 verbatim
class NonSingular (A : HermitianMat n R) : Prop where
  isUnit : IsUnit A.mat


-- @@ L48-50 verbatim
@[simp]
theorem isUnit_mat_of_nonSingular [NonSingular A] : IsUnit A.mat :=
  NonSingular.isUnit


-- @@ L52-53 verbatim
theorem nonsingular_iff_isUnit : NonSingular A ↔ IsUnit A.mat := by
  exact Iff.intro (fun h ↦ h.isUnit) NonSingular.mk


-- @@ L55-56 verbatim
instance instHasInv_of_invertible [i : Invertible A.mat] : NonSingular A :=
  ⟨isUnit_of_invertible _⟩


-- @@ L58-59 verbatim
instance instInvertible_of_hasInv [h : NonSingular A] : Invertible A.mat :=
  h.isUnit.invertible


-- @@ L61-62 verbatim
instance : NonSingular (1 : HermitianMat n R) :=
  instHasInv_of_invertible (i := invertibleOne)


-- @@ L64-64 verbatim
variable {A : HermitianMat n 𝕜} {B : HermitianMat m 𝕜} {C : Matrix n n 𝕜}

-- @@ L65-65 verbatim
open ComplexOrder


-- @@ L67-68 verbatim
theorem nonSingular_of_posDef (hA : A.mat.PosDef) : NonSingular A :=
  ⟨hA.isUnit⟩


-- @@ L70-74 verbatim
theorem nonSingular_iff_posDef_of_PSD (hA : 0 ≤ A) :
    NonSingular A ↔ A.mat.PosDef := by
  refine ⟨fun h ↦ ?_, fun hA₂ ↦ nonSingular_of_posDef hA₂⟩
  have : IsUnit A.mat := h.isUnit
  grind [zero_le_iff]


-- @@ L76-77 verbatim
theorem nonSingular_smul [i : NonSingular A] {c : ℝ} (hc : IsUnit c) : NonSingular (c • A) :=
  ⟨Matrix.isUnit_smul hc i.isUnit⟩


-- @@ L79-80 verbatim
theorem nonSingular_iff_zero_notMem_spectrum : NonSingular A ↔ 0 ∉ spectrum ℝ A.mat := by
  simp [nonsingular_iff_isUnit, spectrum, resolventSet]


-- @@ L82-83 verbatim
theorem nonSingular_iff_eigenvalue_ne_zero : NonSingular A ↔ ∀ i, A.H.eigenvalues i ≠ 0 := by
  simp [nonSingular_iff_zero_notMem_spectrum, A.H.spectrum_real_eq_range_eigenvalues]


-- @@ L85-86 verbatim
theorem nonSingular_iff_det_ne_zero : NonSingular A ↔ A.mat.det ≠ 0 := by
  simp [Matrix.isUnit_iff_isUnit_det, nonsingular_iff_isUnit]


-- @@ L88-112 verbatim
theorem nonSingular_iff_ker_bot : NonSingular A ↔ A.ker = ⊥ := by
  rw [nonSingular_iff_det_ne_zero];
  have h_det_nonzero_to_ker_trivial : A.mat.det ≠ 0 → A.ker = ⊥ := by
    intro h_det_nonzero
    rw [Submodule.eq_bot_iff]
    have h_inv : Invertible A.mat := by
      convert Matrix.invertibleOfDetInvertible A.mat
      exact invertibleOfNonzero h_det_nonzero
    have h_ker_trivial (x : n → 𝕜) (hx : A.mat.mulVec x = 0) : x = 0 := by
      simpa using congr_arg (h_inv.1.mulVec) hx
    intro x hx
    rw [mem_ker_iff_mulVec_zero] at hx
    exact PiLp.ext (fun i => congr_fun (h_ker_trivial x.ofLp hx) i)
  refine ⟨h_det_nonzero_to_ker_trivial, fun h h' => ?_⟩
  obtain ⟨x, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h'
  have h_inj : Function.Injective (Matrix.mulVecLin A.mat) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hy
    have hm : (WithLp.toLp 2 y) ∈ A.ker := (mem_ker_iff_mulVec_zero A _).mpr hy
    rw [h] at hm
    have := (Submodule.mem_bot (R := 𝕜)).mp hm
    simpa using this
  specialize @h_inj x 0
  simp_all


-- @@ L114-131 verbatim
theorem nonSingular_iff_support_top : NonSingular A ↔ A.support = ⊤ := by
  simp only [support, Submodule.eq_top_iff']
  refine ⟨fun hA ↦ ?_, fun hA ↦ ?_⟩
  · intro x
    have hA_inv : IsUnit A.mat := hA.isUnit
    rcases hA_inv.exists_right_inv with ⟨y, hy⟩
    exact ⟨WithLp.toLp 2 (y.mulVec x.ofLp), by
      apply PiLp.ext; intro i
      simp [lin, Matrix.toLpLin_apply, Matrix.mulVec_mulVec, hy]⟩
  · constructor
    have : Function.Surjective A.mat.mulVec := by
      intro y
      obtain ⟨x, hx⟩ := hA (WithLp.toLp 2 y)
      exact ⟨x.ofLp, by
        have := congr_arg WithLp.ofLp hx
        simp [lin, Matrix.toLpLin_apply] at this
        exact this⟩
    exact Matrix.mulVec_surjective_iff_isUnit.mp this


-- @@ L133-135 verbatim
@[simp]
theorem nonSingular_iff_neg : NonSingular (-A) ↔ NonSingular A := by
  simp [nonSingular_iff_det_ne_zero, Matrix.det_neg]


-- @@ L137-140 verbatim
@[simp]
theorem nonSingular_iff_inv : NonSingular (A⁻¹) ↔ NonSingular A := by
  rw [nonsingular_iff_isUnit, nonsingular_iff_isUnit]
  exact Matrix.isUnit_nonsing_inv_iff


-- @@ L142-145 verbatim
@[simp]
theorem nonSingular_iff_kronecker [Nonempty n] [Nonempty m] :
    NonSingular (A ⊗ₖ B) ↔ NonSingular A ∧ NonSingular B := by
  simp [nonSingular_iff_det_ne_zero, Matrix.det_kronecker]


-- @@ L147-148 verbatim
theorem nonSingular_iff_conj (hC : IsUnit C) : NonSingular (A.conj C) ↔ NonSingular A := by
  simp_all [Matrix.isUnit_iff_isUnit_det, nonsingular_iff_isUnit]


-- @@ L150-156 verbatim
@[simp]
theorem nonSingular_iff_reindex (e : n ≃ m) : NonSingular (A.reindex e) ↔ NonSingular A := by
  rw [nonSingular_iff_det_ne_zero, nonSingular_iff_det_ne_zero]
  rw [reindex_eq_conj, ← Matrix.det_reindex_self e, conj_apply_mat]
  congr! 2
  ext : 2
  simp [Matrix.mul_apply, Matrix.one_apply]


-- @@ L158-158 verbatim
section fwd


-- @@ L160-162 verbatim
theorem nonSingular_empty [IsEmpty n] : NonSingular A := by
  rw [Subsingleton.eq_one A]
  infer_instance


-- @@ L164-164 verbatim
variable [NonSingular A] [NonSingular B]


-- @@ L166-167 verbatim
theorem nonSingular_det_ne_zero : A.mat.det ≠ 0 := by
  rwa [← nonSingular_iff_det_ne_zero]


-- @@ L169-171 verbatim
@[simp]
theorem nonSingular_ker_bot : A.ker = ⊥ := by
  rwa [← nonSingular_iff_ker_bot]


-- @@ L173-175 verbatim
@[simp]
theorem nonSingular_support_top : A.support = ⊤ := by
  rwa [← nonSingular_iff_support_top]


-- @@ L177-178 verbatim
instance nonSingular_neg : NonSingular (-A) := by
  rwa [nonSingular_iff_neg]


-- @@ L180-181 verbatim
instance nonSingular_inv : NonSingular (A⁻¹) := by
  rwa [nonSingular_iff_inv]


-- @@ L183-184 verbatim
instance nonSingular_kron [Nonempty n] [Nonempty m] : NonSingular (A ⊗ₖ B) :=
  nonSingular_iff_kronecker.mpr ⟨inferInstance, inferInstance⟩


-- @@ L186-187 verbatim
theorem nonSingular_conj (hC : IsUnit C) : NonSingular (A.conj C) := by
  rwa [nonSingular_iff_conj hC]


-- @@ L189-191 verbatim
instance nonSingular_conj_isometry {B : HermitianMat n 𝕜} [NonSingular B] :
    NonSingular (A.conj B.mat) := by
  simpa [nonSingular_iff_conj]


-- @@ L193-194 verbatim
theorem nonSingular_zero_notMem_spectrum : 0 ∉ spectrum ℝ A.mat := by
  rwa [← nonSingular_iff_zero_notMem_spectrum]


-- @@ L196-197 verbatim
theorem nonSingular_eigenvalue_ne_zero : ∀ i, A.H.eigenvalues i ≠ 0 := by
  rwa [← nonSingular_iff_eigenvalue_ne_zero]


-- @@ L199-199 verbatim
end fwd


-- @@ L201-201 verbatim
end HermitianMat
