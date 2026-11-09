module

public import BernoulliRegular.GaussSum.SignInvariant.Trace


-- @@ L5-10 verbatim
/-!
# Finite-Fourier sign invariants for quadratic Gauss sums

This file contains the operator-theoretic and matrix-reduction part of the
finite-Fourier sign-invariant package.
-/


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
noncomputable section


-- @@ L16-16 verbatim
namespace BernoulliRegular


-- @@ L18-18 verbatim
open scoped BigOperators ComplexConjugate


-- @@ L20-20 verbatim
section SignInvariant


-- @@ L22-22 verbatim
variable (p : ℕ) [hp : Fact p.Prime]


-- @@ L24-27 verbatim
/-- The DFT scaled by `1 / √p`, so that its square is pullback by negation. -/
noncomputable def normalizedDft : (ZMod p → ℂ) →ₗ[ℂ] (ZMod p → ℂ) :=
  ((Real.sqrt p : ℂ)⁻¹) •
    ((ZMod.dft : (ZMod p → ℂ) ≃ₗ[ℂ] (ZMod p → ℂ)).toLinearMap)


-- @@ L29-33 verbatim
/-- Pullback of functions along `x ↦ -x`. -/
noncomputable def negArgumentLinearMap : (ZMod p → ℂ) →ₗ[ℂ] (ZMod p → ℂ) where
  toFun Φ x := Φ (-x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


-- @@ L35-37 verbatim
theorem normalizedDft_apply (Φ : ZMod p → ℂ) (x : ZMod p) :
    normalizedDft p Φ x = (Real.sqrt p : ℂ)⁻¹ * ZMod.dft Φ x := by
  simp [normalizedDft, smul_eq_mul]


-- @@ L39-54 verbatim
theorem normalizedDft_sq_apply (Φ : ZMod p → ℂ) (x : ZMod p) :
    normalizedDft p (normalizedDft p Φ) x = Φ (-x) := by
  have hp_nonneg : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hsqrt_ne : (Real.sqrt p : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.2 (by exact_mod_cast hp.out.pos)
  have hscalar :
      (Real.sqrt p : ℂ)⁻¹ * ((Real.sqrt p : ℂ)⁻¹ * (p : ℂ)) = 1 := by
    field_simp [hsqrt_ne]
    have hsqrt_sq : ((Real.sqrt p : ℂ) ^ 2) = (p : ℂ) := by
      exact_mod_cast (Real.sq_sqrt hp_nonneg)
    simpa [pow_two] using hsqrt_sq.symm
  calc
    normalizedDft p (normalizedDft p Φ) x
        = ((Real.sqrt p : ℂ)⁻¹ * ((Real.sqrt p : ℂ)⁻¹ * (p : ℂ))) * Φ (-x) := by
            simp [normalizedDft, ZMod.dft_dft, mul_assoc, mul_left_comm, mul_comm]
    _ = Φ (-x) := by rw [hscalar, one_mul]


-- @@ L56-62 verbatim
/-- The normalized DFT squares to pullback along negation. -/
theorem normalizedDft_sq_eq_negArgument :
    (normalizedDft p).comp (normalizedDft p) = negArgumentLinearMap p := by
  apply LinearMap.ext
  intro Φ
  ext x
  exact normalizedDft_sq_apply (p := p) Φ x


-- @@ L64-69 verbatim
/-- The submodule of even functions on `ZMod p`. -/
def evenSubmodule : Submodule ℂ (ZMod p → ℂ) where
  carrier := {Φ | Function.Even Φ}
  zero_mem' := Function.Even.zero
  add_mem' hΦ hΨ := hΦ.add hΨ
  smul_mem' c _ hΦ := hΦ.const_smul c


-- @@ L71-76 verbatim
/-- The submodule of odd functions on `ZMod p`. -/
def oddSubmodule : Submodule ℂ (ZMod p → ℂ) where
  carrier := {Φ | Function.Odd Φ}
  zero_mem' := Function.Odd.zero
  add_mem' hΦ hΨ := hΦ.add hΨ
  smul_mem' c _ hΦ := hΦ.const_smul c


-- @@ L78-81 verbatim
theorem normalizedDft_maps_even {Φ : ZMod p → ℂ} (hΦ : Function.Even Φ) :
    Function.Even (normalizedDft p Φ) := by
  have hdft : Function.Even (ZMod.dft Φ) := (ZMod.dft_even_iff).2 hΦ
  simpa [normalizedDft] using hdft.const_smul ((Real.sqrt p : ℂ)⁻¹)


-- @@ L83-86 verbatim
theorem normalizedDft_maps_odd {Φ : ZMod p → ℂ} (hΦ : Function.Odd Φ) :
    Function.Odd (normalizedDft p Φ) := by
  have hdft : Function.Odd (ZMod.dft Φ) := (ZMod.dft_odd_iff).2 hΦ
  simpa [normalizedDft] using hdft.const_smul ((Real.sqrt p : ℂ)⁻¹)


-- @@ L88-91 verbatim
/-- The normalized DFT restricted to the even submodule. -/
noncomputable def normalizedDftEven :
    evenSubmodule (p := p) →ₗ[ℂ] evenSubmodule (p := p) :=
  (normalizedDft (p := p)).restrict fun _ hΦ ↦ normalizedDft_maps_even (p := p) hΦ


-- @@ L93-96 verbatim
/-- The normalized DFT restricted to the odd submodule. -/
noncomputable def normalizedDftOdd :
    oddSubmodule (p := p) →ₗ[ℂ] oddSubmodule (p := p) :=
  (normalizedDft (p := p)).restrict fun _ hΦ ↦ normalizedDft_maps_odd (p := p) hΦ


-- @@ L98-103 verbatim
/-- On even functions, the normalized DFT squares to the identity. -/
theorem normalizedDft_sq_eq_self_of_even {Φ : ZMod p → ℂ} (hΦ : Function.Even Φ) :
    normalizedDft p (normalizedDft p Φ) = Φ := by
  ext x
  rw [normalizedDft_sq_apply (p := p)]
  exact hΦ x


-- @@ L105-110 verbatim
/-- On odd functions, the normalized DFT squares to minus the identity. -/
theorem normalizedDft_sq_eq_neg_self_of_odd {Φ : ZMod p → ℂ} (hΦ : Function.Odd Φ) :
    normalizedDft p (normalizedDft p Φ) = -Φ := by
  ext x
  rw [normalizedDft_sq_apply (p := p)]
  simpa [Pi.neg_apply] using hΦ x


-- @@ L112-117 verbatim
/-- The normalized DFT has square `id` on the even submodule. -/
theorem normalizedDftEven_sq :
    (normalizedDftEven (p := p)).comp (normalizedDftEven (p := p)) =
      (LinearMap.id : evenSubmodule (p := p) →ₗ[ℂ] evenSubmodule (p := p)) := by
  ext Φ x
  exact congrFun (normalizedDft_sq_eq_self_of_even (p := p) Φ.2) x


-- @@ L119-124 verbatim
/-- The normalized DFT has square `-id` on the odd submodule. -/
theorem normalizedDftOdd_sq :
    (normalizedDftOdd (p := p)).comp (normalizedDftOdd (p := p)) =
      -(LinearMap.id : oddSubmodule (p := p) →ₗ[ℂ] oddSubmodule (p := p)) := by
  ext Φ x
  exact congrFun (normalizedDft_sq_eq_neg_self_of_odd (p := p) Φ.2) x


-- @@ L126-128 verbatim
/-- The raw Fourier kernel matrix for `ZMod.dft` in the standard basis. -/
noncomputable def fourierMatrix : Matrix (ZMod p) (ZMod p) ℂ :=
  Matrix.of fun x k ↦ ZMod.stdAddChar (N := p) (-(x * k))


-- @@ L130-132 verbatim
/-- The normalized Fourier matrix, i.e. the matrix of `normalizedDft`. -/
noncomputable def normalizedFourierMatrix : Matrix (ZMod p) (ZMod p) ℂ :=
  Matrix.of fun x k ↦ (Real.sqrt p : ℂ)⁻¹ * ZMod.stdAddChar (N := p) (-(x * k))


-- @@ L134-137 verbatim
theorem normalizedFourierMatrix_eq_smul_fourierMatrix :
    normalizedFourierMatrix p = ((Real.sqrt p : ℂ)⁻¹) • fourierMatrix p := by
  ext x k
  simp [normalizedFourierMatrix, fourierMatrix, smul_eq_mul]


-- @@ L139-147 verbatim
/-- Matrix form of the unnormalized DFT in the standard basis. -/
theorem toMatrix_dft_eq_fourierMatrix :
    LinearMap.toMatrix (Pi.basisFun ℂ (ZMod p)) (Pi.basisFun ℂ (ZMod p))
        ((ZMod.dft : (ZMod p → ℂ) ≃ₗ[ℂ] (ZMod p → ℂ)).toLinearMap) =
      fourierMatrix p := by
  ext x k
  rw [LinearMap.toMatrix_apply, Pi.basisFun_repr]
  simpa [fourierMatrix, mul_comm] using
    (dft_basisFun_apply (p := p) (x := k) (k := x))


-- @@ L149-159 verbatim
/-- Matrix form of the normalized DFT in the standard basis. -/
theorem toMatrix_normalizedDft_eq_normalizedFourierMatrix :
    LinearMap.toMatrix (Pi.basisFun ℂ (ZMod p)) (Pi.basisFun ℂ (ZMod p))
        (normalizedDft p) =
      normalizedFourierMatrix p := by
  ext x k
  rw [LinearMap.toMatrix_apply, Pi.basisFun_repr]
  rw [normalizedDft_apply]
  simpa [normalizedFourierMatrix, mul_comm] using
    congrArg (fun z : ℂ ↦ (Real.sqrt p : ℂ)⁻¹ * z)
      (dft_basisFun_apply (p := p) (x := k) (k := x))


-- @@ L161-165 verbatim
/-- Determinant reduction from `normalizedDft` to its explicit Fourier matrix. -/
theorem det_normalizedDft_eq_det_normalizedFourierMatrix :
    LinearMap.det (normalizedDft p) = Matrix.det (normalizedFourierMatrix p) := by
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℂ (ZMod p)) (normalizedDft p),
    toMatrix_normalizedDft_eq_normalizedFourierMatrix]


-- @@ L167-171 verbatim
/-- A fixed equivalence used to reindex `ZMod p` by `Fin p` for matrix
determinant computations. -/
noncomputable def zmodEquivFin : ZMod p ≃ Fin p :=
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  (ZMod.finEquiv p).symm.toEquiv


-- @@ L173-183 verbatim
theorem zmodEquivFin_symm_apply (i : Fin p) :
    (zmodEquivFin (p := p)).symm i = (i : ZMod p) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  change ZMod.finEquiv p i = (i : ZMod p)
  cases p with
  | zero =>
      exact (hp.out.ne_zero rfl).elim
  | succ n =>
      have hrefl : ZMod.finEquiv (n + 1) i = i := rfl
      rw [hrefl]
      exact (Fin.cast_val_eq_self i).symm


-- @@ L185-187 verbatim
/-- The normalized Fourier matrix reindexed by `Fin p`. -/
noncomputable def normalizedFourierMatrixFin : Matrix (Fin p) (Fin p) ℂ :=
  Matrix.reindex (zmodEquivFin (p := p)) (zmodEquivFin (p := p)) (normalizedFourierMatrix p)


-- @@ L189-191 verbatim
/-- The raw Fourier matrix reindexed by `Fin p`. -/
noncomputable def fourierMatrixFin : Matrix (Fin p) (Fin p) ℂ :=
  Matrix.reindex (zmodEquivFin (p := p)) (zmodEquivFin (p := p)) (fourierMatrix p)


-- @@ L193-196 verbatim
theorem normalizedFourierMatrixFin_eq_smul_fourierMatrixFin :
    normalizedFourierMatrixFin p = ((Real.sqrt p : ℂ)⁻¹) • fourierMatrixFin p := by
  ext i j
  simp [normalizedFourierMatrixFin, fourierMatrixFin, normalizedFourierMatrix_eq_smul_fourierMatrix]


-- @@ L198-203 verbatim
/-- Reindexing does not change the determinant, so the `Fin p` model is a clean
stand-in for the original normalized Fourier matrix. -/
theorem det_normalizedFourierMatrix_eq_det_normalizedFourierMatrixFin :
    Matrix.det (normalizedFourierMatrix p) = Matrix.det (normalizedFourierMatrixFin p) := by
  rw [normalizedFourierMatrixFin,
    Matrix.det_reindex_self (zmodEquivFin (p := p)) (normalizedFourierMatrix p)]


-- @@ L205-205 verbatim
end SignInvariant


-- @@ L207-207 verbatim
end BernoulliRegular

