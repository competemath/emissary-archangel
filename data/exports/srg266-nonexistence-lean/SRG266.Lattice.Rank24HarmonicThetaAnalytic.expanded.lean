/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.HarmonicThetaSeries
import SRG266.Lattice.LatticeHarmonicGaussianPoisson
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule


-- @@ L11-11 verbatim
noncomputable section


-- @@ L13-13 verbatim
namespace SRG266.Lattice


-- @@ L15-15 verbatim
open Complex Filter Function ModularGroup ModularForm UpperHalfPlane

-- @@ L16-16 verbatim
open scoped BigOperators Manifold MatrixGroups RealInnerProductSpace Topology


-- @@ L18-18 verbatim
local notation "𝕢" => Function.Periodic.qParam


-- @@ L20-22 verbatim
def pdLatticePoint (N : PDUnimodularLattice 24) (z : Fin 24 → ℤ) :
    EuclideanSpace ℝ (Fin 24) :=
  pdEuclideanEquiv N (intVectorToReal z)


-- @@ L24-26 verbatim
def pdCarrierPoint (N : PDUnimodularLattice 24) (x : N.carrier) :
    EuclideanSpace ℝ (Fin 24) :=
  pdLatticePoint N ((pdFinBasis N).equivFun x)


-- @@ L28-32 verbatim
@[simp]
theorem pdCoordEquiv_finBasis_equivFun
    (N : PDUnimodularLattice 24) (x : N.carrier) :
    pdCoordEquiv N ((pdFinBasis N).equivFun x) = x := by
  exact (pdFinBasis N).equivFun.symm_apply_apply x


-- @@ L34-41 verbatim
@[simp]
theorem inner_pdCarrierPoint (N : PDUnimodularLattice 24)
    (x y : N.carrier) :
    inner ℝ (pdCarrierPoint N x) (pdCarrierPoint N y) =
      (N.pairing x y : ℝ) := by
  unfold pdCarrierPoint pdLatticePoint
  rw [inner_pdEuclideanEquiv_intVector,
    pdCoordEquiv_finBasis_equivFun, pdCoordEquiv_finBasis_equivFun]


-- @@ L43-49 verbatim
@[simp]
theorem norm_sq_pdCarrierPoint (N : PDUnimodularLattice 24)
    (x : N.carrier) :
    ‖pdCarrierPoint N x‖ ^ 2 = (N.pairing x x : ℝ) := by
  unfold pdCarrierPoint pdLatticePoint
  rw [norm_sq_pdEuclideanEquiv_intVector,
    pdCoordEquiv_finBasis_equivFun]


-- @@ L51-58 verbatim
theorem harmonicQuadratic_pdCarrierPoint
    (N : PDUnimodularLattice 24) (x y v : N.carrier) :
    harmonicQuadratic (pdCarrierPoint N x) (pdCarrierPoint N y)
        (pdCarrierPoint N v) =
      (24 * N.pairing v x * N.pairing v y -
        N.pairing x y * N.pairing v v : ℤ) := by
  simp only [harmonicQuadratic, inner_pdCarrierPoint]
  norm_num


-- @@ L60-63 verbatim
def evenNormIndex (N : PDUnimodularLattice 24)
    (_heven : ∀ z : N.carrier, Even (N.pairing z z))
    (z : Fin 24 → ℤ) : ℕ :=
  Int.toNat (N.pairing (pdCoordEquiv N z) (pdCoordEquiv N z) / 2)


-- @@ L65-74 verbatim
theorem pairing_pdCoordEquiv_eq_two_evenNormIndex
    (N : PDUnimodularLattice 24)
    (heven : ∀ z : N.carrier, Even (N.pairing z z))
    (z : Fin 24 → ℤ) :
    N.pairing (pdCoordEquiv N z) (pdCoordEquiv N z) =
      2 * evenNormIndex N heven z := by
  have hnonneg := pairing_self_nonneg N (pdCoordEquiv N z)
  obtain ⟨a, ha⟩ := heven (pdCoordEquiv N z)
  simp only [evenNormIndex]
  omega


-- @@ L76-97 verbatim
def evenNormFiberEquiv (N : PDUnimodularLattice 24)
    (heven : ∀ z : N.carrier, Even (N.pairing z z)) (k : ℕ) :
    {z : Fin 24 → ℤ //
      z ∈ evenNormIndex N heven ⁻¹' ({k} : Set ℕ)} ≃ NormShell N (2 * k) where
  toFun z := ⟨pdCoordEquiv N z.1, by
    have hz : evenNormIndex N heven z.1 = k := by
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using z.2
    rw [pairing_pdCoordEquiv_eq_two_evenNormIndex N heven z.1, hz]
    norm_num⟩
  invFun v := ⟨(pdFinBasis N).equivFun v.1, by
    change evenNormIndex N heven ((pdFinBasis N).equivFun v.1) = k
    have h := pairing_pdCoordEquiv_eq_two_evenNormIndex
      N heven ((pdFinBasis N).equivFun v.1)
    rw [pdCoordEquiv_finBasis_equivFun, v.2] at h
    omega⟩
  left_inv z := by
    apply Subtype.ext
    change (pdFinBasis N).equivFun (pdCoordEquiv N z.1) = z.1
    exact (pdFinBasis N).equivFun.apply_symm_apply z.1
  right_inv v := by
    apply Subtype.ext
    exact pdCoordEquiv_finBasis_equivFun N v.1


-- @@ L99-104 verbatim
@[simp]
theorem pdCarrierPoint_pdCoordEquiv
    (N : PDUnimodularLattice 24) (z : Fin 24 → ℤ) :
    pdCarrierPoint N (pdCoordEquiv N z) = pdLatticePoint N z := by
  unfold pdCarrierPoint pdLatticePoint pdCoordEquiv
  rw [(pdFinBasis N).equivFun.apply_symm_apply]


-- @@ L106-116 verbatim
theorem harmonicQuadratic_pdLatticePoint
    (N : PDUnimodularLattice 24) (x y : N.carrier)
    (z : Fin 24 → ℤ) :
    harmonicQuadratic (pdCarrierPoint N x) (pdCarrierPoint N y)
        (pdLatticePoint N z) =
      (24 * N.pairing (pdCoordEquiv N z) x *
          N.pairing (pdCoordEquiv N z) y -
        N.pairing x y *
          N.pairing (pdCoordEquiv N z) (pdCoordEquiv N z) : ℤ) := by
  rw [← pdCarrierPoint_pdCoordEquiv]
  exact harmonicQuadratic_pdCarrierPoint N x y (pdCoordEquiv N z)


-- @@ L118-159 verbatim
theorem tsum_evenNormFiber_harmonicQuadratic
    (N : PDUnimodularLattice 24)
    (heven : ∀ z : N.carrier, Even (N.pairing z z))
    (x y : N.carrier) (q : ℂ) (k : ℕ) :
    (∑' z : {z : Fin 24 → ℤ //
        z ∈ evenNormIndex N heven ⁻¹' ({k} : Set ℕ)},
      (harmonicQuadratic (pdCarrierPoint N x) (pdCarrierPoint N y)
        (pdLatticePoint N z.1) : ℂ) *
          q ^ evenNormIndex N heven z.1) =
      (harmonicThetaCoefficient N x y k : ℂ) * q ^ k := by
  let e := evenNormFiberEquiv N heven k
  let g : {z : Fin 24 → ℤ //
      z ∈ evenNormIndex N heven ⁻¹' ({k} : Set ℕ)} → ℂ := fun z =>
    (harmonicQuadratic (pdCarrierPoint N x) (pdCarrierPoint N y)
      (pdLatticePoint N z.1) : ℂ) * q ^ evenNormIndex N heven z.1
  calc
    (∑' z : {z : Fin 24 → ℤ //
        z ∈ evenNormIndex N heven ⁻¹' ({k} : Set ℕ)}, g z) =
        ∑' v : NormShell N (2 * k), g (e.symm v) := by
      simpa [e, g] using
        e.tsum_eq (fun v : NormShell N (2 * k) => g (e.symm v))
    _ = (harmonicThetaCoefficient N x y k : ℂ) * q ^ k := by
      rw [tsum_fintype]
      simp only [harmonicThetaCoefficient, Int.cast_sum, g]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro v _
      change
        (harmonicQuadratic (pdCarrierPoint N x) (pdCarrierPoint N y)
          (pdLatticePoint N ((pdFinBasis N).equivFun v.1)) : ℂ) *
            q ^ evenNormIndex N heven ((pdFinBasis N).equivFun v.1) =
          ((24 * N.pairing v.1 x * N.pairing v.1 y -
            N.pairing x y * N.pairing v.1 v.1 : ℤ) : ℂ) * q ^ k
      rw [harmonicQuadratic_pdLatticePoint]
      simp only [pdCoordEquiv_finBasis_equivFun, Int.cast_sub, Int.cast_mul]
      have hindex : evenNormIndex N heven ((pdFinBasis N).equivFun v.1) = k := by
        have h := pairing_pdCoordEquiv_eq_two_evenNormIndex
          N heven ((pdFinBasis N).equivFun v.1)
        rw [pdCoordEquiv_finBasis_equivFun, v.2] at h
        omega
      rw [hindex]
      norm_cast


-- @@ L161-185 verbatim
theorem norm_harmonicTheta_coordinate_term
    (N : PDUnimodularLattice 24)
    (heven : ∀ z : N.carrier, Even (N.pairing z z))
    (x y : N.carrier) (τ : ℍ) (z : Fin 24 → ℤ) :
    ‖(harmonicQuadratic (pdCarrierPoint N x) (pdCarrierPoint N y)
        (pdLatticePoint N z) : ℂ) *
      𝕢 1 τ ^ evenNormIndex N heven z‖ =
    ‖harmonicGaussian τ.im (pdCarrierPoint N x) (pdCarrierPoint N y)
      (pdLatticePoint N z)‖ := by
  rw [norm_mul, norm_pow, Function.Periodic.norm_qParam,
    div_one, harmonicGaussian, realGaussian, norm_mul, Complex.norm_exp]
  have hre :
      (-((Real.pi * τ.im : ℝ) : ℂ) *
        (‖pdLatticePoint N z‖ : ℂ) ^ 2).re =
        -(Real.pi * τ.im) * ‖pdLatticePoint N z‖ ^ 2 := by
    norm_cast
  rw [hre, ← Real.exp_nat_mul]
  congr 1
  rw [show ‖pdLatticePoint N z‖ ^ 2 =
      (N.pairing (pdCoordEquiv N z) (pdCoordEquiv N z) : ℝ) by
    simpa [pdLatticePoint] using norm_sq_pdEuclideanEquiv_intVector N z]
  rw [pairing_pdCoordEquiv_eq_two_evenNormIndex N heven z]
  push_cast
  simp only [UpperHalfPlane.coe_im]
  ring_nf


-- @@ L187-200 verbatim
theorem summable_harmonicTheta_coordinate_term
    (N : PDUnimodularLattice 24)
    (heven : ∀ z : N.carrier, Even (N.pairing z z))
    (x y : N.carrier) (τ : ℍ) :
    Summable fun z : Fin 24 → ℤ =>
      (harmonicQuadratic (pdCarrierPoint N x) (pdCarrierPoint N y)
        (pdLatticePoint N z) : ℂ) *
          𝕢 1 τ ^ evenNormIndex N heven z := by
  rw [← summable_norm_iff]
  exact (summable_harmonicGaussian_pdEuclideanEquiv_intVector
    N τ.im_pos (pdCarrierPoint N x) (pdCarrierPoint N y)).norm.congr
      (fun z => by
        simpa [pdLatticePoint] using
          (norm_harmonicTheta_coordinate_term N heven x y τ z).symm)


-- @@ L202-230 verbatim
theorem hasSum_harmonicTheta_coefficients
    (N : PDUnimodularLattice 24)
    (heven : ∀ z : N.carrier, Even (N.pairing z z))
    (x y : N.carrier) (τ : ℍ) :
    HasSum (fun k : ℕ =>
      (harmonicThetaCoefficient N x y k : ℂ) * 𝕢 1 τ ^ k)
      (∑' z : Fin 24 → ℤ,
        (harmonicQuadratic (pdCarrierPoint N x) (pdCarrierPoint N y)
          (pdLatticePoint N z) : ℂ) *
            𝕢 1 τ ^ evenNormIndex N heven z) := by
  let g : (Fin 24 → ℤ) → ℂ := fun z =>
    (harmonicQuadratic (pdCarrierPoint N x) (pdCarrierPoint N y)
      (pdLatticePoint N z) : ℂ) *
        𝕢 1 τ ^ evenNormIndex N heven z
  have hsum : Summable g :=
    summable_harmonicTheta_coordinate_term N heven x y τ
  have hfiber := hsum.hasSum.tsum_fiberwise (evenNormIndex N heven)
  have hfun :
      (fun k : ℕ =>
        (harmonicThetaCoefficient N x y k : ℂ) * 𝕢 1 τ ^ k) =
      (fun k : ℕ =>
        ∑' z : {z : Fin 24 → ℤ //
          z ∈ evenNormIndex N heven ⁻¹' ({k} : Set ℕ)}, g z) := by
    funext k
    simpa only [g] using
      (tsum_evenNormFiber_harmonicQuadratic
        N heven x y (𝕢 1 τ) k).symm
  rw [hfun]
  simpa only [g, Set.mem_preimage, Set.mem_singleton_iff] using hfiber


-- @@ L232-234 verbatim
def harmonicThetaFunction
    (N : PDUnimodularLattice 24) (x y : N.carrier) (τ : ℍ) : ℂ :=
  ∑' k : ℕ, (harmonicThetaCoefficient N x y k : ℂ) * 𝕢 1 τ ^ k


-- @@ L236-242 verbatim
theorem summable_harmonicTheta_coefficients
    (N : PDUnimodularLattice 24)
    (heven : ∀ z : N.carrier, Even (N.pairing z z))
    (x y : N.carrier) (τ : ℍ) :
    Summable fun k : ℕ =>
      (harmonicThetaCoefficient N x y k : ℂ) * 𝕢 1 τ ^ k :=
  (hasSum_harmonicTheta_coefficients N heven x y τ).summable


-- @@ L244-253 verbatim
theorem harmonicThetaFunction_eq_coordinate_tsum
    (N : PDUnimodularLattice 24)
    (heven : ∀ z : N.carrier, Even (N.pairing z z))
    (x y : N.carrier) (τ : ℍ) :
    harmonicThetaFunction N x y τ =
      ∑' z : Fin 24 → ℤ,
        (harmonicQuadratic (pdCarrierPoint N x) (pdCarrierPoint N y)
          (pdLatticePoint N z) : ℂ) *
            𝕢 1 τ ^ evenNormIndex N heven z := by
  exact (hasSum_harmonicTheta_coefficients N heven x y τ).tsum_eq


-- @@ L255-259 verbatim
def harmonicThetaFSeries
    (N : PDUnimodularLattice 24) (x y : N.carrier) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ fun k =>
    (harmonicThetaCoefficient N x y k : ℂ)


-- @@ L261-276 verbatim
theorem summable_harmonicTheta_coeff_mul_pow_of_norm_lt_one
    (N : PDUnimodularLattice 24)
    (heven : ∀ z : N.carrier, Even (N.pairing z z))
    (x y : N.carrier) {q : ℂ} (hq : ‖q‖ < 1) :
    Summable fun k : ℕ =>
      (harmonicThetaCoefficient N x y k : ℂ) * q ^ k := by
  by_cases hq0 : q = 0
  · subst q
    simpa +contextual [zero_pow_eq] using
      (hasSum_ite_eq 0 (harmonicThetaCoefficient N x y 0 : ℂ)).summable
  · let τ : ℍ := ⟨Function.Periodic.invQParam 1 q,
      Function.Periodic.im_invQParam_pos_of_norm_lt_one one_pos hq hq0⟩
    have hparam : 𝕢 1 (τ : ℂ) = q :=
      Function.Periodic.qParam_right_inv one_ne_zero hq0
    simpa only [hparam] using
      summable_harmonicTheta_coefficients N heven x y τ


-- @@ L278-289 verbatim
theorem harmonicThetaFSeries_one_le_radius
    (N : PDUnimodularLattice 24)
    (heven : ∀ z : N.carrier, Even (N.pairing z z))
    (x y : N.carrier) :
    1 ≤ (harmonicThetaFSeries N x y).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  have hs := (summable_harmonicTheta_coeff_mul_pow_of_norm_lt_one
    N heven x y (q := (r : ℂ)) (by simpa using hr)).norm
  simpa only [harmonicThetaFSeries, FormalMultilinearSeries.ofScalars_norm,
    norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg r.2,
    NNReal.norm_eq] using hs


-- @@ L291-297 verbatim
theorem harmonicThetaFunction_eq_fseriesSum
    (N : PDUnimodularLattice 24) (x y : N.carrier) (τ : ℍ) :
    harmonicThetaFunction N x y τ =
      (harmonicThetaFSeries N x y).sum (𝕢 1 τ) := by
  simp only [harmonicThetaFunction, harmonicThetaFSeries,
    FormalMultilinearSeries.sum, FormalMultilinearSeries.ofScalars_apply_eq,
    smul_eq_mul]


-- @@ L299-325 verbatim
theorem harmonicThetaFunction_mdifferentiable
    (N : PDUnimodularLattice 24)
    (heven : ∀ z : N.carrier, Even (N.pairing z z))
    (x y : N.carrier) :
    MDiff (harmonicThetaFunction N x y) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro z hz
  let p := harmonicThetaFSeries N x y
  have hq : ‖𝕢 1 z‖ < 1 :=
    Function.Periodic.norm_qParam_lt_one one_pos hz
  have hmem : 𝕢 1 z ∈ Metric.eball 0 p.radius := by
    apply mem_eball_zero_iff.2
    have hq' : (↑‖𝕢 1 z‖₊ : ENNReal) < 1 := by
      exact_mod_cast hq
    exact lt_of_lt_of_le (by simpa only [enorm_eq_nnnorm] using hq')
      (harmonicThetaFSeries_one_le_radius N heven x y)
  have hp : AnalyticAt ℂ p.sum (𝕢 1 z) :=
    p.analyticOnNhd _ hmem
  have hcomp : DifferentiableAt ℂ (fun w : ℂ => p.sum (𝕢 1 w)) z :=
    hp.differentiableAt.comp z (by
      unfold Function.Periodic.qParam
      fun_prop)
  apply DifferentiableAt.differentiableWithinAt
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hz] with w hw
  simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hw]
  rw [harmonicThetaFunction_eq_fseriesSum]


-- @@ L327-335 verbatim
theorem hasSum_harmonicThetaFunction
    (N : PDUnimodularLattice 24)
    (heven : ∀ z : N.carrier, Even (N.pairing z z))
    (x y : N.carrier) (τ : ℍ) :
    HasSum (fun k : ℕ =>
      (harmonicThetaCoefficient N x y k : ℂ) • 𝕢 1 τ ^ k)
      (harmonicThetaFunction N x y τ) := by
  simpa only [smul_eq_mul, harmonicThetaFunction] using
    (summable_harmonicTheta_coefficients N heven x y τ).hasSum


-- @@ L337-343 verbatim
theorem harmonicThetaFunction_isBoundedAtImInfty
    (N : PDUnimodularLattice 24)
    (heven : ∀ z : N.carrier, Even (N.pairing z z))
    (x y : N.carrier) :
    IsBoundedAtImInfty (harmonicThetaFunction N x y) :=
  UpperHalfPlane.isBoundedAtImInfty_of_hasSum_qExpansion one_pos
    (hasSum_harmonicThetaFunction N heven x y)


-- @@ L345-358 verbatim
theorem harmonicThetaCoefficient_zero
    (N : PDUnimodularLattice 24) (x y : N.carrier) :
    harmonicThetaCoefficient N x y 0 = 0 := by
  classical
  unfold harmonicThetaCoefficient
  apply Finset.sum_eq_zero
  intro v _
  have hv : v.1 = 0 := by
    by_contra hv0
    have hpos := N.positiveDefinite v.1 hv0
    rw [v.2] at hpos
    norm_num at hpos
  rw [hv]
  simp


-- @@ L360-370 verbatim
theorem qExpansion_eq_harmonicThetaSeries
    (N : PDUnimodularLattice 24)
    (heven : ∀ z : N.carrier, Even (N.pairing z z))
    (x y : N.carrier) (f : ModularForm 𝒮ℒ 14)
    (hf : ∀ τ, f τ = harmonicThetaFunction N x y τ) :
    qExpansion 1 f = harmonicThetaSeries N x y := by
  ext k
  rw [harmonicThetaSeries_coeff]
  exact (ModularFormClass.qExpansion_coeff_unique
    (f := f) one_pos one_mem_strictPeriods_SL (fun τ => by
      simpa only [hf τ] using hasSum_harmonicThetaFunction N heven x y τ) k).symm


-- @@ L372-373 verbatim
def positiveImaginaryPoint (t : ℝ) (ht : 0 < t) : ℍ :=
  ⟨(t : ℂ) * Complex.I, by simpa using ht⟩


-- @@ L375-377 verbatim
@[simp]
theorem positiveImaginaryPoint_coe (t : ℝ) (ht : 0 < t) :
    ((positiveImaginaryPoint t ht : ℍ) : ℂ) = (t : ℂ) * Complex.I := rfl


-- @@ L379-402 verbatim
theorem harmonicTheta_coordinate_term_positiveImaginary
    (N : PDUnimodularLattice 24)
    (heven : ∀ z : N.carrier, Even (N.pairing z z))
    (x y : N.carrier) {t : ℝ} (ht : 0 < t) (z : Fin 24 → ℤ) :
    (harmonicQuadratic (pdCarrierPoint N x) (pdCarrierPoint N y)
        (pdLatticePoint N z) : ℂ) *
      𝕢 1 (positiveImaginaryPoint t ht) ^ evenNormIndex N heven z =
    harmonicGaussian t (pdCarrierPoint N x) (pdCarrierPoint N y)
      (pdLatticePoint N z) := by
  unfold harmonicGaussian realGaussian Function.Periodic.qParam
  rw [positiveImaginaryPoint_coe]
  norm_num only [ofReal_one, div_one]
  rw [← Complex.exp_nat_mul]
  congr 1
  rw [← ofReal_pow]
  rw [show ‖pdLatticePoint N z‖ ^ 2 =
      (N.pairing (pdCoordEquiv N z) (pdCoordEquiv N z) : ℝ) by
    simpa [pdLatticePoint] using norm_sq_pdEuclideanEquiv_intVector N z]
  rw [pairing_pdCoordEquiv_eq_two_evenNormIndex N heven z]
  push_cast
  congr 1
  ring_nf
  rw [Complex.I_sq]
  ring


-- @@ L404-414 verbatim
theorem harmonicThetaFunction_positiveImaginary_eq_gaussian_tsum
    (N : PDUnimodularLattice 24)
    (heven : ∀ z : N.carrier, Even (N.pairing z z))
    (x y : N.carrier) {t : ℝ} (ht : 0 < t) :
    harmonicThetaFunction N x y (positiveImaginaryPoint t ht) =
      ∑' z : Fin 24 → ℤ,
        harmonicGaussian t (pdCarrierPoint N x) (pdCarrierPoint N y)
          (pdLatticePoint N z) := by
  rw [harmonicThetaFunction_eq_coordinate_tsum N heven]
  apply tsum_congr
  exact harmonicTheta_coordinate_term_positiveImaginary N heven x y ht


-- @@ L416-430 verbatim
theorem harmonicThetaFunction_poisson_positiveImaginary
    (N : PDUnimodularLattice 24)
    (heven : ∀ z : N.carrier, Even (N.pairing z z))
    (x y : N.carrier) {t : ℝ} (ht : 0 < t) :
    harmonicThetaFunction N x y (positiveImaginaryPoint t ht) =
      -((t : ℂ)⁻¹) ^ 14 *
        harmonicThetaFunction N x y
          (positiveImaginaryPoint t⁻¹ (inv_pos.mpr ht)) := by
  rw [harmonicThetaFunction_positiveImaginary_eq_gaussian_tsum
      N heven x y ht,
    harmonicThetaFunction_positiveImaginary_eq_gaussian_tsum
      N heven x y (inv_pos.mpr ht)]
  simpa only [pdLatticePoint] using
    harmonicGaussian_latticePoisson_rank24
      N ht (pdCarrierPoint N x) (pdCarrierPoint N y)


-- @@ L432-443 verbatim
theorem modular_S_smul_positiveImaginaryPoint
    {t : ℝ} (ht : 0 < t) :
    ModularGroup.S • positiveImaginaryPoint t ht =
      positiveImaginaryPoint t⁻¹ (inv_pos.mpr ht) := by
  apply UpperHalfPlane.coe_injective
  rw [UpperHalfPlane.modular_S_smul]
  simp only [positiveImaginaryPoint_coe]
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  field_simp
  rw [Complex.I_sq]
  push_cast
  field_simp


-- @@ L445-478 verbatim
theorem harmonicThetaFunction_S_positiveImaginary
    (N : PDUnimodularLattice 24)
    (heven : ∀ z : N.carrier, Even (N.pairing z z))
    (x y : N.carrier) {t : ℝ} (ht : 0 < t) :
    harmonicThetaFunction N x y
        (ModularGroup.S • positiveImaginaryPoint t ht) =
      ((positiveImaginaryPoint t ht : ℂ) ^ 14) *
        harmonicThetaFunction N x y (positiveImaginaryPoint t ht) := by
  rw [modular_S_smul_positiveImaginaryPoint ht]
  have hp := harmonicThetaFunction_poisson_positiveImaginary
    N heven x y ht
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  calc
    harmonicThetaFunction N x y
        (positiveImaginaryPoint t⁻¹ (inv_pos.mpr ht)) =
      -(t : ℂ) ^ 14 * harmonicThetaFunction N x y
        (positiveImaginaryPoint t ht) := by
          calc
            _ = -(t : ℂ) ^ 14 *
                (-((t : ℂ)⁻¹) ^ 14 *
                  harmonicThetaFunction N x y
                    (positiveImaginaryPoint t⁻¹ (inv_pos.mpr ht))) := by
                field_simp
            _ = -(t : ℂ) ^ 14 *
                harmonicThetaFunction N x y
                  (positiveImaginaryPoint t ht) := by rw [hp]
    _ = ((positiveImaginaryPoint t ht : ℂ) ^ 14) *
        harmonicThetaFunction N x y (positiveImaginaryPoint t ht) := by
      rw [positiveImaginaryPoint_coe, mul_pow]
      have hI14 : Complex.I ^ 14 = -1 := by
        rw [show 14 = 2 * 7 by norm_num, pow_mul, Complex.I_sq]
        norm_num
      rw [hI14]
      ring


-- @@ L480-483 verbatim
def harmonicThetaSDefect
    (N : PDUnimodularLattice 24) (x y : N.carrier) : ℍ → ℂ := fun τ =>
  harmonicThetaFunction N x y (ModularGroup.S • τ) -
    (τ : ℂ) ^ 14 * harmonicThetaFunction N x y τ


-- @@ L485-494 verbatim
theorem harmonicThetaSDefect_mdifferentiable
    (N : PDUnimodularLattice 24)
    (heven : ∀ z : N.carrier, Even (N.pairing z z))
    (x y : N.carrier) :
    MDiff (harmonicThetaSDefect N x y) := by
  have hθ := harmonicThetaFunction_mdifferentiable N heven x y
  have hSdet : 0 < ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ).det.val := by
    norm_num [ModularGroup.S]
  exact (hθ.comp (UpperHalfPlane.mdifferentiable_smul hSdet)).sub
    ((UpperHalfPlane.mdifferentiable_coe.pow 14).mul hθ)


-- @@ L496-497 verbatim
def harmonicThetaIdentitySequence (n : ℕ) : ℍ :=
  positiveImaginaryPoint (1 + 1 / ((n : ℝ) + 1)) (by positivity)


-- @@ L499-513 verbatim
theorem harmonicThetaIdentitySequence_tendsto :
    Tendsto harmonicThetaIdentitySequence atTop (nhds UpperHalfPlane.I) := by
  rw [UpperHalfPlane.isOpenEmbedding_coe.tendsto_nhds_iff,
    Function.comp_def]
  have hr : Tendsto (fun n : ℕ => (1 + 1 / ((n : ℝ) + 1) : ℝ))
      atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hc : Tendsto
      (fun n : ℕ => ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I)
      atTop (nhds ((1 : ℂ) * Complex.I)) :=
    (Complex.continuous_ofReal.continuousAt.tendsto.comp hr).mul
      tendsto_const_nhds
  simpa only [harmonicThetaIdentitySequence, positiveImaginaryPoint_coe,
    one_mul, UpperHalfPlane.coe_I] using hc


-- @@ L515-525 verbatim
theorem harmonicThetaIdentitySequence_ne_I (n : ℕ) :
    harmonicThetaIdentitySequence n ≠ UpperHalfPlane.I := by
  intro h
  have hcoe := congrArg ((↑) : ℍ → ℂ) h
  have him : 1 + 1 / ((n : ℝ) + 1) = 1 := by
    simpa only [harmonicThetaIdentitySequence, positiveImaginaryPoint_coe,
      UpperHalfPlane.coe_I, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re,
      mul_zero, sub_zero, add_zero] using congrArg Complex.im hcoe
  have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
  linarith


-- @@ L527-532 verbatim
theorem harmonicThetaIdentitySequence_tendsto_punctured :
    Tendsto harmonicThetaIdentitySequence atTop
      (nhdsWithin UpperHalfPlane.I {UpperHalfPlane.I}ᶜ) := by
  apply tendsto_nhdsWithin_iff.mpr
  exact ⟨harmonicThetaIdentitySequence_tendsto,
    Filter.Eventually.of_forall harmonicThetaIdentitySequence_ne_I⟩


-- @@ L534-541 verbatim
theorem harmonicThetaSDefect_identitySequence_eq_zero
    (N : PDUnimodularLattice 24)
    (heven : ∀ z : N.carrier, Even (N.pairing z z))
    (x y : N.carrier) (n : ℕ) :
    harmonicThetaSDefect N x y (harmonicThetaIdentitySequence n) = 0 := by
  unfold harmonicThetaSDefect harmonicThetaIdentitySequence
  rw [harmonicThetaFunction_S_positiveImaginary N heven]
  ring


-- @@ L543-556 verbatim
theorem harmonicThetaFunction_S
    (N : PDUnimodularLattice 24)
    (heven : ∀ z : N.carrier, Even (N.pairing z z))
    (x y : N.carrier) (τ : ℍ) :
    harmonicThetaFunction N x y (ModularGroup.S • τ) =
      (τ : ℂ) ^ 14 * harmonicThetaFunction N x y τ := by
  have hzero : harmonicThetaSDefect N x y = 0 :=
    UpperHalfPlane.eq_zero_of_frequently
      (harmonicThetaSDefect_mdifferentiable N heven x y)
      (harmonicThetaIdentitySequence_tendsto_punctured.frequently
        (Filter.Frequently.of_forall
          (harmonicThetaSDefect_identitySequence_eq_zero N heven x y)))
  have hpoint := congrFun hzero τ
  simpa only [harmonicThetaSDefect, Pi.zero_apply, sub_eq_zero] using hpoint


-- @@ L558-566 verbatim
theorem qParam_one_vadd (z : ℍ) :
    𝕢 1 ((1 : ℝ) +ᵥ z) = 𝕢 1 z := by
  unfold Function.Periodic.qParam
  rw [UpperHalfPlane.coe_vadd]
  norm_num only [ofReal_one, div_one]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * ((1 : ℂ) + z) =
      2 * (Real.pi : ℂ) * Complex.I * z + 2 * Real.pi * Complex.I by ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I]
  simp


-- @@ L568-575 verbatim
theorem harmonicThetaFunction_vadd_one
    (N : PDUnimodularLattice 24) (x y : N.carrier) (z : ℍ) :
    harmonicThetaFunction N x y ((1 : ℝ) +ᵥ z) =
      harmonicThetaFunction N x y z := by
  unfold harmonicThetaFunction
  apply tsum_congr
  intro k
  rw [qParam_one_vadd]


-- @@ L577-585 verbatim
theorem harmonicThetaFunction_T_invariant
    (N : PDUnimodularLattice 24) (x y : N.carrier) :
    harmonicThetaFunction N x y ∣[(14 : ℤ)] ModularGroup.T =
      harmonicThetaFunction N x y := by
  ext z
  rw [SL_slash_apply, UpperHalfPlane.denom,
    UpperHalfPlane.modular_T_smul, harmonicThetaFunction_vadd_one,
    ModularGroup.T]
  simp


-- @@ L587-603 verbatim
theorem harmonicThetaFunction_S_invariant
    (N : PDUnimodularLattice 24)
    (heven : ∀ z : N.carrier, Even (N.pairing z z))
    (x y : N.carrier) :
    harmonicThetaFunction N x y ∣[(14 : ℤ)] ModularGroup.S =
      harmonicThetaFunction N x y := by
  ext z
  rw [SlashInvariantForm.slash_S_apply]
  have htransform :
      harmonicThetaFunction N x y
          (.mk ((-z : ℂ)⁻¹) z.im_inv_neg_coe_pos) =
        (z : ℂ) ^ 14 * harmonicThetaFunction N x y z := by
    simpa only [UpperHalfPlane.modular_S_smul] using
      harmonicThetaFunction_S N heven x y z
  rw [htransform]
  simp only [Int.reduceNeg, zpow_neg, zpow_ofNat]
  field_simp [z.ne_zero]


-- @@ L605-623 verbatim
def harmonicThetaModularForm
    (N : PDUnimodularLattice 24)
    (heven : ∀ z : N.carrier, Even (N.pairing z z))
    (x y : N.carrier) : ModularForm 𝒮ℒ 14 where
  toFun := harmonicThetaFunction N x y
  slash_action_eq' γ hγ := by
    obtain ⟨γ, rfl⟩ := hγ
    exact SlashInvariantForm.slash_action_generators_SL2Z
      (harmonicThetaFunction_S_invariant N heven x y)
      (harmonicThetaFunction_T_invariant N x y) γ
  holo' := harmonicThetaFunction_mdifferentiable N heven x y
  bdd_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [SlashInvariantForm.slash_action_generators_SL2Z
      (harmonicThetaFunction_S_invariant N heven x y)
      (harmonicThetaFunction_T_invariant N x y) γ]
    exact harmonicThetaFunction_isBoundedAtImInfty N heven x y


-- @@ L625-631 verbatim
@[simp]
theorem harmonicThetaModularForm_apply
    (N : PDUnimodularLattice 24)
    (heven : ∀ z : N.carrier, Even (N.pairing z z))
    (x y : N.carrier) (τ : ℍ) :
    harmonicThetaModularForm N heven x y τ =
      harmonicThetaFunction N x y τ := rfl


-- @@ L633-640 verbatim
theorem harmonicThetaModularForm_qExpansion
    (N : PDUnimodularLattice 24)
    (heven : ∀ z : N.carrier, Even (N.pairing z z))
    (x y : N.carrier) :
    qExpansion 1 (harmonicThetaModularForm N heven x y) =
      harmonicThetaSeries N x y :=
  qExpansion_eq_harmonicThetaSeries N heven x y
    (harmonicThetaModularForm N heven x y) (fun _ => rfl)


-- @@ L642-649 verbatim
theorem harmonicThetaModularForm_coeff_zero
    (N : PDUnimodularLattice 24)
    (heven : ∀ z : N.carrier, Even (N.pairing z z))
    (x y : N.carrier) :
    (qExpansion 1 (harmonicThetaModularForm N heven x y)).coeff 0 = 0 := by
  rw [harmonicThetaModularForm_qExpansion, harmonicThetaSeries_coeff,
    harmonicThetaCoefficient_zero]
  norm_num


-- @@ L651-656 verbatim
def harmonicThetaCuspForm
    (N : PDUnimodularLattice 24)
    (heven : ∀ z : N.carrier, Even (N.pairing z z))
    (x y : N.carrier) : CuspForm 𝒮ℒ 14 :=
  ModularForm.toCuspForm (harmonicThetaModularForm N heven x y)
    (harmonicThetaModularForm_coeff_zero N heven x y)


-- @@ L658-664 verbatim
@[simp]
theorem harmonicThetaCuspForm_apply
    (N : PDUnimodularLattice 24)
    (heven : ∀ z : N.carrier, Even (N.pairing z z))
    (x y : N.carrier) (τ : ℍ) :
    harmonicThetaCuspForm N heven x y τ =
      harmonicThetaFunction N x y τ := rfl


-- @@ L666-673 verbatim
theorem harmonicThetaCuspForm_qExpansion
    (N : PDUnimodularLattice 24)
    (heven : ∀ z : N.carrier, Even (N.pairing z z))
    (x y : N.carrier) :
    qExpansion 1 (harmonicThetaCuspForm N heven x y) =
      harmonicThetaSeries N x y :=
  qExpansion_eq_harmonicThetaSeries N heven x y
    (harmonicThetaCuspForm N heven x y) (fun _ => rfl)


-- @@ L675-675 verbatim
end SRG266.Lattice
