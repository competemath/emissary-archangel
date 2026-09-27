/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Uniformization.SpecialPeriods5
import all LeanPool.HopfProblem.Foundations.Core1
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.PeriodFamily.PeriodPoint
import all LeanPool.HopfProblem.PeriodFamily.HolomorphicPeriodMap1
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods2
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods5


-- @@ L17-21 verbatim
/-!
# Hopf problem: period family · core 1

Supporting definitions and proofs for this stage of the six-sphere construction.
-/



-- @@ L24-24 verbatim
open Set Function Filter Manifold Topology


-- @@ L26-29 verbatim
open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane


-- @@ L31-31 verbatim
universe u v


-- @@ L33-33 verbatim
noncomputable section


-- @@ L35-35 verbatim
namespace Mathoverflow1973


-- @@ L37-37 verbatim
local infixr:80 " ≫ₚ " => Path.trans


-- @@ L39-39 verbatim
local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f


-- @@ L41-43 verbatim
private theorem PeriodPoint.discriminant_le_im_beta (p : PeriodPoint) (hτ : 0 < p.τ.im) :
    p.discriminant ≤ p.β.im := by
  exact sub_le_self _ (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hτ.le)


-- @@ L45-48 verbatim
private theorem
    PeriodPoint.discriminant_le_im_beta_add_tau_sub (p : PeriodPoint) (hτ : 0 < p.τ.im) :
    p.discriminant ≤ (p.β + p.τ).im - p.τ.im := by
  simpa only [Complex.add_im, add_sub_cancel_right] using p.discriminant_le_im_beta hτ


-- @@ L50-59 verbatim
private theorem
    PeriodPoint.tendsto_discriminant_atBot {X : Type*} {l : Filter X} (P : X → PeriodPoint)
    (hτ : ∀ᶠ z in l, 0 < (P z).τ.im) (hτinf : Filter.Tendsto (fun z => (P z).τ.im) l Filter.atTop)
    (hb : ∃ C : ℝ, ∀ᶠ z in l, ((P z).β + (P z).τ).im ≤ C) :
    Filter.Tendsto (fun z => (P z).discriminant) l Filter.atBot := by
  obtain ⟨C, hC⟩ := hb
  refine Filter.tendsto_atBot.mpr fun R => ?_
  filter_upwards [hτ, hC, hτinf.eventually_ge_atTop (C - R)] with z hzτ hzC hzR
  have hD := (P z).discriminant_le_im_beta_add_tau_sub hzτ
  linarith


-- @@ L61-68 verbatim
private theorem PeriodPoint.continuousOn_discriminant {X : Type*} [TopologicalSpace X]
    (P : X → PeriodPoint) {s : Set X} (hτ : ContinuousOn (fun z => (P z).τ) s)
    (hμ : ContinuousOn (fun z => (P z).μ) s) (hβ : ContinuousOn (fun z => (P z).β) s)
    (hτ₀ : ∀ z ∈ s, (P z).τ.im ≠ 0) : ContinuousOn (fun z => (P z).discriminant) s := by
  exact
    (Complex.continuous_im.comp_continuousOn hβ).sub
      ((continuousOn_const.mul ((Complex.continuous_im.comp_continuousOn hμ).pow 2)).div
        (Complex.continuous_im.comp_continuousOn hτ) hτ₀)


-- @@ L70-71 verbatim
private def PeriodPoint.shiftBeta (p : PeriodPoint) (c : ℂ) : PeriodPoint :=
  ⟨p.τ, p.μ, p.β + c⟩


-- @@ L73-77 verbatim
@[simp]
private theorem PeriodPoint.shiftBeta_discriminant (p : PeriodPoint) (c : ℂ) :
    (p.shiftBeta c).discriminant = p.discriminant + c.im := by
  simp only [discriminant, shiftBeta, Complex.add_im]
  ring


-- @@ L79-87 verbatim
private theorem PeriodPoint.exists_uniform_shift_of_bddAbove {X : Type*} (P : X → PeriodPoint)
    (hτ : ∀ z, 0 < (P z).τ.im) (hD : BddAbove (Set.range fun z => (P z).discriminant)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ c : ℂ, c.im < -M → ∀ z, ((P z).shiftBeta c).Admissible := by
  obtain ⟨C, hC⟩ := hD
  refine ⟨Max.max C 0, le_max_right _ _, fun c hc z => ⟨hτ z, ?_⟩⟩
  rw [shiftBeta_discriminant]
  have hDz : (P z).discriminant ≤ C := hC (Set.mem_range_self z)
  have hCM : C ≤ Max.max C 0 := le_max_left _ _
  linarith


-- @@ L89-97 verbatim
private theorem
    PeriodPoint.exists_negative_imaginary_shift_of_bddAbove {X : Type*} (P : X → PeriodPoint)
    (hτ : ∀ z, 0 < (P z).τ.im) (hD : BddAbove (Set.range fun z => (P z).discriminant)) :
    ∃ M : ℝ, 0 < M ∧ ∀ z, ((P z).shiftBeta (-((M : ℂ) * Complex.I))).Admissible := by
  obtain ⟨M, hM, hshift⟩ := exists_uniform_shift_of_bddAbove P hτ hD
  refine ⟨M + 1, by linarith, hshift _ ?_⟩
  simp only [Complex.neg_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im,
    Complex.I_re, mul_one, MulZeroClass.mul_zero, add_zero]
  linarith


-- @@ L99-101 verbatim
private def PeriodFamily.dualComplexMatrix (g : SpecialPeriods.TriangleGroup) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  (SpecialPeriods.triangleDualRepresentation g : LatticeMatrix).map (Int.castRingHom ℂ)


-- @@ L103-105 verbatim
@[simp]
private theorem PeriodFamily.dualComplexMatrix_one : dualComplexMatrix 1 = 1 := by
  simp [dualComplexMatrix]


-- @@ L107-110 verbatim
private theorem PeriodFamily.dualComplexMatrix_mul (g h : SpecialPeriods.TriangleGroup) :
    dualComplexMatrix (g * h) = dualComplexMatrix g * dualComplexMatrix h := by
  simp only [dualComplexMatrix, map_mul, Matrix.SpecialLinearGroup.coe_mul]
  exact Matrix.map_mul


-- @@ L112-115 verbatim
@[simp]
private theorem PeriodFamily.dualComplexMatrix_generator₁ :
    dualComplexMatrix SpecialPeriods.triangleGenerator₁ = A₁.map (Int.castRingHom ℂ) := by
  rw [dualComplexMatrix, SpecialPeriods.triangleDualRepresentation_generator₁_matrix]


-- @@ L117-120 verbatim
@[simp]
private theorem PeriodFamily.dualComplexMatrix_generator₂ :
    dualComplexMatrix SpecialPeriods.triangleGenerator₂ = A₂.map (Int.castRingHom ℂ) := by
  rw [dualComplexMatrix, SpecialPeriods.triangleDualRepresentation_generator₂_matrix]


-- @@ L122-123 verbatim
private def PeriodFamily.matrixRight (M : Matrix (Fin 2) (Fin 4) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i k => M i (![2, 3] k)


-- @@ L125-128 verbatim
private theorem PeriodFamily.periodMatrix_right (p : PeriodPoint) (R : Matrix (Fin 2) (Fin 2) ℂ) :
    (fun i k => (R * p.matrix) i (![2, 3] k)) = R := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [PeriodPoint.matrix, Matrix.mul_apply, Fin.sum_univ_two]


-- @@ L130-139 verbatim
private structure PeriodFamily.Data (V B : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction SpecialPeriods.TriangleGroup B] where
  periods : HolomorphicPeriodMap V B
  base_holomorphic :
    ∀ g : SpecialPeriods.TriangleGroup,
      ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ V) ω (fun b : B => g • b)
  covariance₁ :
    ∀ b, periods.point (SpecialPeriods.triangleGenerator₁ • b) = (periods.point b).step₁
  covariance₂ :
    ∀ b, periods.point (SpecialPeriods.triangleGenerator₂ • b) = (periods.point b).step₂


-- @@ L141-146 verbatim
private def
    PeriodFamily.Data.rightBlock {V : Type*} {B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction SpecialPeriods.TriangleGroup B]
    (D : PeriodFamily.Data V B) (g : SpecialPeriods.TriangleGroup) (b : B) :
    Matrix (Fin 2) (Fin 2) ℂ := fun i k =>
  ((D.periods.point (g • b)).val.matrix * PeriodFamily.dualComplexMatrix g) i (![2, 3] k)


-- @@ L148-155 verbatim
private def PeriodFamily.Data.HasCovariance_mo1973_18367 {V : Type*} {B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (g : SpecialPeriods.TriangleGroup) : Prop :=
  ∀ b : B,
    ∃ R : Matrix (Fin 2) (Fin 2) ℂ,
      (D.periods.point (g • b)).val.matrix * PeriodFamily.dualComplexMatrix g =
        R * (D.periods.point b).val.matrix


-- @@ L157-162 verbatim
private theorem PeriodFamily.Data.hasCovariance_one_mo1973_18368 {V : Type*} {B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) :
    D.HasCovariance_mo1973_18367 1 := by
  intro b
  exact ⟨1, by simp⟩


-- @@ L164-174 verbatim
private theorem PeriodFamily.Data.hasCovariance_mul_mo1973_18369 {V : Type*} {B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    {g h : SpecialPeriods.TriangleGroup} (hg : D.HasCovariance_mo1973_18367 g)
    (hh : D.HasCovariance_mo1973_18367 h) : D.HasCovariance_mo1973_18367 (g * h) := by
  intro b
  obtain ⟨Rg, hg⟩ := hg (h • b)
  obtain ⟨Rh, hh⟩ := hh b
  refine ⟨Rg * Rh, ?_⟩
  rw [SemigroupAction.mul_smul, PeriodFamily.dualComplexMatrix_mul, ← Matrix.mul_assoc, hg,
    Matrix.mul_assoc, hh, Matrix.mul_assoc]


-- @@ L176-191 verbatim
private theorem PeriodFamily.Data.hasCovariance_generator₁_mo1973_18370 {V : Type*} {B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) :
    D.HasCovariance_mo1973_18367 SpecialPeriods.triangleGenerator₁ := by
  intro b
  refine ⟨(D.periods.point b).val.R₁, ?_⟩
  rw [D.covariance₁, PeriodFamily.dualComplexMatrix_generator₁]
  change (D.periods.point b).val.step₁.matrix * A₁.map (Int.castRingHom ℂ) = _
  rw [PeriodPoint.step₁_matrix _
      ((D.periods.point b).val.τ_ne_zero (D.periods.point b).property.1),
    Matrix.mul_assoc]
  have h : (T₁.map (Int.castRingHom ℂ)).transpose * A₁.map (Int.castRingHom ℂ) = 1 := by
    change T₁.transpose.map (Int.castRingHom ℂ) * A₁.map (Int.castRingHom ℂ) = 1
    rw [← Matrix.map_mul, show T₁.transpose * A₁ = 1 by decide]
    simp
  rw [h, Matrix.mul_one]


-- @@ L193-208 verbatim
private theorem PeriodFamily.Data.hasCovariance_generator₂_mo1973_18371 {V : Type*} {B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) :
    D.HasCovariance_mo1973_18367 SpecialPeriods.triangleGenerator₂ := by
  intro b
  refine ⟨(D.periods.point b).val.R₂, ?_⟩
  rw [D.covariance₂, PeriodFamily.dualComplexMatrix_generator₂]
  change (D.periods.point b).val.step₂.matrix * A₂.map (Int.castRingHom ℂ) = _
  rw [PeriodPoint.step₂_matrix _
      ((D.periods.point b).val.τ_ne_zero (D.periods.point b).property.1),
    Matrix.mul_assoc]
  have h : (T₂.map (Int.castRingHom ℂ)).transpose * A₂.map (Int.castRingHom ℂ) = 1 := by
    change T₂.transpose.map (Int.castRingHom ℂ) * A₂.map (Int.castRingHom ℂ) = 1
    rw [← Matrix.map_mul, show T₂.transpose * A₂ = 1 by decide]
    simp
  rw [h, Matrix.mul_one]


-- @@ L210-217 verbatim
private theorem PeriodFamily.Data.hasCovariance_pow_mo1973_18372 {V : Type*} {B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    {g : SpecialPeriods.TriangleGroup} (hg : D.HasCovariance_mo1973_18367 g) (n : ℕ) :
    D.HasCovariance_mo1973_18367 (g ^ n) := by
  induction n with
  | zero => simpa using D.hasCovariance_one_mo1973_18368
  | succ n ih => simpa only [pow_succ] using D.hasCovariance_mul_mo1973_18369 ih hg


-- @@ L219-223 verbatim
public
theorem PeriodFamily.Data.cyclic_eq_generator_pow_mo1973_18373 {n : ℕ} [NeZero n]
    (x : Multiplicative (ZMod n)) : x = Multiplicative.ofAdd (1 : ZMod n) ^ x.toAdd.val := by
  change x.toAdd = x.toAdd.val • (1 : ZMod n)
  simpa only [nsmul_eq_mul, mul_one] using (ZMod.natCast_zmod_val x.toAdd).symm


-- @@ L225-236 verbatim
private theorem PeriodFamily.Data.hasCovariance_mo1973_18374 {V : Type*} {B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (g : SpecialPeriods.TriangleGroup) : D.HasCovariance_mo1973_18367 g := by
  induction g using Monoid.Coprod.induction_on with
  | inl x =>
    rw [cyclic_eq_generator_pow_mo1973_18373 x, map_pow]
    exact D.hasCovariance_pow_mo1973_18372 D.hasCovariance_generator₁_mo1973_18370 _
  | inr x =>
    rw [cyclic_eq_generator_pow_mo1973_18373 x, map_pow]
    exact D.hasCovariance_pow_mo1973_18372 D.hasCovariance_generator₂_mo1973_18371 _
  | mul g h hg hh => exact D.hasCovariance_mul_mo1973_18369 hg hh


-- @@ L238-247 verbatim
private theorem PeriodFamily.Data.rightBlock_eq_of_covariance {V : Type*} {B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (g : SpecialPeriods.TriangleGroup) (b : B) (R : Matrix (Fin 2) (Fin 2) ℂ)
    (hR :
      (D.periods.point (g • b)).val.matrix * PeriodFamily.dualComplexMatrix g =
        R * (D.periods.point b).val.matrix) :
    D.rightBlock g b = R := by
  unfold rightBlock
  rw [hR, PeriodFamily.periodMatrix_right]


-- @@ L249-257 verbatim
private theorem PeriodFamily.Data.matrix_covariance {V : Type*} {B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (g : SpecialPeriods.TriangleGroup) (b : B) :
    (D.periods.point (g • b)).val.matrix * PeriodFamily.dualComplexMatrix g =
      D.rightBlock g b * (D.periods.point b).val.matrix := by
  obtain ⟨R, hR⟩ := D.hasCovariance_mo1973_18374 g b
  rw [D.rightBlock_eq_of_covariance g b R hR]
  exact hR


-- @@ L259-262 verbatim
private abbrev PeriodFamily.Data.TotalSpace {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction SpecialPeriods.TriangleGroup B]
    (D : PeriodFamily.Data V B) :=
  D.periods.TotalSpace


-- @@ L264-264 verbatim
end Mathoverflow1973


-- @@ L266-266 verbatim
end
