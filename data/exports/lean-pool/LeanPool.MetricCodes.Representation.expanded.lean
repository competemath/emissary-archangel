/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/
module

public import LeanPool.MetricCodes.Hierarchy
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Analysis.InnerProductSpace.TensorProduct


-- @@ L13-17 verbatim
/-!
# Representation-theoretic foundations

Associated Gegenbauer systems, harmonic Young spaces, and higher projection graphs.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
noncomputable section MetricCodesNoncomputable


-- @@ L23-23 verbatim
namespace MetricCodes


-- @@ L25-25 verbatim
namespace Spherical


-- @@ L27-27 verbatim
section


-- @@ L29-29 verbatim
open Polynomial Function Module

-- @@ L30-30 verbatim
open scoped BigOperators Nat


-- @@ L32-32 verbatim
namespace AssociatedGegenbauer


-- @@ L34-45 verbatim
/-- The normalized Gegenbauer polynomials bundled as a polynomial sequence with degree equal to
the index. -/
def normalizedSequence (n : ℕ) (hn : 2 ≤ n) : Polynomial.Sequence ℝ where
  elems' := SpherePacking.Gegenbauer.normalized n
  degree_eq' := by
    intro i
    have hne : SpherePacking.Gegenbauer.normalized n i ≠ 0 := by
      intro hzero
      have hone := SpherePacking.Gegenbauer.normalized_eval_one hn i
      simp only [hzero, eval_zero, zero_ne_one] at hone
    rw [Polynomial.degree_eq_natDegree hne,
      SpherePacking.Gegenbauer.normalized_natDegree hn i]


-- @@ L47-52 verbatim
theorem normalizedSequence_leadingCoeff_isUnit
    (n : ℕ) (hn : 2 ≤ n) (i : ℕ) :
    IsUnit ((normalizedSequence n hn i).leadingCoeff) := by
  apply isUnit_iff_ne_zero.mpr
  exact Polynomial.leadingCoeff_ne_zero.mpr
    (Polynomial.Sequence.ne_zero (normalizedSequence n hn) i)


-- @@ L54-58 verbatim
/-- The basis of real polynomials given by the normalized Gegenbauer sequence. -/
def normalizedBasis (n : ℕ) (hn : 2 ≤ n) :
    Basis ℕ ℝ (Polynomial ℝ) :=
  (normalizedSequence n hn).basis
    (normalizedSequence_leadingCoeff_isUnit n hn)


-- @@ L60-63 verbatim
/-- The coefficient used in the spherical-code argument. -/
def coefficient (n : ℕ) (hn : 2 ≤ n)
    (r : ℕ) (p : Polynomial ℝ) : ℝ :=
  ((normalizedBasis n hn).repr p) r


-- @@ L65-68 verbatim
/-- Evaluate the `j`th derivative of the degree-`i` normalized Gegenbauer polynomial at `t`. -/
def derivativeValue (n i j : ℕ) (t : ℝ) : ℝ :=
  ((Polynomial.derivative^[j])
    (SpherePacking.Gegenbauer.normalized n i)).eval t


-- @@ L70-78 verbatim
/-- The `l`th shifted-power term in the associated Gegenbauer generator, with its derivative and
combinatorial coefficient. -/
def generatorTerm (n i k : ℕ) (t : ℝ) (l : ℕ) : Polynomial ℝ :=
  Polynomial.C
    (((k.choose l : ℕ) : ℝ) ^ 2 *
      (l.factorial : ℝ) *
      (-(1 - t ^ 2)) ^ (k - l) *
      derivativeValue n i (2 * k - l) t) *
    (Polynomial.C t + Polynomial.X) ^ l


-- @@ L80-84 verbatim
/-- The sum of the generator terms normalized by `k!` times the `k`th derivative at one. -/
def generator (n i k : ℕ) (t : ℝ) : Polynomial ℝ :=
  Polynomial.C
      (((k.factorial : ℝ) * derivativeValue n i k 1)⁻¹) *
    ∑ l ∈ Finset.range (k + 1), generatorTerm n i k t l


-- @@ L86-90 verbatim
/-- The theta used in the spherical-code argument. -/
def theta (n : ℕ) (hn : 4 ≤ n)
    (i k r : ℕ) (t : ℝ) : ℝ :=
  coefficient (n - 2) (by omega) r (generator n i k t) /
    coefficient (n - 2) (by omega) r ((1 + Polynomial.X) ^ k)


-- @@ L92-92 verbatim
end AssociatedGegenbauer


-- @@ L94-94 verbatim
end


-- @@ L96-96 verbatim
section


-- @@ L98-98 verbatim
open scoped BigOperators InnerProductSpace


-- @@ L100-100 verbatim
namespace FirstFibreContractions


-- @@ L102-102 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]




-- @@ L106-106 verbatim
end FirstFibreContractions


-- @@ L108-108 verbatim
namespace AssociatedOverlap


-- @@ L110-110 verbatim
open SpherePacking


-- @@ L112-120 verbatim
theorem polynomialInner_sub_right
    (n : ℕ) (p q r : MvPolynomial (Fin n) ℝ) :
    SpherePacking.Fischer.polynomialInner n p (q - r) =
      SpherePacking.Fischer.polynomialInner n p q -
        SpherePacking.Fischer.polynomialInner n p r := by
  rw [SpherePacking.Fischer.polynomialInner_comm n p (q - r),
    SpherePacking.fischer_polynomialInner_sub_left,
    SpherePacking.Fischer.polynomialInner_comm n q p,
    SpherePacking.Fischer.polynomialInner_comm n r p]


-- @@ L122-129 verbatim
theorem eval_axisPolynomial
    {n : ℕ} (x y : SpherePacking.Euclidean n) :
    MvPolynomial.eval (fun i => x i)
        (SpherePacking.axisPolynomial n y) =
      ⟪x, y⟫_ℝ := by
  classical
  simp only [axisPolynomial, mul_comm, map_sum, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C,
    PiLp.inner_apply, RCLike.inner_apply, Real.ringHom_apply]


-- @@ L131-131 verbatim
end AssociatedOverlap


-- @@ L133-133 verbatim
end


-- @@ L135-135 verbatim
section



-- @@ L138-138 verbatim
open scoped BigOperators InnerProductSpace


-- @@ L140-140 verbatim
namespace AssociatedAxisTransport


-- @@ L142-146 verbatim
/-- The common axis reflection used in the spherical-code argument. -/
def commonAxisReflection {n : ℕ}
    (x y : SpherePacking.Euclidean n) :
    SpherePacking.Euclidean n ≃ₗᵢ[ℝ] SpherePacking.Euclidean n :=
  Submodule.reflection (ℝ ∙ (x - y))ᗮ


-- @@ L148-152 verbatim
theorem commonAxisReflection_apply_left {n : ℕ}
    (x y : SpherePacking.Euclidean n)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    commonAxisReflection x y x = y := by
  exact Submodule.reflection_sub (hx.trans hy.symm)


-- @@ L154-154 verbatim
end AssociatedAxisTransport


-- @@ L156-156 verbatim
end


-- @@ L158-158 verbatim
section


-- @@ L160-160 verbatim
open scoped BigOperators InnerProductSpace


-- @@ L162-162 verbatim
namespace OrthogonalPolynomialTransport


-- @@ L164-171 verbatim
/-- The polynomial map used in the spherical-code argument. -/
def polynomialMap {n : ℕ}
    (U : SpherePacking.Euclidean n ≃ₗᵢ[ℝ]
      SpherePacking.Euclidean n) :
    MvPolynomial (Fin n) ℝ →ₐ[ℝ] MvPolynomial (Fin n) ℝ :=
  MvPolynomial.aeval (fun i : Fin n =>
    SpherePacking.axisPolynomial n
      (U (EuclideanSpace.single i (1 : ℝ))))


-- @@ L173-179 verbatim
@[simp] theorem polynomialMap_X {n : ℕ}
    (U : SpherePacking.Euclidean n ≃ₗᵢ[ℝ]
      SpherePacking.Euclidean n) (i : Fin n) :
    polynomialMap U (MvPolynomial.X i) =
      SpherePacking.axisPolynomial n
        (U (EuclideanSpace.single i (1 : ℝ))) := by
  exact MvPolynomial.aeval_X _ i


-- @@ L181-204 verbatim
theorem eval_polynomialMap {n : ℕ}
    (U : SpherePacking.Euclidean n ≃ₗᵢ[ℝ]
      SpherePacking.Euclidean n)
    (p : MvPolynomial (Fin n) ℝ)
    (x : SpherePacking.Euclidean n) :
    MvPolynomial.eval (fun i : Fin n => x i) (polynomialMap U p) =
      MvPolynomial.eval (fun i : Fin n => (U.symm x) i) p := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c =>
      simp only [MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, MvPolynomial.eval_C]
  | add p q hp hq =>
      simp only [map_add, hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, polynomialMap_X, MvPolynomial.eval_X, hp]
      congr 1
      rw [MetricCodes.Spherical.AssociatedOverlap.eval_axisPolynomial]
      have hinner := U.inner_map_map (U.symm x)
        (EuclideanSpace.single i (1 : ℝ))
      simp only [U.apply_symm_apply] at hinner
      calc
        ⟪x, U (EuclideanSpace.single i (1 : ℝ))⟫_ℝ =
          ⟪U.symm x, EuclideanSpace.single i (1 : ℝ)⟫_ℝ := hinner
        _ = _ := by simp only [EuclideanSpace.inner_single_right, Real.ringHom_apply, one_mul]


-- @@ L206-222 verbatim
theorem polynomialMap_axisPolynomial {n : ℕ}
    (U : SpherePacking.Euclidean n ≃ₗᵢ[ℝ]
      SpherePacking.Euclidean n)
    (x : SpherePacking.Euclidean n) :
    polynomialMap U (SpherePacking.axisPolynomial n x) =
      SpherePacking.axisPolynomial n (U x) := by
  apply MvPolynomial.funext
  intro coordinates
  let z : SpherePacking.Euclidean n := WithLp.toLp 2 coordinates
  change MvPolynomial.eval (fun i : Fin n => z i)
      (polynomialMap U (SpherePacking.axisPolynomial n x)) =
    MvPolynomial.eval (fun i : Fin n => z i)
      (SpherePacking.axisPolynomial n (U x))
  rw [eval_polynomialMap,
    MetricCodes.Spherical.AssociatedOverlap.eval_axisPolynomial,
    MetricCodes.Spherical.AssociatedOverlap.eval_axisPolynomial]
  simpa only [LinearIsometryEquiv.apply_symm_apply] using (U.inner_map_map (U.symm z) x).symm


-- @@ L224-240 verbatim
theorem polynomialMap_comp {n : ℕ}
    (U V : SpherePacking.Euclidean n ≃ₗᵢ[ℝ]
      SpherePacking.Euclidean n) :
    (polynomialMap U).comp (polynomialMap V) =
      polynomialMap (V.trans U) := by
  apply MvPolynomial.algHom_ext
  intro i
  apply MvPolynomial.funext
  intro coordinates
  let x : SpherePacking.Euclidean n := WithLp.toLp 2 coordinates
  change
    MvPolynomial.eval (fun j : Fin n => x j)
      ((polynomialMap U) ((polynomialMap V) (MvPolynomial.X i))) =
      MvPolynomial.eval (fun j : Fin n => x j)
        (polynomialMap (V.trans U) (MvPolynomial.X i))
  rw [eval_polynomialMap, eval_polynomialMap, eval_polynomialMap]
  simp only [MvPolynomial.eval_X, LinearIsometryEquiv.symm_trans, LinearIsometryEquiv.trans_apply]


-- @@ L242-256 verbatim
theorem polynomialMap_refl (n : ℕ) :
    polynomialMap (LinearIsometryEquiv.refl ℝ
      (SpherePacking.Euclidean n)) = AlgHom.id ℝ _ := by
  apply MvPolynomial.algHom_ext
  intro i
  apply MvPolynomial.funext
  intro coordinates
  let x : SpherePacking.Euclidean n := WithLp.toLp 2 coordinates
  change
    MvPolynomial.eval (fun j : Fin n => x j)
      (polynomialMap (LinearIsometryEquiv.refl ℝ
        (SpherePacking.Euclidean n)) (MvPolynomial.X i)) =
      MvPolynomial.eval (fun j : Fin n => x j) (MvPolynomial.X i)
  rw [eval_polynomialMap]
  rfl


-- @@ L258-283 verbatim
/-- The polynomial equiv used in the spherical-code argument. -/
def polynomialEquiv {n : ℕ}
    (U : SpherePacking.Euclidean n ≃ₗᵢ[ℝ]
      SpherePacking.Euclidean n) :
    MvPolynomial (Fin n) ℝ ≃ₐ[ℝ] MvPolynomial (Fin n) ℝ where
  toFun := polynomialMap U
  invFun := polynomialMap U.symm
  left_inv p := by
    have hcomp := polynomialMap_comp U.symm U
    have htrans : U.trans U.symm =
        LinearIsometryEquiv.refl ℝ (SpherePacking.Euclidean n) := by
      ext x
      simp only [LinearIsometryEquiv.self_trans_symm, LinearIsometryEquiv.coe_refl, id_eq]
    rw [htrans, polynomialMap_refl] at hcomp
    exact DFunLike.congr_fun hcomp p
  right_inv p := by
    have hcomp := polynomialMap_comp U U.symm
    have htrans : U.symm.trans U =
        LinearIsometryEquiv.refl ℝ (SpherePacking.Euclidean n) := by
      ext x
      simp only [LinearIsometryEquiv.symm_trans_self, LinearIsometryEquiv.coe_refl, id_eq]
    rw [htrans, polynomialMap_refl] at hcomp
    exact DFunLike.congr_fun hcomp p
  map_mul' := map_mul (polynomialMap U)
  map_add' := map_add (polynomialMap U)
  commutes' := (polynomialMap U).commutes


-- @@ L285-296 verbatim
theorem polynomialMap_isHomogeneous {n k : ℕ}
    (U : SpherePacking.Euclidean n ≃ₗᵢ[ℝ]
      SpherePacking.Euclidean n)
    (p : MvPolynomial (Fin n) ℝ)
    (hp : p.IsHomogeneous k) :
    (polynomialMap U p).IsHomogeneous k := by
  change (MvPolynomial.aeval
    (fun i : Fin n => SpherePacking.axisPolynomial n
      (U (EuclideanSpace.single i (1 : ℝ)))) p).IsHomogeneous k
  simpa only [one_mul] using hp.aeval _
    (fun i => SpherePacking.axisPolynomial_isHomogeneous
      (U (EuclideanSpace.single i (1 : ℝ))))


-- @@ L298-305 verbatim
theorem directionalDerivative_X {n : ℕ}
    (x : SpherePacking.Euclidean n) (i : Fin n) :
    SpherePacking.directionalDerivative n x (MvPolynomial.X i) =
      MvPolynomial.C (x i) := by
  classical
  simp only [SpherePacking.directionalDerivative_apply, MvPolynomial.pderiv_X, Pi.single_apply,
    smul_ite, MvPolynomial.smul_eq_C_mul, mul_one, smul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte]


-- @@ L307-332 verbatim
theorem directionalDerivative_polynomialMap {n : ℕ}
    (U : SpherePacking.Euclidean n ≃ₗᵢ[ℝ]
      SpherePacking.Euclidean n)
    (x : SpherePacking.Euclidean n)
    (p : MvPolynomial (Fin n) ℝ) :
    SpherePacking.directionalDerivative n (U x) (polynomialMap U p) =
      polynomialMap U (SpherePacking.directionalDerivative n x p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c =>
      simp only [MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq,
        SpherePacking.directionalDerivative_apply, MvPolynomial.derivation_C, smul_zero,
        Finset.sum_const_zero, map_zero]
  | add p q hp hq =>
      simp only [map_add, hp, hq]
  | mul_X p i hp =>
      rw [map_mul, polynomialMap_X,
        SpherePacking.directionalDerivative_mul, hp,
        SpherePacking.directionalDerivative_axisPolynomial,
        U.inner_map_map, EuclideanSpace.inner_single_right]
      simp only [one_mul]
      rw [SpherePacking.directionalDerivative_mul,
        directionalDerivative_X, map_add, map_mul, map_mul,
        polynomialMap_X]
      simp only [SpherePacking.directionalDerivative_apply, map_sum, map_smul, Real.ringHom_apply,
        MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq]


-- @@ L334-349 verbatim
theorem rotatedCoordinate_orthogonality {n : ℕ}
    (U : SpherePacking.Euclidean n ≃ₗᵢ[ℝ]
      SpherePacking.Euclidean n)
    (j k : Fin n) :
    (∑ i : Fin n,
      (U (EuclideanSpace.single i (1 : ℝ))) j *
        (U (EuclideanSpace.single i (1 : ℝ))) k) =
      if j = k then 1 else 0 := by
  classical
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).map U
  have h := b.sum_inner_mul_inner
    (EuclideanSpace.single j (1 : ℝ))
    (EuclideanSpace.single k (1 : ℝ))
  simpa [b, EuclideanSpace.basisFun_apply,
    EuclideanSpace.inner_single_left,
    EuclideanSpace.inner_single_right, PiLp.single_apply, eq_comm] using h


-- @@ L351-358 verbatim
theorem directionalDerivative_single {n : ℕ}
    (i : Fin n) (p : MvPolynomial (Fin n) ℝ) :
    SpherePacking.directionalDerivative n
      (EuclideanSpace.single i (1 : ℝ)) p =
      MvPolynomial.pderiv i p := by
  classical
  simp only [SpherePacking.directionalDerivative_apply, PiLp.single_apply, ite_smul, one_smul,
    zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]


-- @@ L360-369 verbatim
theorem coeff_zero_polynomialMap {n : ℕ}
    (U : SpherePacking.Euclidean n ≃ₗᵢ[ℝ]
      SpherePacking.Euclidean n)
    (p : MvPolynomial (Fin n) ℝ) :
    (polynomialMap U p).coeff 0 =
      p.coeff 0 := by
  have h := eval_polynomialMap U p (0 : SpherePacking.Euclidean n)
  simp only [map_zero, PiLp.zero_apply] at h
  simpa only [MvPolynomial.eval_zero', MvPolynomial.constantCoeff_eq]
    using h


-- @@ L371-394 verbatim
theorem polynomialInner_polynomialMap {n : ℕ}
    (U : SpherePacking.Euclidean n ≃ₗᵢ[ℝ]
      SpherePacking.Euclidean n)
    (p q : MvPolynomial (Fin n) ℝ) :
    SpherePacking.Fischer.polynomialInner n
        (polynomialMap U p) (polynomialMap U q) =
      SpherePacking.Fischer.polynomialInner n p q := by
  classical
  induction p using MvPolynomial.induction_on generalizing q with
  | C c =>
      simp only [SpherePacking.Fischer.polynomialInner, MvPolynomial.algHom_C,
        MvPolynomial.algebraMap_eq, mul_zero, coeff_zero_polynomialMap, zero_mul,
        MvPolynomial.sum_C]
  | add p r hp hr =>
      rw [map_add,
        SpherePacking.Fischer.polynomialInner_add_left,
        SpherePacking.Fischer.polynomialInner_add_left, hp, hr]
  | mul_X p i hp =>
      rw [map_mul, polynomialMap_X,
        mul_comm (polynomialMap U p), mul_comm p,
        SpherePacking.Fischer.polynomialInner_axis_directional,
        directionalDerivative_polynomialMap, hp,
        directionalDerivative_single,
        SpherePacking.Fischer.polynomialInner_X_mul]


-- @@ L396-396 verbatim
end OrthogonalPolynomialTransport


-- @@ L398-398 verbatim
end


-- @@ L400-400 verbatim
namespace HigherHarmonicYoung


-- @@ L402-402 verbatim
section



-- @@ L405-405 verbatim
open scoped BigOperators


-- @@ L407-409 verbatim
/-- The polynomial space used in the spherical-code argument. -/
abbrev PolynomialSpace (r n : ℕ) :=
  MvPolynomial (Fin ((r + 1) * n)) ℝ


-- @@ L411-414 verbatim
/-- The variable index used in the spherical-code argument. -/
def variableIndex {r n : ℕ} (i : Fin (r + 1)) (j : Fin n) :
    Fin ((r + 1) * n) :=
  finProdFinEquiv (i, j)


-- @@ L416-419 verbatim
theorem variableIndex_injective {r n : ℕ} :
    Function.Injective
      (fun z : Fin (r + 1) × Fin n => variableIndex z.1 z.2) := by
  exact finProdFinEquiv.injective


-- @@ L421-426 verbatim
/-- The row euler used in the spherical-code argument. -/
def rowEuler (r n : ℕ) (i : Fin (r + 1)) :
    PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n :=
  ∑ j : Fin n,
    (LinearMap.mulLeft ℝ (MvPolynomial.X (variableIndex i j))).comp
      (MvPolynomial.pderiv (variableIndex i j)).toLinearMap


-- @@ L428-435 verbatim
@[simp] theorem rowEuler_apply
    {r n : ℕ} (i : Fin (r + 1)) (p : PolynomialSpace r n) :
    rowEuler r n i p =
      ∑ j : Fin n,
        MvPolynomial.X (variableIndex i j) *
          MvPolynomial.pderiv (variableIndex i j) p := by
  simp only [rowEuler, LinearMap.coe_sum, LinearMap.coe_comp, Derivation.coeFn_coe,
    Finset.sum_apply, Function.comp_apply, LinearMap.mulLeft_apply]


-- @@ L437-442 verbatim
/-- The trace operator used in the spherical-code argument. -/
def traceOperator (r n : ℕ) (i j : Fin (r + 1)) :
    PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n :=
  ∑ k : Fin n,
    (MvPolynomial.pderiv (variableIndex i k)).toLinearMap.comp
      (MvPolynomial.pderiv (variableIndex j k)).toLinearMap


-- @@ L444-451 verbatim
@[simp] theorem traceOperator_apply
    {r n : ℕ} (i j : Fin (r + 1)) (p : PolynomialSpace r n) :
    traceOperator r n i j p =
      ∑ k : Fin n,
        MvPolynomial.pderiv (variableIndex i k)
          (MvPolynomial.pderiv (variableIndex j k) p) := by
  simp only [traceOperator, LinearMap.coe_sum, LinearMap.coe_comp, Derivation.coeFn_coe,
    Finset.sum_apply, Function.comp_apply]


-- @@ L453-462 verbatim
theorem traceOperator_comm
    {r n : ℕ} (i j : Fin (r + 1)) :
    traceOperator r n i j = traceOperator r n j i := by
  apply LinearMap.ext
  intro p
  simp_rw [traceOperator_apply]
  apply Finset.sum_congr rfl
  intro k _
  exact SpherePacking.mvPolynomial_pderiv_commute
    (variableIndex i k) (variableIndex j k) p


-- @@ L464-469 verbatim
/-- The polarization used in the spherical-code argument. -/
def polarization (r n : ℕ) (i j : Fin (r + 1)) :
    PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n :=
  ∑ k : Fin n,
    (LinearMap.mulLeft ℝ (MvPolynomial.X (variableIndex i k))).comp
      (MvPolynomial.pderiv (variableIndex j k)).toLinearMap


-- @@ L471-478 verbatim
@[simp] theorem polarization_apply
    {r n : ℕ} (i j : Fin (r + 1)) (p : PolynomialSpace r n) :
    polarization r n i j p =
      ∑ k : Fin n,
        MvPolynomial.X (variableIndex i k) *
          MvPolynomial.pderiv (variableIndex j k) p := by
  simp only [polarization, LinearMap.coe_sum, LinearMap.coe_comp, Derivation.coeFn_coe,
    Finset.sum_apply, Function.comp_apply, LinearMap.mulLeft_apply]


-- @@ L480-482 verbatim
@[simp] theorem polarization_self
    {r n : ℕ} (i : Fin (r + 1)) :
    polarization r n i i = rowEuler r n i := rfl


-- @@ L484-488 verbatim
/-- The simultaneous row-Euler eigenspace with eigenvalues specified by `lam`. -/
def rowWeightSubmodule {r n : ℕ} (lam : Fin (r + 1) → ℕ) :
    Submodule ℝ (PolynomialSpace r n) :=
  ⨅ i : Fin (r + 1),
    (rowEuler r n i - (lam i : ℝ) • LinearMap.id).ker


-- @@ L490-495 verbatim
@[simp] theorem mem_rowWeightSubmodule
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (p : PolynomialSpace r n) :
    p ∈ rowWeightSubmodule lam ↔
      ∀ i : Fin (r + 1), rowEuler r n i p = (lam i : ℝ) • p := by
  simp only [rowWeightSubmodule, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    rowEuler_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq, sub_eq_zero]


-- @@ L497-501 verbatim
/-- The trace free submodule used in the spherical-code argument. -/
def traceFreeSubmodule (r n : ℕ) :
    Submodule ℝ (PolynomialSpace r n) :=
  ⨅ i : Fin (r + 1), ⨅ j : Fin (r + 1),
    (traceOperator r n i j).ker


-- @@ L503-507 verbatim
@[simp] theorem mem_traceFreeSubmodule
    {r n : ℕ} (p : PolynomialSpace r n) :
    p ∈ traceFreeSubmodule r n ↔
      ∀ i j : Fin (r + 1), traceOperator r n i j p = 0 := by
  simp only [traceFreeSubmodule, Submodule.mem_iInf, LinearMap.mem_ker, traceOperator_apply]


-- @@ L509-513 verbatim
/-- The intersection of the kernels of the upper-row polarization operators. -/
def highestWeightSubmodule (r n : ℕ) :
    Submodule ℝ (PolynomialSpace r n) :=
  ⨅ i : Fin (r + 1), ⨅ j : Fin (r + 1), ⨅ (_ : i < j),
    (polarization r n i j).ker


-- @@ L515-519 verbatim
@[simp] theorem mem_highestWeightSubmodule
    {r n : ℕ} (p : PolynomialSpace r n) :
    p ∈ highestWeightSubmodule r n ↔
      ∀ i j : Fin (r + 1), i < j → polarization r n i j p = 0 := by
  simp only [highestWeightSubmodule, Submodule.mem_iInf, LinearMap.mem_ker, polarization_apply]


-- @@ L521-527 verbatim
/-- The harmonic young submodule used in the spherical-code argument. -/
def harmonicYoungSubmodule {r n : ℕ} (lam : Fin (r + 1) → ℕ) :
    Submodule ℝ (PolynomialSpace r n) :=
  MvPolynomial.homogeneousSubmodule
    (Fin ((r + 1) * n)) ℝ (∑ i, lam i) ⊓
      (rowWeightSubmodule lam ⊓
        (traceFreeSubmodule r n ⊓ highestWeightSubmodule r n))


-- @@ L529-538 verbatim
@[simp] theorem mem_harmonicYoungSubmodule
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (p : PolynomialSpace r n) :
    p ∈ harmonicYoungSubmodule lam ↔
      p.IsHomogeneous (∑ i, lam i) ∧
        (∀ i : Fin (r + 1), rowEuler r n i p = (lam i : ℝ) • p) ∧
        (∀ i j : Fin (r + 1), traceOperator r n i j p = 0) ∧
        (∀ i j : Fin (r + 1), i < j → polarization r n i j p = 0) := by
  simp only [harmonicYoungSubmodule, Submodule.mem_inf, MvPolynomial.mem_homogeneousSubmodule,
    mem_rowWeightSubmodule, rowEuler_apply, mem_traceFreeSubmodule, traceOperator_apply,
    mem_highestWeightSubmodule, polarization_apply]


-- @@ L540-542 verbatim
/-- The harmonic young space used in the spherical-code argument. -/
abbrev HarmonicYoungSpace {r n : ℕ} (lam : Fin (r + 1) → ℕ) :=
  harmonicYoungSubmodule (n := n) lam


-- @@ L544-557 verbatim
instance harmonicYoungSpace_finiteDimensional
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) :
    FiniteDimensional ℝ (HarmonicYoungSpace (n := n) lam) := by
  let f : HarmonicYoungSpace (n := n) lam →ₗ[ℝ]
      MvPolynomial.homogeneousSubmodule
        (Fin ((r + 1) * n)) ℝ (∑ i, lam i) :=
    Submodule.inclusion (fun _ hp => hp.1)
  apply FiniteDimensional.of_injective f
  intro p q hpq
  apply Subtype.ext
  exact congrArg
    (fun z : MvPolynomial.homogeneousSubmodule
      (Fin ((r + 1) * n)) ℝ (∑ i, lam i) =>
        (z : PolynomialSpace r n)) hpq


-- @@ L559-561 verbatim
/-- The Euclidean product of `r + 1` rows, each with `n` coordinates. -/
abbrev RowEuclideanSpace (r n : ℕ) :=
  PiLp 2 (fun _ : Fin (r + 1) => SpherePacking.Euclidean n)


-- @@ L563-571 verbatim
/-- The isometry regrouping a flat Euclidean coordinate vector into its rows. -/
def rowEuclideanEquiv (r n : ℕ) :
    SpherePacking.Euclidean ((r + 1) * n) ≃ₗᵢ[ℝ]
      RowEuclideanSpace r n :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (finProdFinEquiv.symm.trans
      (Equiv.sigmaEquivProd (Fin (r + 1)) (Fin n)).symm)).trans
    (LinearIsometryEquiv.piLpCurry ℝ 2
      (fun _ : Fin (r + 1) => fun _ : Fin n => ℝ))


-- @@ L573-577 verbatim
theorem rowEuclideanEquiv_apply
    {r n : ℕ} (x : SpherePacking.Euclidean ((r + 1) * n))
    (i : Fin (r + 1)) (j : Fin n) :
    rowEuclideanEquiv r n x i j = x (variableIndex i j) := by
  rfl


-- @@ L579-585 verbatim
theorem rowEuclideanEquiv_symm_apply
    {r n : ℕ} (x : RowEuclideanSpace r n)
    (i : Fin (r + 1)) (j : Fin n) :
    (rowEuclideanEquiv r n).symm x (variableIndex i j) = x i j := by
  have h := congrArg (fun y : RowEuclideanSpace r n => y i j)
    ((rowEuclideanEquiv r n).apply_symm_apply x)
  simpa only [rowEuclideanEquiv_apply] using h


-- @@ L587-596 verbatim
/-- Apply the same Euclidean isometry independently to every row of a flat coordinate vector. -/
def blockIsometry {r n : ℕ}
    (U : SpherePacking.Euclidean n ≃ₗᵢ[ℝ]
      SpherePacking.Euclidean n) :
    SpherePacking.Euclidean ((r + 1) * n) ≃ₗᵢ[ℝ]
      SpherePacking.Euclidean ((r + 1) * n) :=
  (rowEuclideanEquiv r n).trans
    ((LinearIsometryEquiv.piLpCongrRight 2
      (fun _ : Fin (r + 1) => U)).trans
      (rowEuclideanEquiv r n).symm)


-- @@ L598-610 verbatim
theorem blockIsometry_apply
    {r n : ℕ}
    (U : SpherePacking.Euclidean n ≃ₗᵢ[ℝ]
      SpherePacking.Euclidean n)
    (x : SpherePacking.Euclidean ((r + 1) * n))
    (i : Fin (r + 1)) (j : Fin n) :
    blockIsometry (r := r) U x (variableIndex i j) =
      U (WithLp.toLp 2
        (fun k : Fin n => x (variableIndex i k))) j := by
  unfold blockIsometry
  rw [LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.trans_apply, rowEuclideanEquiv_symm_apply]
  rfl


-- @@ L612-629 verbatim
theorem row_of_single_same
    {r n : ℕ} (i : Fin (r + 1)) (j : Fin n) :
    WithLp.toLp 2
      (fun k : Fin n =>
        (EuclideanSpace.single (variableIndex i j) (1 : ℝ) :
          SpherePacking.Euclidean ((r + 1) * n))
            (variableIndex i k)) =
      (EuclideanSpace.single j (1 : ℝ) : SpherePacking.Euclidean n) := by
  ext k
  have hindex : variableIndex i k = variableIndex i j ↔ k = j := by
    constructor
    · intro h
      have hpair : (i, k) = (i, j) :=
        variableIndex_injective (r := r) (n := n) h
      exact congrArg Prod.snd hpair
    · rintro rfl
      rfl
  simp only [EuclideanSpace.single, PiLp.single_apply, hindex]


-- @@ L631-646 verbatim
theorem row_of_single_ne
    {r n : ℕ} (i h : Fin (r + 1)) (j : Fin n) (hne : h ≠ i) :
    WithLp.toLp 2
      (fun k : Fin n =>
        (EuclideanSpace.single (variableIndex i j) (1 : ℝ) :
          SpherePacking.Euclidean ((r + 1) * n))
            (variableIndex h k)) =
      (0 : SpherePacking.Euclidean n) := by
  ext k
  have hindex : variableIndex h k ≠ variableIndex i j := by
    intro heq
    have hpair : (h, k) = (i, j) :=
      variableIndex_injective (r := r) (n := n) heq
    exact hne (congrArg Prod.fst hpair)
  simp only [EuclideanSpace.single, ne_eq, hindex, not_false_eq_true, PiLp.single_eq_of_ne,
    PiLp.zero_apply]


-- @@ L648-662 verbatim
theorem blockIsometry_single
    {r n : ℕ}
    (U : SpherePacking.Euclidean n ≃ₗᵢ[ℝ]
      SpherePacking.Euclidean n)
    (i h : Fin (r + 1)) (j k : Fin n) :
    blockIsometry (r := r) U
        (EuclideanSpace.single (variableIndex i j) (1 : ℝ))
          (variableIndex h k) =
      if h = i then U (EuclideanSpace.single j (1 : ℝ)) k else 0 := by
  rw [blockIsometry_apply]
  split_ifs with heq
  · subst h
    rw [row_of_single_same]
  · rw [row_of_single_ne i h j heq, map_zero]
    rfl


-- @@ L664-671 verbatim
/-- The polynomial algebra action induced by applying the orthogonal transformation to every
row. -/
def polynomialAction {r n : ℕ}
    (U : SpherePacking.Euclidean n ≃ₗᵢ[ℝ]
      SpherePacking.Euclidean n) :
    PolynomialSpace r n ≃ₐ[ℝ] PolynomialSpace r n :=
  MetricCodes.Spherical.OrthogonalPolynomialTransport.polynomialEquiv
    (blockIsometry (r := r) U)


-- @@ L673-677 verbatim
/-- Embed a Euclidean vector into row `i`, with every other row zero. -/
def rowVector {r n : ℕ} (i : Fin (r + 1))
    (v : SpherePacking.Euclidean n) :
    SpherePacking.Euclidean ((r + 1) * n) :=
  (rowEuclideanEquiv r n).symm (PiLp.single 2 i v)


-- @@ L679-689 verbatim
theorem rowVector_apply
    {r n : ℕ} (i h : Fin (r + 1))
    (v : SpherePacking.Euclidean n) (k : Fin n) :
    rowVector i v (variableIndex h k) =
      if h = i then v k else 0 := by
  unfold rowVector
  rw [rowEuclideanEquiv_symm_apply]
  split_ifs with h
  · subst h
    simp only [PiLp.single_eq_same]
  · simp only [ne_eq, h, not_false_eq_true, PiLp.single_eq_of_ne, PiLp.zero_apply]


-- @@ L691-702 verbatim
theorem blockIsometry_rowVector
    {r n : ℕ}
    (U : SpherePacking.Euclidean n ≃ₗᵢ[ℝ]
      SpherePacking.Euclidean n)
    (i : Fin (r + 1)) (v : SpherePacking.Euclidean n) :
    blockIsometry (r := r) U (rowVector i v) =
      rowVector i (U v) := by
  apply (rowEuclideanEquiv r n).injective
  ext h k
  simp only [blockIsometry, rowVector, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.piLpCongrRight_single,
    PiLp.single_apply]


-- @@ L704-708 verbatim
/-- The row directional derivative used in the spherical-code argument. -/
def rowDirectionalDerivative (r n : ℕ)
    (i : Fin (r + 1)) (v : SpherePacking.Euclidean n) :
    PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n :=
  SpherePacking.directionalDerivative ((r + 1) * n) (rowVector i v)


-- @@ L710-726 verbatim
@[simp] theorem rowDirectionalDerivative_apply
    {r n : ℕ} (i : Fin (r + 1))
    (v : SpherePacking.Euclidean n) (p : PolynomialSpace r n) :
    rowDirectionalDerivative r n i v p =
      ∑ k : Fin n, v k •
        MvPolynomial.pderiv (variableIndex i k) p := by
  classical
  rw [rowDirectionalDerivative,
    SpherePacking.directionalDerivative_apply]
  rw [← (finProdFinEquiv (m := r + 1) (n := n)).sum_comp]
  rw [Fintype.sum_prod_type]
  change
    (∑ h : Fin (r + 1), ∑ k : Fin n,
      rowVector i v (variableIndex h k) •
        MvPolynomial.pderiv (variableIndex h k) p) = _
  simp only [rowVector_apply, ite_smul, zero_smul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]


-- @@ L728-747 verbatim
theorem rowDirectionalDerivative_polynomialAction
    {r n : ℕ}
    (U : SpherePacking.Euclidean n ≃ₗᵢ[ℝ]
      SpherePacking.Euclidean n)
    (i : Fin (r + 1)) (v : SpherePacking.Euclidean n)
    (p : PolynomialSpace r n) :
    rowDirectionalDerivative r n i (U v) (polynomialAction U p) =
      polynomialAction U (rowDirectionalDerivative r n i v p) := by
  change SpherePacking.directionalDerivative ((r + 1) * n)
      (rowVector i (U v))
      (MetricCodes.Spherical.OrthogonalPolynomialTransport.polynomialMap
        (blockIsometry U) p) =
    MetricCodes.Spherical.OrthogonalPolynomialTransport.polynomialMap
      (blockIsometry U)
      (SpherePacking.directionalDerivative ((r + 1) * n) (rowVector i v) p)
  rw [← blockIsometry_rowVector U i v]
  exact
    MetricCodes.Spherical.OrthogonalPolynomialTransport.directionalDerivative_polynomialMap
      (blockIsometry U)
      (rowVector i v) p


-- @@ L749-756 verbatim
theorem rowDirectionalDerivative_single
    {r n : ℕ} (i : Fin (r + 1)) (k : Fin n)
    (p : PolynomialSpace r n) :
    rowDirectionalDerivative r n i
      (EuclideanSpace.single k (1 : ℝ)) p =
      MvPolynomial.pderiv (variableIndex i k) p := by
  simp only [EuclideanSpace.single, rowDirectionalDerivative_apply, PiLp.single_apply, ite_smul,
    one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]



-- @@ L759-787 verbatim
theorem rotatedRowTrace
    {r n : ℕ}
    (U : SpherePacking.Euclidean n ≃ₗᵢ[ℝ]
      SpherePacking.Euclidean n)
    (i j : Fin (r + 1)) (p : PolynomialSpace r n) :
    (∑ k : Fin n,
      rowDirectionalDerivative r n i
        (U (EuclideanSpace.single k (1 : ℝ)))
        (rowDirectionalDerivative r n j
          (U (EuclideanSpace.single k (1 : ℝ))) p)) =
      traceOperator r n i j p := by
  classical
  simp_rw [rowDirectionalDerivative_apply]
  simp_rw [map_sum]
  simp_rw [(MvPolynomial.pderiv _).map_smul,
    Finset.smul_sum, smul_smul]
  calc
    _ = ∑ u : Fin n, ∑ v : Fin n,
        (∑ k : Fin n,
          (U (EuclideanSpace.single k (1 : ℝ))) u *
            (U (EuclideanSpace.single k (1 : ℝ))) v) •
          MvPolynomial.pderiv (variableIndex i u)
            (MvPolynomial.pderiv (variableIndex j v) p) := by
      simp_rw [Finset.sum_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun u _ => Finset.sum_comm
    _ = _ := by
      simp only [OrthogonalPolynomialTransport.rotatedCoordinate_orthogonality, ite_smul, one_smul,
        zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, traceOperator_apply]


-- @@ L789-826 verbatim
theorem traceOperator_polynomialAction
    {r n : ℕ}
    (U : SpherePacking.Euclidean n ≃ₗᵢ[ℝ]
      SpherePacking.Euclidean n)
    (i j : Fin (r + 1)) (p : PolynomialSpace r n) :
    traceOperator r n i j (polynomialAction U p) =
      polynomialAction U (traceOperator r n i j p) := by
  classical
  calc
    traceOperator r n i j (polynomialAction U p) =
      ∑ k : Fin n,
        rowDirectionalDerivative r n i
          (U (EuclideanSpace.single k (1 : ℝ)))
          (rowDirectionalDerivative r n j
            (U (EuclideanSpace.single k (1 : ℝ)))
              (polynomialAction U p)) :=
      (rotatedRowTrace U i j (polynomialAction U p)).symm
    _ = ∑ k : Fin n,
          polynomialAction U
            (rowDirectionalDerivative r n i
              (EuclideanSpace.single k (1 : ℝ))
              (rowDirectionalDerivative r n j
                (EuclideanSpace.single k (1 : ℝ)) p)) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [rowDirectionalDerivative_polynomialAction,
            rowDirectionalDerivative_polynomialAction]
    _ = polynomialAction U
          (∑ k : Fin n,
            rowDirectionalDerivative r n i
              (EuclideanSpace.single k (1 : ℝ))
              (rowDirectionalDerivative r n j
                (EuclideanSpace.single k (1 : ℝ)) p)) := by
          rw [map_sum]
    _ = polynomialAction U (traceOperator r n i j p) := by
          simp only [rowDirectionalDerivative_apply, PiLp.single_apply, ite_smul, one_smul,
            zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, map_sum,
            traceOperator_apply]


-- @@ L828-828 verbatim
end


-- @@ L830-830 verbatim
section



-- @@ L833-833 verbatim
open scoped BigOperators InnerProductSpace


-- @@ L835-840 verbatim
/-- The young homogeneous embedding used in the spherical-code argument. -/
def youngHomogeneousEmbedding {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    HarmonicYoungSpace (n := n) lam →ₗ[ℝ]
      SpherePacking.Fischer.Homogeneous ((r + 1) * n) (∑ i, lam i) :=
  Submodule.inclusion (fun _ hp => hp.1)


-- @@ L842-849 verbatim
theorem youngHomogeneousEmbedding_injective {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    Function.Injective (youngHomogeneousEmbedding (n := n) lam) := by
  intro p q h
  apply Subtype.ext
  exact congrArg
    (fun z : SpherePacking.Fischer.Homogeneous ((r + 1) * n) (∑ i, lam i) =>
      (z : PolynomialSpace r n)) h


-- @@ L851-859 verbatim
/-- The Fischer coefficient embedding restricted to the harmonic Young space of weight `lam`. -/
def youngCoefficientEmbedding {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    HarmonicYoungSpace (n := n) lam →ₗ[ℝ]
      SpherePacking.Fischer.CoefficientSpace
        ((r + 1) * n) (∑ i, lam i) :=
  (SpherePacking.Fischer.coefficientEmbedding
    ((r + 1) * n) (∑ i, lam i)).comp
      (youngHomogeneousEmbedding lam)


-- @@ L861-866 verbatim
theorem youngCoefficientEmbedding_injective {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    Function.Injective (youngCoefficientEmbedding (n := n) lam) :=
  (SpherePacking.Fischer.coefficientEmbedding_injective
    ((r + 1) * n) (∑ i, lam i)).comp
      (youngHomogeneousEmbedding_injective lam)


-- @@ L868-875 verbatim
/-- The Fischer inner product of harmonic Young polynomials through their homogeneous embedding. -/
def youngFischerInner {r n : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (p q : HarmonicYoungSpace (n := n) lam) : ℝ :=
  SpherePacking.Fischer.homogeneousInner
    ((r + 1) * n) (∑ i, lam i)
      (youngHomogeneousEmbedding lam p)
      (youngHomogeneousEmbedding lam q)


-- @@ L877-886 verbatim
theorem youngFischerInner_eq_polynomialInner {r n : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (p q : HarmonicYoungSpace (n := n) lam) :
    youngFischerInner lam p q =
      SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        (p : PolynomialSpace r n) (q : PolynomialSpace r n) := by
  exact SpherePacking.Fischer.homogeneousInner_eq_polynomialInner
    ((r + 1) * n) (∑ i, lam i)
      (youngHomogeneousEmbedding lam p)
      (youngHomogeneousEmbedding lam q)


-- @@ L888-895 verbatim
/-- The inner product core on the harmonic Young space induced by its injective coefficient
embedding. -/
@[implicit_reducible] def youngFischerCore {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    InnerProductSpace.Core ℝ (HarmonicYoungSpace (n := n) lam) :=
  SpherePacking.Fischer.embeddingInnerCore
    (youngCoefficientEmbedding lam)
      (youngCoefficientEmbedding_injective lam)


-- @@ L897-900 verbatim
noncomputable instance instYoungFischerInner {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    Inner ℝ (HarmonicYoungSpace (n := n) lam) :=
  ⟨youngFischerInner lam⟩


-- @@ L902-907 verbatim
noncomputable instance instYoungFischerNormedAddCommGroup {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    NormedAddCommGroup (HarmonicYoungSpace (n := n) lam) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℝ
    (HarmonicYoungSpace (n := n) lam)
    _ _ _ (youngFischerCore lam)


-- @@ L909-912 verbatim
noncomputable instance instYoungFischerInnerProductSpace {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    InnerProductSpace ℝ (HarmonicYoungSpace (n := n) lam) :=
  InnerProductSpace.ofCore _


-- @@ L914-919 verbatim
theorem young_inner_eq_polynomialInner {r n : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (p q : HarmonicYoungSpace (n := n) lam) :
    ⟪p, q⟫_ℝ = SpherePacking.Fischer.polynomialInner ((r + 1) * n)
      (p : PolynomialSpace r n) (q : PolynomialSpace r n) :=
  youngFischerInner_eq_polynomialInner lam p q


-- @@ L921-936 verbatim
theorem young_polynomialAction_inner {r n : ℕ}
    (U : SpherePacking.Euclidean n ≃ₗᵢ[ℝ]
      SpherePacking.Euclidean n)
    (lam : Fin (r + 1) → ℕ)
    (p q : HarmonicYoungSpace (n := n) lam)
    (p' q' : HarmonicYoungSpace (n := n) lam)
    (hp : (p' : PolynomialSpace r n) =
      polynomialAction U (p : PolynomialSpace r n))
    (hq : (q' : PolynomialSpace r n) =
      polynomialAction U (q : PolynomialSpace r n)) :
    ⟪p', q'⟫_ℝ = ⟪p, q⟫_ℝ := by
  rw [young_inner_eq_polynomialInner, young_inner_eq_polynomialInner,
    hp, hq]
  exact MetricCodes.Spherical.OrthogonalPolynomialTransport.polynomialInner_polynomialMap
    (blockIsometry (r := r) U)
      (p : PolynomialSpace r n) (q : PolynomialSpace r n)


-- @@ L938-938 verbatim
end


-- @@ L940-940 verbatim
section



-- @@ L943-943 verbatim
open scoped BigOperators InnerProductSpace


-- @@ L945-948 verbatim
/-- The row axis polynomial used in the spherical-code argument. -/
def rowAxisPolynomial {r n : ℕ} (i : Fin (r + 1))
    (v : SpherePacking.Euclidean n) : PolynomialSpace r n :=
  SpherePacking.axisPolynomial ((r + 1) * n) (rowVector i v)


-- @@ L950-967 verbatim
theorem rowAxisPolynomial_eq_sum {r n : ℕ} (i : Fin (r + 1))
    (v : SpherePacking.Euclidean n) :
    rowAxisPolynomial i v =
      ∑ k : Fin n,
        MvPolynomial.C (v k) * MvPolynomial.X (variableIndex i k) := by
  classical
  unfold rowAxisPolynomial SpherePacking.axisPolynomial
  rw [← (finProdFinEquiv (m := r + 1) (n := n)).sum_comp,
    Fintype.sum_prod_type]
  change
    (∑ h : Fin (r + 1), ∑ k : Fin n,
      MvPolynomial.C (rowVector i v (variableIndex h k)) *
        MvPolynomial.X (variableIndex h k)) = _
  rw [Finset.sum_eq_single i]
  · simp only [rowVector_apply, ↓reduceIte]
  · intro h _ hne
    simp only [rowVector_apply, hne, ↓reduceIte, MvPolynomial.C_0, zero_mul, Finset.sum_const_zero]
  · simp only [Finset.mem_univ, not_true_eq_false, IsEmpty.forall_iff]



-- @@ L970-1005 verbatim
theorem rotatedRowPolarization {r n : ℕ}
    (U : SpherePacking.Euclidean n ≃ₗᵢ[ℝ]
      SpherePacking.Euclidean n)
    (i j : Fin (r + 1)) (p : PolynomialSpace r n) :
    (∑ k : Fin n,
      rowAxisPolynomial i (U (EuclideanSpace.single k (1 : ℝ))) *
        rowDirectionalDerivative r n j
          (U (EuclideanSpace.single k (1 : ℝ))) p) =
      polarization r n i j p := by
  classical
  simp_rw [rowAxisPolynomial_eq_sum, rowDirectionalDerivative_apply,
    MvPolynomial.smul_eq_C_mul]
  calc
    _ = ∑ u : Fin n, ∑ v : Fin n,
      MvPolynomial.C
          (∑ k : Fin n,
            (U (EuclideanSpace.single k (1 : ℝ))) u *
              (U (EuclideanSpace.single k (1 : ℝ))) v) *
        (MvPolynomial.X (variableIndex i u) *
          MvPolynomial.pderiv (variableIndex j v) p) := by
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      rw [map_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      rw [map_mul]
      ring
    _ = _ := by
      simp only [OrthogonalPolynomialTransport.rotatedCoordinate_orthogonality,
        MonoidWithZeroHom.map_ite_one_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, ↓reduceIte, polarization_apply]


-- @@ L1007-1022 verbatim
theorem polynomialAction_variableIndex {r n : ℕ}
    (U : SpherePacking.Euclidean n ≃ₗᵢ[ℝ]
      SpherePacking.Euclidean n)
    (i : Fin (r + 1)) (k : Fin n) :
    polynomialAction U (MvPolynomial.X (variableIndex i k)) =
      rowAxisPolynomial i
        (U (EuclideanSpace.single k (1 : ℝ))) := by
  change MetricCodes.Spherical.OrthogonalPolynomialTransport.polynomialMap
      (blockIsometry (r := r) U) (MvPolynomial.X (variableIndex i k)) = _
  rw [MetricCodes.Spherical.OrthogonalPolynomialTransport.polynomialMap_X]
  unfold rowAxisPolynomial
  congr 1
  apply (rowEuclideanEquiv r n).injective
  ext h j
  simp only [rowEuclideanEquiv_apply, blockIsometry_single,
    rowVector_apply]


-- @@ L1024-1042 verbatim
theorem polarization_polynomialAction {r n : ℕ}
    (U : SpherePacking.Euclidean n ≃ₗᵢ[ℝ]
      SpherePacking.Euclidean n)
    (i j : Fin (r + 1)) (p : PolynomialSpace r n) :
    polarization r n i j (polynomialAction U p) =
      polynomialAction U (polarization r n i j p) := by
  rw [← rotatedRowPolarization U i j (polynomialAction U p)]
  calc
    _ = ∑ k : Fin n,
      polynomialAction U
        (MvPolynomial.X (variableIndex i k) *
          MvPolynomial.pderiv (variableIndex j k) p) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [rowDirectionalDerivative_polynomialAction,
        rowDirectionalDerivative_single,
        ← polynomialAction_variableIndex, map_mul]
    _ = polynomialAction U (polarization r n i j p) := by
      rw [polarization_apply, map_sum]


-- @@ L1044-1051 verbatim
theorem rowEuler_polynomialAction {r n : ℕ}
    (U : SpherePacking.Euclidean n ≃ₗᵢ[ℝ]
      SpherePacking.Euclidean n)
    (i : Fin (r + 1)) (p : PolynomialSpace r n) :
    rowEuler r n i (polynomialAction U p) =
      polynomialAction U (rowEuler r n i p) := by
  simpa only [← polarization_self, polarization_apply, map_sum, map_mul] using
    polarization_polynomialAction U i i p


-- @@ L1053-1070 verbatim
theorem polynomialAction_mem_harmonicYoungSubmodule {r n : ℕ}
    (U : SpherePacking.Euclidean n ≃ₗᵢ[ℝ]
      SpherePacking.Euclidean n)
    (lam : Fin (r + 1) → ℕ)
    {p : PolynomialSpace r n}
    (hp : p ∈ harmonicYoungSubmodule lam) :
    polynomialAction U p ∈ harmonicYoungSubmodule lam := by
  rw [mem_harmonicYoungSubmodule] at hp ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact
      MetricCodes.Spherical.OrthogonalPolynomialTransport.polynomialMap_isHomogeneous
        (blockIsometry (r := r) U) p hp.1
  · intro i
    rw [rowEuler_polynomialAction, hp.2.1 i, map_smul]
  · intro i j
    rw [traceOperator_polynomialAction, hp.2.2.1 i j, map_zero]
  · intro i j hij
    rw [polarization_polynomialAction, hp.2.2.2 i j hij, map_zero]


-- @@ L1072-1089 verbatim
theorem blockIsometry_symm_apply_apply {r n : ℕ}
    (U : SpherePacking.Euclidean n ≃ₗᵢ[ℝ]
      SpherePacking.Euclidean n)
    (x : SpherePacking.Euclidean ((r + 1) * n)) :
    blockIsometry (r := r) U.symm (blockIsometry U x) = x := by
  apply (rowEuclideanEquiv r n).injective
  ext i j
  change
    blockIsometry U.symm (blockIsometry U x) (variableIndex i j) =
      x (variableIndex i j)
  rw [blockIsometry_apply]
  have hrow :
      WithLp.toLp 2
        (fun k : Fin n => blockIsometry U x (variableIndex i k)) =
        U (WithLp.toLp 2 (fun k : Fin n => x (variableIndex i k))) := by
    ext k
    exact blockIsometry_apply U x i k
  rw [hrow, U.symm_apply_apply]


-- @@ L1091-1109 verbatim
theorem polynomialAction_symm_apply_apply {r n : ℕ}
    (U : SpherePacking.Euclidean n ≃ₗᵢ[ℝ]
      SpherePacking.Euclidean n)
    (p : PolynomialSpace r n) :
    polynomialAction U.symm (polynomialAction U p) = p := by
  have hcomp :=
    MetricCodes.Spherical.OrthogonalPolynomialTransport.polynomialMap_comp
      (blockIsometry (r := r) U.symm) (blockIsometry (r := r) U)
  have hisometry :
      (blockIsometry (r := r) U).trans (blockIsometry U.symm) =
        LinearIsometryEquiv.refl ℝ
          (SpherePacking.Euclidean ((r + 1) * n)) := by
    apply DFunLike.ext _ _
    intro x
    exact blockIsometry_symm_apply_apply U x
  rw [hisometry,
    MetricCodes.Spherical.OrthogonalPolynomialTransport.polynomialMap_refl]
    at hcomp
  exact DFunLike.congr_fun hcomp p



-- @@ L1112-1137 verbatim
/-- The linear equivalence on harmonic Young space induced by the rowwise orthogonal polynomial
action. -/
def youngOrthogonalLinearEquiv {r n : ℕ}
    (U : SpherePacking.Euclidean n ≃ₗᵢ[ℝ]
      SpherePacking.Euclidean n)
    (lam : Fin (r + 1) → ℕ) :
    HarmonicYoungSpace (n := n) lam ≃ₗ[ℝ]
      HarmonicYoungSpace (n := n) lam where
  toFun p := ⟨polynomialAction U p,
    polynomialAction_mem_harmonicYoungSubmodule U lam p.property⟩
  invFun p := ⟨polynomialAction U.symm p,
    polynomialAction_mem_harmonicYoungSubmodule U.symm lam p.property⟩
  left_inv p := by
    apply Subtype.ext
    exact polynomialAction_symm_apply_apply U (p : PolynomialSpace r n)
  right_inv p := by
    apply Subtype.ext
    simpa only [LinearIsometryEquiv.symm_symm] using
      polynomialAction_symm_apply_apply U.symm (p : PolynomialSpace r n)
  map_add' p q := by
    apply Subtype.ext
    exact map_add (polynomialAction U)
      (p : PolynomialSpace r n) (q : PolynomialSpace r n)
  map_smul' c p := by
    apply Subtype.ext
    exact map_smul (polynomialAction U) c (p : PolynomialSpace r n)


-- @@ L1139-1149 verbatim
/-- The young orthogonal isometry used in the spherical-code argument. -/
def youngOrthogonalIsometry {r n : ℕ}
    (U : SpherePacking.Euclidean n ≃ₗᵢ[ℝ]
      SpherePacking.Euclidean n)
    (lam : Fin (r + 1) → ℕ) :
    HarmonicYoungSpace (n := n) lam ≃ₗᵢ[ℝ]
      HarmonicYoungSpace (n := n) lam :=
  (youngOrthogonalLinearEquiv U lam).isometryOfInner
    (fun p q => young_polynomialAction_inner U lam p q
      (youngOrthogonalLinearEquiv U lam p)
      (youngOrthogonalLinearEquiv U lam q) rfl rfl)


-- @@ L1151-1151 verbatim
end


-- @@ L1153-1153 verbatim
section



-- @@ L1156-1156 verbatim
open scoped BigOperators InnerProductSpace


-- @@ L1158-1165 verbatim
/-- The subspace of Fischer coefficients arising from harmonic Young polynomials of weight
`lam`. -/
def youngCoefficientRange {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    Submodule ℝ
      (SpherePacking.Fischer.CoefficientSpace
        ((r + 1) * n) (∑ i, lam i)) :=
  LinearMap.range (youngCoefficientEmbedding lam)


-- @@ L1167-1178 verbatim
/-- Project coefficient space orthogonally onto the harmonic Young coefficient range and recover
its polynomial. -/
def youngProjection {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    SpherePacking.Fischer.CoefficientSpace
        ((r + 1) * n) (∑ i, lam i) →ₗ[ℝ]
      HarmonicYoungSpace (n := n) lam :=
  LinearMap.linearProjOfIsCompl
    (youngCoefficientRange lam)ᗮ
    (youngCoefficientEmbedding lam)
    (youngCoefficientEmbedding_injective lam)
    (youngCoefficientRange lam).isCompl_orthogonal


-- @@ L1180-1188 verbatim
@[simp] theorem youngProjection_coefficientEmbedding {r n : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (p : HarmonicYoungSpace (n := n) lam) :
    youngProjection lam (youngCoefficientEmbedding lam p) = p := by
  exact LinearMap.linearProjOfIsCompl_apply_left
    (youngCoefficientRange lam)ᗮ
    (youngCoefficientEmbedding lam)
    (youngCoefficientEmbedding_injective lam)
    (youngCoefficientRange lam).isCompl_orthogonal p


-- @@ L1190-1198 verbatim
/-- The young homogeneous projection used in the spherical-code argument. -/
def youngHomogeneousProjection {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    SpherePacking.Fischer.Homogeneous
        ((r + 1) * n) (∑ i, lam i) →ₗ[ℝ]
      HarmonicYoungSpace (n := n) lam :=
  (youngProjection lam).comp
    (SpherePacking.Fischer.coefficientEmbedding
      ((r + 1) * n) (∑ i, lam i))


-- @@ L1200-1219 verbatim
/-- The row axis homogeneous used in the spherical-code argument. -/
def rowAxisHomogeneous {r n : ℕ}
    (mu lam : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, mu i) = (∑ i, lam i) + 1)
    (i : Fin (r + 1)) (v : SpherePacking.Euclidean n) :
    HarmonicYoungSpace (n := n) lam →ₗ[ℝ]
      SpherePacking.Fischer.Homogeneous ((r + 1) * n) (∑ j, mu j) :=
  LinearMap.codRestrict
    (MvPolynomial.homogeneousSubmodule
      (Fin ((r + 1) * n)) ℝ (∑ j, mu j))
    ((LinearMap.mulLeft ℝ
      (SpherePacking.axisPolynomial ((r + 1) * n) (rowVector i v))).comp
        (harmonicYoungSubmodule lam).subtype)
    (fun p => by
      change
        (SpherePacking.axisPolynomial ((r + 1) * n) (rowVector i v) *
          (p : PolynomialSpace r n)).IsHomogeneous (∑ j, mu j)
      rw [hdeg]
      simpa only [Nat.add_comm] using (SpherePacking.axisPolynomial_isHomogeneous (rowVector i
        v)).mul p.property.1)


-- @@ L1221-1229 verbatim
/-- The projected coordinate raise used in the spherical-code argument. -/
def projectedCoordinateRaise {r n : ℕ}
    (mu lam : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, mu i) = (∑ i, lam i) + 1)
    (i : Fin (r + 1)) (v : SpherePacking.Euclidean n) :
    HarmonicYoungSpace (n := n) lam →ₗ[ℝ]
      HarmonicYoungSpace (n := n) mu :=
  (youngHomogeneousProjection mu).comp
    (rowAxisHomogeneous mu lam hdeg i v)


-- @@ L1231-1251 verbatim
/-- The row directional homogeneous used in the spherical-code argument. -/
def rowDirectionalHomogeneous {r n : ℕ}
    (mu lam : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, lam i) = (∑ i, mu i) + 1)
    (i : Fin (r + 1)) (v : SpherePacking.Euclidean n) :
    HarmonicYoungSpace (n := n) lam →ₗ[ℝ]
      SpherePacking.Fischer.Homogeneous ((r + 1) * n) (∑ j, mu j) :=
  LinearMap.codRestrict
    (MvPolynomial.homogeneousSubmodule
      (Fin ((r + 1) * n)) ℝ (∑ j, mu j))
    ((rowDirectionalDerivative r n i v).comp
      (harmonicYoungSubmodule lam).subtype)
    (fun p => by
      change
        (SpherePacking.directionalDerivative ((r + 1) * n)
          (rowVector i v) (p : PolynomialSpace r n)).IsHomogeneous
            (∑ j, mu j)
      have hp := SpherePacking.directionalDerivative_isHomogeneous
        (rowVector i v) p.property.1
      rw [hdeg] at hp
      simpa only [SpherePacking.directionalDerivative_apply, add_tsub_cancel_right] using hp)


-- @@ L1253-1261 verbatim
/-- The projected coordinate lower used in the spherical-code argument. -/
def projectedCoordinateLower {r n : ℕ}
    (mu lam : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, lam i) = (∑ i, mu i) + 1)
    (i : Fin (r + 1)) (v : SpherePacking.Euclidean n) :
    HarmonicYoungSpace (n := n) lam →ₗ[ℝ]
      HarmonicYoungSpace (n := n) mu :=
  (youngHomogeneousProjection mu).comp
    (rowDirectionalHomogeneous mu lam hdeg i v)


-- @@ L1263-1269 verbatim
/-- The harmonic Young coefficient embedding bundled as a linear isometry. -/
def youngCoefficientIsometry {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    HarmonicYoungSpace (n := n) lam →ₗᵢ[ℝ]
      SpherePacking.Fischer.CoefficientSpace
        ((r + 1) * n) (∑ i, lam i) :=
  (youngCoefficientEmbedding lam).isometryOfInner (fun _ _ => rfl)


-- @@ L1271-1284 verbatim
theorem youngProjection_residual_orthogonal {r n : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (v : SpherePacking.Fischer.CoefficientSpace
      ((r + 1) * n) (∑ i, lam i)) :
    v - youngCoefficientEmbedding lam (youngProjection lam v) ∈
      (youngCoefficientRange lam)ᗮ := by
  rw [← LinearMap.ker_linearProjOfIsCompl
    (youngCoefficientRange lam)ᗮ
    (youngCoefficientEmbedding lam)
    (youngCoefficientEmbedding_injective lam)
    (youngCoefficientRange lam).isCompl_orthogonal]
  change youngProjection lam
    (v - youngCoefficientEmbedding lam (youngProjection lam v)) = 0
  rw [map_sub, youngProjection_coefficientEmbedding, sub_self]


-- @@ L1286-1309 verbatim
theorem youngProjection_inner {r n : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (v : SpherePacking.Fischer.CoefficientSpace
      ((r + 1) * n) (∑ i, lam i))
    (p : HarmonicYoungSpace (n := n) lam) :
    ⟪youngProjection lam v, p⟫_ℝ =
      ⟪v, youngCoefficientIsometry lam p⟫_ℝ := by
  have horth :=
    (Submodule.mem_orthogonal' (youngCoefficientRange lam) _).mp
      (youngProjection_residual_orthogonal lam v)
      (youngCoefficientEmbedding lam p)
      ⟨p, rfl⟩
  rw [inner_sub_left] at horth
  have hisometry :=
    (youngCoefficientIsometry lam).inner_map_map
      (youngProjection lam v) p
  change
    ⟪youngProjection lam v, p⟫_ℝ =
      ⟪v, youngCoefficientEmbedding lam p⟫_ℝ
  change
    ⟪youngCoefficientEmbedding lam (youngProjection lam v),
      youngCoefficientEmbedding lam p⟫_ℝ =
        ⟪youngProjection lam v, p⟫_ℝ at hisometry
  linarith


-- @@ L1311-1329 verbatim
theorem youngHomogeneousProjection_inner {r n : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (v : SpherePacking.Fischer.Homogeneous
      ((r + 1) * n) (∑ i, lam i))
    (p : HarmonicYoungSpace (n := n) lam) :
    ⟪youngHomogeneousProjection lam v, p⟫_ℝ =
      SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        (v : PolynomialSpace r n) (p : PolynomialSpace r n) := by
  change
    ⟪youngProjection lam
        (SpherePacking.Fischer.coefficientEmbedding
          ((r + 1) * n) (∑ i, lam i) v), p⟫_ℝ = _
  rw [youngProjection_inner]
  change
    SpherePacking.Fischer.homogeneousInner
      ((r + 1) * n) (∑ i, lam i)
      v (youngHomogeneousEmbedding lam p) = _
  exact SpherePacking.Fischer.homogeneousInner_eq_polynomialInner
    ((r + 1) * n) (∑ i, lam i) v (youngHomogeneousEmbedding lam p)


-- @@ L1331-1347 verbatim
/-- The rowwise orthogonal polynomial action restricted to homogeneous degree `k`. -/
def youngHomogeneousAction {r n : ℕ}
    (U : SpherePacking.Euclidean n ≃ₗᵢ[ℝ]
      SpherePacking.Euclidean n)
    (k : ℕ) :
    SpherePacking.Fischer.Homogeneous ((r + 1) * n) k →ₗ[ℝ]
      SpherePacking.Fischer.Homogeneous ((r + 1) * n) k where
  toFun p := ⟨polynomialAction U p,
    MetricCodes.Spherical.OrthogonalPolynomialTransport.polynomialMap_isHomogeneous
      (blockIsometry (r := r) U) p p.property⟩
  map_add' p q := by
    apply Subtype.ext
    exact map_add (polynomialAction U)
      (p : PolynomialSpace r n) (q : PolynomialSpace r n)
  map_smul' c p := by
    apply Subtype.ext
    exact map_smul (polynomialAction U) c (p : PolynomialSpace r n)


-- @@ L1349-1402 verbatim
theorem youngHomogeneousProjection_equivariant {r n : ℕ}
    (U : SpherePacking.Euclidean n ≃ₗᵢ[ℝ]
      SpherePacking.Euclidean n)
    (lam : Fin (r + 1) → ℕ)
    (v : SpherePacking.Fischer.Homogeneous
      ((r + 1) * n) (∑ i, lam i)) :
    youngHomogeneousProjection lam
        (youngHomogeneousAction U (∑ i, lam i) v) =
      youngOrthogonalIsometry U lam (youngHomogeneousProjection lam v) := by
  apply ext_inner_right ℝ
  intro p
  let q := youngOrthogonalIsometry U.symm lam p
  have hq : youngOrthogonalIsometry U lam q = p := by
    apply Subtype.ext
    change
      polynomialAction U
        (polynomialAction U.symm (p : PolynomialSpace r n)) =
          (p : PolynomialSpace r n)
    simpa only [LinearIsometryEquiv.symm_symm] using
      polynomialAction_symm_apply_apply U.symm (p : PolynomialSpace r n)
  calc
    ⟪youngHomogeneousProjection lam
        (youngHomogeneousAction U (∑ i, lam i) v), p⟫_ℝ =
      SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        (polynomialAction U (v : PolynomialSpace r n))
        (p : PolynomialSpace r n) :=
      youngHomogeneousProjection_inner lam
        (youngHomogeneousAction U (∑ i, lam i) v) p
    _ = SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        (polynomialAction U (v : PolynomialSpace r n))
        (polynomialAction U (q : PolynomialSpace r n)) := by
      have hp : (p : PolynomialSpace r n) =
          polynomialAction U (q : PolynomialSpace r n) :=
        (congrArg (fun z : HarmonicYoungSpace (n := n) lam =>
          (z : PolynomialSpace r n)) hq).symm
      rw [hp]
    _ = SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        (v : PolynomialSpace r n) (q : PolynomialSpace r n) :=
      MetricCodes.Spherical.OrthogonalPolynomialTransport.polynomialInner_polynomialMap
        (blockIsometry (r := r) U)
        (v : PolynomialSpace r n) (q : PolynomialSpace r n)
    _ = ⟪youngHomogeneousProjection lam v, q⟫_ℝ :=
      (youngHomogeneousProjection_inner lam v q).symm
    _ = ⟪youngOrthogonalIsometry U lam
          (youngHomogeneousProjection lam v), p⟫_ℝ := by
      calc
        ⟪youngHomogeneousProjection lam v, q⟫_ℝ =
            ⟪youngOrthogonalIsometry U lam
                (youngHomogeneousProjection lam v),
              youngOrthogonalIsometry U lam q⟫_ℝ :=
          ((youngOrthogonalIsometry U lam).inner_map_map
            (youngHomogeneousProjection lam v) q).symm
        _ = ⟪youngOrthogonalIsometry U lam
            (youngHomogeneousProjection lam v), p⟫_ℝ := by rw [hq]


-- @@ L1404-1445 verbatim
theorem projectedCoordinateRaise_inner {r n : ℕ}
    (mu lam : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, mu i) = (∑ i, lam i) + 1)
    (i : Fin (r + 1)) (v : SpherePacking.Euclidean n)
    (p : HarmonicYoungSpace (n := n) lam)
    (q : HarmonicYoungSpace (n := n) mu) :
    ⟪projectedCoordinateRaise mu lam hdeg i v p, q⟫_ℝ =
      ⟪p, projectedCoordinateLower lam mu hdeg i v q⟫_ℝ := by
  unfold projectedCoordinateRaise projectedCoordinateLower
  change
    ⟪youngHomogeneousProjection mu (rowAxisHomogeneous mu lam hdeg i v p),
      q⟫_ℝ =
      ⟪p, youngHomogeneousProjection lam
        (rowDirectionalHomogeneous lam mu hdeg i v q)⟫_ℝ
  calc
    ⟪youngHomogeneousProjection mu
          (rowAxisHomogeneous mu lam hdeg i v p), q⟫_ℝ =
        SpherePacking.Fischer.polynomialInner ((r + 1) * n)
          (SpherePacking.axisPolynomial ((r + 1) * n) (rowVector i v) *
            (p : PolynomialSpace r n))
          (q : PolynomialSpace r n) :=
      youngHomogeneousProjection_inner mu
        (rowAxisHomogeneous mu lam hdeg i v p) q
    _ = SpherePacking.Fischer.polynomialInner ((r + 1) * n)
          (p : PolynomialSpace r n)
          (SpherePacking.directionalDerivative ((r + 1) * n)
            (rowVector i v) (q : PolynomialSpace r n)) :=
      SpherePacking.Fischer.polynomialInner_axis_directional
        ((r + 1) * n) (rowVector i v)
        (p : PolynomialSpace r n) (q : PolynomialSpace r n)
    _ = SpherePacking.Fischer.polynomialInner ((r + 1) * n)
          (SpherePacking.directionalDerivative ((r + 1) * n)
            (rowVector i v) (q : PolynomialSpace r n))
          (p : PolynomialSpace r n) :=
      SpherePacking.Fischer.polynomialInner_comm _ _ _
    _ = ⟪youngHomogeneousProjection lam
          (rowDirectionalHomogeneous lam mu hdeg i v q), p⟫_ℝ :=
      (youngHomogeneousProjection_inner lam
        (rowDirectionalHomogeneous lam mu hdeg i v q) p).symm
    _ = ⟪p, youngHomogeneousProjection lam
          (rowDirectionalHomogeneous lam mu hdeg i v q)⟫_ℝ :=
      real_inner_comm p _


-- @@ L1447-1483 verbatim
theorem projectedCoordinateRaise_equivariant {r n : ℕ}
    (U : SpherePacking.Euclidean n ≃ₗᵢ[ℝ]
      SpherePacking.Euclidean n)
    (mu lam : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, mu i) = (∑ i, lam i) + 1)
    (i : Fin (r + 1)) (v : SpherePacking.Euclidean n)
    (p : HarmonicYoungSpace (n := n) lam) :
    projectedCoordinateRaise mu lam hdeg i (U v)
        (youngOrthogonalIsometry U lam p) =
      youngOrthogonalIsometry U mu
        (projectedCoordinateRaise mu lam hdeg i v p) := by
  unfold projectedCoordinateRaise
  change
    youngHomogeneousProjection mu
      (rowAxisHomogeneous mu lam hdeg i (U v)
        (youngOrthogonalIsometry U lam p)) =
      youngOrthogonalIsometry U mu
        (youngHomogeneousProjection mu
          (rowAxisHomogeneous mu lam hdeg i v p))
  rw [← youngHomogeneousProjection_equivariant U mu]
  congr 1
  apply Subtype.ext
  change
    SpherePacking.axisPolynomial ((r + 1) * n) (rowVector i (U v)) *
        polynomialAction U (p : PolynomialSpace r n) =
      polynomialAction U
        (SpherePacking.axisPolynomial ((r + 1) * n) (rowVector i v) *
          (p : PolynomialSpace r n))
  rw [map_mul]
  congr 1
  change
    SpherePacking.axisPolynomial ((r + 1) * n) (rowVector i (U v)) =
      MetricCodes.Spherical.OrthogonalPolynomialTransport.polynomialMap
        (blockIsometry (r := r) U)
        (SpherePacking.axisPolynomial ((r + 1) * n) (rowVector i v))
  rw [MetricCodes.Spherical.OrthogonalPolynomialTransport.polynomialMap_axisPolynomial,
    blockIsometry_rowVector]


-- @@ L1485-1508 verbatim
theorem projectedCoordinateLower_equivariant {r n : ℕ}
    (U : SpherePacking.Euclidean n ≃ₗᵢ[ℝ]
      SpherePacking.Euclidean n)
    (mu lam : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, lam i) = (∑ i, mu i) + 1)
    (i : Fin (r + 1)) (v : SpherePacking.Euclidean n)
    (p : HarmonicYoungSpace (n := n) lam) :
    projectedCoordinateLower mu lam hdeg i (U v)
        (youngOrthogonalIsometry U lam p) =
      youngOrthogonalIsometry U mu
        (projectedCoordinateLower mu lam hdeg i v p) := by
  unfold projectedCoordinateLower
  change
    youngHomogeneousProjection mu
      (rowDirectionalHomogeneous mu lam hdeg i (U v)
        (youngOrthogonalIsometry U lam p)) =
      youngOrthogonalIsometry U mu
        (youngHomogeneousProjection mu
          (rowDirectionalHomogeneous mu lam hdeg i v p))
  rw [← youngHomogeneousProjection_equivariant U mu]
  congr 1
  apply Subtype.ext
  exact rowDirectionalDerivative_polynomialAction U i v
    (p : PolynomialSpace r n)


-- @@ L1510-1510 verbatim
end


-- @@ L1512-1512 verbatim
end HigherHarmonicYoung


-- @@ L1514-1514 verbatim
section



-- @@ L1517-1517 verbatim
open Filter Topology

-- @@ L1518-1518 verbatim
open scoped BigOperators Nat Topology


-- @@ L1520-1520 verbatim
namespace HigherHierarchy.Weyl


-- @@ L1522-1524 verbatim
/-- The tail length used in the spherical-code argument. -/
def tailLength (n r : ℕ) (i : Fin (r + 1)) : ℕ :=
  n - i.val - r - 3


-- @@ L1526-1528 verbatim
/-- The row tail used in the spherical-code argument. -/
def rowTail {r : ℕ} (i : Fin (r + 1)) : ℕ :=
  r - i.val


-- @@ L1530-1538 verbatim
/-- The row factor used in the spherical-code argument. -/
def rowFactor {r : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ)
    (i : Fin (r + 1)) : ℝ :=
  ((2 * (lam i : ℝ) + (n : ℝ) - 2 * ((i.val + 1 : ℕ) : ℝ)) /
      ((n : ℝ) - 2 * ((i.val + 1 : ℕ) : ℝ))) *
    (((lam i + tailLength n r i).factorial : ℝ) /
      ((tailLength n r i).factorial : ℝ)) *
    (((rowTail i).factorial : ℝ) /
      ((lam i + rowTail i).factorial : ℝ))


-- @@ L1540-1547 verbatim
/-- The pair factor used in the spherical-code argument. -/
def pairFactor {r : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ)
    (i j : Fin (r + 1)) : ℝ :=
  (((lam i : ℝ) - (lam j : ℝ) + (j.val : ℝ) - (i.val : ℝ)) /
      ((j.val : ℝ) - (i.val : ℝ))) *
    (((lam i : ℝ) + (lam j : ℝ) + (n : ℝ) -
        (i.val : ℝ) - (j.val : ℝ) - 2) /
      ((n : ℝ) - (i.val : ℝ) - (j.val : ℝ) - 2))


-- @@ L1549-1552 verbatim
/-- The dimension used in the spherical-code argument. -/
def dimension {r : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ) : ℝ :=
  (∏ i, rowFactor n lam i) *
    ∏ i, ∏ j, if i < j then pairFactor n lam i j else 1


-- @@ L1554-1560 verbatim
theorem linearDenominator_pos {r n : ℕ}
    (hn : 2 * r + 4 ≤ n) (i : Fin (r + 1)) :
    0 < (n : ℝ) - 2 * ((i.val + 1 : ℕ) : ℝ) := by
  have hi : i.val ≤ r := by omega
  have hnat : 2 * (i.val + 1) < n := by omega
  apply sub_pos.mpr
  exact_mod_cast hnat


-- @@ L1562-1574 verbatim
theorem rowFactor_pos {r n : ℕ}
    (hn : 2 * r + 4 ≤ n) (lam : Fin (r + 1) → ℕ)
    (i : Fin (r + 1)) : 0 < rowFactor n lam i := by
  unfold rowFactor
  apply mul_pos
  · apply mul_pos
    · apply div_pos
      · have h := linearDenominator_pos hn i
        have hlam : 0 ≤ (lam i : ℝ) := Nat.cast_nonneg _
        linarith
      · exact linearDenominator_pos hn i
    · positivity
  · positivity


-- @@ L1576-1584 verbatim
theorem differenceNumerator_pos {r : ℕ}
    {lam : Fin (r + 1) → ℕ} (hlam : Antitone lam)
    {i j : Fin (r + 1)} (hij : i < j) :
    0 < (lam i : ℝ) - (lam j : ℝ) + (j.val : ℝ) - (i.val : ℝ) := by
  have hweights : (lam j : ℝ) ≤ (lam i : ℝ) := by
    exact_mod_cast hlam hij.le
  have hindices : (i.val : ℝ) < (j.val : ℝ) := by
    exact_mod_cast hij
  linarith


-- @@ L1586-1594 verbatim
theorem sumDenominator_pos {r n : ℕ}
    (hn : 2 * r + 4 ≤ n) (i j : Fin (r + 1)) :
    0 < (n : ℝ) - (i.val : ℝ) - (j.val : ℝ) - 2 := by
  have hi : i.val ≤ r := by omega
  have hj : j.val ≤ r := by omega
  have hnat : i.val + j.val + 2 < n := by omega
  have hcast : (i.val : ℝ) + (j.val : ℝ) + 2 < (n : ℝ) := by
    exact_mod_cast hnat
  linarith


-- @@ L1596-1612 verbatim
theorem pairFactor_pos {r n : ℕ}
    (hn : 2 * r + 4 ≤ n)
    {lam : Fin (r + 1) → ℕ} (hlam : Antitone lam)
    {i j : Fin (r + 1)} (hij : i < j) :
    0 < pairFactor n lam i j := by
  unfold pairFactor
  apply mul_pos
  · apply div_pos (differenceNumerator_pos hlam hij)
    have hindices : (i.val : ℝ) < (j.val : ℝ) := by
      exact_mod_cast hij
    linarith
  · apply div_pos
    · have hden := sumDenominator_pos hn i j
      have hi : 0 ≤ (lam i : ℝ) := Nat.cast_nonneg _
      have hj : 0 ≤ (lam j : ℝ) := Nat.cast_nonneg _
      linarith
    · exact sumDenominator_pos hn i j


-- @@ L1614-1627 verbatim
theorem dimension_pos {r n : ℕ}
    (hn : 2 * r + 4 ≤ n)
    {lam : Fin (r + 1) → ℕ} (hlam : Antitone lam) :
    0 < dimension n lam := by
  unfold dimension
  apply mul_pos
  · exact Finset.prod_pos fun i _ => rowFactor_pos hn lam i
  · apply Finset.prod_pos
    intro i _
    apply Finset.prod_pos
    intro j _
    split_ifs with h
    · exact pairFactor_pos hn hlam h
    · norm_num


-- @@ L1629-1643 verbatim
theorem rowFactor_eq_binomial {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) (i : Fin (r + 1)) :
    rowFactor n lam i =
      ((2 * (lam i : ℝ) + (n : ℝ) - 2 * ((i.val + 1 : ℕ) : ℝ)) /
          ((n : ℝ) - 2 * ((i.val + 1 : ℕ) : ℝ))) *
        (((lam i + tailLength n r i).choose (lam i) : ℝ) /
          ((lam i + rowTail i).choose (lam i) : ℝ)) := by
  unfold rowFactor
  rw [Nat.cast_add_choose ℝ, Nat.cast_add_choose ℝ]
  have hlam : ((lam i).factorial : ℝ) ≠ 0 := by positivity
  have ht : ((tailLength n r i).factorial : ℝ) ≠ 0 := by positivity
  have hr : ((rowTail i).factorial : ℝ) ≠ 0 := by positivity
  have hlt : ((lam i + tailLength n r i).factorial : ℝ) ≠ 0 := by positivity
  have hlr : ((lam i + rowTail i).factorial : ℝ) ≠ 0 := by positivity
  field_simp


-- @@ L1645-1686 verbatim
theorem rowFactor_update_succ_self {r n : ℕ}
    (hn : 2 * r + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ) (ell : Fin (r + 1)) :
    rowFactor n (Function.update lam ell (lam ell + 1)) ell =
      rowFactor n lam ell *
        ((2 * (lam ell : ℝ) + (n : ℝ) -
            2 * ((ell.val + 1 : ℕ) : ℝ) + 2) /
          (2 * (lam ell : ℝ) + (n : ℝ) -
            2 * ((ell.val + 1 : ℕ) : ℝ))) *
        (((lam ell : ℝ) + (tailLength n r ell : ℝ) + 1) /
          ((lam ell : ℝ) + (rowTail ell : ℝ) + 1)) := by
  have hlinear :
      (2 * (lam ell : ℝ) + (n : ℝ) -
        2 * ((ell.val + 1 : ℕ) : ℝ)) ≠ 0 := by
    have hd := linearDenominator_pos hn ell
    have hl : 0 ≤ (lam ell : ℝ) := Nat.cast_nonneg _
    linarith
  have hden := (linearDenominator_pos hn ell).ne'
  have hden' : (n : ℝ) - 2 * ((ell.val : ℝ) + 1) ≠ 0 := by
    simpa only [ne_eq, Nat.cast_add, Nat.cast_one] using hden
  have hlinear' :
      2 * (lam ell : ℝ) + (n : ℝ) -
        2 * ((ell.val : ℝ) + 1) ≠ 0 := by
    simpa only [ne_eq, Nat.cast_add, Nat.cast_one] using hlinear
  have htail : ((tailLength n r ell).factorial : ℝ) ≠ 0 := by positivity
  have hrow : ((rowTail ell).factorial : ℝ) ≠ 0 := by positivity
  have hbig : ((lam ell + tailLength n r ell).factorial : ℝ) ≠ 0 := by positivity
  have hsmall : ((lam ell + rowTail ell).factorial : ℝ) ≠ 0 := by positivity
  have hsmalllin : (lam ell : ℝ) + (rowTail ell : ℝ) + 1 ≠ 0 := by
    have hl : 0 ≤ (lam ell : ℝ) := Nat.cast_nonneg _
    have hr : 0 ≤ (rowTail ell : ℝ) := Nat.cast_nonneg _
    linarith
  have hargbig :
      lam ell + 1 + tailLength n r ell =
        (lam ell + tailLength n r ell) + 1 := by omega
  have hargsmall :
      lam ell + 1 + rowTail ell = (lam ell + rowTail ell) + 1 := by omega
  unfold rowFactor
  simp only [Function.update_self, Nat.cast_add, Nat.cast_one,
    hargbig, hargsmall, Nat.factorial_succ, Nat.cast_mul]
  field_simp [hden, hlinear, hden', hlinear', htail, hrow, hbig,
    hsmall, hsmalllin]; ring


-- @@ L1688-1694 verbatim
theorem rowFactor_update_succ_ne {r : ℕ} (n : ℕ)
    (lam : Fin (r + 1) → ℕ) (ell i : Fin (r + 1))
    (h : i ≠ ell) :
    rowFactor n (Function.update lam ell (lam ell + 1)) i =
      rowFactor n lam i := by
  unfold rowFactor
  rw [Function.update_of_ne h]


-- @@ L1696-1718 verbatim
theorem tendsto_log_linear_div {x : ℕ → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hx : Tendsto (fun n : ℕ => x n / (n : ℝ)) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => Real.log (x n) / (n : ℝ))
      atTop (𝓝 0) := by
  have hlog :
      Tendsto (fun n : ℕ => Real.log (x n / (n : ℝ)))
        atTop (𝓝 (Real.log c)) :=
    (Real.continuousAt_log hc.ne').tendsto.comp hx
  have hratio := hlog.mul (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hsum := hratio.add SpherePacking.tendsto_log_natCast_div_natCast
  have heq :
      (fun n : ℕ =>
        Real.log (x n / (n : ℝ)) * (n : ℝ)⁻¹ +
          Real.log (n : ℝ) / (n : ℝ)) =ᶠ[atTop]
      (fun n : ℕ => Real.log (x n) / (n : ℝ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ),
      hx.eventually (Ioi_mem_nhds hc)] with n hn hxn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have hxn' : x n / (n : ℝ) ≠ 0 := hxn.ne'
    rw [← div_eq_mul_inv, ← add_div,
      ← Real.log_mul hxn' hn', div_mul_cancel₀ _ hn']
  simpa only [mul_zero, add_zero] using hsum.congr' heq


-- @@ L1720-1767 verbatim
theorem tendsto_log_fixedTail_choose_div
    (k : ℕ → ℕ) (c : ℕ) {a : ℝ} (ha : 0 < a)
    (hk : Tendsto (fun n : ℕ => (k n : ℝ) / (n : ℝ))
      atTop (𝓝 a)) :
    Tendsto
      (fun n : ℕ =>
        Real.log (((k n + c).choose (k n) : ℝ)) / (n : ℝ))
      atTop (𝓝 0) := by
  have hplus :
      Tendsto (fun n : ℕ => ((k n + c : ℕ) : ℝ) / (n : ℝ))
        atTop (𝓝 a) := by
    have h := hk.add (tendsto_const_div_atTop_nhds_zero_nat (c : ℝ))
    simpa only [Nat.cast_add, add_div, add_zero] using h
  have hlog :
      Tendsto
        (fun n : ℕ => (c : ℝ) *
          (Real.log ((k n + c : ℕ) : ℝ) / (n : ℝ)))
        atTop (𝓝 0) := by
    simpa only [Nat.cast_add, mul_zero] using (tendsto_log_linear_div ha hplus).const_mul (c : ℝ)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds (x := (0 : ℝ))) hlog
  · apply Eventually.of_forall
    intro n
    apply div_nonneg
    · apply Real.log_nonneg
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (Nat.choose_pos (by omega : k n ≤ k n + c)))
    · exact Nat.cast_nonneg n
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hchoose :
        (k n + c).choose (k n) = (k n + c).choose c :=
      Nat.choose_symm_add
    have hbound :
        ((k n + c).choose (k n) : ℝ) ≤
          (((k n + c : ℕ) ^ c : ℕ) : ℝ) := by
      rw [hchoose]
      exact_mod_cast Nat.choose_le_pow (k n + c) c
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    have hpos : 0 < ((k n + c).choose (k n) : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega : k n ≤ k n + c)
    calc
      Real.log (((k n + c).choose (k n) : ℝ)) ≤
          Real.log ((((k n + c : ℕ) ^ c : ℕ) : ℝ)) :=
        Real.log_le_log hpos hbound
      _ = (c : ℝ) * Real.log ((k n + c : ℕ) : ℝ) := by
        push_cast
        rw [Real.log_pow]


-- @@ L1769-1778 verbatim
theorem tendsto_tailLength_ratio (r : ℕ) (i : Fin (r + 1)) :
    Tendsto (fun n : ℕ => (tailLength n r i : ℝ) / (n : ℝ))
      atTop (𝓝 1) := by
  have h := SpherePacking.tendsto_nat_sequence_sub_cast_div
    (fun n : ℕ => n) (i.val + r + 3) 1 tendsto_id
    SpherePacking.tendsto_natCast_div_self
  refine h.congr' (Eventually.of_forall fun n => ?_)
  congr 2
  unfold tailLength
  omega


-- @@ L1780-1801 verbatim
theorem tendsto_log_rowBinomial_div
    {r : ℕ} (i : Fin (r + 1))
    (k : ℕ → ℕ) {a : ℝ} (ha : 0 < a)
    (hkTop : Tendsto k atTop atTop)
    (hk : Tendsto (fun n : ℕ => (k n : ℝ) / (n : ℝ))
      atTop (𝓝 a)) :
    Tendsto
      (fun n : ℕ =>
        Real.log (((k n + tailLength n r i).choose (k n) : ℝ)) /
          (n : ℝ))
      atTop
      (𝓝 ((1 + a) * Real.log (1 + a) - a * Real.log a)) := by
  have htailTop : Tendsto (fun n : ℕ => tailLength n r i) atTop atTop := by
    have h := (tendsto_sub_atTop_nat (i.val + r + 3)).comp tendsto_id
    refine h.congr' (Eventually.of_forall fun n => ?_)
    change n - (i.val + r + 3) = tailLength n r i
    unfold tailLength
    omega
  have h := SpherePacking.tendsto_log_add_choose_div
    k (fun n : ℕ => tailLength n r i) a 1 hkTop htailTop hk
    (tendsto_tailLength_ratio r i) ha (by norm_num)
  simpa only [add_comm, Real.log_one, mul_zero, sub_zero] using h


-- @@ L1803-1832 verbatim
theorem tendsto_linearRowFactor
    (k : ℕ → ℕ) (c : ℕ) {a : ℝ}
    (hk : Tendsto (fun n : ℕ => (k n : ℝ) / (n : ℝ))
      atTop (𝓝 a)) :
    Tendsto
      (fun n : ℕ =>
        (2 * (k n : ℝ) + (n : ℝ) - (c : ℝ)) /
          ((n : ℝ) - (c : ℝ)))
      atTop (𝓝 (2 * a + 1)) := by
  have hone := SpherePacking.tendsto_natCast_div_self
  have hconst := tendsto_const_div_atTop_nhds_zero_nat (c : ℝ)
  have hnum := ((hk.const_mul 2).add hone).sub hconst
  have hden := hone.sub hconst
  have hratio := hnum.div hden (by norm_num)
  have heq :
      (fun n : ℕ =>
        (2 * ((k n : ℝ) / (n : ℝ)) + (n : ℝ) / (n : ℝ) -
            (c : ℝ) / (n : ℝ)) /
          ((n : ℝ) / (n : ℝ) - (c : ℝ) / (n : ℝ))) =ᶠ[atTop]
      (fun n : ℕ =>
        (2 * (k n : ℝ) + (n : ℝ) - (c : ℝ)) /
          ((n : ℝ) - (c : ℝ))) := by
    filter_upwards [eventually_gt_atTop c] with n hn
    have hn' : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le c) hn))
    have hnc : (n : ℝ) - (c : ℝ) ≠ 0 := by
      have h : (c : ℝ) < (n : ℝ) := by exact_mod_cast hn
      linarith
    field_simp
  simpa only [sub_zero, div_one] using hratio.congr' heq


-- @@ L1834-1903 verbatim
theorem tendsto_log_rowFactor_div
    {r : ℕ} (i : Fin (r + 1))
    (lam : ℕ → Fin (r + 1) → ℕ) {a : ℝ} (ha : 0 < a)
    (hlamTop : Tendsto (fun n : ℕ => lam n i) atTop atTop)
    (hlam : Tendsto
      (fun n : ℕ => (lam n i : ℝ) / (n : ℝ)) atTop (𝓝 a)) :
    Tendsto
      (fun n : ℕ => Real.log (rowFactor n (lam n) i) / (n : ℝ))
      atTop
      (𝓝 ((1 + a) * Real.log (1 + a) - a * Real.log a)) := by
  have hlin := tendsto_linearRowFactor
    (fun n : ℕ => lam n i) (2 * (i.val + 1)) hlam
  have hlinlog :
      Tendsto
        (fun n : ℕ =>
          Real.log
            ((2 * (lam n i : ℝ) + (n : ℝ) -
                ((2 * (i.val + 1) : ℕ) : ℝ)) /
              ((n : ℝ) - ((2 * (i.val + 1) : ℕ) : ℝ))) /
            (n : ℝ))
        atTop (𝓝 0) := by
    have hlog := (Real.continuousAt_log
      (by positivity : 2 * a + 1 ≠ 0)).tendsto.comp hlin
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, div_eq_mul_inv,
      Function.comp_apply, mul_zero] using hlog.mul (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hbig := tendsto_log_rowBinomial_div i
    (fun n : ℕ => lam n i) ha hlamTop hlam
  have hsmall := tendsto_log_fixedTail_choose_div
    (fun n : ℕ => lam n i) (rowTail i) ha hlam
  have hsum := (hlinlog.add hbig).sub hsmall
  have heq :
      (fun n : ℕ =>
        (Real.log
            ((2 * (lam n i : ℝ) + (n : ℝ) -
                ((2 * (i.val + 1) : ℕ) : ℝ)) /
              ((n : ℝ) - ((2 * (i.val + 1) : ℕ) : ℝ))) /
            (n : ℝ) +
          Real.log
            (((lam n i + tailLength n r i).choose (lam n i) : ℝ)) /
              (n : ℝ)) -
          Real.log
            (((lam n i + rowTail i).choose (lam n i) : ℝ)) /
              (n : ℝ)) =ᶠ[atTop]
      (fun n : ℕ => Real.log (rowFactor n (lam n) i) / (n : ℝ)) := by
    filter_upwards [eventually_ge_atTop (2 * r + 4)] with n hn
    rw [rowFactor_eq_binomial]
    have hlinpos :
        0 <
          (2 * (lam n i : ℝ) + (n : ℝ) -
              ((2 * (i.val + 1) : ℕ) : ℝ)) /
            ((n : ℝ) - ((2 * (i.val + 1) : ℕ) : ℝ)) := by
      have hden := linearDenominator_pos hn i
      apply div_pos
      · have hlam' : 0 ≤ (lam n i : ℝ) := Nat.cast_nonneg _
        push_cast
        push_cast at hden
        linarith
      · simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, sub_pos] using hden
    have hbigpos :
        0 < ((lam n i + tailLength n r i).choose (lam n i) : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega : lam n i ≤ lam n i + tailLength n r i)
    have hsmallpos :
        0 < ((lam n i + rowTail i).choose (lam n i) : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega : lam n i ≤ lam n i + rowTail i)
    push_cast at hlinpos
    push_cast
    rw [Real.log_mul hlinpos.ne' (div_ne_zero hbigpos.ne' hsmallpos.ne'),
      Real.log_div hbigpos.ne' hsmallpos.ne']
    ring
  simpa only [zero_add, sub_zero] using hsum.congr' heq


-- @@ L1905-2019 verbatim
theorem tendsto_log_pairFactor_div
    {r : ℕ} (i j : Fin (r + 1)) (hij : i < j)
    (lam : ℕ → Fin (r + 1) → ℕ)
    {aᵢ aⱼ : ℝ} (haᵢ : 0 < aᵢ) (haⱼ : 0 < aⱼ)
    (hsep : aⱼ < aᵢ)
    (hi : Tendsto (fun n : ℕ => (lam n i : ℝ) / (n : ℝ))
      atTop (𝓝 aᵢ))
    (hj : Tendsto (fun n : ℕ => (lam n j : ℝ) / (n : ℝ))
      atTop (𝓝 aⱼ)) :
    Tendsto (fun n : ℕ => Real.log (pairFactor n (lam n) i j) / (n : ℝ))
      atTop (𝓝 0) := by
  have hd : 0 < (j.val : ℝ) - (i.val : ℝ) := by
    have h : (i.val : ℝ) < (j.val : ℝ) := by exact_mod_cast hij
    linarith
  have hconst :=
    tendsto_const_div_atTop_nhds_zero_nat ((j.val : ℝ) - (i.val : ℝ))
  have hdiffscaled := ((hi.sub hj).add hconst).div_const
    ((j.val : ℝ) - (i.val : ℝ))
  simp only [add_zero] at hdiffscaled
  have hdiff :
      Tendsto
        (fun n : ℕ =>
          (((lam n i : ℝ) - (lam n j : ℝ) +
              (j.val : ℝ) - (i.val : ℝ)) /
            ((j.val : ℝ) - (i.val : ℝ))) / (n : ℝ))
        atTop
        (𝓝 ((aᵢ - aⱼ) / ((j.val : ℝ) - (i.val : ℝ)))) := by
    refine hdiffscaled.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    field_simp; ring
  have hdiffLog := tendsto_log_linear_div
    (div_pos (sub_pos.mpr hsep) hd) hdiff
  have hone := SpherePacking.tendsto_natCast_div_self
  have hshift :=
    tendsto_const_div_atTop_nhds_zero_nat
      ((i.val : ℝ) + (j.val : ℝ) + 2)
  have hsumScaled := (((hi.add hj).add hone).sub hshift).div
    (hone.sub hshift) (by norm_num)
  simp only [sub_zero, div_one] at hsumScaled
  have hsum :
      Tendsto
        (fun n : ℕ =>
          ((lam n i : ℝ) + (lam n j : ℝ) + (n : ℝ) -
              (i.val : ℝ) - (j.val : ℝ) - 2) /
            ((n : ℝ) - (i.val : ℝ) - (j.val : ℝ) - 2))
        atTop (𝓝 (aᵢ + aⱼ + 1)) := by
    refine hsumScaled.congr' ?_
    filter_upwards [eventually_gt_atTop (i.val + j.val + 2)] with n hn
    have hn' : (n : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (show 0 < n by omega)
    change
      (((lam n i : ℝ) / (n : ℝ) +
          (lam n j : ℝ) / (n : ℝ) + (n : ℝ) / (n : ℝ) -
          ((i.val : ℝ) + (j.val : ℝ) + 2) / (n : ℝ)) /
        ((n : ℝ) / (n : ℝ) -
          ((i.val : ℝ) + (j.val : ℝ) + 2) / (n : ℝ))) = _
    have hnum :
        (lam n i : ℝ) / (n : ℝ) +
            (lam n j : ℝ) / (n : ℝ) + (n : ℝ) / (n : ℝ) -
            ((i.val : ℝ) + (j.val : ℝ) + 2) / (n : ℝ) =
          ((lam n i : ℝ) + (lam n j : ℝ) + (n : ℝ) -
            ((i.val : ℝ) + (j.val : ℝ) + 2)) / (n : ℝ) := by
      ring
    have hden :
        (n : ℝ) / (n : ℝ) -
            ((i.val : ℝ) + (j.val : ℝ) + 2) / (n : ℝ) =
          ((n : ℝ) - ((i.val : ℝ) + (j.val : ℝ) + 2)) / (n : ℝ) := by
      ring
    rw [hnum, hden, div_div_div_cancel_right₀ hn']
    ring
  have hsumLog :
      Tendsto
        (fun n : ℕ =>
          Real.log
            (((lam n i : ℝ) + (lam n j : ℝ) + (n : ℝ) -
                (i.val : ℝ) - (j.val : ℝ) - 2) /
              ((n : ℝ) - (i.val : ℝ) - (j.val : ℝ) - 2)) /
            (n : ℝ))
        atTop (𝓝 0) := by
    have hlog := (Real.continuousAt_log
      (by positivity : aᵢ + aⱼ + 1 ≠ 0)).tendsto.comp hsum
    simpa only [div_eq_mul_inv, Function.comp_apply, mul_zero] using
      hlog.mul (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  have htotal := hdiffLog.add hsumLog
  have heq :
      (fun n : ℕ =>
        Real.log
            (((lam n i : ℝ) - (lam n j : ℝ) +
                (j.val : ℝ) - (i.val : ℝ)) /
              ((j.val : ℝ) - (i.val : ℝ))) / (n : ℝ) +
          Real.log
            (((lam n i : ℝ) + (lam n j : ℝ) + (n : ℝ) -
                (i.val : ℝ) - (j.val : ℝ) - 2) /
              ((n : ℝ) - (i.val : ℝ) - (j.val : ℝ) - 2)) /
            (n : ℝ)) =ᶠ[atTop]
      (fun n : ℕ =>
        Real.log (pairFactor n (lam n) i j) / (n : ℝ)) := by
    filter_upwards [
      hdiff.eventually (Ioi_mem_nhds
        (div_pos (sub_pos.mpr hsep) hd)),
      hsum.eventually (Ioi_mem_nhds
        (by positivity : 0 < aᵢ + aⱼ + 1)),
      eventually_gt_atTop (0 : ℕ)] with n hfirst hsecond hn
    have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
    have hfirst' :
        0 <
          ((lam n i : ℝ) - (lam n j : ℝ) +
              (j.val : ℝ) - (i.val : ℝ)) /
            ((j.val : ℝ) - (i.val : ℝ)) :=
      (div_pos_iff_of_pos_right hn').mp hfirst
    unfold pairFactor
    rw [Real.log_mul hfirst'.ne' hsecond.ne']
    ring
  simpa only [add_zero] using htotal.congr' heq


-- @@ L2021-2104 verbatim
theorem tendsto_log_dimension_div
    {r : ℕ} (lam : ℕ → Fin (r + 1) → ℕ)
    (a : Fin (r + 1) → ℝ)
    (ha : ∀ i, 0 < a i)
    (hanti : StrictAnti a)
    (hdominant : ∀ n, Antitone (lam n))
    (hTop : ∀ i, Tendsto (fun n : ℕ => lam n i) atTop atTop)
    (hlim : ∀ i,
      Tendsto (fun n : ℕ => (lam n i : ℝ) / (n : ℝ))
        atTop (𝓝 (a i))) :
    Tendsto
      (fun n : ℕ => Real.log (dimension n (lam n)) / (n : ℝ))
      atTop
      (𝓝 (∑ i : Fin (r + 1),
        ((1 + a i) * Real.log (1 + a i) - a i * Real.log (a i)))) := by
  have hrows :
      Tendsto
        (fun n : ℕ =>
          ∑ i : Fin (r + 1), Real.log (rowFactor n (lam n) i) / (n : ℝ))
        atTop
        (𝓝 (∑ i : Fin (r + 1),
          ((1 + a i) * Real.log (1 + a i) - a i * Real.log (a i)))) := by
    exact tendsto_finsetSum Finset.univ fun i _ =>
      tendsto_log_rowFactor_div i lam (ha i) (hTop i) (hlim i)
  have hpair (i j : Fin (r + 1)) :
      Tendsto
        (fun n : ℕ =>
          if i < j then Real.log (pairFactor n (lam n) i j) / (n : ℝ)
            else 0)
        atTop (𝓝 0) := by
    by_cases hij : i < j
    · simp only [hij, ↓reduceIte]
      exact tendsto_log_pairFactor_div i j hij lam (ha i) (ha j)
        (hanti hij) (hlim i) (hlim j)
    · simp only [hij, ↓reduceIte, tendsto_const_nhds_iff]
  have hpairs :
      Tendsto
        (fun n : ℕ =>
          ∑ i : Fin (r + 1), ∑ j : Fin (r + 1),
            if i < j then Real.log (pairFactor n (lam n) i j) / (n : ℝ)
              else 0)
        atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using
      (tendsto_finsetSum Finset.univ fun i _ => tendsto_finsetSum Finset.univ fun j _ => hpair i j)
  have hcombined := hrows.add hpairs
  have heq :
      (fun n : ℕ =>
        (∑ i : Fin (r + 1), Real.log (rowFactor n (lam n) i) / (n : ℝ)) +
          ∑ i : Fin (r + 1), ∑ j : Fin (r + 1),
            if i < j then Real.log (pairFactor n (lam n) i j) / (n : ℝ)
              else 0) =ᶠ[atTop]
      (fun n : ℕ => Real.log (dimension n (lam n)) / (n : ℝ)) := by
    filter_upwards [eventually_ge_atTop (2 * r + 4)] with n hn
    have hrow (i : Fin (r + 1)) : rowFactor n (lam n) i ≠ 0 :=
      (rowFactor_pos hn (lam n) i).ne'
    have hpair' (i j : Fin (r + 1)) :
        (if i < j then pairFactor n (lam n) i j else 1) ≠ 0 := by
      split_ifs with hij
      · exact (pairFactor_pos hn (hdominant n) hij).ne'
      · exact one_ne_zero
    have hinner (i : Fin (r + 1)) :
        (∏ j, if i < j then pairFactor n (lam n) i j else 1) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j _ => hpair' i j
    have hrowprod : (∏ i, rowFactor n (lam n) i) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => hrow i
    have hpairprod :
        (∏ i, ∏ j, if i < j then pairFactor n (lam n) i j else 1) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => hinner i
    have hloginner (i : Fin (r + 1)) :
        Real.log (∏ j, if i < j then pairFactor n (lam n) i j else 1) =
          ∑ j, if i < j then Real.log (pairFactor n (lam n) i j) else 0 := by
      rw [Real.log_prod fun j _ => hpair' i j]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> simp
    unfold dimension
    rw [Real.log_mul hrowprod hpairprod,
      Real.log_prod fun i _ => hrow i,
      Real.log_prod fun i _ => hinner i]
    simp_rw [hloginner]
    rw [add_div]
    simp_rw [Finset.sum_div]
    simp only [ite_div, zero_div]
  simpa only [Finset.sum_sub_distrib, add_zero] using hcombined.congr' heq


-- @@ L2106-2133 verbatim
theorem tendsto_log_dimension_div_log_two
    {r : ℕ} (lam : ℕ → Fin (r + 1) → ℕ)
    (a : Fin (r + 1) → ℝ)
    (ha : ∀ i, 0 < a i)
    (hanti : StrictAnti a)
    (hdominant : ∀ n, Antitone (lam n))
    (hTop : ∀ i, Tendsto (fun n : ℕ => lam n i) atTop atTop)
    (hlim : ∀ i,
      Tendsto (fun n : ℕ => (lam n i : ℝ) / (n : ℝ))
        atTop (𝓝 (a i))) :
    Tendsto
      (fun n : ℕ =>
        (Real.log (dimension n (lam n)) / (n : ℝ)) / Real.log 2)
      atTop (𝓝 (∑ i : Fin (r + 1), MetricCodes.sphericalEntropy (a i))) := by
  have h := (tendsto_log_dimension_div lam a ha hanti hdominant hTop hlim).div_const
    (Real.log 2)
  have hentropy :
      (∑ i : Fin (r + 1),
        ((1 + a i) * Real.log (1 + a i) - a i * Real.log (a i))) /
          Real.log 2 =
        ∑ i : Fin (r + 1), MetricCodes.sphericalEntropy (a i) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    unfold MetricCodes.sphericalEntropy Real.logb
    ring
  rw [hentropy] at h
  exact h


-- @@ L2135-2138 verbatim
/-- The floored weight used in the spherical-code argument. -/
def flooredWeight {r : ℕ} (a : Fin (r + 1) → ℝ) (n : ℕ)
    (i : Fin (r + 1)) : ℕ :=
  ⌊a i * (n : ℝ)⌋₊


-- @@ L2140-2146 verbatim
theorem flooredWeight_antitone {r : ℕ}
    {a : Fin (r + 1) → ℝ} (ha : Antitone a) (n : ℕ) :
    Antitone (flooredWeight a n) := by
  intro i j hij
  unfold flooredWeight
  exact Nat.floor_mono
    (mul_le_mul_of_nonneg_right (ha hij) (Nat.cast_nonneg n))


-- @@ L2148-2148 verbatim
end HigherHierarchy.Weyl


-- @@ L2150-2150 verbatim
end


-- @@ L2152-2152 verbatim
section



-- @@ L2155-2155 verbatim
open scoped BigOperators


-- @@ L2157-2157 verbatim
namespace HigherRepresentationGraph


-- @@ L2159-2160 verbatim
/-- The ambient weight used in the spherical-code argument. -/
abbrev AmbientWeight (r : ℕ) := Fin (r + 1) → ℕ


-- @@ L2162-2163 verbatim
/-- A stabilizer weight with `r` natural-number coordinates. -/
abbrev StabilizerWeight (r : ℕ) := Fin r → ℕ


-- @@ L2165-2168 verbatim
/-- The interlaces used in the spherical-code argument. -/
def Interlaces {r : ℕ}
    (lam : AmbientWeight r) (μ : StabilizerWeight r) : Prop :=
  ∀ i : Fin r, μ i ≤ lam i.castSucc ∧ lam i.succ ≤ μ i


-- @@ L2170-2173 verbatim
/-- The strict interlaces used in the spherical-code argument. -/
def StrictInterlaces {r : ℕ}
    (lam : AmbientWeight r) (μ : StabilizerWeight r) : Prop :=
  ∀ i : Fin r, μ i < lam i.castSucc ∧ lam i.succ < μ i


-- @@ L2175-2179 verbatim
theorem StrictInterlaces.interlaces {r : ℕ}
    {lam : AmbientWeight r} {μ : StabilizerWeight r}
    (h : StrictInterlaces lam μ) : Interlaces lam μ := by
  intro i
  exact ⟨(h i).1.le, (h i).2.le⟩


-- @@ L2181-2186 verbatim
theorem Interlaces.antitone_ambient {r : ℕ}
    {lam : AmbientWeight r} {μ : StabilizerWeight r}
    (h : Interlaces lam μ) : Antitone lam := by
  apply Fin.antitone_iff_succ_le.mpr
  intro i
  exact (h i).2.trans (h i).1


-- @@ L2188-2191 verbatim
/-- The raise used in the spherical-code argument. -/
def raise {r : ℕ} (lam : AmbientWeight r)
    (i : Fin (r + 1)) : AmbientWeight r :=
  fun j => if j = i then lam j + 1 else lam j


-- @@ L2193-2196 verbatim
/-- Adjacency of ambient weights when either is obtained from the other by raising one
coordinate. -/
def Adjacent {r : ℕ} (lam ν : AmbientWeight r) : Prop :=
  ∃ i : Fin (r + 1), ν = raise lam i ∨ lam = raise ν i


-- @@ L2198-2202 verbatim
theorem Adjacent.symm {r : ℕ} {lam ν : AmbientWeight r}
    (h : Adjacent lam ν) : Adjacent ν lam := by
  obtain ⟨i, h | h⟩ := h
  · exact ⟨i, Or.inr h⟩
  · exact ⟨i, Or.inl h⟩


-- @@ L2204-2204 verbatim
end HigherRepresentationGraph


-- @@ L2206-2206 verbatim
end


-- @@ L2208-2208 verbatim
section


-- @@ L2210-2210 verbatim
open scoped BigOperators InnerProductSpace TensorProduct


-- @@ L2212-2212 verbatim
namespace MixedTensorRepresentations




-- @@ L2216-2216 verbatim
open SpherePacking.HarmonicCoordinateOperators


-- @@ L2218-2218 verbatim
end MixedTensorRepresentations


-- @@ L2220-2220 verbatim
end


-- @@ L2222-2222 verbatim
section



-- @@ L2225-2225 verbatim
open scoped BigOperators


-- @@ L2227-2227 verbatim
namespace TwoRowYoungBidegreeDecomposition


-- @@ L2229-2229 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung


-- @@ L2231-2246 verbatim
theorem coeff_X_mul_pderiv {R σ : Type*} [CommSemiring R]
    (p : MvPolynomial σ R) (a : σ) (d : σ →₀ ℕ) :
    (MvPolynomial.X a * MvPolynomial.pderiv a p).coeff d =
      d a • p.coeff d := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
      simp only [map_add, mul_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp,
        nsmul_eq_mul, hq, smul_add]
  | monomial m c =>
      rw [MvPolynomial.X_mul_pderiv_monomial,
        MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial]
      split_ifs with h
      · subst m
        rfl
      · simp only [nsmul_zero]


-- @@ L2248-2248 verbatim
end TwoRowYoungBidegreeDecomposition


-- @@ L2250-2250 verbatim
end


-- @@ L2252-2252 verbatim
namespace HigherHarmonicYoung


-- @@ L2254-2254 verbatim
section



-- @@ L2257-2257 verbatim
open scoped BigOperators

-- @@ L2258-2258 verbatim
open MetricCodes.Spherical.TwoRowYoungBidegreeDecomposition


-- @@ L2260-2263 verbatim
/-- The row exponent used in the spherical-code argument. -/
def rowExponent {r n : ℕ}
    (d : Fin ((r + 1) * n) →₀ ℕ) (i : Fin (r + 1)) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun j => d (variableIndex i j)


-- @@ L2265-2268 verbatim
@[simp] theorem rowExponent_apply {r n : ℕ}
    (d : Fin ((r + 1) * n) →₀ ℕ)
    (i : Fin (r + 1)) (j : Fin n) :
    rowExponent d i j = d (variableIndex i j) := rfl


-- @@ L2270-2275 verbatim
theorem rowExponent_degree {r n : ℕ}
    (d : Fin ((r + 1) * n) →₀ ℕ) (i : Fin (r + 1)) :
    (rowExponent d i).degree =
      ∑ j : Fin n, d (variableIndex i j) := by
  rw [Finsupp.degree_eq_sum]
  rfl


-- @@ L2277-2284 verbatim
theorem degree_eq_sum_rowExponent {r n : ℕ}
    (d : Fin ((r + 1) * n) →₀ ℕ) :
    d.degree = ∑ i : Fin (r + 1), (rowExponent d i).degree := by
  rw [Finsupp.degree_eq_sum]
  simp_rw [rowExponent_degree]
  have h := Equiv.sum_comp
    (finProdFinEquiv (m := r + 1) (n := n)) (fun k => d k)
  simpa only [variableIndex, Fintype.sum_prod_type] using h.symm


-- @@ L2286-2293 verbatim
theorem coeff_rowEuler {r n : ℕ}
    (p : PolynomialSpace r n) (i : Fin (r + 1))
    (d : Fin ((r + 1) * n) →₀ ℕ) :
    (rowEuler r n i p).coeff d =
      (rowExponent d i).degree • p.coeff d := by
  rw [rowEuler_apply, MvPolynomial.coeff_sum]
  simp_rw [coeff_X_mul_pderiv]
  rw [Finset.sum_nsmul_assoc, rowExponent_degree]


-- @@ L2295-2311 verbatim
theorem harmonicYoung_rowExponent_degree {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (p : HarmonicYoungSpace (n := n) lam)
    (d : Fin ((r + 1) * n) →₀ ℕ)
    (hd : (p : PolynomialSpace r n).coeff d ≠ 0)
    (i : Fin (r + 1)) :
    (rowExponent d i).degree = lam i := by
  have hrow :=
    ((mem_harmonicYoungSubmodule lam
      (p : PolynomialSpace r n)).mp p.property).2.1 i
  have hcoeff := congrArg (·.coeff d) hrow
  rw [coeff_rowEuler, MvPolynomial.coeff_smul] at hcoeff
  have hmul :
      ((rowExponent d i).degree : ℝ) *
          (p : PolynomialSpace r n).coeff d =
        (lam i : ℝ) * (p : PolynomialSpace r n).coeff d := by
    simpa only [mul_eq_mul_right_iff, Nat.cast_inj, nsmul_eq_mul, smul_eq_mul] using hcoeff
  exact_mod_cast mul_right_cancel₀ hd hmul


-- @@ L2313-2319 verbatim
/-- The flatten row exponents used in the spherical-code argument. -/
def flattenRowExponents {r n : ℕ}
    (a : Fin (r + 1) → (Fin n →₀ ℕ)) :
    Fin ((r + 1) * n) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun k =>
    a ((finProdFinEquiv (m := r + 1) (n := n)).symm k).1
      ((finProdFinEquiv (m := r + 1) (n := n)).symm k).2


-- @@ L2321-2334 verbatim
@[simp] theorem flattenRowExponents_apply {r n : ℕ}
    (a : Fin (r + 1) → (Fin n →₀ ℕ))
    (i : Fin (r + 1)) (j : Fin n) :
    flattenRowExponents a (variableIndex i j) = a i j := by
  change
    a ((finProdFinEquiv (m := r + 1) (n := n)).symm
        (variableIndex i j)).1
      ((finProdFinEquiv (m := r + 1) (n := n)).symm
        (variableIndex i j)).2 = a i j
  have hpair :
      (finProdFinEquiv (m := r + 1) (n := n)).symm
          (variableIndex i j) = (i, j) :=
    (finProdFinEquiv (m := r + 1) (n := n)).symm_apply_apply (i, j)
  rw [hpair]


-- @@ L2336-2341 verbatim
@[simp] theorem rowExponent_flattenRowExponents {r n : ℕ}
    (a : Fin (r + 1) → (Fin n →₀ ℕ)) (i : Fin (r + 1)) :
    rowExponent (flattenRowExponents a) i = a i := by
  apply Finsupp.ext
  intro j
  exact flattenRowExponents_apply a i j


-- @@ L2343-2357 verbatim
@[simp] theorem flattenRowExponents_rowExponent {r n : ℕ}
    (d : Fin ((r + 1) * n) →₀ ℕ) :
    flattenRowExponents (fun i => rowExponent d i) = d := by
  apply Finsupp.ext
  intro k
  let i := ((finProdFinEquiv (m := r + 1) (n := n)).symm k).1
  let j := ((finProdFinEquiv (m := r + 1) (n := n)).symm k).2
  have hk : variableIndex i j = k := by
    change
      finProdFinEquiv
        (((finProdFinEquiv (m := r + 1) (n := n)).symm k).1,
          ((finProdFinEquiv (m := r + 1) (n := n)).symm k).2) = k
    exact (finProdFinEquiv (m := r + 1) (n := n)).apply_symm_apply k
  rw [← hk]
  simp only [flattenRowExponents_apply, rowExponent_apply]


-- @@ L2359-2365 verbatim
theorem flattenRowExponents_injective {r n : ℕ} :
    Function.Injective
      (flattenRowExponents (r := r) (n := n)) := by
  intro a b hab
  funext i
  have hrow := congrArg (fun d => rowExponent d i) hab
  simpa only [rowExponent_flattenRowExponents] using hrow


-- @@ L2367-2373 verbatim
/-- The row degree families used in the spherical-code argument. -/
def rowDegreeFamilies {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    Finset (Fin (r + 1) → (Fin n →₀ ℕ)) :=
  ((Finset.univ : Finset (Fin (r + 1))).pi
    (fun i => (Finset.univ : Finset (Fin n)).finsuppAntidiag (lam i))).image
      (fun f i => f i (Finset.mem_univ i))


-- @@ L2375-2400 verbatim
theorem mem_rowDegreeFamilies {r n : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (a : Fin (r + 1) → (Fin n →₀ ℕ)) :
    a ∈ rowDegreeFamilies lam ↔
      ∀ i : Fin (r + 1), (a i).degree = lam i := by
  unfold rowDegreeFamilies
  rw [Finset.mem_image]
  constructor
  · rintro ⟨f, hf, hfa⟩ i
    have hi := Finset.mem_pi.mp hf i (Finset.mem_univ i)
    have hdegree :
        (f i (Finset.mem_univ i)).degree = lam i := by
      simpa only [Finsupp.degree_eq_sum, Finset.mem_finsuppAntidiag, Finset.subset_univ,
        and_true] using hi
    have hai := congrFun hfa i
    simpa only [hai] using hdegree
  · intro ha
    let f : (i : Fin (r + 1)) →
        i ∈ (Finset.univ : Finset (Fin (r + 1))) → (Fin n →₀ ℕ) :=
      fun i _ => a i
    refine ⟨f, ?_, ?_⟩
    · apply Finset.mem_pi.mpr
      intro i _
      simpa only [Finset.mem_finsuppAntidiag, Finset.subset_univ, and_true,
        Finsupp.degree_eq_sum] using ha i
    · rfl


-- @@ L2402-2417 verbatim
theorem card_rowDegreeFamilies {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    (rowDegreeFamilies (n := n) lam).card =
      ∏ i : Fin (r + 1), (n + lam i - 1).choose (lam i) := by
  unfold rowDegreeFamilies
  have hinj :
      Function.Injective
        (fun f : (i : Fin (r + 1)) →
            i ∈ (Finset.univ : Finset (Fin (r + 1))) →
              (Fin n →₀ ℕ) =>
          fun i => f i (Finset.mem_univ i)) := by
    intro f g h
    funext i hi
    exact congrFun h i
  rw [Finset.card_image_of_injective _ hinj, Finset.card_pi]
  simp only [Finset.card_finsuppAntidiag_nat_eq_choose, Finset.card_univ, Fintype.card_fin]


-- @@ L2419-2423 verbatim
/-- The young multihomogeneous exponents used in the spherical-code argument. -/
def youngMultihomogeneousExponents {r : ℕ} (n : ℕ)
    (lam : Fin (r + 1) → ℕ) :
    Finset (Fin ((r + 1) * n) →₀ ℕ) :=
  (rowDegreeFamilies (n := n) lam).image flattenRowExponents


-- @@ L2425-2431 verbatim
theorem card_youngMultihomogeneousExponents {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    (youngMultihomogeneousExponents n lam).card =
      ∏ i : Fin (r + 1), (n + lam i - 1).choose (lam i) := by
  unfold youngMultihomogeneousExponents
  rw [Finset.card_image_of_injective _ flattenRowExponents_injective]
  exact card_rowDegreeFamilies lam


-- @@ L2433-2438 verbatim
/-- The young multihomogeneous submodule used in the spherical-code argument. -/
def youngMultihomogeneousSubmodule {r : ℕ} (n : ℕ)
    (lam : Fin (r + 1) → ℕ) : Submodule ℝ (PolynomialSpace r n) :=
  MvPolynomial.restrictSupport ℝ
    (youngMultihomogeneousExponents n lam :
      Set (Fin ((r + 1) * n) →₀ ℕ))


-- @@ L2440-2452 verbatim
theorem finrank_youngMultihomogeneousSubmodule {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    Module.finrank ℝ (youngMultihomogeneousSubmodule n lam) =
      ∏ i : Fin (r + 1), (n + lam i - 1).choose (lam i) := by
  change Module.finrank ℝ
    (MvPolynomial.restrictSupport ℝ
      (youngMultihomogeneousExponents n lam :
        Set (Fin ((r + 1) * n) →₀ ℕ))) = _
  rw [Module.finrank_eq_card_finset_basis
    (MvPolynomial.basisRestrictSupport ℝ
      (youngMultihomogeneousExponents n lam :
        Set (Fin ((r + 1) * n) →₀ ℕ)))]
  exact card_youngMultihomogeneousExponents lam


-- @@ L2454-2471 verbatim
theorem harmonicYoung_mem_youngMultihomogeneousSubmodule {r n : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (p : HarmonicYoungSpace (n := n) lam) :
    (p : PolynomialSpace r n) ∈
      youngMultihomogeneousSubmodule n lam := by
  change
    (p : PolynomialSpace r n).support ⊆
      youngMultihomogeneousExponents n lam
  intro d hd
  have hcoeff : (p : PolynomialSpace r n).coeff d ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  unfold youngMultihomogeneousExponents
  rw [Finset.mem_image]
  refine ⟨fun i => rowExponent d i, ?_,
    flattenRowExponents_rowExponent d⟩
  apply (mem_rowDegreeFamilies lam _).2
  intro i
  exact harmonicYoung_rowExponent_degree lam p d hcoeff i


-- @@ L2473-2473 verbatim
end


-- @@ L2475-2475 verbatim
section



-- @@ L2478-2478 verbatim
open scoped BigOperators


-- @@ L2480-2491 verbatim
instance youngMultihomogeneousSubmodule_finiteDimensional
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) :
    FiniteDimensional ℝ (youngMultihomogeneousSubmodule n lam) := by
  change FiniteDimensional ℝ
    (MvPolynomial.restrictSupport ℝ
      (↑(youngMultihomogeneousExponents n lam) :
        Set (Fin ((r + 1) * n) →₀ ℕ)))
  exact FiniteDimensional.of_finite_basis
    (MvPolynomial.basisRestrictSupport ℝ
      (↑(youngMultihomogeneousExponents n lam) :
        Set (Fin ((r + 1) * n) →₀ ℕ)))
    (Finset.finite_toSet _)


-- @@ L2493-2504 verbatim
theorem youngMultihomogeneous_rowExponent_degree
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    {p : PolynomialSpace r n}
    (hp : p ∈ youngMultihomogeneousSubmodule n lam)
    {d : Fin ((r + 1) * n) →₀ ℕ}
    (hd : p.coeff d ≠ 0) (i : Fin (r + 1)) :
    (rowExponent d i).degree = lam i := by
  change p.support ⊆ youngMultihomogeneousExponents n lam at hp
  have hd' : d ∈ p.support := MvPolynomial.mem_support_iff.mpr hd
  have hfamily : d ∈ youngMultihomogeneousExponents n lam := hp hd'
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hfamily
  simpa only [rowExponent_flattenRowExponents] using (mem_rowDegreeFamilies lam a).mp ha i


-- @@ L2506-2518 verbatim
theorem youngMultihomogeneous_rowEuler
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (p : youngMultihomogeneousSubmodule n lam)
    (i : Fin (r + 1)) :
    rowEuler r n i (p : PolynomialSpace r n) =
      (lam i : ℝ) • (p : PolynomialSpace r n) := by
  apply MvPolynomial.ext
  intro d
  rw [coeff_rowEuler, MvPolynomial.coeff_smul]
  by_cases hd : (p : PolynomialSpace r n).coeff d = 0
  · simp only [hd, nsmul_zero, smul_eq_mul, mul_zero]
  · rw [youngMultihomogeneous_rowExponent_degree lam p.property hd i]
    simp only [nsmul_eq_mul, smul_eq_mul]


-- @@ L2520-2530 verbatim
theorem youngMultihomogeneous_isHomogeneous
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (p : youngMultihomogeneousSubmodule n lam) :
    (p : PolynomialSpace r n).IsHomogeneous (∑ i, lam i) := by
  intro d hd
  have hdegree : d.degree = ∑ i : Fin (r + 1), lam i := by
    rw [degree_eq_sum_rowExponent d]
    apply Finset.sum_congr rfl
    intro i _
    exact youngMultihomogeneous_rowExponent_degree lam p.property hd i
  simpa only [Pi.one_def, Finsupp.degree_eq_weight_one] using hdegree


-- @@ L2532-2532 verbatim
end


-- @@ L2534-2534 verbatim
end HigherHarmonicYoung


-- @@ L2536-2536 verbatim
end Spherical


-- @@ L2538-2538 verbatim
section


-- @@ L2540-2540 verbatim
open scoped BigOperators Matrix InnerProductSpace


-- @@ L2542-2542 verbatim
namespace HigherProjectionGraph


-- @@ L2544-2544 verbatim
variable {I X : Type*} [Fintype I] [DecidableEq I]


-- @@ L2546-2597 verbatim
/-- Data encoding the data construction. -/
structure Data (I X : Type*) [Fintype I] [DecidableEq I]
    (D d Q : ℕ) where
  /-- The dimension component. -/
  dimension : I → ℕ
  dimension_pos : ∀ i, 0 < dimension i
  /-- The block component. -/
  block : I → Matrix (Fin D) (Fin D) ℝ
  block_symmetric : ∀ i, (block i)ᵀ = block i
  block_idempotent : ∀ i, block i * block i = block i
  block_orthogonal : ∀ i j, i ≠ j → block i * block j = 0
  block_complete : (∑ i, block i) = 1
  block_trace : ∀ i, Matrix.trace (block i) = (dimension i : ℝ)
  /-- The fibre component. -/
  fibre : I → X → Matrix (Fin D) (Fin d) ℝ
  fibre_isometry : ∀ i x, (fibre i x)ᵀ * fibre i x = 1
  fibre_support : ∀ i x, block i * fibre i x = fibre i x
  /-- The correlation component. -/
  correlation : X → X → ℝ
  /-- The axis component. -/
  axis : X → Matrix (Fin Q) (Fin D) ℝ
  axis_inner : ∀ x y,
    (axis x)ᵀ * axis y = correlation x y • (1 : Matrix (Fin D) (Fin D) ℝ)
  /-- The probability component. -/
  probability : I → I → ℝ
  probability_nonneg : ∀ target source, 0 ≤ probability target source
  balance : ∀ target source,
    (dimension target : ℝ) * probability target source =
      (dimension source : ℝ) * probability source target
  /-- The channel component. -/
  channel : I → I → Matrix (Fin Q) (Fin D) ℝ
  channel_isometry : ∀ target source,
    (channel target source)ᵀ * channel target source =
      if 0 < probability target source then block source else 0
  channel_orthogonal : ∀ target source target' source',
    (target, source) ≠ (target', source') →
      (channel target source)ᵀ * channel target' source' = 0
  channel_axis : ∀ target source j x,
    (channel target source)ᵀ * axis x * fibre j x =
      if target = j then
        Real.sqrt (probability target source) • fibre source x
      else 0
  /-- The eigenvalue component. -/
  eigenvalue : ℝ
  eigenvalue_pos : 0 < eigenvalue
  /-- The eigenvector component. -/
  eigenvector : I → ℝ
  eigenvector_pos : ∀ i, 0 < eigenvector i
  eigenvector_unit : (∑ i, eigenvector i ^ 2) = 1
  eigenvector_equation : ∀ i,
    (∑ j, Real.sqrt (probability i j * probability j i) * eigenvector j) =
      eigenvalue * eigenvector i


-- @@ L2599-2599 verbatim
namespace Data


-- @@ L2601-2601 verbatim
variable {D d Q : ℕ} (A : Data I X D d Q)


-- @@ L2603-2605 verbatim
/-- The weight used in the metric-code argument. -/
def weight (i : I) : ℝ :=
  Real.sqrt (A.dimension i : ℝ) * A.eigenvector i


-- @@ L2607-2610 verbatim
theorem weight_pos (i : I) : 0 < A.weight i := by
  exact mul_pos
    (Real.sqrt_pos.2 (by exact_mod_cast A.dimension_pos i))
    (A.eigenvector_pos i)


-- @@ L2612-2613 verbatim
/-- The sum of the positive vertex weights used to normalize the graph amplitudes. -/
def normalization : ℝ := ∑ i, A.weight i


-- @@ L2615-2617 verbatim
theorem normalization_pos [Nonempty I] : 0 < A.normalization := by
  unfold normalization
  exact Finset.sum_pos (fun i _ => A.weight_pos i) Finset.univ_nonempty


-- @@ L2619-2646 verbatim
theorem sqrt_dimension_mul_symmetric_edge (target source : I) :
    Real.sqrt (A.dimension source : ℝ) *
        Real.sqrt
          (A.probability source target * A.probability target source) =
      A.probability target source * Real.sqrt (A.dimension target : ℝ) := by
  have hs : 0 ≤ (A.dimension source : ℝ) := Nat.cast_nonneg _
  have ht : 0 ≤ (A.dimension target : ℝ) := Nat.cast_nonneg _
  have hpst := A.probability_nonneg source target
  have hpts := A.probability_nonneg target source
  have hsquare :
      (Real.sqrt (A.dimension source : ℝ) *
        Real.sqrt
          (A.probability source target * A.probability target source)) ^ 2 =
      (A.probability target source *
        Real.sqrt (A.dimension target : ℝ)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hs,
      Real.sq_sqrt (mul_nonneg hpst hpts),
      mul_pow, Real.sq_sqrt ht]
    have hb := A.balance target source
    nlinarith
  nlinarith [Real.sqrt_nonneg (A.dimension source : ℝ),
    Real.sqrt_nonneg
      (A.probability source target * A.probability target source),
    Real.sqrt_nonneg (A.dimension target : ℝ),
    mul_nonneg hpts (Real.sqrt_nonneg (A.dimension target : ℝ)),
    mul_nonneg (Real.sqrt_nonneg (A.dimension source : ℝ))
      (Real.sqrt_nonneg
        (A.probability source target * A.probability target source))]


-- @@ L2648-2692 verbatim
theorem weighted_eigenvector_equation (source : I) :
    (∑ target, A.probability target source * A.weight target) =
      A.eigenvalue * A.weight source := by
  calc
    (∑ target, A.probability target source * A.weight target) =
        ∑ target,
          Real.sqrt (A.dimension source : ℝ) *
            (Real.sqrt
              (A.probability source target *
                A.probability target source) * A.eigenvector target) := by
          apply Finset.sum_congr rfl
          intro target _
          change
            A.probability target source *
                (Real.sqrt (A.dimension target : ℝ) *
                  A.eigenvector target) = _
          calc
            A.probability target source *
                (Real.sqrt (A.dimension target : ℝ) *
                  A.eigenvector target) =
                (A.probability target source *
                  Real.sqrt (A.dimension target : ℝ)) *
                    A.eigenvector target := by ring
            _ = (Real.sqrt (A.dimension source : ℝ) *
                  Real.sqrt
                    (A.probability source target *
                      A.probability target source)) *
                    A.eigenvector target := by
                  rw [A.sqrt_dimension_mul_symmetric_edge target source]
            _ = _ := by ring
    _ = Real.sqrt (A.dimension source : ℝ) *
          (∑ target,
            Real.sqrt
              (A.probability source target *
                A.probability target source) * A.eigenvector target) := by
          rw [Finset.mul_sum]
    _ = A.eigenvalue * A.weight source := by
          rw [A.eigenvector_equation source]
          change
            Real.sqrt (A.dimension source : ℝ) *
                (A.eigenvalue * A.eigenvector source) =
              A.eigenvalue *
                (Real.sqrt (A.dimension source : ℝ) *
                  A.eigenvector source)
          ring


-- @@ L2694-2696 verbatim
/-- The square root of the vertex weight divided by the total weight. -/
def amplitude (i : I) : ℝ :=
  Real.sqrt (A.weight i / A.normalization)


-- @@ L2698-2701 verbatim
theorem amplitude_pos [Nonempty I] (i : I) : 0 < A.amplitude i := by
  unfold amplitude
  exact Real.sqrt_pos.2
    (div_pos (A.weight_pos i) A.normalization_pos)


-- @@ L2703-2707 verbatim
theorem amplitude_sq [Nonempty I] (i : I) :
    A.amplitude i ^ 2 = A.weight i / A.normalization := by
  unfold amplitude
  exact Real.sq_sqrt
    (div_nonneg (A.weight_pos i).le A.normalization_pos.le)


-- @@ L2709-2713 verbatim
theorem amplitude_sq_sum [Nonempty I] :
    (∑ i, A.amplitude i ^ 2) = 1 := by
  simp_rw [A.amplitude_sq]
  rw [← Finset.sum_div]
  exact div_self A.normalization_pos.ne'


-- @@ L2715-2732 verbatim
theorem amplitude_eigenvector_equation [Nonempty I] (source : I) :
    (∑ target,
      A.probability target source * A.amplitude target ^ 2) =
      A.eigenvalue * A.amplitude source ^ 2 := by
  simp_rw [A.amplitude_sq]
  calc
    (∑ target,
      A.probability target source *
        (A.weight target / A.normalization)) =
        (∑ target, A.probability target source * A.weight target) /
          A.normalization := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro target _
            ring
    _ = A.eigenvalue * (A.weight source / A.normalization) := by
          rw [A.weighted_eigenvector_equation source]
          ring


-- @@ L2734-2747 verbatim
theorem fibre_orthogonal {i j : I} (hij : i ≠ j) (x y : X) :
    (A.fibre i x)ᵀ * A.fibre j y = 0 := by
  have hleft : (A.fibre i x)ᵀ * A.block i = (A.fibre i x)ᵀ := by
    have h := congrArg Matrix.transpose (A.fibre_support i x)
    simpa only [Matrix.transpose_mul, A.block_symmetric i] using h
  calc
    (A.fibre i x)ᵀ * A.fibre j y =
        ((A.fibre i x)ᵀ * A.block i) *
          (A.block j * A.fibre j y) := by
            rw [hleft, A.fibre_support j y]
    _ = (A.fibre i x)ᵀ *
          ((A.block i * A.block j) * A.fibre j y) := by
            simp only [Matrix.mul_assoc]
    _ = 0 := by rw [A.block_orthogonal i j hij]; simp only [Matrix.zero_mul, Matrix.mul_zero]


-- @@ L2749-2751 verbatim
/-- The sum of the fibre matrices weighted by their normalized amplitudes. -/
def combinedFibre (x : X) : Matrix (Fin D) (Fin d) ℝ :=
  ∑ i, A.amplitude i • A.fibre i x


-- @@ L2753-2764 verbatim
private theorem weighted_matrix_transpose_mul_metriccodes2_81758290
    {ι m n : Type*} [Fintype ι] [Fintype m]
    (c e : ι → ℝ) (U V : ι → Matrix m n ℝ) :
    (∑ i, c i • U i)ᵀ * (∑ j, e j • V j) =
      ∑ i, ∑ j, (c i * e j) • ((U i)ᵀ * V j) := by
  classical
  simp only [Matrix.transpose_sum, Matrix.transpose_smul,
    Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul,
    Matrix.mul_smul]
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]


-- @@ L2766-2783 verbatim
theorem combinedFibre_isometry [Nonempty I] (x : X) :
    (A.combinedFibre x)ᵀ * A.combinedFibre x = 1 := by
  classical
  unfold combinedFibre
  rw [weighted_matrix_transpose_mul_metriccodes2_81758290]
  have hcross (i j : I) :
      (A.fibre i x)ᵀ * A.fibre j x =
        if i = j then 1 else 0 := by
    split_ifs with h
    · subst j
      exact A.fibre_isometry i x
    · exact A.fibre_orthogonal h x x
  simp_rw [hcross]
  simp only [smul_ite, smul_zero]
  have hsum := A.amplitude_sq_sum
  simpa only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, ← Finset.sum_smul, pow_two,
    one_smul] using
    congrArg (fun r : ℝ => r • (1 : Matrix (Fin d) (Fin d) ℝ)) hsum


-- @@ L2785-2787 verbatim
/-- The projection matrix obtained by multiplying the combined fibre matrix by its transpose. -/
def combinedProjection (x : X) : Matrix (Fin D) (Fin D) ℝ :=
  A.combinedFibre x * (A.combinedFibre x)ᵀ


-- @@ L2789-2791 verbatim
theorem combinedProjection_symmetric (x : X) :
    (A.combinedProjection x)ᵀ = A.combinedProjection x := by
  simp only [combinedProjection, Matrix.transpose_mul, Matrix.transpose_transpose]


-- @@ L2793-2799 verbatim
theorem combinedProjection_idempotent [Nonempty I] (x : X) :
    A.combinedProjection x * A.combinedProjection x =
      A.combinedProjection x := by
  unfold combinedProjection
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (A.combinedFibre x)ᵀ,
    A.combinedFibre_isometry x]
  simp only [Matrix.one_mul]


-- @@ L2801-2806 verbatim
theorem combinedProjection_trace [Nonempty I] (x : X) :
    Matrix.trace (A.combinedProjection x) = (d : ℝ) := by
  unfold combinedProjection
  rw [Matrix.trace_mul_comm, A.combinedFibre_isometry x,
    Matrix.trace_one]
  simp only [Fintype.card_fin]


-- @@ L2808-2813 verbatim
/-- The projection family assembled from the weighted orthogonal fibres. -/
def projectionFamily [Nonempty I] : MetricCodes.ProjectionFamily X D d where
  projection := A.combinedProjection
  symmetric := A.combinedProjection_symmetric
  idempotent := A.combinedProjection_idempotent
  trace_eq := A.combinedProjection_trace


-- @@ L2815-2819 verbatim
/-- The edge-channel coefficient scaled by the target-to-source amplitude ratio and the square
root of the eigenvalue. -/
def edgeCoefficient (target source : I) : ℝ :=
  Real.sqrt (A.probability target source) * A.amplitude target /
    (Real.sqrt A.eigenvalue * A.amplitude source)


-- @@ L2821-2828 verbatim
theorem edgeCoefficient_sq (target source : I) :
    A.edgeCoefficient target source ^ 2 =
      A.probability target source * A.amplitude target ^ 2 /
        (A.eigenvalue * A.amplitude source ^ 2) := by
  unfold edgeCoefficient
  rw [div_pow, mul_pow, mul_pow,
    Real.sq_sqrt (A.probability_nonneg target source),
    Real.sq_sqrt A.eigenvalue_pos.le]


-- @@ L2830-2836 verbatim
theorem edgeCoefficient_sq_sum [Nonempty I] (source : I) :
    (∑ target, A.edgeCoefficient target source ^ 2) = 1 := by
  simp_rw [A.edgeCoefficient_sq]
  rw [← Finset.sum_div, A.amplitude_eigenvector_equation]
  exact div_self
    (mul_ne_zero A.eigenvalue_pos.ne'
      (pow_ne_zero _ (A.amplitude_pos source).ne'))


-- @@ L2838-2840 verbatim
/-- The sum of all edge channels weighted by their edge coefficients. -/
def assembledChannel : Matrix (Fin Q) (Fin D) ℝ :=
  ∑ e : I × I, A.edgeCoefficient e.1 e.2 • A.channel e.1 e.2


-- @@ L2842-2853 verbatim
theorem edgeCoefficient_smul_channelGram
    (target source : I) :
    (A.edgeCoefficient target source ^ 2) •
      (if 0 < A.probability target source then A.block source else 0) =
        (A.edgeCoefficient target source ^ 2) • A.block source := by
  split_ifs with hp
  · rfl
  · have hzero : A.probability target source = 0 :=
      le_antisymm (le_of_not_gt hp)
        (A.probability_nonneg target source)
    simp only [edgeCoefficient, hzero, Real.sqrt_zero, zero_mul, zero_div, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, smul_zero, zero_smul]


-- @@ L2855-2891 verbatim
theorem assembledChannel_isometry [Nonempty I] :
    (A.assembledChannel)ᵀ * A.assembledChannel =
      (1 : Matrix (Fin D) (Fin D) ℝ) := by
  classical
  unfold assembledChannel
  rw [weighted_matrix_transpose_mul_metriccodes2_81758290]
  have hcross (e f : I × I) :
      (A.channel e.1 e.2)ᵀ * A.channel f.1 f.2 =
        if e = f then
          if 0 < A.probability e.1 e.2 then A.block e.2 else 0
        else 0 := by
    by_cases hef : e = f
    · subst f
      simp only [A.channel_isometry, ↓reduceIte]
    · simp only [A.channel_orthogonal e.1 e.2 f.1 f.2 (by simpa using hef), hef, ↓reduceIte]
  simp_rw [hcross]
  simp only [smul_ite, smul_zero]
  simp only [Fintype.sum_ite_eq]
  have hedge (target source : I) :
      (if 0 < A.probability target source then
        (A.edgeCoefficient target source ^ 2) • A.block source
      else 0) =
        (A.edgeCoefficient target source ^ 2) • A.block source := by
    simpa only [ite_eq_left_iff, not_lt, smul_ite, smul_zero] using
      A.edgeCoefficient_smul_channelGram target source
  simp_rw [← pow_two, hedge]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  calc
    (∑ source, ∑ target,
      A.edgeCoefficient target source ^ 2 • A.block source) =
        ∑ source,
          (∑ target, A.edgeCoefficient target source ^ 2) •
            A.block source := by
              simp_rw [Finset.sum_smul]
    _ = ∑ source, A.block source := by
          simp_rw [A.edgeCoefficient_sq_sum, one_smul]
    _ = 1 := A.block_complete


-- @@ L2893-2906 verbatim
theorem edgeCoefficient_axis_scalar [Nonempty I]
    (target source : I) :
    A.edgeCoefficient target source * A.amplitude target *
        Real.sqrt (A.probability target source) =
      A.probability target source * A.amplitude target ^ 2 /
        (Real.sqrt A.eigenvalue * A.amplitude source) := by
  unfold edgeCoefficient
  have hp := A.probability_nonneg target source
  have he : Real.sqrt A.eigenvalue ≠ 0 :=
    (Real.sqrt_pos.2 A.eigenvalue_pos).ne'
  have ha : A.amplitude source ≠ 0 :=
    (A.amplitude_pos source).ne'
  field_simp
  nlinarith [Real.sq_sqrt hp]


-- @@ L2908-2920 verbatim
theorem edgeCoefficient_axis_sum [Nonempty I] (source : I) :
    (∑ target,
      A.edgeCoefficient target source * A.amplitude target *
        Real.sqrt (A.probability target source)) =
      Real.sqrt A.eigenvalue * A.amplitude source := by
  simp_rw [A.edgeCoefficient_axis_scalar]
  rw [← Finset.sum_div, A.amplitude_eigenvector_equation]
  have he : Real.sqrt A.eigenvalue ≠ 0 :=
    (Real.sqrt_pos.2 A.eigenvalue_pos).ne'
  have ha : A.amplitude source ≠ 0 :=
    (A.amplitude_pos source).ne'
  field_simp
  nlinarith [Real.sq_sqrt A.eigenvalue_pos.le]


-- @@ L2922-2974 verbatim
theorem assembledChannel_axis [Nonempty I] (x : X) :
    (A.assembledChannel)ᵀ * A.axis x * A.combinedFibre x =
      Real.sqrt A.eigenvalue • A.combinedFibre x := by
  classical
  unfold assembledChannel combinedFibre
  simp only [Matrix.transpose_sum, Matrix.transpose_smul,
    Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul,
    Matrix.mul_smul]
  simp_rw [A.channel_axis]
  simp only [smul_ite, smul_zero]
  simp_rw [Fintype.sum_prod_type]
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [smul_ite, smul_zero]
  calc
    (∑ target, ∑ j, ∑ source,
        if target = j then
          A.amplitude j •
            (A.edgeCoefficient target source *
              Real.sqrt (A.probability target source)) •
                A.fibre source x
        else 0) =
        ∑ target, ∑ source,
          (A.amplitude target *
            (A.edgeCoefficient target source *
              Real.sqrt (A.probability target source))) •
                A.fibre source x := by
          apply Finset.sum_congr rfl
          intro target _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro source _
          simp only [smul_smul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    _ = ∑ source,
          (Real.sqrt A.eigenvalue * A.amplitude source) •
            A.fibre source x := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro source _
          rw [← Finset.sum_smul]
          congr 1
          calc
            (∑ target,
              A.amplitude target *
                (A.edgeCoefficient target source *
                  Real.sqrt (A.probability target source))) =
                ∑ target,
                  A.edgeCoefficient target source * A.amplitude target *
                    Real.sqrt (A.probability target source) := by
                    apply Finset.sum_congr rfl
                    intro target _
                    ring
            _ = _ := A.edgeCoefficient_axis_sum source


-- @@ L2976-2981 verbatim
theorem assembledChannel_axis_projection [Nonempty I] (x : X) :
    (A.assembledChannel)ᵀ * A.axis x * A.combinedProjection x =
      Real.sqrt A.eigenvalue • A.combinedProjection x := by
  unfold combinedProjection
  rw [← Matrix.mul_assoc,
    A.assembledChannel_axis x, Matrix.smul_mul]


-- @@ L2983-2989 verbatim
theorem projection_axis_transpose_assembled [Nonempty I] (x : X) :
    A.combinedProjection x * (A.axis x)ᵀ * A.assembledChannel =
      Real.sqrt A.eigenvalue • A.combinedProjection x := by
  have h := congrArg Matrix.transpose
    (A.assembledChannel_axis_projection x)
  simpa only [Matrix.mul_assoc, Matrix.transpose_mul, A.combinedProjection_symmetric x,
    Matrix.transpose_transpose, Matrix.transpose_smul] using h


-- @@ L2991-2993 verbatim
/-- The lift used in the metric-code argument. -/
def lift (x : X) : Matrix (Fin Q) (Fin D) ℝ :=
  A.axis x * A.combinedProjection x


-- @@ L2995-2997 verbatim
/-- The bulk used in the metric-code argument. -/
def bulk (x : X) : Matrix (Fin Q) (Fin D) ℝ :=
  A.assembledChannel * A.combinedProjection x


-- @@ L2999-3001 verbatim
/-- The remainder used in the metric-code argument. -/
def remainder (x : X) : Matrix (Fin Q) (Fin D) ℝ :=
  A.lift x - Real.sqrt A.eigenvalue • A.bulk x


-- @@ L3003-3011 verbatim
theorem lift_transpose_mul_lift (x y : X) :
    (A.lift x)ᵀ * A.lift y =
      A.correlation x y •
        (A.combinedProjection x * A.combinedProjection y) := by
  unfold lift
  rw [Matrix.transpose_mul, A.combinedProjection_symmetric x,
    Matrix.mul_assoc, ← Matrix.mul_assoc (A.axis x)ᵀ,
    A.axis_inner x y]
  simp only [Algebra.smul_mul_assoc, one_mul, Algebra.mul_smul_comm]


-- @@ L3013-3021 verbatim
theorem bulk_transpose_mul_bulk [Nonempty I] (x y : X) :
    (A.bulk x)ᵀ * A.bulk y =
      A.combinedProjection x * A.combinedProjection y := by
  unfold bulk
  rw [Matrix.transpose_mul, A.combinedProjection_symmetric x,
    Matrix.mul_assoc,
    ← Matrix.mul_assoc (A.assembledChannel)ᵀ,
    A.assembledChannel_isometry]
  simp only [one_mul]


-- @@ L3023-3036 verbatim
theorem lift_transpose_mul_bulk [Nonempty I] (x y : X) :
    (A.lift x)ᵀ * A.bulk y =
      Real.sqrt A.eigenvalue •
        (A.combinedProjection x * A.combinedProjection y) := by
  unfold lift bulk
  calc
    (A.axis x * A.combinedProjection x)ᵀ *
        (A.assembledChannel * A.combinedProjection y) =
      (A.combinedProjection x * (A.axis x)ᵀ *
        A.assembledChannel) * A.combinedProjection y := by
          simp only [Matrix.transpose_mul, A.combinedProjection_symmetric x, Matrix.mul_assoc]
    _ = _ := by
      rw [A.projection_axis_transpose_assembled x,
        Matrix.smul_mul]


-- @@ L3038-3052 verbatim
theorem bulk_transpose_mul_lift [Nonempty I] (x y : X) :
    (A.bulk x)ᵀ * A.lift y =
      Real.sqrt A.eigenvalue •
        (A.combinedProjection x * A.combinedProjection y) := by
  unfold bulk lift
  calc
    (A.assembledChannel * A.combinedProjection x)ᵀ *
        (A.axis y * A.combinedProjection y) =
      A.combinedProjection x *
        ((A.assembledChannel)ᵀ * A.axis y *
          A.combinedProjection y) := by
          simp only [Matrix.transpose_mul, A.combinedProjection_symmetric x, Matrix.mul_assoc]
    _ = _ := by
      rw [A.assembledChannel_axis_projection y,
        Matrix.mul_smul]


-- @@ L3054-3082 verbatim
theorem remainder_transpose_mul [Nonempty I] (x y : X) :
    (A.remainder x)ᵀ * A.remainder y =
      (A.correlation x y - A.eigenvalue) •
        (A.combinedProjection x * A.combinedProjection y) := by
  unfold remainder
  simp only [Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
    Matrix.mul_smul]
  rw [A.lift_transpose_mul_lift x y,
    A.lift_transpose_mul_bulk x y,
    A.bulk_transpose_mul_lift x y,
    A.bulk_transpose_mul_bulk x y]
  have hroot := Real.sq_sqrt A.eigenvalue_pos.le
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  calc
    A.correlation x y *
          (A.combinedProjection x * A.combinedProjection y) i j -
        Real.sqrt A.eigenvalue *
          (Real.sqrt A.eigenvalue *
            (A.combinedProjection x * A.combinedProjection y) i j) -
        Real.sqrt A.eigenvalue *
          (Real.sqrt A.eigenvalue *
              (A.combinedProjection x * A.combinedProjection y) i j -
            Real.sqrt A.eigenvalue *
              (A.combinedProjection x * A.combinedProjection y) i j) =
        (A.correlation x y - Real.sqrt A.eigenvalue ^ 2) *
          (A.combinedProjection x * A.combinedProjection y) i j := by ring
    _ = _ := by rw [hroot]


-- @@ L3084-3087 verbatim
/-- The Euclidean vector of matrix entries used for the graph's Hilbert–Schmidt features. -/
def matrixFeature (M : Matrix (Fin Q) (Fin D) ℝ) :
    EuclideanSpace ℝ (Fin Q × Fin D) :=
  WithLp.toLp 2 (fun i : Fin Q × Fin D => M i.1 i.2)


-- @@ L3089-3096 verbatim
theorem matrixFeature_inner (M N : Matrix (Fin Q) (Fin D) ℝ) :
    ⟪matrixFeature M, matrixFeature N⟫_ℝ =
      Matrix.trace (Mᵀ * N) := by
  rw [PiLp.inner_apply]
  simp only [matrixFeature, WithLp.ofLp_toLp, Real.inner_apply,
    Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]


-- @@ L3098-3101 verbatim
/-- The Euclidean matrix-entry feature of the graph remainder at `x`. -/
def remainderFeature (x : X) :
    EuclideanSpace ℝ (Fin Q × Fin D) :=
  matrixFeature (A.remainder x)


-- @@ L3103-3109 verbatim
theorem remainderFeature_inner [Nonempty I] (x y : X) :
    ⟪A.remainderFeature x, A.remainderFeature y⟫_ℝ =
      (A.correlation x y - A.eigenvalue) *
        (A.projectionFamily).overlap x y := by
  unfold remainderFeature
  rw [matrixFeature_inner, A.remainder_transpose_mul]
  simp only [Matrix.trace_smul, smul_eq_mul, ProjectionFamily.overlap, projectionFamily]


-- @@ L3111-3114 verbatim
theorem ambientDimension_eq_sum :
    (D : ℝ) = ∑ i, (A.dimension i : ℝ) := by
  have h := congrArg Matrix.trace A.block_complete
  simpa only [Matrix.trace_one, Fintype.card_fin, Matrix.trace_sum, A.block_trace] using h.symm


-- @@ L3116-3132 verbatim
theorem code_bound [Nonempty I]
    (C : Finset X) {s : ℝ}
    (hd : 0 < d)
    (hs : s < 1)
    (hgap : s < A.eigenvalue)
    (hdiag : ∀ x ∈ C, A.correlation x x = 1)
    (hsep : ∀ x ∈ C, ∀ y ∈ C,
      x ≠ y → A.correlation x y ≤ s) :
    (C.card : ℝ) ≤
      ((1 - s) / (A.eigenvalue - s)) *
        ((∑ i, (A.dimension i : ℝ)) / (d : ℝ)) := by
  have h := MetricCodes.projection_certificate
    A.projectionFamily C A.correlation A.remainderFeature
    hd hs hgap hdiag hsep
    (fun x _ y _ => A.remainderFeature_inner x y)
  rw [A.ambientDimension_eq_sum] at h
  exact h


-- @@ L3134-3134 verbatim
end Data


-- @@ L3136-3136 verbatim
end HigherProjectionGraph


-- @@ L3138-3138 verbatim
end


-- @@ L3140-3140 verbatim
namespace Spherical


-- @@ L3142-3142 verbatim
section


-- @@ L3144-3144 verbatim
open scoped BigOperators InnerProductSpace Matrix


-- @@ L3146-3146 verbatim
namespace HigherProjectionInstantiation


-- @@ L3148-3150 verbatim
/-- The sphere point used in the spherical-code argument. -/
abbrev SpherePoint (n : ℕ) :=
  {x : SpherePacking.Euclidean n // ‖x‖ = 1}


-- @@ L3152-3212 verbatim
/-- Data encoding the realized hilbert graph construction. -/
structure RealizedHilbertGraph
    (I X E V F : Type*) [Fintype I] [DecidableEq I]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] where
  /-- The dimension component. -/
  dimension : I → ℕ
  dimension_pos : ∀ i, 0 < dimension i
  /-- The block component. -/
  block : I → V →ₗ[ℝ] V
  block_adjoint : ∀ i, (block i).adjoint = block i
  block_idempotent : ∀ i, (block i).comp (block i) = block i
  block_orthogonal : ∀ i j, i ≠ j → (block i).comp (block j) = 0
  block_complete : (∑ i, block i) = LinearMap.id
  block_trace : ∀ i, LinearMap.trace ℝ V (block i) = (dimension i : ℝ)
  /-- The fibre component. -/
  fibre : I → X → E →ₗᵢ[ℝ] V
  fibre_support : ∀ i x,
    (block i).comp (fibre i x).toLinearMap = (fibre i x).toLinearMap
  /-- The correlation component. -/
  correlation : X → X → ℝ
  /-- The axis component. -/
  axis : X → V →ₗ[ℝ] F
  axis_inner : ∀ x y,
    (axis x).adjoint.comp (axis y) =
      correlation x y • (LinearMap.id : V →ₗ[ℝ] V)
  /-- The probability component. -/
  probability : I → I → ℝ
  probability_nonneg : ∀ target source, 0 ≤ probability target source
  balance : ∀ target source,
    (dimension target : ℝ) * probability target source =
      (dimension source : ℝ) * probability source target
  /-- The channel component. -/
  channel : I → I → V →ₗ[ℝ] F
  channel_isometry : ∀ target source,
    (channel target source).adjoint.comp (channel target source) =
      if 0 < probability target source then block source else 0
  channel_orthogonal : ∀ target source target' source',
    (target, source) ≠ (target', source') →
      (channel target source).adjoint.comp
        (channel target' source') = 0
  channel_axis : ∀ target source j x,
    (channel target source).adjoint.comp
        ((axis x).comp (fibre j x).toLinearMap) =
      if target = j then
        Real.sqrt (probability target source) • (fibre source x).toLinearMap
      else 0
  /-- The eigenvalue component. -/
  eigenvalue : ℝ
  eigenvalue_pos : 0 < eigenvalue
  /-- The eigenvector component. -/
  eigenvector : I → ℝ
  eigenvector_pos : ∀ i, 0 < eigenvector i
  eigenvector_unit : (∑ i, eigenvector i ^ 2) = 1
  eigenvector_equation : ∀ i,
    (∑ j, Real.sqrt (probability i j * probability j i) * eigenvector j) =
      eigenvalue * eigenvector i


-- @@ L3214-3214 verbatim
namespace RealizedHilbertGraph


-- @@ L3216-3216 verbatim
variable {I X E V F : Type*} [Fintype I] [DecidableEq I]

-- @@ L3217-3218 verbatim
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]


-- @@ L3220-3221 verbatim
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]


-- @@ L3223-3224 verbatim
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]


-- @@ L3226-3232 verbatim
/-- The standard orthonormal basis indexed by the finite dimension of the real inner product
space. -/
abbrev euclideanBasis (T : Type*)
    [NormedAddCommGroup T] [InnerProductSpace ℝ T]
    [FiniteDimensional ℝ T] :
    OrthonormalBasis (Fin (Module.finrank ℝ T)) ℝ T :=
  stdOrthonormalBasis ℝ T


-- @@ L3234-3244 verbatim
/-- The matrix of a linear map in the standard orthonormal bases of its source and target. -/
def coordinateMatrix {U T : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [FiniteDimensional ℝ U]
    [NormedAddCommGroup T] [InnerProductSpace ℝ T]
    [FiniteDimensional ℝ T]
    (f : U →ₗ[ℝ] T) :
    Matrix (Fin (Module.finrank ℝ T))
      (Fin (Module.finrank ℝ U)) ℝ :=
  LinearMap.toMatrix (euclideanBasis U).toBasis
    (euclideanBasis T).toBasis f


-- @@ L3246-3257 verbatim
private theorem coordinateMatrix_adjoint_metriccodes2_851911c7 {U T : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [FiniteDimensional ℝ U]
    [NormedAddCommGroup T] [InnerProductSpace ℝ T]
    [FiniteDimensional ℝ T]
    (f : U →ₗ[ℝ] T) :
    coordinateMatrix f.adjoint = (coordinateMatrix
      f)ᵀ := by
  simpa only [coordinateMatrix,
    Matrix.conjTranspose_eq_transpose_of_trivial] using
    LinearMap.toMatrix_adjoint (euclideanBasis U)
      (euclideanBasis T) f


-- @@ L3259-3272 verbatim
private theorem coordinateMatrix_comp_metriccodes2_851911c7 {U T Z : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [FiniteDimensional ℝ U]
    [NormedAddCommGroup T] [InnerProductSpace ℝ T]
    [FiniteDimensional ℝ T]
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    [FiniteDimensional ℝ Z]
    (f : T →ₗ[ℝ] Z) (g : U →ₗ[ℝ] T) :
    coordinateMatrix (f.comp g) =
      coordinateMatrix f * coordinateMatrix g := by
  exact LinearMap.toMatrix_comp
    (euclideanBasis U).toBasis (euclideanBasis
      T).toBasis
    (euclideanBasis Z).toBasis f g


-- @@ L3274-3278 verbatim
private theorem coordinateMatrix_id_metriccodes2_851911c7 {T : Type*}
    [NormedAddCommGroup T] [InnerProductSpace ℝ T]
    [FiniteDimensional ℝ T] :
    coordinateMatrix (LinearMap.id : T →ₗ[ℝ] T) = 1 := by
  exact LinearMap.toMatrix_id (euclideanBasis T).toBasis


-- @@ L3280-3352 verbatim
/-- The to finite data used in the spherical-code argument. -/
def toFiniteData (G : RealizedHilbertGraph I X E V F) :
    MetricCodes.HigherProjectionGraph.Data I X
      (Module.finrank ℝ V) (Module.finrank ℝ E)
      (Module.finrank ℝ F) where
  dimension := G.dimension
  dimension_pos := G.dimension_pos
  block i := coordinateMatrix (G.block i)
  block_symmetric i := by
    rw [← coordinateMatrix_adjoint_metriccodes2_851911c7, G.block_adjoint]
  block_idempotent i := by
    rw [← coordinateMatrix_comp_metriccodes2_851911c7, G.block_idempotent]
  block_orthogonal i j hij := by
    rw [← coordinateMatrix_comp_metriccodes2_851911c7, G.block_orthogonal i j hij]
    simp only [coordinateMatrix, map_zero]
  block_complete := by
    change
      (∑ i, LinearMap.toMatrix
        (euclideanBasis V).toBasis (euclideanBasis
          V).toBasis
        (G.block i)) = 1
    rw [← map_sum, G.block_complete,
      LinearMap.toMatrix_id]
  block_trace i := by
    unfold coordinateMatrix
    rw [← LinearMap.trace_eq_matrix_trace ℝ
      (euclideanBasis V).toBasis]
    exact G.block_trace i
  fibre i x := coordinateMatrix (G.fibre i x).toLinearMap
  fibre_isometry i x := by
    rw [← coordinateMatrix_adjoint_metriccodes2_851911c7, ←
      coordinateMatrix_comp_metriccodes2_851911c7,
      (G.fibre i x).adjoint_comp_self', coordinateMatrix_id_metriccodes2_851911c7]
  fibre_support i x := by
    rw [← coordinateMatrix_comp_metriccodes2_851911c7, G.fibre_support]
  correlation := G.correlation
  axis x := coordinateMatrix (G.axis x)
  axis_inner x y := by
    rw [← coordinateMatrix_adjoint_metriccodes2_851911c7, ←
      coordinateMatrix_comp_metriccodes2_851911c7,
      G.axis_inner]
    change
      LinearMap.toMatrix (euclideanBasis V).toBasis
        (euclideanBasis V).toBasis
        (G.correlation x y • (LinearMap.id : V →ₗ[ℝ] V)) = _
    rw [map_smul, LinearMap.toMatrix_id]
  probability := G.probability
  probability_nonneg := G.probability_nonneg
  balance := G.balance
  channel target source :=
    coordinateMatrix (G.channel target source)
  channel_isometry target source := by
    rw [← coordinateMatrix_adjoint_metriccodes2_851911c7, ←
      coordinateMatrix_comp_metriccodes2_851911c7,
      G.channel_isometry]
    split_ifs <;> simp [coordinateMatrix]
  channel_orthogonal target source target' source' h := by
    rw [← coordinateMatrix_adjoint_metriccodes2_851911c7, ←
      coordinateMatrix_comp_metriccodes2_851911c7,
      G.channel_orthogonal target source target' source' h]
    simp only [coordinateMatrix, map_zero]
  channel_axis target source j x := by
    rw [← coordinateMatrix_adjoint_metriccodes2_851911c7, ←
      coordinateMatrix_comp_metriccodes2_851911c7,
      ← coordinateMatrix_comp_metriccodes2_851911c7, LinearMap.comp_assoc,
      G.channel_axis]
    split_ifs <;> simp [coordinateMatrix]
  eigenvalue := G.eigenvalue
  eigenvalue_pos := G.eigenvalue_pos
  eigenvector := G.eigenvector
  eigenvector_pos := G.eigenvector_pos
  eigenvector_unit := G.eigenvector_unit
  eigenvector_equation := G.eigenvector_equation


-- @@ L3354-3354 verbatim
end RealizedHilbertGraph


-- @@ L3356-3367 verbatim
/-- The points of a spherical code bundled with their unit-norm proofs. -/
def codePoints {n : ℕ} {s : ℝ}
    (C : SpherePacking.SphericalCode n s) :
    Finset (SpherePoint n) := by
  classical
  let e : {x // x ∈ C.points} ↪ SpherePoint n :=
    { toFun := fun x => ⟨x.val, C.unit_norm x.val x.property⟩
      inj' := by
        intro x y h
        apply Subtype.ext
        exact congrArg (fun z : SpherePoint n => z.val) h }
  exact C.points.attach.map e


-- @@ L3369-3373 verbatim
@[simp] theorem codePoints_card {n : ℕ} {s : ℝ}
    (C : SpherePacking.SphericalCode n s) :
    (codePoints C).card = C.points.card := by
  classical
  simp only [codePoints, Finset.card_map, Finset.card_attach]


-- @@ L3375-3390 verbatim
theorem mem_codePoints_iff {n : ℕ} {s : ℝ}
    (C : SpherePacking.SphericalCode n s) (x : SpherePoint n) :
    x ∈ codePoints C ↔ x.val ∈ C.points := by
  classical
  constructor
  · intro hx
    change x ∈ C.points.attach.map _ at hx
    obtain ⟨y, _, hy⟩ := Finset.mem_map.mp hx
    have hval : y.val = x.val := congrArg Subtype.val hy
    exact hval ▸ y.property
  · intro hx
    change x ∈ C.points.attach.map _
    refine Finset.mem_map.mpr ⟨⟨x.val, hx⟩, ?_, ?_⟩
    · simp only [Finset.mem_attach]
    · apply Subtype.ext
      rfl


-- @@ L3392-3417 verbatim
theorem sphericalCode_bound_of_realized_graph
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {n D d Q : ℕ}
    (A : MetricCodes.HigherProjectionGraph.Data
      I (SpherePoint n) D d Q)
    (hinner : ∀ x y : SpherePoint n,
      A.correlation x y =
        ⟪(x.val : SpherePacking.Euclidean n), y.val⟫_ℝ)
    {s : ℝ} (hd : 0 < d) (hs : s < 1)
    (hgap : s < A.eigenvalue)
    (C : SpherePacking.SphericalCode n s) :
    (C.points.card : ℝ) ≤
      ((1 - s) / (A.eigenvalue - s)) *
        ((∑ i, (A.dimension i : ℝ)) / (d : ℝ)) := by
  have h := A.code_bound (codePoints C) hd hs hgap
    (fun x _ => by
      rw [hinner]
      simp only [inner_self_eq_norm_sq_to_K, x.property, Real.ringHom_apply, one_pow])
    (fun x hx y hy hxy => by
      rw [hinner]
      apply C.inner_le x.val ((mem_codePoints_iff C x).mp hx)
        y.val ((mem_codePoints_iff C y).mp hy)
      intro h
      apply hxy
      exact Subtype.ext h)
  simpa only [codePoints_card] using h


-- @@ L3419-3419 verbatim
end HigherProjectionInstantiation


-- @@ L3421-3421 verbatim
end


-- @@ L3423-3423 verbatim
section


-- @@ L3425-3425 verbatim
open scoped BigOperators InnerProductSpace


-- @@ L3427-3427 verbatim
namespace HigherYoungGraphAssembly


-- @@ L3429-3429 verbatim
variable {I : Type*} [Fintype I] [DecidableEq I]

-- @@ L3430-3433 verbatim
variable (V : I → Type*)
  [∀ i, NormedAddCommGroup (V i)]
  [∀ i, InnerProductSpace ℝ (V i)]
  [∀ i, FiniteDimensional ℝ (V i)]


-- @@ L3435-3436 verbatim
/-- The vertex ambient used in the spherical-code argument. -/
abbrev VertexAmbient := PiLp 2 V


-- @@ L3438-3462 verbatim
/-- The vertex inclusion used in the spherical-code argument. -/
def vertexInclusion (i : I) : V i →ₗᵢ[ℝ] VertexAmbient V := by
  let f : V i →ₗ[ℝ] VertexAmbient V :=
    { toFun := fun v => PiLp.single 2 i v
      map_add' := by
        intro u v
        exact PiLp.single_add 2 i
      map_smul' := by
        intro c v
        apply PiLp.ext
        intro j
        by_cases h : j = i
        · subst j
          simp only [PiLp.single_eq_same, Real.ringHom_apply, PiLp.smul_apply]
        · simp only [PiLp.ofLp_single, Pi.single_eq_of_ne h, Real.ringHom_apply, PiLp.smul_apply,
            smul_zero]}
  refine f.isometryOfInner ?_
  intro u v
  rw [PiLp.inner_apply, Finset.sum_eq_single i]
  · simp only [LinearMap.coe_mk, AddHom.coe_mk, PiLp.single_eq_same, f]
  · intro j _ hj
    simp only [LinearMap.coe_mk, AddHom.coe_mk, PiLp.ofLp_single, Pi.single_eq_of_ne hj,
      inner_self_eq_norm_sq_to_K, norm_zero, Real.ringHom_apply, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, f]
  · simp only [Finset.mem_univ, not_true_eq_false, IsEmpty.forall_iff]


-- @@ L3464-3468 verbatim
omit [∀ i, FiniteDimensional ℝ (V i)] in
@[simp] theorem vertexInclusion_apply_self (i : I) (v : V i) :
    vertexInclusion V i v i = v := by
  simp only [vertexInclusion, LinearMap.coe_isometryOfInner, LinearMap.coe_mk, AddHom.coe_mk,
    PiLp.single_eq_same]


-- @@ L3470-3475 verbatim
omit [∀ i, FiniteDimensional ℝ (V i)] in
@[simp] theorem vertexInclusion_apply_ne
    {i j : I} (h : j ≠ i) (v : V i) :
    vertexInclusion V i v j = 0 := by
  simp only [vertexInclusion, LinearMap.coe_isometryOfInner, LinearMap.coe_mk, AddHom.coe_mk,
    PiLp.ofLp_single, Pi.single_eq_of_ne h]


-- @@ L3477-3488 verbatim
@[simp] theorem vertexInclusion_adjoint_apply (i : I)
    (v : VertexAmbient V) :
    (vertexInclusion V i).adjoint v = v i := by
  apply ext_inner_left ℝ
  intro u
  rw [LinearMap.adjoint_inner_right, PiLp.inner_apply,
    Finset.sum_eq_single i]
  · simp only [LinearIsometry.coe_toLinearMap, vertexInclusion_apply_self]
  · intro j _ hj
    simp only [LinearIsometry.coe_toLinearMap, vertexInclusion_apply_ne V hj, inner_zero_left]
  · simp only [Finset.mem_univ, not_true_eq_false, LinearIsometry.coe_toLinearMap,
      vertexInclusion_apply_self, IsEmpty.forall_iff]


-- @@ L3490-3492 verbatim
/-- The vertex projection used in the spherical-code argument. -/
def vertexProjection (i : I) : VertexAmbient V →ₗ[ℝ] VertexAmbient V :=
  (vertexInclusion V i).toLinearMap.comp (vertexInclusion V i).adjoint


-- @@ L3494-3498 verbatim
@[simp] theorem vertexProjection_apply_self (i : I)
    (v : VertexAmbient V) :
    vertexProjection V i v i = v i := by
  simp only [vertexProjection, LinearMap.coe_comp, LinearIsometry.coe_toLinearMap,
    Function.comp_apply, vertexInclusion_adjoint_apply, vertexInclusion_apply_self]


-- @@ L3500-3504 verbatim
@[simp] theorem vertexProjection_apply_ne {i j : I} (h : j ≠ i)
    (v : VertexAmbient V) :
    vertexProjection V i v j = 0 := by
  simp only [vertexProjection, LinearMap.coe_comp, LinearIsometry.coe_toLinearMap,
    Function.comp_apply, vertexInclusion_adjoint_apply, vertexInclusion_apply_ne V h]


-- @@ L3506-3509 verbatim
theorem vertexProjection_adjoint (i : I) :
    (vertexProjection V i).adjoint = vertexProjection V i := by
  unfold vertexProjection
  rw [LinearMap.adjoint_comp, LinearMap.adjoint_adjoint]


-- @@ L3511-3518 verbatim
theorem vertexProjection_idempotent (i : I) :
    (vertexProjection V i).comp (vertexProjection V i) =
      vertexProjection V i := by
  ext v j
  by_cases h : j = i
  · subst j
    simp only [LinearMap.coe_comp, Function.comp_apply, vertexProjection_apply_self]
  · simp only [LinearMap.coe_comp, Function.comp_apply, vertexProjection_apply_ne V h]


-- @@ L3520-3528 verbatim
theorem vertexProjection_orthogonal {i j : I} (h : i ≠ j) :
    (vertexProjection V i).comp (vertexProjection V j) = 0 := by
  ext v k
  by_cases hi : k = i
  · subst k
    simp only [LinearMap.coe_comp, Function.comp_apply, vertexProjection_apply_self,
      vertexProjection_apply_ne V h, LinearMap.zero_apply, PiLp.zero_apply]
  · simp only [LinearMap.coe_comp, Function.comp_apply, vertexProjection_apply_ne V hi,
      LinearMap.zero_apply, PiLp.zero_apply]


-- @@ L3530-3539 verbatim
theorem sum_vertexProjection :
    (∑ i, vertexProjection V i) =
      (LinearMap.id : VertexAmbient V →ₗ[ℝ] VertexAmbient V) := by
  ext v j
  simp only [LinearMap.sum_apply, LinearMap.id_apply]
  rw [WithLp.ofLp_sum, Finset.sum_apply, Finset.sum_eq_single j]
  · simp only [vertexProjection_apply_self]
  · intro i _ hi
    exact vertexProjection_apply_ne V hi.symm v
  · simp only [Finset.mem_univ, not_true_eq_false, vertexProjection_apply_self, IsEmpty.forall_iff]


-- @@ L3541-3547 verbatim
theorem trace_vertexProjection (i : I) :
    LinearMap.trace ℝ (VertexAmbient V) (vertexProjection V i) =
      (Module.finrank ℝ (V i) : ℝ) := by
  unfold vertexProjection
  rw [LinearMap.trace_comp_comm',
    (vertexInclusion V i).adjoint_comp_self']
  simp only [LinearMap.trace_id]


-- @@ L3549-3549 verbatim
end HigherYoungGraphAssembly


-- @@ L3551-3551 verbatim
end


-- @@ L3553-3553 verbatim
section



-- @@ L3556-3556 verbatim
open scoped BigOperators InnerProductSpace TensorProduct


-- @@ L3558-3558 verbatim
namespace HigherYoungMovingFibres


-- @@ L3560-3560 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L3561-3561 verbatim
open MetricCodes.Spherical.HigherYoungGraphAssembly

-- @@ L3562-3562 verbatim
open MetricCodes.Spherical.HigherProjectionInstantiation


-- @@ L3564-3574 verbatim
/-- The moving young fibre used in the spherical-code argument. -/
def movingYoungFibre {r n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (lam : Fin (r + 1) → ℕ)
    (o : SpherePoint n)
    (base : E →ₗᵢ[ℝ] HarmonicYoungSpace (n := n) lam)
    (x : SpherePoint n) :
    E →ₗᵢ[ℝ] HarmonicYoungSpace (n := n) lam :=
  (youngOrthogonalIsometry
    (AssociatedAxisTransport.commonAxisReflection o.val x.val)
    lam).toLinearIsometry.comp base


-- @@ L3576-3579 verbatim
/-- The young vertex used in the spherical-code argument. -/
abbrev YoungVertex {I : Type*} {r n : ℕ}
    (lam : I → Fin (r + 1) → ℕ) (i : I) : Type :=
  HarmonicYoungSpace (n := n) (lam i)


-- @@ L3581-3591 verbatim
/-- The moving young block fibre used in the spherical-code argument. -/
def movingYoungBlockFibre {I : Type*} [Fintype I] [DecidableEq I]
    {r n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (lam : I → Fin (r + 1) → ℕ)
    (o : SpherePoint n)
    (base : (i : I) → E →ₗᵢ[ℝ] YoungVertex (n := n) lam i)
    (i : I) (x : SpherePoint n) :
    E →ₗᵢ[ℝ] VertexAmbient (YoungVertex (n := n) lam) :=
  (vertexInclusion (YoungVertex (n := n) lam) i).comp
    (movingYoungFibre (lam i) o (base i) x)


-- @@ L3593-3604 verbatim
@[simp] theorem movingYoungBlockFibre_apply_self
    {I : Type*} [Fintype I] [DecidableEq I]
    {r n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (lam : I → Fin (r + 1) → ℕ)
    (o : SpherePoint n)
    (base : (i : I) → E →ₗᵢ[ℝ] YoungVertex (n := n) lam i)
    (i : I) (x : SpherePoint n) (v : E) :
    movingYoungBlockFibre lam o base i x v i =
      movingYoungFibre (lam i) o (base i) x v := by
  simp only [movingYoungBlockFibre, LinearIsometry.coe_comp, Function.comp_apply,
    vertexInclusion_apply_self]


-- @@ L3606-3616 verbatim
@[simp] theorem movingYoungBlockFibre_apply_ne
    {I : Type*} [Fintype I] [DecidableEq I]
    {r n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (lam : I → Fin (r + 1) → ℕ)
    (o : SpherePoint n)
    (base : (i : I) → E →ₗᵢ[ℝ] YoungVertex (n := n) lam i)
    (i j : I) (hji : j ≠ i) (x : SpherePoint n) (v : E) :
    movingYoungBlockFibre lam o base i x v j = 0 := by
  exact vertexInclusion_apply_ne (YoungVertex (n := n) lam) hji
    (movingYoungFibre (lam i) o (base i) x v)


-- @@ L3618-3639 verbatim
theorem movingYoungBlockFibre_support
    {I : Type*} [Fintype I] [DecidableEq I]
    {r n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (lam : I → Fin (r + 1) → ℕ)
    (o : SpherePoint n)
    (base : (i : I) → E →ₗᵢ[ℝ] YoungVertex (n := n) lam i)
    (i : I) (x : SpherePoint n) :
    (vertexProjection (YoungVertex (n := n) lam) i).comp
        (movingYoungBlockFibre lam o base i x).toLinearMap =
      (movingYoungBlockFibre lam o base i x).toLinearMap := by
  apply LinearMap.ext
  intro v
  apply PiLp.ext
  intro j
  by_cases hji : j = i
  · subst j
    simp only [LinearMap.coe_comp, LinearIsometry.coe_toLinearMap, Function.comp_apply,
      vertexProjection_apply_self, movingYoungBlockFibre_apply_self]
  · simp only [LinearMap.coe_comp, LinearIsometry.coe_toLinearMap, Function.comp_apply,
      vertexProjection_apply_ne (YoungVertex (n := n) lam) hji,
      movingYoungBlockFibre_apply_ne lam o base i j hji]


-- @@ L3641-3646 verbatim
/-- The axis tensor used in the spherical-code argument. -/
def axisTensor {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (x : SpherePoint n) :
    V →ₗ[ℝ] (SpherePacking.Euclidean n ⊗[ℝ] V) :=
  TensorProduct.mk ℝ (SpherePacking.Euclidean n) V x.val


-- @@ L3648-3651 verbatim
@[simp] theorem axisTensor_apply {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (x : SpherePoint n) (v : V) :
    axisTensor x v = x.val ⊗ₜ[ℝ] v := rfl


-- @@ L3653-3669 verbatim
theorem axisTensor_adjoint_comp {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    (x y : SpherePoint n) :
    (axisTensor (V := V) x).adjoint.comp (axisTensor y) =
      ⟪(x.val : SpherePacking.Euclidean n), y.val⟫_ℝ •
        (LinearMap.id : V →ₗ[ℝ] V) := by
  apply LinearMap.ext
  intro v
  apply ext_inner_right ℝ
  intro w
  change
    ⟪(axisTensor (V := V) x).adjoint (axisTensor y v), w⟫_ℝ =
      ⟪⟪x.val, y.val⟫_ℝ • v, w⟫_ℝ
  rw [LinearMap.adjoint_inner_left, axisTensor_apply, axisTensor_apply,
    TensorProduct.inner_tmul, real_inner_smul_left]
  rw [real_inner_comm x.val y.val]


-- @@ L3671-3671 verbatim
end HigherYoungMovingFibres


-- @@ L3673-3673 verbatim
end


-- @@ L3675-3675 verbatim
section



-- @@ L3678-3678 verbatim
open scoped BigOperators


-- @@ L3680-3680 verbatim
namespace HigherHarmonicYoung.GelfandTsetlin


-- @@ L3682-3695 verbatim
theorem rowEuler_mul {r n : ℕ} (i : Fin (r + 1))
    (p q : PolynomialSpace r n) :
    rowEuler r n i (p * q) =
      rowEuler r n i p * q + p * rowEuler r n i q := by
  simp only [rowEuler_apply, MvPolynomial.pderiv_mul]
  simp_rw [mul_add, Finset.sum_add_distrib,
    Finset.sum_mul, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    ring
  · apply Finset.sum_congr rfl
    intro j _
    ring


-- @@ L3697-3710 verbatim
theorem polarization_mul {r n : ℕ} (i j : Fin (r + 1))
    (p q : PolynomialSpace r n) :
    polarization r n i j (p * q) =
      polarization r n i j p * q + p * polarization r n i j q := by
  simp only [polarization_apply, MvPolynomial.pderiv_mul]
  simp_rw [mul_add, Finset.sum_add_distrib,
    Finset.sum_mul, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro k _
    ring
  · apply Finset.sum_congr rfl
    intro k _
    ring


-- @@ L3712-3712 verbatim
end HigherHarmonicYoung.GelfandTsetlin


-- @@ L3714-3714 verbatim
end


-- @@ L3716-3716 verbatim
section



-- @@ L3719-3719 verbatim
open scoped BigOperators InnerProductSpace


-- @@ L3721-3721 verbatim
namespace HigherYoungBranchingFibres


-- @@ L3723-3723 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L3724-3724 verbatim
open MetricCodes.Spherical.HigherYoungMovingFibres


-- @@ L3726-3733 verbatim
theorem multiFactorial_eq_finsupp_prod {n : ℕ}
    (a : Fin n →₀ ℕ) :
    SpherePacking.Fischer.multiFactorial a =
      a.prod (fun _ k => (k.factorial : ℝ)) := by
  classical
  symm
  simpa only [SpherePacking.Fischer.multiFactorial] using
    Finsupp.prod_of_support_subset a (Finset.subset_univ _) (fun _ k => (k.factorial : ℝ)) (by simp)


-- @@ L3735-3741 verbatim
theorem multiFactorial_mapDomain {n m : ℕ}
    (f : Fin n → Fin m) (hf : Function.Injective f)
    (a : Fin n →₀ ℕ) :
    SpherePacking.Fischer.multiFactorial (a.mapDomain f) =
      SpherePacking.Fischer.multiFactorial a := by
  rw [multiFactorial_eq_finsupp_prod, multiFactorial_eq_finsupp_prod,
    Finsupp.prod_mapDomain_index_inj hf]


-- @@ L3743-3758 verbatim
theorem polynomialInner_rename_injective {n m : ℕ}
    (f : Fin n → Fin m) (hf : Function.Injective f)
    (p q : MvPolynomial (Fin n) ℝ) :
    SpherePacking.Fischer.polynomialInner m
      (MvPolynomial.rename f p) (MvPolynomial.rename f q) =
        SpherePacking.Fischer.polynomialInner n p q := by
  induction p using MvPolynomial.induction_on' with
  | monomial a c =>
      rw [MvPolynomial.rename_monomial,
        SpherePacking.Fischer.polynomialInner_monomial,
        MvPolynomial.coeff_rename_mapDomain f hf,
        multiFactorial_mapDomain f hf,
        SpherePacking.Fischer.polynomialInner_monomial]
  | add p q hp hq =>
      rw [map_add, SpherePacking.Fischer.polynomialInner_add_left,
        SpherePacking.Fischer.polynomialInner_add_left, hp, hq]


-- @@ L3760-3764 verbatim
variable {E V : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]


-- @@ L3766-3766 verbatim
end HigherYoungBranchingFibres


-- @@ L3768-3768 verbatim
end


-- @@ L3770-3770 verbatim
namespace HigherHarmonicYoung


-- @@ L3772-3772 verbatim
section



-- @@ L3775-3775 verbatim
open scoped BigOperators


-- @@ L3777-3782 verbatim
/-- The row pairing polynomial used in the spherical-code argument. -/
def rowPairingPolynomial {r n : ℕ} (i j : Fin (r + 1)) :
    PolynomialSpace r n :=
  ∑ k : Fin n,
    MvPolynomial.X (variableIndex i k) *
      MvPolynomial.X (variableIndex j k)


-- @@ L3784-3792 verbatim
theorem rowPairingPolynomial_isHomogeneous {r n : ℕ}
    (i j : Fin (r + 1)) :
    (rowPairingPolynomial (n := n) i j).IsHomogeneous 2 := by
  unfold rowPairingPolynomial
  apply MvPolynomial.IsHomogeneous.sum
  intro k _
  simpa only [Nat.reduceAdd] using
    (MvPolynomial.isHomogeneous_X ℝ (variableIndex i k)).mul (MvPolynomial.isHomogeneous_X ℝ
      (variableIndex j k))


-- @@ L3794-3804 verbatim
/-- The homogeneous row pairing multiplication used in the spherical-code argument. -/
def homogeneousRowPairingMultiplication {r n : ℕ}
    (i j : Fin (r + 1)) (m : ℕ) :
    SpherePacking.Fischer.Homogeneous ((r + 1) * n) m →ₗ[ℝ]
      SpherePacking.Fischer.Homogeneous ((r + 1) * n) (m + 2) :=
  (LinearMap.mulLeft ℝ
    (rowPairingPolynomial (n := n) i j)).restrict
      (fun p hp => by
        simpa only [LinearMap.mulLeft_apply, MvPolynomial.mem_homogeneousSubmodule,
          Nat.add_comm] using
          (rowPairingPolynomial_isHomogeneous i j).mul hp)


-- @@ L3806-3813 verbatim
@[simp] theorem homogeneousRowPairingMultiplication_apply
    {r n : ℕ} (i j : Fin (r + 1)) (m : ℕ)
    (p : SpherePacking.Fischer.Homogeneous ((r + 1) * n) m) :
    ((homogeneousRowPairingMultiplication i j m p :
      SpherePacking.Fischer.Homogeneous ((r + 1) * n) (m + 2)) :
        PolynomialSpace r n) =
      rowPairingPolynomial (n := n) i j *
        (p : PolynomialSpace r n) := rfl


-- @@ L3815-3823 verbatim
theorem traceOperator_isHomogeneous {r n m : ℕ}
    (i j : Fin (r + 1)) (p : PolynomialSpace r n)
    (hp : p.IsHomogeneous m) :
    (traceOperator r n i j p).IsHomogeneous (m - 2) := by
  rw [traceOperator_apply]
  apply MvPolynomial.IsHomogeneous.sum
  intro k _
  simpa only [Nat.sub_sub, Nat.reduceAdd] using
    (hp.pderiv (i := variableIndex j k)).pderiv (i := variableIndex i k)


-- @@ L3825-3840 verbatim
/-- The homogeneous row trace used in the spherical-code argument. -/
def homogeneousRowTrace {r n : ℕ}
    (i j : Fin (r + 1)) (m : ℕ) :
    SpherePacking.Fischer.Homogeneous ((r + 1) * n) (m + 2) →ₗ[ℝ]
      SpherePacking.Fischer.Homogeneous ((r + 1) * n) m :=
  LinearMap.codRestrict
    (MvPolynomial.homogeneousSubmodule
      (Fin ((r + 1) * n)) ℝ m)
    ((traceOperator r n i j).domRestrict
      (MvPolynomial.homogeneousSubmodule
        (Fin ((r + 1) * n)) ℝ (m + 2)))
    (fun p => by
      change
        (traceOperator r n i j (p : PolynomialSpace r n)).IsHomogeneous m
      simpa only [traceOperator_apply, add_tsub_cancel_right] using
        traceOperator_isHomogeneous i j (p : PolynomialSpace r n) p.property)


-- @@ L3842-3848 verbatim
@[simp] theorem homogeneousRowTrace_apply {r n : ℕ}
    (i j : Fin (r + 1)) (m : ℕ)
    (p : SpherePacking.Fischer.Homogeneous ((r + 1) * n) (m + 2)) :
    ((homogeneousRowTrace i j m p :
      SpherePacking.Fischer.Homogeneous ((r + 1) * n) m) :
        PolynomialSpace r n) =
      traceOperator r n i j (p : PolynomialSpace r n) := rfl


-- @@ L3850-3865 verbatim
theorem polynomialInner_rowPairing_trace {r n : ℕ}
    (i j : Fin (r + 1)) (p q : PolynomialSpace r n) :
    SpherePacking.Fischer.polynomialInner ((r + 1) * n)
      (rowPairingPolynomial (n := n) i j * p) q =
    SpherePacking.Fischer.polynomialInner ((r + 1) * n)
      p (traceOperator r n i j q) := by
  classical
  rw [rowPairingPolynomial, Finset.sum_mul,
    SpherePacking.Fischer.polynomialInner_sum_left,
    traceOperator_apply,
    SpherePacking.Fischer.polynomialInner_sum_right]
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_assoc, SpherePacking.Fischer.polynomialInner_X_mul,
    SpherePacking.Fischer.polynomialInner_X_mul]
  rw [SpherePacking.mvPolynomial_pderiv_commute]


-- @@ L3867-3867 verbatim
open MetricCodes.Spherical.TwoRowYoungBidegreeDecomposition

-- @@ L3868-3868 verbatim
open SpherePacking.HarmonicCoordinateOperators


-- @@ L3870-3870 verbatim
end


-- @@ L3872-3872 verbatim
section



-- @@ L3875-3875 verbatim
open scoped BigOperators InnerProductSpace

-- @@ L3876-3876 verbatim
open MetricCodes.Spherical.HigherHierarchy


-- @@ L3878-3891 verbatim
/-- Data encoding the young polynomial frame construction. -/
structure YoungPolynomialFrame {r : ℕ} (n : ℕ)
    (lam : Fin (r + 1) → ℕ) (ι : Type*) where
  /-- The polynomial component. -/
  polynomial : ι → PolynomialSpace r n
  homogeneous : ∀ i, (polynomial i).IsHomogeneous (∑ j, lam j)
  rowEuler : ∀ i j,
    HigherHarmonicYoung.rowEuler r n j (polynomial i) =
      (lam j : ℝ) • polynomial i
  traceFree : ∀ i j k,
    traceOperator r n j k (polynomial i) = 0
  highestWeight : ∀ i j k, j < k →
    polarization r n j k (polynomial i) = 0
  independent : LinearIndependent ℝ polynomial


-- @@ L3893-3893 verbatim
namespace YoungPolynomialFrame


-- @@ L3895-3895 verbatim
variable {r n : ℕ} {lam : Fin (r + 1) → ℕ} {ι : Type*}


-- @@ L3897-3902 verbatim
/-- The harmonic Young vector obtained from a frame polynomial and its defining certificates. -/
def vector (F : YoungPolynomialFrame n lam ι) (i : ι) :
    HarmonicYoungSpace (n := n) lam :=
  ⟨F.polynomial i, (mem_harmonicYoungSubmodule lam _).2
    ⟨F.homogeneous i, F.rowEuler i, F.traceFree i,
      F.highestWeight i⟩⟩


-- @@ L3904-3908 verbatim
theorem vector_linearIndependent (F : YoungPolynomialFrame n lam ι) :
    LinearIndependent ℝ F.vector := by
  apply LinearIndependent.of_comp
    (harmonicYoungSubmodule (n := n) lam).subtype
  simpa only [Submodule.coe_subtype, Function.comp_def, vector] using F.independent


-- @@ L3910-3935 verbatim
theorem span_vector_eq_top (F : YoungPolynomialFrame n lam ι)
    (hspan : ∀ p : PolynomialSpace r n,
      p ∈ harmonicYoungSubmodule (n := n) lam →
        p ∈ Submodule.span ℝ (Set.range F.polynomial)) :
    Submodule.span ℝ (Set.range F.vector) = ⊤ := by
  apply Submodule.eq_top_iff'.2
  intro p
  have hp := hspan (p : PolynomialSpace r n) p.property
  have hmap :
      Submodule.map (harmonicYoungSubmodule (n := n) lam).subtype
          (Submodule.span ℝ (Set.range F.vector)) =
        Submodule.span ℝ (Set.range F.polynomial) := by
    rw [Submodule.map_span]
    congr 1
    ext q
    constructor
    · rintro ⟨v, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨F.vector i, ⟨i, rfl⟩, rfl⟩
  rw [← hmap] at hp
  obtain ⟨q, hq, heq⟩ := hp
  have hqp : q = p := by
    apply Subtype.ext
    exact heq
  rwa [hqp] at hq


-- @@ L3937-3944 verbatim
/-- The basis used in the spherical-code argument. -/
def basis (F : YoungPolynomialFrame n lam ι)
    (hspan : ∀ p : PolynomialSpace r n,
      p ∈ harmonicYoungSubmodule (n := n) lam →
        p ∈ Submodule.span ℝ (Set.range F.polynomial)) :
    Module.Basis ι ℝ (HarmonicYoungSpace (n := n) lam) :=
  Module.Basis.mk F.vector_linearIndependent
    (F.span_vector_eq_top hspan).ge


-- @@ L3946-3946 verbatim
end YoungPolynomialFrame


-- @@ L3948-3948 verbatim
end


-- @@ L3950-3950 verbatim
section



-- @@ L3953-3953 verbatim
open scoped BigOperators InnerProductSpace


-- @@ L3955-3965 verbatim
theorem variableIndex_eq_iff_harmonicLift {r n : ℕ}
    (i j : Fin (r + 1)) (a b : Fin n) :
    variableIndex i a = variableIndex j b ↔ i = j ∧ a = b := by
  constructor
  · intro h
    have hpair : (i, a) = (j, b) := by
      apply variableIndex_injective (r := r) (n := n)
      exact h
    exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩
  · rintro ⟨rfl, rfl⟩
    rfl


-- @@ L3967-3985 verbatim
theorem pderiv_polarization_harmonicLift {r n : ℕ}
    (a i j : Fin (r + 1)) (k : Fin n) (p : PolynomialSpace r n) :
    MvPolynomial.pderiv (variableIndex a k) (polarization r n i j p) =
      (if a = i then MvPolynomial.pderiv (variableIndex j k) p else 0) +
        polarization r n i j
          (MvPolynomial.pderiv (variableIndex a k) p) := by
  classical
  simp only [polarization_apply, map_sum, MvPolynomial.pderiv_mul,
    Finset.sum_add_distrib]
  refine congrArg₂ (· + ·) ?_ ?_
  · by_cases h : a = i
    · subst a
      simp only [MvPolynomial.pderiv_X, Pi.single_apply, variableIndex_eq_iff_harmonicLift,
        true_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    · simp only [MvPolynomial.pderiv_X, ne_eq, variableIndex_eq_iff_harmonicLift, h, false_and,
        not_false_eq_true, Pi.single_eq_of_ne', zero_mul, Finset.sum_const_zero, ↓reduceIte]
  · apply Finset.sum_congr rfl
    intro l _
    rw [SpherePacking.mvPolynomial_pderiv_commute]


-- @@ L3987-4021 verbatim
theorem traceOperator_polarization_harmonicLift {r n : ℕ}
    (a b i j : Fin (r + 1)) (p : PolynomialSpace r n) :
    traceOperator r n a b (polarization r n i j p) =
      polarization r n i j (traceOperator r n a b p) +
        (if a = i then traceOperator r n j b p else 0) +
        (if b = i then traceOperator r n a j p else 0) := by
  classical
  calc
    traceOperator r n a b (polarization r n i j p) =
        ∑ k : Fin n,
          ((if b = i then
              MvPolynomial.pderiv (variableIndex a k)
                (MvPolynomial.pderiv (variableIndex j k) p)
            else 0) +
            (if a = i then
              MvPolynomial.pderiv (variableIndex j k)
                (MvPolynomial.pderiv (variableIndex b k) p)
            else 0) +
            polarization r n i j
              (MvPolynomial.pderiv (variableIndex a k)
                (MvPolynomial.pderiv (variableIndex b k) p))) := by
      rw [traceOperator_apply]
      apply Finset.sum_congr rfl
      intro k _
      rw [pderiv_polarization_harmonicLift b i j k,
        map_add, pderiv_polarization_harmonicLift a i j k]
      split_ifs <;> simp; abel
    _ = polarization r n i j (traceOperator r n a b p) +
        (if a = i then traceOperator r n j b p else 0) +
        (if b = i then traceOperator r n a j p else 0) := by
      by_cases ha : a = i <;> by_cases hb : b = i
      all_goals
        simp only [ha, hb, ite_true, ite_false, Finset.sum_add_distrib,
          zero_add, add_zero, traceOperator_apply,
          map_sum] <;> try abel


-- @@ L4023-4063 verbatim
theorem traceFree_of_firstTrace_and_highestWeight {r n : ℕ}
    (p : PolynomialSpace r n)
    (hfirst : traceOperator r n 0 0 p = 0)
    (hyoung : ∀ i j : Fin (r + 1), i < j →
      polarization r n i j p = 0) :
    ∀ a b : Fin (r + 1), traceOperator r n a b p = 0 := by
  have hfirstMixed : ∀ j : Fin (r + 1),
      traceOperator r n 0 j p = 0 := by
    intro j
    by_cases hj : j = 0
    · subst j
      exact hfirst
    · have hjpos : (0 : Fin (r + 1)) < j :=
        Fin.pos_iff_ne_zero.mpr hj
      have hcomm :=
        traceOperator_polarization_harmonicLift 0 0 0 j p
      rw [hyoung 0 j hjpos, map_zero, hfirst, map_zero] at hcomm
      have hsym : traceOperator r n j 0 p =
          traceOperator r n 0 j p := by
        rw [traceOperator_comm j 0]
      rw [hsym] at hcomm
      exact add_self_eq_zero.mp (by simpa only [traceOperator_apply, add_self_eq_zero, ↓reduceIte,
                                      zero_add] using hcomm.symm)
  intro a b
  by_cases ha : a = 0
  · subst a
    exact hfirstMixed b
  · by_cases hb : b = 0
    · subst b
      rw [traceOperator_comm a 0]
      exact hfirstMixed a
    · have hbpos : (0 : Fin (r + 1)) < b :=
        Fin.pos_iff_ne_zero.mpr hb
      have hcomm :=
        traceOperator_polarization_harmonicLift 0 a 0 b p
      rw [hyoung 0 b hbpos, map_zero,
        hfirstMixed a, map_zero] at hcomm
      have hba : traceOperator r n b a p = 0 := by
        simpa only [traceOperator_apply, ↓reduceIte, zero_add, ha, add_zero] using hcomm.symm
      rw [traceOperator_comm a b]
      exact hba


-- @@ L4065-4081 verbatim
theorem mem_harmonicYoungSubmodule_iff_firstTrace_and_highestWeight
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (p : PolynomialSpace r n) :
    p ∈ harmonicYoungSubmodule lam ↔
      p.IsHomogeneous (∑ i, lam i) ∧
        (∀ i : Fin (r + 1), rowEuler r n i p = (lam i : ℝ) • p) ∧
        traceOperator r n 0 0 p = 0 ∧
        (∀ i j : Fin (r + 1), i < j →
          polarization r n i j p = 0) := by
  rw [mem_harmonicYoungSubmodule]
  constructor
  · rintro ⟨hhom, hweight, htrace, hhighest⟩
    exact ⟨hhom, hweight, htrace 0 0, hhighest⟩
  · rintro ⟨hhom, hweight, hfirst, hhighest⟩
    exact ⟨hhom, hweight,
      traceFree_of_firstTrace_and_highestWeight p hfirst hhighest,
      hhighest⟩


-- @@ L4083-4102 verbatim
theorem mem_harmonicYoungSubmodule_iff_multihomogeneous_firstTrace_highestWeight
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (p : PolynomialSpace r n) :
    p ∈ harmonicYoungSubmodule lam ↔
      p ∈ youngMultihomogeneousSubmodule n lam ∧
        traceOperator r n 0 0 p = 0 ∧
        (∀ i j : Fin (r + 1), i < j →
          polarization r n i j p = 0) := by
  constructor
  · intro hp
    have hconditions :=
      (mem_harmonicYoungSubmodule_iff_firstTrace_and_highestWeight
        lam p).mp hp
    exact ⟨harmonicYoung_mem_youngMultihomogeneousSubmodule lam
      ⟨p, hp⟩, hconditions.2.2⟩
  · rintro ⟨hdegree, hfirst, hhighest⟩
    rw [mem_harmonicYoungSubmodule_iff_firstTrace_and_highestWeight]
    exact ⟨youngMultihomogeneous_isHomogeneous lam ⟨p, hdegree⟩,
      youngMultihomogeneous_rowEuler lam ⟨p, hdegree⟩,
      hfirst, hhighest⟩


-- @@ L4104-4111 verbatim
theorem polarization_mem_traceFreeSubmodule {r n : ℕ}
    (i j : Fin (r + 1)) (p : PolynomialSpace r n)
    (hp : p ∈ traceFreeSubmodule r n) :
    polarization r n i j p ∈ traceFreeSubmodule r n := by
  rw [mem_traceFreeSubmodule] at hp ⊢
  intro a b
  rw [traceOperator_polarization_harmonicLift, hp a b, map_zero]
  split_ifs <;> simp [hp]


-- @@ L4113-4144 verbatim
theorem polynomialInner_polarization_harmonicLift {r n : ℕ}
    (i j : Fin (r + 1)) (p q : PolynomialSpace r n) :
    SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        (polarization r n i j p) q =
      SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        p (polarization r n j i q) := by
  classical
  simp_rw [polarization_apply,
    SpherePacking.Fischer.polynomialInner_sum_left,
    SpherePacking.Fischer.polynomialInner_sum_right]
  apply Finset.sum_congr rfl
  intro k _
  calc
    SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        (MvPolynomial.X (variableIndex i k) *
          MvPolynomial.pderiv (variableIndex j k) p) q =
      SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        (MvPolynomial.pderiv (variableIndex j k) p)
        (MvPolynomial.pderiv (variableIndex i k) q) :=
      SpherePacking.Fischer.polynomialInner_X_mul _ _ _ _
    _ = SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        (MvPolynomial.pderiv (variableIndex i k) q)
        (MvPolynomial.pderiv (variableIndex j k) p) :=
      SpherePacking.Fischer.polynomialInner_comm _ _ _
    _ = SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        (MvPolynomial.X (variableIndex j k) *
          MvPolynomial.pderiv (variableIndex i k) q) p :=
      (SpherePacking.Fischer.polynomialInner_X_mul _ _ _ _).symm
    _ = SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        p (MvPolynomial.X (variableIndex j k) *
          MvPolynomial.pderiv (variableIndex i k) q) :=
      SpherePacking.Fischer.polynomialInner_comm _ _ _


-- @@ L4146-4152 verbatim
/-- The homogeneous trace free submodule used in the spherical-code argument. -/
def homogeneousTraceFreeSubmodule (r n m : ℕ) :
    Submodule ℝ
      (SpherePacking.Fischer.Homogeneous ((r + 1) * n) m) :=
  (traceFreeSubmodule r n).comap
    (MvPolynomial.homogeneousSubmodule
      (Fin ((r + 1) * n)) ℝ m).subtype


-- @@ L4154-4160 verbatim
@[simp] theorem mem_homogeneousTraceFreeSubmodule {r n m : ℕ}
    (p : SpherePacking.Fischer.Homogeneous ((r + 1) * n) m) :
    p ∈ homogeneousTraceFreeSubmodule r n m ↔
      ∀ i j : Fin (r + 1),
        traceOperator r n i j (p : PolynomialSpace r n) = 0 := by
  change (p : PolynomialSpace r n) ∈ traceFreeSubmodule r n ↔ _
  exact mem_traceFreeSubmodule (p : PolynomialSpace r n)


-- @@ L4162-4167 verbatim
/-- The coefficient embedding restricted to homogeneous trace-free polynomials. -/
def homogeneousTraceFreeCoefficientEmbedding (r n m : ℕ) :
    homogeneousTraceFreeSubmodule r n m →ₗ[ℝ]
      SpherePacking.Fischer.CoefficientSpace ((r + 1) * n) m :=
  (SpherePacking.Fischer.coefficientEmbedding ((r + 1) * n) m).comp
    (homogeneousTraceFreeSubmodule r n m).subtype


-- @@ L4169-4175 verbatim
theorem homogeneousTraceFreeCoefficientEmbedding_injective
    (r n m : ℕ) :
    Function.Injective
      (homogeneousTraceFreeCoefficientEmbedding r n m) :=
  (SpherePacking.Fischer.coefficientEmbedding_injective
    ((r + 1) * n) m).comp
      (homogeneousTraceFreeSubmodule r n m).subtype_injective


-- @@ L4177-4181 verbatim
/-- The range of the homogeneous trace-free coefficient embedding. -/
def homogeneousTraceFreeCoefficientRange (r n m : ℕ) :
    Submodule ℝ
      (SpherePacking.Fischer.CoefficientSpace ((r + 1) * n) m) :=
  LinearMap.range (homogeneousTraceFreeCoefficientEmbedding r n m)


-- @@ L4183-4195 verbatim
/-- Orthogonally project coefficient space to the homogeneous trace-free range and recover the
polynomial. -/
def simultaneousHarmonicCoefficientProjection (r n m : ℕ) :
    SpherePacking.Fischer.CoefficientSpace ((r + 1) * n) m →ₗ[ℝ]
      homogeneousTraceFreeSubmodule r n m := by
  let e := homogeneousTraceFreeCoefficientEmbedding r n m
  have he : Function.Injective e :=
    homogeneousTraceFreeCoefficientEmbedding_injective r n m
  let S : Submodule ℝ
      (SpherePacking.Fischer.CoefficientSpace ((r + 1) * n) m) :=
    LinearMap.range e
  exact ((LinearEquiv.ofInjective e he).symm.toLinearMap).comp
    (S.projectionOnto Sᗮ S.isCompl_orthogonal)


-- @@ L4197-4202 verbatim
/-- The simultaneous harmonic projection used in the spherical-code argument. -/
def simultaneousHarmonicProjection (r n m : ℕ) :
    SpherePacking.Fischer.Homogeneous ((r + 1) * n) m →ₗ[ℝ]
      homogeneousTraceFreeSubmodule r n m :=
  (simultaneousHarmonicCoefficientProjection r n m).comp
    (SpherePacking.Fischer.coefficientEmbedding ((r + 1) * n) m)


-- @@ L4204-4211 verbatim
@[simp] theorem simultaneousHarmonicProjection_traceFree
    {r n m : ℕ} (p : homogeneousTraceFreeSubmodule r n m) :
    simultaneousHarmonicProjection r n m p.val = p := by
  unfold simultaneousHarmonicProjection
    simultaneousHarmonicCoefficientProjection
  dsimp
  rw [Submodule.projectionOnto_apply_of_mem_left]
  exact (LinearEquiv.ofInjective _ _).symm_apply_apply p


-- @@ L4213-4222 verbatim
theorem simultaneousHarmonicProjection_traceOperator
    {r n m : ℕ}
    (p : SpherePacking.Fischer.Homogeneous ((r + 1) * n) m)
    (i j : Fin (r + 1)) :
    traceOperator r n i j
      ((simultaneousHarmonicProjection r n m p).val :
        PolynomialSpace r n) = 0 :=
  (mem_homogeneousTraceFreeSubmodule
    (simultaneousHarmonicProjection r n m p).val).mp
      (simultaneousHarmonicProjection r n m p).property i j


-- @@ L4224-4244 verbatim
theorem simultaneousHarmonicProjection_coefficient_eq_projection
    {r n m : ℕ}
    (p : SpherePacking.Fischer.Homogeneous ((r + 1) * n) m) :
    homogeneousTraceFreeCoefficientEmbedding r n m
        (simultaneousHarmonicProjection r n m p) =
      (homogeneousTraceFreeCoefficientRange r n m).projection
        (homogeneousTraceFreeCoefficientRange r n m)ᗮ
        (homogeneousTraceFreeCoefficientRange r n m).isCompl_orthogonal
        (SpherePacking.Fischer.coefficientEmbedding
          ((r + 1) * n) m p) := by
  unfold simultaneousHarmonicProjection
    simultaneousHarmonicCoefficientProjection
  dsimp
  have h := (LinearEquiv.ofInjective
    (homogeneousTraceFreeCoefficientEmbedding r n m)
    (homogeneousTraceFreeCoefficientEmbedding_injective r n m)).apply_symm_apply
      ((homogeneousTraceFreeCoefficientRange r n m).projectionOnto
        (homogeneousTraceFreeCoefficientRange r n m)ᗮ
        (homogeneousTraceFreeCoefficientRange r n m).isCompl_orthogonal
        (SpherePacking.Fischer.coefficientEmbedding ((r + 1) * n) m p))
  exact congrArg Subtype.val h


-- @@ L4246-4255 verbatim
theorem simultaneousHarmonicProjection_residual_orthogonal
    {r n m : ℕ}
    (p : SpherePacking.Fischer.Homogeneous ((r + 1) * n) m) :
    SpherePacking.Fischer.coefficientEmbedding ((r + 1) * n) m p -
        homogeneousTraceFreeCoefficientEmbedding r n m
          (simultaneousHarmonicProjection r n m p) ∈
      (homogeneousTraceFreeCoefficientRange r n m)ᗮ := by
  rw [simultaneousHarmonicProjection_coefficient_eq_projection]
  exact Submodule.sub_projection_mem
    (homogeneousTraceFreeCoefficientRange r n m).isCompl_orthogonal _


-- @@ L4257-4280 verbatim
theorem simultaneousHarmonicProjection_polynomialInner
    {r n m : ℕ}
    (p : SpherePacking.Fischer.Homogeneous ((r + 1) * n) m)
    (q : homogeneousTraceFreeSubmodule r n m) :
    SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        ((simultaneousHarmonicProjection r n m p).val :
          PolynomialSpace r n)
        (q.val : PolynomialSpace r n) =
      SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        (p : PolynomialSpace r n) (q.val : PolynomialSpace r n) := by
  have horth :=
    (Submodule.mem_orthogonal'
      (homogeneousTraceFreeCoefficientRange r n m) _).mp
      (simultaneousHarmonicProjection_residual_orthogonal p)
      (homogeneousTraceFreeCoefficientEmbedding r n m q)
      ⟨q, rfl⟩
  rw [inner_sub_left] at horth
  change
    SpherePacking.Fischer.homogeneousInner ((r + 1) * n) m p q.val -
      SpherePacking.Fischer.homogeneousInner ((r + 1) * n) m
        (simultaneousHarmonicProjection r n m p).val q.val = 0 at horth
  rw [SpherePacking.Fischer.homogeneousInner_eq_polynomialInner,
    SpherePacking.Fischer.homogeneousInner_eq_polynomialInner] at horth
  linarith


-- @@ L4282-4302 verbatim
theorem polarization_isHomogeneous_harmonicLift {r n m : ℕ}
    (i j : Fin (r + 1)) (p : PolynomialSpace r n)
    (hp : p.IsHomogeneous m) :
    (polarization r n i j p).IsHomogeneous m := by
  classical
  cases m with
  | zero =>
      have hconstant :
          p = MvPolynomial.C (p.coeff 0) :=
        MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
          ((MvPolynomial.totalDegree_zero_iff_isHomogeneous _).mpr hp)
      rw [hconstant]
      simp only [polarization_apply, MvPolynomial.derivation_C, mul_zero, Finset.sum_const_zero,
        MvPolynomial.isHomogeneous_zero]
  | succ m =>
      rw [polarization_apply]
      apply MvPolynomial.IsHomogeneous.sum
      intro k _
      simpa only [add_tsub_cancel_right, Nat.add_comm] using
        (MvPolynomial.isHomogeneous_X ℝ (variableIndex i k)).mul (hp.pderiv (i := variableIndex
          j k))


-- @@ L4304-4310 verbatim
/-- The row polarization operator restricted to homogeneous degree `m`. -/
def homogeneousPolarization (r n m : ℕ)
    (i j : Fin (r + 1)) :
    SpherePacking.Fischer.Homogeneous ((r + 1) * n) m →ₗ[ℝ]
      SpherePacking.Fischer.Homogeneous ((r + 1) * n) m :=
  (polarization r n i j).restrict
    (fun p hp => polarization_isHomogeneous_harmonicLift i j p hp)


-- @@ L4312-4318 verbatim
@[simp] theorem homogeneousPolarization_apply_coe {r n m : ℕ}
    (i j : Fin (r + 1))
    (p : SpherePacking.Fischer.Homogeneous ((r + 1) * n) m) :
    ((homogeneousPolarization r n m i j p :
      SpherePacking.Fischer.Homogeneous ((r + 1) * n) m) :
        PolynomialSpace r n) =
      polarization r n i j (p : PolynomialSpace r n) := rfl


-- @@ L4320-4330 verbatim
theorem homogeneousPolarization_mem_traceFree {r n m : ℕ}
    (i j : Fin (r + 1))
    (p : SpherePacking.Fischer.Homogeneous ((r + 1) * n) m)
    (hp : p ∈ homogeneousTraceFreeSubmodule r n m) :
    homogeneousPolarization r n m i j p ∈
      homogeneousTraceFreeSubmodule r n m := by
  rw [mem_homogeneousTraceFreeSubmodule] at hp ⊢
  exact (mem_traceFreeSubmodule _).mp
    (polarization_mem_traceFreeSubmodule i j
      (p : PolynomialSpace r n)
      ((mem_traceFreeSubmodule _).mpr hp))


-- @@ L4332-4338 verbatim
/-- The row polarization operator restricted further to homogeneous trace-free polynomials. -/
def traceFreeHomogeneousPolarization (r n m : ℕ)
    (i j : Fin (r + 1)) :
    homogeneousTraceFreeSubmodule r n m →ₗ[ℝ]
      homogeneousTraceFreeSubmodule r n m :=
  (homogeneousPolarization r n m i j).restrict
    (fun p hp => homogeneousPolarization_mem_traceFree i j p hp)


-- @@ L4340-4353 verbatim
theorem polynomialInner_sub_left_harmonicLift {N : ℕ}
    (p q s : MvPolynomial (Fin N) ℝ) :
    SpherePacking.Fischer.polynomialInner N (p - q) s =
      SpherePacking.Fischer.polynomialInner N p s -
        SpherePacking.Fischer.polynomialInner N q s := by
  rw [sub_eq_add_neg, SpherePacking.Fischer.polynomialInner_add_left]
  have hneg :
      SpherePacking.Fischer.polynomialInner N (-q) s =
        -SpherePacking.Fischer.polynomialInner N q s := by
    rw [← neg_one_smul ℝ q,
      SpherePacking.Fischer.polynomialInner_smul_left]
    ring
  rw [hneg]
  rfl


-- @@ L4355-4413 verbatim
theorem simultaneousHarmonicProjection_polarization
    {r n m : ℕ} (i j : Fin (r + 1))
    (p : SpherePacking.Fischer.Homogeneous ((r + 1) * n) m) :
    simultaneousHarmonicProjection r n m
        (homogeneousPolarization r n m i j p) =
      traceFreeHomogeneousPolarization r n m i j
        (simultaneousHarmonicProjection r n m p) := by
  let A := simultaneousHarmonicProjection r n m
    (homogeneousPolarization r n m i j p)
  let B := traceFreeHomogeneousPolarization r n m i j
    (simultaneousHarmonicProjection r n m p)
  have hpair (q : homogeneousTraceFreeSubmodule r n m) :
      SpherePacking.Fischer.polynomialInner ((r + 1) * n)
          (A.val : PolynomialSpace r n) (q.val : PolynomialSpace r n) =
        SpherePacking.Fischer.polynomialInner ((r + 1) * n)
          (B.val : PolynomialSpace r n) (q.val : PolynomialSpace r n) := by
    calc
      SpherePacking.Fischer.polynomialInner ((r + 1) * n)
          (A.val : PolynomialSpace r n) (q.val : PolynomialSpace r n) =
        SpherePacking.Fischer.polynomialInner ((r + 1) * n)
          (polarization r n i j (p : PolynomialSpace r n))
          (q.val : PolynomialSpace r n) :=
        simultaneousHarmonicProjection_polynomialInner
          (homogeneousPolarization r n m i j p) q
      _ = SpherePacking.Fischer.polynomialInner ((r + 1) * n)
          (p : PolynomialSpace r n)
          (polarization r n j i (q.val : PolynomialSpace r n)) :=
        polynomialInner_polarization_harmonicLift i j _ _
      _ = SpherePacking.Fischer.polynomialInner ((r + 1) * n)
          ((simultaneousHarmonicProjection r n m p).val :
            PolynomialSpace r n)
          (polarization r n j i (q.val : PolynomialSpace r n)) :=
        (simultaneousHarmonicProjection_polynomialInner p
          (traceFreeHomogeneousPolarization r n m j i q)).symm
      _ = SpherePacking.Fischer.polynomialInner ((r + 1) * n)
          (B.val : PolynomialSpace r n)
          (q.val : PolynomialSpace r n) :=
        (polynomialInner_polarization_harmonicLift i j _ _).symm
  have hzero :
      SpherePacking.Fischer.polynomialInner ((r + 1) * n)
          (((A - B).val :
            SpherePacking.Fischer.Homogeneous ((r + 1) * n) m) :
              PolynomialSpace r n)
          (((A - B).val :
            SpherePacking.Fischer.Homogeneous ((r + 1) * n) m) :
              PolynomialSpace r n) = 0 := by
    change SpherePacking.Fischer.polynomialInner ((r + 1) * n)
      ((A.val : PolynomialSpace r n) - (B.val : PolynomialSpace r n))
      (((A - B).val :
        SpherePacking.Fischer.Homogeneous ((r + 1) * n) m) :
          PolynomialSpace r n) = 0
    rw [polynomialInner_sub_left_harmonicLift,
      hpair (A - B), sub_self]
  change A = B
  apply sub_eq_zero.mp
  apply Subtype.ext
  apply Subtype.ext
  exact (SpherePacking.Fischer.polynomialInner_self_eq_zero
    ((r + 1) * n) _).mp hzero


-- @@ L4415-4428 verbatim
theorem simultaneousHarmonicProjection_polarization_coe
    {r n m : ℕ} (i j : Fin (r + 1))
    (p : SpherePacking.Fischer.Homogeneous ((r + 1) * n) m) :
    (((simultaneousHarmonicProjection r n m
      (homogeneousPolarization r n m i j p)).val :
        SpherePacking.Fischer.Homogeneous ((r + 1) * n) m) :
          PolynomialSpace r n) =
      polarization r n i j
        ((simultaneousHarmonicProjection r n m p).val :
          PolynomialSpace r n) := by
  exact congrArg
    (fun q : homogeneousTraceFreeSubmodule r n m =>
      (q.val : PolynomialSpace r n))
    (simultaneousHarmonicProjection_polarization i j p)


-- @@ L4430-4459 verbatim
theorem simultaneousHarmonicProjection_rowWeight
    {r n m : ℕ} (i : Fin (r + 1)) (c : ℝ)
    (p : SpherePacking.Fischer.Homogeneous ((r + 1) * n) m)
    (hp : rowEuler r n i (p : PolynomialSpace r n) =
      c • (p : PolynomialSpace r n)) :
    rowEuler r n i
        ((simultaneousHarmonicProjection r n m p).val :
          PolynomialSpace r n) =
      c • ((simultaneousHarmonicProjection r n m p).val :
        PolynomialSpace r n) := by
  have hhom : homogeneousPolarization r n m i i p = c • p := by
    apply Subtype.ext
    simpa only [homogeneousPolarization_apply_coe, polarization_self, rowEuler_apply,
      SetLike.val_smul] using hp
  calc
    rowEuler r n i
        ((simultaneousHarmonicProjection r n m p).val :
          PolynomialSpace r n) =
      polarization r n i i
        ((simultaneousHarmonicProjection r n m p).val :
          PolynomialSpace r n) := by rw [polarization_self]
    _ = (((simultaneousHarmonicProjection r n m
      (homogeneousPolarization r n m i i p)).val :
        SpherePacking.Fischer.Homogeneous ((r + 1) * n) m) :
          PolynomialSpace r n) :=
      (simultaneousHarmonicProjection_polarization_coe i i p).symm
    _ = c • ((simultaneousHarmonicProjection r n m p).val :
          PolynomialSpace r n) := by
      rw [hhom, map_smul]
      rfl


-- @@ L4461-4480 verbatim
theorem simultaneousHarmonicProjection_polarization_eq_zero
    {r n m : ℕ} (i j : Fin (r + 1))
    (p : SpherePacking.Fischer.Homogeneous ((r + 1) * n) m)
    (hp : polarization r n i j (p : PolynomialSpace r n) = 0) :
    polarization r n i j
      ((simultaneousHarmonicProjection r n m p).val :
        PolynomialSpace r n) = 0 := by
  have hhom : homogeneousPolarization r n m i j p = 0 := by
    apply Subtype.ext
    exact hp
  calc
    polarization r n i j
        ((simultaneousHarmonicProjection r n m p).val :
          PolynomialSpace r n) =
      (((simultaneousHarmonicProjection r n m
        (homogeneousPolarization r n m i j p)).val :
          SpherePacking.Fischer.Homogeneous ((r + 1) * n) m) :
            PolynomialSpace r n) :=
        (simultaneousHarmonicProjection_polarization_coe i j p).symm
    _ = 0 := by rw [hhom, map_zero]; rfl


-- @@ L4482-4490 verbatim
/-- The homogeneous young highest weight submodule used in the spherical-code argument. -/
def homogeneousYoungHighestWeightSubmodule {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    Submodule ℝ
      (SpherePacking.Fischer.Homogeneous ((r + 1) * n)
        (∑ i, lam i)) :=
  (rowWeightSubmodule (n := n) lam ⊓ highestWeightSubmodule r n).comap
    (MvPolynomial.homogeneousSubmodule
      (Fin ((r + 1) * n)) ℝ (∑ i, lam i)).subtype


-- @@ L4492-4506 verbatim
@[simp] theorem mem_homogeneousYoungHighestWeightSubmodule
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (p : SpherePacking.Fischer.Homogeneous ((r + 1) * n)
      (∑ i, lam i)) :
    p ∈ homogeneousYoungHighestWeightSubmodule (n := n) lam ↔
      (∀ i : Fin (r + 1),
        rowEuler r n i (p : PolynomialSpace r n) =
          (lam i : ℝ) • (p : PolynomialSpace r n)) ∧
      (∀ i j : Fin (r + 1), i < j →
        polarization r n i j (p : PolynomialSpace r n) = 0) := by
  change
    (p : PolynomialSpace r n) ∈
      rowWeightSubmodule lam ⊓ highestWeightSubmodule r n ↔ _
  simp only [Submodule.mem_inf, mem_rowWeightSubmodule,
    mem_highestWeightSubmodule]


-- @@ L4508-4526 verbatim
/-- The harmonic young highest weight embedding used in the spherical-code argument. -/
def harmonicYoungHighestWeightEmbedding {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    HarmonicYoungSpace (n := n) lam →ₗ[ℝ]
      homogeneousYoungHighestWeightSubmodule (n := n) lam where
  toFun p :=
    ⟨youngHomogeneousEmbedding lam p,
      (mem_homogeneousYoungHighestWeightSubmodule lam
        (youngHomogeneousEmbedding lam p)).mpr
        ⟨((mem_harmonicYoungSubmodule lam
          (p : PolynomialSpace r n)).mp p.property).2.1,
          ((mem_harmonicYoungSubmodule lam
            (p : PolynomialSpace r n)).mp p.property).2.2.2⟩⟩
  map_add' p q := by
    apply Subtype.ext
    exact map_add (youngHomogeneousEmbedding lam) p q
  map_smul' c p := by
    apply Subtype.ext
    exact map_smul (youngHomogeneousEmbedding lam) c p


-- @@ L4528-4567 verbatim
/-- The young harmonic lift used in the spherical-code argument. -/
def youngHarmonicLift {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    homogeneousYoungHighestWeightSubmodule (n := n) lam →ₗ[ℝ]
      HarmonicYoungSpace (n := n) lam where
  toFun p :=
    ⟨((simultaneousHarmonicProjection r n (∑ i, lam i)
      p.val).val : PolynomialSpace r n), by
      rw [mem_harmonicYoungSubmodule]
      have hseed :=
        (mem_homogeneousYoungHighestWeightSubmodule lam p.val).mp
          p.property
      refine ⟨(simultaneousHarmonicProjection r n
        (∑ i, lam i) p.val).val.property, ?_, ?_, ?_⟩
      · intro i
        exact simultaneousHarmonicProjection_rowWeight i (lam i)
          p.val (hseed.1 i)
      · intro i j
        exact simultaneousHarmonicProjection_traceOperator p.val i j
      · intro i j hij
        exact simultaneousHarmonicProjection_polarization_eq_zero
          i j p.val (hseed.2 i j hij)⟩
  map_add' p q := by
    apply Subtype.ext
    change
      (((simultaneousHarmonicProjection r n (∑ i, lam i)
          (p.val + q.val)).val :
            SpherePacking.Fischer.Homogeneous ((r + 1) * n)
              (∑ i, lam i)) : PolynomialSpace r n) = _
    rw [map_add]
    rfl
  map_smul' c p := by
    apply Subtype.ext
    change
      (((simultaneousHarmonicProjection r n (∑ i, lam i)
          (c • p.val)).val :
            SpherePacking.Fischer.Homogeneous ((r + 1) * n)
              (∑ i, lam i)) : PolynomialSpace r n) = _
    rw [map_smul]
    rfl


-- @@ L4569-4569 verbatim
end



-- @@ L4572-4572 verbatim
section



-- @@ L4575-4575 verbatim
open scoped BigOperators


-- @@ L4577-4604 verbatim
theorem mem_youngMultihomogeneousSubmodule_iff_rowEuler
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (p : PolynomialSpace r n) :
    p ∈ youngMultihomogeneousSubmodule n lam ↔
      ∀ i : Fin (r + 1), rowEuler r n i p = (lam i : ℝ) • p := by
  constructor
  · intro hp i
    exact youngMultihomogeneous_rowEuler lam ⟨p, hp⟩ i
  · intro hp
    change p.support ⊆ youngMultihomogeneousExponents n lam
    intro d hd
    have hdne : p.coeff d ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hd
    have hdegree : ∀ i : Fin (r + 1),
        (rowExponent d i).degree = lam i := by
      intro i
      have heuler := congrArg (·.coeff d) (hp i)
      rw [coeff_rowEuler, MvPolynomial.coeff_smul] at heuler
      have hmul :
          ((rowExponent d i).degree : ℝ) * p.coeff d =
            (lam i : ℝ) * p.coeff d := by
        simpa only [mul_eq_mul_right_iff, Nat.cast_inj, nsmul_eq_mul, smul_eq_mul] using heuler
      exact_mod_cast mul_right_cancel₀ hdne hmul
    unfold youngMultihomogeneousExponents
    rw [Finset.mem_image]
    exact ⟨fun i => rowExponent d i,
      (mem_rowDegreeFamilies lam _).mpr hdegree,
      flattenRowExponents_rowExponent d⟩


-- @@ L4606-4619 verbatim
theorem polarization_mul_euler {r n : ℕ}
    (i j : Fin (r + 1)) (p q : PolynomialSpace r n) :
    polarization r n i j (p * q) =
      polarization r n i j p * q + p * polarization r n i j q := by
  classical
  simp only [polarization_apply, MvPolynomial.pderiv_mul,
    mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro k _
    ring
  · apply Finset.sum_congr rfl
    intro k _
    ring


-- @@ L4621-4634 verbatim
theorem polarization_X_euler {r n : ℕ}
    (i j a : Fin (r + 1)) (k : Fin n) :
    polarization r n i j (MvPolynomial.X (variableIndex a k)) =
      if j = a then MvPolynomial.X (variableIndex i k) else 0 := by
  classical
  by_cases h : j = a
  · subst a
    simp only [polarization_apply, MvPolynomial.pderiv_X, Pi.single_apply,
      variableIndex_eq_iff_harmonicLift, true_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte]
  · have h' : a ≠ j := Ne.symm h
    simp only [polarization_apply, MvPolynomial.pderiv_X, ne_eq, variableIndex_eq_iff_harmonicLift,
      h', false_and, not_false_eq_true, Pi.single_eq_of_ne, mul_zero, Finset.sum_const_zero, h,
      ↓reduceIte]


-- @@ L4636-4680 verbatim
theorem rowEuler_polarization_commutator {r n : ℕ}
    (a i j : Fin (r + 1)) (p : PolynomialSpace r n) :
    rowEuler r n a (polarization r n i j p) =
      polarization r n i j (rowEuler r n a p) +
        (if a = i then polarization r n i j p else 0) -
          (if a = j then polarization r n i j p else 0) := by
  classical
  let S : PolynomialSpace r n :=
    ∑ k : Fin n,
      MvPolynomial.X (variableIndex a k) *
        polarization r n i j
          (MvPolynomial.pderiv (variableIndex a k) p)
  have hleft :
      rowEuler r n a (polarization r n i j p) =
        (if a = i then polarization r n i j p else 0) + S := by
    rw [rowEuler_apply]
    simp_rw [pderiv_polarization_harmonicLift, mul_add,
      Finset.sum_add_distrib]
    by_cases hai : a = i
    · subst a
      simp only [↓reduceIte, polarization_apply, S]
    · simp only [hai, ↓reduceIte, mul_zero, Finset.sum_const_zero, polarization_apply, zero_add, S]
  have hright :
      polarization r n i j (rowEuler r n a p) =
        (if j = a then polarization r n i j p else 0) + S := by
    rw [rowEuler_apply, map_sum]
    simp_rw [polarization_mul_euler, polarization_X_euler,
      Finset.sum_add_distrib]
    by_cases hja : j = a
    · subst a
      simp only [↓reduceIte, polarization_apply, S]
    · simp only [hja, ↓reduceIte, zero_mul, Finset.sum_const_zero, polarization_apply, zero_add, S]
  rw [hleft, hright]
  by_cases hai : a = i
  · subst i
    by_cases hja : j = a
    · subst j
      simp
    · have haj : a ≠ j := Ne.symm hja
      simp only [↓reduceIte, polarization_apply, hja, zero_add, haj, sub_zero]; abel
  · by_cases hja : j = a
    · subst j
      simp only [hai, ↓reduceIte, zero_add, polarization_apply, add_zero, add_sub_cancel_left]
    · have haj : a ≠ j := Ne.symm hja
      simp only [hai, ↓reduceIte, zero_add, hja, add_zero, haj, sub_zero]


-- @@ L4682-4711 verbatim
theorem polarization_mem_youngMultihomogeneous_transfer
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (i j : Fin (r + 1)) (hij : i ≠ j)
    {p : PolynomialSpace r n}
    (hp : p ∈ youngMultihomogeneousSubmodule n
      (Function.update lam j (lam j + 1))) :
    polarization r n i j p ∈ youngMultihomogeneousSubmodule n
      (Function.update lam i (lam i + 1)) := by
  have hweight :=
    (mem_youngMultihomogeneousSubmodule_iff_rowEuler
      (Function.update lam j (lam j + 1)) p).mp hp
  apply
    (mem_youngMultihomogeneousSubmodule_iff_rowEuler
      (Function.update lam i (lam i + 1)) _).mpr
  intro k
  rw [rowEuler_polarization_commutator, hweight k, map_smul]
  by_cases hki : k = i
  · subst k
    have hji : j ≠ i := Ne.symm hij
    simp only [Function.update, hij, ↓reduceDIte, polarization_apply, ↓reduceIte, sub_zero,
      Nat.cast_add, Nat.cast_one, add_smul, one_smul]
  · by_cases hkj : k = j
    · subst k
      have hji : j ≠ i := Ne.symm hij
      simp only [Function.update, ↓reduceDIte, Nat.cast_add, Nat.cast_one, polarization_apply,
        add_smul, one_smul, hji, ↓reduceIte, add_zero, add_sub_cancel_right]
    · have hki' : i ≠ k := Ne.symm hki
      have hkj' : j ≠ k := Ne.symm hkj
      simp only [Function.update, hkj, ↓reduceDIte, polarization_apply, hki, ↓reduceIte, add_zero,
        sub_zero]


-- @@ L4713-4713 verbatim
end



-- @@ L4716-4716 verbatim
section



-- @@ L4719-4719 verbatim
open scoped BigOperators InnerProductSpace


-- @@ L4721-4721 verbatim
section DoubleQuadraticRoots


-- @@ L4723-4723 verbatim
open Polynomial Module


-- @@ L4725-4725 verbatim
variable {R : Type*} [CommRing R]


-- @@ L4727-4727 verbatim
variable [IsDomain R]


-- @@ L4729-4729 verbatim
end DoubleQuadraticRoots


-- @@ L4731-4731 verbatim
end


-- @@ L4733-4733 verbatim
section



-- @@ L4736-4758 verbatim
theorem youngMultihomogeneous_pderiv_eq_zero_of_rowDegree_zero
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (p : youngMultihomogeneousSubmodule n lam)
    (a : Fin (r + 1)) (ha : lam a = 0) (k : Fin n) :
    MvPolynomial.pderiv (variableIndex a k)
      (p : PolynomialSpace r n) = 0 := by
  classical
  apply MvPolynomial.ext
  intro d
  rw [MvPolynomial.coeff_pderiv]
  have hcoeff :
      (p : PolynomialSpace r n).coeff
          (d + Finsupp.single (variableIndex a k) 1) = 0 := by
    by_contra hnonzero
    have hdegree := youngMultihomogeneous_rowExponent_degree
      lam p.property hnonzero a
    have hrow :
        rowExponent (d + Finsupp.single (variableIndex a k) 1) a = 0 :=
      (Finsupp.degree_eq_zero_iff _).mp (hdegree.trans ha)
    have hcoordinate := congrArg (fun e : Fin n →₀ ℕ => e k) hrow
    simp only [rowExponent_apply, Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same,
      Finsupp.coe_zero, Pi.zero_apply, Nat.add_eq_zero_iff, one_ne_zero, and_false] at hcoordinate
  simp only [hcoeff, zero_mul, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]


-- @@ L4760-4769 verbatim
theorem youngMultihomogeneous_polarization_eq_zero_of_rowDegree_zero
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (p : youngMultihomogeneousSubmodule n lam)
    (a b : Fin (r + 1)) (hb : lam b = 0) :
    polarization r n a b (p : PolynomialSpace r n) = 0 := by
  rw [polarization_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [youngMultihomogeneous_pderiv_eq_zero_of_rowDegree_zero
    lam p b hb k, mul_zero]


-- @@ L4771-4771 verbatim
end


-- @@ L4773-4773 verbatim
section



-- @@ L4776-4776 verbatim
open scoped BigOperators InnerProductSpace


-- @@ L4778-4778 verbatim
namespace BranchingDimension


-- @@ L4780-4780 verbatim
open MetricCodes.Spherical.HigherHierarchy

-- @@ L4781-4781 verbatim
open MetricCodes.Spherical.HigherYoungGraphAssembly

-- @@ L4782-4782 verbatim
open MetricCodes.Spherical.MixedTensorRepresentations


-- @@ L4784-4787 verbatim
/-- The full branch weight used in the spherical-code argument. -/
def FullBranchWeight {r : ℕ} (lam : Fin (r + 1) → ℕ) :=
  { mu : (∀ i : Fin (r + 1), Fin (lam i + 1)) //
      ∀ i : Fin r, lam i.succ ≤ (mu i.castSucc).val }


-- @@ L4789-4793 verbatim
instance fullBranchWeightFintype {r : ℕ}
    (lam : Fin (r + 1) → ℕ) : Fintype (FullBranchWeight lam) := by
  classical
  unfold FullBranchWeight
  infer_instance


-- @@ L4795-4797 verbatim
noncomputable instance fullBranchWeightDecidableEq {r : ℕ}
    (lam : Fin (r + 1) → ℕ) : DecidableEq (FullBranchWeight lam) :=
  Classical.decEq _


-- @@ L4799-4803 verbatim
/-- The full branch signature used in the spherical-code argument. -/
def fullBranchSignature {r : ℕ}
    {lam : Fin (r + 1) → ℕ}
    (mu : FullBranchWeight lam) : Fin (r + 1) → ℕ :=
  fun i => (mu.val i).val


-- @@ L4805-4810 verbatim
theorem fullBranchSignature_le {r : ℕ}
    {lam : Fin (r + 1) → ℕ}
    (mu : FullBranchWeight lam) (i : Fin (r + 1)) :
    fullBranchSignature mu i ≤ lam i := by
  have h := (mu.val i).isLt
  exact Nat.lt_succ_iff.mp h


-- @@ L4812-4816 verbatim
theorem fullBranchSignature_succ_le {r : ℕ}
    {lam : Fin (r + 1) → ℕ}
    (mu : FullBranchWeight lam) (i : Fin r) :
    lam i.succ ≤ fullBranchSignature mu i.castSucc :=
  mu.property i


-- @@ L4818-4824 verbatim
theorem fullBranchSignature_antitone {r : ℕ}
    {lam : Fin (r + 1) → ℕ}
    (mu : FullBranchWeight lam) : Antitone (fullBranchSignature mu) := by
  apply Fin.antitone_iff_succ_le.mpr
  intro i
  exact (fullBranchSignature_le mu i.succ).trans
    (fullBranchSignature_succ_le mu i)


-- @@ L4826-4842 verbatim
/-- The full branch of interlaces used in the spherical-code argument. -/
def fullBranchOfInterlaces {r : ℕ}
    {lam : Fin (r + 1) → ℕ}
    (mu : Fin r → ℕ)
    (h : MetricCodes.Spherical.HigherRepresentationGraph.Interlaces
      lam mu) : FullBranchWeight lam := by
  let signature : Fin (r + 1) → ℕ := Fin.snoc mu 0
  let weight : ∀ i : Fin (r + 1), Fin (lam i + 1) :=
    fun i => ⟨signature i, by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Fin.snoc_last, lt_add_iff_pos_left, Order.lt_add_one_iff, zero_le, signature]
      · simp only [Fin.snoc_castSucc, Order.lt_add_one_iff, signature]
        exact (h j).1⟩
  refine ⟨weight, ?_⟩
  intro i
  change lam i.succ ≤ signature i.castSucc
  simpa [signature] using (h i).2


-- @@ L4844-4851 verbatim
@[simp] theorem fullBranchOfInterlaces_castSucc {r : ℕ}
    {lam : Fin (r + 1) → ℕ}
    (mu : Fin r → ℕ)
    (h : MetricCodes.Spherical.HigherRepresentationGraph.Interlaces
      lam mu) (i : Fin r) :
    fullBranchSignature (fullBranchOfInterlaces mu h) i.castSucc =
      mu i := by
  simp [fullBranchOfInterlaces, fullBranchSignature]


-- @@ L4853-4860 verbatim
@[simp] theorem fullBranchOfInterlaces_last {r : ℕ}
    {lam : Fin (r + 1) → ℕ}
    (mu : Fin r → ℕ)
    (h : MetricCodes.Spherical.HigherRepresentationGraph.Interlaces
      lam mu) :
    fullBranchSignature (fullBranchOfInterlaces mu h) (Fin.last r) =
      0 := by
  simp [fullBranchOfInterlaces, fullBranchSignature]


-- @@ L4862-4871 verbatim
theorem fullBranchOfInterlaces_signature {r : ℕ}
    {lam : Fin (r + 1) → ℕ}
    (mu : Fin r → ℕ)
    (h : MetricCodes.Spherical.HigherRepresentationGraph.Interlaces
      lam mu) :
    fullBranchSignature (fullBranchOfInterlaces mu h) = Fin.snoc mu 0 := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [fullBranchOfInterlaces_last, Fin.snoc_last]
  · simp only [fullBranchOfInterlaces_castSucc, Fin.snoc_castSucc]


-- @@ L4873-4878 verbatim
/-- The weyl branching recurrence used in the spherical-code argument. -/
def WeylBranchingRecurrence {r : ℕ} (n : ℕ)
    (lam : Fin (r + 1) → ℕ) : Prop :=
  Weyl.dimension n lam =
    ∑ mu : FullBranchWeight lam,
      Weyl.dimension (n - 1) (fullBranchSignature mu)


-- @@ L4880-4880 verbatim
end BranchingDimension


-- @@ L4882-4882 verbatim
end


-- @@ L4884-4884 verbatim
section



-- @@ L4887-4887 verbatim
open scoped BigOperators


-- @@ L4889-4894 verbatim
/-- The polynomial real part used in the spherical-code argument. -/
def polynomialRealPart {σ : Type*} :
    MvPolynomial σ ℂ →ₗ[ℝ] MvPolynomial σ ℝ :=
  (AddMonoidAlgebra.coeffLinearEquiv ℝ).symm.toLinearMap.comp
    ((Finsupp.mapRange.linearMap Complex.reLm).comp
      (AddMonoidAlgebra.coeffLinearEquiv ℝ).toLinearMap)


-- @@ L4896-4901 verbatim
/-- The polynomial imaginary part used in the spherical-code argument. -/
def polynomialImaginaryPart {σ : Type*} :
    MvPolynomial σ ℂ →ₗ[ℝ] MvPolynomial σ ℝ :=
  (AddMonoidAlgebra.coeffLinearEquiv ℝ).symm.toLinearMap.comp
    ((Finsupp.mapRange.linearMap Complex.imLm).comp
      (AddMonoidAlgebra.coeffLinearEquiv ℝ).toLinearMap)


-- @@ L4903-4905 verbatim
@[simp] theorem coeff_polynomialRealPart {σ : Type*}
    (p : MvPolynomial σ ℂ) (d : σ →₀ ℕ) :
    (polynomialRealPart p).coeff d = (p.coeff d).re := rfl


-- @@ L4907-4909 verbatim
@[simp] theorem coeff_polynomialImaginaryPart {σ : Type*}
    (p : MvPolynomial σ ℂ) (d : σ →₀ ℕ) :
    (polynomialImaginaryPart p).coeff d = (p.coeff d).im := rfl


-- @@ L4911-4929 verbatim
theorem polynomialRealPart_ne_zero_or_polynomialImaginaryPart_ne_zero
    {σ : Type*} {p : MvPolynomial σ ℂ} (hp : p ≠ 0) :
    polynomialRealPart p ≠ 0 ∨ polynomialImaginaryPart p ≠ 0 := by
  obtain ⟨d, hd⟩ := MvPolynomial.ne_zero_iff.mp hp
  by_cases hre : (p.coeff d).re = 0
  · right
    intro him
    have hi : (p.coeff d).im = 0 := by
      simpa only [coeff_polynomialImaginaryPart, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero,
        Pi.zero_apply] using
        congrArg (fun q : MvPolynomial σ ℝ => q.coeff d) him
    apply hd
    apply Complex.ext <;> simp [hre, hi]
  · left
    intro hreal
    exact hre (by
      simpa only [coeff_polynomialRealPart, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero,
        Pi.zero_apply] using
        congrArg (fun q : MvPolynomial σ ℝ => q.coeff d) hreal)


-- @@ L4931-4939 verbatim
theorem polynomialRealPart_pderiv {σ : Type*} (i : σ)
    (p : MvPolynomial σ ℂ) :
    polynomialRealPart (MvPolynomial.pderiv i p) =
      MvPolynomial.pderiv i (polynomialRealPart p) := by
  apply MvPolynomial.ext
  intro d
  simp only [coeff_polynomialRealPart, MvPolynomial.coeff_pderiv, Complex.mul_re, Complex.add_re,
    Complex.natCast_re, Complex.one_re, Complex.add_im, Complex.natCast_im, Complex.one_im,
    add_zero, mul_zero, sub_zero]


-- @@ L4941-4949 verbatim
theorem polynomialImaginaryPart_pderiv {σ : Type*} (i : σ)
    (p : MvPolynomial σ ℂ) :
    polynomialImaginaryPart (MvPolynomial.pderiv i p) =
      MvPolynomial.pderiv i (polynomialImaginaryPart p) := by
  apply MvPolynomial.ext
  intro d
  simp only [coeff_polynomialImaginaryPart, MvPolynomial.coeff_pderiv, Complex.mul_im,
    Complex.add_im, Complex.natCast_im, Complex.one_im, add_zero, mul_zero, Complex.add_re,
    Complex.natCast_re, Complex.one_re, zero_add]


-- @@ L4951-4958 verbatim
theorem polynomialRealPart_X_mul {σ : Type*} (i : σ)
    (p : MvPolynomial σ ℂ) :
    polynomialRealPart (MvPolynomial.X i * p) =
      MvPolynomial.X i * polynomialRealPart p := by
  classical
  apply MvPolynomial.ext
  intro d
  by_cases h : d i = 0 <;> simp [MvPolynomial.coeff_X_mul', h]


-- @@ L4960-4967 verbatim
theorem polynomialImaginaryPart_X_mul {σ : Type*} (i : σ)
    (p : MvPolynomial σ ℂ) :
    polynomialImaginaryPart (MvPolynomial.X i * p) =
      MvPolynomial.X i * polynomialImaginaryPart p := by
  classical
  apply MvPolynomial.ext
  intro d
  by_cases h : d i = 0 <;> simp [MvPolynomial.coeff_X_mul', h]


-- @@ L4969-4976 verbatim
theorem polynomialRealPart_isHomogeneous {σ : Type*}
    {p : MvPolynomial σ ℂ} {k : ℕ}
    (hp : p.IsHomogeneous k) :
    (polynomialRealPart p).IsHomogeneous k := by
  intro d hd
  apply hp
  intro hzero
  exact hd (by simp only [coeff_polynomialRealPart, hzero, Complex.zero_re])


-- @@ L4978-4985 verbatim
theorem polynomialImaginaryPart_isHomogeneous {σ : Type*}
    {p : MvPolynomial σ ℂ} {k : ℕ}
    (hp : p.IsHomogeneous k) :
    (polynomialImaginaryPart p).IsHomogeneous k := by
  intro d hd
  apply hp
  intro hzero
  exact hd (by simp only [coeff_polynomialImaginaryPart, hzero, Complex.zero_im])


-- @@ L4987-4993 verbatim
/-- The complex row euler used in the spherical-code argument. -/
def complexRowEuler {r n : ℕ} (i : Fin (r + 1))
    (p : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    MvPolynomial (Fin ((r + 1) * n)) ℂ :=
  ∑ j : Fin n,
    MvPolynomial.X (variableIndex i j) *
      MvPolynomial.pderiv (variableIndex i j) p


-- @@ L4995-5001 verbatim
/-- The complex trace operator used in the spherical-code argument. -/
def complexTraceOperator {r n : ℕ} (i j : Fin (r + 1))
    (p : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    MvPolynomial (Fin ((r + 1) * n)) ℂ :=
  ∑ k : Fin n,
    MvPolynomial.pderiv (variableIndex i k)
      (MvPolynomial.pderiv (variableIndex j k) p)


-- @@ L5003-5009 verbatim
/-- The complex polarization used in the spherical-code argument. -/
def complexPolarization {r n : ℕ} (i j : Fin (r + 1))
    (p : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    MvPolynomial (Fin ((r + 1) * n)) ℂ :=
  ∑ k : Fin n,
    MvPolynomial.X (variableIndex i k) *
      MvPolynomial.pderiv (variableIndex j k) p


-- @@ L5011-5016 verbatim
theorem polynomialRealPart_complexRowEuler {r n : ℕ}
    (i : Fin (r + 1)) (p : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    polynomialRealPart (complexRowEuler i p) =
      rowEuler r n i (polynomialRealPart p) := by
  simp only [complexRowEuler, map_sum, polynomialRealPart_X_mul,
    polynomialRealPart_pderiv, rowEuler_apply]


-- @@ L5018-5023 verbatim
theorem polynomialImaginaryPart_complexRowEuler {r n : ℕ}
    (i : Fin (r + 1)) (p : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    polynomialImaginaryPart (complexRowEuler i p) =
      rowEuler r n i (polynomialImaginaryPart p) := by
  simp only [complexRowEuler, map_sum, polynomialImaginaryPart_X_mul,
    polynomialImaginaryPart_pderiv, rowEuler_apply]


-- @@ L5025-5030 verbatim
theorem polynomialRealPart_complexTraceOperator {r n : ℕ}
    (i j : Fin (r + 1)) (p : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    polynomialRealPart (complexTraceOperator i j p) =
      traceOperator r n i j (polynomialRealPart p) := by
  simp only [complexTraceOperator, map_sum, polynomialRealPart_pderiv,
    traceOperator_apply]


-- @@ L5032-5037 verbatim
theorem polynomialImaginaryPart_complexTraceOperator {r n : ℕ}
    (i j : Fin (r + 1)) (p : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    polynomialImaginaryPart (complexTraceOperator i j p) =
      traceOperator r n i j (polynomialImaginaryPart p) := by
  simp only [complexTraceOperator, map_sum,
    polynomialImaginaryPart_pderiv, traceOperator_apply]


-- @@ L5039-5044 verbatim
theorem polynomialRealPart_complexPolarization {r n : ℕ}
    (i j : Fin (r + 1)) (p : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    polynomialRealPart (complexPolarization i j p) =
      polarization r n i j (polynomialRealPart p) := by
  simp only [complexPolarization, map_sum, polynomialRealPart_X_mul,
    polynomialRealPart_pderiv, polarization_apply]


-- @@ L5046-5052 verbatim
theorem polynomialImaginaryPart_complexPolarization {r n : ℕ}
    (i j : Fin (r + 1)) (p : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    polynomialImaginaryPart (complexPolarization i j p) =
      polarization r n i j (polynomialImaginaryPart p) := by
  simp only [complexPolarization, map_sum,
    polynomialImaginaryPart_X_mul, polynomialImaginaryPart_pderiv,
    polarization_apply]


-- @@ L5054-5066 verbatim
/-- Data encoding the complex highest weight witness construction. -/
structure ComplexHighestWeightWitness {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) where
  /-- The polynomial component. -/
  polynomial : MvPolynomial (Fin ((r + 1) * n)) ℂ
  nonzero : polynomial ≠ 0
  homogeneous : polynomial.IsHomogeneous (∑ i, lam i)
  rowEuler : ∀ i : Fin (r + 1),
    complexRowEuler i polynomial = (lam i : ℝ) • polynomial
  traceFree : ∀ i j : Fin (r + 1),
    complexTraceOperator i j polynomial = 0
  highestWeight : ∀ i j : Fin (r + 1), i < j →
    complexPolarization i j polynomial = 0


-- @@ L5068-5081 verbatim
theorem ComplexHighestWeightWitness.realPart_mem {r n : ℕ}
    {lam : Fin (r + 1) → ℕ}
    (w : ComplexHighestWeightWitness (n := n) lam) :
    polynomialRealPart w.polynomial ∈
      harmonicYoungSubmodule (n := n) lam := by
  rw [mem_harmonicYoungSubmodule]
  refine ⟨polynomialRealPart_isHomogeneous w.homogeneous, ?_, ?_, ?_⟩
  · intro i
    rw [← polynomialRealPart_complexRowEuler, w.rowEuler, map_smul]
  · intro i j
    rw [← polynomialRealPart_complexTraceOperator, w.traceFree, map_zero]
  · intro i j hij
    rw [← polynomialRealPart_complexPolarization,
      w.highestWeight i j hij, map_zero]


-- @@ L5083-5098 verbatim
theorem ComplexHighestWeightWitness.imaginaryPart_mem {r n : ℕ}
    {lam : Fin (r + 1) → ℕ}
    (w : ComplexHighestWeightWitness (n := n) lam) :
    polynomialImaginaryPart w.polynomial ∈
      harmonicYoungSubmodule (n := n) lam := by
  rw [mem_harmonicYoungSubmodule]
  refine ⟨polynomialImaginaryPart_isHomogeneous w.homogeneous,
    ?_, ?_, ?_⟩
  · intro i
    rw [← polynomialImaginaryPart_complexRowEuler, w.rowEuler, map_smul]
  · intro i j
    rw [← polynomialImaginaryPart_complexTraceOperator,
      w.traceFree, map_zero]
  · intro i j hij
    rw [← polynomialImaginaryPart_complexPolarization,
      w.highestWeight i j hij, map_zero]


-- @@ L5100-5112 verbatim
theorem exists_nonzero_harmonicYoung_of_complexWitness {r n : ℕ}
    {lam : Fin (r + 1) → ℕ}
    (w : ComplexHighestWeightWitness (n := n) lam) :
    ∃ p : HarmonicYoungSpace (n := n) lam, p ≠ 0 := by
  rcases polynomialRealPart_ne_zero_or_polynomialImaginaryPart_ne_zero
    w.nonzero with hreal | himaginary
  · refine ⟨⟨polynomialRealPart w.polynomial, w.realPart_mem⟩, ?_⟩
    intro hzero
    exact hreal (congrArg Subtype.val hzero)
  · refine ⟨⟨polynomialImaginaryPart w.polynomial, w.imaginaryPart_mem⟩,
      ?_⟩
    intro hzero
    exact himaginary (congrArg Subtype.val hzero)


-- @@ L5114-5119 verbatim
theorem finrank_harmonicYoung_pos_of_complexWitness {r n : ℕ}
    {lam : Fin (r + 1) → ℕ}
    (w : ComplexHighestWeightWitness (n := n) lam) :
    0 < Module.finrank ℝ (HarmonicYoungSpace (n := n) lam) := by
  exact Module.finrank_pos_iff_exists_ne_zero.mpr
    (exists_nonzero_harmonicYoung_of_complexWitness w)


-- @@ L5121-5124 verbatim
/-- The even coordinate `2 * i` in the ambient space reserved for a null-coordinate pair. -/
def nullEvenCoordinate {m n : ℕ} (hn : 2 * m ≤ n)
    (i : Fin m) : Fin n :=
  ⟨2 * i.val, by have hi := i.isLt; omega⟩


-- @@ L5126-5129 verbatim
/-- The odd coordinate `2 * i + 1` in the ambient space reserved for a null-coordinate pair. -/
def nullOddCoordinate {m n : ℕ} (hn : 2 * m ≤ n)
    (i : Fin m) : Fin n :=
  ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩


-- @@ L5131-5141 verbatim
@[simp] theorem nullEvenCoordinate_inj {m n : ℕ} (hn : 2 * m ≤ n)
    {i j : Fin m} : nullEvenCoordinate hn i = nullEvenCoordinate hn j ↔
      i = j := by
  constructor
  · intro h
    apply Fin.ext
    have hval := congrArg Fin.val h
    dsimp [nullEvenCoordinate] at hval
    omega
  · intro h
    exact congrArg (nullEvenCoordinate hn) h


-- @@ L5143-5153 verbatim
@[simp] theorem nullOddCoordinate_inj {m n : ℕ} (hn : 2 * m ≤ n)
    {i j : Fin m} : nullOddCoordinate hn i = nullOddCoordinate hn j ↔
      i = j := by
  constructor
  · intro h
    apply Fin.ext
    have hval := congrArg Fin.val h
    dsimp [nullOddCoordinate] at hval
    omega
  · intro h
    exact congrArg (nullOddCoordinate hn) h


-- @@ L5155-5161 verbatim
theorem nullEvenCoordinate_ne_nullOddCoordinate {m n : ℕ}
    (hn : 2 * m ≤ n) (i j : Fin m) :
    nullEvenCoordinate hn i ≠ nullOddCoordinate hn j := by
  intro h
  have hval := congrArg Fin.val h
  dsimp [nullEvenCoordinate, nullOddCoordinate] at hval
  omega


-- @@ L5163-5169 verbatim
/-- The complex coefficients `1` and `I` on the even and odd coordinates of a null pair, and
zero elsewhere. -/
def nullCoordinateCoefficient {m n : ℕ} (hn : 2 * m ≤ n)
    (i : Fin m) (k : Fin n) : ℂ :=
  if k = nullEvenCoordinate hn i then 1
  else if k = nullOddCoordinate hn i then Complex.I
  else 0


-- @@ L5171-5210 verbatim
theorem sum_nullCoordinateCoefficient_mul {m n : ℕ}
    (hn : 2 * m ≤ n) (i j : Fin m) :
    (∑ k : Fin n,
      nullCoordinateCoefficient hn i k *
        nullCoordinateCoefficient hn j k) = 0 := by
  classical
  have hsplit (k : Fin n) :
      nullCoordinateCoefficient hn i k *
          nullCoordinateCoefficient hn j k =
        (if k = nullEvenCoordinate hn i then
          nullCoordinateCoefficient hn j k else 0) +
        (if k = nullOddCoordinate hn i then
          Complex.I * nullCoordinateCoefficient hn j k else 0) := by
    by_cases he : k = nullEvenCoordinate hn i
    · subst k
      have hne := nullEvenCoordinate_ne_nullOddCoordinate hn i i
      simp only [nullCoordinateCoefficient, ↓reduceIte, nullEvenCoordinate_inj, mul_ite, mul_one,
        one_mul, mul_zero, hne, add_zero]
    · by_cases ho : k = nullOddCoordinate hn i
      · subst k
        have hne := nullEvenCoordinate_ne_nullOddCoordinate hn i i
        simp only [nullCoordinateCoefficient, Ne.symm hne, ↓reduceIte, nullOddCoordinate_inj,
          mul_ite, mul_one, Complex.I_mul_I, mul_zero, zero_add]
      · simp only [nullCoordinateCoefficient, he, ↓reduceIte, ho, mul_ite, mul_one, zero_mul,
          mul_zero, ite_self, add_zero]
  simp_rw [hsplit, Finset.sum_add_distrib, Fintype.sum_ite_eq']
  by_cases hij : i = j
  · subst j
    have hne := nullEvenCoordinate_ne_nullOddCoordinate hn i i
    simp only [nullCoordinateCoefficient, ↓reduceIte, Ne.symm hne, Complex.I_mul_I, add_neg_cancel]
  · have heven :
        nullEvenCoordinate hn i ≠ nullEvenCoordinate hn j :=
      fun h => hij ((nullEvenCoordinate_inj hn).mp h)
    have hodd :
        nullOddCoordinate hn i ≠ nullOddCoordinate hn j :=
      fun h => hij ((nullOddCoordinate_inj hn).mp h)
    have heo := nullEvenCoordinate_ne_nullOddCoordinate hn i j
    have hoe : nullOddCoordinate hn i ≠ nullEvenCoordinate hn j :=
      Ne.symm (nullEvenCoordinate_ne_nullOddCoordinate hn j i)
    simp only [nullCoordinateCoefficient, heven, ↓reduceIte, heo, hoe, hodd, mul_zero, add_zero]


-- @@ L5212-5221 verbatim
theorem variableIndex_eq_iff {r n : ℕ}
    (i j : Fin (r + 1)) (k l : Fin n) :
    variableIndex i k = variableIndex j l ↔ i = j ∧ k = l := by
  constructor
  · intro h
    have hp : (i, k) = (j, l) :=
      variableIndex_injective (r := r) (n := n) h
    exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
  · rintro ⟨rfl, rfl⟩
    rfl


-- @@ L5223-5229 verbatim
/-- The null row linear form used in the spherical-code argument. -/
def nullRowLinearForm {r m n : ℕ} (hn : 2 * m ≤ n)
    (i : Fin (r + 1)) (j : Fin m) :
    MvPolynomial (Fin ((r + 1) * n)) ℂ :=
  ∑ k : Fin n,
    MvPolynomial.C (nullCoordinateCoefficient hn j k) *
      MvPolynomial.X (variableIndex i k)


-- @@ L5231-5248 verbatim
theorem pderiv_nullRowLinearForm {r m n : ℕ}
    (hn : 2 * m ≤ n) (h i : Fin (r + 1))
    (j : Fin m) (k : Fin n) :
    MvPolynomial.pderiv (variableIndex h k)
        (nullRowLinearForm hn i j) =
      if h = i then MvPolynomial.C (nullCoordinateCoefficient hn j k)
      else 0 := by
  classical
  unfold nullRowLinearForm
  simp only [map_sum, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_C, zero_mul, zero_add,
    MvPolynomial.pderiv_X, Pi.single_apply,
    variableIndex_eq_iff]
  by_cases hi : h = i
  · subst i
    simp only [true_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte]
  · simp only [Ne.symm hi, false_and, ↓reduceIte, mul_zero, Finset.sum_const_zero, hi]


-- @@ L5250-5254 verbatim
/-- The null substitution used in the spherical-code argument. -/
def nullSubstitution {r m n : ℕ} (hn : 2 * m ≤ n) :
    MvPolynomial (Fin (r + 1) × Fin m) ℂ →ₐ[ℂ]
      MvPolynomial (Fin ((r + 1) * n)) ℂ :=
  MvPolynomial.aeval fun z => nullRowLinearForm hn z.1 z.2


-- @@ L5256-5260 verbatim
@[simp] theorem nullSubstitution_X {r m n : ℕ}
    (hn : 2 * m ≤ n) (i : Fin (r + 1)) (j : Fin m) :
    nullSubstitution (r := r) hn (MvPolynomial.X (i, j)) =
      nullRowLinearForm hn i j := by
  simp only [nullSubstitution, MvPolynomial.aeval_eq_bind₁, MvPolynomial.bind₁_X_right]


-- @@ L5262-5304 verbatim
theorem pderiv_nullSubstitution {r m n : ℕ}
    (hn : 2 * m ≤ n) (i : Fin (r + 1)) (k : Fin n)
    (q : MvPolynomial (Fin (r + 1) × Fin m) ℂ) :
    MvPolynomial.pderiv (variableIndex i k)
        (nullSubstitution (r := r) hn q) =
      ∑ j : Fin m,
        MvPolynomial.C (nullCoordinateCoefficient hn j k) *
          nullSubstitution hn
            (MvPolynomial.pderiv (i, j) q) := by
  classical
  induction q using MvPolynomial.induction_on with
  | C c =>
      simp only [nullSubstitution, MvPolynomial.aeval_eq_bind₁, MvPolynomial.algHom_C,
        MvPolynomial.algebraMap_eq, MvPolynomial.derivation_C, map_zero, mul_zero,
        Finset.sum_const_zero]
  | add p q hp hq =>
      simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X q z hq =>
      rcases z with ⟨h, j⟩
      simp only [map_mul, nullSubstitution_X,
        MvPolynomial.pderiv_mul, hq,
        pderiv_nullRowLinearForm,
        MvPolynomial.pderiv_X, Pi.single_apply,
        Prod.mk.injEq, map_add, map_mul,
        nullSubstitution_X]
      by_cases hrow : i = h
      · subst h
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
        congr 1
        · rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro x _
          ring
        · simp only [↓reduceIte, mul_comm, true_and, MonoidWithZeroHom.map_ite_one_zero, ite_mul,
            one_mul, zero_mul, mul_ite, Finset.sum_ite_eq, Finset.mem_univ]
      · have hrow' : h ≠ i := Ne.symm hrow
        simp only [hrow, hrow', false_and, ↓reduceIte,
          map_zero, mul_zero, add_zero]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        ring


-- @@ L5306-5332 verbatim
theorem complexTraceOperator_nullSubstitution {r m n : ℕ}
    (hn : 2 * m ≤ n) (i j : Fin (r + 1))
    (q : MvPolynomial (Fin (r + 1) × Fin m) ℂ) :
    complexTraceOperator i j (nullSubstitution hn q) = 0 := by
  classical
  unfold complexTraceOperator
  simp_rw [pderiv_nullSubstitution hn j,
    map_sum, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_C, zero_mul, zero_add,
    pderiv_nullSubstitution hn i,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro a _
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  have hnull :
      (∑ k : Fin n,
        (MvPolynomial.C (nullCoordinateCoefficient hn b k) :
          MvPolynomial (Fin ((r + 1) * n)) ℂ) *
            MvPolynomial.C (nullCoordinateCoefficient hn a k)) = 0 := by
    simp_rw [← map_mul]
    rw [← map_sum, sum_nullCoordinateCoefficient_mul hn b a, map_zero]
  rw [hnull, zero_mul]


-- @@ L5334-5338 verbatim
/-- The source polarization used in the spherical-code argument. -/
def sourcePolarization {r m : ℕ} (i j : Fin (r + 1))
    (q : MvPolynomial (Fin (r + 1) × Fin m) ℂ) :
    MvPolynomial (Fin (r + 1) × Fin m) ℂ :=
  ∑ a : Fin m, MvPolynomial.X (i, a) * MvPolynomial.pderiv (j, a) q


-- @@ L5340-5355 verbatim
theorem complexPolarization_nullSubstitution {r m n : ℕ}
    (hn : 2 * m ≤ n) (i j : Fin (r + 1))
    (q : MvPolynomial (Fin (r + 1) × Fin m) ℂ) :
    complexPolarization i j (nullSubstitution hn q) =
      nullSubstitution hn (sourcePolarization i j q) := by
  classical
  unfold complexPolarization sourcePolarization
  simp_rw [pderiv_nullSubstitution hn j, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [map_sum, map_mul, nullSubstitution_X]
  apply Finset.sum_congr rfl
  intro a _
  rw [nullRowLinearForm, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring


-- @@ L5357-5383 verbatim
theorem nullRowLinearForm_eq_even_add_I_odd {r m n : ℕ}
    (hn : 2 * m ≤ n) (i : Fin (r + 1)) (j : Fin m) :
    nullRowLinearForm hn i j =
      MvPolynomial.X (variableIndex i (nullEvenCoordinate hn j)) +
        MvPolynomial.C Complex.I *
          MvPolynomial.X (variableIndex i (nullOddCoordinate hn j)) := by
  classical
  unfold nullRowLinearForm
  have hsplit (k : Fin n) :
      MvPolynomial.C (nullCoordinateCoefficient hn j k) *
          MvPolynomial.X (variableIndex i k) =
        (if k = nullEvenCoordinate hn j then
          MvPolynomial.X (variableIndex i k) else 0) +
        (if k = nullOddCoordinate hn j then
          MvPolynomial.C Complex.I *
            MvPolynomial.X (variableIndex i k) else 0) := by
    by_cases he : k = nullEvenCoordinate hn j
    · subst k
      have hne := nullEvenCoordinate_ne_nullOddCoordinate hn j j
      simp only [nullCoordinateCoefficient, ↓reduceIte, MvPolynomial.C_1, one_mul, hne, add_zero]
    · by_cases ho : k = nullOddCoordinate hn j
      · subst k
        have hne := nullEvenCoordinate_ne_nullOddCoordinate hn j j
        simp only [nullCoordinateCoefficient, Ne.symm hne, ↓reduceIte, zero_add]
      · simp only [nullCoordinateCoefficient, he, ↓reduceIte, ho, MvPolynomial.C_0, zero_mul,
          add_zero]
  simp_rw [hsplit, Finset.sum_add_distrib, Fintype.sum_ite_eq']


-- @@ L5385-5394 verbatim
/-- The polynomial retraction retaining the selected even coordinates as variables and sending
the other coordinates to zero. -/
def nullRetraction {r m n : ℕ} (hn : 2 * m ≤ n) :
    MvPolynomial (Fin ((r + 1) * n)) ℂ →ₐ[ℂ]
      MvPolynomial (Fin (r + 1) × Fin m) ℂ :=
  MvPolynomial.aeval fun z =>
    let ik := (finProdFinEquiv (m := r + 1) (n := n)).symm z
    ∑ a : Fin m,
      if ik.2 = nullEvenCoordinate hn a then
        MvPolynomial.X (ik.1, a) else 0


-- @@ L5396-5412 verbatim
@[simp] theorem nullRetraction_X_variableIndex {r m n : ℕ}
    (hn : 2 * m ≤ n) (i : Fin (r + 1)) (k : Fin n) :
    nullRetraction hn (MvPolynomial.X (variableIndex i k)) =
      ∑ a : Fin m,
        if k = nullEvenCoordinate hn a then
          MvPolynomial.X (i, a) else 0 := by
  simp only [nullRetraction, MvPolynomial.aeval_X]
  change
    (∑ a : Fin m,
      if ((finProdFinEquiv (m := r + 1) (n := n)).symm
          ((finProdFinEquiv (m := r + 1) (n := n)) (i, k))).2 =
          nullEvenCoordinate hn a then
        MvPolynomial.X (R := ℂ)
          (((finProdFinEquiv (m := r + 1) (n := n)).symm
            ((finProdFinEquiv (m := r + 1) (n := n)) (i, k))).1, a)
      else 0) = _
  simp only [Equiv.symm_apply_apply]


-- @@ L5414-5420 verbatim
theorem nullRetraction_X_even {r m n : ℕ}
    (hn : 2 * m ≤ n) (i : Fin (r + 1)) (a : Fin m) :
    nullRetraction hn
        (MvPolynomial.X (variableIndex i (nullEvenCoordinate hn a))) =
      MvPolynomial.X (i, a) := by
  rw [nullRetraction_X_variableIndex]
  simp only [nullEvenCoordinate_inj, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]


-- @@ L5422-5429 verbatim
theorem nullRetraction_X_odd {r m n : ℕ}
    (hn : 2 * m ≤ n) (i : Fin (r + 1)) (a : Fin m) :
    nullRetraction hn
        (MvPolynomial.X (variableIndex i (nullOddCoordinate hn a))) = 0 := by
  rw [nullRetraction_X_variableIndex]
  apply Finset.sum_eq_zero
  intro b _
  simp only [Ne.symm (nullEvenCoordinate_ne_nullOddCoordinate hn b a), ↓reduceIte]


-- @@ L5431-5447 verbatim
theorem nullRetraction_nullSubstitution {r m n : ℕ}
    (hn : 2 * m ≤ n)
    (q : MvPolynomial (Fin (r + 1) × Fin m) ℂ) :
    nullRetraction hn (nullSubstitution hn q) = q := by
  have hcomp :
      (nullRetraction hn).comp (nullSubstitution (r := r) hn) =
        AlgHom.id ℂ (MvPolynomial (Fin (r + 1) × Fin m) ℂ) := by
    apply MvPolynomial.algHom_ext
    intro z
    rcases z with ⟨i, a⟩
    change nullRetraction hn
      (nullSubstitution hn (MvPolynomial.X (i, a))) =
        MvPolynomial.X (i, a)
    rw [nullSubstitution_X, nullRowLinearForm_eq_even_add_I_odd,
      map_add, map_mul, nullRetraction_X_even, nullRetraction_X_odd]
    simp only [MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, mul_zero, add_zero]
  exact DFunLike.congr_fun hcomp q


-- @@ L5449-5452 verbatim
theorem nullSubstitution_injective {r m n : ℕ}
    (hn : 2 * m ≤ n) :
    Function.Injective (nullSubstitution (r := r) hn) :=
  Function.LeftInverse.injective (nullRetraction_nullSubstitution hn)


-- @@ L5454-5454 verbatim
namespace DeterminantVectors


-- @@ L5456-5459 verbatim
/-- The even coordinate used in the spherical-code argument. -/
def evenCoordinate {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (j : Fin (r + 1)) : Fin n :=
  ⟨2 * j.val, by have := j.isLt; omega⟩


-- @@ L5461-5464 verbatim
/-- The odd coordinate used in the spherical-code argument. -/
def oddCoordinate {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (j : Fin (r + 1)) : Fin n :=
  ⟨2 * j.val + 1, by have := j.isLt; omega⟩


-- @@ L5466-5468 verbatim
@[simp] theorem evenCoordinate_val {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (j : Fin (r + 1)) :
    (evenCoordinate h j).val = 2 * j.val := rfl


-- @@ L5470-5472 verbatim
@[simp] theorem oddCoordinate_val {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (j : Fin (r + 1)) :
    (oddCoordinate h j).val = 2 * j.val + 1 := rfl


-- @@ L5474-5484 verbatim
@[simp] theorem evenCoordinate_inj {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (i j : Fin (r + 1)) :
    evenCoordinate h i = evenCoordinate h j ↔ i = j := by
  constructor
  · intro heq
    apply Fin.ext
    have hv := congrArg Fin.val heq
    simp only [evenCoordinate_val] at hv
    omega
  · rintro rfl
    rfl


-- @@ L5486-5496 verbatim
@[simp] theorem oddCoordinate_inj {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (i j : Fin (r + 1)) :
    oddCoordinate h i = oddCoordinate h j ↔ i = j := by
  constructor
  · intro heq
    apply Fin.ext
    have hv := congrArg Fin.val heq
    simp only [oddCoordinate_val] at hv
    omega
  · rintro rfl
    rfl


-- @@ L5498-5504 verbatim
theorem evenCoordinate_ne_oddCoordinate {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (i j : Fin (r + 1)) :
    evenCoordinate h i ≠ oddCoordinate h j := by
  intro heq
  have hv := congrArg Fin.val heq
  simp only [evenCoordinate_val, oddCoordinate_val] at hv
  omega


-- @@ L5506-5514 verbatim
@[simp] theorem variableIndex_eq_iff {r n : ℕ}
    (i j : Fin (r + 1)) (a b : Fin n) :
    variableIndex i a = variableIndex j b ↔ i = j ∧ a = b := by
  constructor
  · intro heq
    have hpair : (i, a) = (j, b) := variableIndex_injective heq
    exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩
  · rintro ⟨rfl, rfl⟩
    rfl


-- @@ L5516-5521 verbatim
/-- The isotropic variable used in the spherical-code argument. -/
def isotropicVariable {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (i j : Fin (r + 1)) : MvPolynomial (Fin ((r + 1) * n)) ℂ :=
  MvPolynomial.X (variableIndex i (evenCoordinate h j)) +
    MvPolynomial.C Complex.I *
      MvPolynomial.X (variableIndex i (oddCoordinate h j))


-- @@ L5523-5527 verbatim
theorem isotropicVariable_isHomogeneous {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (i j : Fin (r + 1)) :
    (isotropicVariable h i j).IsHomogeneous 1 := by
  exact (MvPolynomial.isHomogeneous_X _ _).add
    ((MvPolynomial.isHomogeneous_X _ _).C_mul _)


-- @@ L5529-5538 verbatim
/-- The row derivation used in the spherical-code argument. -/
def rowDerivation {r n : ℕ} (i j : Fin (r + 1)) :
    Derivation ℂ (MvPolynomial (Fin ((r + 1) * n)) ℂ)
      (MvPolynomial (Fin ((r + 1) * n)) ℂ) :=
  ∑ a : Fin n,
    (MvPolynomial.X (variableIndex i a) :
      MvPolynomial (Fin ((r + 1) * n)) ℂ) •
      (MvPolynomial.pderiv (variableIndex j a) :
        Derivation ℂ (MvPolynomial (Fin ((r + 1) * n)) ℂ)
          (MvPolynomial (Fin ((r + 1) * n)) ℂ))


-- @@ L5540-5555 verbatim
@[simp] theorem rowDerivation_apply {r n : ℕ}
    (i j : Fin (r + 1))
    (p : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    rowDerivation i j p =
      ∑ a : Fin n, MvPolynomial.X (variableIndex i a) *
        MvPolynomial.pderiv (variableIndex j a) p := by
  change
    (Derivation.coeFnAddMonoidHom
      (∑ a : Fin n,
        (MvPolynomial.X (variableIndex i a) :
          MvPolynomial (Fin ((r + 1) * n)) ℂ) •
          (MvPolynomial.pderiv (variableIndex j a) :
            Derivation ℂ (MvPolynomial (Fin ((r + 1) * n)) ℂ)
              (MvPolynomial (Fin ((r + 1) * n)) ℂ)))) p = _
  rw [map_sum, Finset.sum_apply]
  rfl


-- @@ L5557-5577 verbatim
theorem rowDerivation_isotropicVariable {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (i j a b : Fin (r + 1)) :
    rowDerivation i j (isotropicVariable h a b) =
      if j = a then isotropicVariable h i b else 0 := by
  classical
  rw [rowDerivation_apply]
  simp only [isotropicVariable, map_add, MvPolynomial.pderiv_C_mul,
    MvPolynomial.pderiv_X]
  by_cases hja : j = a
  · subst a
    simp only [Pi.single_apply, variableIndex_eq_iff, true_and,
      mul_add, Finset.sum_add_distrib]
    simp only [mul_ite, mul_comm, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      ite_mul]
  · have hne (c : Fin n) (d : Fin n) :
        variableIndex a d ≠ variableIndex j c := by
      intro heq
      exact hja ((variableIndex_eq_iff a j d c).mp heq).1.symm
    simp only [ne_eq, hne, not_false_eq_true, Pi.single_eq_of_ne, mul_zero, add_zero,
      Finset.sum_const_zero, hja, ↓reduceIte]


-- @@ L5579-5591 verbatim
theorem derivation_prod_eq_zero {σ α : Type*}
    (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (s : Finset α) (f : α → MvPolynomial σ ℂ)
    (h : ∀ a ∈ s, D (f a) = 0) :
    D (∏ a ∈ s, f a) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Derivation.map_one_eq_zero]
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, D.leibniz,
        h a (Finset.mem_insert_self a s),
        ih (fun b hb => h b (Finset.mem_insert_of_mem hb))]
      simp only [smul_eq_mul, mul_zero, add_zero]


-- @@ L5593-5616 verbatim
theorem derivation_prod_update {σ α : Type*} [DecidableEq α]
    (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (s : Finset α) (f : α → MvPolynomial σ ℂ)
    (a : α) (ha : a ∈ s)
    (h : ∀ b ∈ s, b ≠ a → D (f b) = 0) :
    D (∏ b ∈ s, f b) =
      ∏ b ∈ s, if b = a then D (f a) else f b := by
  classical
  have herase :
      D (∏ b ∈ s.erase a, f b) = 0 := by
    apply derivation_prod_eq_zero
    intro b hb
    exact h b (Finset.mem_of_mem_erase hb)
      (Finset.ne_of_mem_erase hb)
  rw [← Finset.mul_prod_erase s f ha, D.leibniz, herase]
  simp only [smul_eq_mul, mul_zero, zero_add]
  rw [← Finset.mul_prod_erase s
    (fun b => if b = a then D (f a) else f b) ha]
  simp only [ite_true]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro b hb
  simp only [Finset.ne_of_mem_erase hb, ↓reduceIte]


-- @@ L5618-5648 verbatim
theorem derivation_det_singleRow {σ ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (A : Matrix ι ι (MvPolynomial σ ℂ)) (a : ι)
    (h : ∀ b c, b ≠ a → D (A b c) = 0) :
    D A.det = (A.updateRow a (fun c => D (A a c))).det := by
  classical
  rw [Matrix.det_apply', Matrix.det_apply', map_sum]
  apply Finset.sum_congr rfl
  intro π _
  rw [D.leibniz, D.map_intCast]
  simp only [smul_eq_mul, mul_zero, add_zero]
  congr 1
  rw [derivation_prod_update D Finset.univ
    (fun c => A (π c) c) (π.symm a) (Finset.mem_univ _)]
  · apply Finset.prod_congr rfl
    intro c _
    by_cases hc : π c = a
    · have hc' : c = π.symm a := by
        simpa only [Equiv.symm_apply_apply] using congrArg π.symm hc
      simp only [hc', ↓reduceIte, Equiv.apply_symm_apply, Matrix.updateRow_apply]
    · have hc' : c ≠ π.symm a := by
        intro hc'
        apply hc
        simp only [hc', Equiv.apply_symm_apply]
      simp only [hc', ↓reduceIte, Matrix.updateRow_apply, hc]
  · intro b _ hb
    apply h
    intro heq
    apply hb
    simpa only [Equiv.symm_apply_apply] using congrArg π.symm heq


-- @@ L5650-5662 verbatim
theorem derivation_det_eq_zero {σ ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (A : Matrix ι ι (MvPolynomial σ ℂ))
    (h : ∀ a b, D (A a b) = 0) : D A.det = 0 := by
  classical
  rw [Matrix.det_apply', map_sum]
  apply Finset.sum_eq_zero
  intro π _
  rw [D.leibniz, D.map_intCast,
    derivation_prod_eq_zero D Finset.univ
      (fun c => A (π c) c) (fun c _ => h (π c) c)]
  simp only [smul_eq_mul, mul_zero, add_zero]


-- @@ L5664-5667 verbatim
/-- The minor index used in the spherical-code argument. -/
def minorIndex {r : ℕ} (k : Fin (r + 1))
    (i : Fin (k.val + 1)) : Fin (r + 1) :=
  ⟨i.val, by have := i.isLt; have := k.isLt; omega⟩


-- @@ L5669-5673 verbatim
/-- The determinant of the leading `(k + 1)`-square matrix of isotropic variables. -/
def leadingMinor {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (k : Fin (r + 1)) : MvPolynomial (Fin ((r + 1) * n)) ℂ :=
  Matrix.det (Matrix.of fun i j : Fin (k.val + 1) =>
    isotropicVariable h (minorIndex k i) (minorIndex k j))


-- @@ L5675-5694 verbatim
theorem leadingMinor_isHomogeneous {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (k : Fin (r + 1)) :
    (leadingMinor h k).IsHomogeneous (k.val + 1) := by
  classical
  unfold leadingMinor
  rw [Matrix.det_apply']
  simp only [Matrix.of_apply]
  apply MvPolynomial.IsHomogeneous.sum
  intro π _
  have hprod :
      (∏ i : Fin (k.val + 1),
        isotropicVariable h (minorIndex k (π i)) (minorIndex k i))
          |>.IsHomogeneous (k.val + 1) := by
    convert MvPolynomial.IsHomogeneous.prod Finset.univ
      (fun i : Fin (k.val + 1) =>
        isotropicVariable h (minorIndex k (π i)) (minorIndex k i))
      (fun _ => 1)
      (fun i _ => isotropicVariable_isHomogeneous h
        (minorIndex k (π i)) (minorIndex k i)) using 1; simp
  simpa only [map_intCast] using hprod.C_mul (((Equiv.Perm.sign π : ℤ) : ℂ))


-- @@ L5696-5750 verbatim
theorem rowDerivation_leadingMinor_upper {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (i j : Fin (r + 1)) (hij : i < j) (k : Fin (r + 1)) :
    rowDerivation i j (leadingMinor h k) = 0 := by
  classical
  unfold leadingMinor
  by_cases hj : j.val ≤ k.val
  · let jj : Fin (k.val + 1) := ⟨j.val, by omega⟩
    let ii : Fin (k.val + 1) := ⟨i.val, by
      have hijv : i.val < j.val := hij
      omega⟩
    have hjj : minorIndex k jj = j := Fin.ext rfl
    have hii : minorIndex k ii = i := Fin.ext rfl
    rw [derivation_det_singleRow
      (rowDerivation (n := n) i j)
      (Matrix.of fun a b : Fin (k.val + 1) =>
        isotropicVariable h (minorIndex k a) (minorIndex k b)) jj]
    · have hrow :
          (fun b : Fin (k.val + 1) =>
            rowDerivation i j
              (isotropicVariable h (minorIndex k jj) (minorIndex k b))) =
          (fun b : Fin (k.val + 1) =>
            isotropicVariable h (minorIndex k ii) (minorIndex k b)) := by
        funext b
        rw [rowDerivation_isotropicVariable, hjj, hii, ite_eq_left rfl]
      simp only [Matrix.of_apply]
      rw [hrow]
      apply Matrix.det_updateRow_eq_zero
      intro hbad
      have hvals := congrArg Fin.val hbad
      have hijv : i.val < j.val := hij
      change i.val = j.val at hvals
      omega
    · intro a b hab
      simp only [Matrix.of_apply]
      rw [rowDerivation_isotropicVariable]
      have hne : j ≠ minorIndex k a := by
        intro heq
        apply hab
        apply Fin.ext
        have hv := congrArg Fin.val heq
        change j.val = a.val at hv
        exact hv.symm
      simp only [hne, ↓reduceIte]
  · apply derivation_det_eq_zero
    intro a b
    simp only [Matrix.of_apply]
    rw [rowDerivation_isotropicVariable]
    have hne : j ≠ minorIndex k a := by
      intro heq
      have hv := congrArg Fin.val heq
      change j.val = a.val at hv
      have ha := a.isLt
      omega
    simp only [hne, ↓reduceIte]


-- @@ L5752-5806 verbatim
theorem rowDerivation_leadingMinor_self {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (i : Fin (r + 1)) (k : Fin (r + 1)) :
    rowDerivation i i (leadingMinor h k) =
      if i ≤ k then leadingMinor h k else 0 := by
  classical
  unfold leadingMinor
  by_cases hi : i.val ≤ k.val
  · let ii : Fin (k.val + 1) := ⟨i.val, by omega⟩
    have hii : minorIndex k ii = i := Fin.ext rfl
    rw [ite_eq_left (show i ≤ k from hi), derivation_det_singleRow
      (rowDerivation (n := n) i i)
      (Matrix.of fun a b : Fin (k.val + 1) =>
        isotropicVariable h (minorIndex k a) (minorIndex k b)) ii]
    · have hrow :
          (fun b : Fin (k.val + 1) =>
            rowDerivation i i
              (isotropicVariable h (minorIndex k ii) (minorIndex k b))) =
          (fun b : Fin (k.val + 1) =>
            isotropicVariable h (minorIndex k ii) (minorIndex k b)) := by
        funext b
        rw [rowDerivation_isotropicVariable, hii, ite_eq_left rfl]
      simp only [Matrix.of_apply]
      rw [hrow]
      have hrowMatrix :
          (fun b : Fin (k.val + 1) =>
            isotropicVariable h (minorIndex k ii) (minorIndex k b)) =
          (fun b => (Matrix.of fun a b : Fin (k.val + 1) =>
            isotropicVariable h (minorIndex k a) (minorIndex k b)) ii b) := by
        funext b
        simp only [Matrix.of_apply]
      rw [hrowMatrix, Matrix.updateRow_eq_self]
    · intro a b hab
      simp only [Matrix.of_apply]
      rw [rowDerivation_isotropicVariable]
      have hne : i ≠ minorIndex k a := by
        intro heq
        apply hab
        apply Fin.ext
        have hv := congrArg Fin.val heq
        change i.val = a.val at hv
        exact hv.symm
      simp only [hne, ↓reduceIte]
  · rw [ite_eq_right (show ¬ i ≤ k from hi)]
    apply derivation_det_eq_zero
    intro a b
    simp only [Matrix.of_apply]
    rw [rowDerivation_isotropicVariable]
    have hne : i ≠ minorIndex k a := by
      intro heq
      have hv := congrArg Fin.val heq
      change i.val = a.val at hv
      have ha := a.isLt
      omega
    simp only [hne, ↓reduceIte]


-- @@ L5808-5835 verbatim
theorem isotropicVariable_eq_nullRowLinearForm {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (i j : Fin (r + 1)) :
    isotropicVariable h i j = nullRowLinearForm h i j := by
  classical
  unfold nullRowLinearForm
  have heq : evenCoordinate h j = nullEvenCoordinate h j := rfl
  have hoq : oddCoordinate h j = nullOddCoordinate h j := rfl
  have hsplit (a : Fin n) :
      MvPolynomial.C (nullCoordinateCoefficient h j a) *
          MvPolynomial.X (variableIndex i a) =
        (if a = evenCoordinate h j then
          MvPolynomial.X (variableIndex i a) else 0) +
        (if a = oddCoordinate h j then
          MvPolynomial.C Complex.I *
            MvPolynomial.X (variableIndex i a) else 0) := by
    by_cases he : a = evenCoordinate h j
    · subst a
      have hne := evenCoordinate_ne_oddCoordinate h j j
      simp only [nullCoordinateCoefficient, ← heq, ↓reduceIte, MvPolynomial.C_1, one_mul, hne,
        add_zero]
    · by_cases ho : a = oddCoordinate h j
      · subst a
        have hne := evenCoordinate_ne_oddCoordinate h j j
        simp only [nullCoordinateCoefficient, ← heq, Ne.symm hne, ↓reduceIte, ← hoq, zero_add]
      · simp only [nullCoordinateCoefficient, ← heq, he, ↓reduceIte, ← hoq, ho, MvPolynomial.C_0,
          zero_mul, add_zero]
  simp_rw [hsplit, Finset.sum_add_distrib, Fintype.sum_ite_eq']
  rfl


-- @@ L5837-5841 verbatim
/-- The source leading minor used in the spherical-code argument. -/
def sourceLeadingMinor {r : ℕ} (k : Fin (r + 1)) :
    MvPolynomial (Fin (r + 1) × Fin (r + 1)) ℂ :=
  Matrix.det (Matrix.of fun i j : Fin (k.val + 1) =>
    MvPolynomial.X (minorIndex k i, minorIndex k j))


-- @@ L5843-5854 verbatim
theorem nullSubstitution_sourceLeadingMinor {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (k : Fin (r + 1)) :
    nullSubstitution h (sourceLeadingMinor k) = leadingMinor h k := by
  unfold sourceLeadingMinor leadingMinor
  rw [(nullSubstitution h).map_det]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  simpa only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply] using
    (nullSubstitution_X h (minorIndex k i) (minorIndex k j)).trans
      (isotropicVariable_eq_nullRowLinearForm h
        (minorIndex k i) (minorIndex k j)).symm


-- @@ L5856-5860 verbatim
/-- The diagonal evaluation used in the spherical-code argument. -/
def diagonalEvaluation {r n : ℕ} : Fin ((r + 1) * n) → ℂ :=
  fun a =>
    let z := (finProdFinEquiv (m := r + 1) (n := n)).symm a
    if z.2.val = 2 * z.1.val then 1 else 0


-- @@ L5862-5866 verbatim
@[simp] theorem diagonalEvaluation_variableIndex {r n : ℕ}
    (i : Fin (r + 1)) (j : Fin n) :
    diagonalEvaluation (variableIndex i j) =
      if j.val = 2 * i.val then 1 else 0 := by
  simp only [diagonalEvaluation, variableIndex, Equiv.symm_apply_apply]


-- @@ L5868-5881 verbatim
theorem eval_isotropicVariable {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (i j : Fin (r + 1)) :
    MvPolynomial.eval diagonalEvaluation (isotropicVariable h i j) =
      if i = j then 1 else 0 := by
  simp only [isotropicVariable, map_add, map_mul, MvPolynomial.eval_X,
    MvPolynomial.eval_C, diagonalEvaluation_variableIndex,
    evenCoordinate_val, oddCoordinate_val]
  by_cases hij : i = j
  · subst j
    simp only [↓reduceIte, Nat.add_eq_left, one_ne_zero, mul_zero, add_zero]
  · have hv : i.val ≠ j.val := fun heq => hij (Fin.ext heq)
    have heven : 2 * j.val ≠ 2 * i.val := by omega
    have hodd : 2 * j.val + 1 ≠ 2 * i.val := by omega
    simp only [heven, ↓reduceIte, hodd, mul_zero, add_zero, hij]


-- @@ L5883-5901 verbatim
theorem eval_leadingMinor {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (k : Fin (r + 1)) :
    MvPolynomial.eval diagonalEvaluation (leadingMinor h k) = 1 := by
  unfold leadingMinor
  rw [(MvPolynomial.eval diagonalEvaluation).map_det]
  have hmatrix :
      (Matrix.of fun i j : Fin (k.val + 1) =>
        MvPolynomial.eval diagonalEvaluation
          (isotropicVariable h (minorIndex k i) (minorIndex k j))) =
        (1 : Matrix (Fin (k.val + 1)) (Fin (k.val + 1)) ℂ) := by
    ext i j
    simp only [Matrix.of_apply]
    rw [eval_isotropicVariable]
    simp only [minorIndex, Fin.ext_iff, Matrix.one_apply]
  change
    Matrix.det (Matrix.of fun i j : Fin (k.val + 1) =>
      MvPolynomial.eval diagonalEvaluation
        (isotropicVariable h (minorIndex k i) (minorIndex k j))) = 1
  rw [hmatrix, Matrix.det_one]


-- @@ L5903-5906 verbatim
/-- The highest weight polynomial used in the spherical-code argument. -/
def highestWeightPolynomial {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (e : Fin (r + 1) → ℕ) : MvPolynomial (Fin ((r + 1) * n)) ℂ :=
  ∏ k : Fin (r + 1), leadingMinor h k ^ e k


-- @@ L5908-5912 verbatim
/-- The source highest weight polynomial used in the spherical-code argument. -/
def sourceHighestWeightPolynomial {r : ℕ}
    (e : Fin (r + 1) → ℕ) :
    MvPolynomial (Fin (r + 1) × Fin (r + 1)) ℂ :=
  ∏ k : Fin (r + 1), sourceLeadingMinor k ^ e k


-- @@ L5914-5919 verbatim
theorem nullSubstitution_sourceHighestWeightPolynomial {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (e : Fin (r + 1) → ℕ) :
    nullSubstitution h (sourceHighestWeightPolynomial e) =
      highestWeightPolynomial h e := by
  simp only [sourceHighestWeightPolynomial, map_prod, map_pow, nullSubstitution_sourceLeadingMinor,
    highestWeightPolynomial]


-- @@ L5921-5927 verbatim
theorem complexTraceOperator_highestWeightPolynomial {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (e : Fin (r + 1) → ℕ)
    (i j : Fin (r + 1)) :
    complexTraceOperator i j (highestWeightPolynomial h e) = 0 := by
  rw [← nullSubstitution_sourceHighestWeightPolynomial]
  exact complexTraceOperator_nullSubstitution h i j
    (sourceHighestWeightPolynomial e)


-- @@ L5929-5939 verbatim
theorem rowDerivation_highestWeightPolynomial_upper {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (e : Fin (r + 1) → ℕ)
    (i j : Fin (r + 1)) (hij : i < j) :
    rowDerivation i j (highestWeightPolynomial h e) = 0 := by
  classical
  unfold highestWeightPolynomial
  apply derivation_prod_eq_zero
  intro k _
  rw [(rowDerivation i j).leibniz_pow,
    rowDerivation_leadingMinor_upper h i j hij k]
  simp only [smul_eq_mul, mul_zero, nsmul_zero]


-- @@ L5941-5948 verbatim
theorem highestWeightPolynomial_isHomogeneous_minorDegrees {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (e : Fin (r + 1) → ℕ) :
    (highestWeightPolynomial h e).IsHomogeneous
      (∑ k : Fin (r + 1), (k.val + 1) * e k) := by
  unfold highestWeightPolynomial
  apply MvPolynomial.IsHomogeneous.prod
  intro k _
  exact (leadingMinor_isHomogeneous h k).pow (e k)


-- @@ L5950-5964 verbatim
theorem derivation_prod_eigen {σ α : Type*}
    (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (s : Finset α) (f : α → MvPolynomial σ ℂ) (c : α → ℕ)
    (h : ∀ a ∈ s, D (f a) = (c a : ℂ) • f a) :
    D (∏ a ∈ s, f a) = (∑ a ∈ s, c a : ℂ) • ∏ a ∈ s, f a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Derivation.map_one_eq_zero, Finset.sum_empty, zero_smul]
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        D.leibniz, h a (Finset.mem_insert_self a s),
        ih (fun b hb => h b (Finset.mem_insert_of_mem hb))]
      simp only [Algebra.smul_def, map_add,
        Algebra.algebraMap_self_apply]
      ring


-- @@ L5966-5971 verbatim
theorem eval_highestWeightPolynomial {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (e : Fin (r + 1) → ℕ) :
    MvPolynomial.eval diagonalEvaluation
      (highestWeightPolynomial h e) = 1 := by
  simp only [highestWeightPolynomial, map_prod, map_pow, eval_leadingMinor, one_pow,
    Finset.prod_const_one]


-- @@ L5973-5978 verbatim
theorem highestWeightPolynomial_ne_zero {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (e : Fin (r + 1) → ℕ) :
    highestWeightPolynomial h e ≠ 0 := by
  intro hz
  have := eval_highestWeightPolynomial h e
  simp only [hz, map_zero, zero_ne_one] at this


-- @@ L5980-5983 verbatim
/-- The determinant weight used in the spherical-code argument. -/
def determinantWeight {r : ℕ} (e : Fin (r + 1) → ℕ)
    (i : Fin (r + 1)) : ℕ :=
  ∑ k : Fin (r + 1), if i ≤ k then e k else 0


-- @@ L5985-6001 verbatim
theorem sum_determinantWeight {r : ℕ}
    (e : Fin (r + 1) → ℕ) :
    (∑ i : Fin (r + 1), determinantWeight e i) =
      ∑ k : Fin (r + 1), (k.val + 1) * e k := by
  classical
  unfold determinantWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.sum_filter]
  have hfilter :
      (Finset.univ.filter (fun i : Fin (r + 1) => i ≤ k)) =
        Finset.Iic k := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic]
  rw [hfilter, Finset.sum_const, Fin.card_Iic]
  simp only [smul_eq_mul]


-- @@ L6003-6008 verbatim
theorem highestWeightPolynomial_isHomogeneous {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (e : Fin (r + 1) → ℕ) :
    (highestWeightPolynomial h e).IsHomogeneous
      (∑ i : Fin (r + 1), determinantWeight e i) := by
  rw [sum_determinantWeight]
  exact highestWeightPolynomial_isHomogeneous_minorDegrees h e


-- @@ L6010-6033 verbatim
theorem rowDerivation_highestWeightPolynomial_self {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (e : Fin (r + 1) → ℕ)
    (i : Fin (r + 1)) :
    rowDerivation i i (highestWeightPolynomial h e) =
      (determinantWeight e i : ℂ) • highestWeightPolynomial h e := by
  classical
  unfold highestWeightPolynomial determinantWeight
  rw [Nat.cast_sum]
  apply derivation_prod_eigen (rowDerivation i i) Finset.univ
    (fun k : Fin (r + 1) => leadingMinor h k ^ e k)
    (fun k => if i ≤ k then e k else 0)
  intro k _
  rw [(rowDerivation i i).leibniz_pow,
    rowDerivation_leadingMinor_self]
  by_cases hik : i ≤ k
  · simp only [hik, ite_true]
    cases he : e k with
    | zero => simp only [zero_tsub, pow_zero, smul_eq_mul, one_mul, CharP.cast_eq_zero,
                zero_smul]
    | succ m =>
        simp only [add_tsub_cancel_right, smul_eq_mul, Algebra.smul_def, eq_natCast, Nat.cast_add,
          Nat.cast_one, pow_succ, MvPolynomial.algebraMap_eq, MvPolynomial.C_add, map_natCast,
          MvPolynomial.C_1]
  · simp only [hik, ↓reduceIte, smul_eq_mul, mul_zero, nsmul_zero, CharP.cast_eq_zero, zero_smul]


-- @@ L6035-6040 verbatim
theorem complexPolarization_eq_rowDerivation {r n : ℕ}
    (i j : Fin (r + 1))
    (p : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    complexPolarization i j p = rowDerivation i j p := by
  rw [rowDerivation_apply]
  rfl


-- @@ L6042-6047 verbatim
theorem complexRowEuler_eq_rowDerivation {r n : ℕ}
    (i : Fin (r + 1))
    (p : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    complexRowEuler i p = rowDerivation i i p := by
  rw [rowDerivation_apply]
  rfl


-- @@ L6049-6053 verbatim
/-- The signature exponent used in the spherical-code argument. -/
def signatureExponent {r : ℕ}
    (lam : Fin (r + 1) → ℕ) : Fin (r + 1) → ℕ :=
  Fin.lastCases (lam (Fin.last r))
    (fun i : Fin r => lam i.castSucc - lam i.succ)


-- @@ L6055-6058 verbatim
@[simp] theorem signatureExponent_last {r : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    signatureExponent lam (Fin.last r) = lam (Fin.last r) := by
  simp only [signatureExponent, Fin.lastCases_last]


-- @@ L6060-6064 verbatim
@[simp] theorem signatureExponent_castSucc {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (i : Fin r) :
    signatureExponent lam i.castSucc =
      lam i.castSucc - lam i.succ := by
  simp only [signatureExponent, Fin.lastCases_castSucc]


-- @@ L6066-6070 verbatim
@[simp] theorem determinantWeight_last {r : ℕ}
    (e : Fin (r + 1) → ℕ) :
    determinantWeight e (Fin.last r) = e (Fin.last r) := by
  classical
  simp only [determinantWeight, Fin.last_le_iff, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]


-- @@ L6072-6100 verbatim
theorem determinantWeight_castSucc {r : ℕ}
    (e : Fin (r + 1) → ℕ) (i : Fin r) :
    determinantWeight e i.castSucc =
      e i.castSucc + determinantWeight e i.succ := by
  classical
  unfold determinantWeight
  have hsplit (k : Fin (r + 1)) :
      (if i.castSucc ≤ k then e k else 0) =
        (if k = i.castSucc then e k else 0) +
          (if i.succ ≤ k then e k else 0) := by
    by_cases hk : k = i.castSucc
    · subst k
      have hnot : ¬ i.succ ≤ i.castSucc :=
        not_le_of_gt Fin.castSucc_lt_succ
      simp only [Std.le_refl, ↓reduceIte, hnot, add_zero]
    · have hvals : k.val ≠ i.val := by
        intro heq
        apply hk
        apply Fin.ext
        exact heq
      have hiff : i.castSucc ≤ k ↔ i.succ ≤ k := by
        change i.val ≤ k.val ↔ i.val + 1 ≤ k.val
        omega
      by_cases hs : i.succ ≤ k
      · have hc : i.castSucc ≤ k := hiff.mpr hs
        simp only [hc, ↓reduceIte, hk, hs, zero_add]
      · have hc : ¬ i.castSucc ≤ k := fun hc => hs (hiff.mp hc)
        simp only [hc, ↓reduceIte, hk, hs, add_zero]
  simp_rw [hsplit, Finset.sum_add_distrib, Fintype.sum_ite_eq']


-- @@ L6102-6112 verbatim
theorem determinantWeight_signatureExponent {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam) :
    determinantWeight (signatureExponent lam) = lam := by
  funext i
  induction i using Fin.reverseInduction with
  | last => simp only [determinantWeight_last, signatureExponent_last]
  | cast i ih =>
      rw [determinantWeight_castSucc,
        signatureExponent_castSucc, ih]
      apply Nat.sub_add_cancel
      exact hdom (Fin.castSucc_lt_succ.le)


-- @@ L6114-6136 verbatim
/-- The dominant highest weight witness used in the spherical-code argument. -/
def dominantHighestWeightWitness {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam) :
    ComplexHighestWeightWitness (n := n) lam where
  polynomial := highestWeightPolynomial h (signatureExponent lam)
  nonzero := highestWeightPolynomial_ne_zero h (signatureExponent lam)
  homogeneous := by
    simpa only [determinantWeight_signatureExponent lam hdom] using
      highestWeightPolynomial_isHomogeneous h (signatureExponent lam)
  rowEuler i := by
    rw [complexRowEuler_eq_rowDerivation,
      rowDerivation_highestWeightPolynomial_self]
    have heq := congrFun
      (determinantWeight_signatureExponent lam hdom) i
    rw [heq]
    simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq, map_natCast]
  traceFree i j :=
    complexTraceOperator_highestWeightPolynomial h (signatureExponent lam) i j
  highestWeight i j hij := by
    rw [complexPolarization_eq_rowDerivation]
    exact rowDerivation_highestWeightPolynomial_upper h
      (signatureExponent lam) i j hij


-- @@ L6138-6143 verbatim
theorem exists_nonzero_harmonicYoung_of_antitone {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam) :
    ∃ p : HarmonicYoungSpace (n := n) lam, p ≠ 0 :=
  exists_nonzero_harmonicYoung_of_complexWitness
    (dominantHighestWeightWitness h lam hdom)


-- @@ L6145-6150 verbatim
theorem finrank_harmonicYoung_pos_of_antitone {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam) :
    0 < Module.finrank ℝ (HarmonicYoungSpace (n := n) lam) :=
  finrank_harmonicYoung_pos_of_complexWitness
    (dominantHighestWeightWitness h lam hdom)


-- @@ L6152-6158 verbatim
/-- The conjugate isotropic variable used in the spherical-code argument. -/
def conjugateIsotropicVariable {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (i j : Fin (r + 1)) :
    MvPolynomial (Fin ((r + 1) * n)) ℂ :=
  MvPolynomial.X (variableIndex i (evenCoordinate h j)) -
    MvPolynomial.C Complex.I *
      MvPolynomial.X (variableIndex i (oddCoordinate h j))


-- @@ L6160-6168 verbatim
theorem pderiv_even_isotropicVariable {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (a p i j : Fin (r + 1)) :
    MvPolynomial.pderiv (variableIndex a (evenCoordinate h p))
        (isotropicVariable h i j) =
      if a = i ∧ p = j then 1 else 0 := by
  classical
  simp [isotropicVariable, Pi.single_apply, variableIndex_eq_iff, evenCoordinate_inj,
    evenCoordinate_ne_oddCoordinate, eq_comm]


-- @@ L6170-6180 verbatim
theorem pderiv_odd_isotropicVariable {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (a p i j : Fin (r + 1)) :
    MvPolynomial.pderiv (variableIndex a (oddCoordinate h p))
        (isotropicVariable h i j) =
      if a = i ∧ p = j then MvPolynomial.C Complex.I else 0 := by
  classical
  simp only [isotropicVariable, map_add, MvPolynomial.pderiv_X, ne_eq, variableIndex_eq_iff,
    eq_comm, evenCoordinate_ne_oddCoordinate, and_false, not_false_eq_true, Pi.single_eq_of_ne,
    Derivation.leibniz, Pi.single_apply, oddCoordinate_inj, smul_eq_mul, mul_ite, mul_one, mul_zero,
    MvPolynomial.derivation_C, add_zero, zero_add]


-- @@ L6182-6201 verbatim
/-- The ambient positive root used in the spherical-code argument. -/
def ambientPositiveRoot {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (p q : Fin (r + 1)) :
    Derivation ℂ (MvPolynomial (Fin ((r + 1) * n)) ℂ)
      (MvPolynomial (Fin ((r + 1) * n)) ℂ) :=
  ∑ a : Fin (r + 1), (
    isotropicVariable h a p •
      ((MvPolynomial.pderiv (variableIndex a (evenCoordinate h q)) :
        Derivation ℂ (MvPolynomial (Fin ((r + 1) * n)) ℂ)
          (MvPolynomial (Fin ((r + 1) * n)) ℂ)) -
        (MvPolynomial.C Complex.I :
          MvPolynomial (Fin ((r + 1) * n)) ℂ) •
          MvPolynomial.pderiv (variableIndex a (oddCoordinate h q))) -
    conjugateIsotropicVariable h a q •
      ((MvPolynomial.pderiv (variableIndex a (evenCoordinate h p)) :
        Derivation ℂ (MvPolynomial (Fin ((r + 1) * n)) ℂ)
          (MvPolynomial (Fin ((r + 1) * n)) ℂ)) +
        (MvPolynomial.C Complex.I :
          MvPolynomial (Fin ((r + 1) * n)) ℂ) •
          MvPolynomial.pderiv (variableIndex a (oddCoordinate h p))))


-- @@ L6203-6236 verbatim
theorem ambientPositiveRoot_apply {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (p q : Fin (r + 1))
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    ambientPositiveRoot h p q f =
      ∑ a : Fin (r + 1),
        (isotropicVariable h a p *
          (MvPolynomial.pderiv (variableIndex a (evenCoordinate h q)) f -
            MvPolynomial.C Complex.I *
              MvPolynomial.pderiv (variableIndex a (oddCoordinate h q)) f) -
          conjugateIsotropicVariable h a q *
          (MvPolynomial.pderiv (variableIndex a (evenCoordinate h p)) f +
            MvPolynomial.C Complex.I *
              MvPolynomial.pderiv (variableIndex a (oddCoordinate h p)) f)) := by
  classical
  change
    (Derivation.coeFnAddMonoidHom
      (∑ a : Fin (r + 1), (
        isotropicVariable h a p •
          ((MvPolynomial.pderiv (variableIndex a (evenCoordinate h q)) :
            Derivation ℂ (MvPolynomial (Fin ((r + 1) * n)) ℂ)
              (MvPolynomial (Fin ((r + 1) * n)) ℂ)) -
            (MvPolynomial.C Complex.I :
              MvPolynomial (Fin ((r + 1) * n)) ℂ) •
              MvPolynomial.pderiv (variableIndex a (oddCoordinate h q))) -
        conjugateIsotropicVariable h a q •
          ((MvPolynomial.pderiv (variableIndex a (evenCoordinate h p)) :
            Derivation ℂ (MvPolynomial (Fin ((r + 1) * n)) ℂ)
              (MvPolynomial (Fin ((r + 1) * n)) ℂ)) +
            (MvPolynomial.C Complex.I :
              MvPolynomial (Fin ((r + 1) * n)) ℂ) •
              MvPolynomial.pderiv (variableIndex a (oddCoordinate h p))))))
        f = _
  rw [map_sum, Finset.sum_apply]
  rfl


-- @@ L6238-6286 verbatim
theorem ambientPositiveRoot_isotropicVariable {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (p q i j : Fin (r + 1)) :
    ambientPositiveRoot h p q (isotropicVariable h i j) =
      if q = j then (2 : ℂ) • isotropicVariable h i p else 0 := by
  classical
  rw [ambientPositiveRoot_apply]
  have hterm (a : Fin (r + 1)) :
      (isotropicVariable h a p *
          (MvPolynomial.pderiv (variableIndex a (evenCoordinate h q))
              (isotropicVariable h i j) -
            MvPolynomial.C Complex.I *
              MvPolynomial.pderiv (variableIndex a (oddCoordinate h q))
                (isotropicVariable h i j)) -
        conjugateIsotropicVariable h a q *
          (MvPolynomial.pderiv (variableIndex a (evenCoordinate h p))
              (isotropicVariable h i j) +
            MvPolynomial.C Complex.I *
              MvPolynomial.pderiv (variableIndex a (oddCoordinate h p))
                (isotropicVariable h i j))) =
        if a = i ∧ q = j then
          (2 : ℂ) • isotropicVariable h i p else 0 := by
    simp_rw [pderiv_even_isotropicVariable,
      pderiv_odd_isotropicVariable]
    by_cases ha : a = i
    · subst a
      by_cases hq : q = j
      · subst q
        by_cases hp : p = j
        · subst p
          simp only [and_self, ↓reduceIte, ← map_mul, Complex.I_mul_I, MvPolynomial.C_neg,
            MvPolynomial.C_1, sub_neg_eq_add, add_neg_cancel, mul_zero, sub_zero, Algebra.smul_def,
            MvPolynomial.algebraMap_eq]
          rw [map_ofNat (MvPolynomial.C :
            ℂ →+* MvPolynomial (Fin ((r + 1) * n)) ℂ) 2]
          ring
        · simp only [and_self, ↓reduceIte, ← map_mul, Complex.I_mul_I, MvPolynomial.C_neg,
            MvPolynomial.C_1, sub_neg_eq_add, hp, and_false, mul_zero, add_zero, sub_zero,
            Algebra.smul_def, MvPolynomial.algebraMap_eq]
          rw [map_ofNat (MvPolynomial.C :
            ℂ →+* MvPolynomial (Fin ((r + 1) * n)) ℂ) 2]
          ring
      · by_cases hp : p = j
        · subst p
          simp only [hq, and_false, ↓reduceIte, mul_zero, sub_self, and_self, ← map_mul,
            Complex.I_mul_I, MvPolynomial.C_neg, MvPolynomial.C_1, add_neg_cancel]
        · simp only [hq, and_false, ↓reduceIte, mul_zero, sub_self, hp, add_zero]
    · simp only [ha, false_and, ↓reduceIte, mul_zero, sub_self, add_zero]
  simp_rw [hterm]
  by_cases hq : q = j <;> simp [hq]


-- @@ L6288-6299 verbatim
theorem derivation_det_singleColumn {σ ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (A : Matrix ι ι (MvPolynomial σ ℂ)) (a : ι)
    (h : ∀ b c, c ≠ a → D (A b c) = 0) :
    D A.det = (A.updateCol a (fun b => D (A b a))).det := by
  rw [← Matrix.det_transpose A]
  rw [derivation_det_singleRow D A.transpose a]
  · rw [Matrix.updateRow_transpose, Matrix.det_transpose]
    congr 1
  · intro b c hb
    exact h c b hb


-- @@ L6301-6367 verbatim
theorem ambientPositiveRoot_leadingMinor {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (p q : Fin (r + 1)) (hpq : p < q) (k : Fin (r + 1)) :
    ambientPositiveRoot h p q (leadingMinor h k) = 0 := by
  classical
  unfold leadingMinor
  by_cases hq : q.val ≤ k.val
  · let qq : Fin (k.val + 1) := ⟨q.val, by omega⟩
    let pp : Fin (k.val + 1) := ⟨p.val, by
      have hpqv : p.val < q.val := hpq
      omega⟩
    have hqq : minorIndex k qq = q := Fin.ext rfl
    have hpp : minorIndex k pp = p := Fin.ext rfl
    rw [derivation_det_singleColumn
      (ambientPositiveRoot h p q)
      (Matrix.of fun a b : Fin (k.val + 1) =>
        isotropicVariable h (minorIndex k a) (minorIndex k b)) qq]
    · have hcol :
          (fun a : Fin (k.val + 1) =>
            ambientPositiveRoot h p q
              (isotropicVariable h (minorIndex k a) (minorIndex k qq))) =
          (MvPolynomial.C (2 : ℂ) :
            MvPolynomial (Fin ((r + 1) * n)) ℂ) •
              (fun a : Fin (k.val + 1) =>
                isotropicVariable h (minorIndex k a) (minorIndex k pp)) := by
        funext a
        rw [ambientPositiveRoot_isotropicVariable, hqq,
          ite_eq_left rfl, hpp]
        simp [Pi.smul_apply, Algebra.smul_def, smul_eq_mul]
      simp only [Matrix.of_apply]
      rw [hcol, Matrix.det_updateCol_smul]
      have hcolumn :
          (fun a : Fin (k.val + 1) =>
            isotropicVariable h (minorIndex k a) (minorIndex k pp)) =
          (fun a => (Matrix.of fun a b : Fin (k.val + 1) =>
            isotropicVariable h (minorIndex k a) (minorIndex k b)) a pp) := by
        funext a
        simp only [Matrix.of_apply]
      rw [hcolumn, Matrix.det_updateCol_eq_zero]
      · simp only [mul_zero]
      · intro hbad
        have hvals := congrArg Fin.val hbad
        have hpqv : p.val < q.val := hpq
        change p.val = q.val at hvals
        omega
    · intro a b hb
      simp only [Matrix.of_apply]
      rw [ambientPositiveRoot_isotropicVariable]
      have hne : q ≠ minorIndex k b := by
        intro heq
        apply hb
        apply Fin.ext
        have hv := congrArg Fin.val heq
        change q.val = b.val at hv
        exact hv.symm
      simp only [hne, ↓reduceIte]
  · apply derivation_det_eq_zero
    intro a b
    simp only [Matrix.of_apply]
    rw [ambientPositiveRoot_isotropicVariable]
    have hne : q ≠ minorIndex k b := by
      intro heq
      have hv := congrArg Fin.val heq
      change q.val = b.val at hv
      have hb := b.isLt
      omega
    simp only [hne, ↓reduceIte]


-- @@ L6369-6379 verbatim
theorem ambientPositiveRoot_highestWeightPolynomial {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (e : Fin (r + 1) → ℕ)
    (p q : Fin (r + 1)) (hpq : p < q) :
    ambientPositiveRoot h p q (highestWeightPolynomial h e) = 0 := by
  classical
  unfold highestWeightPolynomial
  apply derivation_prod_eq_zero
  intro k _
  rw [(ambientPositiveRoot h p q).leibniz_pow,
    ambientPositiveRoot_leadingMinor h p q hpq k]
  simp only [smul_eq_mul, mul_zero, nsmul_zero]


-- @@ L6381-6388 verbatim
theorem ambientPositiveRoot_dominantHighestWeightWitness {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (p q : Fin (r + 1)) (hpq : p < q) :
    ambientPositiveRoot h p q
        (dominantHighestWeightWitness h lam hdom).polynomial = 0 := by
  exact ambientPositiveRoot_highestWeightPolynomial h
    (signatureExponent lam) p q hpq


-- @@ L6390-6400 verbatim
/-- The antiholomorphic derivative used in the spherical-code argument. -/
def antiholomorphicDerivative {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (a p : Fin (r + 1)) :
    Derivation ℂ (MvPolynomial (Fin ((r + 1) * n)) ℂ)
      (MvPolynomial (Fin ((r + 1) * n)) ℂ) :=
  (MvPolynomial.pderiv (variableIndex a (evenCoordinate h p)) :
    Derivation ℂ (MvPolynomial (Fin ((r + 1) * n)) ℂ)
      (MvPolynomial (Fin ((r + 1) * n)) ℂ)) +
    (MvPolynomial.C Complex.I :
      MvPolynomial (Fin ((r + 1) * n)) ℂ) •
      MvPolynomial.pderiv (variableIndex a (oddCoordinate h p))


-- @@ L6402-6416 verbatim
theorem antiholomorphicDerivative_isotropicVariable {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (a p i j : Fin (r + 1)) :
    antiholomorphicDerivative h a p (isotropicVariable h i j) = 0 := by
  change
    MvPolynomial.pderiv (variableIndex a (evenCoordinate h p))
        (isotropicVariable h i j) +
      MvPolynomial.C Complex.I *
        MvPolynomial.pderiv (variableIndex a (oddCoordinate h p))
          (isotropicVariable h i j) = 0
  rw [pderiv_even_isotropicVariable,
    pderiv_odd_isotropicVariable]
  by_cases hij : a = i ∧ p = j
  · simp only [hij, and_self, ↓reduceIte, ← map_mul, Complex.I_mul_I, MvPolynomial.C_neg,
      MvPolynomial.C_1, add_neg_cancel]
  · simp only [hij, ↓reduceIte, mul_zero, add_zero]


-- @@ L6418-6425 verbatim
/-- The ambient sum positive root used in the spherical-code argument. -/
def ambientSumPositiveRoot {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (p q : Fin (r + 1)) :
    Derivation ℂ (MvPolynomial (Fin ((r + 1) * n)) ℂ)
      (MvPolynomial (Fin ((r + 1) * n)) ℂ) :=
  ∑ a : Fin (r + 1),
    (isotropicVariable h a p • antiholomorphicDerivative h a q -
      isotropicVariable h a q • antiholomorphicDerivative h a p)


-- @@ L6427-6445 verbatim
theorem ambientSumPositiveRoot_isotropicVariable {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (p q i j : Fin (r + 1)) :
    ambientSumPositiveRoot h p q (isotropicVariable h i j) = 0 := by
  classical
  change
    (Derivation.coeFnAddMonoidHom
      (∑ a : Fin (r + 1),
        (isotropicVariable h a p • antiholomorphicDerivative h a q -
          isotropicVariable h a q • antiholomorphicDerivative h a p)))
        (isotropicVariable h i j) = 0
  rw [map_sum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro a _
  change
    isotropicVariable h a p *
        antiholomorphicDerivative h a q (isotropicVariable h i j) -
      isotropicVariable h a q *
        antiholomorphicDerivative h a p (isotropicVariable h i j) = 0
  simp only [antiholomorphicDerivative_isotropicVariable, mul_zero, sub_self]


-- @@ L6447-6454 verbatim
theorem ambientSumPositiveRoot_leadingMinor {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (p q k : Fin (r + 1)) :
    ambientSumPositiveRoot h p q (leadingMinor h k) = 0 := by
  unfold leadingMinor
  apply derivation_det_eq_zero
  intro a b
  exact ambientSumPositiveRoot_isotropicVariable h p q
    (minorIndex k a) (minorIndex k b)


-- @@ L6456-6466 verbatim
theorem ambientSumPositiveRoot_highestWeightPolynomial {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (e : Fin (r + 1) → ℕ)
    (p q : Fin (r + 1)) :
    ambientSumPositiveRoot h p q (highestWeightPolynomial h e) = 0 := by
  classical
  unfold highestWeightPolynomial
  apply derivation_prod_eq_zero
  intro k _
  rw [(ambientSumPositiveRoot h p q).leibniz_pow,
    ambientSumPositiveRoot_leadingMinor h p q k]
  simp only [smul_eq_mul, mul_zero, nsmul_zero]


-- @@ L6468-6475 verbatim
theorem ambientSumPositiveRoot_dominantHighestWeightWitness {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (p q : Fin (r + 1)) :
    ambientSumPositiveRoot h p q
        (dominantHighestWeightWitness h lam hdom).polynomial = 0 :=
  ambientSumPositiveRoot_highestWeightPolynomial h
    (signatureExponent lam) p q


-- @@ L6477-6498 verbatim
theorem pderiv_outside_isotropicVariable {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (a i j : Fin (r + 1)) (t : Fin n)
    (ht : 2 * (r + 1) ≤ t.val) :
    MvPolynomial.pderiv (variableIndex a t)
        (isotropicVariable h i j) = 0 := by
  classical
  have he : evenCoordinate h j ≠ t := by
    intro he
    have hv := congrArg Fin.val he
    have hj := j.isLt
    simp only [evenCoordinate_val] at hv
    omega
  have ho : oddCoordinate h j ≠ t := by
    intro ho
    have hv := congrArg Fin.val ho
    have hj := j.isLt
    simp only [oddCoordinate_val] at hv
    omega
  simp only [isotropicVariable, map_add, MvPolynomial.pderiv_X, ne_eq, variableIndex_eq_iff, he,
    and_false, not_false_eq_true, Pi.single_eq_of_ne, Derivation.leibniz, ho, smul_eq_mul, mul_zero,
    MvPolynomial.derivation_C, add_zero]


-- @@ L6500-6513 verbatim
/-- The ambient short positive root used in the spherical-code argument. -/
def ambientShortPositiveRoot {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (p : Fin (r + 1)) (t : Fin n) :
    Derivation ℂ (MvPolynomial (Fin ((r + 1) * n)) ℂ)
      (MvPolynomial (Fin ((r + 1) * n)) ℂ) :=
  ∑ a : Fin (r + 1),
    (isotropicVariable h a p •
      (MvPolynomial.pderiv (variableIndex a t) :
        Derivation ℂ (MvPolynomial (Fin ((r + 1) * n)) ℂ)
          (MvPolynomial (Fin ((r + 1) * n)) ℂ)) -
      (MvPolynomial.X (variableIndex a t) :
        MvPolynomial (Fin ((r + 1) * n)) ℂ) •
        antiholomorphicDerivative h a p)


-- @@ L6515-6544 verbatim
theorem ambientShortPositiveRoot_isotropicVariable {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (p i j : Fin (r + 1)) (t : Fin n)
    (ht : 2 * (r + 1) ≤ t.val) :
    ambientShortPositiveRoot h p t (isotropicVariable h i j) = 0 := by
  classical
  change
    (Derivation.coeFnAddMonoidHom
      (∑ a : Fin (r + 1),
        (isotropicVariable h a p •
          (MvPolynomial.pderiv (variableIndex a t) :
            Derivation ℂ (MvPolynomial (Fin ((r + 1) * n)) ℂ)
              (MvPolynomial (Fin ((r + 1) * n)) ℂ)) -
          (MvPolynomial.X (variableIndex a t) :
            MvPolynomial (Fin ((r + 1) * n)) ℂ) •
            antiholomorphicDerivative h a p)))
        (isotropicVariable h i j) = 0
  rw [map_sum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro a _
  change
    isotropicVariable h a p *
      MvPolynomial.pderiv (variableIndex a t)
        (isotropicVariable h i j) -
      MvPolynomial.X (variableIndex a t) *
        antiholomorphicDerivative h a p
          (isotropicVariable h i j) = 0
  rw [pderiv_outside_isotropicVariable h a i j t ht,
    antiholomorphicDerivative_isotropicVariable]
  simp only [mul_zero, sub_self]


-- @@ L6546-6555 verbatim
theorem ambientShortPositiveRoot_leadingMinor {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (p k : Fin (r + 1)) (t : Fin n)
    (ht : 2 * (r + 1) ≤ t.val) :
    ambientShortPositiveRoot h p t (leadingMinor h k) = 0 := by
  unfold leadingMinor
  apply derivation_det_eq_zero
  intro a b
  exact ambientShortPositiveRoot_isotropicVariable h p
    (minorIndex k a) (minorIndex k b) t ht


-- @@ L6557-6568 verbatim
theorem ambientShortPositiveRoot_highestWeightPolynomial {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (e : Fin (r + 1) → ℕ)
    (p : Fin (r + 1)) (t : Fin n)
    (ht : 2 * (r + 1) ≤ t.val) :
    ambientShortPositiveRoot h p t (highestWeightPolynomial h e) = 0 := by
  classical
  unfold highestWeightPolynomial
  apply derivation_prod_eq_zero
  intro k _
  rw [(ambientShortPositiveRoot h p t).leibniz_pow,
    ambientShortPositiveRoot_leadingMinor h p k t ht]
  simp only [smul_eq_mul, mul_zero, nsmul_zero]


-- @@ L6570-6578 verbatim
theorem ambientShortPositiveRoot_dominantHighestWeightWitness {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (p : Fin (r + 1)) (t : Fin n)
    (ht : 2 * (r + 1) ≤ t.val) :
    ambientShortPositiveRoot h p t
        (dominantHighestWeightWitness h lam hdom).polynomial = 0 :=
  ambientShortPositiveRoot_highestWeightPolynomial h
    (signatureExponent lam) p t ht


-- @@ L6580-6585 verbatim
/-- The ambient cartan used in the spherical-code argument. -/
def ambientCartan {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (p : Fin (r + 1)) :
    Derivation ℂ (MvPolynomial (Fin ((r + 1) * n)) ℂ)
      (MvPolynomial (Fin ((r + 1) * n)) ℂ) :=
  ambientPositiveRoot h p p


-- @@ L6587-6591 verbatim
theorem ambientCartan_isotropicVariable {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (p i j : Fin (r + 1)) :
    ambientCartan h p (isotropicVariable h i j) =
      if p = j then (2 : ℂ) • isotropicVariable h i p else 0 :=
  ambientPositiveRoot_isotropicVariable h p p i j


-- @@ L6593-6651 verbatim
theorem ambientCartan_leadingMinor {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (p k : Fin (r + 1)) :
    ambientCartan h p (leadingMinor h k) =
      if p ≤ k then (2 : ℂ) • leadingMinor h k else 0 := by
  classical
  unfold leadingMinor
  by_cases hp : p.val ≤ k.val
  · let pp : Fin (k.val + 1) := ⟨p.val, by omega⟩
    have hpp : minorIndex k pp = p := Fin.ext rfl
    rw [ite_eq_left (show p ≤ k from hp), derivation_det_singleColumn
      (ambientCartan h p)
      (Matrix.of fun a b : Fin (k.val + 1) =>
        isotropicVariable h (minorIndex k a) (minorIndex k b)) pp]
    · have hcol :
          (fun a : Fin (k.val + 1) =>
            ambientCartan h p
              (isotropicVariable h (minorIndex k a) (minorIndex k pp))) =
          (MvPolynomial.C (2 : ℂ) :
            MvPolynomial (Fin ((r + 1) * n)) ℂ) •
              (fun a : Fin (k.val + 1) =>
                isotropicVariable h (minorIndex k a) (minorIndex k pp)) := by
        funext a
        rw [ambientCartan_isotropicVariable, hpp, ite_eq_left rfl]
        simp [Pi.smul_apply, Algebra.smul_def, smul_eq_mul]
      simp only [Matrix.of_apply]
      rw [hcol, Matrix.det_updateCol_smul]
      have hcolumn :
          (fun a : Fin (k.val + 1) =>
            isotropicVariable h (minorIndex k a) (minorIndex k pp)) =
          (fun a => (Matrix.of fun a b : Fin (k.val + 1) =>
            isotropicVariable h (minorIndex k a) (minorIndex k b)) a pp) := by
        funext a
        simp only [Matrix.of_apply]
      rw [hcolumn, Matrix.updateCol_eq_self]
      simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq]
    · intro a b hb
      simp only [Matrix.of_apply]
      rw [ambientCartan_isotropicVariable]
      have hne : p ≠ minorIndex k b := by
        intro heq
        apply hb
        apply Fin.ext
        have hv := congrArg Fin.val heq
        change p.val = b.val at hv
        exact hv.symm
      simp only [hne, ↓reduceIte]
  · rw [ite_eq_right (show ¬ p ≤ k from hp)]
    apply derivation_det_eq_zero
    intro a b
    simp only [Matrix.of_apply]
    rw [ambientCartan_isotropicVariable]
    have hne : p ≠ minorIndex k b := by
      intro heq
      have hv := congrArg Fin.val heq
      change p.val = b.val at hv
      have hb := b.isLt
      omega
    simp only [hne, ↓reduceIte]


-- @@ L6653-6689 verbatim
theorem ambientCartan_highestWeightPolynomial {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (e : Fin (r + 1) → ℕ)
    (p : Fin (r + 1)) :
    ambientCartan h p (highestWeightPolynomial h e) =
      ((2 * determinantWeight e p : ℕ) : ℂ) •
        highestWeightPolynomial h e := by
  classical
  have hsum :
      (∑ k : Fin (r + 1), if p ≤ k then 2 * e k else 0) =
        2 * determinantWeight e p := by
    unfold determinantWeight
    calc
      (∑ k : Fin (r + 1), if p ≤ k then 2 * e k else 0) =
          ∑ k : Fin (r + 1), 2 * (if p ≤ k then e k else 0) := by
            apply Finset.sum_congr rfl
            intro k _
            split_ifs <;> simp
      _ = 2 * ∑ k : Fin (r + 1), if p ≤ k then e k else 0 := by
        rw [Finset.mul_sum]
  unfold highestWeightPolynomial
  rw [← hsum, Nat.cast_sum]
  apply derivation_prod_eigen (ambientCartan h p)
    Finset.univ
    (fun k : Fin (r + 1) => leadingMinor h k ^ e k)
    (fun k => if p ≤ k then 2 * e k else 0)
  intro k _
  rw [(ambientCartan h p).leibniz_pow,
    ambientCartan_leadingMinor]
  by_cases hpk : p ≤ k
  · simp only [hpk, ite_true]
    cases he : e k with
    | zero => simp only [zero_tsub, pow_zero, smul_eq_mul, Algebra.mul_smul_comm, one_mul,
                mul_zero, CharP.cast_eq_zero, zero_smul]
    | succ m =>
        simp [Algebra.smul_def, pow_succ, smul_eq_mul]
        ring
  · simp only [hpk, ↓reduceIte, smul_eq_mul, mul_zero, nsmul_zero, CharP.cast_eq_zero, zero_smul]


-- @@ L6691-6703 verbatim
theorem ambientCartan_dominantHighestWeightWitness {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (p : Fin (r + 1)) :
    ambientCartan h p (dominantHighestWeightWitness h lam hdom).polynomial =
      ((2 * lam p : ℕ) : ℂ) •
        (dominantHighestWeightWitness h lam hdom).polynomial := by
  change
    ambientCartan h p (highestWeightPolynomial h (signatureExponent lam)) =
      ((2 * lam p : ℕ) : ℂ) •
        highestWeightPolynomial h (signatureExponent lam)
  rw [ambientCartan_highestWeightPolynomial,
    congrFun (determinantWeight_signatureExponent lam hdom) p]


-- @@ L6705-6705 verbatim
end DeterminantVectors


-- @@ L6707-6707 verbatim
end


-- @@ L6709-6709 verbatim
end HigherHarmonicYoung


-- @@ L6711-6711 verbatim
section


-- @@ L6713-6713 verbatim
open scoped BigOperators


-- @@ L6715-6715 verbatim
namespace HigherChannel


-- @@ L6717-6721 verbatim
/-- The finite interlacing used in the spherical-code argument. -/
def FiniteInterlacing {r : ℕ} (n : ℕ)
    (lam : Fin (r + 1) → ℕ) (mu : Fin r → ℕ) : Prop :=
  2 * r + 4 ≤ n ∧
    ∀ m : Fin r, mu m ≤ lam m.castSucc ∧ lam m.succ ≤ mu m


-- @@ L6723-6726 verbatim
/-- The ambient shift used in the spherical-code argument. -/
def ambientShift {r : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ)
    (ℓ : Fin (r + 1)) : ℝ :=
  (lam ℓ : ℝ) + (n : ℝ) / 2 - ((ℓ.val : ℝ) + 1)


-- @@ L6728-6731 verbatim
/-- The stabilizer shift used in the spherical-code argument. -/
def stabilizerShift {r : ℕ} (n : ℕ) (mu : Fin r → ℕ)
    (m : Fin r) : ℝ :=
  (mu m : ℝ) + ((n : ℝ) - 1) / 2 - ((m.val : ℝ) + 1)


-- @@ L6733-6735 verbatim
/-- The wall shift used in the spherical-code argument. -/
def wallShift (n r : ℕ) : ℝ :=
  (n : ℝ) / 2 - (r : ℝ) - 1


-- @@ L6737-6742 verbatim
theorem FiniteInterlacing.wallShift_pos {r n : ℕ}
    {lam : Fin (r + 1) → ℕ} {mu : Fin r → ℕ}
    (h : FiniteInterlacing n lam mu) : 0 < wallShift n r := by
  have hn : (2 * r + 4 : ℝ) ≤ n := by exact_mod_cast h.1
  unfold wallShift
  linarith


-- @@ L6744-6749 verbatim
theorem FiniteInterlacing.one_le_wallShift {r n : ℕ}
    {lam : Fin (r + 1) → ℕ} {mu : Fin r → ℕ}
    (h : FiniteInterlacing n lam mu) : 1 ≤ wallShift n r := by
  have hn : (2 * r + 4 : ℝ) ≤ n := by exact_mod_cast h.1
  unfold wallShift
  linarith


-- @@ L6751-6759 verbatim
theorem FiniteInterlacing.ambientShift_succ_add_one_le {r n : ℕ}
    {lam : Fin (r + 1) → ℕ} {mu : Fin r → ℕ}
    (h : FiniteInterlacing n lam mu) (m : Fin r) :
    ambientShift n lam m.succ + 1 ≤ ambientShift n lam m.castSucc := by
  have hweight : lam m.succ ≤ lam m.castSucc := (h.2 m).2.trans (h.2 m).1
  have hweight' : (lam m.succ : ℝ) ≤ lam m.castSucc := by exact_mod_cast hweight
  unfold ambientShift
  simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
  linarith


-- @@ L6761-6767 verbatim
theorem FiniteInterlacing.ambientShift_strictAnti {r n : ℕ}
    {lam : Fin (r + 1) → ℕ} {mu : Fin r → ℕ}
    (h : FiniteInterlacing n lam mu) :
    StrictAnti (ambientShift n lam) := by
  apply Fin.strictAnti_iff_succ_lt.mpr
  intro m
  linarith [h.ambientShift_succ_add_one_le m]


-- @@ L6769-6773 verbatim
theorem ambientShift_last {r n : ℕ} (lam : Fin (r + 1) → ℕ) :
    ambientShift n lam (Fin.last r) =
      (lam (Fin.last r) : ℝ) + wallShift n r := by
  simp only [ambientShift, Fin.val_last, wallShift]
  ring


-- @@ L6775-6783 verbatim
theorem FiniteInterlacing.ambientShift_pos {r n : ℕ}
    {lam : Fin (r + 1) → ℕ} {mu : Fin r → ℕ}
    (h : FiniteInterlacing n lam mu) (ℓ : Fin (r + 1)) :
    0 < ambientShift n lam ℓ := by
  have hlast : 0 < ambientShift n lam (Fin.last r) := by
    rw [ambientShift_last]
    exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) h.wallShift_pos
  exact hlast.trans_le
    (h.ambientShift_strictAnti.antitone ℓ.le_last)


-- @@ L6785-6792 verbatim
theorem FiniteInterlacing.wallShift_le_ambientShift {r n : ℕ}
    {lam : Fin (r + 1) → ℕ} {mu : Fin r → ℕ}
    (h : FiniteInterlacing n lam mu) (ℓ : Fin (r + 1)) :
    wallShift n r ≤ ambientShift n lam ℓ := by
  have hlast : wallShift n r ≤ ambientShift n lam (Fin.last r) := by
    rw [ambientShift_last]
    exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  exact hlast.trans (h.ambientShift_strictAnti.antitone ℓ.le_last)


-- @@ L6794-6802 verbatim
theorem FiniteInterlacing.ambientShift_castSucc_ge {r n : ℕ}
    {lam : Fin (r + 1) → ℕ} {mu : Fin r → ℕ}
    (h : FiniteInterlacing n lam mu) (m : Fin r) :
    stabilizerShift n mu m + 1 / 2 ≤
      ambientShift n lam m.castSucc := by
  have hweight : (mu m : ℝ) ≤ lam m.castSucc := by exact_mod_cast (h.2 m).1
  unfold ambientShift stabilizerShift
  simp only [Fin.val_castSucc]
  linarith


-- @@ L6804-6811 verbatim
theorem FiniteInterlacing.stabilizerShift_ge_succ {r n : ℕ}
    {lam : Fin (r + 1) → ℕ} {mu : Fin r → ℕ}
    (h : FiniteInterlacing n lam mu) (m : Fin r) :
    ambientShift n lam m.succ + 1 / 2 ≤ stabilizerShift n mu m := by
  have hweight : (lam m.succ : ℝ) ≤ mu m := by exact_mod_cast (h.2 m).2
  unfold ambientShift stabilizerShift
  simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
  linarith


-- @@ L6813-6818 verbatim
theorem FiniteInterlacing.stabilizerShift_pos {r n : ℕ}
    {lam : Fin (r + 1) → ℕ} {mu : Fin r → ℕ}
    (h : FiniteInterlacing n lam mu) (m : Fin r) :
    0 < stabilizerShift n mu m := by
  have ha := h.ambientShift_pos m.succ
  linarith [h.stabilizerShift_ge_succ m]


-- @@ L6820-6824 verbatim
/-- The active denominator used in the spherical-code argument. -/
def activeDenominator {r : ℕ}
    (L : Fin (r + 1) → ℝ) (ℓ : Fin (r + 1)) : ℝ :=
  2 * L ℓ * ∏ q : Fin r,
    (L ℓ ^ 2 - L (ℓ.succAbove q) ^ 2)


-- @@ L6826-6834 verbatim
/-- The plus probability used in the spherical-code argument. -/
def plusProbability {r : ℕ} (n : ℕ)
    (lam : Fin (r + 1) → ℕ) (mu : Fin r → ℕ)
    (ℓ : Fin (r + 1)) : ℝ :=
  ((ambientShift n lam ℓ + wallShift n r) *
    ∏ m : Fin r,
      ((ambientShift n lam ℓ + 1 / 2) ^ 2 -
        stabilizerShift n mu m ^ 2)) /
      activeDenominator (ambientShift n lam) ℓ


-- @@ L6836-6844 verbatim
/-- The minus probability used in the spherical-code argument. -/
def minusProbability {r : ℕ} (n : ℕ)
    (lam : Fin (r + 1) → ℕ) (mu : Fin r → ℕ)
    (ℓ : Fin (r + 1)) : ℝ :=
  ((ambientShift n lam ℓ - wallShift n r) *
    ∏ m : Fin r,
      ((ambientShift n lam ℓ - 1 / 2) ^ 2 -
        stabilizerShift n mu m ^ 2)) /
      activeDenominator (ambientShift n lam) ℓ


-- @@ L6846-6862 verbatim
theorem FiniteInterlacing.activeDenominator_ne_zero {r n : ℕ}
    {lam : Fin (r + 1) → ℕ} {mu : Fin r → ℕ}
    (h : FiniteInterlacing n lam mu) (ℓ : Fin (r + 1)) :
    activeDenominator (ambientShift n lam) ℓ ≠ 0 := by
  unfold activeDenominator
  apply mul_ne_zero
  · exact mul_ne_zero (by norm_num) (h.ambientShift_pos ℓ).ne'
  · apply Finset.prod_ne_zero_iff.mpr
    intro q _
    apply sub_ne_zero.mpr
    intro heq
    have hpos := h.ambientShift_pos ℓ
    have hpos' := h.ambientShift_pos (ℓ.succAbove q)
    have hsame : ambientShift n lam ℓ =
        ambientShift n lam (ℓ.succAbove q) := by nlinarith
    exact (Fin.ne_succAbove ℓ q)
      (h.ambientShift_strictAnti.injective hsame)


-- @@ L6864-6908 verbatim
theorem FiniteInterlacing.plusFactor_nonneg {r n : ℕ}
    {lam : Fin (r + 1) → ℕ} {mu : Fin r → ℕ}
    (h : FiniteInterlacing n lam mu)
    (ℓ : Fin (r + 1)) (m : Fin r) :
    0 ≤ ((ambientShift n lam ℓ + 1 / 2) ^ 2 -
        stabilizerShift n mu m ^ 2) /
      (ambientShift n lam ℓ ^ 2 -
        ambientShift n lam (ℓ.succAbove m) ^ 2) := by
  by_cases hm : m.castSucc < ℓ
  · rw [Fin.succAbove_of_castSucc_lt ℓ m hm]
    have hindex : m.succ ≤ ℓ := Fin.castSucc_lt_iff_succ_le.mp hm
    have hL : ambientShift n lam ℓ ≤ ambientShift n lam m.succ :=
      h.ambientShift_strictAnti.antitone hindex
    have hupper : ambientShift n lam ℓ + 1 / 2 ≤ stabilizerShift n mu m := by
      linarith [h.stabilizerShift_ge_succ m]
    have hnonneg : 0 ≤ ambientShift n lam ℓ + 1 / 2 := by
      linarith [h.ambientShift_pos ℓ]
    have hnum :
        (ambientShift n lam ℓ + 1 / 2) ^ 2 -
          stabilizerShift n mu m ^ 2 ≤ 0 := by
      linarith [(sq_le_sq₀ hnonneg (h.stabilizerShift_pos m).le).2 hupper]
    have hlt : ambientShift n lam ℓ < ambientShift n lam m.castSucc :=
      h.ambientShift_strictAnti hm
    have hden : ambientShift n lam ℓ ^ 2 -
        ambientShift n lam m.castSucc ^ 2 < 0 := by
      nlinarith [h.ambientShift_pos ℓ, h.ambientShift_pos m.castSucc]
    exact div_nonneg_of_nonpos hnum hden.le
  · have hm' : ℓ ≤ m.castSucc := le_of_not_gt hm
    rw [Fin.succAbove_of_le_castSucc ℓ m hm']
    have hL : ambientShift n lam m.castSucc ≤ ambientShift n lam ℓ :=
      h.ambientShift_strictAnti.antitone hm'
    have hlower : stabilizerShift n mu m ≤ ambientShift n lam ℓ + 1 / 2 := by
      linarith [h.ambientShift_castSucc_ge m]
    have hnum : 0 ≤
        (ambientShift n lam ℓ + 1 / 2) ^ 2 -
          stabilizerShift n mu m ^ 2 := by
      have hnonneg : 0 ≤ ambientShift n lam ℓ + 1 / 2 := by
        linarith [h.ambientShift_pos ℓ]
      linarith [(sq_le_sq₀ (h.stabilizerShift_pos m).le hnonneg).2 hlower]
    have hlt : ambientShift n lam m.succ < ambientShift n lam ℓ :=
      h.ambientShift_strictAnti (Fin.le_castSucc_iff.mp hm')
    have hden : 0 ≤ ambientShift n lam ℓ ^ 2 -
        ambientShift n lam m.succ ^ 2 := by
      nlinarith [h.ambientShift_pos ℓ, h.ambientShift_pos m.succ]
    exact div_nonneg hnum hden


-- @@ L6910-6952 verbatim
theorem FiniteInterlacing.minusFactor_nonneg {r n : ℕ}
    {lam : Fin (r + 1) → ℕ} {mu : Fin r → ℕ}
    (h : FiniteInterlacing n lam mu)
    (ℓ : Fin (r + 1)) (m : Fin r) :
    0 ≤ ((ambientShift n lam ℓ - 1 / 2) ^ 2 -
        stabilizerShift n mu m ^ 2) /
      (ambientShift n lam ℓ ^ 2 -
        ambientShift n lam (ℓ.succAbove m) ^ 2) := by
  have hhalf : 0 ≤ ambientShift n lam ℓ - 1 / 2 := by
    linarith [h.one_le_wallShift, h.wallShift_le_ambientShift ℓ]
  by_cases hm : m.castSucc < ℓ
  · rw [Fin.succAbove_of_castSucc_lt ℓ m hm]
    have hindex : m.succ ≤ ℓ := Fin.castSucc_lt_iff_succ_le.mp hm
    have hL : ambientShift n lam ℓ ≤ ambientShift n lam m.succ :=
      h.ambientShift_strictAnti.antitone hindex
    have hupper : ambientShift n lam ℓ - 1 / 2 ≤ stabilizerShift n mu m := by
      linarith [h.stabilizerShift_ge_succ m]
    have hnum :
        (ambientShift n lam ℓ - 1 / 2) ^ 2 -
          stabilizerShift n mu m ^ 2 ≤ 0 := by
      linarith [(sq_le_sq₀ hhalf (h.stabilizerShift_pos m).le).2 hupper]
    have hlt : ambientShift n lam ℓ < ambientShift n lam m.castSucc :=
      h.ambientShift_strictAnti hm
    have hden : ambientShift n lam ℓ ^ 2 -
        ambientShift n lam m.castSucc ^ 2 < 0 := by
      nlinarith [h.ambientShift_pos ℓ, h.ambientShift_pos m.castSucc]
    exact div_nonneg_of_nonpos hnum hden.le
  · have hm' : ℓ ≤ m.castSucc := le_of_not_gt hm
    rw [Fin.succAbove_of_le_castSucc ℓ m hm']
    have hL : ambientShift n lam m.castSucc ≤ ambientShift n lam ℓ :=
      h.ambientShift_strictAnti.antitone hm'
    have hlower : stabilizerShift n mu m ≤ ambientShift n lam ℓ - 1 / 2 := by
      linarith [h.ambientShift_castSucc_ge m]
    have hnum : 0 ≤
        (ambientShift n lam ℓ - 1 / 2) ^ 2 -
          stabilizerShift n mu m ^ 2 := by
      linarith [(sq_le_sq₀ (h.stabilizerShift_pos m).le hhalf).2 hlower]
    have hlt : ambientShift n lam m.succ < ambientShift n lam ℓ :=
      h.ambientShift_strictAnti (Fin.le_castSucc_iff.mp hm')
    have hden : 0 ≤ ambientShift n lam ℓ ^ 2 -
        ambientShift n lam m.succ ^ 2 := by
      nlinarith [h.ambientShift_pos ℓ, h.ambientShift_pos m.succ]
    exact div_nonneg hnum hden


-- @@ L6954-6963 verbatim
theorem FiniteInterlacing.plusProbability_nonneg {r n : ℕ}
    {lam : Fin (r + 1) → ℕ} {mu : Fin r → ℕ}
    (h : FiniteInterlacing n lam mu) (ℓ : Fin (r + 1)) :
    0 ≤ plusProbability n lam mu ℓ := by
  unfold plusProbability activeDenominator
  rw [mul_div_mul_comm, ← Finset.prod_div_distrib]
  exact mul_nonneg
    (div_nonneg (by linarith [h.ambientShift_pos ℓ, h.wallShift_pos])
      (mul_pos (by norm_num) (h.ambientShift_pos ℓ)).le)
    (Finset.prod_nonneg fun m _ => h.plusFactor_nonneg ℓ m)


-- @@ L6965-6974 verbatim
theorem FiniteInterlacing.minusProbability_nonneg {r n : ℕ}
    {lam : Fin (r + 1) → ℕ} {mu : Fin r → ℕ}
    (h : FiniteInterlacing n lam mu) (ℓ : Fin (r + 1)) :
    0 ≤ minusProbability n lam mu ℓ := by
  unfold minusProbability activeDenominator
  rw [mul_div_mul_comm, ← Finset.prod_div_distrib]
  exact mul_nonneg
    (div_nonneg (by linarith [h.wallShift_le_ambientShift ℓ])
      (mul_pos (by norm_num) (h.ambientShift_pos ℓ)).le)
    (Finset.prod_nonneg fun m _ => h.minusFactor_nonneg ℓ m)


-- @@ L6976-6979 verbatim
/-- The signed node used in the spherical-code argument. -/
def signedNode {r : ℕ} (L : Fin (r + 1) → ℝ)
    (z : Fin (r + 1) × Bool) : ℝ :=
  if z.2 then L z.1 else -L z.1


-- @@ L6981-6993 verbatim
theorem signedNode_injective {r : ℕ}
    {L : Fin (r + 1) → ℝ}
    (hpos : ∀ ℓ, 0 < L ℓ) (hinj : Function.Injective L) :
    Function.Injective (signedNode L) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ heq
  cases a <;> cases b <;>
    simp only [signedNode, Bool.false_eq_true, ite_false, ite_true] at heq
  · exact Prod.ext (hinj (neg_injective heq)) rfl
  · exfalso
    linarith [hpos i, hpos j]
  · exfalso
    linarith [hpos i, hpos j]
  · exact Prod.ext (hinj heq) rfl


-- @@ L6995-7001 verbatim
/-- The channel numerator polynomial used in the spherical-code argument. -/
def channelNumeratorPolynomial {r : ℕ}
    (rho : ℝ) (M : Fin r → ℝ) : Polynomial ℝ :=
  (Polynomial.X + Polynomial.C rho) *
    ∏ m : Fin r,
      ((Polynomial.X + Polynomial.C (1 / 2 - M m)) *
        (Polynomial.X + Polynomial.C (1 / 2 + M m)))


-- @@ L7003-7013 verbatim
theorem channelNumeratorPolynomial_eval_pos {r : ℕ}
    (rho : ℝ) (M : Fin r → ℝ) (t : ℝ) :
    (channelNumeratorPolynomial rho M).eval t =
      (t + rho) * ∏ m : Fin r, ((t + 1 / 2) ^ 2 - M m ^ 2) := by
  unfold channelNumeratorPolynomial
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro m _
  ring


-- @@ L7015-7020 verbatim
private theorem signed_erase_pos_metriccodes2_e052d2d1 {r : ℕ} (ℓ : Fin (r + 1)) :
    (Finset.univ : Finset (Fin (r + 1) × Bool)).erase (ℓ, true) =
      ((Finset.univ.erase ℓ).product (Finset.univ : Finset Bool)) ∪
        {(ℓ, false)} := by
  ext ⟨q, b⟩
  cases b <;> by_cases hq : q = ℓ <;> simp [hq]


-- @@ L7022-7027 verbatim
private theorem signed_erase_neg_metriccodes2_e052d2d1 {r : ℕ} (ℓ : Fin (r + 1)) :
    (Finset.univ : Finset (Fin (r + 1) × Bool)).erase (ℓ, false) =
      ((Finset.univ.erase ℓ).product (Finset.univ : Finset Bool)) ∪
        {(ℓ, true)} := by
  ext ⟨q, b⟩
  cases b <;> by_cases hq : q = ℓ <;> simp [hq]


-- @@ L7029-7058 verbatim
theorem signedNode_denominator_pos {r : ℕ}
    (L : Fin (r + 1) → ℝ) (ℓ : Fin (r + 1)) :
    (∏ z ∈ (Finset.univ : Finset (Fin (r + 1) × Bool)).erase (ℓ, true),
      (L ℓ - signedNode L z)) =
        2 * L ℓ * ∏ j ∈ Finset.univ.erase ℓ,
          (L ℓ ^ 2 - L j ^ 2) := by
  rw [signed_erase_pos_metriccodes2_e052d2d1]
  have hdisjoint :
      Disjoint (((Finset.univ.erase ℓ).product (Finset.univ : Finset Bool)))
        {(ℓ, false)} := by
    simp only [Fintype.univ_bool, Finset.product_eq_sprod, Finset.disjoint_singleton_right,
      Finset.mem_product, Finset.mem_erase, ne_eq, not_true_eq_false, Finset.mem_univ, and_true,
      Finset.mem_insert, Bool.false_eq_true, Finset.mem_singleton, or_true, not_false_eq_true]
  rw [Finset.prod_union hdisjoint, Finset.prod_singleton]
  have hproduct :
      (∏ z ∈ ((Finset.univ.erase ℓ).product (Finset.univ : Finset Bool)),
        (L ℓ - signedNode L z)) =
      ∏ j ∈ Finset.univ.erase ℓ,
        ∏ b : Bool, (L ℓ - signedNode L (j, b)) := by
    exact Finset.prod_product (Finset.univ.erase ℓ)
      (Finset.univ : Finset Bool) (fun z => L ℓ - signedNode L z)
  rw [hproduct]
  simp only [signedNode, Bool.false_eq_true, ite_false, ite_true,
    Fintype.prod_bool]
  have hfactor : ∀ j : Fin (r + 1),
      (L ℓ - L j) * (L ℓ - -L j) = L ℓ ^ 2 - L j ^ 2 := by
    intro j
    ring
  simp_rw [hfactor]
  ring


-- @@ L7060-7089 verbatim
theorem signedNode_denominator_neg {r : ℕ}
    (L : Fin (r + 1) → ℝ) (ℓ : Fin (r + 1)) :
    (∏ z ∈ (Finset.univ : Finset (Fin (r + 1) × Bool)).erase (ℓ, false),
      (-L ℓ - signedNode L z)) =
        -(2 * L ℓ * ∏ j ∈ Finset.univ.erase ℓ,
          (L ℓ ^ 2 - L j ^ 2)) := by
  rw [signed_erase_neg_metriccodes2_e052d2d1]
  have hdisjoint :
      Disjoint (((Finset.univ.erase ℓ).product (Finset.univ : Finset Bool)))
        {(ℓ, true)} := by
    simp only [Fintype.univ_bool, Finset.product_eq_sprod, Finset.disjoint_singleton_right,
      Finset.mem_product, Finset.mem_erase, ne_eq, not_true_eq_false, Finset.mem_univ, and_true,
      Finset.mem_insert, Finset.mem_singleton, Bool.true_eq_false, or_false, not_false_eq_true]
  rw [Finset.prod_union hdisjoint, Finset.prod_singleton]
  have hproduct :
      (∏ z ∈ ((Finset.univ.erase ℓ).product (Finset.univ : Finset Bool)),
        (-L ℓ - signedNode L z)) =
      ∏ j ∈ Finset.univ.erase ℓ,
        ∏ b : Bool, (-L ℓ - signedNode L (j, b)) := by
    exact Finset.prod_product (Finset.univ.erase ℓ)
      (Finset.univ : Finset Bool) (fun z => -L ℓ - signedNode L z)
  rw [hproduct]
  simp only [signedNode, Bool.false_eq_true, ite_false, ite_true,
    Fintype.prod_bool]
  have hfactor : ∀ j : Fin (r + 1),
      (-L ℓ - L j) * (-L ℓ - -L j) = L ℓ ^ 2 - L j ^ 2 := by
    intro j
    ring
  simp_rw [hfactor]
  ring


-- @@ L7091-7104 verbatim
theorem activeQuadraticDenominator_eq_prod_erase {r : ℕ}
    (L : Fin (r + 1) → ℝ) (ℓ : Fin (r + 1)) :
    (∏ m : Fin r, (L ℓ ^ 2 - L (ℓ.succAbove m) ^ 2)) =
      ∏ j ∈ Finset.univ.erase ℓ, (L ℓ ^ 2 - L j ^ 2) := by
  classical
  refine Finset.prod_bij (fun j _ => ℓ.succAbove j)
    (fun j _ => ?_) (fun i _ j _ hij => ?_) (fun j hj => ?_)
    (fun _ _ => rfl)
  · simp only [Finset.mem_erase, ne_eq, Fin.succAbove_ne, not_false_eq_true, Finset.mem_univ,
      and_self]
  · exact Fin.succAbove_right_injective hij
  · obtain ⟨hj', _⟩ := Finset.mem_erase.mp hj
    obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hj'
    exact ⟨i, Finset.mem_univ i, hi⟩


-- @@ L7106-7111 verbatim
theorem signedNode_denominator_pos_eq_active {r : ℕ}
    (L : Fin (r + 1) → ℝ) (ℓ : Fin (r + 1)) :
    (∏ z ∈ (Finset.univ : Finset (Fin (r + 1) × Bool)).erase (ℓ, true),
      (L ℓ - signedNode L z)) = activeDenominator L ℓ := by
  rw [signedNode_denominator_pos, activeDenominator,
    activeQuadraticDenominator_eq_prod_erase]


-- @@ L7113-7118 verbatim
theorem signedNode_denominator_neg_eq_active {r : ℕ}
    (L : Fin (r + 1) → ℝ) (ℓ : Fin (r + 1)) :
    (∏ z ∈ (Finset.univ : Finset (Fin (r + 1) × Bool)).erase (ℓ, false),
      (-L ℓ - signedNode L z)) = -activeDenominator L ℓ := by
  rw [signedNode_denominator_neg, activeDenominator,
    activeQuadraticDenominator_eq_prod_erase]


-- @@ L7120-7120 verbatim
end HigherChannel


-- @@ L7122-7122 verbatim
end


-- @@ L7124-7124 verbatim
section



-- @@ L7127-7127 verbatim
open scoped BigOperators InnerProductSpace


-- @@ L7129-7129 verbatim
namespace ThreeRowYoungBranching


-- @@ L7131-7131 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L7132-7132 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.GelfandTsetlin


-- @@ L7134-7139 verbatim
/-- Embed a row-variable index into the larger array with one additional row and one additional
coordinate. -/
def transverseVariableIndex {r n : ℕ}
    (a : Fin ((r + 1) * n)) : Fin ((r + 2) * (n + 1)) :=
  let z := finProdFinEquiv.symm a
  variableIndex (r := r + 1) z.1.castSucc z.2.castSucc


-- @@ L7141-7145 verbatim
@[simp] theorem transverseVariableIndex_variableIndex {r n : ℕ}
    (i : Fin (r + 1)) (j : Fin n) :
    transverseVariableIndex (variableIndex i j) =
      variableIndex (r := r + 1) i.castSucc j.castSucc := by
  simp only [transverseVariableIndex, variableIndex, Equiv.symm_apply_apply]


-- @@ L7147-7159 verbatim
theorem transverseVariableIndex_injective {r n : ℕ} :
    Function.Injective (transverseVariableIndex (r := r) (n := n)) := by
  intro a b hab
  have hpair :
      ((finProdFinEquiv.symm a).1.castSucc,
        (finProdFinEquiv.symm a).2.castSucc) =
      ((finProdFinEquiv.symm b).1.castSucc,
        (finProdFinEquiv.symm b).2.castSucc) :=
    variableIndex_injective (r := r + 1) (n := n + 1) hab
  apply finProdFinEquiv.symm.injective
  apply Prod.ext
  · exact Fin.castSucc_injective _ (congrArg Prod.fst hpair)
  · exact Fin.castSucc_injective _ (congrArg Prod.snd hpair)


-- @@ L7161-7164 verbatim
/-- The transverse polynomial used in the spherical-code argument. -/
def transversePolynomial {r : ℕ} (n : ℕ) :
    PolynomialSpace r n →ₐ[ℝ] PolynomialSpace (r + 1) (n + 1) :=
  MvPolynomial.rename (transverseVariableIndex (r := r) (n := n))


-- @@ L7166-7170 verbatim
@[simp] theorem transversePolynomial_X {r n : ℕ}
    (i : Fin (r + 1)) (j : Fin n) :
    transversePolynomial (r := r) n (MvPolynomial.X (variableIndex i j)) =
      MvPolynomial.X (variableIndex (r := r + 1) i.castSucc j.castSucc) := by
  simp only [transversePolynomial, MvPolynomial.rename_X, transverseVariableIndex_variableIndex]


-- @@ L7172-7180 verbatim
@[simp] theorem pderiv_transversePolynomial_castSucc {r n : ℕ}
    (i : Fin (r + 1)) (j : Fin n) (p : PolynomialSpace r n) :
    MvPolynomial.pderiv
        (variableIndex (r := r + 1) i.castSucc j.castSucc)
        (transversePolynomial n p) =
      transversePolynomial n (MvPolynomial.pderiv (variableIndex i j) p) := by
  simpa only [transversePolynomial, transverseVariableIndex_variableIndex] using
    MvPolynomial.pderiv_rename (transverseVariableIndex_injective (r := r) (n := n))
      (variableIndex i j) p


-- @@ L7182-7196 verbatim
@[simp] theorem pderiv_transversePolynomial_lastCoordinate {r n : ℕ}
    (i : Fin (r + 2)) (p : PolynomialSpace r n) :
    MvPolynomial.pderiv
        (variableIndex (r := r + 1) i (Fin.last n))
        (transversePolynomial n p) = 0 := by
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  intro hmem
  obtain ⟨a, _, ha⟩ :=
    MvPolynomial.mem_vars_rename
      (transverseVariableIndex (r := r) (n := n)) p hmem
  have hpair :
      ((finProdFinEquiv.symm a).1.castSucc,
        (finProdFinEquiv.symm a).2.castSucc) = (i, Fin.last n) :=
    variableIndex_injective (r := r + 1) (n := n + 1) ha
  exact Fin.castSucc_ne_last _ (congrArg Prod.snd hpair)


-- @@ L7198-7213 verbatim
@[simp] theorem pderiv_transversePolynomial_lastRow {r n : ℕ}
    (j : Fin (n + 1)) (p : PolynomialSpace r n) :
    MvPolynomial.pderiv
        (variableIndex (r := r + 1) (Fin.last (r + 1)) j)
        (transversePolynomial n p) = 0 := by
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  intro hmem
  obtain ⟨a, _, ha⟩ :=
    MvPolynomial.mem_vars_rename
      (transverseVariableIndex (r := r) (n := n)) p hmem
  have hpair :
      ((finProdFinEquiv.symm a).1.castSucc,
        (finProdFinEquiv.symm a).2.castSucc) =
        (Fin.last (r + 1), j) :=
    variableIndex_injective (r := r + 1) (n := n + 1) ha
  exact Fin.castSucc_ne_last _ (congrArg Prod.fst hpair)


-- @@ L7215-7218 verbatim
/-- The append zero weight used in the spherical-code argument. -/
def appendZeroWeight {r : ℕ} (mu : Fin (r + 1) → ℕ) :
    Fin (r + 2) → ℕ :=
  Fin.lastCases 0 mu


-- @@ L7220-7223 verbatim
@[simp] theorem appendZeroWeight_castSucc {r : ℕ}
    (mu : Fin (r + 1) → ℕ) (i : Fin (r + 1)) :
    appendZeroWeight mu i.castSucc = mu i := by
  simp only [appendZeroWeight, Fin.lastCases_castSucc]


-- @@ L7225-7228 verbatim
@[simp] theorem appendZeroWeight_last {r : ℕ}
    (mu : Fin (r + 1) → ℕ) :
    appendZeroWeight mu (Fin.last (r + 1)) = 0 := by
  simp only [appendZeroWeight, Fin.lastCases_last]


-- @@ L7230-7234 verbatim
@[simp] theorem sum_appendZeroWeight {r : ℕ}
    (mu : Fin (r + 1) → ℕ) :
    (∑ i, appendZeroWeight mu i) = ∑ i, mu i := by
  rw [Fin.sum_univ_castSucc]
  simp only [appendZeroWeight_castSucc, appendZeroWeight_last, add_zero]


-- @@ L7236-7247 verbatim
theorem rowEuler_transversePolynomial_castSucc {r n : ℕ}
    (i : Fin (r + 1)) (p : PolynomialSpace r n) :
    rowEuler (r + 1) (n + 1) i.castSucc
        (transversePolynomial n p) =
      transversePolynomial n (rowEuler r n i p) := by
  rw [rowEuler_apply, Fin.sum_univ_castSucc]
  simp only [pderiv_transversePolynomial_castSucc,
    pderiv_transversePolynomial_lastCoordinate, mul_zero, add_zero]
  rw [rowEuler_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul, transversePolynomial_X]


-- @@ L7249-7257 verbatim
theorem traceOperator_transversePolynomial_castSucc {r n : ℕ}
    (i j : Fin (r + 1)) (p : PolynomialSpace r n) :
    traceOperator (r + 1) (n + 1) i.castSucc j.castSucc
        (transversePolynomial n p) =
      transversePolynomial n (traceOperator r n i j p) := by
  rw [traceOperator_apply, Fin.sum_univ_castSucc]
  simp only [pderiv_transversePolynomial_lastCoordinate, map_zero,
    pderiv_transversePolynomial_castSucc, add_zero]
  simp only [traceOperator_apply, map_sum]


-- @@ L7259-7264 verbatim
theorem traceOperator_transversePolynomial_last_right {r n : ℕ}
    (i : Fin (r + 2)) (p : PolynomialSpace r n) :
    traceOperator (r + 1) (n + 1) i (Fin.last (r + 1))
      (transversePolynomial n p) = 0 := by
  simp only [traceOperator_apply, pderiv_transversePolynomial_lastRow, map_zero,
    Finset.sum_const_zero]


-- @@ L7266-7271 verbatim
theorem traceOperator_transversePolynomial_last_left {r n : ℕ}
    (i : Fin (r + 2)) (p : PolynomialSpace r n) :
    traceOperator (r + 1) (n + 1) (Fin.last (r + 1)) i
      (transversePolynomial n p) = 0 := by
  rw [traceOperator_comm]
  exact traceOperator_transversePolynomial_last_right i p


-- @@ L7273-7284 verbatim
theorem polarization_transversePolynomial_castSucc {r n : ℕ}
    (i j : Fin (r + 1)) (p : PolynomialSpace r n) :
    polarization (r + 1) (n + 1) i.castSucc j.castSucc
        (transversePolynomial n p) =
      transversePolynomial n (polarization r n i j p) := by
  rw [polarization_apply, Fin.sum_univ_castSucc]
  simp only [pderiv_transversePolynomial_lastCoordinate, mul_zero,
    pderiv_transversePolynomial_castSucc, add_zero]
  rw [polarization_apply, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_mul, transversePolynomial_X]


-- @@ L7286-7322 verbatim
theorem transversePolynomial_mem_harmonicYoung {r n : ℕ}
    (mu : Fin (r + 1) → ℕ) (p : PolynomialSpace r n)
    (hp : p ∈ harmonicYoungSubmodule (n := n) mu) :
    transversePolynomial n p ∈
      harmonicYoungSubmodule (n := n + 1) (appendZeroWeight mu) := by
  rw [mem_harmonicYoungSubmodule] at hp ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sum_appendZeroWeight]
    exact hp.1.rename_isHomogeneous
  · intro i
    induction i using Fin.lastCases with
    | last => simp only [rowEuler_apply, pderiv_transversePolynomial_lastRow, mul_zero,
                Finset.sum_const_zero, appendZeroWeight_last, CharP.cast_eq_zero, zero_smul]
    | cast i =>
        rw [rowEuler_transversePolynomial_castSucc, hp.2.1 i]
        simp only [map_smul, appendZeroWeight_castSucc]
  · intro i j
    induction i using Fin.lastCases with
    | last => exact traceOperator_transversePolynomial_last_left j p
    | cast i =>
        induction j using Fin.lastCases with
        | last => exact traceOperator_transversePolynomial_last_right i.castSucc p
        | cast j =>
            rw [traceOperator_transversePolynomial_castSucc,
              hp.2.2.1 i j, map_zero]
  · intro i j hij
    induction i using Fin.lastCases with
    | last =>
        exact (not_lt_of_ge (Fin.le_last j) hij).elim
    | cast i =>
        induction j using Fin.lastCases with
        | last => simp only [polarization_apply, pderiv_transversePolynomial_lastRow, mul_zero,
                    Finset.sum_const_zero]
        | cast j =>
            have hij' : i < j := by simpa only [Fin.castSucc_lt_castSucc_iff] using hij
            rw [polarization_transversePolynomial_castSucc,
              hp.2.2.2 i j hij', map_zero]


-- @@ L7324-7340 verbatim
/-- Embed harmonic Young space by appending a zero weight and adding a transverse coordinate. -/
def appendZeroYoungEmbedding {r n : ℕ}
    (mu : Fin (r + 1) → ℕ) :
    HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      HarmonicYoungSpace (n := n + 1) (appendZeroWeight mu) where
  toFun (p : HarmonicYoungSpace (n := n) mu) :=
    ⟨transversePolynomial (r := r) n (p : PolynomialSpace r n),
      transversePolynomial_mem_harmonicYoung (r := r) (n := n) mu
        (p : PolynomialSpace r n) p.property⟩
  map_add' p q := by
    apply Subtype.ext
    exact map_add (transversePolynomial n)
      (p : PolynomialSpace r n) (q : PolynomialSpace r n)
  map_smul' c p := by
    apply Subtype.ext
    exact map_smul (transversePolynomial n) c
      (p : PolynomialSpace r n)


-- @@ L7342-7363 verbatim
/-- The transverse embedding with an appended zero weight, bundled as a linear isometry. -/
def appendZeroYoungIsometry {r n : ℕ}
    (mu : Fin (r + 1) → ℕ) :
    HarmonicYoungSpace (n := n) mu →ₗᵢ[ℝ]
      HarmonicYoungSpace (n := n + 1) (appendZeroWeight mu) :=
  (appendZeroYoungEmbedding mu).isometryOfInner (by
    intro p q
    calc
      ⟪appendZeroYoungEmbedding mu p,
        appendZeroYoungEmbedding mu q⟫_ℝ =
          SpherePacking.Fischer.polynomialInner ((r + 2) * (n + 1))
            (transversePolynomial n (p : PolynomialSpace r n))
            (transversePolynomial n (q : PolynomialSpace r n)) :=
        young_inner_eq_polynomialInner (appendZeroWeight mu)
          (appendZeroYoungEmbedding mu p) (appendZeroYoungEmbedding mu q)
      _ = SpherePacking.Fischer.polynomialInner ((r + 1) * n)
            (p : PolynomialSpace r n) (q : PolynomialSpace r n) :=
        MetricCodes.Spherical.HigherYoungBranchingFibres.polynomialInner_rename_injective
          (transverseVariableIndex (r := r) (n := n))
          transverseVariableIndex_injective
          (p : PolynomialSpace r n) (q : PolynomialSpace r n)
      _ = ⟪p, q⟫_ℝ := (young_inner_eq_polynomialInner mu p q).symm)


-- @@ L7365-7370 verbatim
/-- Embed a row-variable index into the larger array with one additional row and the same
coordinate dimension. -/
def zeroRowVariableIndex {r n : ℕ}
    (a : Fin ((r + 1) * n)) : Fin ((r + 2) * n) :=
  let z := finProdFinEquiv.symm a
  variableIndex (r := r + 1) z.1.castSucc z.2


-- @@ L7372-7376 verbatim
@[simp] theorem zeroRowVariableIndex_variableIndex {r n : ℕ}
    (i : Fin (r + 1)) (j : Fin n) :
    zeroRowVariableIndex (variableIndex i j) =
      variableIndex (r := r + 1) i.castSucc j := by
  simp only [zeroRowVariableIndex, variableIndex, Equiv.symm_apply_apply]


-- @@ L7378-7390 verbatim
theorem zeroRowVariableIndex_injective {r n : ℕ} :
    Function.Injective (zeroRowVariableIndex (r := r) (n := n)) := by
  intro a b hab
  have hpair :
      ((finProdFinEquiv.symm a).1.castSucc,
        (finProdFinEquiv.symm a).2) =
      ((finProdFinEquiv.symm b).1.castSucc,
        (finProdFinEquiv.symm b).2) :=
    variableIndex_injective (r := r + 1) (n := n) hab
  apply finProdFinEquiv.symm.injective
  apply Prod.ext
  · exact Fin.castSucc_injective _ (congrArg Prod.fst hpair)
  · exact congrArg (fun z : Fin (r + 2) × Fin n => z.2) hpair


-- @@ L7392-7395 verbatim
/-- The zero row polynomial used in the spherical-code argument. -/
def zeroRowPolynomial {r : ℕ} (n : ℕ) :
    PolynomialSpace r n →ₐ[ℝ] PolynomialSpace (r + 1) n :=
  MvPolynomial.rename (zeroRowVariableIndex (r := r) (n := n))


-- @@ L7397-7401 verbatim
@[simp] theorem zeroRowPolynomial_X {r n : ℕ}
    (i : Fin (r + 1)) (j : Fin n) :
    zeroRowPolynomial (r := r) n (MvPolynomial.X (variableIndex i j)) =
      MvPolynomial.X (variableIndex (r := r + 1) i.castSucc j) := by
  simp only [zeroRowPolynomial, MvPolynomial.rename_X, zeroRowVariableIndex_variableIndex]


-- @@ L7403-7410 verbatim
@[simp] theorem pderiv_zeroRowPolynomial_castSucc {r n : ℕ}
    (i : Fin (r + 1)) (j : Fin n) (p : PolynomialSpace r n) :
    MvPolynomial.pderiv (variableIndex (r := r + 1) i.castSucc j)
        (zeroRowPolynomial n p) =
      zeroRowPolynomial n (MvPolynomial.pderiv (variableIndex i j) p) := by
  simpa only [zeroRowPolynomial, zeroRowVariableIndex_variableIndex] using
    MvPolynomial.pderiv_rename (zeroRowVariableIndex_injective (r := r) (n := n)) (variableIndex
      i j) p


-- @@ L7412-7427 verbatim
@[simp] theorem pderiv_zeroRowPolynomial_lastRow {r n : ℕ}
    (j : Fin n) (p : PolynomialSpace r n) :
    MvPolynomial.pderiv
        (variableIndex (r := r + 1) (Fin.last (r + 1)) j)
        (zeroRowPolynomial n p) = 0 := by
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  intro hmem
  obtain ⟨a, _, ha⟩ :=
    MvPolynomial.mem_vars_rename
      (zeroRowVariableIndex (r := r) (n := n)) p hmem
  have hpair :
      ((finProdFinEquiv.symm a).1.castSucc,
        (finProdFinEquiv.symm a).2) =
        (Fin.last (r + 1), j) :=
    variableIndex_injective (r := r + 1) (n := n) ha
  exact Fin.castSucc_ne_last _ (congrArg Prod.fst hpair)


-- @@ L7429-7437 verbatim
theorem rowEuler_zeroRowPolynomial_castSucc {r n : ℕ}
    (i : Fin (r + 1)) (p : PolynomialSpace r n) :
    rowEuler (r + 1) n i.castSucc (zeroRowPolynomial n p) =
      zeroRowPolynomial n (rowEuler r n i p) := by
  rw [rowEuler_apply, rowEuler_apply, map_sum]
  simp_rw [pderiv_zeroRowPolynomial_castSucc]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul, zeroRowPolynomial_X]


-- @@ L7439-7444 verbatim
theorem traceOperator_zeroRowPolynomial_castSucc {r n : ℕ}
    (i j : Fin (r + 1)) (p : PolynomialSpace r n) :
    traceOperator (r + 1) n i.castSucc j.castSucc
        (zeroRowPolynomial n p) =
      zeroRowPolynomial n (traceOperator r n i j p) := by
  simp only [traceOperator_apply, pderiv_zeroRowPolynomial_castSucc, map_sum]


-- @@ L7446-7450 verbatim
theorem traceOperator_zeroRowPolynomial_last_right {r n : ℕ}
    (i : Fin (r + 2)) (p : PolynomialSpace r n) :
    traceOperator (r + 1) n i (Fin.last (r + 1))
      (zeroRowPolynomial n p) = 0 := by
  simp only [traceOperator_apply, pderiv_zeroRowPolynomial_lastRow, map_zero, Finset.sum_const_zero]


-- @@ L7452-7457 verbatim
theorem traceOperator_zeroRowPolynomial_last_left {r n : ℕ}
    (i : Fin (r + 2)) (p : PolynomialSpace r n) :
    traceOperator (r + 1) n (Fin.last (r + 1)) i
      (zeroRowPolynomial n p) = 0 := by
  rw [traceOperator_comm]
  exact traceOperator_zeroRowPolynomial_last_right i p


-- @@ L7459-7468 verbatim
theorem polarization_zeroRowPolynomial_castSucc {r n : ℕ}
    (i j : Fin (r + 1)) (p : PolynomialSpace r n) :
    polarization (r + 1) n i.castSucc j.castSucc
        (zeroRowPolynomial n p) =
      zeroRowPolynomial n (polarization r n i j p) := by
  rw [polarization_apply, polarization_apply, map_sum]
  simp_rw [pderiv_zeroRowPolynomial_castSucc]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_mul, zeroRowPolynomial_X]


-- @@ L7470-7506 verbatim
theorem zeroRowPolynomial_mem_harmonicYoung {r n : ℕ}
    (mu : Fin (r + 1) → ℕ) (p : PolynomialSpace r n)
    (hp : p ∈ harmonicYoungSubmodule (n := n) mu) :
    zeroRowPolynomial n p ∈
      harmonicYoungSubmodule (n := n) (appendZeroWeight mu) := by
  rw [mem_harmonicYoungSubmodule] at hp ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sum_appendZeroWeight]
    exact hp.1.rename_isHomogeneous
  · intro i
    induction i using Fin.lastCases with
    | last => simp only [rowEuler_apply, pderiv_zeroRowPolynomial_lastRow, mul_zero,
                Finset.sum_const_zero, appendZeroWeight_last, CharP.cast_eq_zero, zero_smul]
    | cast i =>
        rw [rowEuler_zeroRowPolynomial_castSucc, hp.2.1 i]
        simp only [map_smul, appendZeroWeight_castSucc]
  · intro i j
    induction i using Fin.lastCases with
    | last => exact traceOperator_zeroRowPolynomial_last_left j p
    | cast i =>
        induction j using Fin.lastCases with
        | last => exact traceOperator_zeroRowPolynomial_last_right i.castSucc p
        | cast j =>
            rw [traceOperator_zeroRowPolynomial_castSucc,
              hp.2.2.1 i j, map_zero]
  · intro i j hij
    induction i using Fin.lastCases with
    | last =>
        exact (not_lt_of_ge (Fin.le_last j) hij).elim
    | cast i =>
        induction j using Fin.lastCases with
        | last => simp only [polarization_apply, pderiv_zeroRowPolynomial_lastRow, mul_zero,
                    Finset.sum_const_zero]
        | cast j =>
            have hij' : i < j := by simpa only [Fin.castSucc_lt_castSucc_iff] using hij
            rw [polarization_zeroRowPolynomial_castSucc,
              hp.2.2.2 i j hij', map_zero]


-- @@ L7508-7546 verbatim
theorem zeroRowPolynomial_mem_harmonicYoung_iff {r n : ℕ}
    (mu : Fin (r + 1) → ℕ) (p : PolynomialSpace r n) :
    zeroRowPolynomial n p ∈
        harmonicYoungSubmodule (n := n) (appendZeroWeight mu) ↔
      p ∈ harmonicYoungSubmodule (n := n) mu := by
  constructor
  · intro hp
    rw [mem_harmonicYoungSubmodule] at hp ⊢
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [sum_appendZeroWeight] at hp
      exact
        (MvPolynomial.IsHomogeneous.rename_isHomogeneous_iff
          (zeroRowVariableIndex_injective (r := r) (n := n))).mp hp.1
    · intro i
      apply MvPolynomial.rename_injective
        (zeroRowVariableIndex (r := r) (n := n))
        zeroRowVariableIndex_injective
      change zeroRowPolynomial n (rowEuler r n i p) =
        zeroRowPolynomial n ((mu i : ℝ) • p)
      rw [← rowEuler_zeroRowPolynomial_castSucc,
        hp.2.1 i.castSucc, appendZeroWeight_castSucc, map_smul]
    · intro i j
      apply MvPolynomial.rename_injective
        (zeroRowVariableIndex (r := r) (n := n))
        zeroRowVariableIndex_injective
      change zeroRowPolynomial n (traceOperator r n i j p) =
        zeroRowPolynomial n 0
      rw [← traceOperator_zeroRowPolynomial_castSucc,
        hp.2.2.1 i.castSucc j.castSucc, map_zero]
    · intro i j hij
      apply MvPolynomial.rename_injective
        (zeroRowVariableIndex (r := r) (n := n))
        zeroRowVariableIndex_injective
      change zeroRowPolynomial n (polarization r n i j p) =
        zeroRowPolynomial n 0
      rw [← polarization_zeroRowPolynomial_castSucc,
        hp.2.2.2 i.castSucc j.castSucc (by simpa only [Fin.castSucc_lt_castSucc_iff] using hij),
          map_zero]
  · exact zeroRowPolynomial_mem_harmonicYoung mu p


-- @@ L7548-7565 verbatim
/-- Embed harmonic Young space by appending a zero row weight while retaining the coordinate
dimension. -/
def appendZeroRowEmbedding {r n : ℕ}
    (mu : Fin (r + 1) → ℕ) :
    HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      HarmonicYoungSpace (n := n) (appendZeroWeight mu) where
  toFun (p : HarmonicYoungSpace (n := n) mu) :=
    ⟨zeroRowPolynomial (r := r) n (p : PolynomialSpace r n),
      zeroRowPolynomial_mem_harmonicYoung (r := r) (n := n) mu
        (p : PolynomialSpace r n) p.property⟩
  map_add' p q := by
    apply Subtype.ext
    exact map_add (zeroRowPolynomial n)
      (p : PolynomialSpace r n) (q : PolynomialSpace r n)
  map_smul' c p := by
    apply Subtype.ext
    exact map_smul (zeroRowPolynomial n) c
      (p : PolynomialSpace r n)


-- @@ L7567-7597 verbatim
theorem vars_appendZeroYoung_subset_range {r n : ℕ}
    (mu : Fin (r + 1) → ℕ)
    (p : HarmonicYoungSpace (n := n) (appendZeroWeight mu)) :
    (↑(p : PolynomialSpace (r + 1) n).vars :
      Set (Fin ((r + 2) * n))) ⊆
        Set.range (zeroRowVariableIndex (r := r) (n := n)) := by
  intro a ha
  let z := (finProdFinEquiv (m := r + 2) (n := n)).symm a
  have hindex : variableIndex z.1 z.2 = a := by
    exact (finProdFinEquiv (m := r + 2) (n := n)).apply_symm_apply a
  have hrow : z.1 ≠ Fin.last (r + 1) := by
    intro hlast
    obtain ⟨d, hd, hda⟩ :=
      (MvPolynomial.mem_vars_iff_mem_support a).mp ha
    have hcoeff : (p : PolynomialSpace (r + 1) n).coeff d ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hd
    have hdegree :=
      harmonicYoung_rowExponent_degree (appendZeroWeight mu) p d hcoeff
        (Fin.last (r + 1))
    have hzero : rowExponent d (Fin.last (r + 1)) = 0 :=
      (Finsupp.degree_eq_zero_iff _).mp (by simpa only [appendZeroWeight_last] using hdegree)
    have hatcoord :=
      congrArg (fun e : Fin n →₀ ℕ => e z.2) hzero
    apply (Finsupp.mem_support_iff.mp hda)
    calc
      d a = d (variableIndex z.1 z.2) := congrArg d hindex.symm
      _ = d (variableIndex (Fin.last (r + 1)) z.2) := by rw [hlast]
      _ = 0 := by simpa only [rowExponent_apply, Finsupp.coe_zero, Pi.zero_apply] using hatcoord
  obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.mpr hrow
  refine ⟨variableIndex i z.2, ?_⟩
  rw [zeroRowVariableIndex_variableIndex, hi, hindex]


-- @@ L7599-7616 verbatim
theorem appendZeroRowEmbedding_surjective {r n : ℕ}
    (mu : Fin (r + 1) → ℕ) :
    Function.Surjective (appendZeroRowEmbedding (n := n) mu) := by
  intro p
  obtain ⟨q, hq⟩ :=
    MvPolynomial.exists_rename_eq_of_vars_subset_range
      (p : PolynomialSpace (r + 1) n)
      (zeroRowVariableIndex (r := r) (n := n))
      zeroRowVariableIndex_injective
      (vars_appendZeroYoung_subset_range mu p)
  have hq' : zeroRowPolynomial n q =
      (p : PolynomialSpace (r + 1) n) := hq
  have hyoung : q ∈ harmonicYoungSubmodule (n := n) mu :=
    (zeroRowPolynomial_mem_harmonicYoung_iff mu q).mp
      (by rw [hq']; exact p.property)
  refine ⟨⟨q, hyoung⟩, ?_⟩
  apply Subtype.ext
  exact hq'


-- @@ L7618-7639 verbatim
/-- The embedding that appends a zero row weight, bundled as a linear isometry. -/
def appendZeroRowIsometry {r n : ℕ}
    (mu : Fin (r + 1) → ℕ) :
    HarmonicYoungSpace (n := n) mu →ₗᵢ[ℝ]
      HarmonicYoungSpace (n := n) (appendZeroWeight mu) :=
  (appendZeroRowEmbedding mu).isometryOfInner (by
    intro p q
    calc
      ⟪appendZeroRowEmbedding mu p,
        appendZeroRowEmbedding mu q⟫_ℝ =
          SpherePacking.Fischer.polynomialInner ((r + 2) * n)
            (zeroRowPolynomial n (p : PolynomialSpace r n))
            (zeroRowPolynomial n (q : PolynomialSpace r n)) :=
        young_inner_eq_polynomialInner (appendZeroWeight mu)
          (appendZeroRowEmbedding mu p) (appendZeroRowEmbedding mu q)
      _ = SpherePacking.Fischer.polynomialInner ((r + 1) * n)
            (p : PolynomialSpace r n) (q : PolynomialSpace r n) :=
        MetricCodes.Spherical.HigherYoungBranchingFibres.polynomialInner_rename_injective
          (zeroRowVariableIndex (r := r) (n := n))
          zeroRowVariableIndex_injective
          (p : PolynomialSpace r n) (q : PolynomialSpace r n)
      _ = ⟪p, q⟫_ℝ := (young_inner_eq_polynomialInner mu p q).symm)


-- @@ L7641-7647 verbatim
/-- The append zero row isometry equiv used in the spherical-code argument. -/
def appendZeroRowIsometryEquiv {r n : ℕ}
    (mu : Fin (r + 1) → ℕ) :
    HarmonicYoungSpace (n := n) mu ≃ₗᵢ[ℝ]
      HarmonicYoungSpace (n := n) (appendZeroWeight mu) :=
  LinearIsometryEquiv.ofSurjective (appendZeroRowIsometry mu)
    (appendZeroRowEmbedding_surjective mu)


-- @@ L7649-7654 verbatim
theorem finrank_harmonicYoung_appendZero_eq {r n : ℕ}
    (mu : Fin (r + 1) → ℕ) :
    Module.finrank ℝ
        (HarmonicYoungSpace (n := n) (appendZeroWeight mu)) =
      Module.finrank ℝ (HarmonicYoungSpace (n := n) mu) :=
  (appendZeroRowIsometryEquiv (n := n) mu).toLinearEquiv.finrank_eq.symm


-- @@ L7656-7656 verbatim
end ThreeRowYoungBranching


-- @@ L7658-7658 verbatim
end


-- @@ L7660-7660 verbatim
namespace HigherHarmonicYoung


-- @@ L7662-7662 verbatim
section



-- @@ L7665-7665 verbatim
open scoped BigOperators InnerProductSpace


-- @@ L7667-7667 verbatim
namespace ArbitraryRankBranching


-- @@ L7669-7669 verbatim
open MetricCodes.Spherical.HigherRepresentationGraph

-- @@ L7670-7670 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension

-- @@ L7671-7671 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors

-- @@ L7672-7672 verbatim
open MetricCodes.Spherical.ThreeRowYoungBranching


-- @@ L7674-7679 verbatim
theorem appendZeroWeight_eq_snoc {r : ℕ}
    (mu : Fin (r + 1) → ℕ) :
    appendZeroWeight mu = Fin.snoc mu 0 := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp [appendZeroWeight]


-- @@ L7681-7686 verbatim
theorem fullBranchOfInterlaces_signature_eq_appendZeroWeight
    {r : ℕ} {lam : Fin (r + 2) → ℕ}
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu) :
    fullBranchSignature (fullBranchOfInterlaces mu h) =
      appendZeroWeight mu := by
  rw [fullBranchOfInterlaces_signature, appendZeroWeight_eq_snoc]


-- @@ L7688-7693 verbatim
/-- The terminal zero selected branch isometry used in the spherical-code argument. -/
def terminalZeroSelectedBranchIsometry {r n : ℕ}
    (mu : Fin (r + 1) → ℕ) :
    HarmonicYoungSpace (n := n) mu →ₗᵢ[ℝ]
      HarmonicYoungSpace (n := n + 1) (appendZeroWeight mu) :=
  appendZeroYoungIsometry mu


-- @@ L7695-7700 verbatim
theorem interlaces_antitone_stabilizer {r : ℕ}
    {lam : Fin (r + 2) → ℕ} {mu : Fin (r + 1) → ℕ}
    (h : Interlaces lam mu) : Antitone mu := by
  apply Fin.antitone_iff_succ_le.mpr
  intro i
  exact (h i.succ).1.trans (h i.castSucc).2


-- @@ L7702-7708 verbatim
theorem finrank_selectedStabilizer_pos {r n : ℕ}
    {lam : Fin (r + 2) → ℕ} (mu : Fin (r + 1) → ℕ)
    (h : Interlaces lam mu) (hn : 2 * (r + 1) ≤ n - 1) :
    0 < Module.finrank ℝ
      (HarmonicYoungSpace (n := n - 1) mu) :=
  finrank_harmonicYoung_pos_of_antitone hn mu
    (interlaces_antitone_stabilizer h)


-- @@ L7710-7710 verbatim
end ArbitraryRankBranching


-- @@ L7712-7712 verbatim
end


-- @@ L7714-7714 verbatim
section



-- @@ L7717-7717 verbatim
open scoped BigOperators InnerProductSpace TensorProduct


-- @@ L7719-7745 verbatim
theorem projectedCoordinateLower_axis_add {r n : ℕ}
    (mu lam : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, lam i) = (∑ i, mu i) + 1)
    (row : Fin (r + 1)) (v w : SpherePacking.Euclidean n)
    (p : HarmonicYoungSpace (n := n) lam) :
    projectedCoordinateLower mu lam hdeg row (v + w) p =
      projectedCoordinateLower mu lam hdeg row v p +
        projectedCoordinateLower mu lam hdeg row w p := by
  unfold projectedCoordinateLower
  change
    youngHomogeneousProjection mu
      (rowDirectionalHomogeneous mu lam hdeg row (v + w) p) =
        youngHomogeneousProjection mu
          (rowDirectionalHomogeneous mu lam hdeg row v p) +
        youngHomogeneousProjection mu
          (rowDirectionalHomogeneous mu lam hdeg row w p)
  rw [← map_add]
  congr 1
  apply Subtype.ext
  change
    rowDirectionalDerivative r n row (v + w)
        (p : PolynomialSpace r n) =
      rowDirectionalDerivative r n row v
        (p : PolynomialSpace r n) +
        rowDirectionalDerivative r n row w
          (p : PolynomialSpace r n)
  simp only [rowDirectionalDerivative_apply, PiLp.add_apply, add_smul, Finset.sum_add_distrib]


-- @@ L7747-7769 verbatim
theorem projectedCoordinateLower_axis_smul {r n : ℕ}
    (mu lam : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, lam i) = (∑ i, mu i) + 1)
    (row : Fin (r + 1)) (c : ℝ) (v : SpherePacking.Euclidean n)
    (p : HarmonicYoungSpace (n := n) lam) :
    projectedCoordinateLower mu lam hdeg row (c • v) p =
      c • projectedCoordinateLower mu lam hdeg row v p := by
  unfold projectedCoordinateLower
  change
    youngHomogeneousProjection mu
      (rowDirectionalHomogeneous mu lam hdeg row (c • v) p) =
        c • youngHomogeneousProjection mu
          (rowDirectionalHomogeneous mu lam hdeg row v p)
  rw [← map_smul]
  congr 1
  apply Subtype.ext
  change
    rowDirectionalDerivative r n row (c • v)
        (p : PolynomialSpace r n) =
      c • rowDirectionalDerivative r n row v
        (p : PolynomialSpace r n)
  simp only [rowDirectionalDerivative_apply, PiLp.smul_apply, smul_eq_mul, Finset.smul_sum,
    smul_smul]


-- @@ L7771-7781 verbatim
/-- The projected coordinate lower axis used in the spherical-code argument. -/
def projectedCoordinateLowerAxis {r n : ℕ}
    (mu lam : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, lam i) = (∑ i, mu i) + 1)
    (row : Fin (r + 1))
    (p : HarmonicYoungSpace (n := n) lam) :
    SpherePacking.Euclidean n →ₗ[ℝ]
      HarmonicYoungSpace (n := n) mu where
  toFun v := projectedCoordinateLower mu lam hdeg row v p
  map_add' v w := projectedCoordinateLower_axis_add mu lam hdeg row v w p
  map_smul' c v := projectedCoordinateLower_axis_smul mu lam hdeg row c v p


-- @@ L7783-7809 verbatim
theorem projectedCoordinateRaise_axis_add {r n : ℕ}
    (mu lam : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, mu i) = (∑ i, lam i) + 1)
    (row : Fin (r + 1)) (v w : SpherePacking.Euclidean n)
    (p : HarmonicYoungSpace (n := n) lam) :
    projectedCoordinateRaise mu lam hdeg row (v + w) p =
      projectedCoordinateRaise mu lam hdeg row v p +
        projectedCoordinateRaise mu lam hdeg row w p := by
  apply ext_inner_right ℝ
  intro q
  calc
    ⟪projectedCoordinateRaise mu lam hdeg row (v + w) p, q⟫_ℝ =
        ⟪p, projectedCoordinateLower lam mu hdeg row (v + w) q⟫_ℝ :=
      projectedCoordinateRaise_inner mu lam hdeg row (v + w) p q
    _ = ⟪p, projectedCoordinateLower lam mu hdeg row v q +
          projectedCoordinateLower lam mu hdeg row w q⟫_ℝ := by
      rw [projectedCoordinateLower_axis_add]
    _ = ⟪p, projectedCoordinateLower lam mu hdeg row v q⟫_ℝ +
          ⟪p, projectedCoordinateLower lam mu hdeg row w q⟫_ℝ :=
      inner_add_right _ _ _
    _ = ⟪projectedCoordinateRaise mu lam hdeg row v p, q⟫_ℝ +
          ⟪projectedCoordinateRaise mu lam hdeg row w p, q⟫_ℝ := by
      rw [projectedCoordinateRaise_inner mu lam hdeg row v p q,
        projectedCoordinateRaise_inner mu lam hdeg row w p q]
    _ = ⟪projectedCoordinateRaise mu lam hdeg row v p +
          projectedCoordinateRaise mu lam hdeg row w p, q⟫_ℝ :=
      (inner_add_left _ _ _).symm


-- @@ L7811-7831 verbatim
theorem projectedCoordinateRaise_axis_smul {r n : ℕ}
    (mu lam : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, mu i) = (∑ i, lam i) + 1)
    (row : Fin (r + 1)) (c : ℝ) (v : SpherePacking.Euclidean n)
    (p : HarmonicYoungSpace (n := n) lam) :
    projectedCoordinateRaise mu lam hdeg row (c • v) p =
      c • projectedCoordinateRaise mu lam hdeg row v p := by
  apply ext_inner_right ℝ
  intro q
  calc
    ⟪projectedCoordinateRaise mu lam hdeg row (c • v) p, q⟫_ℝ =
        ⟪p, projectedCoordinateLower lam mu hdeg row (c • v) q⟫_ℝ :=
      projectedCoordinateRaise_inner mu lam hdeg row (c • v) p q
    _ = ⟪p, c • projectedCoordinateLower lam mu hdeg row v q⟫_ℝ := by
      rw [projectedCoordinateLower_axis_smul]
    _ = c * ⟪p, projectedCoordinateLower lam mu hdeg row v q⟫_ℝ :=
      real_inner_smul_right _ _ _
    _ = c * ⟪projectedCoordinateRaise mu lam hdeg row v p, q⟫_ℝ := by
      rw [projectedCoordinateRaise_inner mu lam hdeg row v p q]
    _ = ⟪c • projectedCoordinateRaise mu lam hdeg row v p, q⟫_ℝ :=
      (real_inner_smul_left _ _ _).symm


-- @@ L7833-7843 verbatim
/-- The projected coordinate raise axis used in the spherical-code argument. -/
def projectedCoordinateRaiseAxis {r n : ℕ}
    (mu lam : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, mu i) = (∑ i, lam i) + 1)
    (row : Fin (r + 1))
    (p : HarmonicYoungSpace (n := n) lam) :
    SpherePacking.Euclidean n →ₗ[ℝ]
      HarmonicYoungSpace (n := n) mu where
  toFun v := projectedCoordinateRaise mu lam hdeg row v p
  map_add' v w := projectedCoordinateRaise_axis_add mu lam hdeg row v w p
  map_smul' c v := projectedCoordinateRaise_axis_smul mu lam hdeg row c v p


-- @@ L7845-7862 verbatim
/-- The young clebsch raise used in the spherical-code argument. -/
def youngClebschRaise {r n : ℕ}
    (mu lam : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, mu i) = (∑ i, lam i) + 1)
    (row : Fin (r + 1)) :
    HarmonicYoungSpace (n := n) lam →ₗ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) mu) where
  toFun p := ∑ j : Fin n,
    (EuclideanSpace.basisFun (Fin n) ℝ j) ⊗ₜ[ℝ]
      projectedCoordinateRaise mu lam hdeg row
        (EuclideanSpace.basisFun (Fin n) ℝ j) p
  map_add' p q := by
    simp only [EuclideanSpace.basisFun_apply, map_add, TensorProduct.tmul_add,
      Finset.sum_add_distrib]
  map_smul' c p := by
    simp only [EuclideanSpace.basisFun_apply, map_smul, TensorProduct.tmul_smul, Real.ringHom_apply,
      Finset.smul_sum]


-- @@ L7864-7873 verbatim
@[simp] theorem youngClebschRaise_apply {r n : ℕ}
    (mu lam : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, mu i) = (∑ i, lam i) + 1)
    (row : Fin (r + 1))
    (p : HarmonicYoungSpace (n := n) lam) :
    youngClebschRaise mu lam hdeg row p =
      ∑ j : Fin n,
        (EuclideanSpace.basisFun (Fin n) ℝ j) ⊗ₜ[ℝ]
          projectedCoordinateRaise mu lam hdeg row
            (EuclideanSpace.basisFun (Fin n) ℝ j) p := rfl


-- @@ L7875-7892 verbatim
/-- The young clebsch lower used in the spherical-code argument. -/
def youngClebschLower {r n : ℕ}
    (mu lam : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, lam i) = (∑ i, mu i) + 1)
    (row : Fin (r + 1)) :
    HarmonicYoungSpace (n := n) lam →ₗ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) mu) where
  toFun p := ∑ j : Fin n,
    (EuclideanSpace.basisFun (Fin n) ℝ j) ⊗ₜ[ℝ]
      projectedCoordinateLower mu lam hdeg row
        (EuclideanSpace.basisFun (Fin n) ℝ j) p
  map_add' p q := by
    simp only [EuclideanSpace.basisFun_apply, map_add, TensorProduct.tmul_add,
      Finset.sum_add_distrib]
  map_smul' c p := by
    simp only [EuclideanSpace.basisFun_apply, map_smul, TensorProduct.tmul_smul, Real.ringHom_apply,
      Finset.smul_sum]


-- @@ L7894-7903 verbatim
@[simp] theorem youngClebschLower_apply {r n : ℕ}
    (mu lam : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, lam i) = (∑ i, mu i) + 1)
    (row : Fin (r + 1))
    (p : HarmonicYoungSpace (n := n) lam) :
    youngClebschLower mu lam hdeg row p =
      ∑ j : Fin n,
        (EuclideanSpace.basisFun (Fin n) ℝ j) ⊗ₜ[ℝ]
          projectedCoordinateLower mu lam hdeg row
            (EuclideanSpace.basisFun (Fin n) ℝ j) p := rfl


-- @@ L7905-7922 verbatim
theorem youngClebschLower_inner {r n : ℕ}
    (mu lam : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, lam i) = (∑ i, mu i) + 1)
    (row : Fin (r + 1))
    (p q : HarmonicYoungSpace (n := n) lam) :
    ⟪youngClebschLower mu lam hdeg row p,
      youngClebschLower mu lam hdeg row q⟫_ℝ =
      ∑ j : Fin n,
        ⟪projectedCoordinateLower mu lam hdeg row
            (EuclideanSpace.basisFun (Fin n) ℝ j) p,
          projectedCoordinateLower mu lam hdeg row
            (EuclideanSpace.basisFun (Fin n) ℝ j) q⟫_ℝ := by
  simp only [youngClebschLower_apply, sum_inner, inner_sum,
    TensorProduct.inner_tmul,
    (EuclideanSpace.basisFun (Fin n) ℝ).inner_eq_ite,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  rfl


-- @@ L7924-7940 verbatim
theorem youngClebschRaise_inner_basis_tmul {r n : ℕ}
    (mu lam : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, mu i) = (∑ i, lam i) + 1)
    (row : Fin (r + 1)) (j : Fin n)
    (p : HarmonicYoungSpace (n := n) lam)
    (q : HarmonicYoungSpace (n := n) mu) :
    ⟪youngClebschRaise mu lam hdeg row p,
      (EuclideanSpace.basisFun (Fin n) ℝ j) ⊗ₜ[ℝ] q⟫_ℝ =
      ⟪p, projectedCoordinateLower lam mu hdeg row
        (EuclideanSpace.basisFun (Fin n) ℝ j) q⟫_ℝ := by
  simp only [youngClebschRaise_apply, sum_inner,
    TensorProduct.inner_tmul,
    (EuclideanSpace.basisFun (Fin n) ℝ).inner_eq_ite,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  exact projectedCoordinateRaise_inner mu lam hdeg row
    (EuclideanSpace.basisFun (Fin n) ℝ j) p q


-- @@ L7942-7954 verbatim
theorem youngClebschRaise_adjoint_basis_tmul {r n : ℕ}
    (mu lam : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, mu i) = (∑ i, lam i) + 1)
    (row : Fin (r + 1)) (j : Fin n)
    (q : HarmonicYoungSpace (n := n) mu) :
    (youngClebschRaise mu lam hdeg row).adjoint
        ((EuclideanSpace.basisFun (Fin n) ℝ j) ⊗ₜ[ℝ] q) =
      projectedCoordinateLower lam mu hdeg row
        (EuclideanSpace.basisFun (Fin n) ℝ j) q := by
  apply ext_inner_left ℝ
  intro p
  rw [LinearMap.adjoint_inner_right]
  exact youngClebschRaise_inner_basis_tmul mu lam hdeg row j p q


-- @@ L7956-7991 verbatim
theorem youngClebschRaise_adjoint_tmul {r n : ℕ}
    (mu lam : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, mu i) = (∑ i, lam i) + 1)
    (row : Fin (r + 1))
    (v : SpherePacking.Euclidean n)
    (q : HarmonicYoungSpace (n := n) mu) :
    (youngClebschRaise mu lam hdeg row).adjoint
        (v ⊗ₜ[ℝ] q) =
      projectedCoordinateLower lam mu hdeg row v q := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hv : (∑ j : Fin n, v j • b j) = v := by
    simpa [b] using b.sum_repr v
  calc
    (youngClebschRaise mu lam hdeg row).adjoint (v ⊗ₜ[ℝ] q) =
        (youngClebschRaise mu lam hdeg row).adjoint
          ((∑ j : Fin n, v j • b j) ⊗ₜ[ℝ] q) := by rw [hv]
    _ = ∑ j : Fin n,
        v j • (youngClebschRaise mu lam hdeg row).adjoint
          (b j ⊗ₜ[ℝ] q) := by
      rw [TensorProduct.sum_tmul, map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [← TensorProduct.smul_tmul', map_smul]
    _ = ∑ j : Fin n,
        v j • projectedCoordinateLower lam mu hdeg row (b j) q := by
      apply Finset.sum_congr rfl
      intro j _
      rw [youngClebschRaise_adjoint_basis_tmul]
    _ = projectedCoordinateLowerAxis lam mu hdeg row q
          (∑ j : Fin n, v j • b j) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_smul]
      rfl
    _ = projectedCoordinateLower lam mu hdeg row v q := by rw [hv]; rfl


-- @@ L7993-8022 verbatim
theorem youngClebschLower_adjoint_basis_tmul {r n : ℕ}
    (mu lam : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, lam i) = (∑ i, mu i) + 1)
    (row : Fin (r + 1)) (j : Fin n)
    (q : HarmonicYoungSpace (n := n) mu) :
    (youngClebschLower mu lam hdeg row).adjoint
        ((EuclideanSpace.basisFun (Fin n) ℝ j) ⊗ₜ[ℝ] q) =
      projectedCoordinateRaise lam mu hdeg row
        (EuclideanSpace.basisFun (Fin n) ℝ j) q := by
  apply ext_inner_left ℝ
  intro p
  rw [LinearMap.adjoint_inner_right]
  simp only [youngClebschLower_apply, sum_inner,
    TensorProduct.inner_tmul,
    (EuclideanSpace.basisFun (Fin n) ℝ).inner_eq_ite,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  calc
    ⟪projectedCoordinateLower mu lam hdeg row
        (EuclideanSpace.basisFun (Fin n) ℝ j) p, q⟫_ℝ =
        ⟪q, projectedCoordinateLower mu lam hdeg row
          (EuclideanSpace.basisFun (Fin n) ℝ j) p⟫_ℝ :=
      real_inner_comm _ _
    _ = ⟪projectedCoordinateRaise lam mu hdeg row
          (EuclideanSpace.basisFun (Fin n) ℝ j) q, p⟫_ℝ :=
      (projectedCoordinateRaise_inner lam mu hdeg row
        (EuclideanSpace.basisFun (Fin n) ℝ j) q p).symm
    _ = ⟪p, projectedCoordinateRaise lam mu hdeg row
          (EuclideanSpace.basisFun (Fin n) ℝ j) q⟫_ℝ :=
      real_inner_comm _ _


-- @@ L8024-8043 verbatim
theorem youngClebschRaise_adjoint_comp_self {r n : ℕ}
    (mu lam : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, mu i) = (∑ i, lam i) + 1)
    (row : Fin (r + 1)) :
    (youngClebschRaise mu lam hdeg row).adjoint.comp
        (youngClebschRaise mu lam hdeg row) =
      ∑ j : Fin n,
        (projectedCoordinateLower lam mu hdeg row
          (EuclideanSpace.basisFun (Fin n) ℝ j)).comp
            (projectedCoordinateRaise mu lam hdeg row
              (EuclideanSpace.basisFun (Fin n) ℝ j)) := by
  apply LinearMap.ext
  intro p
  simp only [LinearMap.comp_apply, youngClebschRaise_apply,
    map_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact youngClebschRaise_adjoint_basis_tmul mu lam hdeg row j
    (projectedCoordinateRaise mu lam hdeg row
      (EuclideanSpace.basisFun (Fin n) ℝ j) p)


-- @@ L8045-8064 verbatim
theorem youngClebschLower_adjoint_comp_self {r n : ℕ}
    (mu lam : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, lam i) = (∑ i, mu i) + 1)
    (row : Fin (r + 1)) :
    (youngClebschLower mu lam hdeg row).adjoint.comp
        (youngClebschLower mu lam hdeg row) =
      ∑ j : Fin n,
        (projectedCoordinateRaise lam mu hdeg row
          (EuclideanSpace.basisFun (Fin n) ℝ j)).comp
            (projectedCoordinateLower mu lam hdeg row
              (EuclideanSpace.basisFun (Fin n) ℝ j)) := by
  apply LinearMap.ext
  intro p
  simp only [LinearMap.comp_apply, youngClebschLower_apply,
    map_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact youngClebschLower_adjoint_basis_tmul mu lam hdeg row j
    (projectedCoordinateLower mu lam hdeg row
      (EuclideanSpace.basisFun (Fin n) ℝ j) p)


-- @@ L8066-8066 verbatim
namespace FullRankClebsch


-- @@ L8068-8114 verbatim
theorem oppositePolarization_commutator {r n : ℕ}
    (i j : Fin (r + 1)) (p : PolynomialSpace r n) :
    polarization r n i j (polarization r n j i p) +
        rowEuler r n j p =
      polarization r n j i (polarization r n i j p) +
        rowEuler r n i p := by
  classical
  have hcross :
      (∑ k : Fin n,
        MvPolynomial.X (variableIndex i k) *
          polarization r n j i
            (MvPolynomial.pderiv (variableIndex j k) p)) =
        ∑ k : Fin n,
          MvPolynomial.X (variableIndex j k) *
            polarization r n i j
              (MvPolynomial.pderiv (variableIndex i k) p) := by
    simp_rw [polarization_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    rw [SpherePacking.mvPolynomial_pderiv_commute
      (variableIndex i k) (variableIndex j l) p]
    ring
  have hraise :
      polarization r n i j (polarization r n j i p) =
        rowEuler r n i p +
          ∑ k : Fin n,
            MvPolynomial.X (variableIndex i k) *
              polarization r n j i
                (MvPolynomial.pderiv (variableIndex j k) p) := by
    rw [polarization_apply, rowEuler_apply]
    simp_rw [pderiv_polarization_harmonicLift]
    simp only [↓reduceIte, polarization_apply, mul_add, Finset.sum_add_distrib]
  have hlower :
      polarization r n j i (polarization r n i j p) =
        rowEuler r n j p +
          ∑ k : Fin n,
            MvPolynomial.X (variableIndex j k) *
              polarization r n i j
                (MvPolynomial.pderiv (variableIndex i k) p) := by
    rw [polarization_apply, rowEuler_apply]
    simp_rw [pderiv_polarization_harmonicLift]
    simp only [↓reduceIte, polarization_apply, mul_add, Finset.sum_add_distrib]
  rw [hraise, hlower, hcross]
  abel


-- @@ L8116-8116 verbatim
end FullRankClebsch


-- @@ L8118-8118 verbatim
end


-- @@ L8120-8120 verbatim
section



-- @@ L8123-8123 verbatim
open scoped BigOperators


-- @@ L8125-8130 verbatim
/-- The joint harmonic weight submodule used in the spherical-code argument. -/
def jointHarmonicWeightSubmodule {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) :
    Submodule ℝ (youngMultihomogeneousSubmodule n lam) :=
  (traceFreeSubmodule r n).comap
    (youngMultihomogeneousSubmodule n lam).subtype


-- @@ L8132-8135 verbatim
/-- The joint harmonic weight space used in the spherical-code argument. -/
abbrev JointHarmonicWeightSpace {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) :=
  ↥(jointHarmonicWeightSubmodule n lam)


-- @@ L8137-8141 verbatim
@[simp] theorem mem_jointHarmonicWeightSubmodule
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (p : youngMultihomogeneousSubmodule n lam) :
    p ∈ jointHarmonicWeightSubmodule n lam ↔
      (p : PolynomialSpace r n) ∈ traceFreeSubmodule r n := Iff.rfl


-- @@ L8143-8148 verbatim
instance jointHarmonicWeightSpace_finiteDimensional
    {r : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ) :
    FiniteDimensional ℝ (JointHarmonicWeightSpace n lam) := by
  exact FiniteDimensional.of_injective
    (jointHarmonicWeightSubmodule n lam).subtype
    (jointHarmonicWeightSubmodule n lam).subtype_injective


-- @@ L8150-8163 verbatim
/-- Regard a joint harmonic weight polynomial as homogeneous of degree equal to the sum of its
row weights. -/
def jointHarmonicWeightHomogeneousEmbedding {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) :
    JointHarmonicWeightSpace n lam →ₗ[ℝ]
      SpherePacking.Fischer.Homogeneous ((r + 1) * n) (∑ i, lam i) where
  toFun p := ⟨(p.val : PolynomialSpace r n),
    youngMultihomogeneous_isHomogeneous lam p.val⟩
  map_add' p q := by
    apply Subtype.ext
    rfl
  map_smul' c p := by
    apply Subtype.ext
    rfl


-- @@ L8165-8174 verbatim
theorem jointHarmonicWeightHomogeneousEmbedding_injective
    {r : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ) :
    Function.Injective (jointHarmonicWeightHomogeneousEmbedding n lam) := by
  intro p q h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg
    (fun z : SpherePacking.Fischer.Homogeneous
      ((r + 1) * n) (∑ i, lam i) =>
        (z : PolynomialSpace r n)) h


-- @@ L8176-8184 verbatim
/-- The Fischer coefficient embedding of the joint harmonic weight space. -/
def jointHarmonicWeightCoefficientEmbedding {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) :
    JointHarmonicWeightSpace n lam →ₗ[ℝ]
      SpherePacking.Fischer.CoefficientSpace
        ((r + 1) * n) (∑ i, lam i) :=
  (SpherePacking.Fischer.coefficientEmbedding
    ((r + 1) * n) (∑ i, lam i)).comp
      (jointHarmonicWeightHomogeneousEmbedding n lam)


-- @@ L8186-8192 verbatim
theorem jointHarmonicWeightCoefficientEmbedding_injective
    {r : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ) :
    Function.Injective
      (jointHarmonicWeightCoefficientEmbedding n lam) :=
  (SpherePacking.Fischer.coefficientEmbedding_injective
    ((r + 1) * n) (∑ i, lam i)).comp
      (jointHarmonicWeightHomogeneousEmbedding_injective n lam)


-- @@ L8194-8200 verbatim
/-- The joint harmonic weight fischer core used in the spherical-code argument. -/
@[implicit_reducible] def jointHarmonicWeightFischerCore
    {r : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ) :
    InnerProductSpace.Core ℝ (JointHarmonicWeightSpace n lam) :=
  SpherePacking.Fischer.embeddingInnerCore
    (jointHarmonicWeightCoefficientEmbedding n lam)
    (jointHarmonicWeightCoefficientEmbedding_injective n lam)


-- @@ L8202-8217 verbatim
theorem jointHarmonicWeightFischerCore_inner
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (p q : JointHarmonicWeightSpace n lam) :
    (jointHarmonicWeightFischerCore n lam).inner p q =
      SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        (p.val : PolynomialSpace r n)
        (q.val : PolynomialSpace r n) := by
  change
    SpherePacking.Fischer.homogeneousInner
      ((r + 1) * n) (∑ i, lam i)
        (jointHarmonicWeightHomogeneousEmbedding n lam p)
        (jointHarmonicWeightHomogeneousEmbedding n lam q) = _
  exact SpherePacking.Fischer.homogeneousInner_eq_polynomialInner
    ((r + 1) * n) (∑ i, lam i)
    (jointHarmonicWeightHomogeneousEmbedding n lam p)
    (jointHarmonicWeightHomogeneousEmbedding n lam q)


-- @@ L8219-8219 verbatim
end


-- @@ L8221-8221 verbatim
section



-- @@ L8224-8224 verbatim
open scoped BigOperators InnerProductSpace TensorProduct


-- @@ L8226-8239 verbatim
theorem traceOperator_pderiv_comm {r n : ℕ}
    (a b row : Fin (r + 1)) (j : Fin n)
    (p : PolynomialSpace r n) :
    traceOperator r n a b
        (MvPolynomial.pderiv (variableIndex row j) p) =
      MvPolynomial.pderiv (variableIndex row j)
        (traceOperator r n a b p) := by
  rw [traceOperator_apply, traceOperator_apply, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [SpherePacking.mvPolynomial_pderiv_commute
    (variableIndex b k) (variableIndex row j),
    SpherePacking.mvPolynomial_pderiv_commute
      (variableIndex a k) (variableIndex row j)]


-- @@ L8241-8259 verbatim
theorem polarization_pderiv_of_ne {r n : ℕ}
    (a b row : Fin (r + 1)) (j : Fin n)
    (hne : a ≠ row) (p : PolynomialSpace r n) :
    polarization r n a b
        (MvPolynomial.pderiv (variableIndex row j) p) =
      MvPolynomial.pderiv (variableIndex row j)
        (polarization r n a b p) := by
  rw [polarization_apply, polarization_apply, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hindex : variableIndex a k ≠ variableIndex row j := by
    intro h
    have hpair : (a, k) = (row, j) := variableIndex_injective h
    exact hne (congrArg Prod.fst hpair)
  rw [MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_X_of_ne hindex]
  simp only [zero_mul, zero_add]
  rw [SpherePacking.mvPolynomial_pderiv_commute
    (variableIndex b k) (variableIndex row j)]


-- @@ L8261-8268 verbatim
theorem rowEuler_pderiv_of_ne {r n : ℕ}
    (a row : Fin (r + 1)) (j : Fin n)
    (hne : a ≠ row) (p : PolynomialSpace r n) :
    rowEuler r n a (MvPolynomial.pderiv (variableIndex row j) p) =
      MvPolynomial.pderiv (variableIndex row j)
        (rowEuler r n a p) := by
  simpa only [polarization_self] using
    polarization_pderiv_of_ne a a row j hne p


-- @@ L8270-8312 verbatim
theorem rowEuler_pderiv_self {r n : ℕ}
    (row : Fin (r + 1)) (j : Fin n)
    (p : PolynomialSpace r n) :
    rowEuler r n row
        (MvPolynomial.pderiv (variableIndex row j) p) =
      MvPolynomial.pderiv (variableIndex row j)
          (rowEuler r n row p) -
        MvPolynomial.pderiv (variableIndex row j) p := by
  rw [rowEuler_apply, rowEuler_apply, map_sum]
  have hsplit :
      (∑ k : Fin n,
        MvPolynomial.pderiv (variableIndex row j)
          (MvPolynomial.X (variableIndex row k) *
            MvPolynomial.pderiv (variableIndex row k) p)) =
        (∑ k : Fin n,
          MvPolynomial.X (variableIndex row k) *
            MvPolynomial.pderiv (variableIndex row k)
              (MvPolynomial.pderiv (variableIndex row j) p)) +
          MvPolynomial.pderiv (variableIndex row j) p := by
    simp_rw [MvPolynomial.pderiv_mul]
    simp_rw [SpherePacking.mvPolynomial_pderiv_commute
      (variableIndex row j) (variableIndex row _)]
    rw [Finset.sum_add_distrib]
    have hdelta :
        (∑ k : Fin n,
          MvPolynomial.pderiv (variableIndex row j)
              (MvPolynomial.X (variableIndex row k)) *
            MvPolynomial.pderiv (variableIndex row k) p) =
          MvPolynomial.pderiv (variableIndex row j) p := by
      rw [Finset.sum_eq_single j]
      · simp only [MvPolynomial.pderiv_X, Pi.single_eq_same, one_mul]
      · intro k _ hkj
        have hindex : variableIndex row k ≠ variableIndex row j := by
          intro h
          have hpair : (row, k) = (row, j) := variableIndex_injective h
          exact hkj (congrArg Prod.snd hpair)
        rw [MvPolynomial.pderiv_X_of_ne hindex, zero_mul]
      · simp only [Finset.mem_univ, not_true_eq_false, MvPolynomial.pderiv_X, Pi.single_eq_same,
          one_mul, IsEmpty.forall_iff]
    rw [hdelta]
    abel
  rw [hsplit]
  abel


-- @@ L8314-8357 verbatim
theorem rowDerivative_fischer_inner_sum {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (p q : HarmonicYoungSpace (n := n) lam) :
    (∑ j : Fin n,
      SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        (MvPolynomial.pderiv (variableIndex row j)
          (p : PolynomialSpace r n))
        (MvPolynomial.pderiv (variableIndex row j)
          (q : PolynomialSpace r n))) =
      (lam row : ℝ) * ⟪p, q⟫_ℝ := by
  have hp :=
    ((mem_harmonicYoungSubmodule lam
      (p : PolynomialSpace r n)).mp p.property).2.1 row
  calc
    _ = ∑ j : Fin n,
        SpherePacking.Fischer.polynomialInner ((r + 1) * n)
          (MvPolynomial.X (variableIndex row j) *
            MvPolynomial.pderiv (variableIndex row j)
              (p : PolynomialSpace r n))
          (q : PolynomialSpace r n) := by
      apply Finset.sum_congr rfl
      intro j _
      exact
        (SpherePacking.Fischer.polynomialInner_X_mul
          ((r + 1) * n) (variableIndex row j)
          (MvPolynomial.pderiv (variableIndex row j)
            (p : PolynomialSpace r n))
          (q : PolynomialSpace r n)).symm
    _ = SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        (rowEuler r n row (p : PolynomialSpace r n))
        (q : PolynomialSpace r n) := by
      rw [rowEuler_apply]
      simpa only using
        (SpherePacking.Fischer.polynomialInner_sum_left ((r + 1) * n) Finset.univ
            (fun j : Fin n =>
              MvPolynomial.X (variableIndex row j) * MvPolynomial.pderiv (variableIndex row j)
                (p : PolynomialSpace r n))
            (q : PolynomialSpace r n)).symm
    _ = SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        ((lam row : ℝ) • (p : PolynomialSpace r n))
        (q : PolynomialSpace r n) := by rw [hp]
    _ = (lam row : ℝ) * ⟪p, q⟫_ℝ := by
      rw [SpherePacking.Fischer.polynomialInner_smul_left,
        young_inner_eq_polynomialInner]


-- @@ L8359-8377 verbatim
theorem youngClebschRaiseLower_trace {r n : ℕ}
    (mu lam : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, mu i) = (∑ i, lam i) + 1)
    (row : Fin (r + 1)) :
    LinearMap.trace ℝ (HarmonicYoungSpace (n := n) lam)
      ((youngClebschRaise (n := n) mu lam hdeg row).adjoint.comp
        (youngClebschRaise (n := n) mu lam hdeg row)) =
      LinearMap.trace ℝ (HarmonicYoungSpace (n := n) mu)
        ((youngClebschLower (n := n) lam mu hdeg row).adjoint.comp
          (youngClebschLower (n := n) lam mu hdeg row)) := by
  rw [youngClebschRaise_adjoint_comp_self,
    youngClebschLower_adjoint_comp_self, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact (LinearMap.trace_comp_comm'
    (projectedCoordinateLower lam mu hdeg row
      (EuclideanSpace.basisFun (Fin n) ℝ j))
    (projectedCoordinateRaise mu lam hdeg row
      (EuclideanSpace.basisFun (Fin n) ℝ j))).symm


-- @@ L8379-8392 verbatim
/-- The normalized young clebsch raise used in the spherical-code argument. -/
def normalizedYoungClebschRaise {r n : ℕ}
    (mu lam : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, mu i) = (∑ i, lam i) + 1)
    (row : Fin (r + 1)) (c : ℝ) (hc : 0 < c)
    (hgram : ∀ p q : HarmonicYoungSpace (n := n) lam,
      ⟪youngClebschRaise mu lam hdeg row p,
        youngClebschRaise mu lam hdeg row q⟫_ℝ =
          c * ⟪p, q⟫_ℝ) :
    HarmonicYoungSpace (n := n) lam →ₗᵢ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) mu) :=
  SpherePacking.HarmonicCoordinateOperators.normalizedChannelIsometry
    (youngClebschRaise mu lam hdeg row) c hc hgram


-- @@ L8394-8407 verbatim
/-- The normalized young clebsch lower used in the spherical-code argument. -/
def normalizedYoungClebschLower {r n : ℕ}
    (mu lam : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, lam i) = (∑ i, mu i) + 1)
    (row : Fin (r + 1)) (c : ℝ) (hc : 0 < c)
    (hgram : ∀ p q : HarmonicYoungSpace (n := n) lam,
      ⟪youngClebschLower mu lam hdeg row p,
        youngClebschLower mu lam hdeg row q⟫_ℝ =
          c * ⟪p, q⟫_ℝ) :
    HarmonicYoungSpace (n := n) lam →ₗᵢ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) mu) :=
  SpherePacking.HarmonicCoordinateOperators.normalizedChannelIsometry
    (youngClebschLower mu lam hdeg row) c hc hgram


-- @@ L8409-8418 verbatim
@[simp] theorem normalizedYoungClebschRaise_toLinearMap {r n : ℕ}
    (mu lam : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, mu i) = (∑ i, lam i) + 1)
    (row : Fin (r + 1)) (c : ℝ) (hc : 0 < c)
    (hgram : ∀ p q : HarmonicYoungSpace (n := n) lam,
      ⟪youngClebschRaise mu lam hdeg row p,
        youngClebschRaise mu lam hdeg row q⟫_ℝ =
          c * ⟪p, q⟫_ℝ) :
    (normalizedYoungClebschRaise mu lam hdeg row c hc hgram).toLinearMap =
      (Real.sqrt c)⁻¹ • youngClebschRaise mu lam hdeg row := rfl


-- @@ L8420-8429 verbatim
@[simp] theorem normalizedYoungClebschLower_toLinearMap {r n : ℕ}
    (mu lam : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, lam i) = (∑ i, mu i) + 1)
    (row : Fin (r + 1)) (c : ℝ) (hc : 0 < c)
    (hgram : ∀ p q : HarmonicYoungSpace (n := n) lam,
      ⟪youngClebschLower mu lam hdeg row p,
        youngClebschLower mu lam hdeg row q⟫_ℝ =
          c * ⟪p, q⟫_ℝ) :
    (normalizedYoungClebschLower mu lam hdeg row c hc hgram).toLinearMap =
      (Real.sqrt c)⁻¹ • youngClebschLower mu lam hdeg row := rfl


-- @@ L8431-8431 verbatim
end


-- @@ L8433-8433 verbatim
section



-- @@ L8436-8436 verbatim
open scoped BigOperators


-- @@ L8438-8441 verbatim
/-- The young gram radial ideal used in the spherical-code argument. -/
def youngGramRadialIdeal (r n : ℕ) : Ideal (PolynomialSpace r n) :=
  Ideal.span (Set.range fun ij : Fin (r + 1) × Fin (r + 1) =>
    rowPairingPolynomial (n := n) ij.1 ij.2)


-- @@ L8443-8446 verbatim
theorem rowPairingPolynomial_mem_youngGramRadialIdeal {r n : ℕ}
    (i j : Fin (r + 1)) :
    rowPairingPolynomial (n := n) i j ∈ youngGramRadialIdeal r n :=
  Ideal.subset_span ⟨(i, j), rfl⟩


-- @@ L8448-8479 verbatim
theorem polynomialInner_youngGramRadialIdeal_eq_zero_of_traceFree
    {r n : ℕ} (p q : PolynomialSpace r n)
    (hp : ∀ i j : Fin (r + 1), traceOperator r n i j p = 0)
    (hq : q ∈ youngGramRadialIdeal r n) :
    SpherePacking.Fischer.polynomialInner ((r + 1) * n) q p = 0 := by
  classical
  change q ∈ Submodule.span (PolynomialSpace r n)
    (Set.range fun ij : Fin (r + 1) × Fin (r + 1) =>
      rowPairingPolynomial (n := n) ij.1 ij.2) at hq
  have hstrong : ∀ a : PolynomialSpace r n,
      SpherePacking.Fischer.polynomialInner ((r + 1) * n) (a * q) p = 0 := by
    induction hq using Submodule.span_induction with
    | mem g hg =>
        obtain ⟨⟨i, j⟩, rfl⟩ := hg
        intro a
        rw [mul_comm a, polynomialInner_rowPairing_trace i j a p, hp i j]
        simp only [SpherePacking.Fischer.polynomialInner, AddMonoidAlgebra.coeff_zero,
          Finsupp.coe_zero, Pi.zero_apply, mul_zero, Finsupp.sum_fun_zero]
    | zero =>
        intro a
        simp only [SpherePacking.Fischer.polynomialInner, mul_zero, AddMonoidAlgebra.coeff_zero,
          Finsupp.sum_zero_index]
    | add x y hx hy ihx ihy =>
        intro a
        rw [mul_add, SpherePacking.Fischer.polynomialInner_add_left,
          ihx a, ihy a, add_zero]
    | smul a x hx ih =>
        intro b
        change SpherePacking.Fischer.polynomialInner ((r + 1) * n)
          (b * (a * x)) p = 0
        simpa only [mul_assoc] using ih (b * a)
  simpa only [one_mul] using hstrong 1


-- @@ L8481-8486 verbatim
/-- The young gram radial weight submodule used in the spherical-code argument. -/
def youngGramRadialWeightSubmodule {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) :
    Submodule ℝ (youngMultihomogeneousSubmodule n lam) :=
  ((youngGramRadialIdeal r n).restrictScalars ℝ).comap
    (youngMultihomogeneousSubmodule n lam).subtype


-- @@ L8488-8492 verbatim
/-- The young gram radial weight quotient used in the spherical-code argument. -/
abbrev YoungGramRadialWeightQuotient {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) :=
  (youngMultihomogeneousSubmodule n lam) ⧸
    youngGramRadialWeightSubmodule n lam


-- @@ L8494-8507 verbatim
/-- Regard a polynomial of the prescribed row multidegrees as homogeneous of their total degree. -/
def youngMultihomogeneousHomogeneousEmbedding {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) :
    youngMultihomogeneousSubmodule n lam →ₗ[ℝ]
      SpherePacking.Fischer.Homogeneous
        ((r + 1) * n) (∑ i, lam i) where
  toFun p := ⟨(p : PolynomialSpace r n),
    youngMultihomogeneous_isHomogeneous lam p⟩
  map_add' p q := by
    apply Subtype.ext
    rfl
  map_smul' c p := by
    apply Subtype.ext
    rfl


-- @@ L8509-8517 verbatim
theorem youngMultihomogeneousHomogeneousEmbedding_injective
    {r : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ) :
    Function.Injective (youngMultihomogeneousHomogeneousEmbedding n lam) := by
  intro p q hpq
  apply Subtype.ext
  exact congrArg
    (fun z : SpherePacking.Fischer.Homogeneous
      ((r + 1) * n) (∑ i, lam i) =>
        (z : PolynomialSpace r n)) hpq


-- @@ L8519-8527 verbatim
/-- The Fischer coefficient embedding restricted to the prescribed row multidegrees. -/
def youngMultihomogeneousCoefficientEmbedding {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) :
    youngMultihomogeneousSubmodule n lam →ₗ[ℝ]
      SpherePacking.Fischer.CoefficientSpace
        ((r + 1) * n) (∑ i, lam i) :=
  (SpherePacking.Fischer.coefficientEmbedding
    ((r + 1) * n) (∑ i, lam i)).comp
      (youngMultihomogeneousHomogeneousEmbedding n lam)


-- @@ L8529-8535 verbatim
theorem youngMultihomogeneousCoefficientEmbedding_injective
    {r : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ) :
    Function.Injective
      (youngMultihomogeneousCoefficientEmbedding n lam) :=
  (SpherePacking.Fischer.coefficientEmbedding_injective
    ((r + 1) * n) (∑ i, lam i)).comp
      (youngMultihomogeneousHomogeneousEmbedding_injective n lam)


-- @@ L8537-8544 verbatim
/-- The inner product core on row-multihomogeneous polynomials induced by their coefficient
embedding. -/
@[implicit_reducible] def youngMultihomogeneousFischerCore
    {r : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ) :
    InnerProductSpace.Core ℝ (youngMultihomogeneousSubmodule n lam) :=
  SpherePacking.Fischer.embeddingInnerCore
    (youngMultihomogeneousCoefficientEmbedding n lam)
    (youngMultihomogeneousCoefficientEmbedding_injective n lam)


-- @@ L8546-8560 verbatim
theorem youngMultihomogeneousFischerCore_inner
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (p q : youngMultihomogeneousSubmodule n lam) :
    (youngMultihomogeneousFischerCore n lam).inner p q =
      SpherePacking.Fischer.polynomialInner ((r + 1) * n)
        (p : PolynomialSpace r n) (q : PolynomialSpace r n) := by
  change
    SpherePacking.Fischer.homogeneousInner
      ((r + 1) * n) (∑ i, lam i)
        (youngMultihomogeneousHomogeneousEmbedding n lam p)
        (youngMultihomogeneousHomogeneousEmbedding n lam q) = _
  exact SpherePacking.Fischer.homogeneousInner_eq_polynomialInner
    ((r + 1) * n) (∑ i, lam i)
    (youngMultihomogeneousHomogeneousEmbedding n lam p)
    (youngMultihomogeneousHomogeneousEmbedding n lam q)


-- @@ L8562-8571 verbatim
theorem rowEuler_variableIndex_X {r n : ℕ}
    (a i : Fin (r + 1)) (k : Fin n) :
    rowEuler r n a (MvPolynomial.X (variableIndex i k)) =
      if a = i then MvPolynomial.X (variableIndex i k) else 0 := by
  by_cases hai : a = i
  · subst i
    simpa only [polarization_self, ↓reduceIte] using
      polarization_X_euler a a a k
  · simpa only [polarization_self, hai, ↓reduceIte] using
      polarization_X_euler a a i k


-- @@ L8573-8582 verbatim
theorem rowEuler_rowPairingPolynomial {r n : ℕ}
    (a i j : Fin (r + 1)) :
    rowEuler r n a (rowPairingPolynomial (n := n) i j) =
      (if a = i then rowPairingPolynomial (n := n) i j else 0) +
        (if a = j then rowPairingPolynomial (n := n) i j else 0) := by
  classical
  rw [rowPairingPolynomial, map_sum]
  simp_rw [GelfandTsetlin.rowEuler_mul, rowEuler_variableIndex_X]
  by_cases hai : a = i <;> by_cases haj : a = j <;>
    simp [hai, haj, Finset.sum_add_distrib]


-- @@ L8584-8597 verbatim
theorem rowEuler_pderiv_variableIndex {r n : ℕ}
    (a i : Fin (r + 1)) (k : Fin n) (p : PolynomialSpace r n) :
    rowEuler r n a (MvPolynomial.pderiv (variableIndex i k) p) =
      MvPolynomial.pderiv (variableIndex i k) (rowEuler r n a p) -
        if a = i then MvPolynomial.pderiv (variableIndex i k) p else 0 := by
  classical
  by_cases hai : a = i
  · subst i
    simpa only [rowEuler_apply, map_sum, Derivation.leibniz, smul_eq_mul, MvPolynomial.pderiv_X,
      ↓reduceIte] using
      rowEuler_pderiv_self a k p
  · simp only [rowEuler_pderiv_of_ne a i k hai p, rowEuler_apply, map_sum, Derivation.leibniz,
      smul_eq_mul, MvPolynomial.pderiv_X, ne_eq, DeterminantVectors.variableIndex_eq_iff, hai,
      false_and, not_false_eq_true, Pi.single_eq_of_ne, mul_zero, add_zero, ↓reduceIte, sub_zero]


-- @@ L8599-8625 verbatim
theorem rowEuler_traceOperator_commutator {r n : ℕ}
    (a i j : Fin (r + 1)) (p : PolynomialSpace r n) :
    rowEuler r n a (traceOperator r n i j p) =
      traceOperator r n i j (rowEuler r n a p) -
        (if a = i then traceOperator r n i j p else 0) -
        (if a = j then traceOperator r n i j p else 0) := by
  classical
  rw [traceOperator_apply, map_sum, traceOperator_apply]
  simp_rw [rowEuler_pderiv_variableIndex]
  by_cases hai : a = i
  · subst i
    by_cases haj : a = j
    · subst j
      simp only [rowEuler_apply, map_sum, Derivation.leibniz, smul_eq_mul, MvPolynomial.pderiv_X,
        ↓reduceIte, map_sub, map_add, Finset.sum_sub_distrib]
    · simp only [rowEuler_apply, map_sum, Derivation.leibniz, smul_eq_mul, MvPolynomial.pderiv_X,
        ne_eq, DeterminantVectors.variableIndex_eq_iff, haj, false_and, not_false_eq_true,
        Pi.single_eq_of_ne, mul_zero, add_zero, ↓reduceIte, sub_zero, Finset.sum_sub_distrib]
  · by_cases haj : a = j
    · subst j
      simp only [rowEuler_apply, map_sum, Derivation.leibniz, smul_eq_mul, MvPolynomial.pderiv_X,
        ↓reduceIte, map_sub, map_add, ne_eq, DeterminantVectors.variableIndex_eq_iff, hai,
        false_and, not_false_eq_true, Pi.single_eq_of_ne, mul_zero, add_zero, sub_zero,
        Finset.sum_sub_distrib]
    · simp only [rowEuler_apply, map_sum, Derivation.leibniz, smul_eq_mul, MvPolynomial.pderiv_X,
        ne_eq, DeterminantVectors.variableIndex_eq_iff, haj, false_and, not_false_eq_true,
        Pi.single_eq_of_ne, mul_zero, add_zero, ↓reduceIte, sub_zero, hai]


-- @@ L8627-8636 verbatim
theorem rowEuler_rowPairing_mul_trace {r n : ℕ}
    (a i j : Fin (r + 1)) (p : PolynomialSpace r n) :
    rowEuler r n a
        (rowPairingPolynomial (n := n) i j * traceOperator r n i j p) =
      rowPairingPolynomial (n := n) i j *
        traceOperator r n i j (rowEuler r n a p) := by
  classical
  rw [GelfandTsetlin.rowEuler_mul, rowEuler_rowPairingPolynomial,
    rowEuler_traceOperator_commutator]
  split_ifs <;> ring


-- @@ L8638-8649 verbatim
theorem rowPairing_mul_trace_mem_youngMultihomogeneousSubmodule
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (p : youngMultihomogeneousSubmodule n lam)
    (i j : Fin (r + 1)) :
    rowPairingPolynomial (n := n) i j *
        traceOperator r n i j (p : PolynomialSpace r n) ∈
      youngMultihomogeneousSubmodule n lam := by
  rw [mem_youngMultihomogeneousSubmodule_iff_rowEuler]
  intro a
  rw [rowEuler_rowPairing_mul_trace,
    youngMultihomogeneous_rowEuler lam p a, map_smul]
  simp only [traceOperator_apply, Algebra.mul_smul_comm]


-- @@ L8651-8679 verbatim
theorem mem_jointHarmonicWeight_iff_gramOrthogonal
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (p : youngMultihomogeneousSubmodule n lam) :
    p ∈ jointHarmonicWeightSubmodule n lam ↔
      ∀ q : youngMultihomogeneousSubmodule n lam,
        q ∈ youngGramRadialWeightSubmodule n lam →
          (youngMultihomogeneousFischerCore n lam).inner q p = 0 := by
  constructor
  · intro hp q hq
    rw [youngMultihomogeneousFischerCore_inner]
    apply polynomialInner_youngGramRadialIdeal_eq_zero_of_traceFree
    · exact (mem_traceFreeSubmodule _).mp hp
    · exact hq
  · intro hp
    rw [mem_jointHarmonicWeightSubmodule, mem_traceFreeSubmodule]
    intro i j
    apply (SpherePacking.Fischer.polynomialInner_self_eq_zero
      ((r + 1) * n) (traceOperator r n i j (p : PolynomialSpace r n))).mp
    rw [← polynomialInner_rowPairing_trace i j]
    let q : youngMultihomogeneousSubmodule n lam :=
      ⟨rowPairingPolynomial (n := n) i j *
          traceOperator r n i j (p : PolynomialSpace r n),
        rowPairing_mul_trace_mem_youngMultihomogeneousSubmodule
          lam p i j⟩
    have hq : q ∈ youngGramRadialWeightSubmodule n lam :=
      (youngGramRadialIdeal r n).mul_mem_right
        (traceOperator r n i j (p : PolynomialSpace r n))
        (rowPairingPolynomial_mem_youngGramRadialIdeal i j)
    simpa [youngMultihomogeneousFischerCore_inner, q] using hp q hq


-- @@ L8681-8707 verbatim
theorem finrank_jointHarmonicWeight_add_finrank_youngGramRadialWeight
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) :
    Module.finrank ℝ (JointHarmonicWeightSpace n lam) +
        Module.finrank ℝ (youngGramRadialWeightSubmodule n lam) =
      ∏ i : Fin (r + 1), (n + lam i - 1).choose (lam i) := by
  let : InnerProductSpace.Core ℝ
      (youngMultihomogeneousSubmodule n lam) :=
    youngMultihomogeneousFischerCore n lam
  let : NormedAddCommGroup (youngMultihomogeneousSubmodule n lam) :=
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
  let : InnerProductSpace ℝ (youngMultihomogeneousSubmodule n lam) :=
    InnerProductSpace.ofCore
      (inferInstance : PreInnerProductSpace.Core ℝ
        (youngMultihomogeneousSubmodule n lam))
  have horth :
      (youngGramRadialWeightSubmodule n lam)ᗮ =
        jointHarmonicWeightSubmodule n lam := by
    ext p
    rw [Submodule.mem_orthogonal,
      mem_jointHarmonicWeight_iff_gramOrthogonal]
  have h :=
    (youngGramRadialWeightSubmodule n lam).finrank_add_finrank_orthogonal
  rw [horth, finrank_youngMultihomogeneousSubmodule] at h
  change Module.finrank ℝ (youngGramRadialWeightSubmodule n lam) +
      Module.finrank ℝ (JointHarmonicWeightSpace n lam) =
        ∏ i : Fin (r + 1), (n + lam i - 1).choose (lam i) at h
  simpa only [Nat.add_comm] using h


-- @@ L8709-8722 verbatim
theorem finrank_jointHarmonicWeight_eq_finrank_youngGramRadialWeightQuotient
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) :
    Module.finrank ℝ (JointHarmonicWeightSpace n lam) =
      Module.finrank ℝ (YoungGramRadialWeightQuotient n lam) := by
  have horth :=
    finrank_jointHarmonicWeight_add_finrank_youngGramRadialWeight
      (n := n) lam
  have hquot :=
    (youngGramRadialWeightSubmodule n lam).finrank_quotient_add_finrank
  rw [finrank_youngMultihomogeneousSubmodule] at hquot
  change Module.finrank ℝ (YoungGramRadialWeightQuotient n lam) +
      Module.finrank ℝ (youngGramRadialWeightSubmodule n lam) =
        ∏ i : Fin (r + 1), (n + lam i - 1).choose (lam i) at hquot
  omega


-- @@ L8724-8724 verbatim
end


-- @@ L8726-8726 verbatim
end HigherHarmonicYoung


-- @@ L8728-8728 verbatim
end Spherical


-- @@ L8730-8730 verbatim
end MetricCodes


-- @@ L8732-8732 verbatim
end MetricCodesNoncomputable
