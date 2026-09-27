/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import LeanPool.RiemannRochFunctionFields.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real


-- @@ L12-20 verbatim
/-!
# Instance pack for elliptic function fields
For a Weierstrass curve `W : WeierstrassCurve.Affine k` and an abstract fraction field `K`
of `W.CoordinateRing`, this file constructs the coordinate-place hypothesis pack required to
state the place dictionary: the `k[X]`- and `k⟮X⟯`-algebra structures with their scalar towers,
the `{1, y}` basis giving `FunctionField k K` and `[K : k⟮X⟯] = 2`, separability of the
Weierstrass generator in every characteristic, and (over an algebraically closed base)
`IsFullConstantField k K`.
-/


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
open Polynomial


-- @@ L26-26 verbatim
open scoped Polynomial.Bivariate RatFunc nonZeroDivisors


-- @@ L28-28 verbatim
noncomputable section


-- @@ L30-30 verbatim
namespace WeierstrassCurve.Affine


-- @@ L32-32 verbatim
variable {k : Type*} [Field k] (W : WeierstrassCurve.Affine k)


-- @@ L34-34 verbatim
/-! ## Curve-side facts: `W.CoordinateRing` over `k[X]` -/


-- @@ L36-36 verbatim
namespace CoordinateRing


-- @@ L38-39 verbatim
instance : Module.Finite k[X] W.CoordinateRing :=
  Module.Finite.of_basis (CoordinateRing.basis W)


-- @@ L41-45 verbatim
theorem algebraMap_polynomial_injective' :
    Function.Injective (algebraMap k[X] W.CoordinateRing) := by
  rw [AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.of.injective_of_degree_ne_zero
    (by rw [degree_polynomial]; exact (by decide : (2 : WithBot ℕ) ≠ 0))


-- @@ L47-49 verbatim
instance : FaithfulSMul k[X] W.CoordinateRing :=
  (faithfulSMul_iff_algebraMap_injective k[X] W.CoordinateRing).mpr
    (algebraMap_polynomial_injective' W)


-- @@ L51-52 verbatim
instance : Algebra.IsIntegral k[X] W.CoordinateRing :=
  Algebra.IsIntegral.of_finite k[X] W.CoordinateRing


-- @@ L54-54 verbatim
example : Algebra.IsAlgebraic k[X] W.CoordinateRing := inferInstance


-- @@ L56-56 verbatim
end CoordinateRing


-- @@ L58-64 verbatim
/-- The derivative (in `Y`) of the Weierstrass polynomial is `W.polynomialY`. -/
theorem derivative_polynomial :
    derivative W.polynomial = W.polynomialY := by
  rw [polynomial, polynomialY]
  simp only [derivative_sub, derivative_add, derivative_pow, derivative_X, derivative_C,
    derivative_C_mul, mul_one, map_ofNat, map_natCast]
  ring


-- @@ L66-84 verbatim
/-- For an elliptic curve, the partial derivative `W_Y` is nonzero (even in char 2). -/
theorem polynomialY_ne_zero [W.IsElliptic] : W.polynomialY ≠ 0 := by
  intro h
  rw [polynomialY] at h
  have h1 : (C (2 : k) : k[X]) = 0 := by
    simpa using congr_arg (fun p => Polynomial.coeff p 1) h
  have h0 : (C W.a₁ * X + C W.a₃ : k[X]) = 0 := by
    simpa using congr_arg (fun p => Polynomial.coeff p 0) h
  have h2 : (2 : k) = 0 := Polynomial.C_eq_zero.mp h1
  have ha₁ : W.a₁ = 0 := by
    simpa using congr_arg (fun p => Polynomial.coeff p 1) h0
  have ha₃ : W.a₃ = 0 := by
    simpa using congr_arg (fun p => Polynomial.coeff p 0) h0
  have hΔ : W.Δ = 0 := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈, ha₁, ha₃]
    linear_combination (-32 * W.a₂ ^ 3 * W.a₆ + 8 * W.a₂ ^ 2 * W.a₄ ^ 2 - 32 * W.a₄ ^ 3
      - 216 * W.a₆ ^ 2 + 144 * W.a₂ * W.a₄ * W.a₆) * h2
  exact not_isUnit_zero (hΔ ▸ W.isUnit_Δ)


-- @@ L86-86 verbatim
/-! ## Item 1: `Algebra k[X] K` and towers -/


-- @@ L88-88 verbatim
variable (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]


-- @@ L90-94 verbatim
/-- The `k[X]`-algebra structure on a fraction field of the coordinate ring,
sending `X` to the coordinate function `x`. -/
@[reducible]
def algebraPolynomial : Algebra k[X] K :=
  ((algebraMap W.CoordinateRing K).comp (algebraMap k[X] W.CoordinateRing)).toAlgebra


-- @@ L96-102 verbatim
omit [IsFractionRing W.CoordinateRing K] in
/-- `algebraPolynomial` is compatible with the coordinate ring inclusion. -/
theorem algebraPolynomial_isScalarTower :
    letI := W.algebraPolynomial K
    IsScalarTower k[X] W.CoordinateRing K :=
  letI := W.algebraPolynomial K
  IsScalarTower.of_algebraMap_eq fun _ => rfl


-- @@ L104-104 verbatim
section AbstractPolynomialAlgebra


-- @@ L106-106 verbatim
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]


-- @@ L108-113 verbatim
include W in
theorem algebraMap_polynomial_injective :
    Function.Injective (algebraMap k[X] K) := by
  rw [IsScalarTower.algebraMap_eq k[X] W.CoordinateRing K]
  exact (IsFractionRing.injective W.CoordinateRing K).comp
    (CoordinateRing.algebraMap_polynomial_injective' W)


-- @@ L115-115 verbatim
/-! ## Item 2: `Algebra k⟮X⟯ K` -/


-- @@ L117-120 verbatim
/-- The rational function field structure on `K`, lifting `k[X] → K` to `k⟮X⟯`. -/
@[reducible]
def algebraRatFunc : Algebra k⟮X⟯ K :=
  (IsFractionRing.lift (W.algebraMap_polynomial_injective K)).toAlgebra


-- @@ L122-127 verbatim
theorem algebraRatFunc_isScalarTower :
    letI := W.algebraRatFunc K
    IsScalarTower k[X] k⟮X⟯ K := by
  let := W.algebraRatFunc K
  refine IsScalarTower.of_algebraMap_eq fun p => ?_
  exact (IsFractionRing.lift_algebraMap (W.algebraMap_polynomial_injective K) p).symm


-- @@ L129-129 verbatim
/-! ## Item 3: `FunctionField k K` via the localized `{1, y}` basis -/


-- @@ L131-131 verbatim
section AbstractRatFuncAlgebra


-- @@ L133-133 verbatim
variable [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]


-- @@ L135-136 verbatim
/-- The coordinate function `y ∈ K`, the image of the `AdjoinRoot` generator. -/
def yCoord : K := algebraMap W.CoordinateRing K (CoordinateRing.mk W Y)


-- @@ L138-140 verbatim
/-- The `{1, y}` basis of `K` over `k⟮X⟯`, localized from `CoordinateRing.basis`. -/
def basisRatFunc : Module.Basis (Fin 2) k⟮X⟯ K :=
  (CoordinateRing.basis W).localizationLocalization k⟮X⟯ k[X]⁰ K


-- @@ L142-145 verbatim
@[simp]
theorem basisRatFunc_zero : W.basisRatFunc K 0 = 1 := by
  rw [basisRatFunc, Module.Basis.localizationLocalization_apply, CoordinateRing.basis_zero,
    map_one]


-- @@ L147-150 verbatim
@[simp]
theorem basisRatFunc_one : W.basisRatFunc K 1 = W.yCoord K := by
  rw [basisRatFunc, Module.Basis.localizationLocalization_apply, CoordinateRing.basis_one,
    yCoord]


-- @@ L152-155 verbatim
include W in
/-- A fraction field of an elliptic coordinate ring is a function field. -/
theorem functionField : _root_.FunctionField k K :=
  Module.Finite.of_basis (W.basisRatFunc K)


-- @@ L157-160 verbatim
include W in
/-- The Weierstrass extension has degree 2 over `k(x)`. -/
theorem finrank_ratFunc_eq_two : Module.finrank k⟮X⟯ K = 2 := by
  rw [Module.finrank_eq_card_basis (W.basisRatFunc K), Fintype.card_fin]


-- @@ L162-162 verbatim
/-! ## Item 4: separability -/


-- @@ L164-173 verbatim
omit [IsFractionRing W.CoordinateRing K] in
theorem aeval_yCoord :
    Polynomial.aeval (W.yCoord K) (W.polynomial.map (algebraMap k[X] k⟮X⟯)) = 0 := by
  have h1 : eval₂ (algebraMap k[X] K) (W.yCoord K) W.polynomial = 0 := by
    rw [IsScalarTower.algebraMap_eq k[X] W.CoordinateRing K, yCoord]
    change eval₂ ((algebraMap W.CoordinateRing K).comp (AdjoinRoot.of W.polynomial))
      ((algebraMap W.CoordinateRing K) (AdjoinRoot.root W.polynomial)) W.polynomial = 0
    rw [← Polynomial.hom_eval₂, AdjoinRoot.eval₂_root, map_zero]
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← IsScalarTower.algebraMap_eq k[X] k⟮X⟯ K]
  exact h1


-- @@ L175-178 verbatim
omit [IsFractionRing W.CoordinateRing K] in
theorem yCoord_isIntegral : IsIntegral k⟮X⟯ (W.yCoord K) :=
  ⟨W.polynomial.map (algebraMap k[X] k⟮X⟯), monic_polynomial.map _, by
    rw [← Polynomial.aeval_def]; exact W.aeval_yCoord K⟩


-- @@ L180-189 verbatim
theorem yCoord_notMem_range :
    W.yCoord K ∉ Set.range (algebraMap k⟮X⟯ K) := by
  rintro ⟨c, hc⟩
  have h := Fintype.linearIndependent_iff.mp (W.basisRatFunc K).linearIndependent ![c, -1]
  have h1 : (![c, -1] : Fin 2 → k⟮X⟯) 1 = 0 := by
    refine h ?_ 1
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, basisRatFunc_zero, basisRatFunc_one]
    rw [← hc, Algebra.smul_def, mul_one, neg_one_smul, add_neg_cancel]
  norm_num at h1


-- @@ L191-224 verbatim
theorem minpoly_yCoord :
    minpoly k⟮X⟯ (W.yCoord K) = W.polynomial.map (algebraMap k[X] k⟮X⟯) := by
  have hmonic : (W.polynomial.map (algebraMap k[X] k⟮X⟯)).Monic := monic_polynomial.map _
  have hdvd : minpoly k⟮X⟯ (W.yCoord K) ∣ W.polynomial.map (algebraMap k[X] k⟮X⟯) :=
    minpoly.dvd k⟮X⟯ (W.yCoord K) (W.aeval_yCoord K)
  have hdeg : (W.polynomial.map (algebraMap k[X] k⟮X⟯)).natDegree = 2 := by
    rw [monic_polynomial.natDegree_map, natDegree_polynomial]
  have hle : (minpoly k⟮X⟯ (W.yCoord K)).natDegree ≤ 2 := by
    rw [← hdeg]; exact natDegree_le_of_dvd hdvd hmonic.ne_zero
  have hge : 2 ≤ (minpoly k⟮X⟯ (W.yCoord K)).natDegree := by
    rcases Nat.lt_or_ge (minpoly k⟮X⟯ (W.yCoord K)).natDegree 2 with hlt | hge
    · have hpos := minpoly.natDegree_pos (W.yCoord_isIntegral K)
      have h1 : (minpoly k⟮X⟯ (W.yCoord K)).natDegree = 1 := by omega
      exact absurd (minpoly.natDegree_eq_one_iff.mp h1) (W.yCoord_notMem_range K)
    · exact hge
  have heq : (minpoly k⟮X⟯ (W.yCoord K)).natDegree = 2 := le_antisymm hle hge
  -- monic ∣ monic with equal degree ⇒ equal
  obtain ⟨c, hc⟩ := hdvd
  have hmp : (minpoly k⟮X⟯ (W.yCoord K)).Monic := minpoly.monic (W.yCoord_isIntegral K)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hc
    exact hmonic.ne_zero hc
  have hcdeg : c.natDegree = 0 := by
    have := congr_arg Polynomial.natDegree hc
    rw [hdeg, Polynomial.natDegree_mul hmp.ne_zero hc0, heq] at this
    omega
  have hcC : c = C (c.coeff 0) := eq_C_of_natDegree_eq_zero hcdeg
  have hlead : c.coeff 0 = 1 := by
    have := congr_arg Polynomial.leadingCoeff hc
    rw [hmonic.leadingCoeff, Polynomial.leadingCoeff_mul, hmp.leadingCoeff, one_mul,
      hcC, Polynomial.leadingCoeff_C] at this
    exact this.symm
  rw [hc, hcC, hlead, Polynomial.C_1, mul_one]


-- @@ L226-257 verbatim
include W in
/-- The elliptic function field is separable over `k(x)`,
in every characteristic. -/
theorem isSeparable [W.IsElliptic] : Algebra.IsSeparable k⟮X⟯ K := by
  -- the generator y is separable
  have hsep : IsSeparable k⟮X⟯ (W.yCoord K) := by
    rw [IsSeparable, separable_iff_derivative_ne_zero
      (minpoly.irreducible (W.yCoord_isIntegral K)), minpoly_yCoord, Polynomial.derivative_map,
      derivative_polynomial]
    intro hzero
    rw [Polynomial.map_eq_zero_iff (IsFractionRing.injective k[X] k⟮X⟯)] at hzero
    exact W.polynomialY_ne_zero hzero
  -- K is generated by y
  have htop : IntermediateField.adjoin k⟮X⟯ {W.yCoord K} = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : z ∈ Submodule.span k⟮X⟯ (Set.range (W.basisRatFunc K)) := by
      rw [(W.basisRatFunc K).span_eq]; trivial
    have hle : Submodule.span k⟮X⟯ (Set.range (W.basisRatFunc K)) ≤
        Subalgebra.toSubmodule (IntermediateField.adjoin k⟮X⟯ {W.yCoord K}).toSubalgebra := by
      rw [Submodule.span_le, Set.range_subset_iff]
      refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
      · simp only [SetLike.mem_coe, Subalgebra.mem_toSubmodule, basisRatFunc_zero]
        exact one_mem _
      · simp only [SetLike.mem_coe, Subalgebra.mem_toSubmodule, basisRatFunc_one]
        exact IntermediateField.mem_adjoin_simple_self k⟮X⟯ (W.yCoord K)
    exact hle hz
  have : Algebra.IsSeparable k⟮X⟯ (IntermediateField.adjoin k⟮X⟯ {W.yCoord K}) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable k⟮X⟯ K).mpr hsep
  let : Algebra k⟮X⟯ (⊤ : IntermediateField k⟮X⟯ K) := IntermediateField.algebra' ⊤
  exact AlgEquiv.Algebra.isSeparable
    ((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv)


-- @@ L259-259 verbatim
end AbstractRatFuncAlgebra


-- @@ L261-261 verbatim
end AbstractPolynomialAlgebra


-- @@ L263-263 verbatim
end WeierstrassCurve.Affine


-- @@ L265-265 verbatim
/-! ## Constant-field algebra structure (no curve needed) -/


-- @@ L267-267 verbatim
namespace FunctionField


-- @@ L269-269 verbatim
open scoped Polynomial


-- @@ L271-271 verbatim
variable (k K : Type*) [Field k] [Field K] [Algebra k[X] K]


-- @@ L273-276 verbatim
/-- The constant field structure `Algebra k K` through `k[X]`. -/
@[reducible]
noncomputable def algebraConstants : Algebra k K :=
  ((algebraMap k[X] K).comp (algebraMap k k[X])).toAlgebra


-- @@ L278-282 verbatim
theorem algebraConstants_isScalarTower :
    letI := algebraConstants k K
    IsScalarTower k k[X] K :=
  letI := algebraConstants k K
  IsScalarTower.of_algebraMap_eq fun _ => rfl


-- @@ L284-284 verbatim
end FunctionField


-- @@ L286-286 verbatim
/-! ## Item 5: `IsFullConstantField` over an algebraically closed base -/


-- @@ L288-300 verbatim
/-- Over an algebraically closed base field, any field extension has full constant field:
an element algebraic over `k` has a linear minimal polynomial. -/
theorem FunctionField.isFullConstantField_of_isAlgClosed (k K : Type*) [Field k] [Field K]
    [Algebra k K] [IsAlgClosed k] : FunctionField.IsFullConstantField k K where
  algebraic_mem x hx := by
    have hint : IsIntegral k x := hx.isIntegral
    have hlead : (minpoly k x).leadingCoeff = 1 := minpoly.monic hint
    have hdeg : (minpoly k x).degree = 1 :=
      IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hint)
    have h0 : Polynomial.aeval x (minpoly k x) = 0 := minpoly.aeval k x
    rw [eq_X_add_C_of_degree_eq_one hdeg, hlead, Polynomial.C_1, one_mul, map_add,
      Polynomial.aeval_X, Polynomial.aeval_C, add_eq_zero_iff_eq_neg] at h0
    exact ⟨-(minpoly k x).coeff 0, by rw [map_neg, ← h0]⟩


-- @@ L302-302 verbatim
end
