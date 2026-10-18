import OAI.AlgebraicGeometry.StableCoordinate.ChartLNDConstant
import OAI.AlgebraicGeometry.StableCoordinate.DeterminantIntersection
import OAI.AlgebraicGeometry.StableCoordinate.RigidityCoefficients
import Mathlib.Tactic.FinCases


-- @@ L6-6 verbatim
namespace OAI


-- @@ L8-15 verbatim
/-!
# Vertical locally nilpotent derivations of the determinant ring

The vertical-coefficient step is the assertion in Section 5 that a locally
nilpotent derivation fixing `a,d,u` has coefficient in `k[a,d,u]`.  The
coefficient is the actual element `c * D b - b * D c` of the determinant-one
quotient, not an assumed polynomial representative.
-/


-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
namespace StableCoordinate.VerticalLND


-- @@ L21-21 verbatim
open DeterminantRing


-- @@ L23-23 verbatim
variable {k : Type*} [CommRing k]


-- @@ L25-35 verbatim
/-- Fixing the three displayed variables means fixing the entire polynomial
coefficient subalgebra; no algebraic-independence assumption is inserted. -/
theorem annihilates_baseMap (D : Derivation k (DeterminantRing.C k) (DeterminantRing.C k))
    (ha : D (a k) = 0) (hd : D (d k) = 0) (hu : D (u k) = 0) :
    ∀ p : Base k, D (baseMap p) = 0 := by
  apply DerivationScalarUpgrade.annihilates_mvPolynomial D baseMap
  intro i
  fin_cases i
  · simpa using ha
  · simpa using hd
  · simpa using hu


-- @@ L37-39 verbatim
/-- The source's common coefficient in the two remaining generator values. -/
def coefficient (D : Derivation k (DeterminantRing.C k) (DeterminantRing.C k)) :
    DeterminantRing.C k := rigidityCoefficient D (b k) (c k)


-- @@ L41-47 verbatim
/-- The coefficient formulas hold in the exact determinant quotient. -/
theorem coefficient_equations
    (D : Derivation k (DeterminantRing.C k) (DeterminantRing.C k))
    (ha : D (a k) = 0) (hd : D (d k) = 0) :
    D (b k) = a k * coefficient D ∧ D (c k) = d k * coefficient D :=
  derivation_rigidityCoefficient D (a k) (d k) (b k) (c k)
    (determinant_relation k) ha hd




-- @@ L51-51 verbatim
section CharacteristicZero


-- @@ L53-53 verbatim
variable {K : Type*} [Field K] [CharZero K]


-- @@ L55-84 verbatim
/-- The source coefficient is constant on the actual `a`-chart. -/
theorem coefficient_chartA_eq_C
    (D : Derivation K (DeterminantRing.C K) (DeterminantRing.C K))
    (hD : ∀ z : DeterminantRing.C K, ∃ n : ℕ,
      (D : DeterminantRing.C K → DeterminantRing.C K)^[n] z = 0)
    (ha : D (a K) = 0) (hd : D (d K) = 0) (hu : D (u K) = 0) :
    chartMapA K (coefficient D) =
      Polynomial.C ((chartMapA K (coefficient D)).coeff 0) := by
  let : IsDomain (BaseAway K 0) :=
    IsLocalization.Away.isDomain (BaseAway K 0) (MvPolynomial.X_ne_zero (R := K) (0 : Fin 3))
  let : CharZero (BaseAway K 0) :=
    charZero_of_injective_algebraMap (algebraMap K (BaseAway K 0)).injective
  let : IsLocalization.Away (baseMap (MvPolynomial.X 0 : Base K)) (AwayA K) := by
    rw [baseMap_X0]
    infer_instance
  have h := ChartLNDConstant.chart_coefficient_eq_C
    (baseMap (k := K)) (MvPolynomial.X 0) D hD
    (annihilates_baseMap D ha hd hu) (chartEquivA K)
    (fun r => by
      change toChartA K (algebraMap (DeterminantRing.C K) (AwayA K) (baseMap r)) = _
      simp only [toChartA_algebraMap, chartMapA_baseMap])
    (b K) (coefficient D)
    (by
      change toChartA K (algebraMap (DeterminantRing.C K) (AwayA K) (b K)) = _
      simp only [toChartA_algebraMap, chartMapA_b])
    (by simpa only [baseMap_X0] using (coefficient_equations D ha hd).1)
  change toChartA K (algebraMap (DeterminantRing.C K) (AwayA K) (coefficient D)) =
    Polynomial.C ((toChartA K
      (algebraMap (DeterminantRing.C K) (AwayA K) (coefficient D))).coeff 0) at h
  simpa only [toChartA_algebraMap] using h


-- @@ L86-115 verbatim
/-- The same source coefficient is constant on the actual `d`-chart. -/
theorem coefficient_chartD_eq_C
    (D : Derivation K (DeterminantRing.C K) (DeterminantRing.C K))
    (hD : ∀ z : DeterminantRing.C K, ∃ n : ℕ,
      (D : DeterminantRing.C K → DeterminantRing.C K)^[n] z = 0)
    (ha : D (a K) = 0) (hd : D (d K) = 0) (hu : D (u K) = 0) :
    chartMapD K (coefficient D) =
      Polynomial.C ((chartMapD K (coefficient D)).coeff 0) := by
  let : IsDomain (BaseAway K 1) :=
    IsLocalization.Away.isDomain (BaseAway K 1) (MvPolynomial.X_ne_zero (R := K) (1 : Fin 3))
  let : CharZero (BaseAway K 1) :=
    charZero_of_injective_algebraMap (algebraMap K (BaseAway K 1)).injective
  let : IsLocalization.Away (baseMap (MvPolynomial.X 1 : Base K)) (AwayD K) := by
    rw [baseMap_X1]
    infer_instance
  have h := ChartLNDConstant.chart_coefficient_eq_C
    (baseMap (k := K)) (MvPolynomial.X 1) D hD
    (annihilates_baseMap D ha hd hu) (chartEquivD K)
    (fun r => by
      change toChartD K (algebraMap (DeterminantRing.C K) (AwayD K) (baseMap r)) = _
      simp only [toChartD_algebraMap, chartMapD_baseMap])
    (c K) (coefficient D)
    (by
      change toChartD K (algebraMap (DeterminantRing.C K) (AwayD K) (c K)) = _
      simp only [toChartD_algebraMap, chartMapD_c])
    (by simpa only [baseMap_X1] using (coefficient_equations D ha hd).2)
  change toChartD K (algebraMap (DeterminantRing.C K) (AwayD K) (coefficient D)) =
    Polynomial.C ((toChartD K
      (algebraMap (DeterminantRing.C K) (AwayD K) (coefficient D))).coeff 0) at h
  simpa only [toChartD_algebraMap] using h


-- @@ L117-126 verbatim
/-- Every vertical LND on the exact determinant hypersurface has a
polynomial coefficient in the three independent variables `a,d,u`. -/
theorem exists_polynomial_coefficient
    (D : Derivation K (DeterminantRing.C K) (DeterminantRing.C K))
    (hD : ∀ z : DeterminantRing.C K, ∃ n : ℕ,
      (D : DeterminantRing.C K → DeterminantRing.C K)^[n] z = 0)
    (ha : D (a K) = 0) (hd : D (d K) = 0) (hu : D (u K) = 0) :
    ∃ r : Base K, baseMap r = coefficient D :=
  exists_base_of_constant_charts K (coefficient_chartA_eq_C D hD ha hd hu)
    (coefficient_chartD_eq_C D hD ha hd hu)


-- @@ L128-135 verbatim
/-- Subalgebra-membership form of the polynomial-coefficient result. -/
theorem coefficient_mem_baseRange
    (D : Derivation K (DeterminantRing.C K) (DeterminantRing.C K))
    (hD : ∀ z : DeterminantRing.C K, ∃ n : ℕ,
      (D : DeterminantRing.C K → DeterminantRing.C K)^[n] z = 0)
    (ha : D (a K) = 0) (hd : D (d K) = 0) (hu : D (u K) = 0) :
    coefficient D ∈ (baseMap (k := K)).range :=
  exists_polynomial_coefficient D hD ha hd hu


-- @@ L137-147 verbatim
/-- Exact generator-value classification of vertical locally nilpotent
derivations; the polynomial representative is constructed, not assumed. -/
theorem classification
    (D : Derivation K (DeterminantRing.C K) (DeterminantRing.C K))
    (hD : ∀ z : DeterminantRing.C K, ∃ n : ℕ,
      (D : DeterminantRing.C K → DeterminantRing.C K)^[n] z = 0)
    (ha : D (a K) = 0) (hd : D (d K) = 0) (hu : D (u K) = 0) :
    ∃ r : Base K, D (b K) = a K * baseMap r ∧ D (c K) = d K * baseMap r := by
  obtain ⟨r, hr⟩ := exists_polynomial_coefficient D hD ha hd hu
  exact ⟨r, by rw [hr]; exact (coefficient_equations D ha hd).1,
    by rw [hr]; exact (coefficient_equations D ha hd).2⟩


-- @@ L149-149 verbatim
end CharacteristicZero


-- @@ L151-151 verbatim
end StableCoordinate.VerticalLND


-- @@ L153-153 verbatim
end


-- @@ L155-155 verbatim
end OAI
