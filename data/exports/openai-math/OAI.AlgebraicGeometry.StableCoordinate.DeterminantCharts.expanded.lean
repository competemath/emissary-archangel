import OAI.AlgebraicGeometry.StableCoordinate.DeterminantRing
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic.LinearCombination


-- @@ L6-6 verbatim
namespace OAI


-- @@ L8-13 verbatim
/-!
# Explicit affine charts for the determinant ring

These are the `a`- and `d`-localizations in Section 5, not the bundle charts
in Section 4. The coefficient algebra has independent variables `a,d,u`.
-/


-- @@ L15-15 verbatim
namespace StableCoordinate.DeterminantRing


-- @@ L17-17 verbatim
open MvPolynomial


-- @@ L19-19 verbatim
variable (k : Type*) [CommRing k]


-- @@ L21-21 verbatim
abbrev BaseAway (i : Fin 3) := Localization.Away (X i : Base k)

-- @@ L22-22 verbatim
abbrev Chart (i : Fin 3) := Polynomial (BaseAway k i)

-- @@ L23-23 verbatim
abbrev AwayA := Localization.Away (a k)

-- @@ L24-24 verbatim
abbrev AwayD := Localization.Away (d k)


-- @@ L26-27 verbatim
noncomputable def chartVariable (i j : Fin 3) : Chart k i :=
  Polynomial.C (algebraMap (Base k) (BaseAway k i) (X j))

-- @@ L28-29 verbatim
noncomputable def chartInverse (i : Fin 3) : Chart k i :=
  Polynomial.C (IsLocalization.Away.invSelf (X i : Base k))


-- @@ L31-33 verbatim
@[simp] theorem chartVariable_mul_inverse (i : Fin 3) :
    chartVariable k i i * chartInverse k i = 1 := by
  rw [chartVariable, chartInverse, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]


-- @@ L35-36 verbatim
theorem chartVariable_isUnit (i : Fin 3) : IsUnit (chartVariable k i i) :=
  isUnit_iff_exists_inv.mpr ⟨chartInverse k i, chartVariable_mul_inverse k i⟩


-- @@ L38-46 verbatim
noncomputable def chartMapA : C k →ₐ[k] Chart k 0 :=
  lift (chartVariable k 0 0) (chartVariable k 0 1) Polynomial.X
    (chartInverse k 0 * (1 + Polynomial.X * chartVariable k 0 1))
    (chartVariable k 0 2) (by
      calc
        _ = (chartVariable k 0 0 * chartInverse k 0) *
            (1 + Polynomial.X * chartVariable k 0 1) -
            Polynomial.X * chartVariable k 0 1 := by ring
        _ = 1 := by rw [chartVariable_mul_inverse]; ring)


-- @@ L48-49 verbatim
@[simp] theorem chartMapA_a : chartMapA k (a k) = chartVariable k 0 0 := by
  simp [chartMapA]

-- @@ L50-51 verbatim
@[simp] theorem chartMapA_d : chartMapA k (d k) = chartVariable k 0 1 := by
  simp [chartMapA]

-- @@ L52-53 verbatim
@[simp] theorem chartMapA_b : chartMapA k (b k) = Polynomial.X := by
  simp [chartMapA]

-- @@ L54-56 verbatim
@[simp] theorem chartMapA_c : chartMapA k (c k) =
    chartInverse k 0 * (1 + Polynomial.X * chartVariable k 0 1) := by
  simp [chartMapA]

-- @@ L57-58 verbatim
@[simp] theorem chartMapA_u : chartMapA k (u k) = chartVariable k 0 2 := by
  simp [chartMapA]


-- @@ L60-62 verbatim
noncomputable def toChartA : AwayA k →ₐ[k] Chart k 0 :=
  IsLocalization.Away.liftAlgHom (a k)
    (show IsUnit (chartMapA k (a k)) by rw [chartMapA_a]; exact chartVariable_isUnit k 0)


-- @@ L64-66 verbatim
@[simp] theorem toChartA_algebraMap (r : C k) :
    toChartA k (algebraMap (C k) (AwayA k) r) = chartMapA k r := by
  simp [toChartA, IsLocalization.Away.liftAlgHom_apply]


-- @@ L68-69 verbatim
noncomputable def baseToAwayA : Base k →ₐ[k] AwayA k :=
  (Algebra.algHom k (C k) (AwayA k)).comp baseMap


-- @@ L71-72 verbatim
@[simp] theorem baseToAwayA_X0 : baseToAwayA k (X 0) =
    algebraMap (C k) (AwayA k) (a k) := by simp [baseToAwayA, Algebra.algHom]

-- @@ L73-74 verbatim
@[simp] theorem baseToAwayA_X1 : baseToAwayA k (X 1) =
    algebraMap (C k) (AwayA k) (d k) := by simp [baseToAwayA, Algebra.algHom]

-- @@ L75-76 verbatim
@[simp] theorem baseToAwayA_X2 : baseToAwayA k (X 2) =
    algebraMap (C k) (AwayA k) (u k) := by simp [baseToAwayA, Algebra.algHom]


-- @@ L78-82 verbatim
noncomputable def coefficientFromChartA : BaseAway k 0 →ₐ[k] AwayA k :=
  IsLocalization.Away.liftAlgHom (X 0 : Base k)
    (show IsUnit (baseToAwayA k (X 0)) by
      rw [baseToAwayA_X0]
      exact IsLocalization.Away.algebraMap_isUnit (a k))


-- @@ L84-86 verbatim
@[simp] theorem coefficientFromChartA_algebraMap (r : Base k) :
    coefficientFromChartA k (algebraMap (Base k) (BaseAway k 0) r) = baseToAwayA k r := by
  simp [coefficientFromChartA, IsLocalization.Away.liftAlgHom_apply]


-- @@ L88-89 verbatim
noncomputable def fromChartA : Chart k 0 →ₐ[k] AwayA k :=
  Polynomial.aevalTower (coefficientFromChartA k) (algebraMap (C k) (AwayA k) (b k))


-- @@ L91-92 verbatim
@[simp] theorem fromChartA_X : fromChartA k Polynomial.X =
    algebraMap (C k) (AwayA k) (b k) := by simp [fromChartA]

-- @@ L93-94 verbatim
@[simp] theorem fromChartA_C (r : BaseAway k 0) :
    fromChartA k (Polynomial.C r) = coefficientFromChartA k r := by simp [fromChartA]

-- @@ L95-97 verbatim
@[simp] theorem fromChartA_variable (i : Fin 3) :
    fromChartA k (chartVariable k 0 i) = baseToAwayA k (X i) := by
  simp [chartVariable]


-- @@ L99-104 verbatim
private theorem map_invSelf_eq {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] (r : R) [IsLocalization.Away r S] (f : S →+* T) (y : T)
    (hy : f (algebraMap R S r) * y = 1) :
    f (IsLocalization.Away.invSelf r) = y := by
  apply ((IsLocalization.Away.algebraMap_isUnit r).map f).mul_left_cancel
  rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one, hy]


-- @@ L106-112 verbatim
@[simp] theorem fromChartA_inverse :
    fromChartA k (chartInverse k 0) = IsLocalization.Away.invSelf (a k) := by
  rw [chartInverse, fromChartA_C]
  apply map_invSelf_eq (X 0 : Base k) (coefficientFromChartA k).toRingHom
  change coefficientFromChartA k (algebraMap (Base k) (BaseAway k 0) (X 0)) *
    IsLocalization.Away.invSelf (a k) = 1
  simp


-- @@ L114-118 verbatim
@[simp] theorem toChartA_inverse :
    toChartA k (IsLocalization.Away.invSelf (a k)) = chartInverse k 0 := by
  apply map_invSelf_eq (a k) (toChartA k).toRingHom
  change toChartA k (algebraMap (C k) (AwayA k) (a k)) * chartInverse k 0 = 1
  simp


-- @@ L120-127 verbatim
theorem localized_c : algebraMap (C k) (AwayA k) (c k) =
    IsLocalization.Away.invSelf (a k) *
      (1 + algebraMap (C k) (AwayA k) (b k) * algebraMap (C k) (AwayA k) (d k)) := by
  apply (IsLocalization.Away.algebraMap_isUnit (a k)).mul_left_cancel
  rw [← mul_assoc, IsLocalization.Away.mul_invSelf, one_mul]
  have h := congrArg (algebraMap (C k) (AwayA k)) (determinant_relation k)
  simp only [map_sub, map_mul, map_one] at h
  linear_combination h


-- @@ L129-132 verbatim
theorem fromChartA_comp_toChartA :
    (fromChartA k).comp (toChartA k) = AlgHom.id k (AwayA k) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (a k))
  apply hom_ext <;> simp [Algebra.algHom, localized_c]


-- @@ L134-141 verbatim
theorem toChartA_comp_fromChartA :
    (toChartA k).comp (fromChartA k) = AlgHom.id k (Chart k 0) := by
  apply Polynomial.algHom_ext'
  · apply IsLocalization.algHom_ext (Submonoid.powers (X 0 : Base k))
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [Algebra.algHom, chartVariable]
  · simp


-- @@ L143-146 verbatim
/-- The actual algebra equivalence `C[a⁻¹] ≃ k[a,a⁻¹,d,u][b]`. -/
noncomputable def chartEquivA : AwayA k ≃ₐ[k] Chart k 0 :=
  AlgEquiv.ofAlgHom (toChartA k) (fromChartA k)
    (toChartA_comp_fromChartA k) (fromChartA_comp_toChartA k)


-- @@ L148-156 verbatim
noncomputable def chartMapD : C k →ₐ[k] Chart k 1 :=
  lift (chartVariable k 1 0) (chartVariable k 1 1)
    (chartInverse k 1 * (chartVariable k 1 0 * Polynomial.X - 1))
    Polynomial.X (chartVariable k 1 2) (by
      calc
        _ = chartVariable k 1 0 * Polynomial.X -
            (chartVariable k 1 1 * chartInverse k 1) *
            (chartVariable k 1 0 * Polynomial.X - 1) := by ring
        _ = 1 := by rw [chartVariable_mul_inverse]; ring)


-- @@ L158-159 verbatim
@[simp] theorem chartMapD_a : chartMapD k (a k) = chartVariable k 1 0 := by
  simp [chartMapD]

-- @@ L160-161 verbatim
@[simp] theorem chartMapD_d : chartMapD k (d k) = chartVariable k 1 1 := by
  simp [chartMapD]

-- @@ L162-164 verbatim
@[simp] theorem chartMapD_b : chartMapD k (b k) =
    chartInverse k 1 * (chartVariable k 1 0 * Polynomial.X - 1) := by
  simp [chartMapD]

-- @@ L165-166 verbatim
@[simp] theorem chartMapD_c : chartMapD k (c k) = Polynomial.X := by
  simp [chartMapD]

-- @@ L167-168 verbatim
@[simp] theorem chartMapD_u : chartMapD k (u k) = chartVariable k 1 2 := by
  simp [chartMapD]


-- @@ L170-172 verbatim
noncomputable def toChartD : AwayD k →ₐ[k] Chart k 1 :=
  IsLocalization.Away.liftAlgHom (d k)
    (show IsUnit (chartMapD k (d k)) by rw [chartMapD_d]; exact chartVariable_isUnit k 1)


-- @@ L174-176 verbatim
@[simp] theorem toChartD_algebraMap (r : C k) :
    toChartD k (algebraMap (C k) (AwayD k) r) = chartMapD k r := by
  simp [toChartD, IsLocalization.Away.liftAlgHom_apply]


-- @@ L178-179 verbatim
noncomputable def baseToAwayD : Base k →ₐ[k] AwayD k :=
  (Algebra.algHom k (C k) (AwayD k)).comp baseMap


-- @@ L181-182 verbatim
@[simp] theorem baseToAwayD_X0 : baseToAwayD k (X 0) =
    algebraMap (C k) (AwayD k) (a k) := by simp [baseToAwayD, Algebra.algHom]

-- @@ L183-184 verbatim
@[simp] theorem baseToAwayD_X1 : baseToAwayD k (X 1) =
    algebraMap (C k) (AwayD k) (d k) := by simp [baseToAwayD, Algebra.algHom]

-- @@ L185-186 verbatim
@[simp] theorem baseToAwayD_X2 : baseToAwayD k (X 2) =
    algebraMap (C k) (AwayD k) (u k) := by simp [baseToAwayD, Algebra.algHom]


-- @@ L188-192 verbatim
noncomputable def coefficientFromChartD : BaseAway k 1 →ₐ[k] AwayD k :=
  IsLocalization.Away.liftAlgHom (X 1 : Base k)
    (show IsUnit (baseToAwayD k (X 1)) by
      rw [baseToAwayD_X1]
      exact IsLocalization.Away.algebraMap_isUnit (d k))


-- @@ L194-196 verbatim
@[simp] theorem coefficientFromChartD_algebraMap (r : Base k) :
    coefficientFromChartD k (algebraMap (Base k) (BaseAway k 1) r) = baseToAwayD k r := by
  simp [coefficientFromChartD, IsLocalization.Away.liftAlgHom_apply]


-- @@ L198-199 verbatim
noncomputable def fromChartD : Chart k 1 →ₐ[k] AwayD k :=
  Polynomial.aevalTower (coefficientFromChartD k) (algebraMap (C k) (AwayD k) (c k))


-- @@ L201-202 verbatim
@[simp] theorem fromChartD_X : fromChartD k Polynomial.X =
    algebraMap (C k) (AwayD k) (c k) := by simp [fromChartD]

-- @@ L203-204 verbatim
@[simp] theorem fromChartD_C (r : BaseAway k 1) :
    fromChartD k (Polynomial.C r) = coefficientFromChartD k r := by simp [fromChartD]

-- @@ L205-207 verbatim
@[simp] theorem fromChartD_variable (i : Fin 3) :
    fromChartD k (chartVariable k 1 i) = baseToAwayD k (X i) := by
  simp [chartVariable]


-- @@ L209-215 verbatim
@[simp] theorem fromChartD_inverse :
    fromChartD k (chartInverse k 1) = IsLocalization.Away.invSelf (d k) := by
  rw [chartInverse, fromChartD_C]
  apply map_invSelf_eq (X 1 : Base k) (coefficientFromChartD k).toRingHom
  change coefficientFromChartD k (algebraMap (Base k) (BaseAway k 1) (X 1)) *
    IsLocalization.Away.invSelf (d k) = 1
  simp


-- @@ L217-221 verbatim
@[simp] theorem toChartD_inverse :
    toChartD k (IsLocalization.Away.invSelf (d k)) = chartInverse k 1 := by
  apply map_invSelf_eq (d k) (toChartD k).toRingHom
  change toChartD k (algebraMap (C k) (AwayD k) (d k)) * chartInverse k 1 = 1
  simp


-- @@ L223-230 verbatim
theorem localized_b : algebraMap (C k) (AwayD k) (b k) =
    IsLocalization.Away.invSelf (d k) *
      (algebraMap (C k) (AwayD k) (a k) * algebraMap (C k) (AwayD k) (c k) - 1) := by
  apply (IsLocalization.Away.algebraMap_isUnit (d k)).mul_left_cancel
  rw [← mul_assoc, IsLocalization.Away.mul_invSelf, one_mul]
  have h := congrArg (algebraMap (C k) (AwayD k)) (determinant_relation k)
  simp only [map_sub, map_mul, map_one] at h
  linear_combination -h


-- @@ L232-235 verbatim
theorem fromChartD_comp_toChartD :
    (fromChartD k).comp (toChartD k) = AlgHom.id k (AwayD k) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (d k))
  apply hom_ext <;> simp [Algebra.algHom, localized_b]


-- @@ L237-244 verbatim
theorem toChartD_comp_fromChartD :
    (toChartD k).comp (fromChartD k) = AlgHom.id k (Chart k 1) := by
  apply Polynomial.algHom_ext'
  · apply IsLocalization.algHom_ext (Submonoid.powers (X 1 : Base k))
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [Algebra.algHom, chartVariable]
  · simp


-- @@ L246-249 verbatim
/-- The actual algebra equivalence `C[d⁻¹] ≃ k[a,d,d⁻¹,u][c]`. -/
noncomputable def chartEquivD : AwayD k ≃ₐ[k] Chart k 1 :=
  AlgEquiv.ofAlgHom (toChartD k) (fromChartD k)
    (toChartD_comp_fromChartD k) (fromChartD_comp_toChartD k)


-- @@ L251-257 verbatim
theorem chartMapA_comp_baseMap :
    (chartMapA k).comp baseMap =
      (Polynomial.CAlgHom : BaseAway k 0 →ₐ[k] Chart k 0).comp
        (Algebra.algHom k (Base k) (BaseAway k 0)) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [baseMap, chartVariable, Algebra.algHom]


-- @@ L259-265 verbatim
theorem chartMapD_comp_baseMap :
    (chartMapD k).comp baseMap =
      (Polynomial.CAlgHom : BaseAway k 1 →ₐ[k] Chart k 1).comp
        (Algebra.algHom k (Base k) (BaseAway k 1)) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [baseMap, chartVariable, Algebra.algHom]


-- @@ L267-269 verbatim
@[simp] theorem chartMapA_baseMap (r : Base k) :
    chartMapA k (baseMap r) = Polynomial.C (algebraMap (Base k) (BaseAway k 0) r) := by
  exact AlgHom.congr_fun (chartMapA_comp_baseMap k) r


-- @@ L271-273 verbatim
@[simp] theorem chartMapD_baseMap (r : Base k) :
    chartMapD k (baseMap r) = Polynomial.C (algebraMap (Base k) (BaseAway k 1) r) := by
  exact AlgHom.congr_fun (chartMapD_comp_baseMap k) r


-- @@ L275-282 verbatim
/-- Algebraic independence of `a,d,u` in the determinant quotient. -/
theorem baseMap_injective [IsDomain k] : Function.Injective (baseMap (k := k)) := by
  intro r s h
  have h' := congrArg (chartMapA k) h
  simp only [chartMapA_baseMap] at h'
  apply IsLocalization.injective (BaseAway k 0)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (MvPolynomial.X_ne_zero (0 : Fin 3)))
  exact Polynomial.C_injective h'


-- @@ L284-287 verbatim
/-- Compatibility with the actual polynomial coefficient algebra. -/
noncomputable def chartMapAOverBase : C k →ₐ[Base k] Chart k 0 where
  __ := (chartMapA k).toRingHom
  commutes' r := chartMapA_baseMap k r


-- @@ L289-292 verbatim
/-- Compatibility with the actual polynomial coefficient algebra. -/
noncomputable def chartMapDOverBase : C k →ₐ[Base k] Chart k 1 where
  __ := (chartMapD k).toRingHom
  commutes' r := chartMapD_baseMap k r


-- @@ L294-295 verbatim
noncomputable instance coefficientAlgebraA : Algebra (BaseAway k 0) (AwayA k) :=
  (coefficientFromChartA k).toRingHom.toAlgebra

-- @@ L296-297 verbatim
noncomputable instance coefficientAlgebraD : Algebra (BaseAway k 1) (AwayD k) :=
  (coefficientFromChartD k).toRingHom.toAlgebra


-- @@ L299-300 verbatim
instance coefficientScalarTowerA : IsScalarTower k (BaseAway k 0) (AwayA k) :=
  IsScalarTower.of_algHom (coefficientFromChartA k)

-- @@ L301-302 verbatim
instance coefficientScalarTowerD : IsScalarTower k (BaseAway k 1) (AwayD k) :=
  IsScalarTower.of_algHom (coefficientFromChartD k)


-- @@ L304-310 verbatim
instance baseCoefficientScalarTowerA : IsScalarTower (Base k) (BaseAway k 0) (AwayA k) := by
  apply IsScalarTower.of_algebraMap_eq
  intro r
  change algebraMap (Base k) (AwayA k) r =
    coefficientFromChartA k (algebraMap (Base k) (BaseAway k 0) r)
  rw [coefficientFromChartA_algebraMap]
  rfl


-- @@ L312-318 verbatim
instance baseCoefficientScalarTowerD : IsScalarTower (Base k) (BaseAway k 1) (AwayD k) := by
  apply IsScalarTower.of_algebraMap_eq
  intro r
  change algebraMap (Base k) (AwayD k) r =
    coefficientFromChartD k (algebraMap (Base k) (BaseAway k 1) r)
  rw [coefficientFromChartD_algebraMap]
  rfl


-- @@ L320-326 verbatim
/-- The a-chart equivalence, over its full localized coefficient ring. -/
noncomputable def chartEquivAOverCoefficients : AwayA k ≃ₐ[BaseAway k 0] Chart k 0 where
  __ := (chartEquivA k).toRingEquiv
  commutes' r := by
    change toChartA k (coefficientFromChartA k r) = Polynomial.C r
    have h := AlgHom.congr_fun (toChartA_comp_fromChartA k) (Polynomial.C r)
    simpa using h


-- @@ L328-334 verbatim
/-- The d-chart equivalence, over its full localized coefficient ring. -/
noncomputable def chartEquivDOverCoefficients : AwayD k ≃ₐ[BaseAway k 1] Chart k 1 where
  __ := (chartEquivD k).toRingEquiv
  commutes' r := by
    change toChartD k (coefficientFromChartD k r) = Polynomial.C r
    have h := AlgHom.congr_fun (toChartD_comp_fromChartD k) (Polynomial.C r)
    simpa using h


-- @@ L336-348 verbatim
/-- Chart injectivity follows from the domain property, not an assumed chart inclusion. -/
theorem chartMapA_injective [IsDomain k] [IsDomain (C k)] :
    Function.Injective (chartMapA k) := by
  have ha : a k ≠ 0 := by
    intro h
    apply MvPolynomial.X_ne_zero (0 : Fin 3) (R := k)
    apply baseMap_injective k
    simpa using h
  intro r s h
  apply IsLocalization.injective (AwayA k) (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
  apply (chartEquivA k).injective
  change toChartA k _ = toChartA k _
  simpa using h


-- @@ L350-362 verbatim
/-- Chart injectivity follows from the domain property, not an assumed chart inclusion. -/
theorem chartMapD_injective [IsDomain k] [IsDomain (C k)] :
    Function.Injective (chartMapD k) := by
  have hd : d k ≠ 0 := by
    intro h
    apply MvPolynomial.X_ne_zero (1 : Fin 3) (R := k)
    apply baseMap_injective k
    simpa using h
  intro r s h
  apply IsLocalization.injective (AwayD k) (powers_le_nonZeroDivisors_of_noZeroDivisors hd)
  apply (chartEquivD k).injective
  change toChartD k _ = toChartD k _
  simpa using h


-- @@ L364-364 verbatim
end StableCoordinate.DeterminantRing


-- @@ L366-366 verbatim
end OAI
