import OAI.AlgebraicGeometry.CommutingDerivations.ParameterBezout
import OAI.AlgebraicGeometry.AbhyankarSathaye.Reconstruction
import OAI.AlgebraicGeometry.AbhyankarSathaye.Quotient
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Fin.VecNotation


-- @@ L8-8 verbatim
namespace OAI


-- @@ L10-13 verbatim
/-!
The Laurent coefficient algebra and localization coordinates.
The coefficient map is the lift of `t ↦ F + 1`.
-/

-- @@ L14-14 verbatim
noncomputable section

-- @@ L15-15 verbatim
namespace AbhyankarSathaye.CommutingDerivations

-- @@ L16-16 verbatim
open MvPolynomial


-- @@ L18-18 verbatim
def ambientC : R := F + 1

-- @@ L19-19 verbatim
abbrev LocalizedAmbient := Localization.Away ambientC

-- @@ L20-20 verbatim
abbrev LaurentCoefficients := Localization.Away (Polynomial.X : Polynomial ℂ)

-- @@ L21-21 verbatim
abbrev RelativePlane := MvPolynomial (Fin 3) LaurentCoefficients


-- @@ L23-23 verbatim
def loc : R →+* LocalizedAmbient := algebraMap R LocalizedAmbient

-- @@ L24-25 verbatim
def coefficientC : LaurentCoefficients :=
  algebraMap (Polynomial ℂ) LaurentCoefficients Polynomial.X

-- @@ L26-27 verbatim
def coefficientD : LaurentCoefficients :=
  IsLocalization.Away.invSelf (Polynomial.X : Polynomial ℂ)

-- @@ L28-28 verbatim
def localD : LocalizedAmbient := IsLocalization.Away.invSelf ambientC


-- @@ L30-31 verbatim
theorem coefficient_unit : coefficientC * coefficientD = 1 :=
  IsLocalization.Away.mul_invSelf _


-- @@ L33-34 verbatim
theorem local_unit : loc ambientC * localD = 1 :=
  IsLocalization.Away.mul_invSelf _


-- @@ L36-37 verbatim
def polynomialCoefficientMap : Polynomial ℂ →+* LocalizedAmbient :=
  (Polynomial.aeval (loc ambientC)).toRingHom


-- @@ L39-44 verbatim
def coefficientMap : LaurentCoefficients →+* LocalizedAmbient :=
  IsLocalization.Away.lift Polynomial.X
    (by
      refine ⟨⟨polynomialCoefficientMap Polynomial.X, localD, ?_, ?_⟩, rfl⟩
      · simpa [polynomialCoefficientMap] using local_unit
      · simpa [polynomialCoefficientMap, mul_comm] using local_unit)


-- @@ L46-47 verbatim
@[simp] theorem coefficientMap_C : coefficientMap coefficientC = loc ambientC := by
  simp [coefficientMap, coefficientC, polynomialCoefficientMap]


-- @@ L49-56 verbatim
@[simp] theorem coefficientMap_D : coefficientMap coefficientD = localD := by
  have h1 : loc ambientC * coefficientMap coefficientD = 1 := by
    simpa using congrArg coefficientMap coefficient_unit
  calc
    coefficientMap coefficientD = (loc ambientC * localD) * coefficientMap coefficientD := by
      rw [local_unit, one_mul]
    _ = localD * (loc ambientC * coefficientMap coefficientD) := by ring
    _ = localD := by rw [h1, mul_one]


-- @@ L58-58 verbatim
def localAlpha : LocalizedAmbient := localD^2 * parameterA (loc ambientC) (loc x) (loc s)

-- @@ L59-60 verbatim
def localBeta : LocalizedAmbient :=
  localD^2 * parameterB (loc ambientC) (loc x) (loc y) (loc s)

-- @@ L61-61 verbatim
def localT : LocalizedAmbient := parameter localAlpha localBeta (loc u) (loc v) (loc w)

-- @@ L62-62 verbatim
def localCoordinates : Fin 3 → LocalizedAmbient := ![loc shiftX, loc shiftY, localT]


-- @@ L64-65 verbatim
theorem local_cusp : (loc x)^2 + (loc y)^3 = loc s * loc h := by
  simpa [mul_comm] using congrArg loc cusp


-- @@ L67-69 verbatim
theorem local_section : loc h = loc ambientC + P (loc x) (loc y) (loc s) := by
  have he : h = ambientC + P x y s := by unfold ambientC F p; ring
  simpa using congrArg loc he


-- @@ L71-72 verbatim
theorem local_bezout : localAlpha * loc h + localBeta * loc y = 1 :=
  parameter_bezout_unit _ _ _ _ _ _ local_cusp local_section local_unit


-- @@ L74-76 verbatim
theorem local_recover_s : localD * ((loc shiftX)^2 + (loc shiftY)^3) = loc s := by
  simpa [shiftX, shiftY] using
    parameter_recover_s _ _ _ _ _ _ local_cusp local_section local_unit


-- @@ L78-80 verbatim
/-- Evaluation at the displayed X,Y,T, with the explicit relative coefficient map. -/
def relativeBackward : RelativePlane →+* LocalizedAmbient :=
  eval₂Hom coefficientMap localCoordinates


-- @@ L82-84 verbatim
@[simp] theorem relativeBackward_C (a : LaurentCoefficients) :
    relativeBackward (C a) = coefficientMap a := by
  simp [relativeBackward]


-- @@ L86-88 verbatim
@[simp] theorem relativeBackward_X (i : Fin 3) :
    relativeBackward (X i) = localCoordinates i := by
  simp [relativeBackward]


-- @@ L90-96 verbatim
/-- A relative algebra equivalence over `ℂ[c,c⁻¹]`, with `c = F + 1`,
and its coordinate equations. -/
def RelativeLocalizationContract : Prop :=
  ∃ e : LocalizedAmbient ≃+* RelativePlane,
    (∀ a, e (coefficientMap a) = C a) ∧
    e (loc shiftX) = X 0 ∧ e (loc shiftY) = X 1 ∧ e localT = X 2 ∧
    e.symm.toRingHom = relativeBackward


-- @@ L98-98 verbatim
end AbhyankarSathaye.CommutingDerivations


-- @@ L100-100 verbatim
end


-- @@ L102-102 verbatim
end OAI
