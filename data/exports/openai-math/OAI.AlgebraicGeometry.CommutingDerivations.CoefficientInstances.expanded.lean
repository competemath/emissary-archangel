import OAI.AlgebraicGeometry.CommutingDerivations.LocalizationSetup
import Mathlib.Algebra.CharP.Algebra


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-7 verbatim
/-! The concrete Laurent coefficient ring is a characteristic-zero domain.
These instances are consequences of its actual localization construction. -/

-- @@ L8-8 verbatim
noncomputable section

-- @@ L9-9 verbatim
namespace AbhyankarSathaye.CommutingDerivations


-- @@ L11-12 verbatim
instance laurentCoefficients_isDomain : IsDomain LaurentCoefficients :=
  Localization.Away.isDomain (Polynomial.X_ne_zero : (Polynomial.X : Polynomial ℂ) ≠ 0)


-- @@ L14-15 verbatim
instance laurentCoefficients_charZero : CharZero LaurentCoefficients :=
  charZero_of_injective_algebraMap (algebraMap ℂ LaurentCoefficients).injective


-- @@ L17-17 verbatim
end AbhyankarSathaye.CommutingDerivations


-- @@ L19-19 verbatim
end


-- @@ L21-21 verbatim
end OAI
