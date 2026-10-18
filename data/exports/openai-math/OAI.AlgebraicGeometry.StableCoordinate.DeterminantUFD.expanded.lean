import OAI.AlgebraicGeometry.StableCoordinate.DeterminantPrimeA
import OAI.AlgebraicGeometry.StableCoordinate.DeterminantCharts
import Mathlib.RingTheory.Ideal.UFD


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-13 verbatim
/-!
# Unique factorization in the determinant ring

The prime element `a` has a localization which is a polynomial algebra over a
localization of a polynomial algebra.  Nagata's prime-element criterion then
proves unique factorization in the actual determinant quotient.
-/


-- @@ L15-15 verbatim
namespace StableCoordinate.DeterminantRing


-- @@ L17-17 verbatim
variable (k : Type*) [CommRing k] [IsNoetherianRing k]


-- @@ L19-19 verbatim
variable [IsDomain k] [UniqueFactorizationMonoid k]


-- @@ L21-21 verbatim
instance C_isNoetherianRing : IsNoetherianRing (C k) := inferInstance


-- @@ L23-25 verbatim
noncomputable instance C_uniqueFactorizationMonoid : UniqueFactorizationMonoid (C k) := by
  apply (UniqueFactorizationMonoid.iff_localizationAway_of_prime (a_prime k)).mpr
  exact (chartEquivA k).symm.toMulEquiv.uniqueFactorizationMonoid inferInstance


-- @@ L27-27 verbatim
end StableCoordinate.DeterminantRing


-- @@ L29-29 verbatim
namespace StableCoordinate.Obstruction


-- @@ L31-31 verbatim
variable (k : Type*) [CommRing k] [IsNoetherianRing k]


-- @@ L33-33 verbatim
instance C_isNoetherianRing : IsNoetherianRing (C k) := inferInstance


-- @@ L35-35 verbatim
variable [IsDomain k] [UniqueFactorizationMonoid k]


-- @@ L37-39 verbatim
/-- The canonical obstruction presentation is definitionally the determinant ring. -/
noncomputable instance C_uniqueFactorizationMonoid : UniqueFactorizationMonoid (C k) :=
  DeterminantRing.C_uniqueFactorizationMonoid k


-- @@ L41-41 verbatim
end StableCoordinate.Obstruction


-- @@ L43-43 verbatim
end OAI
