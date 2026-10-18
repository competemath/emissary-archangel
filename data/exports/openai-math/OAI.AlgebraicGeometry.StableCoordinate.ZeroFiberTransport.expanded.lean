import OAI.AlgebraicGeometry.StableCoordinate.ZeroFiberSpecialization
import OAI.AlgebraicGeometry.StableCoordinate.Definitions


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-12 verbatim
/-!
# Transporting the zero-fiber calculation through a polynomial presentation

The hypothesis of the helper below is a *proved algebra equivalence* to be
supplied by the matrix-change construction.  It does not assert or assume any
of the requested headline claims.
-/


-- @@ L14-14 verbatim
noncomputable section

-- @@ L15-15 verbatim
namespace StableCoordinate.ZeroFiber

-- @@ L16-16 verbatim
open MvPolynomial


-- @@ L18-28 verbatim
/-- Transport the already calculated zero fiber through a polynomial
presentation that takes the distinguished parameter to the exact polynomial.
This helper is instantiated by the explicit presentation construction. -/
def zeroFiberEquivOfPresentation
    (e : Hypersurface ℂ ≃ₐ[ℂ] R 4)
    (he : e (hypersurfaceMk ℂ (X 0)) = f) : FiberRing 0 ≃ₐ[ℂ] R 3 :=
  (Ideal.quotientEquivAlg (parameterIdeal ℂ) (fiberIdeal 0) e (by
    rw [parameterIdeal, Ideal.map_span, Set.image_singleton]
    change Ideal.span ({f - C (0 : ℂ)} : Set (R 4)) =
      Ideal.span ({e (hypersurfaceMk ℂ (X 0))} : Set (R 4))
    rw [he, map_zero, sub_zero])).symm.trans (sourceZeroFiberEquiv ℂ)


-- @@ L30-30 verbatim
end StableCoordinate.ZeroFiber


-- @@ L32-32 verbatim
end


-- @@ L34-34 verbatim
end OAI
