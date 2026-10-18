import OAI.AlgebraicGeometry.StableCoordinate.NonzeroFiberTransport
import OAI.AlgebraicGeometry.StableCoordinate.Presentation


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-12 verbatim
/-!
# Nonzero fibers of the four-variable polynomial

The matrix presentation identifies its distinguished element with exactly
`StableCoordinate.f`.  Composing that presentation with the nonzero-fiber calculation gives an
affine coordinate-algebra isomorphism for every nonzero complex parameter.
-/


-- @@ L14-14 verbatim
noncomputable section


-- @@ L16-16 verbatim
namespace StableCoordinate


-- @@ L18-22 verbatim
/-- Every nonzero complex fiber of the exact polynomial has affine-three-space
coordinate algebra. The zero fiber is treated in `ZeroFiberExact`. -/
def exactNonzeroFiberEquiv (l : ℂ) (hl : l≠0) : FiberRing l ≃ₐ[ℂ] R 3 :=
  NonzeroFiber.transportedFiberEquiv Presentation.originalPresentation f
    Presentation.originalPresentation_p l hl


-- @@ L24-26 verbatim
theorem isAffineThreeSpaceFiber_of_ne_zero (l : ℂ) (hl : l≠0) :
    IsAffineThreeSpaceFiber l :=
  ⟨exactNonzeroFiberEquiv l hl⟩


-- @@ L28-28 verbatim
end StableCoordinate


-- @@ L30-30 verbatim
end


-- @@ L32-32 verbatim
end OAI
