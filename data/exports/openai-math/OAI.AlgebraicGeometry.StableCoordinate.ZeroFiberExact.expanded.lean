import OAI.AlgebraicGeometry.StableCoordinate.ZeroFiberTransport
import OAI.AlgebraicGeometry.StableCoordinate.Presentation


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-13 verbatim
/-!
# The exact polynomial has affine-three-space zero fiber

The proved matrix presentation sends its distinguished parameter to the exact
polynomial `f`.  Transporting the explicit zero-fiber coordinate algebra
isomorphism therefore completes the zero case of Proposition 2.3 without
adding any assumptions to its headline statement.
-/


-- @@ L15-15 verbatim
noncomputable section

-- @@ L16-16 verbatim
namespace StableCoordinate


-- @@ L18-22 verbatim
/-- The fiber at zero of the exact degree-five polynomial is affine
three-space, expressed as an isomorphism of complex coordinate algebras. -/
def zeroFiberEquiv : FiberRing 0 ≃ₐ[ℂ] R 3 :=
  ZeroFiber.zeroFiberEquivOfPresentation
    Presentation.originalPresentation Presentation.originalPresentation_p


-- @@ L24-25 verbatim
theorem zeroFiber_isAffineThreeSpace : IsAffineThreeSpaceFiber 0 :=
  ⟨zeroFiberEquiv⟩


-- @@ L27-27 verbatim
end StableCoordinate


-- @@ L29-29 verbatim
end


-- @@ L31-31 verbatim
end OAI
