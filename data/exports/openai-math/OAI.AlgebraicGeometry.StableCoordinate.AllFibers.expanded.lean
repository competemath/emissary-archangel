import OAI.AlgebraicGeometry.StableCoordinate.NonzeroFiberAssembly
import OAI.AlgebraicGeometry.StableCoordinate.ZeroFiberExact
import OAI.AlgebraicGeometry.StableCoordinate.Rectifiability


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-13 verbatim
/-!
# Every complex fiber of the exact polynomial

The two explicit quotient-algebra calculations cover every parameter, including
zero. Together with the noncoordinate theorem, these equivalences show that every
fiber is affine three-space and its embedding is nonrectifiable.
-/


-- @@ L15-15 verbatim
namespace StableCoordinate


-- @@ L17-25 verbatim
/-- Every complex fiber of the specified polynomial has the coordinate algebra
of affine three-space, with no exceptional parameters. -/
theorem all_fibers_isAffineThreeSpace :
    ∀ t : ℂ, IsAffineThreeSpaceFiber t := by
  intro t
  by_cases ht : t = 0
  · subst t
    exact zeroFiber_isAffineThreeSpace
  · exact isAffineThreeSpaceFiber_of_ne_zero t ht


-- @@ L27-29 verbatim
/-- An actual complex algebra equivalence for each fiber. -/
noncomputable def exactFiberEquiv (t : ℂ) : FiberRing t ≃ₐ[ℂ] R 3 :=
  Classical.choice (all_fibers_isAffineThreeSpace t)


-- @@ L31-35 verbatim
/-- With the unrestricted four-variable coordinate obstruction, the already
proved all-fiber calculation supplies the entire geometric principal group. -/
theorem fiberPackage_of_noncoordinate
    (h : ¬ IsCoordinate (by decide : 0 < 4) f) : FiberPackage :=
  fiberPackage_of_noncoordinate_of_affine h all_fibers_isAffineThreeSpace


-- @@ L37-37 verbatim
end StableCoordinate


-- @@ L39-39 verbatim
end OAI
