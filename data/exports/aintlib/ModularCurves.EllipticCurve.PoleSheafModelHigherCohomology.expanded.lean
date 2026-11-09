import ModularCurves.EllipticCurve.PoleSheafModelHOne
import ModularCurves.ForMathlib.AcyclicAffineOpenCoverHPrime


-- @@ L4-10 verbatim
/-!
# Higher cohomology of pole sheaves on Weierstrass models

The canonical affine `Z`-chart and affine section neighborhood cover a projective
Weierstrass model. Mayer--Vietoris therefore gives vanishing above degree one for
every quasicoherent pole sheaf.
-/


-- @@ L12-12 verbatim
open AlgebraicGeometry CategoryTheory TopologicalSpace


-- @@ L14-14 verbatim
universe u


-- @@ L16-16 verbatim
namespace ModularCurves


-- @@ L18-18 verbatim
variable {K : Type u} [Field K]


-- @@ L20-37 verbatim
/-- On an elliptic projective Weierstrass model, every pole sheaf has vanishing
cohomology in degrees at least two. -/
theorem sectionPoleSheafPower_projModel_subsingleton_H_add_two
    (W : WeierstrassCurve K) [W.IsElliptic] (n q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower (projModelπ W) (projModelZero W)
        (projModelZero_projModelπ W) n).sheaf (q + 2)) := by
  let M := sectionPoleSheafPower (projModelπ W) (projModelZero W)
    (projModelZero_projModelπ W) n
  let N := projModelSectionNeighborhood W
  let Z := projModelZChart W
  letI : M.IsQuasicoherent :=
    sectionPoleSheafPower_isQuasicoherent (projModel_smooth W)
      (projModelZero W) (projModelZero_projModelπ W) n
  exact AlgebraicGeometry.Scheme.Modules.subsingleton_H_add_two_of_two_affine_open_cover
    M N Z N.2 Z.2 (by
      rw [sup_comm]
      exact projModelZChart_sup_sectionNeighborhood_eq_top W) q


-- @@ L39-39 verbatim
end ModularCurves
