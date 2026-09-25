module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.CommonNeighbors44.Aux
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.CommonNeighbors44.Moments.Core
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.CommonNeighbors44.Moments.IndPoly
import SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.AvgLemmas24


-- @@ L7-16 verbatim
/-!
# Design reduction for the indicator sum

The function `x ↦ indPoly (⟪x,u⟫) * indPoly (⟪x,v⟫)` has total degree at most `10` after expansion.
Using the design axiom `EqCase24Pkg.design11`, its finite average over `C` equals the spherical
average over `S23`.

## Main statements
* `CommonNeighbors44Steps.finsetAvg_indPoly_mul_indPoly_eq_sphereAvg`
-/



-- @@ L19-19 verbatim
namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14.CommonNeighbors44Steps


-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
open scoped RealInnerProductSpace BigOperators


-- @@ L25-25 verbatim
open MeasureTheory Set


-- @@ L27-27 verbatim
open Uniqueness.BS81.Thm14

-- @@ L28-28 verbatim
open CommonNeighbors44Aux


-- @@ L30-30 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)


-- @@ L32-40 verbatim
/-- Design reduction for the common-neighbor indicator product: `finsetAvg = sphereAvg24`. -/
public theorem finsetAvg_indPoly_mul_indPoly_eq_sphereAvg
    (C : Set ℝ²⁴) (h : EqCase24Pkg C)
    {u v : ℝ²⁴} (hu : u ∈ C) (hv : v ∈ C) :
    finsetAvg h.code.finite.toFinset
        (fun x : ℝ²⁴ => indPoly (⟪x, u⟫ : ℝ) * indPoly (⟪x, v⟫ : ℝ)) =
      sphereAvg24 (fun x : ℝ²⁴ => indPoly (⟪x, u⟫ : ℝ) * indPoly (⟪x, v⟫ : ℝ)) := by
  simpa using
    (CommonNeighbors44Aux.finsetAvg_indPoly_mul_indPoly_eq_sphereAvg_of_pkg (h := h) hu hv)


-- @@ L42-42 verbatim
end


-- @@ L44-44 verbatim
end SpherePacking.Dim24.Uniqueness.BS81.Thm14.CommonNeighbors44Steps
