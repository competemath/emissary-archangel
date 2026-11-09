import ModularCurves.ForMathlib.SheafCohomologyFiniteProducts
import ModularCurves.ForMathlib.SheafOrderedCechSheafResolution


-- @@ L4-9 verbatim
/-!
# Cohomology of ordered sheaf-level Cech terms

Finite ordered Cech terms inherit cohomology vanishing from their
restriction-pushforward factors.
-/


-- @@ L11-11 verbatim
open CategoryTheory CategoryTheory.Limits TopologicalSpace


-- @@ L13-13 verbatim
universe u


-- @@ L15-15 verbatim
namespace TopCat.Sheaf


-- @@ L17-17 verbatim
open AlgebraicGeometry.Scheme.Modules


-- @@ L19-19 verbatim
variable {X : TopCat.{u}}

-- @@ L20-20 verbatim
variable (F : Sheaf AddCommGrpCat.{u} X)

-- @@ L21-21 verbatim
variable {ι : Type u} [LinearOrder ι] (U : ι → Opens X)


-- @@ L23-33 verbatim
/-- A finite ordered Cech term has vanishing cohomology in a degree whenever
all of its restriction-pushforward factors do. -/
theorem orderedCechTerm_subsingleton_H_of_factors [Finite ι]
    (n q : ℕ)
    (h : ∀ i : OrderedCechIndex ι n,
      Subsingleton (H (orderedCechTermFactor F U n i) q)) :
    Subsingleton (H (orderedCechTerm F U n) q) := by
  letI : Finite (OrderedCechIndex ι n) :=
    Finite.of_injective (fun i => i.1) Subtype.val_injective
  exact CategoryTheory.Sheaf.H.subsingleton_product_of_factors
    (orderedCechTermFactor F U n) q h


-- @@ L35-35 verbatim
end TopCat.Sheaf
