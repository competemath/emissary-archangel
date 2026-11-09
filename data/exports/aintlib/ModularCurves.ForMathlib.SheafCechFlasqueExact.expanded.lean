import ModularCurves.ForMathlib.SheafCechAcyclicComparison
import ModularCurves.ForMathlib.SheafCechFlasqueTerms


-- @@ L4-10 verbatim
/-!
# Exactness of Cech complexes of flasque sheaves

For a finite open cover, every positive cohomology group of every Cech term of
a flasque sheaf vanishes. The acyclic-cover comparison therefore makes its
native Cech complex exact in every positive degree.
-/


-- @@ L12-12 verbatim
open CategoryTheory TopologicalSpace


-- @@ L14-14 verbatim
universe u


-- @@ L16-16 verbatim
namespace TopCat.Sheaf


-- @@ L18-18 verbatim
variable {X : TopCat.{u}}

-- @@ L19-19 verbatim
variable {ι : Type u} (U : ι → Opens X)


-- @@ L21-31 verbatim
/-- The native Cech complex of a flasque sheaf is exact in every positive
degree for a finite open cover. -/
theorem cechComplex_exactAt_succ_of_isFlasque [Finite ι]
    (F : Sheaf AddCommGrpCat.{u} X) [IsFlasque F]
    (hU : ⨆ i, U i = ⊤) (n : ℕ) :
    ((cechComplexFunctor U).obj F.obj).ExactAt (n + 1) := by
  apply cechComplex_exactAt_succ_of_subsingleton_H F U hU
  · intro p q hq
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    exact cechTerm_subsingleton_H_of_isFlasque F U p r
  · exact IsFlasque.subsingleton_H n


-- @@ L33-33 verbatim
end TopCat.Sheaf
