import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceCanonicallyOver
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorPullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.Paper.S1Intro.TangentBundlePullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundlePullback
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.EvaluateHomogeneousAtSections
import MiyaokaMori.AlgebraicGeometry.Modules.HomogeneousEquationAsSection
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafToModules
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ModulesLineBundleZpow
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPower
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceVectorBundle
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundlePullback
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleTensorPower
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotSectionsPolynomial
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.SubstitutedPolynomialDegreeBridge
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.NefPullback


-- @@ L26-30 verbatim
/-! # Degree of the substituted polynomials

Substituting `P_ℓ` into the homogeneous equation `F_j` of degree `d_j`: the `ξ`-degree is `≤ d_j·r₀`, and the
coefficient of `ξ^q` lies in `H^0(ρ^*A^{⊗d_j}⊗L^{-q})` (proof of Theorem 4.2 of the paper).
-/


-- @@ L32-32 verbatim
set_option autoImplicit false

-- @@ L33-33 verbatim
set_option maxHeartbeats 400000


-- @@ L35-35 verbatim
universe u v w u' v'


-- @@ L37-37 verbatim
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

-- @@ L38-38 verbatim
open scoped AlgebraicGeometry


-- @@ L40-40 verbatim
noncomputable section


-- @@ L42-58 verbatim
theorem substituted_equation_degree {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} {N r₀ dj : ℕ}
    (L M : LineBundle C.toVariety)
    (P : Fin (N + 1) →
      (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u))
    (hP : ∀ ℓ, xiDegree L M (P ℓ) ≤ (r₀ : WithBot ℕ))
    (F : MvPolynomial (Fin (N + 1)) k) (hF : F.IsHomogeneous dj)
    (θ : AlgebraicGeometry.Scheme.Modules.tensorPow
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules) dj ≅
      (AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj (M.zpow dj).toModules) :
    xiDegree L (M.zpow dj)
        (θ.hom.app ⊤ (evalHomogeneousAtSections _ F hF P)) ≤ ((dj * r₀ : ℕ) : WithBot ℕ) := by
  exact xiDegree_evalHomogeneousAtSections_le L M P hP F hF θ


-- @@ L60-60 verbatim
end
