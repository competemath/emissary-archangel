import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.EvaluateHomogeneousAtSections
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesPow
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModulesPowLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPower
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SheafSymmetricAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceSectionEquiv
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceVectorBundle


-- @@ L13-19 verbatim
/-! # A homogeneous equation as a section on the total space

The global function on `Tot(A^{⊕(N+1)})` given by `F_j`: substituting the `N+1` coordinates of the
tautological section into the homogeneous polynomial `F_j` of degree `e_j` yields a global section of
the tensor power `(π^*A)^{⊗ e_j}` (`≅ π^*(A^{⊗ e_j})`) of the pulled-back line bundle (in the paper:
"interpreted as a section of the corresponding power of `A`").
-/


-- @@ L21-21 verbatim
set_option autoImplicit false

-- @@ L22-22 verbatim
set_option maxHeartbeats 400000


-- @@ L24-24 verbatim
universe u v w u' v'


-- @@ L26-26 verbatim
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

-- @@ L27-27 verbatim
open scoped AlgebraicGeometry


-- @@ L29-35 verbatim
noncomputable section

/- Write `V := A^{⊕(N+1)}`, `π : Tot(V) → X`. `τ ∈ Γ(Tot V, π^*V)` is the tautological section
   (corresponding to `𝟙` under `totalSpaceHomEquiv`), and `τ_i := π^*(pr_i)(τ) ∈ Γ(Tot V, π^*A)` is
   its `i`-th coordinate; `Tot V` is a `k`-scheme via `π`, and substituting `τ_0, …, τ_N` into the
   homogeneous `F` of degree `e` (`evalHomogeneousAtSections`) gives `F(τ) ∈ Γ(Tot V, (π^*A)^{⊗e})`.
   The target is `(π^*A)^{⊗e}` (`≅ π^*(A^{⊗e})`, pullback being monoidal). -/


-- @@ L37-57 verbatim
noncomputable def homogeneousEquationSection {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (A : X.Modules) [A.IsLineBundle]
    (N : ℕ) {e : ℕ} (F : MvPolynomial (Fin (N + 1)) k) (hF : F.IsHomogeneous e) :
    ((AlgebraicGeometry.Scheme.Modules.tensorPow
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom).obj A)
        e).val.obj (Opposite.op ⊤) : Type u) :=
  letI : (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).left.Over
      (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨(AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom ≫
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  evalHomogeneousAtSections
    ((AlgebraicGeometry.Scheme.Modules.pullback
      (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom).obj A)
    F hF
    (fun i => ((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom).map
          (CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) i)).val.app (Opposite.op ⊤)
      (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))
        (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1)))
        (CategoryTheory.CategoryStruct.id _)))


-- @@ L59-59 verbatim
end
