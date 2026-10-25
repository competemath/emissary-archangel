import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveEmbedding
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SerreTwistIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct


-- @@ L6-10 verbatim
/-! # The tautological bundle on `X` and the line bundle `ℳ` on `C × X`

`O_X(-1)` (the restriction to `X` of the tautological line bundle of `ℙ^N`), and
`ℳ = pr₁^*A ⊗ pr₂^*O_X(-1)` on `C × X` (§2.1 of the paper).
-/


-- @@ L12-12 verbatim
set_option autoImplicit false

-- @@ L13-13 verbatim
set_option maxHeartbeats 400000


-- @@ L15-15 verbatim
universe u v w u' v'


-- @@ L17-17 verbatim
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

-- @@ L18-18 verbatim
open scoped AlgebraicGeometry


-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-34 verbatim
/-- The line bundle `ℳ = pr₁^*A ⊗ pr₂^*O_X(-1)` on `C × X`, where `O_X(-1) = (e^*O_{ℙ^N}(1))^∨` is the
dual of the pullback of the twisting sheaf along the embedding `e`, `C × X` is the fiber product over
`Spec k`, and `pr_i^*` are the pullbacks of sheaves of modules. -/
noncomputable def conePuncturedLineBundle {k : Type u} [Field k] {C X : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N : ℕ}
    (e : ProjectiveEmbedding k X N) (A : C.Modules) [A.IsLineBundle] :
    (CategoryTheory.Limits.pullback (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))).Modules :=
  AlgebraicGeometry.Scheme.Modules.tensor
    ((AlgebraicGeometry.Scheme.Modules.pullback (CategoryTheory.Limits.pullback.fst _ _)).obj A)
    ((AlgebraicGeometry.Scheme.Modules.pullback (CategoryTheory.Limits.pullback.snd _ _)).obj
      (AlgebraicGeometry.Scheme.Modules.moduleSheafDual (e.oX 1)))


-- @@ L36-53 verbatim
/-- `ℳ` is a line bundle: `pr₁^*A` and `pr₂^*O_X(−1)` are line bundles, and the tensor product of line
bundles is a line bundle (Stacks 01CT). `conePuncturedLineBundle` is a plain `def`, which instance search
does not unfold, so the instance is registered explicitly; the `[IsLocallyFree]` needed by
`totalSpacePunctured` follows from the instance "line bundle ⇒ locally free". -/
instance conePuncturedLineBundle.isLineBundle {k : Type u} [Field k] {C X : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N : ℕ}
    (e : ProjectiveEmbedding k X N) (A : C.Modules) [A.IsLineBundle] :
    (conePuncturedLineBundle e A).IsLineBundle := by
  -- `O_{ℙ^N}(1) = projectiveSpaceTwist k N 1` is a line bundle (`projectiveSpaceTwist_isLineBundle`)
  have h1 : (projectiveSpaceTwist k N 1).IsLineBundle := projectiveSpaceTwist_isLineBundle k N 1
  -- `e^*O(1)` is a line bundle (pullback of a line bundle, `IsLineBundle.pullback`)
  have h2 : (e.oX 1).IsLineBundle :=
    @AlgebraicGeometry.Scheme.Modules.IsLineBundle.pullback _ _ e.emb (projectiveSpaceTwist k N 1) h1
  -- the dual (`moduleSheafDual_isLineBundle`), the two pullbacks and the tensor product (`IsLineBundle.tensor`)
  -- are all given by instances
  unfold conePuncturedLineBundle
  infer_instance


-- @@ L55-55 verbatim
end
