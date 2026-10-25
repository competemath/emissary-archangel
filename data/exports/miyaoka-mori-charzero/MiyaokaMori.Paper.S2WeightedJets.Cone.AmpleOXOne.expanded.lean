import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.AmpleLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.OXOne
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceTwistAmple
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafToModules
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveEmbedding
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SerreTwistProjectiveSpace


-- @@ L11-15 verbatim
/-! # `O_X(1)` is ample

The line bundle `O_X(1)` given by the fixed projective embedding `X ⊂ ℙ^N` is ample (§2.1 of the
paper, where `A = f^*O_X(1)`).
-/


-- @@ L17-17 verbatim
set_option autoImplicit false

-- @@ L18-18 verbatim
set_option maxHeartbeats 400000


-- @@ L20-20 verbatim
universe u v w u' v'


-- @@ L22-22 verbatim
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

-- @@ L23-23 verbatim
open scoped AlgebraicGeometry


-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-37 verbatim
theorem ample_OX_one {k : Type u} [Field k] (X : SmoothProjectiveVariety k) :
    AlgebraicGeometry.IsAmple (X.OX 1).toModules := by
  let hOXLine : (X.OX 1).toModules.IsLineBundle := LineBundle.toModules_isLineBundle _
  let hEmbeddingLine : (X.embedding.oX 1).IsLineBundle := by
    unfold ProjectiveEmbedding.oX
    infer_instance
  change AlgebraicGeometry.IsAmple (X.embedding.oX 1)
  unfold ProjectiveEmbedding.oX
  exact AlgebraicGeometry.IsAmple.pullback_of_isClosedImmersion X.embedding.emb
    (projectiveSpaceTwist k X.embDim 1)
    (projectiveSpaceTwist_one_isAmple k X.embDim)


-- @@ L39-39 verbatim
end
