import Mathlib.Analysis.InnerProductSpace.Dual
import SphereEversion.ToMathlib.Analysis.InnerProductSpace.Projection.Submodule


-- @@ L4-4 verbatim
open scoped RealInnerProductSpace


-- @@ L6-6 verbatim
open Submodule InnerProductSpace


-- @@ L8-8 verbatim
open LinearMap (ker)


-- @@ L10-10 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]


-- @@ L12-12 verbatim
@[inherit_doc] local notation "Δ" => spanLine


-- @@ L14-14 verbatim
@[inherit_doc] local notation "{." x "}ᗮ" => spanOrthogonal x


-- @@ L16-16 verbatim
@[inherit_doc] local notation "pr[" x "]ᗮ" => projSpanOrthogonal x


-- @@ L18-24 expanded
theorem orthogonal_span_toDual_symm (π : E →L[ℝ] ℝ) :
    spanOrthogonal ((InnerProductSpace.toDual ℝ E).symm π) = π.ker :=
  by
  ext x
  suffices (∀ a : ℝ, ⟪a • (toDual ℝ E).symm π, x⟫ = 0) ↔ π x = 0 by simp
  refine ⟨fun h ↦ ?_, fun h _ ↦ ?_⟩
  · simpa using h 1
  · simp [inner_smul_left, h]

