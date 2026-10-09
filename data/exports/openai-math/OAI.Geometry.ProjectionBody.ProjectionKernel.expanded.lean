import OAI.Geometry.ProjectionBody.Definitions


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
namespace ProjectionCounterexample


-- @@ L9-10 verbatim
@[simp] theorem project_self {d : ℕ} (u : E d) : project u u = 0 :=
  Submodule.starProjection_orthogonalComplement_singleton_eq_zero u


-- @@ L12-15 verbatim
theorem project_ker {d : ℕ} (u : E d) :
    (project u).toLinearMap.ker = Submodule.span ℝ {u} := by
  change (ℝ ∙ u)ᗮ.starProjection.ker = ℝ ∙ u
  rw [Submodule.ker_starProjection, Submodule.orthogonal_orthogonal]


-- @@ L17-17 verbatim
end ProjectionCounterexample


-- @@ L19-19 verbatim
end


-- @@ L21-21 verbatim
end OAI
