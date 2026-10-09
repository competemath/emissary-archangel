import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
universe u

-- @@ L8-8 verbatim
namespace Problem346


-- @@ L10-10 verbatim
variable (W : Type u) [AddCommGroup W] [Module ℂ W]


-- @@ L12-29 verbatim
/-- Linear functionals separate points of the symmetric algebra over an infinite field. -/
theorem symAlg_eq_zero_of_lift_eq_zero (p : SymmetricAlgebra ℂ W)
    (h : ∀ φ : Module.Dual ℂ W, SymmetricAlgebra.lift φ p = 0) : p = 0 := by
  classical
  let b := Module.Free.chooseBasis ℂ W
  let e := SymmetricAlgebra.equivMvPolynomial b
  apply e.injective
  simp only [map_zero]
  apply MvPolynomial.funext
  intro x
  have he : (MvPolynomial.aeval x).comp e.toAlgHom =
      SymmetricAlgebra.lift (b.constr ℂ x) := by
    apply SymmetricAlgebra.algHom_ext
    apply b.ext
    intro i
    simp [e]
  have hx := congrArg (fun f : SymmetricAlgebra ℂ W →ₐ[ℂ] ℂ => f p) he
  simpa using hx.trans (h (b.constr ℂ x))


-- @@ L31-39 verbatim
/-- Evaluation at vectors separates the symmetric algebra on the dual of a finite-dimensional
space. -/
theorem symAlg_dual_eq_zero_of_eval_eq_zero [FiniteDimensional ℂ W]
    (p : SymmetricAlgebra ℂ (Module.Dual ℂ W))
    (h : ∀ x : W, SymmetricAlgebra.lift (Module.Dual.eval ℂ W x) p = 0) : p = 0 := by
  apply symAlg_eq_zero_of_lift_eq_zero
  intro φ
  obtain ⟨x, rfl⟩ := (Module.evalEquiv ℂ W).surjective φ
  exact h x


-- @@ L41-41 verbatim
end Problem346


-- @@ L43-43 verbatim
end


-- @@ L45-45 verbatim
end OAI
