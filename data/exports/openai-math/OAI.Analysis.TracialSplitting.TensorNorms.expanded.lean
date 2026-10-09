import OAI.Analysis.TracialSplitting.FinitePacking


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe uE uF uN uR



-- @@ L8-8 verbatim
section


-- @@ L10-10 verbatim
noncomputable section


-- @@ L12-12 verbatim
namespace Pureness


-- @@ L14-14 verbatim
namespace CStarAlgebraNorm


-- @@ L16-16 verbatim
variable {R : Type uR} [Ring R] [StarRing R] [Algebra ℂ R]


-- @@ L18-29 verbatim
def ofFaithful {N : Type uN} [CStarAlgebra N]
    (f : R →⋆ₐ[ℂ] N) (hf : Function.Injective f) : CStarAlgebraNorm R where
  toFun x := ‖f x‖
  map_zero' := by simp
  add_le' x y := by simpa only [map_add] using norm_add_le (f x) (f y)
  neg' x := by simp
  mul_le' x y := by simpa only [map_mul] using norm_mul_le (f x) (f y)
  eq_zero_of_map_eq_zero' x hx := hf (by simpa using norm_eq_zero.mp hx)
  smul' c x := by simp [norm_smul]
  cstar x := by
    change ‖f (star x * x)‖ = ‖f x‖ * ‖f x‖
    rw [map_mul, map_star, CStarRing.norm_star_mul_self]


-- @@ L31-33 verbatim
@[simp] lemma ofFaithful_apply {N : Type uN} [CStarAlgebra N]
    (f : R →⋆ₐ[ℂ] N) (hf : Function.Injective f) (x : R) :
    (ofFaithful f hf).toAlgebraNorm x = ‖f x‖ := rfl


-- @@ L35-35 verbatim
end CStarAlgebraNorm


-- @@ L37-37 verbatim
open scoped TensorProduct


-- @@ L39-39 verbatim
universe u v


-- @@ L41-41 verbatim
variable {A : Type u} [CStarAlgebra A] {B : Type v} [CStarAlgebra B]


-- @@ L43-50 verbatim
theorem IsNuclear.faithful_tensor_norm_eq (hA : IsNuclear.{u, v} A)
    {E : Type uE} {F : Type uF} [CStarAlgebra E] [CStarAlgebra F]
    (f : A ⊗[ℂ] B →⋆ₐ[ℂ] E) (g : A ⊗[ℂ] B →⋆ₐ[ℂ] F)
    (hf : Function.Injective f) (hg : Function.Injective g) (z : A ⊗[ℂ] B) :
    ‖f z‖ = ‖g z‖ := by
  have he := (hA B).elim (CStarAlgebraNorm.ofFaithful f hf)
    (CStarAlgebraNorm.ofFaithful g hg)
  exact congrArg (fun p : CStarAlgebraNorm (A ⊗[ℂ] B) => p.toAlgebraNorm z) he


-- @@ L52-62 verbatim
theorem IsNuclear.tensor_norm_le_faithful (hA : IsNuclear.{u, v} A)
    {E : Type uE} {F : Type uF} [CStarAlgebra E] [CStarAlgebra F]
    (f : A ⊗[ℂ] B →⋆ₐ[ℂ] E) (g : A ⊗[ℂ] B →⋆ₐ[ℂ] F)
    (hg : Function.Injective g) (z : A ⊗[ℂ] B) :
    ‖f z‖ ≤ ‖g z‖ := by
  let fg := f.prod g
  have hfg : Function.Injective fg := by
    intro x y h
    exact hg (congrArg Prod.snd h)
  have he := hA.faithful_tensor_norm_eq fg g hfg hg z
  exact (norm_fst_le (fg z)).trans_eq he


-- @@ L64-64 verbatim
end Pureness


-- @@ L66-66 verbatim
end


-- @@ L68-68 verbatim
end


-- @@ L70-70 verbatim
end OAI
