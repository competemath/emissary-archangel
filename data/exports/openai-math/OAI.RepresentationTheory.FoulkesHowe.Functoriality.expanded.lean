import OAI.RepresentationTheory.FoulkesHowe.Model


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped BigOperators

-- @@ L7-7 verbatim
universe u v w

-- @@ L8-8 verbatim
namespace Problem346


-- @@ L10-12 verbatim
variable {V : Type u} {W : Type v} {U : Type w}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U]


-- @@ L14-16 verbatim
/-- The algebra map induced by a complex-linear map. -/
def symAlgMap (f : V →ₗ[ℂ] W) : SymmetricAlgebra ℂ V →ₐ[ℂ] SymmetricAlgebra ℂ W :=
  SymmetricAlgebra.lift ((SymmetricAlgebra.ι ℂ W).comp f)


-- @@ L18-20 verbatim
@[simp] theorem symAlgMap_ι (f : V →ₗ[ℂ] W) (x : V) :
    symAlgMap f (SymmetricAlgebra.ι ℂ V x) = SymmetricAlgebra.ι ℂ W (f x) := by
  simp [symAlgMap]


-- @@ L22-24 verbatim
@[simp] theorem symAlgMap_symMonomialRaw (n : ℕ) (f : V →ₗ[ℂ] W) (x : Fin n → V) :
    symAlgMap f (symMonomialRaw n V x) = symMonomialRaw n W (fun i => f (x i)) := by
  simp [symMonomialRaw]


-- @@ L26-38 verbatim
/-- Symmetric powers act covariantly on linear maps. -/
def symPowMap (n : ℕ) (f : V →ₗ[ℂ] W) : SymPow n V →ₗ[ℂ] SymPow n W :=
  ((symAlgMap f).toLinearMap.comp (symPowSubmodule n V).subtype).codRestrict
    (symPowSubmodule n W) (by
      have hle : symPowSubmodule n V ≤
          (symPowSubmodule n W).comap (symAlgMap f).toLinearMap := by
        apply Submodule.span_le.mpr
        rintro x ⟨v, rfl⟩
        change symAlgMap f (symMonomialRaw n V v) ∈ symPowSubmodule n W
        rw [symAlgMap_symMonomialRaw]
        exact Submodule.subset_span (Set.mem_range_self _)
      intro x
      exact hle x.property)


-- @@ L40-43 verbatim
@[simp] theorem symPowMap_symMonomial (n : ℕ) (f : V →ₗ[ℂ] W) (x : Fin n → V) :
    symPowMap n f (symMonomial n V x) = symMonomial n W (fun i => f (x i)) := by
  apply Subtype.ext
  exact symAlgMap_symMonomialRaw n f x


-- @@ L45-48 verbatim
@[simp] theorem symAlgMap_id :
    symAlgMap (LinearMap.id : V →ₗ[ℂ] V) = AlgHom.id ℂ (SymmetricAlgebra ℂ V) := by
  ext x
  simp


-- @@ L50-53 verbatim
@[simp] theorem symAlgMap_comp (g : W →ₗ[ℂ] U) (f : V →ₗ[ℂ] W) :
    symAlgMap (g.comp f) = (symAlgMap g).comp (symAlgMap f) := by
  ext x
  simp


-- @@ L55-56 verbatim
@[simp] theorem symPowMap_coe (n : ℕ) (f : V →ₗ[ℂ] W) (x : SymPow n V) :
    (symPowMap n f x : SymmetricAlgebra ℂ W) = symAlgMap f x := rfl


-- @@ L58-63 verbatim
@[simp] theorem symPowMap_id (n : ℕ) :
    symPowMap n (LinearMap.id : V →ₗ[ℂ] V) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp


-- @@ L65-70 verbatim
@[simp] theorem symPowMap_comp (n : ℕ) (g : W →ₗ[ℂ] U) (f : V →ₗ[ℂ] W) :
    symPowMap n (g.comp f) = (symPowMap n g).comp (symPowMap n f) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp


-- @@ L72-83 verbatim
/-- A linear equivalence induces an equivalence on each symmetric power. -/
def symPowEquiv (n : ℕ) (e : V ≃ₗ[ℂ] W) : SymPow n V ≃ₗ[ℂ] SymPow n W where
  toLinearMap := symPowMap n e.toLinearMap
  invFun := symPowMap n e.symm.toLinearMap
  left_inv x := by
    change ((symPowMap n e.symm.toLinearMap).comp (symPowMap n e.toLinearMap)) x = x
    rw [← symPowMap_comp]
    simp
  right_inv x := by
    change ((symPowMap n e.toLinearMap).comp (symPowMap n e.symm.toLinearMap)) x = x
    rw [← symPowMap_comp]
    simp


-- @@ L85-87 verbatim
@[simp] theorem symPowEquiv_symMonomial (n : ℕ) (e : V ≃ₗ[ℂ] W) (x : Fin n → V) :
    symPowEquiv n e (symMonomial n V x) = symMonomial n W (fun i => e (x i)) :=
  symPowMap_symMonomial n e.toLinearMap x


-- @@ L89-90 verbatim
@[simp] theorem symPowEquiv_toLinearMap (n : ℕ) (e : V ≃ₗ[ℂ] W) :
    (symPowEquiv n e).toLinearMap = symPowMap n e.toLinearMap := rfl


-- @@ L92-95 verbatim
@[simp] theorem symPowEquiv_refl (n : ℕ) :
    symPowEquiv n (LinearEquiv.refl ℂ V) = LinearEquiv.refl ℂ (SymPow n V) := by
  apply LinearEquiv.toLinearMap_injective
  exact symPowMap_id n


-- @@ L97-100 verbatim
@[simp] theorem symPowEquiv_trans (n : ℕ) (e : V ≃ₗ[ℂ] W) (f : W ≃ₗ[ℂ] U) :
    symPowEquiv n (e.trans f) = (symPowEquiv n e).trans (symPowEquiv n f) := by
  apply LinearEquiv.toLinearMap_injective
  exact symPowMap_comp n f.toLinearMap e.toLinearMap


-- @@ L102-104 verbatim
@[simp] theorem symPowEquiv_symm (n : ℕ) (e : V ≃ₗ[ℂ] W) :
    symPowEquiv n e.symm = (symPowEquiv n e).symm := by
  rfl


-- @@ L106-113 verbatim
theorem symPowMap_injective (n : ℕ) (f : V →ₗ[ℂ] W) (hf : Function.Injective f) :
    Function.Injective (symPowMap n f) := by
  obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hf)
  have hgf : (symPowMap n g).comp (symPowMap n f) = LinearMap.id := by
    rw [← symPowMap_comp, hg, symPowMap_id]
  have hleft : Function.LeftInverse (symPowMap n g) (symPowMap n f) :=
    fun x => LinearMap.congr_fun hgf x
  exact hleft.injective


-- @@ L115-122 verbatim
theorem symPowMap_surjective (n : ℕ) (f : V →ₗ[ℂ] W) (hf : Function.Surjective f) :
    Function.Surjective (symPowMap n f) := by
  obtain ⟨g, hg⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf)
  have hfg : (symPowMap n f).comp (symPowMap n g) = LinearMap.id := by
    rw [← symPowMap_comp, hg, symPowMap_id]
  have hright : Function.RightInverse (symPowMap n g) (symPowMap n f) :=
    fun x => LinearMap.congr_fun hfg x
  exact hright.surjective


-- @@ L124-124 verbatim
end Problem346


-- @@ L126-126 verbatim
end


-- @@ L128-128 verbatim
end OAI
