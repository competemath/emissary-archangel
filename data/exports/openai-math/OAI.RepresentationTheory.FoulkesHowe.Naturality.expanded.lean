import OAI.RepresentationTheory.FoulkesHowe.Actions
import OAI.RepresentationTheory.FoulkesHowe.Spanning


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped BigOperators

-- @@ L8-8 verbatim
universe u v w

-- @@ L9-9 verbatim
namespace Problem346


-- @@ L11-13 verbatim
variable {V : Type u} {W : Type v} {U : Type w}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U]


-- @@ L15-18 verbatim
/-- The map on a plethysm induced by a linear map on the original space. -/
def plethysmMap (outer inner : ℕ) (f : V →ₗ[ℂ] W) :
    SymPow outer (SymPow inner V) →ₗ[ℂ] SymPow outer (SymPow inner W) :=
  symPowMap outer (symPowMap inner f)


-- @@ L20-26 verbatim
@[simp] theorem plethysmMap_symMonomial (outer inner : ℕ) (f : V →ₗ[ℂ] W)
    (x : Fin outer → Fin inner → V) :
    plethysmMap outer inner f
        (symMonomial outer (SymPow inner V) (fun i => symMonomial inner V (x i))) =
      symMonomial outer (SymPow inner W)
        (fun i => symMonomial inner W (fun j => f (x i j))) := by
  simp [plethysmMap]


-- @@ L28-30 verbatim
@[simp] theorem plethysmMap_id (outer inner : ℕ) :
    plethysmMap outer inner (LinearMap.id : V →ₗ[ℂ] V) = LinearMap.id := by
  simp [plethysmMap]


-- @@ L32-35 verbatim
@[simp] theorem plethysmMap_comp (outer inner : ℕ) (g : W →ₗ[ℂ] U) (f : V →ₗ[ℂ] W) :
    plethysmMap outer inner (g.comp f) =
      (plethysmMap outer inner g).comp (plethysmMap outer inner f) := by
  simp [plethysmMap]


-- @@ L37-38 verbatim
@[simp] theorem plethysmMap_equiv (outer inner : ℕ) (g : V ≃ₗ[ℂ] V) :
    plethysmMap outer inner g.toLinearMap = plethysmAction outer inner g := rfl


-- @@ L40-51 verbatim
/-- The explicitly normalized Foulkes formula is natural in the vector space. -/
theorem plethysmMap_foulkesFormula (a b : ℕ) (f : V →ₗ[ℂ] W)
    (x : Fin b → Fin a → V) :
    plethysmMap a b f (foulkesFormula a b V x) =
      foulkesFormula a b W (fun j i => f (x j i)) := by
  classical
  unfold foulkesFormula
  rw [map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  exact plethysmMap_symMonomial a b f (fun i j => x j ((σ j) i))


-- @@ L53-63 verbatim
/-- Any two maps satisfying the canonical formula form a natural square. -/
theorem IsFoulkesMap.natural {a b : ℕ}
    {μV : SymPow b (SymPow a V) →ₗ[ℂ] SymPow a (SymPow b V)}
    {μW : SymPow b (SymPow a W) →ₗ[ℂ] SymPow a (SymPow b W)}
    (hV : IsFoulkesMap a b V μV) (hW : IsFoulkesMap a b W μW)
    (f : V →ₗ[ℂ] W) :
    (plethysmMap a b f).comp μV = μW.comp (plethysmMap b a f) := by
  apply plethysm_linearMap_ext a b V
  intro x
  simp only [LinearMap.comp_apply, plethysmMap_symMonomial]
  rw [hV, hW, plethysmMap_foulkesFormula]


-- @@ L65-70 verbatim
/-- Every canonical Foulkes map is GL-equivariant. -/
theorem IsFoulkesMap.commutes {a b : ℕ}
    {μ : SymPow b (SymPow a V) →ₗ[ℂ] SymPow a (SymPow b V)}
    (hμ : IsFoulkesMap a b V μ) (g : V ≃ₗ[ℂ] V) :
    (plethysmAction a b g).comp μ = μ.comp (plethysmAction b a g) :=
  hμ.natural hμ g.toLinearMap


-- @@ L72-72 verbatim
end Problem346


-- @@ L74-74 verbatim
end


-- @@ L76-76 verbatim
end OAI
