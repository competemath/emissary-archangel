import OAI.RepresentationTheory.FoulkesHowe.Functoriality


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped BigOperators

-- @@ L7-7 verbatim
universe u

-- @@ L8-8 verbatim
namespace Problem346


-- @@ L10-10 verbatim
variable {V : Type u} [AddCommGroup V] [Module ℂ V]


-- @@ L12-26 verbatim
/-- Any map with the prescribed plethysm action carries the Foulkes formula
    to the formula on the transformed vector array. -/
theorem map_foulkesFormula_of_isPlethysmAction
    {a b : ℕ} {g : V ≃ₗ[ℂ] V}
    {L : SymPow a (SymPow b V) →ₗ[ℂ] SymPow a (SymPow b V)}
    (hL : IsPlethysmAction a b V g L) (v : Fin b → Fin a → V) :
    L (foulkesFormula a b V v) =
      foulkesFormula a b V (fun j i => g (v j i)) := by
  classical
  unfold foulkesFormula
  rw [map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  exact hL (fun i j => v j ((σ j) i))


-- @@ L28-31 verbatim
/-- The canonical action of a linear automorphism on a plethysm. -/
def plethysmEquiv (outer inner : ℕ) (g : V ≃ₗ[ℂ] V) :
    SymPow outer (SymPow inner V) ≃ₗ[ℂ] SymPow outer (SymPow inner V) :=
  symPowEquiv outer (symPowEquiv inner g)


-- @@ L33-36 verbatim
/-- The underlying endomorphism of the canonical plethysm action. -/
def plethysmAction (outer inner : ℕ) (g : V ≃ₗ[ℂ] V) :
    SymPow outer (SymPow inner V) →ₗ[ℂ] SymPow outer (SymPow inner V) :=
  (plethysmEquiv outer inner g).toLinearMap


-- @@ L38-44 verbatim
@[simp] theorem plethysmAction_symMonomial (outer inner : ℕ) (g : V ≃ₗ[ℂ] V)
    (x : Fin outer → Fin inner → V) :
    plethysmAction outer inner g
      (symMonomial outer (SymPow inner V) (fun i => symMonomial inner V (x i))) =
    symMonomial outer (SymPow inner V)
      (fun i => symMonomial inner V (fun j => g (x i j))) := by
  simp [plethysmAction, plethysmEquiv]


-- @@ L46-48 verbatim
theorem plethysmAction_isPlethysmAction (outer inner : ℕ) (g : V ≃ₗ[ℂ] V) :
    IsPlethysmAction outer inner V g (plethysmAction outer inner g) :=
  plethysmAction_symMonomial outer inner g


-- @@ L50-52 verbatim
theorem plethysmAction_bijective (outer inner : ℕ) (g : V ≃ₗ[ℂ] V) :
    Function.Bijective (plethysmAction outer inner g) :=
  (plethysmEquiv outer inner g).bijective


-- @@ L54-65 verbatim
theorem isGLEquivariantEmbedding_of_commutes {a b : ℕ}
    (ι : SymPow a (SymPow b V) →ₗ[ℂ] SymPow b (SymPow a V))
    (hinj : Function.Injective ι)
    (hcomm : ∀ g : V ≃ₗ[ℂ] V,
      (plethysmAction b a g).comp ι = ι.comp (plethysmAction a b g)) :
    IsGLEquivariantEmbedding a b V ι := by
  refine ⟨hinj, ?_⟩
  intro g
  exact ⟨plethysmAction b a g, plethysmAction a b g,
    plethysmAction_isPlethysmAction b a g,
    plethysmAction_isPlethysmAction a b g,
    plethysmAction_bijective b a g, plethysmAction_bijective a b g, hcomm g⟩


-- @@ L67-69 verbatim
@[simp] theorem plethysmAction_refl (outer inner : ℕ) :
    plethysmAction outer inner (LinearEquiv.refl ℂ V) = LinearMap.id := by
  simp [plethysmAction, plethysmEquiv]


-- @@ L71-77 verbatim
@[simp] theorem plethysmAction_trans (outer inner : ℕ) (g h : V ≃ₗ[ℂ] V) :
    plethysmAction outer inner (g.trans h) =
      (plethysmAction outer inner h).comp (plethysmAction outer inner g) := by
  change symPowMap outer (symPowMap inner (g.trans h).toLinearMap) = _
  change symPowMap outer (symPowMap inner (h.toLinearMap.comp g.toLinearMap)) = _
  rw [symPowMap_comp, symPowMap_comp]
  rfl


-- @@ L79-83 verbatim
@[simp] theorem plethysmAction_symm_comp (outer inner : ℕ) (g : V ≃ₗ[ℂ] V) :
    (plethysmAction outer inner g.symm).comp (plethysmAction outer inner g) =
      LinearMap.id := by
  rw [← plethysmAction_trans]
  simp


-- @@ L85-89 verbatim
@[simp] theorem plethysmAction_comp_symm (outer inner : ℕ) (g : V ≃ₗ[ℂ] V) :
    (plethysmAction outer inner g).comp (plethysmAction outer inner g.symm) =
      LinearMap.id := by
  rw [← plethysmAction_trans]
  simp


-- @@ L91-101 verbatim
/-- Conjugating by the natural GL actions preserves the defining canonical formula. -/
theorem isFoulkesMap_conjugate {a b : ℕ}
    {μ : SymPow b (SymPow a V) →ₗ[ℂ] SymPow a (SymPow b V)}
    (hμ : IsFoulkesMap a b V μ) (g : V ≃ₗ[ℂ] V) :
    IsFoulkesMap a b V
      ((plethysmAction a b g.symm).comp (μ.comp (plethysmAction b a g))) := by
  intro v
  simp only [LinearMap.comp_apply, plethysmAction_symMonomial]
  rw [hμ]
  rw [map_foulkesFormula_of_isPlethysmAction (plethysmAction_isPlethysmAction a b g.symm)]
  simp


-- @@ L103-113 verbatim
/-- Uniqueness of the canonical map implies its GL equivariance. -/
theorem foulkesMap_commutes_of_unique {a b : ℕ}
    {μ : SymPow b (SymPow a V) →ₗ[ℂ] SymPow a (SymPow b V)}
    (hμ : IsFoulkesMap a b V μ)
    (huniq : ∀ ν : SymPow b (SymPow a V) →ₗ[ℂ] SymPow a (SymPow b V),
      IsFoulkesMap a b V ν → ν = μ)
    (g : V ≃ₗ[ℂ] V) :
    (plethysmAction a b g).comp μ = μ.comp (plethysmAction b a g) := by
  have hc := huniq _ (isFoulkesMap_conjugate hμ g)
  have he := congrArg (fun L => (plethysmAction a b g).comp L) hc
  simpa only [← LinearMap.comp_assoc, plethysmAction_comp_symm, LinearMap.id_comp] using he.symm


-- @@ L115-115 verbatim
end Problem346


-- @@ L117-117 verbatim
end


-- @@ L119-119 verbatim
end OAI
