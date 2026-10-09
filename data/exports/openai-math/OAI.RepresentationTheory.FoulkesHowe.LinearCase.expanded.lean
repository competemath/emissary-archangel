import OAI.RepresentationTheory.FoulkesHowe.DegreeOne
import OAI.RepresentationTheory.FoulkesHowe.Functoriality


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped BigOperators

-- @@ L8-8 verbatim
universe u

-- @@ L9-9 verbatim
namespace Problem346


-- @@ L11-16 verbatim
@[simp] theorem foulkesFormula_one (b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] (v : Fin b → Fin 1 → V) :
    foulkesFormula 1 b V v =
      symMonomial 1 (SymPow b V) (fun _ => symMonomial b V (fun j => v j 0)) := by
  classical
  simp [foulkesFormula, Fin.eq_zero]


-- @@ L18-21 verbatim
/-- The canonical Foulkes--Howe equivalence when the inner degree is one. -/
def foulkesOneEquiv (b : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V] :
    SymPow b (SymPow 1 V) ≃ₗ[ℂ] SymPow 1 (SymPow b V) :=
  (symPowEquiv b (symPowOneEquiv V)).trans (symPowOneEquiv (SymPow b V)).symm


-- @@ L23-27 verbatim
theorem foulkesOneEquiv_isFoulkesMap (b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] :
    IsFoulkesMap 1 b V (foulkesOneEquiv b V).toLinearMap := by
  intro v
  simp [foulkesOneEquiv]


-- @@ L29-46 verbatim
/-- Degree-one stabilization, with no finite-dimensionality requirement. -/
theorem canonical_foulkes_howe_a_one_aux (V : Type u)
    [AddCommGroup V] [Module ℂ V] (b : ℕ) :
    ∃ μ : SymPow b (SymPow 1 V) →ₗ[ℂ] SymPow 1 (SymPow b V),
      IsFoulkesMap 1 b V μ ∧ Function.Bijective μ ∧
      ∀ ν : SymPow b (SymPow 1 V) →ₗ[ℂ] SymPow 1 (SymPow b V),
        IsFoulkesMap 1 b V ν → ν = μ := by
  refine ⟨(foulkesOneEquiv b V).toLinearMap, foulkesOneEquiv_isFoulkesMap b V,
    (foulkesOneEquiv b V).bijective, ?_⟩
  intro ν hν
  have hspan : Submodule.span ℂ (Set.range (symMonomial b (SymPow 1 V))) = ⊤ := by
    exact (Submodule.span_range_subtype_eq_top_iff (symPowSubmodule b (SymPow 1 V))
      (fun v => Submodule.subset_span (Set.mem_range_self v))).mpr rfl
  apply LinearMap.ext_on_range hspan
  intro v
  have h := (hν (fun j _ => symPowOneEquiv V (v j))).trans
    ((foulkesOneEquiv_isFoulkesMap b V (fun j _ => symPowOneEquiv V (v j))).symm)
  simpa only [← symPowOneEquiv_symm_apply, LinearEquiv.symm_apply_apply] using h


-- @@ L48-48 verbatim
end Problem346


-- @@ L50-50 verbatim
end


-- @@ L52-52 verbatim
end OAI
