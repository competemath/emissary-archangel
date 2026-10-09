import OAI.RepresentationTheory.FoulkesHowe.Model


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
universe u

-- @@ L7-7 verbatim
namespace Problem346


-- @@ L9-23 verbatim
theorem vanishing_on_products_one (V : Type u) [AddCommGroup V] [Module ℂ V]
    (b : ℕ) (T : SymmetricMultilinearForm 1 b V)
    (h : ∀ u : Fin b → V, T (fun _ => symMonomial b V u) = 0) : T = 0 := by
  have hspan : Submodule.span ℂ (Set.range (symMonomial b V)) = ⊤ := by
    exact (Submodule.span_range_subtype_eq_top_iff (symPowSubmodule b V)
      (fun v => Submodule.subset_span (Set.mem_range_self v))).mpr rfl
  apply MultilinearMap.ext_of_span_eq_top (g := fun (_ : Fin 1) => symMonomial b V)
    (fun _ => hspan)
  intro v
  have hv : (fun i : Fin 1 => symMonomial b V (v i)) =
      (fun _ : Fin 1 => symMonomial b V (v 0)) := by
    funext i
    rw [Fin.eq_zero i]
  rw [hv]
  exact h (v 0)


-- @@ L25-25 verbatim
end Problem346


-- @@ L27-27 verbatim
end


-- @@ L29-29 verbatim
end OAI
