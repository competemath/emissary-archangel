import OAI.Analysis.TracialSplitting.FiniteSplitting


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe uNuclear



-- @@ L8-8 verbatim
section


-- @@ L10-10 verbatim
namespace CurrentMain


-- @@ L12-12 verbatim
open Pureness Filter


-- @@ L14-36 verbatim
theorem real_rank_zero_uniform_gamma
    {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [Nontrivial A] [TopologicalSpace.SeparableSpace A]
    (hsimple : TopologicallySimple A) (hinf : ¬FiniteDimensional ℂ A)
    (hA : IsNuclear.{0, uNuclear} A) (_hfinite : StablyFinite A)
    [Nonempty (TracialState A)] (U : Ultrafilter ℕ)
    (hfree : (U : Filter ℕ) ≤ atTop)
    (hRR : RealRankZero (FamilyUltrapower (completionTrace (fun τ : TracialState A => τ)) U)) :
    UniformPropertyGammaAt A U := by
  classical
  let τ := fun t : TracialState A => t
  let D := FamilyUltrapower (completionTrace τ) U
  let j : A →⋆ₐ[ℂ] D := (familyUltrapowerMap (completionTrace τ) U).comp (completionMap τ)
  let σ := familyLimitTrace (completionTrace τ) U
  have hTD : Nonempty (TracialState D) := ⟨σ (fun _ => Classical.arbitrary _)⟩
  apply completion_central_splitting_of_finite_stages τ U hfree
  intro K ε hε
  obtain ⟨P,hP,htest⟩ := finite_set_central_splitting j (simple_starAlgHom_injective hsimple j)
    hA hRR hTD (fun _ hδ => small_full_projections hsimple hinf j hRR hTD hδ) K ε hε
  refine ⟨P,hP,?_⟩
  intro u hu
  exact ⟨(familyTwoNorm_le_uniform σ _).trans_lt (htest u hu).1,
    (familyHalvingError_le_uniform σ P (j (u : A))).trans_lt (htest u hu).2⟩


-- @@ L38-38 verbatim
end CurrentMain


-- @@ L40-40 verbatim
end


-- @@ L42-42 verbatim
end OAI
