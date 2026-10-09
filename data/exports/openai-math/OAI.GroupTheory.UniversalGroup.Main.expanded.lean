import OAI.GroupTheory.UniversalGroup.UniverseTransport


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
open Set Metric Topology BigOperators

-- @@ L6-6 verbatim
open Set Metric Topology

-- @@ L7-7 verbatim
open Set Topology

-- @@ L8-8 verbatim
open Set Metric Topology

-- @@ L9-9 verbatim
open scoped NNReal

-- @@ L10-10 verbatim
open Set Metric Topology

-- @@ L11-11 verbatim
open scoped NNReal ENNReal

-- @@ L12-12 verbatim
open Set Metric Topology

-- @@ L13-13 verbatim
open scoped TensorProduct

-- @@ L14-14 verbatim
open Set Metric Topology


-- @@ L16-16 verbatim
namespace UniversalFInfinity

-- @@ L17-17 verbatim
noncomputable section

-- @@ L18-18 verbatim
universe u


-- @@ L20-48 verbatim
theorem universal_group_of_type_FInfinity :
    ∃ (H : Type u) (groupH : Group H),
      @HasTypeFInfinity H groupH ∧
      ∀ (G : Type u) [Group G] [Group.IsFinitelyPresented G],
        ∃ φ : G →* H, Function.Injective φ := by
  obtain ⟨U,gU,fpU,i,hi⟩ := Higman.NormalWords.embeds_presentation
    RecursiveUniversalThree.enumerator RecursiveUniversalThree.enumerator_primrec.to_comp
  let : Group U := gU
  let : Group.IsFinitelyPresented U := fpU
  have hU : ConcreteEnvelopes.IsUniversal U := by
    intro V _ _
    obtain ⟨j,hj⟩ := RecursiveUniversalThree.universal (G := V)
    exact ⟨i.comp j,hi.comp hj⟩
  obtain ⟨k,hk,hk_inj⟩ := ConcreteEnvelopes.self_maps U hU
  let : Fact (Function.Injective (k (.inl ConcreteEnvelopes.P₂.identity))) := ⟨hk_inj⟩
  let : TopologicalSpace U := ⊥
  let : DiscreteTopology U := ⟨rfl⟩
  let f := k (.inl ConcreteEnvelopes.P₂.identity)
  let H₀ := AscendingTorus.Torus f
  let : TopologicalSpace H₀ := ⊥
  let : DiscreteTopology H₀ := ⟨rfl⟩
  refine ⟨ULift.{u} H₀,inferInstance,?_,?_⟩
  · exact Brown.geometric_lifted_of_uniform
      (TorusGeometry.diagram_milnor_uniform_nullhomotopy k hk)
  · intro G _ _
    obtain ⟨j,hj⟩ := RecursiveUniversalThree.universal (G := G)
    refine ⟨MulEquiv.ulift.symm.toMonoidHom.comp ((AscendingTorus.of f).comp (i.comp j)),?_⟩
    exact MulEquiv.ulift.symm.injective.comp ((AscendingTorus.of_injective f hk_inj).comp
      (hi.comp hj))

-- @@ L49-49 verbatim
end

-- @@ L50-50 verbatim
end UniversalFInfinity


-- @@ L52-52 verbatim
end OAI
