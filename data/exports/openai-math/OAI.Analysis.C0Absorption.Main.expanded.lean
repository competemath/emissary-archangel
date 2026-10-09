import OAI.Analysis.C0Absorption.Aharoni


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
open Set Filter Topology

-- @@ L6-6 verbatim
open scoped NNReal BigOperators ZeroAtInfty

-- @@ L7-7 verbatim
open NormedSpace


-- @@ L9-9 verbatim
namespace C0Absorption

-- @@ L10-10 verbatim
noncomputable section


-- @@ L12-26 verbatim
theorem BiLip.comp {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
    {g : Y → Z} {f : X → Y} (hg : BiLip g) (hf : BiLip f) : BiLip (g ∘ f) := by
  obtain ⟨cg,Cg,hcg,hcgC,hg⟩ := hg
  obtain ⟨cf,Cf,hcf,hcfC,hf⟩ := hf
  have hCg : 0≤Cg := hcg.le.trans hcgC
  have hCf : 0≤Cf := hcf.le.trans hcfC
  refine ⟨cg*cf,Cg*Cf,mul_pos hcg hcf,mul_le_mul hcgC hcfC hcf.le hCg,fun x y => ⟨?_,?_⟩⟩
  · calc
      cg*cf*dist x y = cg*(cf*dist x y) := mul_assoc _ _ _
      _ ≤ cg*dist (f x) (f y) := mul_le_mul_of_nonneg_left (hf x y).1 hcg.le
      _ ≤ dist ((g ∘ f) x) ((g ∘ f) y) := (hg _ _).1
  · calc
      dist ((g ∘ f) x) ((g ∘ f) y) ≤ Cg*dist (f x) (f y) := (hg _ _).2
      _ ≤ Cg*(Cf*dist x y) := mul_le_mul_of_nonneg_left (hf x y).2 hCg
      _ = Cg*Cf*dist x y := (mul_assoc _ _ _).symm


-- @@ L28-31 verbatim
theorem concrete_metricUniversal : MetricUniversal ConcreteSpace := by
  intro M instM instSep
  obtain ⟨f,hf⟩ := c0_metricUniversal M
  exact ⟨concreteC0Embedding ∘ f,concreteC0Embedding_bilip.comp hf⟩


-- @@ L33-37 verbatim
theorem main_result : MainConclusion := by
  refine ⟨ConcreteSpace,inferInstance,inferInstance,inferInstance,inferInstance,
    concrete_noLinearC0,⟨concreteAbsorption,concreteAbsorption_surjective,concreteAbsorption_bilip⟩,
    ⟨concreteC0Embedding,concreteC0Embedding_bilip⟩,concrete_metricUniversal,
    concrete_not_linearly_isomorphic⟩


-- @@ L39-39 verbatim
end

-- @@ L40-40 verbatim
end C0Absorption


-- @@ L42-42 verbatim
end OAI
