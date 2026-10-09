import OAI.Analysis.ProductSpaces.TailCoefficients


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L6-6 verbatim
open scoped ENNReal NNReal Topology


-- @@ L8-8 verbatim
noncomputable section


-- @@ L10-10 verbatim
universe uι uκ


-- @@ L12-12 verbatim
namespace IndependentProducts

-- @@ L13-13 verbatim
namespace FiniteHead

-- @@ L14-17 verbatim
lemma ancestor_of_boundary_prefix (T : FiniteHead) (v : Vertex) (e : T.Boundary)
    (he : e.val.val <+: v) : T.ancestor v = e.val.val.dropLast := by
  have hv : v ∉ T.vertices := fun hv => T.no_boundary_prefix_head hv e he
  rw [T.ancestor_of_not_mem hv, T.exit_eq v hv e he]


-- @@ L19-19 verbatim
section CoefficientJoint

-- @@ L20-21 verbatim
variable {ι : Type uι} {κ : Type uκ} [hιfinite : Fintype ι] [Fintype κ]
  [hιdecidable : DecidableEq ι]

-- @@ L22-22 verbatim
variable (T : FiniteHead) (e : ι → T.Boundary) (v : κ → Vertex) (j : κ → ι) (a : κ → ℝ)

-- @@ L23-23 verbatim
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (h₂ : MemLp (fun w : ℝ => w) 2 μ)


-- @@ L25-38 verbatim
lemma integrable_tailCoefficient_joint {ι : Type uι} {κ : Type uκ}
    [Fintype ι] [Fintype κ] [DecidableEq ι]
    (T : FiniteHead) (e : ι → T.Boundary) (v : κ → Vertex) (j : κ → ι) (a : κ → ℝ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (h₂ : MemLp (fun w : ℝ => w) 2 μ) (i : ι) :
    Integrable (fun z : Sample × Sample => T.tailCoefficient e v j a z.1 i z.2)
      ((productMeasure μ).prod (productMeasure μ)) := by
  classical
  unfold tailCoefficient
  apply integrable_finsetSum
  intro k hk
  split_ifs
  · exact (((pathProduct_memLp μ h₂ _).integrable (by norm_num)).const_mul _).mul_prod
      (integrable_residualProduct μ (h₂.integrable (by norm_num)) _ _)
  · exact integrable_zero _ _ _


-- @@ L40-50 verbatim
include h₂ in
lemma integrable_tailCoefficient_all (i : ι) :
    Integrable (fun z : (ι → Sample) × Sample => T.tailCoefficient e v j a z.2 i (z.1 i))
      ((Measure.pi (fun _ : ι => productMeasure μ)).prod (productMeasure μ)) := by
  have hmp : MeasurePreserving (fun z : (ι → Sample) × Sample => (z.2, z.1 i))
      ((Measure.pi (fun _ : ι => productMeasure μ)).prod (productMeasure μ))
      ((productMeasure μ).prod (productMeasure μ)) := by
    exact (Measure.measurePreserving_swap (μ := productMeasure μ) (ν := productMeasure μ)).comp
      ((measurePreserving_eval (fun _ : ι => productMeasure μ) i).prod (MeasurePreserving.id _))
  exact hmp.integrable_comp (T.measurable_tailCoefficient e v j a i).aestronglyMeasurable |>.mpr
    (T.integrable_tailCoefficient_joint e v j a μ h₂ i)


-- @@ L52-67 verbatim
include h₂ in
lemma stitched_tail_polynomial (z : ((ι → Sample) × Sample) × Sample)
    (he : Function.Injective e) (hv : ∀ k, (e (j k)).val.val <+: v k)
    (hmean : ∫ w : ℝ, w ∂μ = 1) :
    (∑ k, a k * (pathProduct (v k) (T.stitched e z) -
      pathProduct (T.ancestor (v k)) (T.stitched e z))) =
      ∑ i, (T.tailCoefficient e v j a z.2 i (z.1.1 i) * z.1.2 (e i).val -
        ∫ desc, T.tailCoefficient e v j a z.2 i desc ∂productMeasure μ) := by
  classical
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [T.sum_tailCoefficient e v j a z he hv,
    T.sum_tailCoefficient_mean e v j a μ (h₂.integrable (by norm_num)) hmean z.2]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [T.stitched_head e z _ (T.ancestor_mem _), T.ancestor_of_boundary_prefix (v k) (e (j k)) (hv k)]


-- @@ L69-76 verbatim
lemma stitched_head_polynomial {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (T : FiniteHead) (e : ι → T.Boundary) (a : T.vertices → ℝ)
    (z : ((ι → Sample) × Sample) × Sample) :
    (∑ v : T.vertices, a v * pathProduct v (T.stitched e z)) =
      ∑ v : T.vertices, a v * pathProduct v z.2 := by
  apply Finset.sum_congr rfl
  intro v hv
  rw [T.stitched_head e z v v.property]


-- @@ L78-78 verbatim
end CoefficientJoint

-- @@ L79-79 verbatim
end FiniteHead

-- @@ L80-80 verbatim
end IndependentProducts


-- @@ L82-82 verbatim
end


-- @@ L84-84 verbatim
end OAI
