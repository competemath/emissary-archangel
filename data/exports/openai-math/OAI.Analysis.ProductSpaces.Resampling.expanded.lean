import OAI.Analysis.ProductSpaces.FiniteHeads


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L6-6 verbatim
open scoped ENNReal NNReal Topology


-- @@ L8-8 verbatim
noncomputable section


-- @@ L10-10 verbatim
universe uι


-- @@ L12-12 verbatim
namespace IndependentProducts


-- @@ L14-14 verbatim
section Resampling

-- @@ L15-15 verbatim
variable {ι : Type uι} [Fintype ι]


-- @@ L17-21 verbatim
/-- Independent complete samples: descendants, exits, and old coordinates. -/
def expandSamples (z : ((ι → Sample) × Sample) × Sample) : Option (Option ι) → Sample
  | none => z.2
  | some none => z.1.2
  | some (some i) => z.1.1 i


-- @@ L23-39 verbatim
lemma measurePreserving_expandSamples (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    MeasurePreserving (expandSamples (ι := ι))
      (((Measure.pi (fun _ : ι => productMeasure μ)).prod (productMeasure μ)).prod (productMeasure μ))
      (Measure.pi (fun _ : Option (Option ι) => productMeasure μ)) := by
  have h1 : MeasurePreserving (MeasurableEquiv.piOptionEquivProd (fun _ : Option ι => Sample)).symm
      ((Measure.pi (fun _ : ι => productMeasure μ)).prod (productMeasure μ))
      (Measure.pi (fun _ : Option ι => productMeasure μ)) :=
    ⟨by fun_prop, Measure.pi_map_piOptionEquivProd (fun _ : Option ι => productMeasure μ)⟩
  have h2 : MeasurePreserving (MeasurableEquiv.piOptionEquivProd (fun _ : Option (Option ι) => Sample)).symm
      ((Measure.pi (fun _ : Option ι => productMeasure μ)).prod (productMeasure μ))
      (Measure.pi (fun _ : Option (Option ι) => productMeasure μ)) :=
    ⟨by fun_prop, Measure.pi_map_piOptionEquivProd (fun _ : Option (Option ι) => productMeasure μ)⟩
  convert h2.comp (h1.prod (MeasurePreserving.id (productMeasure μ))) using 1
  ext z k e
  cases k with
  | none => rfl
  | some k => cases k <;> rfl


-- @@ L41-41 verbatim
namespace FiniteHead

-- @@ L42-42 verbatim
variable (T : FiniteHead) (e : ι → T.Boundary) (he : Function.Injective e)


-- @@ L44-48 verbatim
noncomputable def sampleSelector (d : Edge) : Option (Option ι) := by
  classical
  exact if h : ∃ i, (e i).val.val <+: d.val then
    if d = (e (Classical.choose h)).val then some none else some (some (Classical.choose h))
  else none


-- @@ L50-56 verbatim
lemma sampleSelector_head {d : Edge} (hd : d.val ∈ T.vertices) :
    T.sampleSelector e d = none := by
  classical
  have hn : ¬ ∃ i, (e i).val.val <+: d.val := by
    rintro ⟨i, hi⟩
    exact T.no_boundary_prefix_head hd (e i) hi
  simp [sampleSelector, hn]


-- @@ L58-63 verbatim
include he in
lemma sampleSelector_exit (i : ι) : T.sampleSelector e (e i).val = some none := by
  classical
  have hh : ∃ j, (e j).val.val <+: (e i).val.val := ⟨i, List.prefix_rfl⟩
  have hi : Classical.choose hh = i := he (T.boundary_eq_of_prefix (Classical.choose_spec hh))
  simp [sampleSelector, hh, hi]


-- @@ L65-71 verbatim
include he in
lemma sampleSelector_desc (i : ι) (d : Edge) (hd : (e i).val.val <+: d.val)
    (hne : d ≠ (e i).val) : T.sampleSelector e d = some (some i) := by
  classical
  have hh : ∃ j, (e j).val.val <+: d.val := ⟨i, hd⟩
  have hi : Classical.choose hh = i := he (T.boundary_unique (Classical.choose_spec hh) hd)
  simp [sampleSelector, hh, hi, hne]


-- @@ L73-74 verbatim
noncomputable def stitched (z : ((ι → Sample) × Sample) × Sample) : Sample :=
  fun d => expandSamples z (T.sampleSelector e d) d


-- @@ L76-80 verbatim
lemma measurePreserving_stitched (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    MeasurePreserving (T.stitched e)
      (((Measure.pi (fun _ : ι => productMeasure μ)).prod (productMeasure μ)).prod (productMeasure μ))
      (productMeasure μ) :=
  (measurePreserving_sampleSelector μ (T.sampleSelector e)).comp (measurePreserving_expandSamples μ)


-- @@ L82-88 verbatim
lemma stitched_head (z : ((ι → Sample) × Sample) × Sample) (v : Vertex) (hv : v ∈ T.vertices) :
    pathProduct v (T.stitched e z) = pathProduct v z.2 := by
  simp only [pathProduct_eq_prod_pathEdges]
  apply Finset.prod_congr rfl
  intro d hd
  have hdt : d.val ∈ T.vertices := T.prefix_mem ((mem_pathEdges_iff v d).mp hd) hv
  simp [stitched, T.sampleSelector_head e hdt, expandSamples]


-- @@ L90-90 verbatim
end FiniteHead


-- @@ L92-100 verbatim
lemma pathProduct_split (v : Vertex) (e : Edge) (he : e.val <+: v) (ω : Sample) :
    pathProduct v ω = pathProduct e.val.dropLast ω * ω e *
      ∏ d ∈ pathEdges v \ pathEdges e.val, ω d := by
  classical
  have h := Finset.prod_sdiff (f := ω) (pathEdges_mono he)
  rw [pathEdges_parent, Finset.prod_insert (self_not_mem_pathEdges_parent e)] at h
  simp only [pathProduct_eq_prod_pathEdges]
  rw [← h, pathEdges_parent]
  ring


-- @@ L102-102 verbatim
namespace FiniteHead

-- @@ L103-103 verbatim
variable (T : FiniteHead) (e : ι → T.Boundary) (he : Function.Injective e)


-- @@ L105-126 verbatim
include he in
lemma stitched_path (z : ((ι → Sample) × Sample) × Sample) (v : Vertex) (i : ι)
    (hi : (e i).val.val <+: v) :
    pathProduct v (T.stitched e z) = pathProduct (e i).val.val.dropLast z.2 * z.1.2 (e i).val *
      ∏ d ∈ pathEdges v \ pathEdges (e i).val.val, z.1.1 i d := by
  classical
  rw [pathProduct_split v (e i).val hi, T.stitched_head e z _ (e i).property.2]
  have hw : T.stitched e z (e i).val = z.1.2 (e i).val := by
    simp [stitched, T.sampleSelector_exit e he i, expandSamples]
  rw [hw]
  congr 1
  apply Finset.prod_congr rfl
  intro d hd
  obtain ⟨hdv, hde⟩ := Finset.mem_sdiff.mp hd
  have hp : (e i).val.val <+: d.val := by
    rcases List.prefix_or_prefix_of_prefix hi ((mem_pathEdges_iff v d).mp hdv) with h | h
    · exact h
    · exact (hde ((mem_pathEdges_iff _ _).mpr h)).elim
  have hne : d ≠ (e i).val := by
    rintro rfl
    exact hde (self_mem_pathEdges _)
  simp [stitched, T.sampleSelector_desc e he i d hp hne, expandSamples]


-- @@ L128-128 verbatim
end FiniteHead

-- @@ L129-129 verbatim
end Resampling

-- @@ L130-130 verbatim
end IndependentProducts


-- @@ L132-132 verbatim
end


-- @@ L134-134 verbatim
end OAI
