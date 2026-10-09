import OAI.Geometry.PinnedDistances.RandomGrids


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u1 u2 u3 u4


-- @@ L7-7 verbatim
section

-- @@ L8-8 verbatim
noncomputable section

-- @@ L9-9 verbatim
open NumberField

-- @@ L10-10 verbatim
open scoped BigOperators

-- @@ L11-11 verbatim
noncomputable section

-- @@ L12-12 verbatim
open MeasureTheory

-- @@ L13-13 verbatim
open scoped Topology

-- @@ L14-14 verbatim
noncomputable section

-- @@ L15-15 verbatim
open MeasureTheory

-- @@ L16-16 verbatim
open scoped Topology ENNReal


-- @@ L18-18 verbatim
noncomputable section

-- @@ L19-19 verbatim
open MeasureTheory NumberField

-- @@ L20-20 verbatim
open scoped BigOperators

-- @@ L21-21 verbatim
namespace WeakPinned.Global

-- @@ L22-22 verbatim
open Hierarchy

-- @@ L23-23 verbatim
variable {P : Type u1} [Fintype P] [DecidableEq P]

-- @@ L24-24 verbatim
variable {K : Type u2} [Field K] [NumberField K]

-- @@ L25-25 verbatim
variable (Z : P → K) (hZ : Function.Injective Z)

-- @@ L26-26 verbatim
include hZ


-- @@ L28-32 verbatim
def good (v : InfinitePlace K) (ω : Grid.FullSample) : Prop :=
  ∀ x y z : P, x ≠ y → y ≠ z → x ≠ z →
    min (Grid.depth ω (v.embedding (Z x)) (v.embedding (Z y)))
      (Grid.depth ω (v.embedding (Z y)) (v.embedding (Z z))) ≤
        Grid.depth ω (v.embedding (Z x)) (v.embedding (Z z))


-- @@ L34-37 verbatim
omit [Fintype P] [DecidableEq P] [NumberField K] in
lemma embedding_ne (v : InfinitePlace K) {x y : P} (hne : x ≠ y) :
    v.embedding (Z x) ≠ v.embedding (Z y) :=
  fun hh => hne (hZ (v.embedding.injective hh))


-- @@ L39-57 verbatim
omit [DecidableEq P] [NumberField K] in
lemma measurableSet_good (v : InfinitePlace K) : MeasurableSet {ω | good Z v ω} := by
  simp only [good, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro x
  apply MeasurableSet.iInter
  intro y
  apply MeasurableSet.iInter
  intro z
  apply MeasurableSet.iInter
  intro hxy
  apply MeasurableSet.iInter
  intro hyz
  apply MeasurableSet.iInter
  intro hxz
  exact measurableSet_le
    ((Grid.measurable_depth (embedding_ne Z hZ v hxy)).min
      (Grid.measurable_depth (embedding_ne Z hZ v hyz)))
    (Grid.measurable_depth (embedding_ne Z hZ v hxz))


-- @@ L59-64 verbatim
omit [DecidableEq P] [NumberField K] in
lemma good_ae (v : InfinitePlace K) : ∀ᵐ ω ∂Grid.fullLaw, good Z v ω := by
  simp only [good, Filter.eventually_all]
  intro x y z hxy hyz hxz
  exact Grid.depth_ultra_ae (embedding_ne Z hZ v hxy)
    (embedding_ne Z hZ v hyz) (embedding_ne Z hZ v hxz)


-- @@ L66-67 verbatim
instance good_decidable (v : InfinitePlace K) (ω : Grid.FullSample) : Decidable (good Z v ω) :=
  Classical.propDecidable _


-- @@ L69-80 verbatim
def arch (v : InfinitePlace K) (ω : Grid.FullSample) : Depth P where
  value x y := if good Z v ω ∧ x ≠ y then Grid.depth ω (v.embedding (Z x)) (v.embedding (Z y)) else 0
  symm x y := by
    by_cases h : good Z v ω
    · by_cases hxy : x = y
      · subst y; rfl
      · simp [h, hxy, Ne.symm hxy, Grid.depth_symm]
    · simp [h]
  ultra x y z hxy hyz hxz := by
    by_cases h : good Z v ω
    · simpa [h,hxy,hyz,hxz] using h x y z hxy hyz hxz
    · simp [h]


-- @@ L82-87 verbatim
omit [NumberField K] in
lemma arch_value_ae (v : InfinitePlace K) {x y : P} (hxy : x ≠ y) :
    (fun ω => (arch Z v ω).value x y) =ᵐ[Grid.fullLaw]
      (fun ω => Grid.depth ω (v.embedding (Z x)) (v.embedding (Z y))) := by
  filter_upwards [good_ae Z hZ v] with ω h
  simp [arch,h,hxy]


-- @@ L89-97 verbatim
omit [NumberField K] in
lemma arch_measurable (v : InfinitePlace K) (x y : P) :
    Measurable (fun ω => (arch Z v ω).value x y) := by
  by_cases hxy : x = y
  · subst y
    simpa only [arch,ne_eq,not_true_eq_false,and_false,reduceIte] using
      (measurable_const : Measurable (fun _ : Grid.FullSample => (0:ℝ)))
  · simpa [arch,hxy] using (Grid.measurable_depth (embedding_ne Z hZ v hxy)).ite
      (measurableSet_good Z hZ v) (measurable_const : Measurable (fun _ : Grid.FullSample => (0:ℝ)))


-- @@ L99-115 verbatim
omit [NumberField K] in
lemma arch_integrable (v : InfinitePlace K) (x y : P) :
    Integrable (fun ω => (arch Z v ω).value x y) Grid.fullLaw := by
  by_cases hxy : x = y
  · subst y
    simpa only [arch,ne_eq,not_true_eq_false,and_false,reduceIte] using
      (integrable_const (0:ℝ) : Integrable (fun _ : Grid.FullSample => (0:ℝ)) Grid.fullLaw)
  · have hi := (Grid.error_integrable_full (embedding_ne Z hZ v hxy)).sub
      (integrable_const (Real.log ‖v.embedding (Z x) - v.embedding (Z y)‖))
    have he : (fun ω => Grid.error ω (v.embedding (Z x)) (v.embedding (Z y)) -
        Real.log ‖v.embedding (Z x) - v.embedding (Z y)‖) =
        (fun ω => Grid.depth ω (v.embedding (Z x)) (v.embedding (Z y))) := by
      funext ω; simp only [Grid.error,add_sub_cancel_right]
    change Integrable (fun ω => Grid.error ω (v.embedding (Z x)) (v.embedding (Z y)) -
        Real.log ‖v.embedding (Z x) - v.embedding (Z y)‖) Grid.fullLaw at hi
    rw [he] at hi
    exact hi.congr (arch_value_ae Z hZ v hxy).symm


-- @@ L117-126 verbatim
lemma arch_mean (v : InfinitePlace K) (x y : P) (hxy : x ≠ y) :
    (∫ ω, (arch Z v ω).value x y ∂Grid.fullLaw) = -Real.log (v (Z x-Z y)) + Grid.kappa := by
  rw [integral_congr_ae (arch_value_ae Z hZ v hxy)]
  have hh := Grid.mean_error_full (embedding_ne Z hZ v hxy)
  have hi := (arch_integrable Z hZ v x y).congr (arch_value_ae Z hZ v hxy)
  simp only [Grid.error] at hh
  rw [integral_add hi (integrable_const _)] at hh
  simp only [integral_const,probReal_univ,one_smul] at hh
  rw [← map_sub, InfinitePlace.norm_embedding_eq] at hh
  linarith


-- @@ L128-137 verbatim
def finite (v : FinitePlace K) : Depth P where
  value x y := if x = y then 0 else -Real.log (v (Z x-Z y))
  symm x y := by
    by_cases hxy : x = y
    · subst y; rfl
    · simp only [hxy,Ne.symm hxy,reduceIte]
      rw [← neg_sub (Z x) (Z y), map_neg_eq_map]
  ultra x y z hxy hyz hxz := by
    simp only [hxy,hyz,hxz,reduceIte]
    exact Arithmetic.finite_raw_ultra v (hZ.ne hxy) (hZ.ne hyz) (hZ.ne hxz)


-- @@ L139-139 verbatim
abbrev DiffPair := {p : P × P // p.1 ≠ p.2}


-- @@ L141-143 verbatim
def badPlaces : Finset (FinitePlace K) :=
  (Arithmetic.finite_nonunit_places (fun p : DiffPair (P := P) => Z p.1.1 - Z p.1.2)
    (fun p => sub_ne_zero.mpr (hZ.ne p.2))).toFinset


-- @@ L145-152 verbatim
omit [DecidableEq P] in
lemma badPlaces_mem (v : FinitePlace K) : v ∈ badPlaces Z hZ ↔ ∃ x y, x ≠ y ∧ v (Z x-Z y) ≠ 1 := by
  simp only [badPlaces, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨⟨⟨x,y⟩,hne⟩,hh⟩
    exact ⟨x,y,hne,hh⟩
  · rintro ⟨x,y,hne,hh⟩
    exact ⟨⟨(x,y),hne⟩,hh⟩


-- @@ L154-164 verbatim
lemma finite_value_sum (x y : P) (hxy : x ≠ y) :
    (∑ v ∈ badPlaces Z hZ, (finite Z hZ v).value x y) =
      ∑ᶠ v : FinitePlace K, -Real.log (v (Z x-Z y)) := by
  simp only [finite,hxy,reduceIte]
  symm
  apply finsum_eq_sum_of_support_subset
  intro v hv
  apply (badPlaces_mem Z hZ v).mpr
  refine ⟨x,y,hxy,?_⟩
  intro hh
  exact hv (by simp [hh])


-- @@ L166-168 verbatim
def S (x : P) : ℝ :=
  (∑ v : InfinitePlace K, Arithmetic.archWeight v * ∫ ω, (arch Z v ω).potential x ∂Grid.fullLaw) +
    (Module.finrank ℚ K : ℝ)⁻¹ * ∑ v ∈ badPlaces Z hZ, (finite Z hZ v).potential x


-- @@ L170-172 verbatim
def L (x y : P) (hxy : x ≠ y) : ℝ :=
  (∑ v : InfinitePlace K, Arithmetic.archWeight v * ∫ ω, (arch Z v ω).overlapLength x y hxy ∂Grid.fullLaw) +
    (Module.finrank ℚ K : ℝ)⁻¹ * ∑ v ∈ badPlaces Z hZ, (finite Z hZ v).overlapLength x y hxy


-- @@ L174-176 verbatim
def M : ℝ :=
  (∑ v : InfinitePlace K, Arithmetic.archWeight v * ∫ ω, (arch Z v ω).M ∂Grid.fullLaw) +
    (Module.finrank ℚ K : ℝ)⁻¹ * ∑ v ∈ badPlaces Z hZ, (finite Z hZ v).M


-- @@ L178-215 verbatim
lemma coordinate_overlap_identity (hn : 2 ≤ Fintype.card P) (x y : P) (hxy : x ≠ y) :
    L Z hZ x y hxy = Grid.kappa - M Z hZ + S Z hZ x + S Z hZ y := by
  have harch : (∑ v : InfinitePlace K, Arithmetic.archWeight v *
      (∫ ω, (arch Z v ω).M ∂Grid.fullLaw)) +
      (∑ v : InfinitePlace K, Arithmetic.archWeight v *
      (∫ ω, (arch Z v ω).overlapLength x y hxy ∂Grid.fullLaw)) -
      (∑ v : InfinitePlace K, Arithmetic.archWeight v *
      (∫ ω, (arch Z v ω).potential x ∂Grid.fullLaw)) -
      (∑ v : InfinitePlace K, Arithmetic.archWeight v *
      (∫ ω, (arch Z v ω).potential y ∂Grid.fullLaw)) =
      (∑ v : InfinitePlace K, Arithmetic.archWeight v * (-Real.log (v (Z x-Z y)))) + Grid.kappa := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    have he : ∀ v : InfinitePlace K,
        Arithmetic.archWeight v * (∫ ω, (arch Z v ω).M ∂Grid.fullLaw) +
        Arithmetic.archWeight v * (∫ ω, (arch Z v ω).overlapLength x y hxy ∂Grid.fullLaw) -
        Arithmetic.archWeight v * (∫ ω, (arch Z v ω).potential x ∂Grid.fullLaw) -
        Arithmetic.archWeight v * (∫ ω, (arch Z v ω).potential y ∂Grid.fullLaw) =
        Arithmetic.archWeight v * (-Real.log (v (Z x-Z y))) + Arithmetic.archWeight v * Grid.kappa := by
      intro v
      have hh := Depth.integral_depth_identity (arch Z v) (arch_measurable Z hZ v)
        (arch_integrable Z hZ v) hn x y hxy
      rw [arch_mean Z hZ v x y hxy] at hh
      linear_combination -Arithmetic.archWeight v * hh
    simp_rw [he]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, Arithmetic.sum_archWeight,one_mul]
  have hfin : (∑ v ∈ badPlaces Z hZ, (finite Z hZ v).M) +
      (∑ v ∈ badPlaces Z hZ, (finite Z hZ v).overlapLength x y hxy) -
      (∑ v ∈ badPlaces Z hZ, (finite Z hZ v).potential x) -
      (∑ v ∈ badPlaces Z hZ, (finite Z hZ v).potential y) =
      ∑ᶠ v : FinitePlace K, -Real.log (v (Z x-Z y)) := by
    rw [← finite_value_sum Z hZ x y hxy, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro v _
    exact ((finite Z hZ v).depth_identity hn x y hxy).symm
  have hprod := Arithmetic.normalized_log_product_formula (Z x-Z y) (sub_ne_zero.mpr (hZ.ne hxy))
  dsimp only [L,M,S]
  linear_combination harch + (Module.finrank ℚ K : ℝ)⁻¹ * hfin + hprod


-- @@ L217-221 verbatim
lemma S_nonneg (x : P) : 0 ≤ S Z hZ x := by
  apply add_nonneg
  · exact Finset.sum_nonneg (fun v _ => mul_nonneg (Arithmetic.archWeight_nonneg v)
      (integral_nonneg (fun ω => (arch Z v ω).potential_nonneg x)))
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun v _ => (finite Z hZ v).potential_nonneg x))


-- @@ L223-227 verbatim
lemma L_nonneg (x y : P) (hxy : x ≠ y) : 0 ≤ L Z hZ x y hxy := by
  apply add_nonneg
  · exact Finset.sum_nonneg (fun v _ => mul_nonneg (Arithmetic.archWeight_nonneg v)
      (integral_nonneg (fun ω => (arch Z v ω).overlapLength_nonneg x y hxy)))
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun v _ => (finite Z hZ v).overlapLength_nonneg x y hxy))


-- @@ L229-229 verbatim
end WeakPinned.Global


-- @@ L231-231 verbatim
namespace WeakPinned.Hierarchy.Depth

-- @@ L232-232 verbatim
open MeasureTheory

-- @@ L233-233 verbatim
variable {P : Type u3} [Fintype P] [DecidableEq P]

-- @@ L234-234 verbatim
variable (d : Depth P)


-- @@ L236-236 verbatim
def count (r : ℝ) (C : Finset P) : ℝ := (d.transformed r).count C


-- @@ L238-238 verbatim
def mass (C : Finset P) : ℝ := if 2 ≤ C.card then ∫ r, d.count r C else 0


-- @@ L240-248 verbatim
lemma sum_map_count (m : Multiset (Finset P)) (f : Finset P → ℝ) :
    (m.map f).sum = ∑ C, (m.count C : ℝ) * f C := by
  induction m using Multiset.induction_on with
  | empty => simp
  | @cons a m ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.count_cons]
      simp_rw [Nat.cast_add, add_mul]
      rw [Finset.sum_add_distrib]
      simp [add_comm]


-- @@ L250-251 verbatim
lemma sumCells_count (f : Finset P → ℝ) (r : ℝ) :
    d.sumCells f r = ∑ C, d.count r C * f C := sum_map_count _ _


-- @@ L253-253 verbatim
lemma count_nonneg (r : ℝ) (C : Finset P) : 0 ≤ d.count r C := Nat.cast_nonneg _


-- @@ L255-260 verbatim
lemma count_le_overlap (r : ℝ) (C : Finset P) (x y : P) (hx : x ∈ C) (hy : y ∈ C) :
    d.count r C ≤ d.pairOverlap r x y := by
  rw [pairOverlap, d.sumCells_count]
  calc
    d.count r C = d.count r C * (if x ∈ C ∧ y ∈ C then (1 : ℝ) else 0) := by simp [hx,hy]
    _ ≤ _ := Finset.single_le_sum (f := fun D => d.count r D * (if x ∈ D ∧ y ∈ D then (1 : ℝ) else 0)) (fun D _ => mul_nonneg (d.count_nonneg r D) (by positivity)) (Finset.mem_univ C)


-- @@ L262-269 verbatim
lemma measurable_count (C : Finset P) : Measurable (fun r => d.count r C) := by
  let F : Finset (Finset P) × Finset (Finset P) → ℝ := fun st =>
    (((st.1.filter (fun D => ¬Fintype.card P < 2*D.card)).val +
       st.2.val.map (fun D => Dᶜ)).count C : ℝ)
  have hh : Measurable (fun r => F (d.cells r, d.giants r)) :=
    (measurable_of_finite F).comp (d.measurable_cells.prodMk d.measurable_giants)
  change Measurable (fun r => F (d.cells r, d.giants r))
  exact hh


-- @@ L271-276 verbatim
lemma integrable_count (hn : 2 ≤ Fintype.card P) (C : Finset P) (hC : 2 ≤ C.card) :
    Integrable (fun r => d.count r C) := by
  obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp hC
  apply (d.integrable_pairOverlap hn x y hxy).mono' (d.measurable_count C).aestronglyMeasurable
  filter_upwards with r
  simpa only [Real.norm_eq_abs, abs_of_nonneg (d.count_nonneg r C)] using d.count_le_overlap r C x y hx hy


-- @@ L278-282 verbatim
lemma mass_nonneg (C : Finset P) : 0 ≤ d.mass C := by
  unfold mass
  split_ifs
  · exact integral_nonneg (fun r => d.count_nonneg r C)
  · rfl


-- @@ L284-285 verbatim
lemma mass_singleton (C : Finset P) (hC : C.card ≤ 1) : d.mass C = 0 := by
  simp [mass, show ¬2 ≤ C.card by omega]


-- @@ L287-293 verbatim
lemma mass_le_overlap (hn : 2 ≤ Fintype.card P) (C : Finset P) (x y : P)
    (hxy : x ≠ y) (hx : x ∈ C) (hy : y ∈ C) :
    d.mass C ≤ d.overlapLength x y hxy := by
  have hC : 2 ≤ C.card := Finset.one_lt_card.mpr ⟨x,hx,y,hy,hxy⟩
  rw [mass, ite_eq_left hC, overlapLength]
  exact integral_mono (d.integrable_count hn C hC) (d.integrable_pairOverlap hn x y hxy)
    (fun r => d.count_le_overlap r C x y hx hy)


-- @@ L295-308 verbatim
lemma integral_sumCells (hn : 2 ≤ Fintype.card P) (f : Finset P → ℝ)
    (hf : ∀ C, C.card ≤ 1 → f C = 0) :
    (∫ r, d.sumCells f r) = ∑ C, d.mass C * f C := by
  have hi (C : Finset P) : Integrable (fun r => d.count r C * f C) := by
    by_cases hC : 2 ≤ C.card
    · exact (d.integrable_count hn C hC).mul_const _
    · simp [hf C (by omega)]
  simp_rw [d.sumCells_count]
  rw [integral_finsetSum _ (fun C _ => hi C)]
  apply Finset.sum_congr rfl
  intro C _
  by_cases hC : 2 ≤ C.card
  · simp [mass,hC,integral_mul_const]
  · simp [mass,hC,hf C (by omega)]


-- @@ L310-320 verbatim
lemma mass_overlap (hn : 2 ≤ Fintype.card P) (x y : P) (hxy : x ≠ y) :
    (∑ C, d.mass C * (if x ∈ C ∧ y ∈ C then (1 : ℝ) else 0)) =
      d.overlapLength x y hxy := by
  symm
  apply d.integral_sumCells hn
  intro C hC
  have hh : ¬(x ∈ C ∧ y ∈ C) := by
    rintro ⟨hx,hy⟩
    have := Finset.one_lt_card.mpr ⟨x,hx,y,hy,hxy⟩
    omega
  simp [hh]


-- @@ L322-322 verbatim
section Param

-- @@ L323-324 verbatim
variable {Ω : Type u4} [MeasurableSpace Ω] (D : Ω → Depth P)
    (hD : ∀ x y, Measurable (fun ω => (D ω).value x y))

-- @@ L325-325 verbatim
include hD

-- @@ L326-339 verbatim
lemma measurable_count_param (C : Finset P) :
    Measurable (fun p : Ω × ℝ => (D p.1).count p.2 C) := by
  let F : Finset (Finset P) × Finset (Finset P) → ℝ := fun st =>
    (((st.1.filter (fun E => ¬Fintype.card P < 2*E.card)).val +
       st.2.val.map (fun E => Eᶜ)).count C : ℝ)
  have hm : Measurable (fun p : Ω×ℝ => ((D p.1).cells p.2, (D p.1).giants p.2)) :=
    (measurable_cells_param (P:=P) (Ω:=Ω×ℝ) (fun p : Ω×ℝ => D p.1)
      (fun x y => (hD x y).comp measurable_fst) Prod.snd measurable_snd).prodMk
    (measurable_giants_param (P:=P) (Ω:=Ω×ℝ) (fun p : Ω×ℝ => D p.1)
      (fun x y => (hD x y).comp measurable_fst) Prod.snd measurable_snd)
  have hh : Measurable (fun p : Ω×ℝ => F ((D p.1).cells p.2, (D p.1).giants p.2)) :=
    (measurable_of_finite F).comp hm
  change Measurable (fun p : Ω×ℝ => F ((D p.1).cells p.2, (D p.1).giants p.2))
  exact hh


-- @@ L341-345 verbatim
lemma measurable_mass_param (C : Finset P) : Measurable (fun ω => (D ω).mass C) := by
  unfold mass
  split_ifs with hC
  · exact (measurable_count_param D hD C).stronglyMeasurable.integral_prod_right.measurable
  · exact measurable_const


-- @@ L347-359 verbatim
lemma integrable_mass_param {μ : Measure Ω}
    (hi : ∀ x y, Integrable (fun ω => (D ω).value x y) μ)
    (hn : 2 ≤ Fintype.card P) (C : Finset P) :
    Integrable (fun ω => (D ω).mass C) μ := by
  by_cases hC : 2 ≤ C.card
  · obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp hC
    apply (integrable_overlapLength_param D hD hi hn x y hxy).mono'
      (measurable_mass_param D hD C).aestronglyMeasurable
    filter_upwards with ω
    simpa only [Real.norm_eq_abs, abs_of_nonneg ((D ω).mass_nonneg C)] using
      (D ω).mass_le_overlap hn C x y hxy hx hy
  · simp only [mass, hC, reduceIte]
    exact integrable_zero _ _ _


-- @@ L361-368 verbatim
lemma averaged_mass_overlap {μ : Measure Ω}
    (hi : ∀ x y, Integrable (fun ω => (D ω).value x y) μ)
    (hn : 2 ≤ Fintype.card P) (x y : P) (hxy : x ≠ y) :
    (∑ C, (∫ ω, (D ω).mass C ∂μ) * (if x ∈ C ∧ y ∈ C then (1 : ℝ) else 0)) =
      ∫ ω, (D ω).overlapLength x y hxy ∂μ := by
  simp_rw [← integral_mul_const]
  rw [← integral_finsetSum _ (fun C _ => (integrable_mass_param D hD hi hn C).mul_const _)]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun ω => (D ω).mass_overlap hn x y hxy))

-- @@ L369-369 verbatim
end Param

-- @@ L370-370 verbatim
end WeakPinned.Hierarchy.Depth


-- @@ L372-372 verbatim
end

-- @@ L373-373 verbatim
end

-- @@ L374-374 verbatim
end

-- @@ L375-375 verbatim
end

-- @@ L376-376 verbatim
end


-- @@ L378-378 verbatim
end OAI
