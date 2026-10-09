import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-7 verbatim
/-!
# Segment tests, their completion, and coordinate functionals
-/


-- @@ L9-9 verbatim
noncomputable section


-- @@ L11-11 verbatim
open scoped BigOperators

-- @@ L12-12 verbatim
open Finset


-- @@ L14-14 verbatim
namespace SegmentLenses
















-- @@ L30-30 verbatim
abbrev InfiniteVertex := List ℕ




-- @@ L34-34 verbatim
def ForestVertex := {p : ℕ × List ℕ // 1 ≤ p.1 ∧ p.2.length ≤ p.1}



-- @@ L37-38 verbatim
def ForestAncestor (a b : ForestVertex) : Prop :=
  a.val.1 = b.val.1 ∧ a.val.2.IsPrefix b.val.2



-- @@ L41-42 verbatim
def IsInterval {V : Type*} (ancestor : V → V → Prop) (S : Finset V) : Prop :=
  ∃ a b, ancestor a b ∧ ∀ v, v ∈ S ↔ ancestor a v ∧ ancestor v b



-- @@ L45-46 verbatim
def Ancestral {V : Type*} (ancestor : V → V → Prop) (H : Finset V) : Prop :=
  ∀ ⦃a b⦄, b ∈ H → ancestor a b → a ∈ H



-- @@ L49-51 verbatim
class SegmentSystem (V : Type*) where
  isSegment : Finset V → Prop
  singleton : ∀ v, isSegment {v}




-- @@ L55-58 verbatim
structure SegmentFamily (V : Type*) [SegmentSystem V] where
  sets : Finset (Finset V)
  segment : ∀ S ∈ sets, SegmentSystem.isSegment S
  disjoint : (sets : Set (Finset V)).PairwiseDisjoint id


-- @@ L60-60 verbatim
namespace SegmentFamily

-- @@ L61-61 verbatim
variable {V : Type*} [SegmentSystem V]


-- @@ L63-63 verbatim
instance : Inhabited (SegmentFamily V) := ⟨⟨∅, by simp, by simp⟩⟩



-- @@ L66-67 verbatim
def column (F : SegmentFamily V) (v : V) : EuclideanSpace ℝ F.sets :=
  by classical exact WithLp.toLp 2 (fun S => if v ∈ S.val then 1 else 0)


-- @@ L69-91 verbatim
theorem norm_column_le (F : SegmentFamily V) (v : V) : ‖F.column v‖ ≤ 1 := by
  classical
  by_cases hv : ∃ S ∈ F.sets, v ∈ S
  · obtain ⟨S, hS, hvS⟩ := hv
    have he : F.column v = PiLp.single 2 (⟨S, hS⟩ : F.sets) (1 : ℝ) := by
      ext T
      change (if v ∈ T.val then (1 : ℝ) else 0) = _
      by_cases hTS : T = ⟨S, hS⟩
      · subst T
        simp [hvS]
      · have hn : v ∉ T.val := by
          intro hvT
          have hne : T.val ≠ S := fun h => hTS (Subtype.ext h)
          exact Finset.disjoint_left.mp (F.disjoint T.property hS hne) hvT hvS
        simp [hTS, hn]
    rw [he, PiLp.norm_single]
    norm_num
  · have he : F.column v = 0 := by
      ext S
      have hn : v ∉ S.val := fun h => hv ⟨S.val, S.property, h⟩
      simp [column, hn]
    rw [he, norm_zero]
    norm_num



-- @@ L94-95 verbatim
def test (F : SegmentFamily V) : (V →₀ ℝ) →ₗ[ℝ] EuclideanSpace ℝ F.sets :=
  Finsupp.linearCombination ℝ F.column


-- @@ L97-112 verbatim
theorem test_apply (F : SegmentFamily V) (u : V →₀ ℝ) (S : F.sets) :
    F.test u S = ∑ v ∈ S.val, u v := by
  classical
  simp only [test, Finsupp.linearCombination_apply, Finsupp.sum,
    WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, column,
    smul_eq_mul]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  apply Finset.sum_subset
  · intro v hv
    exact (Finset.mem_filter.mp hv).2
  · intro v hv hnv
    have hnot : v ∉ u.support := by
      intro hvs
      exact hnv (Finset.mem_filter.mpr ⟨hvs, hv⟩)
    exact Finsupp.notMem_support_iff.mp hnot



-- @@ L115-126 verbatim
theorem norm_test_le (F : SegmentFamily V) (u : V →₀ ℝ) :
    ‖F.test u‖ ≤ ∑ v ∈ u.support, |u v| := by
  classical
  rw [test, Finsupp.linearCombination_apply, Finsupp.sum]
  calc
    ‖∑ v ∈ u.support, u v • F.column v‖ ≤
        ∑ v ∈ u.support, ‖u v • F.column v‖ := norm_sum_le _ _
    _ ≤ ∑ v ∈ u.support, |u v| := by
      apply Finset.sum_le_sum
      intro v hv
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg _) (F.norm_column_le v)



-- @@ L129-130 verbatim
def seminorm (F : SegmentFamily V) : Seminorm ℝ (V →₀ ℝ) :=
  (normSeminorm ℝ (EuclideanSpace ℝ F.sets)).comp F.test


-- @@ L132-136 verbatim
theorem seminorm_sq (F : SegmentFamily V) (u : V →₀ ℝ) :
    F.seminorm u ^ 2 = ∑ S : F.sets, (∑ v ∈ S.val, u v) ^ 2 := by
  change ‖F.test u‖ ^ 2 = _
  rw [EuclideanSpace.real_norm_sq_eq]
  simp_rw [F.test_apply]



-- @@ L139-149 verbatim
def singleton (v : V) : SegmentFamily V where
  sets := {{v}}
  segment := by
    intro S h
    have he : S = {v} := Finset.mem_singleton.mp h
    rw [he]
    exact SegmentSystem.singleton v
  disjoint := by
    intro S hS T hT hne
    simp only [Finset.mem_coe, Finset.mem_singleton] at hS hT
    exact False.elim (hne (hS.trans hT.symm))


-- @@ L151-159 verbatim
theorem singleton_seminorm (v : V) (u : V →₀ ℝ) :
    (singleton v).seminorm u = |u v| := by
  have h := (singleton v).seminorm_sq u
  have hh : (∑ S : (singleton v).sets, (∑ w ∈ S.val, u w) ^ 2) = u v ^ 2 := by
    exact (Finset.sum_coe_sort (singleton v).sets
      (fun S : Finset V => (∑ w ∈ S, u w) ^ 2)).trans (by simp [singleton])
  rw [hh] at h
  have hn := apply_nonneg (singleton v).seminorm u
  nlinarith [sq_abs (u v), abs_nonneg (u v)]


-- @@ L161-161 verbatim
end SegmentFamily




-- @@ L165-166 verbatim
def segmentSeminorm (V : Type*) [SegmentSystem V] : Seminorm ℝ (V →₀ ℝ) :=
  ⨆ F : SegmentFamily V, F.seminorm


-- @@ L168-173 verbatim
theorem segmentTests_bdd (V : Type*) [SegmentSystem V] :
    BddAbove (Set.range (SegmentFamily.seminorm (V := V))) := by
  rw [Seminorm.bddAbove_iff]
  refine ⟨fun u => ∑ v ∈ u.support, |u v|, ?_⟩
  rintro _ ⟨p, ⟨F, rfl⟩, rfl⟩ u
  exact F.norm_test_le u


-- @@ L175-177 verbatim
theorem segmentSeminorm_apply {V : Type*} [SegmentSystem V] (u : V →₀ ℝ) :
    segmentSeminorm V u = ⨆ F : SegmentFamily V, F.seminorm u :=
  Seminorm.iSup_apply (segmentTests_bdd V)


-- @@ L179-182 verbatim
theorem le_segmentSeminorm {V : Type*} [SegmentSystem V]
    (F : SegmentFamily V) (u : V →₀ ℝ) : F.seminorm u ≤ segmentSeminorm V u := by
  have h := le_ciSup (f := fun G : SegmentFamily V => G.seminorm) (segmentTests_bdd V) F
  exact Seminorm.le_def.mp h u


-- @@ L184-187 verbatim
theorem abs_coord_le {V : Type*} [SegmentSystem V] (u : V →₀ ℝ) (v : V) :
    |u v| ≤ segmentSeminorm V u := by
  rw [← SegmentFamily.singleton_seminorm v u]
  exact le_segmentSeminorm _ _



-- @@ L190-199 verbatim
theorem segmentSeminorm_eq_zero {V : Type*} [SegmentSystem V] (u : V →₀ ℝ) :
    segmentSeminorm V u = 0 ↔ u = 0 := by
  constructor
  · intro h
    ext v
    have hh := abs_coord_le u v
    rw [h] at hh
    simpa using hh
  · rintro rfl
    exact map_zero _




-- @@ L203-235 verbatim
theorem indexed_test_bound {V ι : Type*} [SegmentSystem V] [Fintype ι]
    (u : V →₀ ℝ) (S : ι → Finset V)
    (hS : ∀ i, S i = ∅ ∨ SegmentSystem.isSegment (S i))
    (hd : Pairwise fun i j => Disjoint (S i) (S j)) :
    ∑ i, (∑ v ∈ S i, u v) ^ 2 ≤ segmentSeminorm V u ^ 2 := by
  classical
  let F : SegmentFamily V :=
    { sets := (Finset.univ.image S).erase ∅
      segment := by
        intro T hT
        obtain ⟨hne, him⟩ := Finset.mem_erase.mp hT
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp him
        exact (hS i).resolve_left hne
      disjoint := by
        intro A hA B hB hne
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_erase.mp hA).2
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_erase.mp hB).2
        exact hd (fun hij => hne (congrArg S hij)) }
  have he : F.seminorm u ^ 2 = ∑ i, (∑ v ∈ S i, u v) ^ 2 := by
    rw [F.seminorm_sq]
    rw [Finset.sum_coe_sort F.sets (fun T : Finset V => (∑ v ∈ T, u v) ^ 2)]
    change (∑ T ∈ (Finset.univ.image S).erase ∅, (∑ v ∈ T, u v) ^ 2) = _
    rw [Finset.sum_erase _ (by simp)]
    apply Finset.sum_image_of_pairwise_eq_zero
    intro i hi j hj hij heq
    have hempty : S i = ∅ := by
      have hh : Disjoint (S i) (S j) := hd hij
      rw [← heq] at hh
      exact disjoint_self.mp hh
    simp [hempty]
  rw [← he]
  exact (sq_le_sq₀ (apply_nonneg F.seminorm u)
    (apply_nonneg (segmentSeminorm V) u)).mpr (le_segmentSeminorm F u)




-- @@ L239-271 verbatim
theorem refinement_test_bound {V ι : Type*} [SegmentSystem V] [Fintype ι]
    (u : V →₀ ℝ) (S A B : ι → Finset V)
    (hd : Pairwise fun i j => Disjoint (S i) (S j))
    (hA : ∀ i, A i ⊆ S i) (hB : ∀ i, B i ⊆ S i)
    (hAB : ∀ i, Disjoint (A i) (B i))
    (hsA : ∀ i, A i = ∅ ∨ SegmentSystem.isSegment (A i))
    (hsB : ∀ i, B i = ∅ ∨ SegmentSystem.isSegment (B i)) :
    ∑ i, ((∑ v ∈ A i, u v) ^ 2 + (∑ v ∈ B i, u v) ^ 2) ≤
      segmentSeminorm V u ^ 2 := by
  classical
  let pieces : ι × Bool → Finset V := fun j => if j.2 then B j.1 else A j.1
  have hp : ∀ j, pieces j = ∅ ∨ SegmentSystem.isSegment (pieces j) := by
    rintro ⟨i, b⟩
    cases b
    · exact hsA i
    · exact hsB i
  have hsub : ∀ j : ι × Bool, pieces j ⊆ S j.1 := by
    rintro ⟨i, b⟩
    cases b
    · exact hA i
    · exact hB i
  have hpd : Pairwise fun i j => Disjoint (pieces i) (pieces j) := by
    rintro ⟨i, b⟩ ⟨j, c⟩ hne
    by_cases hij : i = j
    · subst j
      cases b <;> cases c
      · exact False.elim (hne rfl)
      · exact hAB i
      · exact (hAB i).symm
      · exact False.elim (hne rfl)
    · exact (hd hij).mono (hsub _) (hsub _)
  have h := indexed_test_bound u pieces hp hpd
  simpa [Fintype.sum_prod_type, pieces, Fintype.sum_bool, add_comm] using h




-- @@ L275-275 verbatim
def Test (V : Type*) := V →₀ ℝ


-- @@ L277-277 verbatim
namespace Test

-- @@ L278-278 verbatim
variable {V : Type*}

-- @@ L279-279 verbatim
instance : AddCommGroup (Test V) := inferInstanceAs (AddCommGroup (V →₀ ℝ))

-- @@ L280-280 verbatim
instance : Module ℝ (Test V) := inferInstanceAs (Module ℝ (V →₀ ℝ))


-- @@ L282-282 verbatim
def coeff (u : Test V) : V →₀ ℝ := u


-- @@ L284-284 verbatim
def ofFinsupp (u : V →₀ ℝ) : Test V := u


-- @@ L286-286 verbatim
variable [SegmentSystem V]

-- @@ L287-287 verbatim
instance : Norm (Test V) where norm u := segmentSeminorm V u.coeff


-- @@ L289-293 verbatim
theorem normCore : NormedSpace.Core ℝ (Test V) where
  norm_nonneg u := apply_nonneg (segmentSeminorm V) u.coeff
  norm_smul c u := map_smul_eq_mul (segmentSeminorm V) c u.coeff
  norm_triangle u v := map_add_le_add (segmentSeminorm V) u.coeff v.coeff
  norm_eq_zero_iff u := segmentSeminorm_eq_zero u.coeff


-- @@ L295-391 verbatim
instance : NormedAddCommGroup (Test V) := by
  have norm_column_le {V : Type _} [SegmentSystem V] (F : SegmentFamily V) (v : V) : ‖F.column v‖ ≤ 1 := by
    classical
    by_cases hv : ∃ S ∈ F.sets, v ∈ S
    · obtain ⟨S, hS, hvS⟩ := hv
      have he : F.column v = PiLp.single 2 (⟨S, hS⟩ : F.sets) (1 : ℝ) := by
        ext T
        change (if v ∈ T.val then (1 : ℝ) else 0) = _
        by_cases hTS : T = ⟨S, hS⟩
        · subst T
          simp [hvS]
        · have hn : v ∉ T.val := by
            intro hvT
            have hne : T.val ≠ S := fun h => hTS (Subtype.ext h)
            exact Finset.disjoint_left.mp (F.disjoint T.property hS hne) hvT hvS
          simp [hTS, hn]
      rw [he, PiLp.norm_single]
      norm_num
    · have he : F.column v = 0 := by
        ext S
        have hn : v ∉ S.val := fun h => hv ⟨S.val, S.property, h⟩
        simp [SegmentFamily.column, hn]
      rw [he, norm_zero]
      norm_num
  have test_apply {V : Type _} [SegmentSystem V] (F : SegmentFamily V) (u : V →₀ ℝ) (S : F.sets) :
      F.test u S = ∑ v ∈ S.val, u v := by
    classical
    simp only [SegmentFamily.test, Finsupp.linearCombination_apply, Finsupp.sum,
      WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, SegmentFamily.column,
      smul_eq_mul]
    simp only [mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    apply Finset.sum_subset
    · intro v hv
      exact (Finset.mem_filter.mp hv).2
    · intro v hv hnv
      have hnot : v ∉ u.support := by
        intro hvs
        exact hnv (Finset.mem_filter.mpr ⟨hvs, hv⟩)
      exact Finsupp.notMem_support_iff.mp hnot
  have norm_test_le {V : Type _} [SegmentSystem V] (F : SegmentFamily V) (u : V →₀ ℝ) :
      ‖F.test u‖ ≤ ∑ v ∈ u.support, |u v| := by
    classical
    rw [SegmentFamily.test, Finsupp.linearCombination_apply, Finsupp.sum]
    calc
      ‖∑ v ∈ u.support, u v • F.column v‖ ≤
          ∑ v ∈ u.support, ‖u v • F.column v‖ := norm_sum_le _ _
      _ ≤ ∑ v ∈ u.support, |u v| := by
        apply Finset.sum_le_sum
        intro v hv
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_of_le_one_right (abs_nonneg _) (norm_column_le F v)
  have seminorm_sq {V : Type _} [SegmentSystem V] (F : SegmentFamily V) (u : V →₀ ℝ) :
      F.seminorm u ^ 2 = ∑ S : F.sets, (∑ v ∈ S.val, u v) ^ 2 := by
    change ‖F.test u‖ ^ 2 = _
    rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro S _
    rw [test_apply]
  have singleton_seminorm {V : Type _} [SegmentSystem V] (v : V) (u : V →₀ ℝ) :
      (SegmentFamily.singleton v).seminorm u = |u v| := by
    have h := seminorm_sq (SegmentFamily.singleton v) u
    have hh : (∑ S : (SegmentFamily.singleton v).sets, (∑ w ∈ S.val, u w) ^ 2) = u v ^ 2 := by
      exact (Finset.sum_coe_sort (SegmentFamily.singleton v).sets
        (fun S : Finset V => (∑ w ∈ S, u w) ^ 2)).trans (by simp [SegmentFamily.singleton])
    rw [hh] at h
    have hn := apply_nonneg (SegmentFamily.singleton v).seminorm u
    nlinarith [sq_abs (u v), abs_nonneg (u v)]
  have segmentTests_bdd (V : Type _) [SegmentSystem V] :
      BddAbove (Set.range (SegmentFamily.seminorm (V := V))) := by
    rw [Seminorm.bddAbove_iff]
    refine ⟨fun u => ∑ v ∈ u.support, |u v|, ?_⟩
    rintro _ ⟨p, ⟨F, rfl⟩, rfl⟩ u
    exact norm_test_le F u
  have le_segmentSeminorm {V : Type _} [SegmentSystem V]
      (F : SegmentFamily V) (u : V →₀ ℝ) : F.seminorm u ≤ segmentSeminorm V u := by
    have h := le_ciSup (f := fun G : SegmentFamily V => G.seminorm) (segmentTests_bdd V) F
    exact Seminorm.le_def.mp h u
  have abs_coord_le {V : Type _} [SegmentSystem V] (u : V →₀ ℝ) (v : V) :
      |u v| ≤ segmentSeminorm V u := by
    rw [← singleton_seminorm v u]
    exact le_segmentSeminorm _ _
  have segmentSeminorm_eq_zero {V : Type _} [SegmentSystem V] (u : V →₀ ℝ) :
      segmentSeminorm V u = 0 ↔ u = 0 := by
    constructor
    · intro h
      ext v
      have hh := abs_coord_le u v
      rw [h] at hh
      simpa using hh
    · rintro rfl
      exact map_zero _
  exact NormedAddCommGroup.ofCore (𝕜 := ℝ) {
    norm_nonneg u := apply_nonneg (segmentSeminorm V) u.coeff
    norm_smul c u := map_smul_eq_mul (segmentSeminorm V) c u.coeff
    norm_triangle u v := map_add_le_add (segmentSeminorm V) u.coeff v.coeff
    norm_eq_zero_iff u := segmentSeminorm_eq_zero u.coeff }

-- @@ L392-393 verbatim
instance : NormedSpace ℝ (Test V) where
  norm_smul_le c u := le_of_eq (map_smul_eq_mul (segmentSeminorm V) c u.coeff)



-- @@ L396-484 verbatim
def evaluation (v : V) : Test V →L[ℝ] ℝ := by
  have norm_column_le {V : Type _} [SegmentSystem V] (F : SegmentFamily V) (v : V) : ‖F.column v‖ ≤ 1 := by
    classical
    by_cases hv : ∃ S ∈ F.sets, v ∈ S
    · obtain ⟨S, hS, hvS⟩ := hv
      have he : F.column v = PiLp.single 2 (⟨S, hS⟩ : F.sets) (1 : ℝ) := by
        ext T
        change (if v ∈ T.val then (1 : ℝ) else 0) = _
        by_cases hTS : T = ⟨S, hS⟩
        · subst T
          simp [hvS]
        · have hn : v ∉ T.val := by
            intro hvT
            have hne : T.val ≠ S := fun h => hTS (Subtype.ext h)
            exact Finset.disjoint_left.mp (F.disjoint T.property hS hne) hvT hvS
          simp [hTS, hn]
      rw [he, PiLp.norm_single]
      norm_num
    · have he : F.column v = 0 := by
        ext S
        have hn : v ∉ S.val := fun h => hv ⟨S.val, S.property, h⟩
        simp [SegmentFamily.column, hn]
      rw [he, norm_zero]
      norm_num
  have test_apply {V : Type _} [SegmentSystem V] (F : SegmentFamily V) (u : V →₀ ℝ) (S : F.sets) :
      F.test u S = ∑ v ∈ S.val, u v := by
    classical
    simp only [SegmentFamily.test, Finsupp.linearCombination_apply, Finsupp.sum,
      WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, SegmentFamily.column,
      smul_eq_mul]
    simp only [mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    apply Finset.sum_subset
    · intro v hv
      exact (Finset.mem_filter.mp hv).2
    · intro v hv hnv
      have hnot : v ∉ u.support := by
        intro hvs
        exact hnv (Finset.mem_filter.mpr ⟨hvs, hv⟩)
      exact Finsupp.notMem_support_iff.mp hnot
  have norm_test_le {V : Type _} [SegmentSystem V] (F : SegmentFamily V) (u : V →₀ ℝ) :
      ‖F.test u‖ ≤ ∑ v ∈ u.support, |u v| := by
    classical
    rw [SegmentFamily.test, Finsupp.linearCombination_apply, Finsupp.sum]
    calc
      ‖∑ v ∈ u.support, u v • F.column v‖ ≤
          ∑ v ∈ u.support, ‖u v • F.column v‖ := norm_sum_le _ _
      _ ≤ ∑ v ∈ u.support, |u v| := by
        apply Finset.sum_le_sum
        intro v hv
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_of_le_one_right (abs_nonneg _) (norm_column_le F v)
  have seminorm_sq {V : Type _} [SegmentSystem V] (F : SegmentFamily V) (u : V →₀ ℝ) :
      F.seminorm u ^ 2 = ∑ S : F.sets, (∑ v ∈ S.val, u v) ^ 2 := by
    change ‖F.test u‖ ^ 2 = _
    rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro S _
    rw [test_apply]
  have singleton_seminorm {V : Type _} [SegmentSystem V] (v : V) (u : V →₀ ℝ) :
      (SegmentFamily.singleton v).seminorm u = |u v| := by
    have h := seminorm_sq (SegmentFamily.singleton v) u
    have hh : (∑ S : (SegmentFamily.singleton v).sets, (∑ w ∈ S.val, u w) ^ 2) = u v ^ 2 := by
      exact (Finset.sum_coe_sort (SegmentFamily.singleton v).sets
        (fun S : Finset V => (∑ w ∈ S, u w) ^ 2)).trans (by simp [SegmentFamily.singleton])
    rw [hh] at h
    have hn := apply_nonneg (SegmentFamily.singleton v).seminorm u
    nlinarith [sq_abs (u v), abs_nonneg (u v)]
  have segmentTests_bdd (V : Type _) [SegmentSystem V] :
      BddAbove (Set.range (SegmentFamily.seminorm (V := V))) := by
    rw [Seminorm.bddAbove_iff]
    refine ⟨fun u => ∑ v ∈ u.support, |u v|, ?_⟩
    rintro _ ⟨p, ⟨F, rfl⟩, rfl⟩ u
    exact norm_test_le F u
  have le_segmentSeminorm {V : Type _} [SegmentSystem V]
      (F : SegmentFamily V) (u : V →₀ ℝ) : F.seminorm u ≤ segmentSeminorm V u := by
    have h := le_ciSup (f := fun G : SegmentFamily V => G.seminorm) (segmentTests_bdd V) F
    exact Seminorm.le_def.mp h u
  have abs_coord_le {V : Type _} [SegmentSystem V] (u : V →₀ ℝ) (v : V) :
      |u v| ≤ segmentSeminorm V u := by
    rw [← singleton_seminorm v u]
    exact le_segmentSeminorm _ _
  exact let f : Test V →ₗ[ℝ] ℝ :=
      { toFun := fun u => u.coeff v
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    f.mkContinuous 1 (fun u => by
      change |u.coeff v| ≤ 1 * segmentSeminorm V u.coeff
      simpa only [one_mul] using abs_coord_le u.coeff v)


-- @@ L486-486 verbatim
end Test



-- @@ L489-489 verbatim
abbrev Primal (V : Type*) [SegmentSystem V] := UniformSpace.Completion (Test V)




-- @@ L493-493 verbatim
abbrev FullDual (V : Type*) [SegmentSystem V] := StrongDual ℝ (Primal V)



-- @@ L496-497 verbatim
def unitVector {V : Type*} [SegmentSystem V] (v : V) : Primal V :=
  (Test.ofFinsupp (Finsupp.single v 1) : Test V)



-- @@ L500-501 verbatim
def coordinate {V : Type*} [SegmentSystem V] (v : V) : FullDual V :=
  (Test.evaluation v).extend UniformSpace.Completion.toComplL



-- @@ L504-505 verbatim
def coordinateSpan (V : Type*) [SegmentSystem V] : Submodule ℝ (FullDual V) :=
  (Submodule.span ℝ (Set.range (coordinate (V := V)))).topologicalClosure



-- @@ L508-508 verbatim
abbrev CoordinatePredual (V : Type*) [SegmentSystem V] : Type _ := ↥(coordinateSpan V)



-- @@ L511-512 verbatim
def head {V : Type*} [SegmentSystem V] (H : Finset V) (x : FullDual V) : FullDual V :=
  ∑ v ∈ H, x (unitVector v) • coordinate v




-- @@ L516-517 verbatim
def tail {V : Type*} [SegmentSystem V] (H : Finset V) (x : FullDual V) : FullDual V :=
  x - head H x


-- @@ L519-521 verbatim
theorem prefix_antisymm {a b : List ℕ}
    (hab : a.IsPrefix b) (hba : b.IsPrefix a) : a = b :=
  hab.eq_of_length (Nat.le_antisymm hab.length_le hba.length_le)


-- @@ L523-532 verbatim
instance infiniteSegments : SegmentSystem InfiniteVertex where
  isSegment := IsInterval List.IsPrefix
  singleton v := by
    refine ⟨v, v, List.prefix_rfl, ?_⟩
    intro w
    simp only [Finset.mem_singleton]
    constructor
    · rintro rfl; exact ⟨List.prefix_rfl, List.prefix_rfl⟩
    · rintro ⟨hvw, hwv⟩
      exact hwv.eq_of_length (Nat.le_antisymm hwv.length_le hvw.length_le)


-- @@ L534-535 verbatim
theorem forestAncestor_refl (v : ForestVertex) : ForestAncestor v v :=
  ⟨rfl, List.prefix_rfl⟩


-- @@ L537-540 verbatim
theorem forestAncestor_antisymm {a b : ForestVertex}
    (hab : ForestAncestor a b) (hba : ForestAncestor b a) : a = b := by
  apply Subtype.ext
  exact Prod.ext hab.1 (prefix_antisymm hab.2 hba.2)


-- @@ L542-551 verbatim
instance forestSegments : SegmentSystem ForestVertex where
  isSegment := IsInterval ForestAncestor
  singleton v := by
    refine ⟨v, v, ⟨rfl, List.prefix_rfl⟩, ?_⟩
    intro w
    simp only [Finset.mem_singleton]
    constructor
    · rintro rfl; exact ⟨⟨rfl, List.prefix_rfl⟩, ⟨rfl, List.prefix_rfl⟩⟩
    · rintro ⟨hvw, hwv⟩
      exact Subtype.ext (Prod.ext hwv.1 (hwv.2.eq_of_length (Nat.le_antisymm hwv.2.length_le hvw.2.length_le)))



-- @@ L554-554 verbatim
abbrev J := Primal ForestVertex


-- @@ L556-556 verbatim
abbrev X := FullDual ForestVertex


-- @@ L558-558 verbatim
abbrev JInfinite := Primal InfiniteVertex


-- @@ L560-560 verbatim
abbrev BInfinite := CoordinatePredual InfiniteVertex



-- @@ L563-563 verbatim
end SegmentLenses



-- @@ L566-566 verbatim
end


-- @@ L568-568 verbatim
end OAI
