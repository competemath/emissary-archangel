import OAI.Combinatorics.DiscreteConvexity.Model


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace TalagrandDiscreteConvexity


-- @@ L7-7 verbatim
open scoped BigOperators


-- @@ L9-9 verbatim
variable {α : Type*} [Fintype α] [DecidableEq α]


-- @@ L11-11 verbatim
noncomputable section


-- @@ L13-15 verbatim
theorem bernoulliMass_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (s : Finset α) : 0 ≤ bernoulliMass p s :=
  mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (sub_nonneg.mpr hp1) _)


-- @@ L17-19 verbatim
theorem familyMeasure_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (D : Family α) : 0 ≤ familyMeasure p D :=
  Finset.sum_nonneg (fun s _ => bernoulliMass_nonneg hp0 hp1 s)


-- @@ L21-22 verbatim
@[simp] theorem familyMeasure_empty (p : ℝ) :
    familyMeasure p (∅ : Family α) = 0 := by simp [familyMeasure]


-- @@ L24-27 verbatim
theorem familyMeasure_mono {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {D E : Family α} (h : D ⊆ E) : familyMeasure p D ≤ familyMeasure p E := by
  exact Finset.sum_le_sum_of_subset_of_nonneg h
    (fun s _ _ => bernoulliMass_nonneg hp0 hp1 s)


-- @@ L29-31 verbatim
omit [Fintype α] [DecidableEq α] in
@[simp] theorem cost_empty (p : ℝ) : cost p (∅ : Family α) = 0 := by
  simp [cost]


-- @@ L33-35 verbatim
omit [Fintype α] [DecidableEq α] in
@[simp] theorem cost_singleton (p : ℝ) (I : Finset α) :
    cost p {I} = p ^ I.card := by simp [cost]


-- @@ L37-39 verbatim
omit [Fintype α] [DecidableEq α] in
theorem cost_nonneg {p : ℝ} (hp : 0 ≤ p) (G : Family α) : 0 ≤ cost p G :=
  Finset.sum_nonneg (fun generator _ => pow_nonneg hp generator.card)


-- @@ L41-44 verbatim
omit [Fintype α] [DecidableEq α] in
theorem cost_mono {p : ℝ} (hp : 0 ≤ p) {G H : Family α} (h : G ⊆ H) :
    cost p G ≤ cost p H :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun generator _ _ => pow_nonneg hp generator.card)


-- @@ L46-53 verbatim
omit [Fintype α] in
theorem cost_union_le {p : ℝ} (hp : 0 ≤ p) (G H : Family α) :
    cost p (G ∪ H) ≤ cost p G + cost p H := by
  calc
    cost p (G ∪ H) ≤ cost p (G ∪ H) + cost p (G ∩ H) :=
      le_add_of_nonneg_right (cost_nonneg hp _)
    _ = cost p G + cost p H := by
      exact Finset.sum_union_inter


-- @@ L55-63 verbatim
omit [Fintype α] in
theorem cost_biUnion_le {ι : Type*} [DecidableEq ι] {p : ℝ} (hp : 0 ≤ p)
    (T : Finset ι) (G : ι → Family α) :
    cost p (T.biUnion G) ≤ ∑ i ∈ T, cost p (G i) := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert a T ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      exact (cost_union_le hp _ _).trans (add_le_add le_rfl ih)


-- @@ L65-69 verbatim
omit [Fintype α] in
theorem cost_image_le {ι : Type*} [DecidableEq ι] {p : ℝ} (hp : 0 ≤ p)
    (T : Finset ι) (G : ι → Finset α) :
    cost p (T.image G) ≤ ∑ i ∈ T, p ^ (G i).card := by
  exact Finset.sum_image_le_of_nonneg (fun I _ => pow_nonneg hp I.card)


-- @@ L71-73 verbatim
omit [Fintype α] [DecidableEq α] in
theorem covers_self (A : Family α) : Covers A A :=
  fun S hS => ⟨S, hS, Finset.Subset.refl S⟩


-- @@ L75-78 verbatim
omit [Fintype α] [DecidableEq α] in
@[simp] theorem covers_empty (G : Family α) : Covers G ∅ := by
  intro S hS
  exact False.elim (Finset.notMem_empty S hS)


-- @@ L80-82 verbatim
omit [Fintype α] [DecidableEq α] in
theorem Covers.mono_target {G A B : Family α} (h : Covers G A) (hBA : B ⊆ A) :
    Covers G B := fun S hS => h S (hBA hS)


-- @@ L84-89 verbatim
omit [Fintype α] [DecidableEq α] in
theorem Covers.mono_cover {G H A : Family α} (h : Covers G A) (hGH : G ⊆ H) :
    Covers H A := by
  intro S hS
  obtain ⟨I, hI, hIS⟩ := h S hS
  exact ⟨I, hGH hI, hIS⟩


-- @@ L91-99 verbatim
omit [Fintype α] in
theorem Covers.union {G H A B : Family α} (hGA : Covers G A) (hHB : Covers H B) :
    Covers (G ∪ H) (A ∪ B) := by
  intro S hS
  rcases Finset.mem_union.mp hS with hS | hS
  · obtain ⟨I, hI, hIS⟩ := hGA S hS
    exact ⟨I, Finset.mem_union_left H hI, hIS⟩
  · obtain ⟨I, hI, hIS⟩ := hHB S hS
    exact ⟨I, Finset.mem_union_right G hI, hIS⟩


-- @@ L101-104 verbatim
omit [Fintype α] [DecidableEq α] in
theorem small_empty (p : ℝ) : Small p (∅ : Family α) := by
  refine ⟨∅, covers_empty _, ?_⟩
  simp


-- @@ L106-109 verbatim
omit [Fintype α] in
@[simp] theorem mem_unionTuple {k : ℕ} {f : Fin k → Finset α} {a : α} :
    a ∈ unionTuple f ↔ ∃ j, a ∈ f j := by
  simp [unionTuple]


-- @@ L111-113 verbatim
omit [Fintype α] in
theorem subset_unionTuple {k : ℕ} (f : Fin k → Finset α) (j : Fin k) :
    f j ⊆ unionTuple f := fun _ ha => mem_unionTuple.mpr ⟨j, ha⟩


-- @@ L115-123 verbatim
omit [Fintype α] in
theorem unionTuple_subset_iff {k : ℕ} (f : Fin k → Finset α) (S : Finset α) :
    unionTuple f ⊆ S ↔ ∀ j, f j ⊆ S := by
  constructor
  · intro h j
    exact (subset_unionTuple f j).trans h
  · intro h a ha
    obtain ⟨j, hj⟩ := mem_unionTuple.mp ha
    exact h j hj


-- @@ L125-129 verbatim
@[simp] theorem mem_unionFamily {k : ℕ} {D : Family α} {S : Finset α} :
    S ∈ unionFamily k D ↔
      ∃ f : Fin k → Finset α, (∀ j, f j ∈ D) ∧ unionTuple f = S := by
  classical
  simp [unionFamily]


-- @@ L131-135 verbatim
@[simp] theorem mem_exceptional {k : ℕ} {D : Family α} {S : Finset α} :
    S ∈ exceptional k D ↔
      ∀ f : Fin k → Finset α, (∀ j, f j ∈ D) → ¬ S ⊆ unionTuple f := by
  classical
  simp [exceptional]


-- @@ L137-146 verbatim
theorem mem_exceptional_iff_unionFamily {k : ℕ} {D : Family α} {S : Finset α} :
    S ∈ exceptional k D ↔ ∀ T ∈ unionFamily k D, ¬ S ⊆ T := by
  constructor
  · intro h T hT
    obtain ⟨f, hf, rfl⟩ := mem_unionFamily.mp hT
    exact mem_exceptional.mp h f hf
  · intro h
    apply mem_exceptional.mpr
    intro f hf
    exact h (unionTuple f) (mem_unionFamily.mpr ⟨f, hf, rfl⟩)


-- @@ L148-152 verbatim
theorem exceptional_tuple_misses {k : ℕ} {D : Family α} {S : Finset α}
    (hS : S ∈ exceptional k D) (f : Fin k → Finset α) (hf : ∀ j, f j ∈ D) :
    ∃ a ∈ S, ∀ j, a ∉ f j := by
  obtain ⟨a, ha, hmiss⟩ := Finset.not_subset.mp (mem_exceptional.mp hS f hf)
  exact ⟨a, ha, fun j hj => hmiss (mem_unionTuple.mpr ⟨j, hj⟩)⟩


-- @@ L154-159 verbatim
theorem exceptional_antitone {k : ℕ} {D E : Family α} (hDE : D ⊆ E) :
    exceptional k E ⊆ exceptional k D := by
  intro S hS
  apply mem_exceptional.mpr
  intro f hf
  exact mem_exceptional.mp hS f (fun j => hDE (hf j))


-- @@ L161-166 verbatim
theorem exceptional_eq_empty_of_full_union {k : ℕ} {D : Family α}
    (f : Fin k → Finset α) (hf : ∀ j, f j ∈ D) (hfull : unionTuple f = Finset.univ) :
    exceptional k D = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro S hS
  exact mem_exceptional.mp hS f hf (hfull.symm ▸ Finset.subset_univ S)


-- @@ L168-170 verbatim
omit [DecidableEq α] in
@[simp] theorem mem_cubeSet {x : α → Bool} {a : α} :
    a ∈ cubeSet x ↔ x a = true := by simp [cubeSet]


-- @@ L172-175 verbatim
@[simp] theorem cubeSet_decide (S : Finset α) :
    cubeSet (fun a => decide (a ∈ S)) = S := by
  ext a
  simp


-- @@ L177-180 verbatim
theorem familyIndicator_nonneg (D : Family α) (x : α → Bool) :
    0 ≤ familyIndicator D x := by
  unfold familyIndicator
  split_ifs <;> simp


-- @@ L182-185 verbatim
theorem familyIndicator_le_one (D : Family α) (x : α → Bool) :
    familyIndicator D x ≤ 1 := by
  unfold familyIndicator
  split_ifs <;> simp


-- @@ L187-190 verbatim
theorem familyIndicator_sq (D : Family α) (x : α → Bool) :
    familyIndicator D x ^ 2 = familyIndicator D x := by
  unfold familyIndicator
  split_ifs <;> simp


-- @@ L192-192 verbatim
end

-- @@ L193-193 verbatim
end TalagrandDiscreteConvexity


-- @@ L195-195 verbatim
end OAI
