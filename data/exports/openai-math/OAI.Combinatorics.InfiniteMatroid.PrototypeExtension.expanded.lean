import OAI.Combinatorics.InfiniteMatroid.Prototype


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
section

-- @@ L6-6 verbatim
open Set Filter

-- @@ L7-7 verbatim
open scoped Topology symmDiff

-- @@ L8-8 verbatim
namespace InfiniteMatroidCounterexample


-- @@ L10-10 verbatim
def prototypePair (B : Set E0) : Set Prototype := {(B,false),(Bᶜ,true)}

-- @@ L11-13 verbatim
lemma mem_prototypePair {B : Set E0} {p : Prototype} :
    p ∈ prototypePair B ↔ p = (B,false) ∨ p = (Bᶜ,true) := by
  simp only [prototypePair,Set.mem_insert_iff,Set.mem_singleton_iff]

-- @@ L14-14 verbatim
lemma prototypePair_finite (B : Set E0) : (prototypePair B).Finite := (Set.finite_singleton _).insert _

-- @@ L15-18 verbatim
lemma symmDiff_inter_right (X Y : Set E0) : X ∆ (X ∩ Y) = X \ Y := by
  ext x
  simp only [Set.mem_symmDiff,Set.mem_inter_iff,Set.mem_sdiff]
  tauto


-- @@ L20-20 verbatim
namespace RankModel

-- @@ L21-21 verbatim
variable (R : RankModel D)


-- @@ L23-36 verbatim
lemma good_union {P Q : Set Prototype} (hP : R.GoodPrototypes P) (hQ : R.GoodPrototypes Q)
    (hPQ : ∀ p ∈ P, ∀ q ∈ Q, ¬ Small (p.1 \ q.1) ∧ ¬ Small (q.1 \ p.1)) :
    R.GoodPrototypes (P ∪ Q) := by
  constructor
  · intro p hp
    exact hp.elim (hP.admissible p) (hQ.admissible p)
  · intro p hp
    exact hp.elim (fun h ↦ Or.inl (hP.flip_closed p h)) (fun h ↦ Or.inr (hQ.flip_closed p h))
  · intro p hp q hq hne
    rcases hp with hp|hp <;> rcases hq with hq|hq
    · exact hP.separated p hp q hq hne
    · exact (hPQ p hp q hq).1
    · exact (hPQ q hq p hp).2
    · exact hQ.separated p hp q hq hne


-- @@ L38-38 verbatim
variable (hK : R.ideal = KIdeal)

-- @@ L39-39 verbatim
include hK

-- @@ L40-57 verbatim
lemma good_pair {B : Set E0} (hB : R.Admissible B) : R.GoodPrototypes (prototypePair B) := by
  constructor
  · intro p hp
    rcases mem_prototypePair.mp hp with rfl|rfl
    · exact hB
    · exact R.admissible_compl hB
  · intro p hp
    rcases mem_prototypePair.mp hp with rfl|rfl
    · exact mem_prototypePair.mpr (Or.inr rfl)
    · exact mem_prototypePair.mpr (Or.inl (by simp [flipPrototype]))
  · intro p hp q hq hne
    rcases mem_prototypePair.mp hp with rfl|rfl <;>
      rcases mem_prototypePair.mp hq with rfl|rfl
    · exact (hne rfl).elim
    · simpa only [Set.sdiff_compl,Set.inter_self] using R.admissible_positive hK hB
    · simpa only [Set.sdiff_eq_compl_inter,Set.inter_self] using
        R.admissible_positive hK (R.admissible_compl hB)
    · exact (hne rfl).elim


-- @@ L59-72 verbatim
lemma good_insert_pair {P : Set Prototype} (hP : R.GoodPrototypes P) {B : Set E0}
    (hB : R.Admissible B)
    (hsep : ∀ p ∈ P, ¬ Small (B \ p.1) ∧ ¬ Small (p.1 \ B)) :
    R.GoodPrototypes (P ∪ prototypePair B) := by
  apply R.good_union hP (R.good_pair hK hB)
  intro p hp q hq
  rcases mem_prototypePair.mp hq with rfl|rfl
  · exact ⟨(hsep p hp).2,(hsep p hp).1⟩
  · have hh := hsep (flipPrototype p) (hP.flip_closed p hp)
    have h1 : p.1 \ Bᶜ = B \ (flipPrototype p).1 := by
      ext x; simp only [flipPrototype,Set.mem_sdiff,Set.mem_compl_iff]; tauto
    have h2 : Bᶜ \ p.1 = (flipPrototype p).1 \ B := by
      ext x; simp only [flipPrototype,Set.mem_sdiff,Set.mem_compl_iff]; tauto
    exact ⟨by rw [h1]; exact hh.1,by rw [h2]; exact hh.2⟩


-- @@ L74-79 verbatim
lemma upper_difference_positive {I T : Set E0} (hI : R.Upper I) (hT : R.Admissible T) :
    ¬ Small (I \ T) := by
  intro hs
  have hi : KSmall0 (I ∆ (I ∩ T)) := by rw [symmDiff_inter_right]; exact small_kSmall0 hs
  have hup : R.Upper (I ∩ T) := ((R.status_invariant hK hi).1).mp hI
  exact ((R.admissible_iff T).mp hT).1 (R.upper_mono hup inter_subset_right)


-- @@ L81-86 verbatim
lemma lower_difference_positive {Y T : Set E0} (hY : R.Lower Y) (hT : R.Admissible T) :
    ¬ Small (T \ Y) := by
  intro hs
  have hi : KSmall0 (T ∆ (T ∩ Y)) := by rw [symmDiff_inter_right]; exact small_kSmall0 hs
  have ht : R.Admissible (T ∩ Y) := ((R.status_invariant hK hi).2.2).mp hT
  exact ((R.admissible_iff _).mp ht).2 (R.lower_mono hY inter_subset_right)


-- @@ L88-116 verbatim
/-- At an unmet interval the exact reservation construction adds one complementary pair. -/
lemma extend_unmet {P : Set Prototype} (hP : R.GoodPrototypes P)
    (hcard : Cardinal.mk P < Cardinal.continuum) {I Y : Set E0} (hIY : I ⊆ Y)
    (hnot : ¬ Meets (PrototypeBases P) I Y) :
    ∃ B, R.GoodPrototypes (P ∪ prototypePair B) ∧ Meets (PrototypeBases (P ∪ prototypePair B)) I Y := by
  have hsep := R.unmet_separation hK hP hIY hnot
  let T : P → Set E0 := fun p ↦ p.1.1
  have hfinish (B : Set E0) (hB : R.Admissible B)
      (hsepB : ∀ p : P, ¬ Small (B \ T p) ∧ ¬ Small (T p \ B))
      (hout : Outcome I Y B) :
      ∃ B, R.GoodPrototypes (P ∪ prototypePair B) ∧ Meets (PrototypeBases (P ∪ prototypePair B)) I Y := by
    refine ⟨B,R.good_insert_pair hK hP hB (fun p hp ↦ hsepB ⟨p,hp⟩),B,?_,hout⟩
    exact ⟨(B,false),Or.inr (mem_prototypePair.mpr (Or.inl rfl)),localRule_self false B⟩
  by_cases hI : R.Upper I
  · obtain ⟨B,_,hBI,hB,hsepB⟩ := R.insert_prototype hK hcard T (empty_subset I)
      R.not_upper_empty (R.upper_not_lower hI)
      (fun p ↦ by simpa using R.admissible_positive hK (hP.admissible p p.2))
      (fun p ↦ R.upper_difference_positive hK hI (hP.admissible p p.2))
    exact hfinish B hB hsepB (Or.inl hBI)
  by_cases hY : R.Lower Y
  · obtain ⟨B,hYB,_,hB,hsepB⟩ := R.insert_prototype hK hcard T (subset_univ Y)
      (fun h ↦ R.upper_not_lower h hY) R.not_lower_univ
      (fun p ↦ R.lower_difference_positive hK hY (hP.admissible p p.2))
      (fun p ↦ by simpa only [← Set.compl_eq_univ_sdiff] using
        R.admissible_positive hK (R.admissible_compl (hP.admissible p p.2)))
    exact hfinish B hB hsepB (Or.inr (Or.inr hYB))
  obtain ⟨B,hIB,hBY,hB,hsepB⟩ := R.insert_prototype hK hcard T hIY hI hY
    (fun p ↦ (hsep p p.2).1) (fun p ↦ (hsep p p.2).2)
  exact hfinish B hB hsepB (Or.inr (Or.inl ⟨hIB,hBY⟩))


-- @@ L118-118 verbatim
end RankModel

-- @@ L119-119 verbatim
end InfiniteMatroidCounterexample

-- @@ L120-120 verbatim
end


-- @@ L122-122 verbatim
end OAI
