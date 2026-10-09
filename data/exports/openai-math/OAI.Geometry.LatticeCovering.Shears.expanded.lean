import OAI.Geometry.LatticeCovering.Patterns


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
section

-- @@ L6-6 verbatim
section

-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open MeasureTheory MeasureTheory.Measure Set

-- @@ L9-9 verbatim
open scoped ENNReal Pointwise


-- @@ L11-11 verbatim
namespace SingleLatticeCovering.Shear.Pattern

-- @@ L12-12 verbatim
variable {α : Type*}

-- @@ L13-13 verbatim
local instance {q : ℕ} : DecidableEq ((Fin q → ℝ) × α) := Classical.decEq _



-- @@ L16-19 verbatim
def slice {q : ℕ} (s : Finset ((Fin (q+1) → ℝ) × α)) (v : ℝ) :
    Finset ((Fin q → ℝ) × α) := by
  classical
  exact (s.filter (fun l => l.1 (Fin.last q) = v)).image (fun l => (Fin.init l.1,l.2))


-- @@ L21-33 verbatim
lemma mem_slice {q : ℕ} (s : Finset ((Fin (q+1) → ℝ) × α)) (v : ℝ)
    (l : (Fin q → ℝ) × α) : l ∈ slice s v ↔ appendPoint v l ∈ s := by
  classical
  simp only [slice, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨a, ⟨ha,hav⟩,hal⟩
    have heq : appendPoint v l = a := by
      rw [← hal]
      simp only [appendPoint, ← hav, Fin.snoc_init_self]
    simpa only [heq] using ha
  · intro hl
    refine ⟨appendPoint v l, ⟨hl, by simp [appendPoint]⟩, ?_⟩
    simp only [appendPoint, Fin.init_snoc]


-- @@ L35-48 verbatim
lemma slice_image {q : ℕ} (s : Finset ((Fin q → ℝ) × α)) (a v : ℝ) :
    slice (s.image (appendPoint a)) v = if a=v then s else ∅ := by
  classical
  ext l
  rw [mem_slice]
  simp only [Finset.mem_image]
  by_cases hav : a=v
  · subst v
    simp only [↓reduceIte, (appendPoint_injective a).eq_iff, exists_eq_right]
  · simp only [hav, ↓reduceIte, Finset.notMem_empty, iff_false, not_exists, not_and]
    intro b hb heq
    have h := congrArg (fun x : (Fin (q+1) → ℝ) × α => x.1 (Fin.last q)) heq
    simp only [appendPoint, Fin.snoc_last] at h
    exact hav h


-- @@ L50-54 verbatim
lemma slice_union {q : ℕ} (s t : Finset ((Fin (q+1) → ℝ) × α)) (v : ℝ) :
    slice (s ∪ t) v = slice s v ∪ slice t v := by
  classical
  ext l
  simp only [mem_slice, Finset.mem_union]


-- @@ L56-58 verbatim
@[simp] lemma slice_mono {q : ℕ} (v : ℝ) (p : Pattern α q) :
    slice (Pattern.mono v p).points v = p.points := by
  simp [points, slice_image]


-- @@ L60-62 verbatim
@[simp] lemma slice_split_left {q : ℕ} (v : ℝ) (p r : Pattern α q) :
    slice (Pattern.split v p r).points v = p.points := by
  simp [points, slice_union, slice_image]


-- @@ L64-66 verbatim
@[simp] lemma slice_split_right {q : ℕ} (v : ℝ) (p r : Pattern α q) :
    slice (Pattern.split v p r).points (v+1) = r.points := by
  simp [points, slice_union, slice_image]


-- @@ L68-72 verbatim
lemma height_mono {q : ℕ} {v : ℝ} {p : Pattern α q}
    {l : (Fin (q+1) → ℝ) × α} (hl : l ∈ (Pattern.mono v p).points) :
    l.1 (Fin.last q) = v := by
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
  simp only [appendPoint, Fin.snoc_last]


-- @@ L74-79 verbatim
lemma height_split {q : ℕ} {v : ℝ} {p r : Pattern α q}
    {l : (Fin (q+1) → ℝ) × α} (hl : l ∈ (Pattern.split v p r).points) :
    l.1 (Fin.last q) = v ∨ l.1 (Fin.last q) = v+1 := by
  rcases Finset.mem_union.mp hl with hl | hl
  · exact Or.inl (height_mono (p := p) hl)
  · exact Or.inr (height_mono (p := r) hl)


-- @@ L81-85 verbatim
lemma mono_base_unique {q : ℕ} {v w : ℝ} {p r : Pattern α q}
    (h : (Pattern.mono v p).points = (Pattern.mono w r).points) : v=w := by
  obtain ⟨a,ha⟩ := p.points_nonempty
  have hm : appendPoint v a ∈ (Pattern.mono w r).points := by rw [← h]; exact Finset.mem_image.mpr ⟨a,ha,rfl⟩
  simpa only [appendPoint, Fin.snoc_last] using height_mono hm


-- @@ L87-99 verbatim
lemma mono_ne_split {q : ℕ} (v w : ℝ) (p r s : Pattern α q) :
    (Pattern.mono v p).points ≠ (Pattern.split w r s).points := by
  intro h
  obtain ⟨a,ha⟩ := r.points_nonempty
  obtain ⟨b,hb⟩ := s.points_nonempty
  have h1 : appendPoint w a ∈ (Pattern.mono v p).points := by
    rw [h, points]; exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,ha,rfl⟩)
  have h2 : appendPoint (w+1) b ∈ (Pattern.mono v p).points := by
    rw [h, points]; exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b,hb,rfl⟩)
  have h1' := height_mono h1
  have h2' := height_mono h2
  simp only [appendPoint, Fin.snoc_last] at h1' h2'
  linarith


-- @@ L101-114 verbatim
lemma split_base_unique {q : ℕ} {v w : ℝ} {p r s t : Pattern α q}
    (h : (Pattern.split v p r).points = (Pattern.split w s t).points) : v=w := by
  obtain ⟨a,ha⟩ := p.points_nonempty
  obtain ⟨b,hb⟩ := s.points_nonempty
  have h1 : appendPoint v a ∈ (Pattern.split w s t).points := by
    rw [← h, points]; exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,ha,rfl⟩)
  have h2 : appendPoint w b ∈ (Pattern.split v p r).points := by
    rw [h, points]; exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨b,hb,rfl⟩)
  have h1' := height_split h1
  have h2' := height_split h2
  simp only [appendPoint, Fin.snoc_last] at h1' h2'
  rcases h1' with h1' | h1'
  · exact h1'
  · rcases h2' with h2' | h2' <;> linarith




-- @@ L118-151 verbatim
lemma points_injective (q : ℕ) : Function.Injective (points (α := α) (q := q)) := by
  induction q with
  | zero =>
    intro p r h
    cases p with
    | leaf a =>
      cases r with
      | leaf b =>
        have : a=b := by simpa [points] using h
        subst b
        rfl
  | succ q ih =>
    intro p z h
    cases p with
    | mono v p =>
      cases z with
      | mono w r =>
        have hv := mono_base_unique h
        subst w
        have hp := congrArg (fun s => slice s v) h
        simp only [slice_mono] at hp
        rw [ih hp]
      | split w r s => exact (mono_ne_split _ _ _ _ _ h).elim
    | split v p r =>
      cases z with
      | mono w s => exact (mono_ne_split _ _ _ _ _ h.symm).elim
      | split w s t =>
        have hv := split_base_unique h
        subst w
        have hp := congrArg (fun s => slice s v) h
        have hr := congrArg (fun s => slice s (v+1)) h
        simp only [slice_split_left] at hp
        simp only [slice_split_right] at hr
        rw [ih hp, ih hr]


-- @@ L153-153 verbatim
end SingleLatticeCovering.Shear.Pattern


-- @@ L155-155 verbatim
namespace SingleLatticeCovering.Shear

-- @@ L156-156 verbatim
variable {α : Type*}

-- @@ L157-157 verbatim
local instance {q : ℕ} : DecidableEq ((Fin q → ℝ) × α) := Classical.decEq _




-- @@ L161-162 verbatim
def UniqueLabels {q : ℕ} (s : Finset ((Fin q → ℝ) × α)) : Prop :=
  ∀ l ∈ s, ∀ r ∈ s, l.1=r.1 → l.2=r.2





-- @@ L167-169 verbatim
def SuffixBinary {q : ℕ} (s : Finset ((Fin q → ℝ) × α)) : Prop :=
  ∀ j : Fin q, ∀ y : Fin q → ℝ, ∃ v : ℝ, ∀ l ∈ s,
    (∀ k : Fin q, j<k → l.1 k = y k) → l.1 j = v ∨ l.1 j = v+1


-- @@ L171-172 verbatim
def SourcePattern {q : ℕ} (s : Finset ((Fin q → ℝ) × α)) : Prop :=
  s.Nonempty ∧ UniqueLabels s ∧ SuffixBinary s


-- @@ L174-174 verbatim
namespace Pattern

-- @@ L175-179 verbatim
lemma UniqueLabels_slice {q : ℕ} {s : Finset ((Fin (q+1) → ℝ) × α)}
    (hs : UniqueLabels s) (v : ℝ) : UniqueLabels (slice s v) := by
  intro l hl r hr h
  have heq : (appendPoint v l).1 = (appendPoint v r).1 := congrArg (fun x : Fin q → ℝ => Fin.snoc (α := fun _ => ℝ) x v) h
  exact hs _ ((mem_slice _ _ _).mp hl) _ ((mem_slice _ _ _).mp hr) heq


-- @@ L181-196 verbatim
lemma SuffixBinary_slice {q : ℕ} {s : Finset ((Fin (q+1) → ℝ) × α)}
    (hs : SuffixBinary s) (v : ℝ) : SuffixBinary (slice s v) := by
  intro j y
  obtain ⟨a,ha⟩ := hs j.castSucc (Fin.snoc (α := fun _ => ℝ) y v)
  refine ⟨a, ?_⟩
  intro l hl hy
  have htail : ∀ k : Fin (q+1), j.castSucc < k →
      (appendPoint v l).1 k = (Fin.snoc (α := fun _ => ℝ) y v) k := by
    intro k
    refine Fin.lastCases ?_ (fun k => ?_) k
    · intro hk
      simp only [appendPoint, Fin.snoc_last]
    · intro hk
      simp only [appendPoint, Fin.snoc_castSucc]
      exact hy k (by simpa using hk)
  simpa only [appendPoint, Fin.snoc_castSucc] using ha _ ((mem_slice _ _ _).mp hl) htail


-- @@ L198-204 verbatim
lemma suffix_last_bound {q : ℕ} {s : Finset ((Fin (q+1) → ℝ) × α)}
    (hs : SuffixBinary s) : ∃ v : ℝ, ∀ l ∈ s,
      l.1 (Fin.last q) = v ∨ l.1 (Fin.last q) = v+1 := by
  obtain ⟨v,hv⟩ := hs (Fin.last q) 0
  refine ⟨v, fun l hl => hv l hl ?_⟩
  intro k hk
  exact False.elim ((not_lt_of_ge (Fin.le_last k)) hk)


-- @@ L206-226 verbatim
lemma slice_partition {q : ℕ} {s : Finset ((Fin (q+1) → ℝ) × α)} (v : ℝ)
    (hv : ∀ l ∈ s, l.1 (Fin.last q) = v ∨ l.1 (Fin.last q) = v+1) :
    s = (slice s v).image (appendPoint v) ∪ (slice s (v+1)).image (appendPoint (v+1)) := by
  classical
  have hin (l : (Fin (q+1) → ℝ) × α) (a : ℝ) (hl : l ∈ s) (ha : l.1 (Fin.last q)=a) :
      l ∈ (slice s a).image (appendPoint a) := by
    have heq : appendPoint a (Fin.init l.1, l.2) = l := by
      simp only [appendPoint, ← ha, Fin.snoc_init_self]
    exact Finset.mem_image.mpr ⟨(Fin.init l.1,l.2), (mem_slice _ _ _).mpr (heq.symm ▸ hl), heq⟩
  ext l
  constructor
  · intro hl
    rcases hv l hl with h | h
    · exact Finset.mem_union_left _ (hin l v hl h)
    · exact Finset.mem_union_right _ (hin l (v+1) hl h)
  · intro hl
    rcases Finset.mem_union.mp hl with hl | hl
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
      exact (mem_slice _ _ _).mp ha
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
      exact (mem_slice _ _ _).mp ha



-- @@ L229-266 verbatim
lemma exists_tree {q : ℕ} (s : Finset ((Fin q → ℝ) × α)) (hs : SourcePattern s) :
    ∃ p : Pattern α q, p.points=s := by
  classical
  induction q with
  | zero =>
    obtain ⟨a,ha⟩ := hs.1
    refine ⟨.leaf a.2, ?_⟩
    have hcoord (l : (Fin 0 → ℝ) × α) : l.1=0 := by ext i; exact Fin.elim0 i
    ext l
    simp only [points, Finset.mem_singleton]
    constructor
    · rintro rfl
      convert ha using 1
      exact Prod.ext (hcoord a).symm rfl
    · intro hl
      exact Prod.ext (hcoord l) (hs.2.1 l hl a ha ((hcoord l).trans (hcoord a).symm))
  | succ q ih =>
    obtain ⟨v,hv⟩ := suffix_last_bound hs.2.2
    have hpart := slice_partition v hv
    have h0 := UniqueLabels_slice hs.2.1 v
    have h1 := UniqueLabels_slice hs.2.1 (v+1)
    have hb0 := SuffixBinary_slice hs.2.2 v
    have hb1 := SuffixBinary_slice hs.2.2 (v+1)
    by_cases hn0 : (slice s v).Nonempty
    · obtain ⟨p,hp⟩ := ih _ ⟨hn0,h0,hb0⟩
      by_cases hn1 : (slice s (v+1)).Nonempty
      · obtain ⟨r,hr⟩ := ih _ ⟨hn1,h1,hb1⟩
        exact ⟨.split v p r, by rw [points, hp, hr, ← hpart]⟩
      · have he := Finset.not_nonempty_iff_eq_empty.mp hn1
        exact ⟨.mono v p, by simpa only [points, hp, he, Finset.image_empty, Finset.union_empty] using hpart.symm⟩
    · have he := Finset.not_nonempty_iff_eq_empty.mp hn0
      have hn1 : (slice s (v+1)).Nonempty := by
        by_contra hn1
        have he1 := Finset.not_nonempty_iff_eq_empty.mp hn1
        simp only [he, he1, Finset.image_empty, Finset.union_self] at hpart
        exact hs.1.ne_empty hpart
      obtain ⟨r,hr⟩ := ih _ ⟨hn1,h1,hb1⟩
      exact ⟨.mono (v+1) r, by simpa only [points, hr, he, Finset.image_empty, Finset.empty_union] using hpart.symm⟩


-- @@ L268-268 verbatim
end Pattern

-- @@ L269-269 verbatim
end SingleLatticeCovering.Shear


-- @@ L271-271 verbatim
namespace SingleLatticeCovering.Shear

-- @@ L272-272 verbatim
open Pattern

-- @@ L273-273 verbatim
variable {α : Type*}



-- @@ L276-278 verbatim
noncomputable def encodeFamily (S : (q : ℕ) → Finset (Finset ((Fin q → ℝ) × α)))
    (q : ℕ) : Finset (Pattern α q) :=
  (S q).preimage Pattern.points (Pattern.points_injective q).injOn


-- @@ L280-282 verbatim
@[simp] lemma mem_encodeFamily (S : (q : ℕ) → Finset (Finset ((Fin q → ℝ) × α)))
    (q : ℕ) (p : Pattern α q) : p ∈ encodeFamily S q ↔ p.points ∈ S q :=
  Finset.mem_preimage


-- @@ L284-288 verbatim
lemma encodeFamily_card_le (S : (q : ℕ) → Finset (Finset ((Fin q → ℝ) × α))) (q : ℕ) :
    (encodeFamily S q).card ≤ (S q).card := by
  classical
  rw [encodeFamily, Finset.card_preimage]
  exact Finset.card_filter_le _ _



-- @@ L291-292 verbatim
def SourceSliceClosed (S : (q : ℕ) → Finset (Finset ((Fin q → ℝ) × α))) (D : ℕ) : Prop :=
  ∀ q < D, ∀ s ∈ S (q+1), ∀ v : ℝ, (slice s v).Nonempty → slice s v ∈ S q


-- @@ L294-308 verbatim
lemma encodeFamily_sliceClosed (S : (q : ℕ) → Finset (Finset ((Fin q → ℝ) × α)))
    (D : ℕ) (hS : SourceSliceClosed S D) : SliceClosed (encodeFamily S) D := by
  intro q hq p hp
  have hp' := (mem_encodeFamily S (q+1) p).mp hp
  cases p with
  | mono v p =>
    have hm : p.points ∈ S q := by
      simpa only [slice_mono] using hS q hq _ hp' v (by simpa only [slice_mono] using p.points_nonempty)
    exact ⟨(mem_encodeFamily _ _ _).mpr hm, (mem_encodeFamily _ _ _).mpr hm⟩
  | split v p r =>
    have hm : p.points ∈ S q := by
      simpa only [slice_split_left] using hS q hq _ hp' v (by simpa only [slice_split_left] using p.points_nonempty)
    have hn : r.points ∈ S q := by
      simpa only [slice_split_right] using hS q hq _ hp' (v+1) (by simpa only [slice_split_right] using r.points_nonempty)
    exact ⟨(mem_encodeFamily _ _ _).mpr hm, (mem_encodeFamily _ _ _).mpr hn⟩


-- @@ L310-310 verbatim
section Endpoint

-- @@ L311-318 verbatim
variable {E T : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup T]
  [MeasurableSpace T] [MeasurableAdd₂ T] [MeasurableNeg T]
  (μ : Measure T) [IsProbabilityMeasure μ] [IsAddLeftInvariant μ] [IsNegInvariant μ]
  (π : E →+ T) (hπ : Function.Surjective π)
  (U : α → Set T) (hU : ∀ a, MeasurableSet (U a))
  (η : α → ℝ≥0∞) (hη0 : ∀ a, η a ≠ 0) (hηt : ∀ a, η a ≠ ∞)
  (hUη : ∀ a, μ (U a) ≤ η a)
  (L : ℝ≥0∞) (hL0 : L ≠ 0) (hLt : L ≠ ∞)


-- @@ L320-320 verbatim
include hπ hU hη0 hηt hUη hL0 hLt




-- @@ L324-343 verbatim
theorem source_simultaneous_shear (D : ℕ)
    (S : (q : ℕ) → Finset (Finset ((Fin q → ℝ) × α)))
    (hsource : ∀ q ≤ D, ∀ s ∈ S q, SourcePattern s)
    (hslice : SourceSliceClosed S D)
    (hQ : (∑ q ∈ Finset.range (D+1), ((S q).card : ℝ≥0∞)) < L) :
    ∃ Z : Fin D → E, ∀ q (hq : q ≤ D) (s : Finset ((Fin q → ℝ) × α)), s ∈ S q →
      μ (⋂ l ∈ s, translate (U l.2) (π (linearShift (restrictColumns hq Z) l.1))) ≤
        L^(s.card-1) * ∏ l ∈ s, η l.2 := by
  classical
  have hbudget : (∑ q ∈ Finset.range (D+1), ((encodeFamily S q).card : ℝ≥0∞)) < L :=
    (Finset.sum_le_sum (fun q _ => Nat.cast_le.mpr (encodeFamily_card_le S q))).trans_lt hQ
  obtain ⟨Z,hZ⟩ := simultaneous_shear μ π hπ U hU η hη0 hηt hUη L hL0 hLt D
    (encodeFamily S) (encodeFamily_sliceClosed S D hslice) hbudget
  refine ⟨Z, ?_⟩
  intro q hq s hs
  obtain ⟨p,hp⟩ := exists_tree s (hsource q hq s hs)
  have hm : p ∈ encodeFamily S q := (mem_encodeFamily _ _ _).mpr (hp.symm ▸ hs)
  have h := hZ q hq p hm
  rw [failure_eq_intersection, ← points_card, labelProduct_eq_prod, hp] at h
  exact h


-- @@ L345-345 verbatim
end Endpoint

-- @@ L346-346 verbatim
end SingleLatticeCovering.Shear




-- @@ L350-350 verbatim
namespace SingleLatticeCovering.Shear

-- @@ L351-351 verbatim
open scoped BigOperators


-- @@ L353-357 verbatim
lemma source_card_le_two_pow {α : Type*} {q : ℕ}
    {s : Finset ((Fin q → ℝ) × α)} (hs : SourcePattern s) : s.card ≤ 2^q := by
  obtain ⟨p,hp⟩ := Pattern.exists_tree s hs
  rw [←hp,Pattern.points_card]
  exact p.size_le_two_pow




-- @@ L361-402 verbatim
lemma small_subsets_card {α : Type*} (s : Finset α) (k : ℕ) :
    (s.powerset.filter (fun t => t.card ≤ k)).card ≤ (s.card+1)^k := by
  classical
  induction k with
  | zero =>
    have hsub : s.powerset.filter (fun t => t.card ≤ 0) ⊆ {∅} := by
      intro t ht
      have ht0 := (Finset.mem_filter.mp ht).2
      simp only [Nat.le_zero, Finset.card_eq_zero] at ht0
      simpa using ht0
    simpa using Finset.card_le_card hsub
  | succ k ih =>
    let F := s.powerset.filter (fun t => t.card ≤ k)
    have hsub : s.powerset.filter (fun t => t.card ≤ k+1) ⊆
        F ∪ s.biUnion (fun a => F.image (insert a)) := by
      intro t ht
      obtain ⟨hts,htk⟩ := Finset.mem_filter.mp ht
      have hts' := Finset.mem_powerset.mp hts
      by_cases hem : t=∅
      · subst t
        apply Finset.mem_union_left
        simp [F]
      · obtain ⟨a,ha⟩ := Finset.nonempty_iff_ne_empty.mpr hem
        have hE : t.erase a ∈ F := by
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_powerset.mpr ((Finset.erase_subset a t).trans hts'),?_⟩
          have hcard := Finset.card_erase_add_one ha
          omega
        apply Finset.mem_union_right
        exact Finset.mem_biUnion.mpr ⟨a,hts' ha,Finset.mem_image.mpr
          ⟨t.erase a,hE,Finset.insert_erase ha⟩⟩
    calc
      _ ≤ (F ∪ s.biUnion (fun a => F.image (insert a))).card := Finset.card_le_card hsub
      _ ≤ F.card+(s.biUnion (fun a => F.image (insert a))).card := Finset.card_union_le _ _
      _ ≤ F.card+∑ a ∈ s, (F.image (insert a)).card :=
        Nat.add_le_add_left (Finset.card_biUnion_le) _
      _ ≤ F.card+s.card*F.card := by
        apply Nat.add_le_add_left
        simpa using Finset.sum_le_sum (fun a (ha : a ∈ s) => Finset.card_image_le (s := F) (f := insert a))
      _ = (s.card+1)*F.card := by ring
      _ ≤ (s.card+1)*(s.card+1)^k := Nat.mul_le_mul_left _ ih
      _ = _ := by ring


-- @@ L404-406 verbatim
noncomputable def alphabetPoints {α : Type*} (A : ℕ → Finset ℝ) (labels : Finset α) (q : ℕ) :
    Finset ((Fin q → ℝ) × α) :=
  (Fintype.piFinset (fun j : Fin q => A j.val)).product labels


-- @@ L408-411 verbatim
lemma mem_alphabetPoints {α : Type*} (A : ℕ → Finset ℝ) (labels : Finset α) (q : ℕ)
    (l : (Fin q → ℝ) × α) :
    l ∈ alphabetPoints A labels q ↔ (∀ j, l.1 j ∈ A j.val) ∧ l.2 ∈ labels := by
  simp [alphabetPoints,Fintype.mem_piFinset]


-- @@ L413-416 verbatim
noncomputable def allPatterns {α : Type*} (A : ℕ → Finset ℝ) (labels : Finset α) (q : ℕ) :
    Finset (Finset ((Fin q → ℝ) × α)) := by
  classical
  exact (alphabetPoints A labels q).powerset.filter SourcePattern


-- @@ L418-422 verbatim
lemma mem_allPatterns {α : Type*} (A : ℕ → Finset ℝ) (labels : Finset α) (q : ℕ)
    (s : Finset ((Fin q → ℝ) × α)) : s ∈ allPatterns A labels q ↔
      s ⊆ alphabetPoints A labels q ∧ SourcePattern s := by
  classical
  simp [allPatterns]


-- @@ L424-436 verbatim
lemma allPatterns_sliceClosed {α : Type*} (A : ℕ → Finset ℝ) (labels : Finset α) (D : ℕ) :
    SourceSliceClosed (allPatterns A labels) D := by
  intro q hq s hs v hv
  obtain ⟨hsub,hsource⟩ := (mem_allPatterns A labels (q+1) s).mp hs
  apply (mem_allPatterns A labels q _).mpr
  refine ⟨?_,hv,Pattern.UniqueLabels_slice hsource.2.1 v,
    Pattern.SuffixBinary_slice hsource.2.2 v⟩
  intro l hl
  have hl' := hsub ((Pattern.mem_slice s v l).mp hl)
  obtain ⟨ha,hlabel⟩ := (mem_alphabetPoints A labels (q+1) _).mp hl'
  apply (mem_alphabetPoints A labels q l).mpr
  refine ⟨fun j => ?_,hlabel⟩
  simpa only [Pattern.appendPoint,Fin.snoc_castSucc,Fin.val_castSucc] using ha j.castSucc


-- @@ L438-445 verbatim
lemma allPatterns_card_bound {α : Type*} (A : ℕ → Finset ℝ) (labels : Finset α) (q : ℕ) :
    (allPatterns A labels q).card ≤ ((alphabetPoints A labels q).card+1)^(2^q) := by
  classical
  apply le_trans _ (small_subsets_card (alphabetPoints A labels q) (2^q))
  apply Finset.card_le_card
  intro s hs
  obtain ⟨hsub,hsource⟩ := (mem_allPatterns A labels q s).mp hs
  exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub,source_card_le_two_pow hsource⟩


-- @@ L447-457 verbatim
lemma allPatterns_total_bound {α : Type*} (A : ℕ → Finset ℝ) (labels : Finset α)
    (D N : ℕ) (hN : ∀ q ≤ D, (alphabetPoints A labels q).card ≤ N) :
    (∑ q ∈ Finset.range (D+1), (allPatterns A labels q).card) ≤ (D+1)*(N+1)^(2^D) := by
  have hf (q : ℕ) (hq : q ∈ Finset.range (D+1)) :
      (allPatterns A labels q).card ≤ (N+1)^(2^D) := by
    have hq' : q ≤ D := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hq
    calc
      _ ≤ ((alphabetPoints A labels q).card+1)^(2^q) := allPatterns_card_bound A labels q
      _ ≤ (N+1)^(2^q) := Nat.pow_le_pow_left (Nat.add_le_add_right (hN q hq') 1) _
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega) hq')
  simpa using Finset.sum_le_sum hf



-- @@ L460-460 verbatim
end SingleLatticeCovering.Shear


-- @@ L462-462 verbatim
end

-- @@ L463-463 verbatim
end


-- @@ L465-465 verbatim
section




-- @@ L469-469 verbatim
noncomputable section

-- @@ L470-470 verbatim
open MeasureTheory MeasureTheory.Measure Set Module

-- @@ L471-471 verbatim
open scoped Pointwise ENNReal


-- @@ L473-473 verbatim
namespace SingleLatticeCovering.Completion


-- @@ L475-475 verbatim
section Haar

-- @@ L476-478 verbatim
variable {T : Type*} [AddCommGroup T] [TopologicalSpace T] [IsTopologicalAddGroup T]
  [MeasurableSpace T] [BorelSpace T] [CompactSpace T]
  (μ : Measure T) [IsAddHaarMeasure μ] [IsProbabilityMeasure μ]




-- @@ L482-499 verbatim
lemma add_eq_univ_of_measure_sum {A B : Set T} (hB : MeasurableSet B)
    (h : 1 < μ.real A + μ.real B) : A+B = univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_contra hx
  let C := (fun t : T => x-t) ⁻¹' B
  have hC : MeasurableSet C := hB.preimage (by fun_prop)
  have hm : μ C = μ B := (measurePreserving_sub_left μ x).measure_preimage hB.nullMeasurableSet
  have hd : Disjoint A C := by
    apply Set.disjoint_left.mpr
    intro a ha hc
    apply hx
    exact ⟨a, ha, x-a, hc, by abel_nf⟩
  have hu := measureReal_le_one (μ := μ) (s := A ∪ C)
  rw [measureReal_union hd hC] at hu
  have hmreal : μ.real C = μ.real B := congrArg ENNReal.toReal hm
  rw [hmreal] at hu
  exact (not_le_of_gt h) hu



-- @@ L502-512 verbatim
lemma preimage_image_eq_kernel_union {T : Type*} [AddCommGroup T] [TopologicalSpace T] [IsTopologicalAddGroup T] [MeasurableSpace T] [BorelSpace T] [CompactSpace T] (f : T →+ T) (A : Set T) :
    f ⁻¹' (f '' A) = ⋃ z : f.ker, (fun x : T => x-z) ⁻¹' A := by
  ext x
  simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
  constructor
  · rintro ⟨a, ha, hax⟩
    have hz : x-a ∈ f.ker := by simp only [AddMonoidHom.mem_ker, map_sub, hax, sub_self]
    exact ⟨⟨x-a, hz⟩, by simpa using ha⟩
  · rintro ⟨z, hz⟩
    refine ⟨x-z, hz, ?_⟩
    simpa only [map_sub, sub_eq_self] using (show f z = 0 from z.property)



-- @@ L515-522 verbatim
lemma measure_image_le_kernel {T : Type*} [AddCommGroup T] [TopologicalSpace T] [IsTopologicalAddGroup T] [MeasurableSpace T] [BorelSpace T] [CompactSpace T] (μ : Measure T) [IsAddHaarMeasure μ] [IsProbabilityMeasure μ] (f : T →+ T) [Fintype f.ker]
    (hf : MeasurePreserving f μ μ) {A : Set T} (hA : MeasurableSet (f '' A)) :
    μ (f '' A) ≤ (Fintype.card f.ker : ℝ≥0∞)*μ A := by
  rw [← hf.measure_preimage hA.nullMeasurableSet, preimage_image_eq_kernel_union]
  calc
    _ ≤ ∑ z : f.ker, μ ((fun x : T => x-z) ⁻¹' A) := measure_iUnion_fintype_le μ _
    _ = _ := by simp only [sub_eq_add_neg, measure_preimage_add_right, Finset.sum_const,
      nsmul_eq_mul, Finset.card_univ]


-- @@ L524-529 verbatim
lemma measureReal_image_le_kernel (f : T →+ T) [Fintype f.ker]
    (hf : MeasurePreserving f μ μ) {A : Set T} (hA : MeasurableSet (f '' A)) :
    μ.real (f '' A) ≤ (Fintype.card f.ker : ℝ)*μ.real A := by
  have h := ENNReal.toReal_mono (by finiteness :
      (Fintype.card f.ker : ℝ≥0∞)*μ A ≠ ∞) (measure_image_le_kernel μ f hf hA)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, measureReal_def] using h


-- @@ L531-531 verbatim
end Haar


-- @@ L533-533 verbatim
abbrev Torus (n : ℕ) := Fin n → AddCircle (1 : ℝ)


-- @@ L535-535 verbatim
def torusMeasure (n : ℕ) : Measure (Torus n) := addHaarMeasure ⊤


-- @@ L537-538 verbatim
instance torusMeasure_haar (n : ℕ) : IsAddHaarMeasure (torusMeasure n) :=
  inferInstanceAs (IsAddHaarMeasure (addHaarMeasure ⊤))


-- @@ L540-541 verbatim
instance torusMeasure_probability (n : ℕ) : IsProbabilityMeasure (torusMeasure n) :=
  ⟨addHaarMeasure_self⟩


-- @@ L543-546 verbatim
lemma real_nsmul_regular (k : ℕ) (hk : k ≠ 0) : IsSMulRegular ℝ k := by
  intro x y h
  have heq : (k : ℝ)*x = (k : ℝ)*y := by simpa only [nsmul_eq_mul] using h
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr hk) heq


-- @@ L548-555 verbatim
lemma circle_torsion_card (k : ℕ) (hk : k ≠ 0) :
    Nat.card {x : AddCircle (1 : ℝ) // k • x = 0} ≤ k := by
  have hfin := AddCircle.finite_torsion_of_isSMulRegular (1 : ℝ) k (real_nsmul_regular k hk)
  let : Finite {x : AddCircle (1 : ℝ) // k • x = 0} := hfin.to_subtype
  have h := AddCircle.card_torsion_le_of_isSMulRegular (1 : ℝ) k hk (real_nsmul_regular k hk)
  change ENat.card {x : AddCircle (1 : ℝ) // k • x = 0} ≤ (k : ℕ∞) at h
  rw [ENat.card_eq_coe_natCard] at h
  exact_mod_cast h


-- @@ L557-573 verbatim
lemma torus_torsion_card (n k : ℕ) (hk : k ≠ 0) :
    Finite {x : Torus n // k • x = 0} ∧
      Nat.card {x : Torus n // k • x = 0} ≤ k^n := by
  have hfin := AddCircle.finite_torsion_of_isSMulRegular (1 : ℝ) k (real_nsmul_regular k hk)
  let : Finite {x : AddCircle (1 : ℝ) // k • x = 0} := hfin.to_subtype
  let f : {x : Torus n // k • x = 0} → (Fin n → {x : AddCircle (1 : ℝ) // k • x = 0}) :=
    fun x i => ⟨x.1 i, congr_fun x.property i⟩
  have hinj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congr_fun h i)
  let : Finite {x : Torus n // k • x = 0} := Finite.of_injective f hinj
  refine ⟨inferInstance, ?_⟩
  have hcard := Nat.card_le_card_of_injective f hinj
  have hp := Nat.pow_le_pow_left (circle_torsion_card k hk) n
  exact hcard.trans (by simpa only [Nat.card_fun, Nat.card_fin] using hp)



-- @@ L576-598 verbatim
lemma torus_measure_image_nsmul (n k : ℕ) (hk : k ≠ 0)
    {A : Set (Torus n)} (hA : IsCompact A) :
    (torusMeasure n).real ((fun x : Torus n => k • x) '' A) ≤
      (k : ℝ)^n * (torusMeasure n).real A := by
  let f : Torus n →+ Torus n := nsmulAddMonoidHom k
  have hfin := (torus_torsion_card n k hk).1
  let : Finite f.ker := hfin
  let : Fintype f.ker := Fintype.ofFinite _
  have hf : MeasurePreserving f (torusMeasure n) (torusMeasure n) := by
    change MeasurePreserving (fun x : Torus n => k • x) (torusMeasure n) (torusMeasure n)
    simpa only [natCast_zsmul] using
      (measurePreserving_zsmul (torusMeasure n) (Int.natCast_ne_zero.mpr hk))
  have hcont : Continuous f := by
    change Continuous (fun x : Torus n => k • x)
    fun_prop
  have hmeas : MeasurableSet (f '' A) := (hA.image hcont).measurableSet
  have h := measureReal_image_le_kernel (torusMeasure n) f hf hmeas
  have hc : (Fintype.card f.ker : ℝ) ≤ (k : ℝ)^n := by
    have : Fintype.card f.ker ≤ k^n := by
      rw [← Nat.card_eq_fintype_card]
      exact (torus_torsion_card n k hk).2
    exact_mod_cast this
  exact h.trans (mul_le_mul_of_nonneg_right hc ENNReal.toReal_nonneg)


-- @@ L600-600 verbatim
abbrev RealSpace (n : ℕ) := Fin n → ℝ


-- @@ L602-604 verbatim
def latticeBasis {n : ℕ} (L : Submodule ℤ (RealSpace n))
    [DiscreteTopology L] [IsZLattice ℝ L] : Basis (Fin n) ℝ (RealSpace n) :=
  (IsZLattice.basis L).ofZLatticeBasis ℝ




-- @@ L608-617 verbatim
def latticeProjection {n : ℕ} (L : Submodule ℤ (RealSpace n))
    [DiscreteTopology L] [IsZLattice ℝ L] : RealSpace n →ₜ+ Torus n where
  toFun x i := ((latticeBasis L).equivFun x i : AddCircle (1 : ℝ))
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp
  continuous_toFun := by
    apply continuous_pi
    intro i
    exact (AddCircle.continuous_mk' (1 : ℝ)).comp
      ((continuous_apply i).comp (latticeBasis L).equivFun.toContinuousLinearEquiv.continuous)


-- @@ L619-630 verbatim
lemma latticeProjection_surjective {n : ℕ} (L : Submodule ℤ (RealSpace n))
    [DiscreteTopology L] [IsZLattice ℝ L] : Function.Surjective (latticeProjection L) := by
  intro y
  have hy : ∀ i, ∃ x : ℝ, (x : AddCircle (1 : ℝ)) = y i :=
    fun i => QuotientAddGroup.mk'_surjective _ (y i)
  choose x hx using hy
  refine ⟨(latticeBasis L).equivFun.symm x, ?_⟩
  ext i
  change (((latticeBasis L).equivFun ((latticeBasis L).equivFun.symm x)) i :
    AddCircle (1 : ℝ)) = y i
  rw [LinearEquiv.apply_symm_apply]
  exact hx i


-- @@ L632-652 verbatim
lemma latticeProjection_eq_zero_iff {n : ℕ} (L : Submodule ℤ (RealSpace n))
    [DiscreteTopology L] [IsZLattice ℝ L] (x : RealSpace n) :
    latticeProjection L x = 0 ↔ x ∈ L := by
  have hspan : Submodule.span ℤ (Set.range (latticeBasis L)) = L :=
    (IsZLattice.basis L).ofZLatticeBasis_span ℝ
  have hcoords : x ∈ L ↔ ∀ i, (latticeBasis L).repr x i ∈ Set.range (algebraMap ℤ ℝ) := by
    conv_lhs => rw [← hspan]
    exact (latticeBasis L).mem_span_iff_repr_mem ℤ x
  rw [hcoords]
  constructor
  · intro h i
    have hi := congr_fun h i
    change (((latticeBasis L).repr x i : ℝ) : AddCircle (1 : ℝ)) = 0 at hi
    obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hi
    exact ⟨z, by simpa using hz⟩
  · intro h
    ext i
    change (((latticeBasis L).repr x i : ℝ) : AddCircle (1 : ℝ)) = 0
    apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
    obtain ⟨z, hz⟩ := h i
    exact ⟨z, by simpa using hz⟩


-- @@ L654-673 verbatim
lemma latticeProjection_image_eq_univ_iff {n : ℕ} (L : Submodule ℤ (RealSpace n))
    [DiscreteTopology L] [IsZLattice ℝ L] (K : Set (RealSpace n)) :
    latticeProjection L '' K = univ ↔ K+(L : Set (RealSpace n)) = univ := by
  constructor
  · intro h
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨a, ha, hax⟩ : ∃ a ∈ K, latticeProjection L a = latticeProjection L x := by
      have : latticeProjection L x ∈ latticeProjection L '' K := by rw [h]; trivial
      exact this
    have hz : x-a ∈ L := (latticeProjection_eq_zero_iff L _).mp (by simp [map_sub, hax])
    exact ⟨a, ha, x-a, hz, by abel_nf⟩
  · intro h
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨x, rfl⟩ := latticeProjection_surjective L y
    have hx : x ∈ K+(L : Set (RealSpace n)) := by rw [h]; trivial
    obtain ⟨a, ha, z, hz, rfl⟩ := hx
    refine ⟨a, ha, ?_⟩
    simp [map_add, (latticeProjection_eq_zero_iff L z).mpr hz]




-- @@ L677-679 verbatim
def holeProportion {n : ℕ} (L : Submodule ℤ (RealSpace n))
    [DiscreteTopology L] [IsZLattice ℝ L] (K : Set (RealSpace n)) : ℝ :=
  1-(torusMeasure n).real (latticeProjection L '' K)


-- @@ L681-692 verbatim
lemma projection_dilate_nsmul {n : ℕ} (L : Submodule ℤ (RealSpace n))
    [DiscreteTopology L] [IsZLattice ℝ L] (K : Set (RealSpace n))
    (k : ℕ) (hk : k ≠ 0) :
    (fun t : Torus n => k • t) '' (latticeProjection L '' ((k : ℝ)⁻¹ • K)) =
      latticeProjection L '' K := by
  have heq (x : RealSpace n) : k • latticeProjection L ((k : ℝ)⁻¹ • x) =
      latticeProjection L x := by
    rw [← map_nsmul]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hk), one_smul]
  rw [← Set.image_smul, Set.image_image, Set.image_image]
  simp only [heq]





-- @@ L697-720 verbatim
theorem completion {n : ℕ} (L : Submodule ℤ (RealSpace n))
    [DiscreteTopology L] [IsZLattice ℝ L] (K : Set (RealSpace n))
    (hK : IsCompact K) (hconv : Convex ℝ K) (k : ℕ) (hk : 0 < k)
    (hhole : holeProportion L K < (1-holeProportion L K)/(k : ℝ)^n) :
    ((1+(k : ℝ)⁻¹) • K)+(L : Set (RealSpace n)) = univ := by
  let A := latticeProjection L '' K
  let B := latticeProjection L '' ((k : ℝ)⁻¹ • K)
  have hB : IsCompact B := (hK.smul _).image (latticeProjection L).continuous
  have hm : (torusMeasure n).real A ≤ (k : ℝ)^n * (torusMeasure n).real B := by
    have h := torus_measure_image_nsmul n k hk.ne' hB
    rw [projection_dilate_nsmul L K k hk.ne'] at h
    exact h
  have hkpow : 0 < (k : ℝ)^n := pow_pos (Nat.cast_pos.mpr hk) n
  have hlow : 1-(torusMeasure n).real A < (torusMeasure n).real B := by
    have hh : (1-(torusMeasure n).real A)*(k : ℝ)^n < (torusMeasure n).real A := by
      have := (lt_div_iff₀ hkpow).mp hhole
      dsimp [holeProportion, A] at *
      linarith
    exact (mul_lt_mul_iff_right₀ hkpow).mp (by nlinarith)
  have hsum : A+B = univ := add_eq_univ_of_measure_sum (torusMeasure n) hB.measurableSet (by linarith)
  apply (latticeProjection_image_eq_univ_iff L _).mp
  rw [hconv.add_smul (show (0 : ℝ) ≤ 1 by norm_num) (inv_nonneg.mpr (Nat.cast_nonneg k)),
    one_smul, Set.image_add]
  exact hsum




-- @@ L724-726 verbatim
def contractLattice {n : ℕ} (L : Submodule ℤ (RealSpace n)) (a : ℝ) (ha : a ≠ 0) :
    Submodule ℤ (RealSpace n) :=
  ZLattice.comap ℝ L (LinearEquiv.smulOfNeZero ℝ (RealSpace n) a ha).toLinearMap


-- @@ L728-732 verbatim
instance contractLattice_discrete {n : ℕ} (L : Submodule ℤ (RealSpace n))
    [DiscreteTopology L] (a : ℝ) (ha : a ≠ 0) : DiscreteTopology (contractLattice L a ha) := by
  change DiscreteTopology (ZLattice.comap ℝ L
    (LinearEquiv.smulOfNeZero ℝ (RealSpace n) a ha).toContinuousLinearEquiv.toLinearMap)
  infer_instance


-- @@ L734-739 verbatim
instance contractLattice_fullSpan {n : ℕ} (L : Submodule ℤ (RealSpace n))
    [DiscreteTopology L] [IsZLattice ℝ L] (a : ℝ) (ha : a ≠ 0) :
    IsZLattice ℝ (contractLattice L a ha) := by
  change IsZLattice ℝ (ZLattice.comap ℝ L
    (LinearEquiv.smulOfNeZero ℝ (RealSpace n) a ha).toContinuousLinearEquiv.toLinearMap)
  infer_instance


-- @@ L741-743 verbatim
lemma mem_contractLattice {n : ℕ} (L : Submodule ℤ (RealSpace n))
    (a : ℝ) (ha : a ≠ 0) (x : RealSpace n) :
    x ∈ contractLattice L a ha ↔ a • x ∈ L := Iff.rfl


-- @@ L745-761 verbatim
lemma contractLattice_covolume {n : ℕ} (L : Submodule ℤ (RealSpace n))
    [DiscreteTopology L] [IsZLattice ℝ L] (a : ℝ) (ha : 0 < a) :
    ZLattice.covolume (contractLattice L a ha.ne') = a⁻¹^n * ZLattice.covolume L := by
  let b := IsZLattice.basis L
  let e := LinearEquiv.smulOfNeZero ℝ (RealSpace n) a ha.ne'
  let b' := b.ofZLatticeComap ℝ L e
  let : DiscreteTopology (ZLattice.comap ℝ L e.toLinearMap) := contractLattice_discrete L a ha.ne'
  let : IsZLattice ℝ (ZLattice.comap ℝ L e.toLinearMap) := contractLattice_fullSpan L a ha.ne'
  change ZLattice.covolume (ZLattice.comap ℝ L e.toLinearMap) = _
  rw [ZLattice.covolume_eq_det _ b', ZLattice.covolume_eq_det _ b]
  have hm : Matrix.of (Subtype.val ∘ b') = a⁻¹ • (Matrix.of (Subtype.val ∘ b) : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp only [Matrix.of_apply, Function.comp_apply, Matrix.smul_apply,
      Basis.ofZLatticeComap_apply, LinearEquiv.smulOfNeZero_symm_apply, Pi.smul_apply,
      smul_eq_mul, b', e]
    simp [Units.smul_def]
  rw [hm, Matrix.det_smul, abs_mul, abs_pow, abs_of_pos (inv_pos.mpr ha), Fintype.card_fin]


-- @@ L763-776 verbatim
lemma cover_contractLattice {n : ℕ} (L : Submodule ℤ (RealSpace n)) (K : Set (RealSpace n))
    (a : ℝ) (ha : a ≠ 0) (hcover : a • K+(L : Set (RealSpace n)) = univ) :
    K+(contractLattice L a ha : Set (RealSpace n)) = univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx : a • x ∈ a • K+(L : Set (RealSpace n)) := by rw [hcover]; trivial
  obtain ⟨v, hv, z, hz, hvz⟩ := hx
  obtain ⟨y, hy, rfl⟩ := hv
  refine ⟨y, hy, a⁻¹ • z, ?_, ?_⟩
  · change a • (a⁻¹ • z) ∈ L
    rw [smul_smul, mul_inv_cancel₀ ha, one_smul]
    exact hz
  · have h := congrArg (fun w : RealSpace n => a⁻¹ • w) hvz
    simpa only [smul_add, smul_smul, inv_mul_cancel₀ ha, one_smul] using h


-- @@ L778-784 verbatim
lemma one_add_inv_pow_le_exp (n : ℕ) (hn : n ≠ 0) :
    (1+(n : ℝ)⁻¹)^n ≤ Real.exp 1 := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1+(n : ℝ)⁻¹)
    (by simpa only [add_comm] using Real.add_one_le_exp (n : ℝ)⁻¹) n
  rw [← Real.exp_nat_mul, mul_inv_cancel₀ hnR] at h
  exact h


-- @@ L786-800 verbatim
lemma small_hole_strict {n : ℕ} (hn : 2 ≤ n) {δ : ℝ}
    (hδ : δ ≤ 1/(n : ℝ)^(2*n)) : δ < (1-δ)/(n : ℝ)^n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 2 ≤ (n : ℝ)^n := hnR.trans (le_self_pow₀ (by linarith) (by omega))
  have hp₀ : 0 < (n : ℝ)^n := by linarith
  rw [Nat.mul_comm 2 n, pow_mul] at hδ
  have hδ' := (le_div_iff₀ (sq_pos_of_pos hp₀)).mp hδ
  apply (lt_div_iff₀ hp₀).mpr
  have hpos : 0 < ((n : ℝ)^n)^2 - (n : ℝ)^n - 1 := by nlinarith
  have hratio : (1/((n : ℝ)^n)^2)*((n : ℝ)^n+1) < 1 := by
    rw [div_mul_eq_mul_div, one_mul]
    apply (div_lt_one (sq_pos_of_pos hp₀)).mpr
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hδ (by positivity : 0 ≤ (n : ℝ)^n+1)
  nlinarith





-- @@ L805-827 verbatim
theorem complete_almost_cover {n : ℕ} (hn : 2 ≤ n)
    (L : Submodule ℤ (RealSpace n)) [DiscreteTopology L] [IsZLattice ℝ L]
    (K : Set (RealSpace n)) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hhole : holeProportion L K ≤ 1/(n : ℝ)^(2*n)) :
    ∃ (L' : Submodule ℤ (RealSpace n)) (_ : DiscreteTopology L'),
      IsZLattice ℝ L' ∧ K+(L' : Set (RealSpace n)) = univ ∧
      (volume K).toReal / ZLattice.covolume L' ≤
        Real.exp 1 * ((volume K).toReal / ZLattice.covolume L) := by
  have hn₀ : 0 < n := by omega
  let a := 1+(n : ℝ)⁻¹
  have ha : 0 < a := by dsimp [a]; positivity
  let L' := contractLattice L a ha.ne'
  refine ⟨L', inferInstance, inferInstance, ?_, ?_⟩
  · exact cover_contractLattice L K a ha.ne'
      (completion L K hK hconv n hn₀ (small_hole_strict hn hhole))
  · have heq : (volume K).toReal / ZLattice.covolume L' =
        a^n * ((volume K).toReal / ZLattice.covolume L) := by
      rw [contractLattice_covolume L a ha, inv_pow, div_mul_eq_div_div,
        div_inv_eq_mul]
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right (one_add_inv_pow_le_exp n hn₀.ne')
      (div_nonneg ENNReal.toReal_nonneg (ZLattice.covolume_pos L).le)




-- @@ L831-831 verbatim
end SingleLatticeCovering.Completion


-- @@ L833-833 verbatim
end

-- @@ L834-834 verbatim
end


-- @@ L836-836 verbatim
section



-- @@ L839-839 verbatim
end

-- @@ L840-840 verbatim
end


-- @@ L842-842 verbatim
end OAI
