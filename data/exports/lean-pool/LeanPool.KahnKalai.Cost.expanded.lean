/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Clemens Posch
-/
module

public import LeanPool.KahnKalai.Basic


-- @@ L10-13 verbatim
/-!
Cover-cost calculus for Tran–Vu: the infimum is a minimum, subadditivity,
empty-family / empty-set evaluation, and `⊆`-minimals.
-/


-- @@ L15-15 verbatim
@[expose] public section


-- @@ L17-17 verbatim
open Finset


-- @@ L19-19 verbatim
namespace KahnKalai


-- @@ L21-21 verbatim
variable {α : Type*} [DecidableEq α] [Fintype α]


-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-27 verbatim
lemma generate_empty : generate (∅ : Finset (Finset α)) = ∅ := by
  ext T
  simp [mem_generate]


-- @@ L29-33 verbatim
lemma generate_eq_univ_of_empty_mem {F : Finset (Finset α)} (h : ∅ ∈ F) :
    generate F = univ := by
  ext T
  simp only [mem_univ, iff_true]
  exact mem_generate.mpr ⟨∅, h, empty_subset T⟩


-- @@ L35-37 verbatim
omit [DecidableEq α] [Fintype α] in
lemma expectation_empty (p : ℝ) : expectation p (∅ : Finset (Finset α)) = 0 := by
  simp [expectation]


-- @@ L39-42 verbatim
omit [DecidableEq α] [Fintype α] in
lemma expectation_singleton_empty (p : ℝ) :
    expectation p ({∅} : Finset (Finset α)) = 1 := by
  simp [expectation]


-- @@ L44-47 verbatim
omit [DecidableEq α] [Fintype α] in
lemma expectation_mono {p : ℝ} (hp : 0 ≤ p) {G₁ G₂ : Finset (Finset α)}
    (h : G₁ ⊆ G₂) : expectation p G₁ ≤ expectation p G₂ :=
  sum_le_sum_of_subset_of_nonneg h fun _ _ _ => pow_nonneg hp _


-- @@ L49-55 verbatim
omit [Fintype α] in
lemma expectation_union_le {p : ℝ} (hp : 0 ≤ p) (G₁ G₂ : Finset (Finset α)) :
    expectation p (G₁ ∪ G₂) ≤ expectation p G₁ + expectation p G₂ := by
  simp only [expectation]
  have h := sum_union_inter (f := fun S : Finset α => p ^ S.card) (s₁ := G₁) (s₂ := G₂)
  have : 0 ≤ ∑ S ∈ G₁ ∩ G₂, p ^ S.card := sum_nonneg fun _ _ => pow_nonneg hp _
  linarith


-- @@ L57-58 verbatim
lemma covers_empty (G : Finset (Finset α)) : Covers G (∅ : Finset (Finset α)) :=
  empty_subset _


-- @@ L60-62 verbatim
lemma covers_union {G H₁ H₂ : Finset (Finset α)} (h₁ : Covers G H₁) (h₂ : Covers G H₂) :
    Covers G (H₁ ∪ H₂) :=
  union_subset h₁ h₂


-- @@ L64-70 verbatim
lemma covers_union_covers {G₁ G₂ H₁ H₂ : Finset (Finset α)}
    (h₁ : Covers G₁ H₁) (h₂ : Covers G₂ H₂) : Covers (G₁ ∪ G₂) (H₁ ∪ H₂) := by
  intro T hT
  rw [mem_union] at hT
  rcases hT with hT | hT
  · exact generate_mono subset_union_left (h₁ hT)
  · exact generate_mono subset_union_right (h₂ hT)


-- @@ L72-74 verbatim
lemma covers_of_subset {G H₁ H₂ : Finset (Finset α)} (hH : H₁ ⊆ H₂) (h : Covers G H₂) :
    Covers G H₁ :=
  hH.trans h


-- @@ L76-79 verbatim
lemma covers_singleton_empty (H : Finset (Finset α)) :
    Covers ({∅} : Finset (Finset α)) H := by
  intro T _
  exact mem_generate.mpr ⟨∅, mem_singleton_self _, empty_subset T⟩


-- @@ L81-84 verbatim
lemma coverCost_le_one {p : ℝ} (hp : 0 ≤ p) (H : Finset (Finset α)) :
    coverCost p H ≤ 1 := by
  simpa [expectation_singleton_empty] using
    coverCost_le_expectation hp (covers_singleton_empty (H := H))


-- @@ L86-88 verbatim
lemma covers_set_nonempty (p : ℝ) (H : Finset (Finset α)) :
    ((fun G : Finset (Finset α) => expectation p G) '' {G | Covers G H}).Nonempty :=
  ⟨expectation p H, ⟨H, covers_self H, rfl⟩⟩


-- @@ L90-92 verbatim
lemma covers_set_finite (p : ℝ) (H : Finset (Finset α)) :
    ((fun G : Finset (Finset α) => expectation p G) '' {G | Covers G H}).Finite :=
  (Set.toFinite _).image _


-- @@ L94-100 verbatim
lemma exists_cover_eq_coverCost (p : ℝ) (H : Finset (Finset α)) :
    ∃ G, Covers G H ∧ expectation p G = coverCost p H := by
  have hne := covers_set_nonempty p H
  have hf := covers_set_finite p H
  have hmem := hne.csInf_mem hf
  obtain ⟨G, hG, hEq⟩ := hmem
  exact ⟨G, hG, hEq⟩


-- @@ L102-106 verbatim
lemma coverCost_empty {p : ℝ} (hp : 0 ≤ p) :
    coverCost p (∅ : Finset (Finset α)) = 0 := by
  refine le_antisymm ?_ (coverCost_nonneg hp _)
  simpa [expectation_empty] using
    coverCost_le_expectation hp (covers_empty (∅ : Finset (Finset α)))


-- @@ L108-111 verbatim
lemma coverCost_eq_zero_of_empty {p : ℝ} (hp : 0 ≤ p) {H : Finset (Finset α)}
    (hH : H = ∅) : coverCost p H = 0 := by
  subst hH
  exact coverCost_empty hp


-- @@ L113-117 verbatim
lemma coverCost_pos_imp_nonempty {p : ℝ} (hp : 0 ≤ p) {H : Finset (Finset α)}
    (h : 0 < coverCost p H) : H.Nonempty := by
  rw [nonempty_iff_ne_empty]
  intro hH
  exact h.ne' (coverCost_eq_zero_of_empty hp hH)


-- @@ L119-131 verbatim
lemma coverCost_of_mem_empty {p : ℝ} (hp : 0 ≤ p) {H : Finset (Finset α)}
    (h : ∅ ∈ H) : coverCost p H = 1 := by
  refine le_antisymm (coverCost_le_one hp H) ?_
  obtain ⟨G, hG, hGe⟩ := exists_cover_eq_coverCost p H
  have hempty : ∅ ∈ generate G := hG h
  obtain ⟨S, hS, hSempty⟩ := mem_generate.mp hempty
  have hS' : S = ∅ := subset_empty.mp hSempty
  subst hS'
  have : (1 : ℝ) ≤ expectation p G := by
    have := single_le_sum (f := fun T : Finset α => p ^ T.card)
      (fun T _ => pow_nonneg hp _) hS
    simpa [expectation] using this
  exact this.trans_eq hGe


-- @@ L133-138 verbatim
lemma coverCost_mono {p : ℝ} (hp : 0 ≤ p) {H₁ H₂ : Finset (Finset α)}
    (h : H₁ ⊆ H₂) : coverCost p H₁ ≤ coverCost p H₂ := by
  obtain ⟨G, hG, hGe⟩ := exists_cover_eq_coverCost p H₂
  have : coverCost p H₁ ≤ expectation p G :=
    coverCost_le_expectation hp (covers_of_subset h hG)
  exact this.trans_eq hGe


-- @@ L140-148 verbatim
lemma coverCost_union_le {p : ℝ} (hp : 0 ≤ p) (H₁ H₂ : Finset (Finset α)) :
    coverCost p (H₁ ∪ H₂) ≤ coverCost p H₁ + coverCost p H₂ := by
  obtain ⟨G₁, hG₁, hE₁⟩ := exists_cover_eq_coverCost p H₁
  obtain ⟨G₂, hG₂, hE₂⟩ := exists_cover_eq_coverCost p H₂
  have hcov : Covers (G₁ ∪ G₂) (H₁ ∪ H₂) := covers_union_covers hG₁ hG₂
  have : coverCost p (H₁ ∪ H₂) ≤ expectation p (G₁ ∪ G₂) :=
    coverCost_le_expectation hp hcov
  have hsum := expectation_union_le hp G₁ G₂
  linarith


-- @@ L150-156 verbatim
lemma coverCost_sdiff_ge {p : ℝ} (hp : 0 ≤ p) (H₁ H₂ : Finset (Finset α)) :
    coverCost p H₁ - coverCost p H₂ ≤ coverCost p (H₁ \ H₂) := by
  have h := coverCost_union_le hp (H₁ \ H₂) H₂
  rw [sdiff_union_self_eq_union] at h
  have hmono : coverCost p H₁ ≤ coverCost p (H₁ ∪ H₂) :=
    coverCost_mono hp subset_union_left
  linarith


-- @@ L158-161 verbatim
lemma coverCost_union_ge_sub {p : ℝ} (hp : 0 ≤ p) (A B : Finset (Finset α)) :
    coverCost p A - coverCost p B ≤ coverCost p (A ∪ B) - coverCost p B := by
  have := coverCost_mono hp (subset_union_left (s₁ := A) (s₂ := B))
  linarith


-- @@ L163-167 verbatim
/-- Subadditivity rearranged: `f(A) ≥ f(A ∪ B) - f(B)`. -/
lemma coverCost_ge_union_sub {p : ℝ} (hp : 0 ≤ p) (A B : Finset (Finset α)) :
    coverCost p (A ∪ B) - coverCost p B ≤ coverCost p A := by
  have := coverCost_union_le hp A B
  linarith


-- @@ L169-171 verbatim
/-- The inclusion-minimal members of a finite family. -/
def minimals (F : Finset (Finset α)) : Finset (Finset α) :=
  F.filter fun T => ∀ U ∈ F, U ⊆ T → U = T


-- @@ L173-174 verbatim
lemma minimals_subset (F : Finset (Finset α)) : minimals F ⊆ F :=
  filter_subset _ _


-- @@ L176-178 verbatim
lemma mem_minimals {F : Finset (Finset α)} {T : Finset α} :
    T ∈ minimals F ↔ T ∈ F ∧ ∀ U ∈ F, U ⊆ T → U = T :=
  mem_filter


-- @@ L180-191 verbatim
lemma exists_minimal_subset {F : Finset (Finset α)} {S : Finset α} (hS : S ∈ F) :
    ∃ T ∈ minimals F, T ⊆ S := by
  classical
  let C := F.filter (fun U => U ⊆ S)
  have hC : C.Nonempty := ⟨S, mem_filter.mpr ⟨hS, Subset.rfl⟩⟩
  obtain ⟨T, hT, hTmin⟩ := C.exists_min_image (fun U => U.card) hC
  have hTF : T ∈ F := (mem_filter.mp hT).1
  have hTS : T ⊆ S := (mem_filter.mp hT).2
  refine ⟨T, mem_filter.mpr ⟨hTF, fun U hU hUT => ?_⟩, hTS⟩
  have hUC : U ∈ C := mem_filter.mpr ⟨hU, hUT.trans hTS⟩
  have hcard : T.card ≤ U.card := hTmin U hUC
  exact eq_of_subset_of_card_le hUT (by simpa using hcard)


-- @@ L193-196 verbatim
lemma covers_minimals (F : Finset (Finset α)) : Covers (minimals F) F := by
  intro S hS
  obtain ⟨T, hT, hTS⟩ := exists_minimal_subset hS
  exact mem_generate.mpr ⟨T, hT, hTS⟩


-- @@ L198-203 verbatim
lemma covers_of_covers_minimals {G F : Finset (Finset α)}
    (h : Covers G (minimals F)) : Covers G F := by
  intro S hS
  obtain ⟨T, hT, hTS⟩ := exists_minimal_subset hS
  obtain ⟨U, hU, hUT⟩ := mem_generate.mp (h hT)
  exact mem_generate.mpr ⟨U, hU, hUT.trans hTS⟩


-- @@ L205-212 verbatim
lemma coverCost_minimals {p : ℝ} (hp : 0 ≤ p) (F : Finset (Finset α)) :
    coverCost p (minimals F) = coverCost p F := by
  apply le_antisymm
  · exact coverCost_mono hp (minimals_subset F)
  · obtain ⟨G, hG, hGe⟩ := exists_cover_eq_coverCost p (minimals F)
    have : coverCost p F ≤ expectation p G :=
      coverCost_le_expectation hp (covers_of_covers_minimals hG)
    exact this.trans_eq hGe


-- @@ L214-216 verbatim
/-- Restrict a family by removing every element of `W` from each member. -/
def restrictFamily (H : Finset (Finset α)) (W : Finset α) : Finset (Finset α) :=
  H.image fun S => S \ W


-- @@ L218-221 verbatim
omit [Fintype α] in
lemma mem_restrictFamily {H : Finset (Finset α)} {W T : Finset α} :
    T ∈ restrictFamily H W ↔ ∃ S ∈ H, S \ W = T :=
  mem_image


-- @@ L223-227 verbatim
omit [Fintype α] in
lemma restrictFamily_disjoint {H : Finset (Finset α)} {W T : Finset α}
    (h : T ∈ restrictFamily H W) : Disjoint T W := by
  obtain ⟨S, _, rfl⟩ := mem_restrictFamily.mp h
  exact disjoint_sdiff_self_left


-- @@ L229-232 verbatim
lemma restrictFamily_subset_sdiff {H : Finset (Finset α)} {W T : Finset α}
    (h : T ∈ restrictFamily H W) : T ⊆ univ \ W := by
  intro x hx
  exact mem_sdiff.mpr ⟨mem_univ x, disjoint_left.mp (restrictFamily_disjoint h) hx⟩


-- @@ L234-239 verbatim
lemma covers_restrict_of_covers {G H : Finset (Finset α)} {W : Finset α}
    (h : Covers G (restrictFamily H W)) : Covers G H := by
  intro S hS
  have hSW : S \ W ∈ restrictFamily H W := mem_image.mpr ⟨S, hS, rfl⟩
  obtain ⟨T, hT, hTS⟩ := mem_generate.mp (h hSW)
  exact mem_generate.mpr ⟨T, hT, hTS.trans sdiff_subset⟩


-- @@ L241-246 verbatim
lemma coverCost_le_restrict {p : ℝ} (hp : 0 ≤ p) (H : Finset (Finset α)) (W : Finset α) :
    coverCost p H ≤ coverCost p (restrictFamily H W) := by
  obtain ⟨G, hG, hGe⟩ := exists_cover_eq_coverCost p (restrictFamily H W)
  have : coverCost p H ≤ expectation p G :=
    coverCost_le_expectation hp (covers_restrict_of_covers hG)
  exact this.trans_eq hGe


-- @@ L248-252 verbatim
lemma coverCost_le_minimals_restrict {p : ℝ} (hp : 0 ≤ p)
    (H : Finset (Finset α)) (W : Finset α) :
    coverCost p H ≤ coverCost p (minimals (restrictFamily H W)) := by
  rw [coverCost_minimals hp]
  exact coverCost_le_restrict hp H W


-- @@ L254-256 verbatim
/-- Members of `F` with size strictly larger than `0.9 ℓ`. -/
def largeMinimals (H : Finset (Finset α)) (W : Finset α) (ℓ : ℕ) : Finset (Finset α) :=
  (minimals (restrictFamily H W)).filter fun T => ⌊((9 : ℝ) / 10) * ℓ⌋₊ + 1 ≤ T.card


-- @@ L258-260 verbatim
/-- Minimal restricted members whose size is at most `0.9 ℓ`. -/
def smallMinimals (H : Finset (Finset α)) (W : Finset α) (ℓ : ℕ) : Finset (Finset α) :=
  (minimals (restrictFamily H W)).filter fun T => T.card ≤ ⌊((9 : ℝ) / 10) * ℓ⌋₊


-- @@ L262-272 verbatim
lemma largeMinimals_union_small (H : Finset (Finset α)) (W : Finset α) (ℓ : ℕ) :
    largeMinimals H W ℓ ∪ smallMinimals H W ℓ = minimals (restrictFamily H W) := by
  classical
  ext T
  simp only [largeMinimals, smallMinimals, mem_union, mem_filter]
  constructor
  · rintro (h | h) <;> exact h.1
  · intro h
    rcases Nat.lt_or_ge T.card (⌊((9 : ℝ) / 10) * ℓ⌋₊ + 1) with hlt | hle
    · exact Or.inr ⟨h, Nat.lt_succ_iff.mp hlt⟩
    · exact Or.inl ⟨h, hle⟩


-- @@ L274-281 verbatim
lemma largeMinimals_disjoint_small (H : Finset (Finset α)) (W : Finset α) (ℓ : ℕ) :
    Disjoint (largeMinimals H W ℓ) (smallMinimals H W ℓ) := by
  classical
  refine disjoint_left.mpr ?_
  intro T hL hS
  have h1 := (mem_filter.mp hL).2
  have h2 := (mem_filter.mp hS).2
  exact (not_le_of_gt (Nat.lt_succ_iff.mpr h2)) h1


-- @@ L283-290 verbatim
lemma coverCost_small_ge {p : ℝ} (hp : 0 ≤ p) (H : Finset (Finset α))
    (W : Finset α) (ℓ : ℕ) :
    coverCost p (minimals (restrictFamily H W)) - coverCost p (largeMinimals H W ℓ)
      ≤ coverCost p (smallMinimals H W ℓ) := by
  have hU := largeMinimals_union_small H W ℓ
  have h := coverCost_union_le hp (smallMinimals H W ℓ) (largeMinimals H W ℓ)
  rw [union_comm, hU] at h
  linarith


-- @@ L292-297 verbatim
omit [Fintype α] in
lemma IsBounded.image_sdiff {H : Finset (Finset α)} {ℓ : ℕ} (hb : IsBounded H ℓ)
    (W : Finset α) : IsBounded (restrictFamily H W) ℓ := by
  intro T hT
  obtain ⟨S, hS, rfl⟩ := mem_restrictFamily.mp hT
  exact (card_le_card sdiff_subset).trans (hb S hS)


-- @@ L299-301 verbatim
lemma IsBounded.minimals {F : Finset (Finset α)} {ℓ : ℕ} (hb : IsBounded F ℓ) :
    IsBounded (minimals F) ℓ :=
  fun T hT => hb T (minimals_subset F hT)


-- @@ L303-306 verbatim
lemma IsBounded.largeMinimals {H : Finset (Finset α)} {ℓ : ℕ} (hb : IsBounded H ℓ)
    (W : Finset α) : IsBounded (largeMinimals H W ℓ) ℓ :=
  fun T hT =>
    (hb.image_sdiff W).minimals T (filter_subset _ _ hT)


-- @@ L308-312 verbatim
lemma IsBounded.smallMinimals {H : Finset (Finset α)} {W : Finset α} {ℓ ℓ₁ : ℕ}
    (hℓ₁ : ℓ₁ = ⌊((9 : ℝ) / 10) * ℓ⌋₊) :
    IsBounded (smallMinimals H W ℓ) ℓ₁ := by
  intro T hT
  exact hℓ₁ ▸ (mem_filter.mp hT).2


-- @@ L314-316 verbatim
lemma largeMinimals_card_gt {H : Finset (Finset α)} {W T : Finset α} {ℓ : ℕ}
    (h : T ∈ largeMinimals H W ℓ) : ⌊((9 : ℝ) / 10) * ℓ⌋₊ + 1 ≤ T.card :=
  (mem_filter.mp h).2


-- @@ L318-320 verbatim
lemma largeMinimals_mem_minimals {H : Finset (Finset α)} {W T : Finset α} {ℓ : ℕ}
    (h : T ∈ largeMinimals H W ℓ) : T ∈ minimals (restrictFamily H W) :=
  (mem_filter.mp h).1


-- @@ L322-326 verbatim
omit [DecidableEq α] in
lemma filter_card_eq_powersetCard (n : ℕ) :
    univ.filter (fun S : Finset α => S.card = n) = powersetCard n univ := by
  ext S
  simp [mem_powersetCard, subset_univ]


-- @@ L328-331 verbatim
omit [DecidableEq α] in
lemma card_level (n : ℕ) :
    #{S : Finset α | S.card = n} = (Fintype.card α).choose n := by
  rw [filter_card_eq_powersetCard, card_powersetCard, card_univ]


-- @@ L333-345 verbatim
lemma generate_level_frac_le (F : Finset (Finset α)) {s t : ℕ}
    (hst : s ≤ t) (ht : t ≤ Fintype.card α) :
    (((generate F).filter (fun S => S.card = s)).card : ℝ) /
        ((Fintype.card α).choose s : ℝ) ≤
      (((generate F).filter (fun S => S.card = t)).card : ℝ) /
        ((Fintype.card α).choose t : ℝ) := by
  revert ht
  induction t, hst using Nat.le_induction with
  | base => intro; exact le_rfl
  | succ n hn ih =>
    intro ht
    have hnN : n < Fintype.card α := Nat.lt_of_succ_le ht
    exact (ih hnN.le).trans (generate_level_frac_mono F n hnN)


-- @@ L347-351 verbatim
omit [DecidableEq α] [Fintype α] in
lemma expectation_mono_p {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q)
    (G : Finset (Finset α)) :
    expectation p G ≤ expectation q G :=
  sum_le_sum fun S _ => pow_le_pow_left₀ hp hpq S.card


-- @@ L353-358 verbatim
lemma coverCost_mono_p {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q)
    (H : Finset (Finset α)) :
    coverCost p H ≤ coverCost q H := by
  obtain ⟨G, hG, hGe⟩ := exists_cover_eq_coverCost q H
  have : coverCost p H ≤ expectation p G := coverCost_le_expectation hp hG
  exact this.trans ((expectation_mono_p hp hpq G).trans_eq hGe)


-- @@ L360-372 verbatim
omit [Fintype α] in
lemma expectation_zero (G : Finset (Finset α)) :
    expectation 0 G = if ∅ ∈ G then 1 else 0 := by
  classical
  have hterm : ∀ S ∈ G, (0 : ℝ) ^ S.card = if S = ∅ then 1 else 0 := by
    intro S _
    by_cases hS : S = ∅
    · simp [hS]
    · have hc : 0 < S.card := card_pos.mpr (nonempty_iff_ne_empty.mpr hS)
      rw [zero_pow hc.ne']
      simp [hS]
  simp only [expectation]
  rw [sum_congr rfl hterm, sum_ite_eq']


-- @@ L374-378 verbatim
lemma coverCost_zero_of_not_mem_empty {H : Finset (Finset α)} (h : ∅ ∉ H) :
    coverCost 0 H = 0 := by
  refine le_antisymm ?_ (coverCost_nonneg le_rfl H)
  have : expectation 0 H = 0 := by simp [expectation_zero, h]
  simpa [this] using coverCost_le_expectation (le_rfl : (0 : ℝ) ≤ 0) (covers_self H)


-- @@ L380-380 verbatim
end


-- @@ L382-382 verbatim
end KahnKalai
