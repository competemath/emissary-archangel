import OAI.Computability.Superstring.Counts


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace Superstring


-- @@ L7-7 verbatim
namespace Input


-- @@ L9-9 verbatim
variable {α : Type} [DecidableEq α]


-- @@ L11-14 verbatim
/-- Quadratic substring enumeration, with boundaries represented explicitly. -/
def subwords (s : List α) : Finset (List α) :=
  (Finset.range (s.length + 1)).biUnion fun i =>
    (Finset.range (s.length + 1)).image fun n => (s.drop i).take n


-- @@ L16-27 verbatim
theorem mem_subwords {w s : List α} : w ∈ subwords s ↔ w <:+: s := by
  constructor
  · intro hw
    obtain ⟨i, _, hw⟩ := Finset.mem_biUnion.mp hw
    obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hw
    exact (List.take_prefix _ _).isInfix.trans (List.drop_suffix _ _).isInfix
  · rintro ⟨a, b, rfl⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨a.length, Finset.mem_range.mpr (by simp only [List.length_append]; omega), ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨w.length, Finset.mem_range.mpr (by simp only [List.length_append]; omega), ?_⟩
    simp


-- @@ L29-31 verbatim
/-- Deleting empty, duplicate and properly contained input words. -/
def core (S : List (List α)) : Finset (List α) :=
  S.toFinset.filter fun s => s ≠ [] ∧ ∀ t ∈ S, s <:+: t → t = s


-- @@ L33-35 verbatim
theorem mem_core {S : List (List α)} {s : List α} :
    s ∈ core S ↔ s ∈ S ∧ s ≠ [] ∧ ∀ t ∈ S, s <:+: t → t = s := by
  simp only [core, Finset.mem_filter, List.mem_toFinset]


-- @@ L37-49 verbatim
theorem core_cover {S : List (List α)} {s : List α} (hs : s ∈ S) (hne : s ≠ []) :
    ∃ t ∈ core S, s <:+: t := by
  let F := S.toFinset.filter (fun t => s <:+: t)
  have hF : F.Nonempty := ⟨s, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hs, List.infix_refl s⟩⟩
  obtain ⟨t, ht, hmax⟩ := Finset.exists_max_image F List.length hF
  obtain ⟨htS, hst⟩ := Finset.mem_filter.mp ht
  refine ⟨t, mem_core.mpr ⟨List.mem_toFinset.mp htS, ?_, ?_⟩, hst⟩
  · intro ht0
    subst t
    exact hne (List.eq_nil_of_length_eq_zero (by have := hst.length_le; simpa using this))
  · intro u hu htu
    apply (htu.eq_of_length_le ?_).symm
    exact hmax u (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hu, hst.trans htu⟩)


-- @@ L51-52 verbatim
def vertices (S : List (List α)) : Finset (List α) :=
  insert [] (S.toFinset.biUnion subwords)


-- @@ L54-57 verbatim
theorem mem_vertices {S : List (List α)} {w : List α} :
    w ∈ vertices S ↔ w = [] ∨ ∃ s ∈ S, w <:+: s := by
  simp only [vertices, Finset.mem_insert, Finset.mem_biUnion, List.mem_toFinset,
    mem_subwords]


-- @@ L59-59 verbatim
def alphabet (S : List (List α)) : Finset α := S.flatten.toFinset


-- @@ L61-61 verbatim
def data (S : List (List α)) : Counts.Data α := ⟨vertices S, core S, alphabet S⟩


-- @@ L63-69 verbatim
theorem closed (S : List (List α)) : Hierarchical.SubstringClosed (vertices S : Set (List α)) := by
  intro s hs w hws
  rcases mem_vertices.mp hs with rfl | ⟨t, ht, hst⟩
  · apply mem_vertices.mpr
    left
    exact List.eq_nil_of_length_eq_zero (by have := hws.length_le; simpa using this)
  · exact mem_vertices.mpr (Or.inr ⟨t, ht, hws.trans hst⟩)


-- @@ L71-75 verbatim
theorem letter_mem {S : List (List α)} {w : List α} (hw : w ∈ vertices S)
    {c : α} (hc : c ∈ w) : c ∈ alphabet S := by
  rcases mem_vertices.mp hw with rfl | ⟨s, hs, hws⟩
  · simp only [List.not_mem_nil] at hc
  · exact List.mem_toFinset.mpr (List.mem_flatten.mpr ⟨s, hs, hws.sublist.subset hc⟩)


-- @@ L77-78 verbatim
theorem required_mem {S : List (List α)} {w : List α} (hw : w ∈ core S) :
    w ∈ vertices S := mem_vertices.mpr (Or.inr ⟨w, (mem_core.mp hw).1, List.infix_refl w⟩)


-- @@ L80-90 verbatim
theorem core_superstring_iff (S : List (List α)) (T : List α) :
    (∀ s ∈ core S, s <:+: T) ↔ ∀ s ∈ S, s <:+: T := by
  constructor
  · intro h s hs
    by_cases hnil : s = []
    · subst s
      exact List.nil_infix
    · obtain ⟨t, ht, hst⟩ := core_cover hs hnil
      exact hst.trans (h t ht)
  · intro h s hs
    exact h s (mem_core.mp hs).1


-- @@ L92-92 verbatim
end Input


-- @@ L94-95 verbatim
theorem concatenation_superstring (S : Instance) : IsCommonSuperstring S S.flatten :=
  fun _ hs => List.infix_of_mem_flatten hs


-- @@ L97-99 verbatim
theorem feasible_lengths_nonempty (S : Instance) :
    {n : ℕ | ∃ T : Word, IsCommonSuperstring S T ∧ T.length = n}.Nonempty :=
  ⟨S.flatten.length, S.flatten, concatenation_superstring S, rfl⟩


-- @@ L101-107 verbatim
/-- The actual computed lower bound is bounded by the unrestricted optimum. -/
theorem weight_le_opt (S : Instance) : (Input.data S).weight ≤ opt S := by
  unfold opt
  apply le_csInf (feasible_lengths_nonempty S)
  rintro n ⟨T, hT, rfl⟩
  apply Counts.Data.weight_le_length
  exact (Input.core_superstring_iff S T).mpr hT



-- @@ L110-114 verbatim
theorem input_count_le_total (S : Instance) {w : Word} (hw : w ≠ []) :
    (Input.data S).count w ≤ S.flatten.length :=
  le_trans ((Input.data S).count_le_number S.flatten
    ((Input.core_superstring_iff S S.flatten).mpr (concatenation_superstring S)) w)
    (Counts.number_le_length hw)


-- @@ L116-116 verbatim
namespace Counts.Data

-- @@ L117-117 verbatim
variable {α : Type} [DecidableEq α] [Inhabited α]


-- @@ L119-123 verbatim
/-- The hypotheses supplied by the actual all-substrings input construction. -/
structure WellFormed (D : Counts.Data α) : Prop where
  empty_mem : [] ∈ D.vertices
  closed : Hierarchical.SubstringClosed (D.vertices : Set (List α))
  letters : ∀ s ∈ D.vertices, ∀ c ∈ s, c ∈ D.alphabet


-- @@ L125-127 verbatim
omit [Inhabited α] in
theorem input_wellFormed (S : List (List α)) : (Input.data S).WellFormed :=
  ⟨Finset.mem_insert_self _ _, Input.closed S, fun _ hs _ hc => Input.letter_mem hs hc⟩


-- @@ L129-132 verbatim
theorem mem_of_count_ne_zero (D : Data α) {s : List α} (hs : D.count s ≠ 0) :
    s ∈ D.vertices := by
  by_contra h
  exact hs (D.count_zero _ (Or.inl h))


-- @@ L134-145 verbatim
theorem left_bound (D : Data α) (hD : D.WellFormed) {s : List α} (hs : s ≠ []) :
    (∑ c ∈ D.alphabet, D.count (c :: s)) ≤ D.count s := by
  by_cases hmem : s ∈ D.vertices
  · rw [← D.left_count]
    exact D.left_le_count hmem hs
  · have hz : ∀ c, D.count (c :: s) = 0 := by
      intro c
      apply D.count_zero
      left
      intro hcs
      exact hmem (hD.closed hcs (List.suffix_cons c s).isInfix)
    simp only [hz, Finset.sum_const_zero, Nat.zero_le]


-- @@ L147-158 verbatim
theorem right_bound (D : Data α) (hD : D.WellFormed) {s : List α} (hs : s ≠ []) :
    (∑ c ∈ D.alphabet, D.count (s ++ [c])) ≤ D.count s := by
  by_cases hmem : s ∈ D.vertices
  · rw [← D.right_count]
    exact D.right_le_count hmem hs
  · have hz : ∀ c, D.count (s ++ [c]) = 0 := by
      intro c
      apply D.count_zero
      left
      intro hsc
      exact hmem (hD.closed hsc (List.prefix_append s [c]).isInfix)
    simp only [hz, Finset.sum_const_zero, Nat.zero_le]



-- @@ L161-162 verbatim
def up (D : Data α) (s : List α) : ℕ :=
  D.count s - ∑ c ∈ D.alphabet, D.count (c :: s)


-- @@ L164-165 verbatim
def down (D : Data α) (s : List α) : ℕ :=
  D.count s - ∑ c ∈ D.alphabet, D.count (s ++ [c])


-- @@ L167-169 verbatim
theorem up_add (D : Data α) (hD : D.WellFormed) {s : List α} (hs : s ≠ []) :
    D.up s + ∑ c ∈ D.alphabet, D.count (c :: s) = D.count s :=
  Nat.sub_add_cancel (D.left_bound hD hs)


-- @@ L171-173 verbatim
theorem down_add (D : Data α) (hD : D.WellFormed) {s : List α} (hs : s ≠ []) :
    D.down s + ∑ c ∈ D.alphabet, D.count (s ++ [c]) = D.count s :=
  Nat.sub_add_cancel (D.right_bound hD hs)


-- @@ L175-200 verbatim
/-- Balance is an exact natural-number equality; no truncated subtraction is
silently cancelled without the extension inequalities. -/
theorem balanced (D : Data α) (hD : D.WellFormed) (s : List α) :
    D.up s + ∑ c ∈ D.alphabet, D.down (c :: s) =
      D.down s + ∑ c ∈ D.alphabet, D.up (s ++ [c]) := by
  have hd := Finset.sum_congr rfl (fun c (_hc : c ∈ D.alphabet) =>
    D.down_add hD (s := c :: s) (List.cons_ne_nil c s))
  have hu := Finset.sum_congr rfl (fun c (_hc : c ∈ D.alphabet) =>
    D.up_add hD (s := s ++ [c]) (by simp))
  rw [Finset.sum_add_distrib] at hd hu
  have heq : (∑ c ∈ D.alphabet, ∑ d ∈ D.alphabet, D.count ((c :: s) ++ [d])) =
      ∑ c ∈ D.alphabet, ∑ d ∈ D.alphabet, D.count (d :: (s ++ [c])) := by
    rw [Finset.sum_comm]
    rfl
  rw [heq] at hd
  by_cases hs : s = []
  · subst s
    have hz : D.count [] = 0 := D.count_zero _ (Or.inr rfl)
    have huz : D.up [] = 0 := by simp only [up, hz, Nat.zero_sub]
    have hdz : D.down [] = 0 := by simp only [down, hz, Nat.zero_sub]
    rw [huz, hdz]
    simp only [List.nil_append, zero_add] at hd hu ⊢
    omega
  · have hl := D.up_add hD hs
    have hr := D.down_add hD hs
    omega


-- @@ L202-221 verbatim
/-- Reindex all left extensions by their unique first letter and suffix. -/
theorem sum_left_all (D : Data α) (hD : D.WellFormed) :
    (∑ s ∈ D.vertices, ∑ c ∈ D.alphabet, D.count (c :: s)) =
      ∑ r ∈ D.vertices, D.count r := by
  rw [← Finset.sum_product D.vertices D.alphabet (fun a => D.count (a.2 :: a.1))]
  apply Finset.sum_bij_ne_zero (fun a _ _ => a.2 :: a.1)
  · intro a _ ha
    exact D.mem_of_count_ne_zero ha
  · intro a _ _ b _ _ hab
    obtain ⟨hc, hs⟩ := List.cons.inj hab
    exact Prod.ext hs hc
  · intro r hr hz
    cases r with
    | nil => exact (hz (D.count_zero _ (Or.inr rfl))).elim
    | cons c s =>
      have hs : s ∈ D.vertices := hD.closed hr (List.suffix_cons c s).isInfix
      have hc : c ∈ D.alphabet := hD.letters _ hr c (List.mem_cons_self ..)
      exact ⟨(s, c), Finset.mem_product.mpr ⟨hs, hc⟩, hz, rfl⟩
  · intros
    rfl


-- @@ L223-248 verbatim
/-- The dual reindexing by prefix and final letter. -/
theorem sum_right_all (D : Data α) (hD : D.WellFormed) :
    (∑ s ∈ D.vertices, ∑ c ∈ D.alphabet, D.count (s ++ [c])) =
      ∑ r ∈ D.vertices, D.count r := by
  rw [← Finset.sum_product D.vertices D.alphabet (fun a => D.count (a.1 ++ [a.2]))]
  apply Finset.sum_bij_ne_zero (fun a _ _ => a.1 ++ [a.2])
  · intro a _ ha
    exact D.mem_of_count_ne_zero ha
  · intro a _ _ b _ _ hab
    have hs := congrArg List.dropLast hab
    simp only [List.dropLast_concat] at hs
    have hc : a.2 = b.2 := by
      rw [hs] at hab
      simpa only [List.append_cancel_left_eq, List.cons.injEq, and_true] using hab
    exact Prod.ext hs hc
  · intro r hr hz
    have hne : r ≠ [] := by intro he; subst r; exact hz (D.count_zero _ (Or.inr rfl))
    let s := r.dropLast
    let c := r.getLast hne
    have hrsc : s ++ [c] = r := List.dropLast_append_getLast hne
    have hs : s ∈ D.vertices := hD.closed hr (hrsc ▸ (List.prefix_append s [c]).isInfix)
    have hc : c ∈ D.alphabet := hD.letters r hr c (hrsc ▸ (by simp))
    refine ⟨(s, c), Finset.mem_product.mpr ⟨hs, hc⟩, ?_, hrsc⟩
    simpa only [hrsc] using hz
  · intros
    rfl


-- @@ L250-264 verbatim
/-- Telescoping of all actual up-edge multiplicities. -/
theorem total_up (D : Data α) (hD : D.WellFormed) :
    (∑ s ∈ D.vertices, D.up s) = D.weight := by
  have hm := Finset.sum_erase_add D.vertices D.count hD.empty_mem
  have hl := Finset.sum_erase_add D.vertices
    (fun s => ∑ c ∈ D.alphabet, D.count (c :: s)) hD.empty_mem
  have hu := Finset.sum_erase_add D.vertices D.up hD.empty_mem
  have hh := Finset.sum_congr rfl (fun s (hs : s ∈ D.vertices.erase []) =>
    D.up_add hD (Finset.mem_erase.mp hs).1)
  rw [Finset.sum_add_distrib] at hh
  have hz : D.count [] = 0 := D.count_zero _ (Or.inr rfl)
  have huz : D.up [] = 0 := by simp only [up, hz, Nat.zero_sub]
  rw [D.sum_left_all hD] at hl
  change _ + D.weight = _ at hl
  omega


-- @@ L266-279 verbatim
theorem total_down (D : Data α) (hD : D.WellFormed) :
    (∑ s ∈ D.vertices, D.down s) = D.weight := by
  have hm := Finset.sum_erase_add D.vertices D.count hD.empty_mem
  have hl := Finset.sum_erase_add D.vertices
    (fun s => ∑ c ∈ D.alphabet, D.count (s ++ [c])) hD.empty_mem
  have hd := Finset.sum_erase_add D.vertices D.down hD.empty_mem
  have hh := Finset.sum_congr rfl (fun s (hs : s ∈ D.vertices.erase []) =>
    D.down_add hD (Finset.mem_erase.mp hs).1)
  rw [Finset.sum_add_distrib] at hh
  have hz : D.count [] = 0 := D.count_zero _ (Or.inr rfl)
  have hdz : D.down [] = 0 := by simp only [down, hz, Nat.zero_sub]
  rw [D.sum_right_all hD] at hl
  change _ + D.weight = _ at hl
  omega


-- @@ L281-281 verbatim
end Counts.Data


-- @@ L283-283 verbatim
end Superstring


-- @@ L285-285 verbatim
end OAI
