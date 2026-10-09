import OAI.Computability.Superstring.Threads


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace Superstring


-- @@ L7-7 verbatim
namespace Hierarchical.Threading


-- @@ L9-9 verbatim
variable {α ι : Type} {V : Set (List α)} [Fintype ι]


-- @@ L11-13 verbatim
/-- Full-text translation equivalence. Finite prefixes alone do not identify groups. -/
def SameText (C : Threading V ι) (i j : ι) : Prop :=
  ∃ d : ℤ, ∀ x : ℤ, C.text i (x + d) = C.text j x


-- @@ L15-28 verbatim
def textSetoid (C : Threading V ι) : Setoid ι where
  r := C.SameText
  iseqv := by
    constructor
    · intro i
      exact ⟨0, by intro x; simp only [add_zero]⟩
    · rintro i j ⟨d, hd⟩
      refine ⟨-d, ?_⟩
      intro x
      simpa only [add_assoc, neg_add_cancel, add_zero] using (hd (x + -d)).symm
    · rintro i j k ⟨d, hd⟩ ⟨e, he⟩
      refine ⟨e + d, ?_⟩
      intro x
      rw [← add_assoc, hd, he]


-- @@ L30-30 verbatim
def Groups (C : Threading V ι) := Quotient C.textSetoid


-- @@ L32-34 verbatim
noncomputable instance (C : Threading V ι) : Fintype C.Groups := by
  classical
  exact inferInstanceAs (Fintype (Quotient C.textSetoid))


-- @@ L36-36 verbatim
noncomputable instance (C : Threading V ι) : DecidableEq C.Groups := Classical.decEq _


-- @@ L38-38 verbatim
def group (C : Threading V ι) (i : ι) : C.Groups := Quotient.mk C.textSetoid i


-- @@ L40-41 verbatim
noncomputable def groupText (C : Threading V ι) (g : C.Groups) : ℤ → α :=
  C.text (Quotient.out g)


-- @@ L43-44 verbatim
noncomputable def groupPeriod (C : Threading V ι) (g : C.Groups) : ℕ :=
  Classical.choose (C.exists_primitive_text (Quotient.out g))


-- @@ L46-48 verbatim
theorem primitive_group (C : Threading V ι) (g : C.Groups) :
    Primitive (C.groupText g) (C.groupPeriod g) :=
  Classical.choose_spec (C.exists_primitive_text (Quotient.out g))


-- @@ L50-52 verbatim
/-- Alignment with an arbitrary fixed two-sided primitive text. -/
def Compatible (C : Threading V ι) (A : ℤ → α) :=
  {i : ι // ∃ d : ℤ, ∀ x, C.text i x = A (x + d)}


-- @@ L54-56 verbatim
noncomputable instance (C : Threading V ι) (A : ℤ → α) : Fintype (C.Compatible A) := by
  classical
  exact inferInstanceAs (Fintype {i : ι // ∃ d : ℤ, ∀ x, C.text i x = A (x + d)})


-- @@ L58-62 verbatim
def phaseMap (C : Threading V ι) {A : ℤ → α} {p : ℕ}
    (j : Fin p × C.Aligned A) : C.Compatible A :=
  ⟨(C.next ^ (j.1.val : ℤ)) j.2.val, (j.1.val : ℤ), by
    intro x
    rw [C.text_zpow, j.2.property]⟩


-- @@ L64-84 verbatim
omit [Fintype ι] in
theorem phaseMap_injective (C : Threading V ι) {A : ℤ → α} {p : ℕ}
    (hp : Primitive A p) : Function.Injective (C.phaseMap (A := A) (p := p)) := by
  rintro ⟨r, a⟩ ⟨s, b⟩ he
  have hval := congrArg Subtype.val he
  have hr : r = s := by
    apply Fin.ext
    have hh : (r.val : ℤ) = s.val := hp.alignment_unique
      (by omega) (by omega) (by omega) (by omega) (by
        intro x
        have ht := congrArg (fun i => C.text i x) hval
        change C.text ((C.next ^ (r.val : ℤ)) a.val) x =
          C.text ((C.next ^ (s.val : ℤ)) b.val) x at ht
        simpa only [C.text_zpow, a.property, b.property] using ht)
    omega
  subst s
  have hab : a = b := by
    apply Subtype.ext
    exact (C.next ^ (r.val : ℤ)).injective hval
  subst b
  rfl


-- @@ L86-112 verbatim
omit [Fintype ι] in
theorem phaseMap_surjective (C : Threading V ι) {A : ℤ → α} {p : ℕ}
    (hp : Primitive A p) : Function.Surjective (C.phaseMap (A := A) (p := p)) := by
  rintro ⟨i, d, hd⟩
  have hpz : (0 : ℤ) < p := by have := hp.positive; omega
  have hm0 := Int.emod_nonneg d (show (p : ℤ) ≠ 0 by omega)
  have hml := Int.emod_lt_of_pos d hpz
  let r : Fin p := ⟨(d % (p : ℤ)).toNat, by omega⟩
  have hr : (r.val : ℤ) = d % (p : ℤ) := by dsimp only [r]; omega
  have he : d - r.val = (d / (p : ℤ)) * p := by
    have := Int.emod_add_ediv_mul d (p : ℤ)
    omega
  have hper : Function.Periodic A (d - r.val) := by
    rw [he]
    simpa only [Int.cast_id] using hp.periodic.int_mul (d / (p : ℤ))
  let a : C.Aligned A := ⟨(C.next ^ (-(r.val : ℤ))) i, by
    funext x
    rw [C.text_zpow, hd]
    have hh := hper x
    convert hh using 1
    congr 1
    omega⟩
  refine ⟨⟨r, a⟩, ?_⟩
  apply Subtype.ext
  change (C.next ^ (r.val : ℤ)) ((C.next ^ (-(r.val : ℤ))) i) = i
  rw [← Equiv.Perm.mul_apply, ← zpow_add, add_neg_cancel, zpow_zero,
    Equiv.Perm.one_apply]


-- @@ L114-118 verbatim
/-- Every primitive phase and aligned passage occurs exactly once. This is the
finite bookkeeping behind splitting a long turn into primitive layers. -/
noncomputable def phaseEquiv (C : Threading V ι) {A : ℤ → α} {p : ℕ}
    (hp : Primitive A p) : (Fin p × C.Aligned A) ≃ C.Compatible A :=
  Equiv.ofBijective C.phaseMap ⟨C.phaseMap_injective hp, C.phaseMap_surjective hp⟩


-- @@ L120-135 verbatim
omit [Fintype ι] in
theorem compatible_group (C : Threading V ι) (g : C.Groups) (i : ι) :
    (∃ d : ℤ, ∀ x, C.text i x = C.groupText g (x + d)) ↔ C.group i = g := by
  have hq : C.group (Quotient.out g) = g := Quotient.out_eq g
  constructor
  · rintro ⟨d, hd⟩
    rw [← hq]
    apply Quotient.sound
    change C.SameText i (Quotient.out g)
    refine ⟨-d, ?_⟩
    intro x
    simpa only [add_assoc, neg_add_cancel, add_zero, groupText] using hd (x + -d)
  · intro hi
    have hh : C.SameText (Quotient.out g) i := Quotient.exact (hq.trans hi.symm)
    obtain ⟨d, hd⟩ := hh
    exact ⟨d, fun x => (hd x).symm⟩


-- @@ L137-139 verbatim
noncomputable def groupFiberEquiv (C : Threading V ι) (g : C.Groups) :
    C.Compatible (C.groupText g) ≃ {i : ι // C.group i = g} :=
  Equiv.subtypeEquivRight (C.compatible_group g)


-- @@ L141-147 verbatim
theorem group_card (C : Threading V ι) (g : C.Groups) :
    Fintype.card {i : ι // C.group i = g} =
      C.groupPeriod g * Fintype.card (C.Aligned (C.groupText g)) := by
  classical
  rw [← Fintype.card_congr (C.groupFiberEquiv g),
    ← Fintype.card_congr (C.phaseEquiv (C.primitive_group g)), Fintype.card_prod,
    Fintype.card_fin]


-- @@ L149-157 verbatim
/-- The exact second budget: primitive period times the number of layers sums
to the original number of down steps, hence to W for the base multiplicities. -/
theorem sum_layer_periods (C : Threading V ι) :
    ∑ g : C.Groups, C.groupPeriod g * Fintype.card (C.Aligned (C.groupText g)) =
      Fintype.card ι := by
  classical
  simp_rw [← C.group_card]
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv C.group)


-- @@ L159-161 verbatim
/-- Primitive phases with stable layer indices. -/
abbrev Phase (C : Threading V ι) :=
  Σ g : C.Groups, Fin (C.groupPeriod g) × Fin (Fintype.card (C.Aligned (C.groupText g)))


-- @@ L163-165 verbatim
noncomputable instance (C : Threading V ι) : Fintype C.Phase :=
  inferInstanceAs (Fintype (Σ g : C.Groups,
    Fin (C.groupPeriod g) × Fin (Fintype.card (C.Aligned (C.groupText g)))))


-- @@ L167-171 verbatim
noncomputable def groupPhaseEquiv (C : Threading V ι) (g : C.Groups) :
    (Fin (C.groupPeriod g) × Fin (Fintype.card (C.Aligned (C.groupText g)))) ≃
      {i : ι // C.group i = g} :=
  (Equiv.prodCongr (Equiv.refl _) (C.enumerate (C.groupText g))).trans
    ((C.phaseEquiv (C.primitive_group g)).trans (C.groupFiberEquiv g))


-- @@ L173-174 verbatim
noncomputable def allPhaseEquiv (C : Threading V ι) : C.Phase ≃ ι :=
  (Equiv.sigmaCongrRight C.groupPhaseEquiv).trans (Equiv.sigmaFiberEquiv C.group)


-- @@ L176-179 verbatim
theorem allPhaseEquiv_value (C : Threading V ι) (g : C.Groups)
    (r : Fin (C.groupPeriod g)) (j : Fin (Fintype.card (C.Aligned (C.groupText g)))) :
    C.allPhaseEquiv ⟨g, r, j⟩ =
      (C.next ^ (r.val : ℤ)) (C.enumerate (C.groupText g) j).val := rfl


-- @@ L181-184 verbatim
/-- Exit window of a sorted layer at a specified primitive phase. -/
noncomputable def phaseWord (C : Threading V ι) (i : C.Phase) : List α :=
  textWord (C.groupText i.1) i.2.1.val
    (C.sortedExit (C.groupText i.1) i.2.2 i.2.1.val)


-- @@ L186-186 verbatim
abbrev Recorded (C : Threading V ι) (s : List α) := {i : C.Phase // s <+: C.phaseWord i}


-- @@ L188-190 verbatim
noncomputable instance (C : Threading V ι) (s : List α) : Fintype (C.Recorded s) := by
  classical
  exact inferInstanceAs (Fintype {i : C.Phase // s <+: C.phaseWord i})


-- @@ L192-209 verbatim
/-- Sorting retains every prefix occurrence histogram, not just total edge cost. -/
theorem phase_prefix_count [DecidableEq α] (C : Threading V ι) (g : C.Groups)
    (r : Fin (C.groupPeriod g)) (s : List α) :
    (Finset.univ.filter (fun j => s <+: C.phaseWord ⟨g, r, j⟩)).card =
      (Finset.univ.filter (fun j => s <+: C.word (C.allPhaseEquiv ⟨g, r, j⟩))).card := by
  classical
  change (Finset.univ.filter (fun j =>
    s <+: textWord (C.groupText g) r.val
      (OrderStats.order (C.exits (C.groupText g) r.val) j))).card = _
  rw [OrderStats.card_filter_order (C.exits (C.groupText g) r.val)
    (fun e => s <+: textWord (C.groupText g) r.val e)]
  congr 1
  apply Finset.filter_congr
  intro j _
  have he := C.translated_word (C.enumerate (C.groupText g) j).val (r.val : ℤ)
  rw [(C.enumerate (C.groupText g) j).property] at he
  rw [C.allPhaseEquiv_value, he]
  rfl


-- @@ L211-224 verbatim
/-- The recorded-occurrence identity for any threaded circulation. -/
theorem card_recorded [DecidableEq α] (C : Threading V ι) (s : List α) :
    Fintype.card (C.Recorded s) =
      (Finset.univ.filter (fun i => s <+: C.word i)).card := by
  classical
  simp only [Fintype.card_subtype, Finset.card_filter]
  rw [← C.allPhaseEquiv.sum_comp (fun i => if s <+: C.word i then 1 else 0)]
  rw [Fintype.sum_sigma, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro g _
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  simpa only [Finset.card_filter] using C.phase_prefix_count g r s


-- @@ L226-226 verbatim
end Hierarchical.Threading


-- @@ L228-228 verbatim
namespace Counts.Data


-- @@ L230-230 verbatim
variable {α : Type} [DecidableEq α] [Inhabited α]


-- @@ L232-235 verbatim
theorem recorded_count (D : Data α) (hD : D.WellFormed) {s : List α} (hs : s ≠ []) :
    Fintype.card ((D.threading hD).Recorded s) = D.count s := by
  rw [Hierarchical.Threading.card_recorded]
  exact DownToken.prefix_count D hD hs


-- @@ L237-241 verbatim
theorem layer_budget (D : Data α) (hD : D.WellFormed) :
    ∑ g : (D.threading hD).Groups,
      (D.threading hD).groupPeriod g *
        Fintype.card ((D.threading hD).Aligned ((D.threading hD).groupText g)) = D.weight := by
  rw [Hierarchical.Threading.sum_layer_periods, DownToken.card D hD]


-- @@ L243-243 verbatim
end Counts.Data


-- @@ L245-245 verbatim
namespace Hierarchical


-- @@ L247-247 verbatim
variable {α : Type}


-- @@ L249-251 verbatim
/-- An occurrence in a two-sided text, retaining its integer origin. -/
def TextOccurs (A : ℤ → α) (s : List α) (x : ℤ) : Prop :=
  ∀ i : Fin s.length, s[i.val]? = some (A (x + i.val))


-- @@ L253-253 verbatim
namespace TextOccurs


-- @@ L255-255 verbatim
variable {A : ℤ → α} {s r : List α} {x d : ℤ}


-- @@ L257-260 verbatim
theorem word (A : ℤ → α) (a b : ℤ) : TextOccurs A (textWord A a b) a := by
  intro i
  rw [List.getElem?_eq_getElem i.isLt]
  simp only [textWord, List.getElem_ofFn]


-- @@ L262-268 verbatim
theorem eq_word (h : TextOccurs A s x) : s = textWord A x (x + s.length) := by
  apply List.ext_getElem
  · simp only [length_textWord, add_sub_cancel_left, Int.toNat_natCast]
  · intro i hi hi'
    have hh := h ⟨i, hi⟩
    simpa only [List.getElem?_eq_getElem hi, Option.some.injEq, textWord,
      List.getElem_ofFn] using hh


-- @@ L270-271 verbatim
theorem get (h : TextOccurs A s x) {i : ℕ} (hi : i < s.length) :
    s[i]? = some (A (x + i)) := h ⟨i, hi⟩


-- @@ L273-275 verbatim
theorem unique (hr : TextOccurs A r x) (hs : TextOccurs A s x)
    (hlen : r.length = s.length) : r = s := by
  rw [hr.eq_word, hs.eq_word, hlen]


-- @@ L277-283 verbatim
theorem trans (hr : TextOccurs A r x) {j : ℕ} (h : Counts.Occurs r s j) :
    TextOccurs A s (x + j) := by
  intro i
  have hi : j + i.val < r.length := by have := h.1; have := i.isLt; omega
  rw [← h.at i.isLt, hr.get hi]
  congr 2
  omega


-- @@ L285-293 verbatim
theorem shift (h : TextOccurs A s x) (hd : Function.Periodic A d) :
    TextOccurs A s (x + d) := by
  intro i
  rw [h i]
  congr 1
  have hh := hd (x + i.val)
  convert hh.symm using 1
  congr 1
  omega


-- @@ L295-311 verbatim
theorem prefix_iff {b : ℤ} (hb : x ≤ b) :
    s <+: textWord A x b ↔ TextOccurs A s x ∧ x + s.length ≤ b := by
  constructor
  · intro hs
    have hlen := hs.length_le
    rw [length_textWord] at hlen
    refine ⟨?_, by omega⟩
    intro i
    have he := hs.getElem i.isLt
    have hw := word A x b ⟨i.val, i.isLt.trans_le hs.length_le⟩
    simpa only [List.getElem?_eq_getElem i.isLt,
      List.getElem?_eq_getElem (i.isLt.trans_le hs.length_le), he] using hw
  · rintro ⟨hs, hlen⟩
    rw [hs.eq_word]
    have he := textWord_append A (show x ≤ x + s.length by omega) hlen
    rw [← he]
    exact List.prefix_append _ _


-- @@ L313-313 verbatim
end TextOccurs


-- @@ L315-315 verbatim
namespace Layer


-- @@ L317-317 verbatim
variable {V : Set (List α)} {A : ℤ → α} {p : ℕ}


-- @@ L319-321 verbatim
/-- The entire recording criterion is the exit window at the occurrence start. -/
def Records (D : Layer V A p) (s : List α) (x : ℤ) : Prop :=
  TextOccurs A s x ∧ x + s.length ≤ D.z x


-- @@ L323-327 verbatim
theorem records_iff_prefix (D : Layer V A p) (s : List α) (x : ℤ) :
    D.Records s x ↔ s <+: textWord A x (D.z x) := by
  have hh := D.lower (x + 1)
  simp only [add_sub_cancel_right] at hh
  exact (TextOccurs.prefix_iff (by omega : x ≤ D.z x)).symm


-- @@ L329-334 verbatim
theorem records_shift (D : Layer V A p) (per : Function.Periodic A (p : ℤ))
    {s : List α} {x : ℤ} (h : D.Records s x) (k : ℤ) : D.Records s (x + k * p) := by
  refine ⟨h.1.shift (by simpa only [Int.cast_id] using per.int_mul k), ?_⟩
  rw [D.shift_int]
  have := h.2
  omega


-- @@ L336-337 verbatim
def Occurrence (D : Layer V A p) (s : List α) :=
  {x : Fin p // D.Records s x.val}


-- @@ L339-341 verbatim
noncomputable instance (D : Layer V A p) (s : List α) : Fintype (D.Occurrence s) := by
  classical
  exact inferInstanceAs (Fintype {x : Fin p // D.Records s x.val})


-- @@ L343-355 verbatim
/-- Normalize an arbitrary lift of a recorded occurrence to its primitive phase. -/
def normalize (D : Layer V A p) (hp : 0 < p) (per : Function.Periodic A (p : ℤ))
    {s : List α} {x : ℤ} (h : D.Records s x) : D.Occurrence s := by
  have hpz : (0 : ℤ) < p := by omega
  have hm0 := Int.emod_nonneg x (show (p : ℤ) ≠ 0 by omega)
  have hml := Int.emod_lt_of_pos x hpz
  refine ⟨⟨(x % (p : ℤ)).toNat, by omega⟩, ?_⟩
  have hh := D.records_shift per h (-(x / (p : ℤ)))
  have he : x + -(x / (p : ℤ)) * p = (x % (p : ℤ)).toNat := by
    have := Int.emod_add_ediv_mul x (p : ℤ)
    rw [neg_mul]
    omega
  rwa [he] at hh


-- @@ L357-362 verbatim
theorem normalize_val (D : Layer V A p) (hp : 0 < p) (per : Function.Periodic A (p : ℤ))
    {s : List α} {x : ℤ} (h : D.Records s x) :
    ((D.normalize hp per h).val.val : ℤ) = x % p := by
  change (((x % (p : ℤ)).toNat : ℕ) : ℤ) = x % p
  have := Int.emod_nonneg x (show (p : ℤ) ≠ 0 by omega)
  omega


-- @@ L364-371 verbatim
/-- Every nonempty suboccurrence of a recorded interval is again recorded. -/
theorem records_suboccurrence (D : Layer V A p) {s r : List α} {x : ℤ} {j : ℕ}
    (hr : D.Records r x) (hs : Counts.Occurs r s j) : D.Records s (x + j) := by
  refine ⟨hr.1.trans hs, ?_⟩
  have hm : D.z x ≤ D.z (x + j) := D.mono (by omega)
  have := hr.2
  have := hs.1
  omega


-- @@ L373-373 verbatim
end Layer

-- @@ L374-374 verbatim
end Hierarchical


-- @@ L376-376 verbatim
end Superstring


-- @@ L378-378 verbatim
end OAI
