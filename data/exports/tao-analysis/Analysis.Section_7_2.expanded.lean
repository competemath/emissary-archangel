import Mathlib.Tactic
import Mathlib.Algebra.Field.Power


-- @@ L4-18 verbatim
/-!
# Analysis I, Section 7.2: Infinite series

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Formal series and their limits.
- Absolute convergence; basic series laws.

-/


-- @@ L20-20 verbatim
namespace Chapter7


-- @@ L22-22 verbatim
open BigOperators


-- @@ L24-32 verbatim
/--
  Definition 7.2.1 (Formal infinite series). This is similar to Chapter 6 sequence, but is
  manipulated differently. As with Chapter 5, we will start series from 0 by default.
-/
@[ext]
structure Series where
  m : ℤ
  seq : ℤ → ℝ
  vanish : ∀ n < m, seq n = 0


-- @@ L34-40 verbatim
/-- Functions from ℕ to ℝ can be thought of as series. -/
instance Series.instCoe : Coe (ℕ → ℝ) Series where
  coe := fun a ↦ {
    m := 0
    seq n := if n ≥ 0 then a n.toNat else 0
    vanish := by grind
  }


-- @@ L42-43 verbatim
@[simp]
theorem Series.eval_coe (a: ℕ → ℝ) (n: ℕ) : (a: Series).seq n = a n := by simp


-- @@ L45-48 verbatim
abbrev Series.mk' {m:ℤ} (a: { n // n ≥ m } → ℝ) : Series where
  m := m
  seq n := if h : n ≥ m then a ⟨n, h⟩ else 0
  vanish := by grind


-- @@ L50-51 verbatim
theorem Series.eval_mk' {m:ℤ} (a : { n // n ≥ m } → ℝ) {n : ℤ} (h:n ≥ m) :
    (Series.mk' a).seq n = a ⟨ n, h ⟩ := by simp [h]


-- @@ L53-54 verbatim
/-- Definition 7.2.2 (Convergence of series) -/
noncomputable abbrev Series.partial (s : Series) (N:ℤ) : ℝ := ∑ n ∈ Finset.Icc s.m N, s.seq n


-- @@ L56-60 verbatim
theorem Series.partial_succ (s : Series) {N:ℤ} (h: N ≥ s.m-1) : s.partial (N+1) = s.partial N + s.seq (N+1) := by
  unfold Series.partial
  rw [add_comm (s.partial N) _]
  convert Finset.sum_insert (show N+1 ∉ Finset.Icc s.m N by simp)
  symm; apply Finset.insert_Icc_right_eq_Icc_add_one; linarith


-- @@ L62-65 verbatim
theorem Series.partial_of_lt {s : Series} {N:ℤ} (h: N < s.m) : s.partial N = 0 := by
  unfold Series.partial
  rw [Finset.sum_eq_zero]
  intro n hn; simp at hn; grind


-- @@ L67-67 verbatim
abbrev Series.convergesTo (s : Series) (L:ℝ) : Prop := Filter.atTop.Tendsto (s.partial) (nhds L)


-- @@ L69-69 verbatim
abbrev Series.converges (s : Series) : Prop := ∃ L, s.convergesTo L


-- @@ L71-71 verbatim
abbrev Series.diverges (s : Series) : Prop := ¬s.converges


-- @@ L73-74 verbatim
open Classical in
noncomputable abbrev Series.sum (s : Series) : ℝ := if h : s.converges then h.choose else 0


-- @@ L76-77 verbatim
theorem Series.converges_of_convergesTo {s : Series} {L:ℝ} (h: s.convergesTo L) :
    s.converges := by use L


-- @@ L79-82 verbatim
/-- Remark 7.2.3 -/
theorem Series.sum_of_converges {s : Series} {L:ℝ} (h: s.convergesTo L) : s.sum = L := by
  simp [sum, converges_of_convergesTo h]
  exact tendsto_nhds_unique ((converges_of_convergesTo h).choose_spec) h


-- @@ L84-85 verbatim
theorem Series.convergesTo_uniq {s : Series} {L L':ℝ} (h: s.convergesTo L) (h': s.convergesTo L') :
    L = L' := tendsto_nhds_unique h h'


-- @@ L87-88 verbatim
theorem Series.convergesTo_sum {s : Series} (h: s.converges) : s.convergesTo s.sum := by
  simp [sum, h]; exact h.choose_spec


-- @@ L90-91 verbatim
/-- Example 7.2.4 -/
noncomputable abbrev Series.example_7_2_4 := mk' (m := 1) (fun n ↦ (2:ℝ)^(-n:ℤ))


-- @@ L93-94 verbatim
theorem Series.example_7_2_4a {N:ℤ} (hN: N ≥ 1) : example_7_2_4.partial N = 1 - (2:ℝ)^(-N) := by
  sorry


-- @@ L96-96 verbatim
theorem Series.example_7_2_4b : example_7_2_4.convergesTo 1 := by sorry


-- @@ L98-98 verbatim
theorem Series.example_7_2_4c : example_7_2_4.sum = 1 := by sorry


-- @@ L100-100 verbatim
noncomputable abbrev Series.example_7_2_4' := mk' (m := 1) (fun n ↦ (2:ℝ)^(n:ℤ))


-- @@ L102-103 verbatim
theorem Series.example_7_2_4'a {N:ℤ} (hN: N ≥ 1) : example_7_2_4'.partial N = (2:ℝ)^(N+1) - 2 := by
  sorry


-- @@ L105-105 verbatim
theorem Series.example_7_2_4'b : example_7_2_4'.diverges := by sorry


-- @@ L107-110 verbatim
/-- Proposition 7.2.5 / Exercise 7.2.2 -/
theorem Series.converges_iff_tail_decay (s:Series) :
    s.converges ↔ ∀ ε > 0, ∃ N ≥ s.m, ∀ p ≥ N, ∀ q ≥ N, |∑ n ∈ Finset.Icc p q, s.seq n| ≤ ε := by
  sorry


-- @@ L112-115 verbatim
/-- Corollary 7.2.6 (Zero test) / Exercise 7.2.3 -/
theorem Series.decay_of_converges {s:Series} (h: s.converges) :
    Filter.atTop.Tendsto s.seq (nhds 0) := by
  sorry


-- @@ L117-119 verbatim
theorem Series.diverges_of_nodecay {s:Series} (h: ¬ Filter.atTop.Tendsto s.seq (nhds 0)) :
    s.diverges := by
  sorry


-- @@ L121-124 verbatim
/-- Example 7.2.7 -/
theorem Series.example_7_2_7 : ((fun _:ℕ ↦ (1:ℝ)):Series).diverges := by
  apply diverges_of_nodecay
  sorry


-- @@ L126-128 verbatim
theorem Series.example_7_2_7' : ((fun n:ℕ ↦ (-1:ℝ)^n):Series).diverges := by
  apply diverges_of_nodecay
  sorry


-- @@ L130-131 verbatim
/-- Definition 7.2.8 (Absolute convergence) -/
abbrev Series.abs (s:Series) : Series := mk' (m:=s.m) (fun n ↦ |s.seq n|)


-- @@ L133-133 verbatim
abbrev Series.absConverges (s:Series) : Prop := s.abs.converges


-- @@ L135-135 verbatim
abbrev Series.condConverges (s:Series) : Prop := s.converges ∧ ¬ s.absConverges


-- @@ L137-139 verbatim
/-- Proposition 7.2.9 (Absolute convergence test) / Exercise 7.2.4 -/
theorem Series.converges_of_absConverges {s:Series} (h : s.absConverges) : s.converges := by
  sorry


-- @@ L141-142 verbatim
theorem Series.abs_le {s:Series} (h : s.absConverges) : |s.sum| ≤ s.abs.sum := by
  sorry


-- @@ L144-183 verbatim
/-- Proposition 7.2.12 (Alternating series test) -/
theorem Series.converges_of_alternating {m:ℤ} {a: { n // n ≥ m} → ℝ} (ha: ∀ n, a n ≥ 0)
  (ha': Antitone a) :
    ((mk' (fun n ↦ (-1)^(n:ℤ) * a n)).converges ↔ Filter.atTop.Tendsto a (nhds 0)) := by
  -- This proof is written to follow the structure of the original text.
  constructor
  . intro h; apply decay_of_converges at h
    rw [tendsto_iff_dist_tendsto_zero] at h ⊢
    rw [←Filter.tendsto_comp_val_Ici_atTop (a := m)] at h
    refine h.congr (fun n => ?_)
    simp [n.property]
  intro h
  unfold converges convergesTo
  set b := mk' fun n ↦ (-1) ^ (n:ℤ) * a n
  set S := b.partial
  have claim0 {N:ℤ} (hN: N ≥ m) : S (N+1) = S N + (-1)^(N+1) * a ⟨ N+1, by grind ⟩ := by
    convert b.partial_succ ?_; simp [b, show N+1 ≥ m by grind]; linarith
  have claim1 {N:ℤ} (hN: N ≥ m) : S (N+2) = S N + (-1)^(N+1) * (a ⟨ N+1, by grind ⟩ - a ⟨ N+2, by grind ⟩) := calc
      S (N+2) = S N + (-1)^(N+1) * a ⟨ N+1, by grind ⟩ + (-1)^(N+2) * a ⟨ N+2, by grind ⟩ := by
        simp_rw [←claim0 hN, show N+2=N+1+1 by abel]; apply claim0; linarith
      _ = S N + (-1)^(N+1) * a ⟨ N+1, by grind ⟩ + (-1) * (-1)^(N+1) * a ⟨ N+2, by grind ⟩ := by
        congr; rw [←zpow_one_add₀] <;> grind
      _ = _ := by ring
  have claim2 {N:ℤ} (hN: N ≥ m) (h': Odd N) : S (N+2) ≥ S N := by
    simp [claim1 hN, h'.add_one.neg_one_zpow]; apply ha'; simp
  have claim3 {N:ℤ} (hN: N ≥ m) (h': Even N) : S (N+2) ≤ S N := by
    simp [claim1 hN, h'.add_one.neg_one_zpow]; apply ha'; simp
  have why1 {N:ℤ} (hN: N ≥ m) (h': Even N) (k:ℕ) : S (N+2*k) ≤ S N := by sorry
  have why2 {N:ℤ} (hN: N ≥ m) (h': Even N) (k:ℕ) : S (N+2*k+1) ≥ S N - a ⟨ N+1, by grind ⟩ := by sorry
  have why3 {N:ℤ} (hN: N ≥ m) (h': Even N) (k:ℕ) : S (N+2*k+1) ≤ S (N+2*k) := by sorry
  have claim4 {N:ℤ} (hN: N ≥ m) (h': Even N) (k:ℕ) : S N -
 a ⟨ N+1, by grind ⟩ ≤ S (N + 2*k + 1) ∧ S (N + 2*k + 1) ≤ S (N + 2*k) ∧ S (N + 2*k) ≤ S N := ⟨ ge_iff_le.mp (why2 hN h' k), why3 hN h' k, why1 hN h' k ⟩
  have why4 {N n:ℤ} (hN: N ≥ m) (h': Even N) (hn: n ≥ N) : S N - a ⟨ N+1, by grind ⟩ ≤ S n ∧ S n ≤ S N := by
    sorry
  have why5 {ε:ℝ} (hε: ε > 0) : ∃ N, ∀ n ≥ N, ∀ m ≥ N, |S n - S m| ≤ ε := by sorry
  have : CauchySeq S := by
    rw [Metric.cauchySeq_iff']
    intro ε hε; choose N hN using why5 (half_pos hε); use N
    intro n hn; rw [Real.dist_eq]; linarith [hN n hn N (by simp)]
  exact cauchySeq_tendsto_of_complete this


-- @@ L185-186 verbatim
/-- Example 7.2.13 -/
noncomputable abbrev Series.example_7_2_13 : Series := (mk' (m:=1) (fun n ↦ (-1:ℝ)^(n:ℤ) / (n:ℤ)))


-- @@ L188-189 verbatim
theorem Series.example_7_2_13a : example_7_2_13.converges := by
  sorry


-- @@ L191-192 verbatim
theorem Series.example_7_2_13b : ¬ example_7_2_13.absConverges := by
  sorry


-- @@ L194-195 verbatim
theorem Series.example_7_2_13c :  example_7_2_13.condConverges := by
  sorry


-- @@ L197-202 verbatim
instance Series.inst_add : Add Series where
  add a b := {
    m := min a.m b.m
    seq n := a.seq n + b.seq n
    vanish n hn := by simp [a.vanish n (by omega), b.vanish n (by omega)]
  }


-- @@ L204-207 verbatim
theorem Series.add_coe (a b: ℕ → ℝ) : (a:Series) + (b:Series) = (fun n ↦ a n + b n) := by
  ext n; rfl
  change (a:Series).seq n + (b:Series).seq n = _
  by_cases h:n ≥ 0 <;> simp [h]


-- @@ L209-212 verbatim
/-- Proposition 7.2.14 (a) (Series laws) / Exercise 7.2.5.  The {name}`convergesTo` form can be more convenient for applications. -/
theorem Series.convergesTo.add {s t:Series} {L M: ℝ} (hs: s.convergesTo L) (ht: t.convergesTo M) :
    (s + t).convergesTo (L + M) := by
  sorry


-- @@ L214-215 verbatim
theorem Series.add {s t:Series} (hs: s.converges) (ht: t.converges) :
    (s + t).converges ∧ (s+t).sum = s.sum + t.sum := by sorry


-- @@ L217-222 verbatim
instance Series.inst.smul : SMul ℝ Series where
  smul c s := {
    m := s.m
    seq n := if n ≥ s.m then c * s.seq n else 0
    vanish := by grind
  }


-- @@ L224-226 verbatim
theorem Series.smul_coe (a: ℕ → ℝ) (c: ℝ) : (c • a:Series) = (fun n ↦ c * a n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h, HSMul.hSMul, SMul.smul]


-- @@ L228-231 verbatim
/-- Proposition 7.2.14 (b) (Series laws) / Exercise 7.2.5.  The {name}`convergesTo` form can be more convenient for applications. -/
theorem Series.convergesTo.smul {s:Series} {L c: ℝ} (hs: s.convergesTo L) :
    (c • s).convergesTo (c * L) := by
  sorry


-- @@ L233-234 verbatim
theorem Series.smul {c:ℝ} {s:Series} (hs: s.converges) :
    (c • s).converges ∧ (c • s).sum = c * s.sum := by sorry


-- @@ L236-242 verbatim
/-- The corresponding API for subtraction was not in the textbook, but is useful in later sections, so is included here. -/
instance Series.inst_sub : Sub Series where
  sub a b := {
    m := min a.m b.m
    seq n := a.seq n - b.seq n
    vanish n hn := by simp [a.vanish n (by omega), b.vanish n (by omega)]
  }


-- @@ L244-247 verbatim
theorem Series.sub_coe (a b: ℕ → ℝ) : (a:Series) - (b:Series) = (fun n ↦ a n - b n) := by
  ext n; rfl
  change (a:Series).seq n - (b:Series).seq n = _
  by_cases h:n ≥ 0 <;> simp [h]


-- @@ L249-251 verbatim
theorem Series.convergesTo.sub {s t:Series} {L M: ℝ} (hs: s.convergesTo L) (ht: t.convergesTo M) :
    (s - t).convergesTo (L - M) := by
  sorry


-- @@ L253-254 verbatim
theorem Series.sub {s t:Series} (hs: s.converges) (ht: t.converges) :
    (s - t).converges ∧ (s-t).sum = s.sum - t.sum := by sorry


-- @@ L256-256 verbatim
abbrev Series.from (s:Series) (m₁:ℤ) : Series := mk' (m := max s.m m₁) (fun n ↦ s.seq (n:ℤ))


-- @@ L258-260 verbatim
/-- Proposition 7.2.14 (c) (Series laws) / Exercise 7.2.5 -/
theorem Series.converges_from (s:Series) (k:ℕ) : s.converges ↔ (s.from (s.m+k)).converges := by
  sorry


-- @@ L262-264 verbatim
theorem Series.sum_from {s:Series} (k:ℕ) (h: s.converges) :
    s.sum = ∑ n ∈ Finset.Ico s.m (s.m+k), s.seq n + (s.from (s.m+k)).sum := by
  sorry


-- @@ L266-269 verbatim
/-- Proposition 7.2.14 (d) (Series laws) / Exercise 7.2.5 -/
theorem Series.shift {s:Series} {x:ℝ} (h: s.convergesTo x) (L:ℤ) :
    (mk' (m := s.m + L) (fun n ↦ s.seq (n - L))).convergesTo x := by
  sorry


-- @@ L271-274 verbatim
/-- Lemma 7.2.15 (telescoping series) / Exercise 7.2.6 -/
theorem Series.telescope {a:ℕ → ℝ} (ha: Filter.atTop.Tendsto a (nhds 0)) :
    ((fun n:ℕ ↦ a n - a (n+1)):Series).convergesTo (a 0) := by
  sorry


-- @@ L276-280 verbatim
/-- Exercise 7.2.1 -/
def Series.exercise_7_2_1_convergent :
  Decidable ( (mk' (m := 1) (fun n ↦ (-1:ℝ)^(n:ℤ))).converges ) := by
  -- The first line of this proof should be `apply isTrue` or `apply isFalse`.
  sorry



-- @@ L283-283 verbatim
end Chapter7
