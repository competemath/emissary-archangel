import Mathlib.Tactic
import Analysis.Section_9_6
import Analysis.Section_11_2


-- @@ L5-18 verbatim
/-!
# Analysis I, Section 11.3: Upper and lower Riemann integrals

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- The upper and lower Riemann integral; the Riemann integral.
- Upper and lower Riemann sums.

-/


-- @@ L20-20 verbatim
namespace Chapter11

-- @@ L21-21 verbatim
open BoundedInterval Chapter9


-- @@ L23-24 verbatim
/-- Definition 11.3.1 (Majorization of functions) -/
abbrev MajorizesOn (g f:ℝ → ℝ) (I: BoundedInterval) : Prop := ∀ x ∈ (I:Set ℝ), f x ≤ g x


-- @@ L26-26 verbatim
abbrev MinorizesOn (g f:ℝ → ℝ) (I: BoundedInterval) : Prop := ∀ x ∈ (I:Set ℝ), g x ≤ f x


-- @@ L28-28 verbatim
theorem MinorizesOn.iff (g f:ℝ → ℝ) (I: BoundedInterval) : MinorizesOn g f I ↔ MajorizesOn f g I := by rfl


-- @@ L30-32 verbatim
/-- Definition 11.3.2 (Upper and lower Riemann integrals ). -/
noncomputable abbrev upper_integral (f:ℝ → ℝ) (I: BoundedInterval) : ℝ :=
  sInf ((PiecewiseConstantOn.integ · I) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I})


-- @@ L34-35 verbatim
noncomputable abbrev lower_integral (f:ℝ → ℝ) (I: BoundedInterval) : ℝ :=
  sSup ((PiecewiseConstantOn.integ · I) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I})


-- @@ L37-39 verbatim
theorem upper_integral_congr {f g:ℝ → ℝ} {I: BoundedInterval} (h: Set.EqOn f g I) :
  upper_integral f I = upper_integral g I := by
  simp [upper_integral]; congr! 2; ext; simp; grind


-- @@ L41-43 verbatim
theorem lower_integral_congr {f g:ℝ → ℝ} {I: BoundedInterval} (h: Set.EqOn f g I) :
  lower_integral f I = lower_integral g I := by
  simp [lower_integral]; congr! 2; ext; simp; grind


-- @@ L45-49 expanded
lemma integral_bound_upper_of_bounded {f : ℝ → ℝ} {M : ℝ} {I : BoundedInterval}
    (h : ∀ x ∈ (I : Set ℝ), |f x| ≤ M) :
    M * BoundedInterval.length I ∈
      (PiecewiseConstantOn.integ · I) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I} :=
  by
  simp
  refine' ⟨fun _ ↦ M, ⟨⟨_, _⟩, PiecewiseConstantOn.integ_const _ _⟩⟩
  . grind [abs_le']
  apply (ConstantOn.of_const (c := M) _).piecewiseConstantOn; simp


-- @@ L51-55 expanded
lemma integral_bound_lower_of_bounded {f : ℝ → ℝ} {M : ℝ} {I : BoundedInterval}
    (h : ∀ x ∈ (I : Set ℝ), |f x| ≤ M) :
    -M * BoundedInterval.length I ∈
      (PiecewiseConstantOn.integ · I) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I} :=
  by
  simp
  refine' ⟨fun _ ↦ -M, ⟨⟨_, _⟩, by convert PiecewiseConstantOn.integ_const _ _ using 1; simp⟩⟩
  . grind [abs_le']
  exact (ConstantOn.of_const (c := -M) (by simp)).piecewiseConstantOn


-- @@ L57-58 verbatim
lemma integral_bound_upper_nonempty {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I) : ((PiecewiseConstantOn.integ · I) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I}).Nonempty :=
  ⟨ _, integral_bound_upper_of_bounded h.choose_spec ⟩


-- @@ L60-61 verbatim
lemma integral_bound_lower_nonempty {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I) : ((PiecewiseConstantOn.integ · I) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I}).Nonempty :=
  ⟨ _, integral_bound_lower_of_bounded h.choose_spec ⟩


-- @@ L63-69 verbatim
lemma integral_bound_lower_le_upper {f:ℝ → ℝ} {I: BoundedInterval} {a b:ℝ}
  (ha: a ∈ (PiecewiseConstantOn.integ · I) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I})
  (hb: b ∈ (PiecewiseConstantOn.integ · I) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I})
  : b ≤ a:= by
    obtain ⟨ g, ⟨ ⟨ hmaj, hgp⟩, rfl ⟩ ⟩ := ha
    obtain ⟨ h, ⟨ ⟨ hmin, hhp⟩, rfl ⟩ ⟩ := hb
    apply hhp.integ_mono _ hgp; intro x hx; linarith [hmin _ hx, hmaj _ hx]


-- @@ L71-74 verbatim
lemma integral_bound_below {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I) :
  BddBelow ((PiecewiseConstantOn.integ · I) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I}) := by
    rw [bddBelow_def]; use (integral_bound_lower_nonempty h).some
    intro a ha; exact integral_bound_lower_le_upper ha (integral_bound_lower_nonempty h).some_mem


-- @@ L76-79 verbatim
lemma integral_bound_above {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I) :
  BddAbove ((PiecewiseConstantOn.integ · I) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I}) := by
    rw [bddAbove_def]; use (integral_bound_upper_nonempty h).some
    intro b hb; exact integral_bound_lower_le_upper (integral_bound_upper_nonempty h).some_mem hb


-- @@ L81-84 expanded
/-- Lemma 11.3.3.  The proof has been reorganized somewhat from the textbook. -/
lemma le_lower_integral {f : ℝ → ℝ} {I : BoundedInterval} {M : ℝ}
    (h : ∀ x ∈ (I : Set ℝ), |f x| ≤ M) : -M * BoundedInterval.length I ≤ lower_integral f I :=
  le_csSup (integral_bound_above (BddOn.of_bounded h)) (integral_bound_lower_of_bounded h)


-- @@ L86-92 verbatim
lemma lower_integral_le_upper {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I) :
  lower_integral f I ≤ upper_integral f I := by
  apply csSup_le (integral_bound_lower_nonempty h)
  intros
  apply le_csInf (integral_bound_upper_nonempty h)
  intros
  solve_by_elim [integral_bound_lower_le_upper]


-- @@ L94-96 expanded
lemma upper_integral_le {f : ℝ → ℝ} {I : BoundedInterval} {M : ℝ}
    (h : ∀ x ∈ (I : Set ℝ), |f x| ≤ M) : upper_integral f I ≤ M * BoundedInterval.length I :=
  csInf_le (integral_bound_below (BddOn.of_bounded h)) (integral_bound_upper_of_bounded h)


-- @@ L98-102 verbatim
lemma upper_integral_le_integ {f g:ℝ → ℝ} {I: BoundedInterval} (hf: BddOn f I)
  (hfg: MajorizesOn g f I) (hg: PiecewiseConstantOn g I) :
  upper_integral f I ≤ hg.integ' := by
  apply csInf_le (integral_bound_below hf) _
  use g; simpa [hg]


-- @@ L104-108 verbatim
lemma integ_le_lower_integral {f h:ℝ → ℝ} {I: BoundedInterval} (hf: BddOn f I)
  (hfh: MinorizesOn h f I) (hg: PiecewiseConstantOn h I) :
  hg.integ' ≤ lower_integral f I := by
  apply le_csSup (integral_bound_above hf) _
  use h; simpa [hg]


-- @@ L110-114 verbatim
lemma lt_of_gt_upper_integral {f:ℝ → ℝ} {I: BoundedInterval} (hf: BddOn f I)
  {X:ℝ} (hX: upper_integral f I < X ) :
  ∃ g, MajorizesOn g f I ∧ PiecewiseConstantOn g I ∧ PiecewiseConstantOn.integ g I < X := by
  choose Y hY hYX using exists_lt_of_csInf_lt (integral_bound_upper_nonempty hf) hX
  simp at hY; peel hY; simp_all; tauto


-- @@ L116-120 verbatim
lemma gt_of_lt_lower_integral {f:ℝ → ℝ} {I: BoundedInterval} (hf: BddOn f I)
  {X:ℝ} (hX: X < lower_integral f I) :
  ∃ h, MinorizesOn h f I ∧ PiecewiseConstantOn h I ∧ X < PiecewiseConstantOn.integ h I := by
  choose Y hY hYX using exists_lt_of_lt_csSup (integral_bound_lower_nonempty hf) hX
  simp at hY; peel hY; simp_all; tauto


-- @@ L122-124 verbatim
/-- Definition 11.3.4 (Riemann integral)
As we permit junk values, the simplest definition for the Riemann integral is the upper integral. -/
noncomputable abbrev integ (f:ℝ → ℝ) (I: BoundedInterval) : ℝ := upper_integral f I


-- @@ L126-127 verbatim
theorem integ_congr {f g:ℝ → ℝ} {I: BoundedInterval} (h: Set.EqOn f g I) :
  integ f I = integ g I := upper_integral_congr h


-- @@ L129-130 verbatim
noncomputable abbrev IntegrableOn (f:ℝ → ℝ) (I: BoundedInterval) : Prop :=
  BddOn f I ∧ lower_integral f I = upper_integral f I


-- @@ L132-135 verbatim
/-- Lemma 11.3.7 / Exercise 11.3.3 -/
theorem integ_of_piecewise_const {f:ℝ → ℝ} {I: BoundedInterval} (hf: PiecewiseConstantOn f I) :
  IntegrableOn f I ∧ integ f I = hf.integ' := by
  sorry


-- @@ L137-143 expanded
/-- Remark 11.3.8 -/
theorem integ_on_subsingleton {f : ℝ → ℝ} {I : BoundedInterval}
    (hI : BoundedInterval.length I = 0) : IntegrableOn f I ∧ integ f I = 0 :=
  by
  observe : Subsingleton I.toSet
  observe hconst : ConstantOn f I
  convert integ_of_piecewise_const hconst.piecewiseConstantOn
  simp [PiecewiseConstantOn.integ_const' hconst, hI]


-- @@ L145-147 expanded
/--
Definition 11.3.9 (Riemann sums).  The restriction to positive length J is not needed thanks to various junk value conventions. -/
noncomputable abbrev upper_riemann_sum (f : ℝ → ℝ) {I : BoundedInterval} (P : Partition I) : ℝ :=
  ∑ J ∈ P.intervals, (sSup (f '' (J : Set ℝ))) * BoundedInterval.length J


-- @@ L149-150 expanded
noncomputable abbrev lower_riemann_sum (f : ℝ → ℝ) {I : BoundedInterval} (P : Partition I) : ℝ :=
  ∑ J ∈ P.intervals, (sInf (f '' (J : Set ℝ))) * BoundedInterval.length J


-- @@ L152-156 verbatim
/-- Lemma 11.3.11 / Exercise 11.3.4 -/
theorem upper_riemann_sum_le {f g: ℝ → ℝ} {I:BoundedInterval} (P: Partition I)
  (hgf: MajorizesOn g f I) (hg: PiecewiseConstantWith g P) :
  upper_riemann_sum f P ≤ integ g I := by
   sorry


-- @@ L158-161 verbatim
theorem lower_riemann_sum_ge {f h: ℝ → ℝ} {I:BoundedInterval} (P: Partition I)
  (hfh: MinorizesOn h f I) (hg: PiecewiseConstantWith h P) :
  integ h I ≤ lower_riemann_sum f P := by
   sorry


-- @@ L163-166 verbatim
/-- Proposition 11.3.12 / Exercise 11.3.5 -/
theorem upper_integ_le_upper_sum {f:ℝ → ℝ} {I:BoundedInterval} (hf: BddOn f I)
  (P: Partition I): upper_integral f I ≤ upper_riemann_sum f P := by
  sorry


-- @@ L168-170 verbatim
theorem upper_integ_eq_inf_upper_sum {f:ℝ → ℝ} {I:BoundedInterval} (hf: BddOn f I) :
  upper_integral f I = sInf (.range (fun P : Partition I ↦ upper_riemann_sum f P)) := by
  sorry


-- @@ L172-174 verbatim
theorem lower_integ_ge_lower_sum {f:ℝ → ℝ} {I:BoundedInterval} (hf: BddOn f I)
  (P: Partition I): lower_riemann_sum f P ≤ lower_integral f I := by
  sorry


-- @@ L176-178 verbatim
theorem lower_integ_eq_sup_lower_sum {f:ℝ → ℝ} {I:BoundedInterval} (hf: BddOn f I) :
  lower_integral f I = sSup (.range (fun P : Partition I ↦ lower_riemann_sum f P)) := by
  sorry


-- @@ L180-183 verbatim
/-- Exercise 11.3.1 (i) -/
theorem MajorizesOn.trans {f g h: ℝ → ℝ} {I: BoundedInterval}
  (hfg: MajorizesOn f g I) (hgh: MajorizesOn g h I) : MajorizesOn f h I := by
  sorry


-- @@ L185-188 verbatim
/-- Exercise 11.3.1 (ii) -/
theorem MajorizesOn.anti_symm {f g: ℝ → ℝ} {I: BoundedInterval}:
  (∀ x ∈ (I:Set ℝ), f x = g x) ↔ MajorizesOn f g I ∧ MajorizesOn g f I := by
  sorry


-- @@ L190-194 verbatim
/-- Exercise 11.3.2 -/
def MajorizesOn.of_add : Decidable ( ∀ (f g h:ℝ → ℝ) (I:BoundedInterval) (hfg: MajorizesOn f g I),
 MajorizesOn (f+h) (g+h) I) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry


-- @@ L196-199 verbatim
def MajorizesOn.of_mul : Decidable ( ∀ (f g h:ℝ → ℝ) (I:BoundedInterval) (hfg: MajorizesOn f g I),
 MajorizesOn (f*h) (g*h) I) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry


-- @@ L201-204 verbatim
def MajorizesOn.of_smul : Decidable ( ∀ (f g:ℝ → ℝ) (c:ℝ) (I:BoundedInterval) (hfg: MajorizesOn f g I),
 MajorizesOn (c • f) (c • g) I) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry



-- @@ L207-207 verbatim
end Chapter11
