/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.OccurrenceFormulas


-- @@ L8-26 verbatim
/-!
# The occurrences of a variable, cyclically ordered

`DescriptiveComplexity.OccurrenceOrder` walks the occurrences of a *clause*; this
file walks those of a **variable** – the same signed positions `(c, s)`, read
along the other index – and closes the walk into a **cycle**
(`DescriptiveComplexity.SatOcc.VarNext`): the last occurrence of a variable is
followed by its first one.

That cycle is what a *truth-setting gadget* needs. A gadget laid along a path
of occurrences is forced into a single configuration, and forces the variable
to one truth value; laid along a cycle it admits exactly two, which is what
makes it an assignment. It is used by the reduction to 3-dimensional matching
(`DescriptiveComplexity.Problems.ThreeDimMatching.Hardness`).

Everything here has a first-order counterpart, over the ordered expansion
`DescriptiveComplexity.SatOcc.satOrd`, since the successor is “the next occurrence,
or the first one if there is no next”, and both halves are first-order.
-/


-- @@ L28-28 verbatim
namespace DescriptiveComplexity


-- @@ L30-30 verbatim
open FirstOrder


-- @@ L32-32 verbatim
namespace SatOcc


-- @@ L34-34 verbatim
open Language Structure


-- @@ L36-36 verbatim
/-! ### The cyclic order on the occurrences of a variable -/


-- @@ L38-38 verbatim
section Semantics


-- @@ L40-40 verbatim
variable {A : Type} [Language.sat.Structure A] [LinearOrder A]


-- @@ L42-44 verbatim
/-- `(c, s)` is the first occurrence of the variable `x`. -/
def VarMin (x c : A) (s : Bool) : Prop :=
  OccIn c x s ∧ ∀ c' t, OccIn c' x t → ¬occLt c' t c s


-- @@ L46-48 verbatim
/-- `(c, s)` is the last occurrence of the variable `x`. -/
def VarMax (x c : A) (s : Bool) : Prop :=
  OccIn c x s ∧ ∀ c' t, OccIn c' x t → ¬occLt c s c' t


-- @@ L50-53 verbatim
/-- `(c', t)` is the occurrence of `x` immediately after `(c, s)`. -/
def VarStep (x c : A) (s : Bool) (c' : A) (t : Bool) : Prop :=
  OccIn c x s ∧ OccIn c' x t ∧ occLt c s c' t ∧
    ∀ c'' u, OccIn c'' x u → ¬(occLt c s c'' u ∧ occLt c'' u c' t)


-- @@ L55-58 verbatim
/-- `(c', t)` follows `(c, s)` **cyclically** among the occurrences of `x`:
the next one, or the first one when `(c, s)` is the last. -/
def VarNext (x c : A) (s : Bool) (c' : A) (t : Bool) : Prop :=
  VarStep x c s c' t ∨ (VarMax x c s ∧ VarMin x c' t)


-- @@ L60-63 verbatim
theorem VarNext.occIn_left {x c c' : A} {s t : Bool} (h : VarNext x c s c' t) :
    OccIn c x s := by
  rcases h with h | ⟨h, -⟩
  exacts [h.1, h.1]


-- @@ L65-68 verbatim
theorem VarNext.occIn_right {x c c' : A} {s t : Bool} (h : VarNext x c s c' t) :
    OccIn c' x t := by
  rcases h with h | ⟨-, h⟩
  exacts [h.2.1, h.1]


-- @@ L70-76 verbatim
/-- The first occurrence of a variable is unique. -/
theorem varMin_unique {x c c' : A} {s t : Bool} (h : VarMin x c s) (h' : VarMin x c' t) :
    c = c' ∧ s = t := by
  rcases occLt_trichotomy c s c' t with hlt | ⟨hc, hs⟩ | hlt
  · exact absurd hlt (h'.2 c s h.1)
  · exact ⟨hc, hs⟩
  · exact absurd hlt (h.2 c' t h'.1)


-- @@ L78-84 verbatim
/-- The last occurrence of a variable is unique. -/
theorem varMax_unique {x c c' : A} {s t : Bool} (h : VarMax x c s) (h' : VarMax x c' t) :
    c = c' ∧ s = t := by
  rcases occLt_trichotomy c s c' t with hlt | ⟨hc, hs⟩ | hlt
  · exact absurd hlt (h.2 c' t h'.1)
  · exact ⟨hc, hs⟩
  · exact absurd hlt (h'.2 c s h.1)


-- @@ L86-92 verbatim
/-- The immediate successor is unique. -/
theorem varStep_right_unique {x c c₁ c₂ : A} {s t₁ t₂ : Bool} (h₁ : VarStep x c s c₁ t₁)
    (h₂ : VarStep x c s c₂ t₂) : c₁ = c₂ ∧ t₁ = t₂ := by
  rcases occLt_trichotomy c₁ t₁ c₂ t₂ with hlt | ⟨hc, ht⟩ | hlt
  · exact absurd ⟨h₁.2.2.1, hlt⟩ (h₂.2.2.2 c₁ t₁ h₁.2.1)
  · exact ⟨hc, ht⟩
  · exact absurd ⟨h₂.2.2.1, hlt⟩ (h₁.2.2.2 c₂ t₂ h₂.2.1)


-- @@ L94-100 verbatim
/-- The immediate predecessor is unique. -/
theorem varStep_left_unique {x c₁ c₂ c' : A} {s₁ s₂ t : Bool} (h₁ : VarStep x c₁ s₁ c' t)
    (h₂ : VarStep x c₂ s₂ c' t) : c₁ = c₂ ∧ s₁ = s₂ := by
  rcases occLt_trichotomy c₁ s₁ c₂ s₂ with hlt | ⟨hc, hs⟩ | hlt
  · exact absurd ⟨hlt, h₂.2.2.1⟩ (h₁.2.2.2 c₂ s₂ h₂.1)
  · exact ⟨hc, hs⟩
  · exact absurd ⟨hlt, h₁.2.2.1⟩ (h₂.2.2.2 c₁ s₁ h₁.1)


-- @@ L102-102 verbatim
variable [Finite A]


-- @@ L104-130 verbatim
/-- A nonempty set of occurrences of a variable has an `occLt`-least
element. -/
theorem exists_minOccP {x : A} {P : A → Bool → Prop} (h : ∃ c s, OccIn c x s ∧ P c s) :
    ∃ c s, OccIn c x s ∧ P c s ∧ ∀ c' t, OccIn c' x t → P c' t → ¬occLt c' t c s := by
  obtain ⟨c₀, hc₀, hmin⟩ :=
    Set.exists_min_image {c : A | ∃ s, OccIn c x s ∧ P c s} id (Set.toFinite _)
      (by obtain ⟨c, s, hcs⟩ := h; exact ⟨c, s, hcs⟩)
  by_cases h0 : OccIn c₀ x false ∧ P c₀ false
  · refine ⟨c₀, false, h0.1, h0.2, fun c' t hct hPt => ?_⟩
    rintro (hlt | ⟨rfl, hlt⟩)
    · exact absurd (hmin c' ⟨t, hct, hPt⟩) (not_le.mpr hlt)
    · exact absurd hlt (by simp)
  · obtain ⟨s₀, hs₀, hP₀⟩ := hc₀
    have hs₀' : s₀ = true := by
      cases s₀ with
      | false => exact absurd ⟨hs₀, hP₀⟩ h0
      | true => rfl
    subst hs₀'
    refine ⟨c₀, true, hs₀, hP₀, fun c' t hct hPt => ?_⟩
    rintro (hlt | ⟨rfl, hlt⟩)
    · exact absurd (hmin c' ⟨t, hct, hPt⟩) (not_le.mpr hlt)
    · have ht : t = false := by
        cases t with
        | false => rfl
        | true => exact absurd hlt (by simp)
      subst ht
      exact h0 ⟨hct, hPt⟩


-- @@ L132-155 verbatim
/-- A variable with an occurrence has a first one. -/
theorem exists_varMin {x : A} (h : ∃ c s, OccIn c x s) : ∃ c s, VarMin x c s := by
  obtain ⟨c₀, hc₀, hmin⟩ :=
    Set.exists_min_image {c : A | ∃ s, OccIn c x s} id (Set.toFinite _)
      (by obtain ⟨c, s, hcs⟩ := h; exact ⟨c, s, hcs⟩)
  by_cases h0 : OccIn c₀ x false
  · refine ⟨c₀, false, h0, fun c' t hct => ?_⟩
    rintro (hlt | ⟨rfl, hlt⟩)
    · exact absurd (hmin c' ⟨t, hct⟩) (not_le.mpr hlt)
    · exact absurd hlt (by simp)
  · obtain ⟨s₀, hs₀⟩ := hc₀
    have hs₀' : s₀ = true := by
      cases s₀ with
      | false => exact absurd hs₀ h0
      | true => rfl
    subst hs₀'
    refine ⟨c₀, true, hs₀, fun c' t hct => ?_⟩
    rintro (hlt | ⟨rfl, hlt⟩)
    · exact absurd (hmin c' ⟨t, hct⟩) (not_le.mpr hlt)
    · have ht : t = false := by
        cases t with
        | false => rfl
        | true => exact absurd hlt (by simp)
      exact h0 (ht ▸ hct)


-- @@ L157-180 verbatim
/-- A variable with an occurrence has a last one. -/
theorem exists_varMax {x : A} (h : ∃ c s, OccIn c x s) : ∃ c s, VarMax x c s := by
  obtain ⟨c₀, hc₀, hmax⟩ :=
    Set.exists_max_image {c : A | ∃ s, OccIn c x s} id (Set.toFinite _)
      (by obtain ⟨c, s, hcs⟩ := h; exact ⟨c, s, hcs⟩)
  by_cases h1 : OccIn c₀ x true
  · refine ⟨c₀, true, h1, fun c' t hct => ?_⟩
    rintro (hlt | ⟨rfl, hlt⟩)
    · exact absurd (hmax c' ⟨t, hct⟩) (not_le.mpr hlt)
    · exact absurd hlt (by simp)
  · obtain ⟨s₀, hs₀⟩ := hc₀
    have hs₀' : s₀ = false := by
      cases s₀ with
      | false => rfl
      | true => exact absurd hs₀ h1
    subst hs₀'
    refine ⟨c₀, false, hs₀, fun c' t hct => ?_⟩
    rintro (hlt | ⟨rfl, hlt⟩)
    · exact absurd (hmax c' ⟨t, hct⟩) (not_le.mpr hlt)
    · have ht : t = true := by
        cases t with
        | false => exact absurd hlt (by simp)
        | true => rfl
      exact h1 (ht ▸ hct)


-- @@ L182-207 verbatim
/-- An occurrence with a later one has an immediate successor. -/
theorem exists_varStep_right {x c : A} {s : Bool} (hx : OccIn c x s)
    (hne : ∃ c' t, OccIn c' x t ∧ occLt c s c' t) : ∃ c' t, VarStep x c s c' t := by
  obtain ⟨c₀, hc₀, hmin⟩ :=
    Set.exists_min_image {c' : A | ∃ t, OccIn c' x t ∧ occLt c s c' t} id (Set.toFinite _)
      (by obtain ⟨c', t, hct⟩ := hne; exact ⟨c', t, hct⟩)
  by_cases h0 : OccIn c₀ x false ∧ occLt c s c₀ false
  · refine ⟨c₀, false, hx, h0.1, h0.2, fun c'' u hc'' => ?_⟩
    rintro ⟨hlt₁, hlt₂ | ⟨rfl, hlt₂⟩⟩
    · exact absurd (hmin c'' ⟨u, hc'', hlt₁⟩) (not_le.mpr hlt₂)
    · exact absurd hlt₂ (by simp)
  · obtain ⟨t₀, ht₀, hlt₀⟩ := hc₀
    have ht₀' : t₀ = true := by
      cases t₀ with
      | false => exact absurd ⟨ht₀, hlt₀⟩ h0
      | true => rfl
    subst ht₀'
    refine ⟨c₀, true, hx, ht₀, hlt₀, fun c'' u hc'' => ?_⟩
    rintro ⟨hlt₁, hlt₂ | ⟨rfl, hlt₂⟩⟩
    · exact absurd (hmin c'' ⟨u, hc'', hlt₁⟩) (not_le.mpr hlt₂)
    · have hu : u = false := by
        cases u with
        | false => rfl
        | true => exact absurd hlt₂ (by simp)
      subst hu
      exact h0 ⟨hc'', hlt₁⟩


-- @@ L209-234 verbatim
/-- An occurrence with an earlier one has an immediate predecessor. -/
theorem exists_varStep_left {x c' : A} {t : Bool} (hx : OccIn c' x t)
    (hne : ∃ c s, OccIn c x s ∧ occLt c s c' t) : ∃ c s, VarStep x c s c' t := by
  obtain ⟨c₀, hc₀, hmax⟩ :=
    Set.exists_max_image {c : A | ∃ s, OccIn c x s ∧ occLt c s c' t} id (Set.toFinite _)
      (by obtain ⟨c, s, hcs⟩ := hne; exact ⟨c, s, hcs⟩)
  by_cases h1 : OccIn c₀ x true ∧ occLt c₀ true c' t
  · refine ⟨c₀, true, h1.1, hx, h1.2, fun c'' u hc'' => ?_⟩
    rintro ⟨hlt₁ | ⟨rfl, hlt₁⟩, hlt₂⟩
    · exact absurd (hmax c'' ⟨u, hc'', hlt₂⟩) (not_le.mpr hlt₁)
    · exact absurd hlt₁ (by simp)
  · obtain ⟨s₀, hs₀, hlt₀⟩ := hc₀
    have hs₀' : s₀ = false := by
      cases s₀ with
      | false => rfl
      | true => exact absurd ⟨hs₀, hlt₀⟩ h1
    subst hs₀'
    refine ⟨c₀, false, hs₀, hx, hlt₀, fun c'' u hc'' => ?_⟩
    rintro ⟨hlt₁ | ⟨rfl, hlt₁⟩, hlt₂⟩
    · exact absurd (hmax c'' ⟨u, hc'', hlt₂⟩) (not_le.mpr hlt₁)
    · have hu : u = true := by
        cases u with
        | false => exact absurd hlt₁ (by simp)
        | true => rfl
      subst hu
      exact h1 ⟨hc'', hlt₂⟩


-- @@ L236-244 verbatim
/-- **Every occurrence has a cyclic successor**: the next one, or the first
one when it is the last. -/
theorem exists_varNext {x c : A} {s : Bool} (hx : OccIn c x s) :
    ∃ c' t, VarNext x c s c' t := by
  by_cases hlast : ∃ c' t, OccIn c' x t ∧ occLt c s c' t
  · obtain ⟨c', t, hstep⟩ := exists_varStep_right hx hlast
    exact ⟨c', t, Or.inl hstep⟩
  · obtain ⟨c', t, hmin⟩ := exists_varMin ⟨c, s, hx⟩
    exact ⟨c', t, Or.inr ⟨⟨hx, fun c'' u hc'' hlt => hlast ⟨c'', u, hc'', hlt⟩⟩, hmin⟩⟩


-- @@ L246-253 verbatim
/-- **Every occurrence has a cyclic predecessor**. -/
theorem exists_varPrev {x c' : A} {t : Bool} (hx : OccIn c' x t) :
    ∃ c s, VarNext x c s c' t := by
  by_cases hfirst : ∃ c s, OccIn c x s ∧ occLt c s c' t
  · obtain ⟨c, s, hstep⟩ := exists_varStep_left hx hfirst
    exact ⟨c, s, Or.inl hstep⟩
  · obtain ⟨c, s, hmax⟩ := exists_varMax ⟨c', t, hx⟩
    exact ⟨c, s, Or.inr ⟨hmax, ⟨hx, fun c'' u hc'' hlt => hfirst ⟨c'', u, hc'', hlt⟩⟩⟩⟩


-- @@ L255-263 verbatim
omit [Finite A] in
/-- The cyclic successor is unique. -/
theorem varNext_right_unique {x c c₁ c₂ : A} {s t₁ t₂ : Bool} (h₁ : VarNext x c s c₁ t₁)
    (h₂ : VarNext x c s c₂ t₂) : c₁ = c₂ ∧ t₁ = t₂ := by
  rcases h₁ with h₁ | ⟨hmax₁, hmin₁⟩ <;> rcases h₂ with h₂ | ⟨hmax₂, hmin₂⟩
  · exact varStep_right_unique h₁ h₂
  · exact absurd h₁.2.2.1 (hmax₂.2 c₁ t₁ h₁.2.1)
  · exact absurd h₂.2.2.1 (hmax₁.2 c₂ t₂ h₂.2.1)
  · exact varMin_unique hmin₁ hmin₂


-- @@ L265-273 verbatim
omit [Finite A] in
/-- The cyclic predecessor is unique. -/
theorem varNext_left_unique {x c₁ c₂ c' : A} {s₁ s₂ t : Bool} (h₁ : VarNext x c₁ s₁ c' t)
    (h₂ : VarNext x c₂ s₂ c' t) : c₁ = c₂ ∧ s₁ = s₂ := by
  rcases h₁ with h₁ | ⟨hmax₁, hmin₁⟩ <;> rcases h₂ with h₂ | ⟨hmax₂, hmin₂⟩
  · exact varStep_left_unique h₁ h₂
  · exact absurd h₁.2.2.1 (hmin₂.2 c₁ s₁ h₁.1)
  · exact absurd h₂.2.2.1 (hmin₁.2 c₂ s₂ h₂.1)
  · exact varMax_unique hmax₁ hmax₂


-- @@ L275-275 verbatim
end Semantics


-- @@ L277-277 verbatim
/-! ### The first-order counterparts -/


-- @@ L279-279 verbatim
section Formulas


-- @@ L281-281 verbatim
variable {α : Type}


-- @@ L283-287 verbatim
/-- Some occurrence of the variable `x` lies strictly before `(c, s)`, as a
formula. -/
noncomputable def varEarlierF (s : Bool) (x c : α) : satOrd.Formula α :=
  ((occF false (.inr ()) (.inl x) ⊓ occLtF false s (.inr ()) (.inl c)) ⊔
    (occF true (.inr ()) (.inl x) ⊓ occLtF true s (.inr ()) (.inl c))).iExs Unit


-- @@ L289-293 verbatim
/-- Some occurrence of the variable `x` lies strictly after `(c, s)`, as a
formula. -/
noncomputable def varLaterF (s : Bool) (x c : α) : satOrd.Formula α :=
  ((occF false (.inr ()) (.inl x) ⊓ occLtF s false (.inl c) (.inr ())) ⊔
    (occF true (.inr ()) (.inl x) ⊓ occLtF s true (.inl c) (.inr ()))).iExs Unit


-- @@ L295-297 verbatim
/-- `(c, s)` is the first occurrence of the variable `x`, as a formula. -/
noncomputable def varMinF (s : Bool) (x c : α) : satOrd.Formula α :=
  occF s c x ⊓ ∼(varEarlierF s x c)


-- @@ L299-301 verbatim
/-- `(c, s)` is the last occurrence of the variable `x`, as a formula. -/
noncomputable def varMaxF (s : Bool) (x c : α) : satOrd.Formula α :=
  occF s c x ⊓ ∼(varLaterF s x c)


-- @@ L303-309 verbatim
/-- Some occurrence of `x` lies strictly between `(c, s)` and `(c', t)`, as a
formula. -/
noncomputable def varBetweenF (s t : Bool) (x c c' : α) : satOrd.Formula α :=
  (((occF false (.inr ()) (.inl x) ⊓ occLtF s false (.inl c) (.inr ())) ⊓
      occLtF false t (.inr ()) (.inl c')) ⊔
    ((occF true (.inr ()) (.inl x) ⊓ occLtF s true (.inl c) (.inr ())) ⊓
      occLtF true t (.inr ()) (.inl c'))).iExs Unit


-- @@ L311-314 verbatim
/-- `(c', t)` is the occurrence of `x` immediately after `(c, s)`, as a
formula. -/
noncomputable def varStepF (s t : Bool) (x c c' : α) : satOrd.Formula α :=
  occF s c x ⊓ occF t c' x ⊓ occLtF s t c c' ⊓ ∼(varBetweenF s t x c c')


-- @@ L316-319 verbatim
/-- `(c', t)` follows `(c, s)` cyclically among the occurrences of `x`, as a
formula. -/
noncomputable def varNextF (s t : Bool) (x c c' : α) : satOrd.Formula α :=
  varStepF s t x c c' ⊔ (varMaxF s x c ⊓ varMinF t x c')


-- @@ L321-321 verbatim
end Formulas


-- @@ L323-323 verbatim
section Realize


-- @@ L325-325 verbatim
variable {A : Type} [Language.sat.Structure A] [LinearOrder A] {α : Type} {v : α → A}


-- @@ L327-337 verbatim
@[simp]
theorem realize_varEarlierF {s : Bool} {x c : α} :
    (varEarlierF s x c).Realize v ↔ ∃ c' t, OccIn c' (v x) t ∧ occLt c' t (v c) s := by
  simp only [varEarlierF, Formula.realize_iExs, Formula.realize_sup, Formula.realize_inf,
    realize_occF, realize_occLtF, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨i, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩
    exacts [⟨i (), false, h₁, h₂⟩, ⟨i (), true, h₁, h₂⟩]
  · rintro ⟨c', t, h₁, h₂⟩
    cases t
    exacts [⟨fun _ => c', Or.inl ⟨h₁, h₂⟩⟩, ⟨fun _ => c', Or.inr ⟨h₁, h₂⟩⟩]


-- @@ L339-349 verbatim
@[simp]
theorem realize_varLaterF {s : Bool} {x c : α} :
    (varLaterF s x c).Realize v ↔ ∃ c' t, OccIn c' (v x) t ∧ occLt (v c) s c' t := by
  simp only [varLaterF, Formula.realize_iExs, Formula.realize_sup, Formula.realize_inf,
    realize_occF, realize_occLtF, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨i, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩
    exacts [⟨i (), false, h₁, h₂⟩, ⟨i (), true, h₁, h₂⟩]
  · rintro ⟨c', t, h₁, h₂⟩
    cases t
    exacts [⟨fun _ => c', Or.inl ⟨h₁, h₂⟩⟩, ⟨fun _ => c', Or.inr ⟨h₁, h₂⟩⟩]


-- @@ L351-357 verbatim
@[simp]
theorem realize_varMinF {s : Bool} {x c : α} :
    (varMinF s x c).Realize v ↔ VarMin (v x) (v c) s := by
  simp only [varMinF, Formula.realize_inf, Formula.realize_not, realize_occF,
    realize_varEarlierF, VarMin]
  exact and_congr Iff.rfl ⟨fun h c' t hc' hlt => h ⟨c', t, hc', hlt⟩,
    fun h ⟨c', t, hc', hlt⟩ => h c' t hc' hlt⟩


-- @@ L359-365 verbatim
@[simp]
theorem realize_varMaxF {s : Bool} {x c : α} :
    (varMaxF s x c).Realize v ↔ VarMax (v x) (v c) s := by
  simp only [varMaxF, Formula.realize_inf, Formula.realize_not, realize_occF,
    realize_varLaterF, VarMax]
  exact and_congr Iff.rfl ⟨fun h c' t hc' hlt => h ⟨c', t, hc', hlt⟩,
    fun h ⟨c', t, hc', hlt⟩ => h c' t hc' hlt⟩


-- @@ L367-378 verbatim
@[simp]
theorem realize_varBetweenF {s t : Bool} {x c c' : α} :
    (varBetweenF s t x c c').Realize v ↔
      ∃ c'' u, OccIn c'' (v x) u ∧ occLt (v c) s c'' u ∧ occLt c'' u (v c') t := by
  simp only [varBetweenF, Formula.realize_iExs, Formula.realize_sup, Formula.realize_inf,
    realize_occF, realize_occLtF, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨i, ⟨⟨h₁, h₂⟩, h₃⟩ | ⟨⟨h₁, h₂⟩, h₃⟩⟩
    exacts [⟨i (), false, h₁, h₂, h₃⟩, ⟨i (), true, h₁, h₂, h₃⟩]
  · rintro ⟨c'', u, h₁, h₂, h₃⟩
    cases u
    exacts [⟨fun _ => c'', Or.inl ⟨⟨h₁, h₂⟩, h₃⟩⟩, ⟨fun _ => c'', Or.inr ⟨⟨h₁, h₂⟩, h₃⟩⟩]


-- @@ L380-391 verbatim
@[simp]
theorem realize_varStepF {s t : Bool} {x c c' : α} :
    (varStepF s t x c c').Realize v ↔ VarStep (v x) (v c) s (v c') t := by
  simp only [varStepF, Formula.realize_inf, Formula.realize_not, realize_occF, realize_occLtF,
    realize_varBetweenF, VarStep]
  constructor
  · rintro ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩
    exact ⟨h₁, h₂, h₃, fun c'' u hc'' hb => h₄ ⟨c'', u, hc'', hb.1, hb.2⟩⟩
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    exact ⟨⟨⟨h₁, h₂⟩, h₃⟩, fun hb => by
      obtain ⟨c'', u, hc'', hb₁, hb₂⟩ := hb
      exact h₄ c'' u hc'' ⟨hb₁, hb₂⟩⟩


-- @@ L393-396 verbatim
@[simp]
theorem realize_varNextF {s t : Bool} {x c c' : α} :
    (varNextF s t x c c').Realize v ↔ VarNext (v x) (v c) s (v c') t := by
  simp [varNextF, VarNext]


-- @@ L398-398 verbatim
end Realize


-- @@ L400-400 verbatim
end SatOcc


-- @@ L402-402 verbatim
end DescriptiveComplexity
