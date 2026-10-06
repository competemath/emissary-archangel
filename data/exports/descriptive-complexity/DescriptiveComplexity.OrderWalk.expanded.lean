/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Order.PiLex
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Card
import DescriptiveComplexity.Padding


-- @@ L11-47 verbatim
/-!
# Walking a finite linear order, first-order

Shared machinery for constructions that traverse a finite linear order – or the
lexicographic order on tuples – one step at a time, with each step described by
a first-order guard over the ordered expansion `L.sum Language.order`.

Two clients, one technique. The SO-Horn definition of HORN-SAT
(`DescriptiveComplexity.Problems.HornSat.Definability`) assembles the unbounded body of
an input clause by walking the order of its elements; the translation of
FO(LFP) into SO-Horn (`DescriptiveComplexity.FixedPointHorn`) walks the lexicographic
order of *stage* and *valuation* tuples to derive the complement of a fixed
point. Both need the same three ingredients, provided here:

* **guards**: formulas `DescriptiveComplexity.minF`, `DescriptiveComplexity.maxF`,
  `DescriptiveComplexity.succF` – being minimal, maximal, the immediate successor – and
  their tuple analogues `DescriptiveComplexity.minTupF`, `DescriptiveComplexity.maxTupF`,
  `DescriptiveComplexity.succTupF` for the lexicographic order, with realization lemmas
  phrased purely in terms of the order of the structure;
* **induction**: `DescriptiveComplexity.order_induction`, walking any finite linear order
  from its minimum along immediate successors – applied not only to the
  universe of a structure but to lexicographic tuple orders over it;
* **the bridge to `Lex`**: the coordinatewise conditions realized by the tuple
  guards characterize bottom, top and covering
  (`DescriptiveComplexity.tupSucc_iff_covBy`…) in `Lex (Fin D → A)`, and
  `DescriptiveComplexity.prodLex_covBy_iff`/`DescriptiveComplexity.finCovBy_iff` do the same for
  the lexicographic product heading a static index; so a walk described by
  guards is a walk along covers of a bona fide finite linear order.

Finally `DescriptiveComplexity.orank` – the rank of an element of a finite linear order,
the number of its strict predecessors – converts that walk into arithmetic:
rank `0` at the bottom (`DescriptiveComplexity.orank_eq_zero`), `+1` along a cover
(`DescriptiveComplexity.orank_covBy`), `Nat.card - 1` at the top
(`DescriptiveComplexity.orank_isTop`). This is how a fixed-point stage indexed by a
tuple is matched with the `ℕ`-indexed stages of
`DescriptiveComplexity.derivesIn`.
-/


-- @@ L49-49 verbatim
namespace DescriptiveComplexity


-- @@ L51-51 verbatim
open FirstOrder


-- @@ L53-53 verbatim
open Language Structure


-- @@ L55-55 verbatim
/-! ### Order guards -/


-- @@ L57-57 verbatim
section Guards


-- @@ L59-59 verbatim
variable {L : Language.{0, 0}} {α : Type}


-- @@ L61-63 verbatim
/-- `x ≤ y`, as a formula over the ordered expansion. -/
noncomputable def leF (x y : α) : (L.sum Language.order).Formula α :=
  Relations.formula₂ leSymb (Term.var x) (Term.var y)


-- @@ L65-67 verbatim
/-- `x < y`, as a formula over the ordered expansion. -/
noncomputable def ltF (x y : α) : (L.sum Language.order).Formula α :=
  leF x y ⊓ ∼(leF y x)


-- @@ L69-71 verbatim
/-- The variable `x` holds a minimum. -/
noncomputable def minF (x : α) : (L.sum Language.order).Formula α :=
  (leF (Sum.inl x) (Sum.inr 0)).iAlls (Fin 1)


-- @@ L73-75 verbatim
/-- The variable `x` holds a maximum. -/
noncomputable def maxF (x : α) : (L.sum Language.order).Formula α :=
  (leF (Sum.inr 0) (Sum.inl x)).iAlls (Fin 1)


-- @@ L77-81 verbatim
/-- `w` holds the immediate predecessor of `z`. -/
noncomputable def succF (w z : α) : (L.sum Language.order).Formula α :=
  ltF w z ⊓
    (show (L.sum Language.order).Formula (α ⊕ Fin 1) from
      ∼(ltF (Sum.inl w) (Sum.inr 0) ⊓ ltF (Sum.inr 0) (Sum.inl z))).iAlls (Fin 1)


-- @@ L83-83 verbatim
variable {A : Type} [L.Structure A] [LinearOrder A] {v : α → A}


-- @@ L85-88 verbatim
@[simp]
theorem realize_leF (x y : α) : (leF (L := L) x y).Realize v ↔ v x ≤ v y := by
  rw [leF, Formula.realize_rel₂, relMap_leSymb]
  exact Iff.rfl


-- @@ L90-93 verbatim
@[simp]
theorem realize_ltF (x y : α) : (ltF (L := L) x y).Realize v ↔ v x < v y := by
  rw [ltF, Formula.realize_inf, Formula.realize_not, realize_leF, realize_leF]
  exact lt_iff_le_not_ge.symm


-- @@ L95-99 verbatim
@[simp]
theorem realize_minF (x : α) : (minF (L := L) x).Realize v ↔ ∀ a : A, v x ≤ a := by
  rw [minF]
  simp only [Formula.realize_iAlls, realize_leF, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun h a => h fun _ => a, fun h i => h (i 0)⟩


-- @@ L101-105 verbatim
@[simp]
theorem realize_maxF (x : α) : (maxF (L := L) x).Realize v ↔ ∀ a : A, a ≤ v x := by
  rw [maxF]
  simp only [Formula.realize_iAlls, realize_leF, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun h a => h fun _ => a, fun h i => h (i 0)⟩


-- @@ L107-113 verbatim
@[simp]
theorem realize_succF (w z : α) :
    (succF (L := L) w z).Realize v ↔ v w < v z ∧ ∀ a : A, ¬(v w < a ∧ a < v z) := by
  rw [succF]
  simp only [Formula.realize_inf, Formula.realize_iAlls, Formula.realize_not, realize_ltF,
    Sum.elim_inl, Sum.elim_inr]
  exact and_congr Iff.rfl ⟨fun h a => h fun _ => a, fun h i => h (i 0)⟩


-- @@ L115-115 verbatim
end Guards


-- @@ L117-117 verbatim
/-! ### Immediate predecessors, and induction along a finite linear order -/


-- @@ L119-119 verbatim
section Pred


-- @@ L121-121 verbatim
variable {A : Type} [LinearOrder A] [Finite A]


-- @@ L123-137 verbatim
/-- In a finite linear order, an element that is not a minimum has an
immediate predecessor. -/
theorem exists_succ_of_not_min {z : A} (hz : ¬∀ a : A, z ≤ a) :
    ∃ w : A, w < z ∧ ∀ a : A, ¬(w < a ∧ a < z) := by
  classical
  have := Fintype.ofFinite A
  have hne : (Finset.univ.filter fun a : A => a < z).Nonempty := by
    push Not at hz
    obtain ⟨a, ha⟩ := hz
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩
  refine ⟨(Finset.univ.filter fun a : A => a < z).max' hne, ?_, ?_⟩
  · exact (Finset.mem_filter.mp ((Finset.univ.filter fun a : A => a < z).max'_mem hne)).2
  · rintro a ⟨hwa, haz⟩
    exact absurd ((Finset.univ.filter fun a : A => a < z).le_max'
      a (Finset.mem_filter.mpr ⟨Finset.mem_univ a, haz⟩)) (not_le.mpr hwa)


-- @@ L139-148 verbatim
/-- Induction along a finite linear order: from the minimum, one immediate
successor at a time. -/
theorem order_induction {P : A → Prop} (hmin : ∀ z : A, (∀ a : A, z ≤ a) → P z)
    (hstep : ∀ w z : A, w < z → (∀ a : A, ¬(w < a ∧ a < z)) → P w → P z) (z : A) : P z := by
  induction z using (Finite.to_wellFoundedLT (α := A)).induction with
  | _ z ih =>
    by_cases hz : ∀ a : A, z ≤ a
    · exact hmin z hz
    · obtain ⟨w, hwz, hnb⟩ := exists_succ_of_not_min hz
      exact hstep w z hwz hnb (ih w hwz)


-- @@ L150-164 verbatim
/-- In a finite linear order, an element that is not a maximum has an
immediate successor. -/
theorem exists_gt_of_not_max {z : A} (hz : ¬∀ a : A, a ≤ z) :
    ∃ w : A, z < w ∧ ∀ a : A, ¬(z < a ∧ a < w) := by
  classical
  have := Fintype.ofFinite A
  have hne : (Finset.univ.filter fun a : A => z < a).Nonempty := by
    push Not at hz
    obtain ⟨a, ha⟩ := hz
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩
  refine ⟨(Finset.univ.filter fun a : A => z < a).min' hne, ?_, ?_⟩
  · exact (Finset.mem_filter.mp ((Finset.univ.filter fun a : A => z < a).min'_mem hne)).2
  · rintro a ⟨hza, haw⟩
    exact absurd ((Finset.univ.filter fun a : A => z < a).min'_le
      a (Finset.mem_filter.mpr ⟨Finset.mem_univ a, hza⟩)) (not_le.mpr haw)


-- @@ L166-177 verbatim
/-- Induction along a finite linear order, downwards: from the maximum, one
immediate predecessor at a time. This is the direction a *scan* is proved
correct in – a walk that stops at the greatest element knows about the elements
above the one it stands on. -/
theorem order_induction_down {P : A → Prop} (hmax : ∀ z : A, (∀ a : A, a ≤ z) → P z)
    (hstep : ∀ w z : A, w < z → (∀ a : A, ¬(w < a ∧ a < z)) → P z → P w) (z : A) : P z := by
  induction z using (Finite.to_wellFoundedGT (α := A)).induction with
  | _ z ih =>
    by_cases hz : ∀ a : A, a ≤ z
    · exact hmax z hz
    · obtain ⟨w, hzw, hnb⟩ := exists_gt_of_not_max hz
      exact hstep z w hzw hnb (ih w hzw)


-- @@ L179-179 verbatim
end Pred


-- @@ L181-181 verbatim
/-! ### The lexicographic successor of a tuple, coordinatewise -/


-- @@ L183-183 verbatim
section TupSucc


-- @@ L185-185 verbatim
variable {D : ℕ} {A : Type} [LinearOrder A]


-- @@ L187-197 verbatim
/-- The tuple `t'` is the immediate successor of `t` in the lexicographic
order (most significant coordinate first), stated coordinatewise: the two
tuples agree before some position `p`, at `p` the second covers the first, and
after `p` the first is all maxima and the second all minima. This is the
condition the guard `DescriptiveComplexity.succTupF` realizes;
`DescriptiveComplexity.tupSucc_iff_covBy` identifies it with covering in
`Lex (Fin D → A)`. -/
def TupSucc (t t' : Fin D → A) : Prop :=
  ∃ p : Fin D, (∀ j, j < p → t j = t' j) ∧
    (t p < t' p ∧ ∀ a : A, ¬(t p < a ∧ a < t' p)) ∧
    ∀ j, p < j → (∀ a : A, a ≤ t j) ∧ (∀ a : A, t' j ≤ a)


-- @@ L199-199 verbatim
end TupSucc


-- @@ L201-201 verbatim
/-! ### Tuple guards, for the lexicographic order -/


-- @@ L203-203 verbatim
section TupGuards


-- @@ L205-205 verbatim
variable {D : ℕ} {L : Language.{0, 0}} {γ : Type}


-- @@ L207-210 verbatim
/-- The variables `sel` hold a lexicographically minimal tuple: every
coordinate is minimal. -/
noncomputable def minTupF (sel : Fin D → γ) : (L.sum Language.order).Formula γ :=
  listInf ((List.finRange D).map fun p => minF (sel p))


-- @@ L212-214 verbatim
/-- The variables `sel` hold a lexicographically maximal tuple. -/
noncomputable def maxTupF (sel : Fin D → γ) : (L.sum Language.order).Formula γ :=
  listInf ((List.finRange D).map fun p => maxF (sel p))


-- @@ L216-224 verbatim
/-- The tuple held by `sel'` is the immediate lexicographic successor of the
one held by `sel`. -/
noncomputable def succTupF (sel sel' : Fin D → γ) : (L.sum Language.order).Formula γ :=
  listSup ((List.finRange D).map fun p =>
    listInf (((List.finRange D).filter fun j => j < p).map fun j =>
      Term.equal (Term.var (sel j)) (Term.var (sel' j))) ⊓
    succF (sel p) (sel' p) ⊓
    listInf (((List.finRange D).filter fun j => p < j).map fun j =>
      maxF (sel j) ⊓ minF (sel' j)))


-- @@ L226-226 verbatim
variable {A : Type} [L.Structure A] [LinearOrder A] {v : γ → A}


-- @@ L228-238 verbatim
@[simp]
theorem realize_minTupF (sel : Fin D → γ) :
    (minTupF (L := L) sel).Realize v ↔ ∀ (p : Fin D) (a : A), v (sel p) ≤ a := by
  rw [minTupF, realize_listInf]
  constructor
  · intro h p
    have := h _ (List.mem_map.mpr ⟨p, List.mem_finRange p, rfl⟩)
    rwa [realize_minF] at this
  · rintro h φ hφ
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hφ
    exact (realize_minF _).mpr (h p)


-- @@ L240-250 verbatim
@[simp]
theorem realize_maxTupF (sel : Fin D → γ) :
    (maxTupF (L := L) sel).Realize v ↔ ∀ (p : Fin D) (a : A), a ≤ v (sel p) := by
  rw [maxTupF, realize_listInf]
  constructor
  · intro h p
    have := h _ (List.mem_map.mpr ⟨p, List.mem_finRange p, rfl⟩)
    rwa [realize_maxF] at this
  · rintro h φ hφ
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hφ
    exact (realize_maxF _).mpr (h p)


-- @@ L252-278 verbatim
theorem realize_succTupF (sel sel' : Fin D → γ) :
    (succTupF (L := L) sel sel').Realize v ↔ TupSucc (v ∘ sel) (v ∘ sel') := by
  rw [succTupF, realize_listSup]
  constructor
  · rintro ⟨φ, hφ, hr⟩
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hφ
    rw [Formula.realize_inf, Formula.realize_inf, realize_listInf, realize_listInf,
      realize_succF] at hr
    refine ⟨p, fun j hj => ?_, hr.1.2, fun j hj => ?_⟩
    · have := hr.1.1 _ (List.mem_map.mpr
        ⟨j, List.mem_filter.mpr ⟨List.mem_finRange j, by simpa using hj⟩, rfl⟩)
      rwa [Formula.realize_equal, Term.realize_var, Term.realize_var] at this
    · have := hr.2 _ (List.mem_map.mpr
        ⟨j, List.mem_filter.mpr ⟨List.mem_finRange j, by simpa using hj⟩, rfl⟩)
      rw [Formula.realize_inf, realize_maxF, realize_minF] at this
      exact this
  · rintro ⟨p, hbefore, hsucc, hafter⟩
    refine ⟨_, List.mem_map.mpr ⟨p, List.mem_finRange p, rfl⟩, ?_⟩
    rw [Formula.realize_inf, Formula.realize_inf, realize_listInf, realize_listInf,
      realize_succF]
    refine ⟨⟨fun φ hφ => ?_, hsucc⟩, fun φ hφ => ?_⟩
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hφ
      rw [Formula.realize_equal, Term.realize_var, Term.realize_var]
      exact hbefore j (by simpa using (List.mem_filter.mp hj).2)
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hφ
      rw [Formula.realize_inf, realize_maxF, realize_minF]
      exact hafter j (by simpa using (List.mem_filter.mp hj).2)


-- @@ L280-280 verbatim
end TupGuards


-- @@ L282-287 verbatim
/-! ### The bridge to `Lex`: bottom, top and covering, coordinatewise

The tuple guards above speak coordinatewise; the walk they describe is along
the finite linear order `Lex (Fin D → A)`. These lemmas identify the two
languages. (`Lex` is a type synonym, so `Finite` and `Nonempty` instances are
provided for it here.) -/


-- @@ L289-289 verbatim
section LexBridge


-- @@ L291-291 verbatim
instance {α : Type*} [Finite α] : Finite (Lex α) := Finite.of_equiv α toLex

-- @@ L292-292 verbatim
instance {α : Type*} [Nonempty α] : Nonempty (Lex α) := Nonempty.map toLex ‹_›


-- @@ L294-294 verbatim
variable {D : ℕ} {A : Type} [LinearOrder A]


-- @@ L296-298 verbatim
theorem lex_lt_iff {t t' : Fin D → A} :
    toLex t < toLex t' ↔ ∃ p, (∀ j, j < p → t j = t' j) ∧ t p < t' p :=
  Iff.rfl


-- @@ L300-327 verbatim
/-- A tuple is a lexicographic bottom iff each coordinate is minimal. -/
theorem tup_isBot_iff {t : Fin D → A} :
    (∀ u : Lex (Fin D → A), toLex t ≤ u) ↔ ∀ (p : Fin D) (a : A), t p ≤ a := by
  classical
  constructor
  · intro h p a
    by_contra hlt
    push Not at hlt
    have := h (toLex (Function.update t p a))
    rcases this.lt_or_eq with hl | he
    · obtain ⟨q, hq, hql⟩ := lex_lt_iff.mp hl
      rcases lt_trichotomy q p with h' | h' | h'
      · rw [Function.update_of_ne (ne_of_lt h')] at hql
        exact absurd hql (lt_irrefl _)
      · rw [h', Function.update_self] at hql
        exact absurd hql (not_lt.mpr hlt.le)
      · have := hq p h'
        rw [Function.update_self] at this
        exact absurd this (ne_of_gt hlt)
    -- the update is strictly below `t`, so equality is impossible too
    · have := congrFun (toLex_inj.mp he) p
      rw [Function.update_self] at this
      exact absurd this (ne_of_gt hlt)
  · intro h u
    by_contra hlt
    push Not at hlt
    obtain ⟨q, hq, hql⟩ := (lex_lt_iff (t := ofLex u) (t' := t)).mp hlt
    exact absurd hql (not_lt.mpr (h q _))


-- @@ L329-355 verbatim
/-- A tuple is a lexicographic top iff each coordinate is maximal. -/
theorem tup_isTop_iff {t : Fin D → A} :
    (∀ u : Lex (Fin D → A), u ≤ toLex t) ↔ ∀ (p : Fin D) (a : A), a ≤ t p := by
  classical
  constructor
  · intro h p a
    by_contra hlt
    push Not at hlt
    have := h (toLex (Function.update t p a))
    rcases this.lt_or_eq with hl | he
    · obtain ⟨q, hq, hql⟩ := lex_lt_iff.mp hl
      rcases lt_trichotomy q p with h' | h' | h'
      · rw [Function.update_of_ne (ne_of_lt h')] at hql
        exact absurd hql (lt_irrefl _)
      · rw [h', Function.update_self] at hql
        exact absurd hql (not_lt.mpr hlt.le)
      · have := hq p h'
        rw [Function.update_self] at this
        exact absurd this (ne_of_gt hlt)
    · have := congrFun (toLex_inj.mp he) p
      rw [Function.update_self] at this
      exact absurd this (ne_of_gt hlt)
  · intro h u
    by_contra hlt
    push Not at hlt
    obtain ⟨q, hq, hql⟩ := (lex_lt_iff (t := t) (t' := ofLex u)).mp hlt
    exact absurd hql (not_lt.mpr (h q _))


-- @@ L357-417 verbatim
/-- **Coordinatewise successors are lexicographic covers**: the condition of
the guard `DescriptiveComplexity.succTupF` says exactly that the second tuple covers
the first in `Lex (Fin D → A)`. -/
theorem tupSucc_iff_covBy {t t' : Fin D → A} :
    TupSucc t t' ↔ toLex t ⋖ toLex t' := by
  classical
  constructor
  · rintro ⟨p, hbefore, ⟨hplt, hpnb⟩, hafter⟩
    refine ⟨lex_lt_iff.mpr ⟨p, hbefore, hplt⟩, ?_⟩
    rintro u htu hut
    obtain ⟨i₁, h₁e, h₁l⟩ := (lex_lt_iff (t := t) (t' := ofLex u)).mp htu
    obtain ⟨i₂, h₂e, h₂l⟩ := (lex_lt_iff (t := ofLex u) (t' := t')).mp hut
    rcases lt_trichotomy i₁ p with hip | hip | hip
    · rcases lt_trichotomy i₂ i₁ with hii | hii | hii
      · rw [← h₁e _ hii, ← hbefore _ (hii.trans hip)] at h₂l
        exact absurd h₂l (lt_irrefl _)
      · rw [hii, ← hbefore _ hip] at h₂l
        exact absurd (h₁l.trans h₂l) (lt_irrefl _)
      · rw [h₂e _ hii, ← hbefore _ hip] at h₁l
        exact absurd h₁l (lt_irrefl _)
    · rw [hip] at h₁e h₁l
      rcases lt_trichotomy i₂ p with hii | hii | hii
      · rw [← h₁e _ hii, ← hbefore _ hii] at h₂l
        exact absurd h₂l (lt_irrefl _)
      · rw [hii] at h₂l
        exact hpnb _ ⟨h₁l, h₂l⟩
      · exact absurd h₂l (not_lt.mpr ((hafter _ hii).2 _))
    · exact absurd h₁l (not_lt.mpr ((hafter _ hip).1 _))
  · rintro ⟨hlt, hnb⟩
    obtain ⟨p, hbefore, hpl⟩ := lex_lt_iff.mp hlt
    refine ⟨p, hbefore, ⟨hpl, fun b hb => ?_⟩, fun j hj => ⟨fun a => ?_, fun a => ?_⟩⟩
    · have h1 : toLex t < toLex (Function.update t p b) :=
        lex_lt_iff.mpr ⟨p, fun j hj => by rw [Function.update_of_ne (ne_of_lt hj)],
          by rw [Function.update_self]; exact hb.1⟩
      have h2 : toLex (Function.update t p b) < toLex t' :=
        lex_lt_iff.mpr ⟨p,
          fun j hj => by rw [Function.update_of_ne (ne_of_lt hj)]; exact hbefore j hj,
          by rw [Function.update_self]; exact hb.2⟩
      exact hnb h1 h2
    · by_contra hlt'
      push Not at hlt'
      have h1 : toLex t < toLex (Function.update t j a) :=
        lex_lt_iff.mpr ⟨j, fun i hi => by rw [Function.update_of_ne (ne_of_lt hi)],
          by rw [Function.update_self]; exact hlt'⟩
      have h2 : toLex (Function.update t j a) < toLex t' :=
        lex_lt_iff.mpr ⟨p,
          fun i hi => by
            rw [Function.update_of_ne (ne_of_lt (hi.trans hj))]; exact hbefore i hi,
          by rw [Function.update_of_ne (ne_of_lt hj)]; exact hpl⟩
      exact hnb h1 h2
    · by_contra hlt'
      push Not at hlt'
      have h1 : toLex t < toLex (Function.update t' j a) :=
        lex_lt_iff.mpr ⟨p,
          fun i hi => by
            rw [Function.update_of_ne (ne_of_lt (hi.trans hj))]; exact hbefore i hi,
          by rw [Function.update_of_ne (ne_of_lt hj)]; exact hpl⟩
      have h2 : toLex (Function.update t' j a) < toLex t' :=
        lex_lt_iff.mpr ⟨j, fun i hi => by rw [Function.update_of_ne (ne_of_lt hi)],
          by rw [Function.update_self]; exact hlt'⟩
      exact hnb h1 h2


-- @@ L419-419 verbatim
/-! #### The lexicographic product with a static head -/


-- @@ L421-421 verbatim
variable {J B : Type} [LinearOrder J] [LinearOrder B]


-- @@ L423-425 verbatim
theorem prodLex_le_iff {a a' : J} {b b' : B} :
    toLex (a, b) ≤ toLex (a', b') ↔ a < a' ∨ a = a' ∧ b ≤ b' :=
  Prod.Lex.toLex_le_toLex


-- @@ L427-429 verbatim
theorem prodLex_lt_iff {a a' : J} {b b' : B} :
    toLex (a, b) < toLex (a', b') ↔ a < a' ∨ a = a' ∧ b < b' :=
  Prod.Lex.toLex_lt_toLex


-- @@ L431-447 verbatim
theorem prodLex_isBot_iff {a : J} {b : B} :
    (∀ u : J ×ₗ B, toLex (a, b) ≤ u) ↔ (∀ x : J, a ≤ x) ∧ ∀ y : B, b ≤ y := by
  constructor
  · intro h
    refine ⟨fun x => ?_, fun y => ?_⟩
    · rcases prodLex_le_iff.mp (h (toLex (x, b))) with hl | ⟨he, -⟩
      · exact hl.le
      · exact he.le
    · rcases prodLex_le_iff.mp (h (toLex (a, y))) with hl | ⟨-, hy⟩
      · exact absurd hl (lt_irrefl _)
      · exact hy
  · rintro ⟨ha, hb⟩ u
    have : toLex (a, b) ≤ toLex (ofLex u) := by
      rcases eq_or_lt_of_le (ha (ofLex u).1) with he | hl
      · exact prodLex_le_iff.mpr (Or.inr ⟨he, hb _⟩)
      · exact prodLex_le_iff.mpr (Or.inl hl)
    exact this


-- @@ L449-465 verbatim
theorem prodLex_isTop_iff {a : J} {b : B} :
    (∀ u : J ×ₗ B, u ≤ toLex (a, b)) ↔ (∀ x : J, x ≤ a) ∧ ∀ y : B, y ≤ b := by
  constructor
  · intro h
    refine ⟨fun x => ?_, fun y => ?_⟩
    · rcases prodLex_le_iff.mp (h (toLex (x, b))) with hl | ⟨he, -⟩
      · exact hl.le
      · exact he.le
    · rcases prodLex_le_iff.mp (h (toLex (a, y))) with hl | ⟨-, hy⟩
      · exact absurd hl (lt_irrefl _)
      · exact hy
  · rintro ⟨ha, hb⟩ u
    have : toLex (ofLex u) ≤ toLex (a, b) := by
      rcases eq_or_lt_of_le (ha (ofLex u).1) with he | hl
      · exact prodLex_le_iff.mpr (Or.inr ⟨he, hb _⟩)
      · exact prodLex_le_iff.mpr (Or.inl hl)
    exact this


-- @@ L467-516 verbatim
/-- Covering in a lexicographic product: either the heads agree and the tails
cover, or the heads cover, the first tail is a top and the second a bottom. -/
theorem prodLex_covBy_iff [Nonempty B] {a a' : J} {b b' : B} :
    toLex (a, b) ⋖ toLex (a', b') ↔
      (a = a' ∧ b ⋖ b') ∨
        (a ⋖ a' ∧ (∀ y : B, y ≤ b) ∧ ∀ y : B, b' ≤ y) := by
  constructor
  · rintro ⟨hlt, hnb⟩
    rcases prodLex_lt_iff.mp hlt with hl | ⟨he, hb⟩
    · refine Or.inr ⟨⟨hl, fun c hac hca' => ?_⟩, fun y => ?_, fun y => ?_⟩
      · obtain ⟨y⟩ := ‹Nonempty B›
        have h1 : toLex (a, b) < toLex (c, y) := prodLex_lt_iff.mpr (Or.inl hac)
        have h2 : toLex (c, y) < toLex (a', b') := prodLex_lt_iff.mpr (Or.inl hca')
        exact hnb h1 h2
      · by_contra hy
        push Not at hy
        have h1 : toLex (a, b) < toLex (a, y) := prodLex_lt_iff.mpr (Or.inr ⟨rfl, hy⟩)
        have h2 : toLex (a, y) < toLex (a', b') := prodLex_lt_iff.mpr (Or.inl hl)
        exact hnb h1 h2
      · by_contra hy
        push Not at hy
        have h1 : toLex (a, b) < toLex (a', y) := prodLex_lt_iff.mpr (Or.inl hl)
        have h2 : toLex (a', y) < toLex (a', b') := prodLex_lt_iff.mpr (Or.inr ⟨rfl, hy⟩)
        exact hnb h1 h2
    · refine Or.inl ⟨he, hb, fun d hbd hdb' => ?_⟩
      have h1 : toLex (a, b) < toLex (a, d) := prodLex_lt_iff.mpr (Or.inr ⟨rfl, hbd⟩)
      have h2 : toLex (a, d) < toLex (a', b') := prodLex_lt_iff.mpr (Or.inr ⟨he, hdb'⟩)
      exact hnb h1 h2
  · rintro (⟨he, hbcov⟩ | ⟨hacov, htop, hbot⟩)
    · obtain ⟨hblt, hbnb⟩ := hbcov
      refine ⟨prodLex_lt_iff.mpr (Or.inr ⟨he, hblt⟩), ?_⟩
      rintro u h₁ h₂
      rcases (prodLex_lt_iff (a := a) (b := b) (a' := (ofLex u).1) (b' := (ofLex u).2)).mp h₁
        with hl₁ | ⟨he₁, hb₁⟩ <;>
        rcases (prodLex_lt_iff (a := (ofLex u).1) (b := (ofLex u).2) (a' := a')
          (b' := b')).mp h₂ with hl₂ | ⟨he₂, hb₂⟩
      · exact absurd (he ▸ hl₁.trans hl₂) (lt_irrefl _)
      · exact absurd (he ▸ he₂ ▸ hl₁) (lt_irrefl _)
      · exact absurd (he ▸ he₁ ▸ hl₂) (lt_irrefl _)
      · exact hbnb hb₁ hb₂
    · obtain ⟨halt, hanb⟩ := hacov
      refine ⟨prodLex_lt_iff.mpr (Or.inl halt), ?_⟩
      rintro u h₁ h₂
      rcases (prodLex_lt_iff (a := a) (b := b) (a' := (ofLex u).1) (b' := (ofLex u).2)).mp h₁
        with hl₁ | ⟨he₁, hb₁⟩
      · rcases (prodLex_lt_iff (a := (ofLex u).1) (b := (ofLex u).2) (a' := a')
          (b' := b')).mp h₂ with hl₂ | ⟨he₂, hb₂⟩
        · exact hanb hl₁ hl₂
        · exact absurd hb₂ (not_lt.mpr (hbot _))
      · exact absurd hb₁ (not_lt.mpr (htop _))


-- @@ L518-531 verbatim
/-- Covering in `Fin n` is incrementing the value. -/
theorem finCovBy_iff {n : ℕ} {j j' : Fin n} : j ⋖ j' ↔ (j : ℕ) + 1 = (j' : ℕ) := by
  constructor
  · rintro ⟨hlt, hnb⟩
    have hv : (j : ℕ) < (j' : ℕ) := hlt
    by_contra hne
    have hlt2 : (j : ℕ) + 1 < (j' : ℕ) := by omega
    have h1 : j < ⟨(j : ℕ) + 1, hlt2.trans j'.isLt⟩ := Fin.lt_def.mpr (Nat.lt_succ_self _)
    have h2 : (⟨(j : ℕ) + 1, hlt2.trans j'.isLt⟩ : Fin n) < j' := Fin.lt_def.mpr hlt2
    exact hnb h1 h2
  · intro h
    refine ⟨Fin.lt_def.mpr (by omega), fun c hjc hcj' => ?_⟩
    rw [Fin.lt_def] at hjc hcj'
    omega


-- @@ L533-533 verbatim
end LexBridge


-- @@ L535-542 verbatim
/-! ### Deciding the lexicographic order of two tuples

`DescriptiveComplexity.succTupF` *walks* the lexicographic order; the two
guards below *decide* it, which is what a reduction defining the order of its
image has to do. They are stated at arbitrary selectors `sel`, `sel'` into a
shared variable type, rather than at the fixed layout `Fin 2 × Fin D` of
`DescriptiveComplexity.lexTupleLeF`, because their consumers compare tuples
sitting at arbitrary positions among the free variables. -/


-- @@ L544-544 verbatim
section LexDecide


-- @@ L546-546 verbatim
variable {D : ℕ} {L : Language.{0, 0}} {γ : Type}


-- @@ L548-555 verbatim
/-- The tuple held by `sel` is lexicographically strictly below the one held by
`sel'`: the two agree before some coordinate, at which the first is strictly
smaller. -/
noncomputable def lexSelLtF (sel sel' : Fin D → γ) : (L.sum Language.order).Formula γ :=
  listSup ((List.finRange D).map fun p =>
    listInf (((List.finRange D).filter fun j => j < p).map fun j =>
      Term.equal (Term.var (sel j)) (Term.var (sel' j))) ⊓
    ltF (sel p) (sel' p))


-- @@ L557-562 verbatim
/-- The tuple held by `sel` is lexicographically below or equal to the one held
by `sel'`. -/
noncomputable def lexSelLeF (sel sel' : Fin D → γ) : (L.sum Language.order).Formula γ :=
  lexSelLtF sel sel' ⊔
    listInf ((List.finRange D).map fun j =>
      Term.equal (Term.var (sel j)) (Term.var (sel' j)))


-- @@ L564-564 verbatim
variable {A : Type} [L.Structure A] [LinearOrder A] {v : γ → A}


-- @@ L566-584 verbatim
@[simp]
theorem realize_lexSelLtF (sel sel' : Fin D → γ) :
    (lexSelLtF (L := L) sel sel').Realize v ↔ toLex (v ∘ sel) < toLex (v ∘ sel') := by
  rw [lexSelLtF, realize_listSup, lex_lt_iff]
  constructor
  · rintro ⟨φ, hφ, hr⟩
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hφ
    rw [Formula.realize_inf, realize_listInf, realize_ltF] at hr
    refine ⟨p, fun j hj => ?_, hr.2⟩
    have := hr.1 _ (List.mem_map.mpr
      ⟨j, List.mem_filter.mpr ⟨List.mem_finRange j, by simpa using hj⟩, rfl⟩)
    rwa [Formula.realize_equal, Term.realize_var, Term.realize_var] at this
  · rintro ⟨p, hag, hp⟩
    refine ⟨_, List.mem_map.mpr ⟨p, List.mem_finRange p, rfl⟩, ?_⟩
    rw [Formula.realize_inf, realize_listInf, realize_ltF]
    refine ⟨fun φ hφ => ?_, hp⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hφ
    rw [Formula.realize_equal, Term.realize_var, Term.realize_var]
    exact hag j (by simpa using (List.mem_filter.mp hj).2)


-- @@ L586-599 verbatim
@[simp]
theorem realize_lexSelLeF (sel sel' : Fin D → γ) :
    (lexSelLeF (L := L) sel sel').Realize v ↔ toLex (v ∘ sel) ≤ toLex (v ∘ sel') := by
  rw [lexSelLeF, Formula.realize_sup, realize_lexSelLtF, realize_listInf, le_iff_lt_or_eq]
  refine or_congr Iff.rfl ?_
  constructor
  · intro h
    refine funext fun j => ?_
    have := h _ (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
    rwa [Formula.realize_equal, Term.realize_var, Term.realize_var] at this
  · intro h φ hφ
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hφ
    rw [Formula.realize_equal, Term.realize_var, Term.realize_var]
    exact congrFun h j


-- @@ L601-601 verbatim
end LexDecide


-- @@ L603-603 verbatim
/-! ### Reaching an element from below a cover -/


-- @@ L605-605 verbatim
section CovByCases


-- @@ L607-607 verbatim
variable {α : Type*} [LinearOrder α]


-- @@ L609-613 verbatim
/-- Whatever is below a cover is below its base, or is the cover itself. -/
theorem covBy_le_cases {a b c : α} (h : a ⋖ b) (hc : c ≤ b) : c ≤ a ∨ c = b := by
  rcases lt_or_eq_of_le hc with hlt | he
  · exact Or.inl ((covBy_iff_lt_iff_le_left.mp h).mp hlt)
  · exact Or.inr he


-- @@ L615-615 verbatim
end CovByCases


-- @@ L617-617 verbatim
/-! ### The rank of an element of a finite linear order -/


-- @@ L619-619 verbatim
section Rank


-- @@ L621-621 verbatim
variable {A : Type} [LinearOrder A]


-- @@ L623-628 verbatim
/-- The rank of an element of a finite linear order: the number of its strict
predecessors. This converts a walk along covers into arithmetic, matching
tuple-indexed fixed-point stages with the `ℕ`-indexed
`DescriptiveComplexity.derivesIn`. -/
noncomputable def orank (z : A) : ℕ :=
  {y : A | y < z}.ncard


-- @@ L630-637 verbatim
/-- A minimum has rank `0`. -/
theorem orank_eq_zero {z : A} (hz : ∀ a : A, z ≤ a) : orank z = 0 := by
  rw [orank]
  have : {y : A | y < z} = ∅ := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    exact hz y
  simp [this]


-- @@ L639-639 verbatim
variable [Finite A]


-- @@ L641-649 verbatim
/-- Rank increases by one along a cover. -/
theorem orank_covBy {w z : A} (h : w ⋖ z) : orank z = orank w + 1 := by
  rw [orank, orank]
  have hset : {y : A | y < z} = insert w {y : A | y < w} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff]
    rw [covBy_iff_lt_iff_le_left.mp h]
    exact le_iff_eq_or_lt
  rw [hset, Set.ncard_insert_of_notMem (by simp)]


-- @@ L651-653 verbatim
/-- Rank is monotone. -/
theorem orank_le_orank {x y : A} (h : x ≤ y) : orank x ≤ orank y :=
  Set.ncard_le_ncard (fun _ hz => lt_of_lt_of_le hz h) (Set.toFinite _)


-- @@ L655-658 verbatim
/-- Rank is strictly monotone. -/
theorem orank_lt_orank {x y : A} (h : x < y) : orank x < orank y :=
  Set.ncard_lt_ncard ⟨fun _ hz => lt_trans hz h, fun hsup => lt_irrefl x (hsup h)⟩
    (Set.toFinite _)


-- @@ L660-666 verbatim
/-- **Rank reflects the order**: it is an order isomorphism onto an initial
segment of `ℕ`, which is what lets a walk along the order be replayed as
arithmetic. -/
theorem orank_le_iff {x y : A} : orank x ≤ orank y ↔ x ≤ y := by
  refine ⟨fun h => ?_, orank_le_orank⟩
  by_contra hxy
  exact absurd (orank_lt_orank (lt_of_not_ge hxy)) (by omega)


-- @@ L668-670 verbatim
/-- Rank tells elements apart. -/
theorem orank_inj_iff {x y : A} : orank x = orank y ↔ x = y :=
  ⟨fun h => le_antisymm (orank_le_iff.mp h.le) (orank_le_iff.mp h.ge), fun h => h ▸ rfl⟩


-- @@ L672-674 verbatim
/-- The rank determines the element. -/
theorem orank_inj {x y : A} (h : orank x = orank y) : x = y :=
  orank_inj_iff.mp h


-- @@ L676-684 verbatim
/-- Rank is below the cardinality. -/
theorem orank_lt_card (x : A) : orank x < Nat.card A := by
  have hsub : {y : A | y < x} ⊆ {x}ᶜ := fun _ hy => ne_of_lt hy
  have hle : orank x ≤ Nat.card A - 1 := by
    rw [orank]
    calc {y : A | y < x}.ncard ≤ ({x}ᶜ : Set A).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = Nat.card A - 1 := by rw [Set.ncard_compl, Set.ncard_singleton]
  have hpos : 0 < Nat.card A := Nat.card_pos_iff.mpr ⟨⟨x⟩, ‹Finite A›⟩
  omega


-- @@ L686-698 verbatim
/-- **Every position below the cardinality is a rank**: the ranks exhaust the
initial segment, by injectivity between two finite types of the same size. -/
theorem exists_orank_eq {m : ℕ} (h : m < Nat.card A) : ∃ x : A, orank x = m := by
  classical
  let := Fintype.ofFinite A
  have hcard : Fintype.card A = Fintype.card (Fin (Nat.card A)) := by
    rw [Fintype.card_fin, Nat.card_eq_fintype_card]
  have hbij : Function.Bijective
      (fun x : A => (⟨orank x, orank_lt_card x⟩ : Fin (Nat.card A))) :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun x y hxy => orank_inj_iff.mp (congrArg Fin.val hxy), hcard⟩
  obtain ⟨x, hx⟩ := hbij.2 ⟨m, h⟩
  exact ⟨x, congrArg Fin.val hx⟩


-- @@ L700-707 verbatim
/-- A maximum has rank `Nat.card A - 1`. -/
theorem orank_isTop {z : A} (hz : ∀ a : A, a ≤ z) : orank z = Nat.card A - 1 := by
  rw [orank]
  have hset : {y : A | y < z} = {z}ᶜ := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ⟨ne_of_lt, fun h => lt_of_le_of_ne (hz y) h⟩
  rw [hset, Set.ncard_compl, Set.ncard_singleton]


-- @@ L709-709 verbatim
end Rank


-- @@ L711-711 verbatim
end DescriptiveComplexity
