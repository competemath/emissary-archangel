/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Qsat.Prefix


-- @@ L8-32 verbatim
/-!
# The levels of the Savitch recursion, and what a valuation reads

Two independent pieces of bookkeeping for the correctness proof.

## Levels

Levels are the state variables of the input, in the ambient order: the first one
(`DescriptiveComplexity.IsMinSV`) carries the two endpoints of the walk, the last
one (`DescriptiveComplexity.IsMaxSV`) the base case, and each other level receives
its pair from the level just above (`DescriptiveComplexity.IsPredSV`). Those three
notions exist and are unique on a finite order, and
`DescriptiveComplexity.svAbove` – the number of levels from a given one down to the
last – decreases by one at each step, starting from
`DescriptiveComplexity.stateDepth` at the first level and ending at `1`. That is
the depth of `DescriptiveComplexity.SavPow` the level computes.

## What a valuation reads

A valuation of the constructed instance is a predicate on its elements; the
correctness proof only ever reads it through the ten projections below
(`DescriptiveComplexity.stS`, `DescriptiveComplexity.stU`,
`DescriptiveComplexity.bitB`, `DescriptiveComplexity.valP`…), one per variable tag,
which turn it back into the states, bits and valuations the reduction means.
-/


-- @@ L34-34 verbatim
namespace DescriptiveComplexity


-- @@ L36-36 verbatim
open FirstOrder


-- @@ L38-38 verbatim
open Language Structure


-- @@ L40-40 verbatim
/-! ### The minimum of the input order -/


-- @@ L42-42 verbatim
section Bot


-- @@ L44-44 verbatim
variable (A : Type) [LinearOrder A] [Finite A] [Nonempty A]


-- @@ L46-48 verbatim
/-- The minimum of the input order: the padding of the coordinates a tag does
not use. -/
noncomputable def qBot : A := (Finite.exists_min (id : A → A)).choose


-- @@ L50-50 verbatim
theorem isBot_qBot : IsBot (qBot A) := (Finite.exists_min (id : A → A)).choose_spec


-- @@ L52-52 verbatim
variable {A}


-- @@ L54-55 verbatim
theorem eq_qBot {q : A} (h : IsBot q) : q = qBot A :=
  le_antisymm (h _) (isBot_qBot A q)


-- @@ L57-59 verbatim
@[simp]
theorem isBot_iff_eq_qBot {q : A} : IsBot q ↔ q = qBot A :=
  ⟨eq_qBot, fun h => h ▸ isBot_qBot A⟩


-- @@ L61-61 verbatim
end Bot


-- @@ L63-63 verbatim
/-! ### The levels -/


-- @@ L65-65 verbatim
section Levels


-- @@ L67-67 verbatim
variable {A : Type} [Language.transSys.Structure A] [LinearOrder A] [Finite A]


-- @@ L69-70 verbatim
omit [Finite A] in
theorem IsMinSV.isSV {ℓ : A} (h : IsMinSV ℓ) : IsSV ℓ := h.1


-- @@ L72-73 verbatim
omit [Finite A] in
theorem IsMaxSV.isSV {ℓ : A} (h : IsMaxSV ℓ) : IsSV ℓ := h.1


-- @@ L75-77 verbatim
omit [Finite A] in
theorem IsMinSV.le {ℓ z : A} (h : IsMinSV ℓ) (hz : IsSV z) : ℓ ≤ z :=
  not_lt.mp (h.2 z hz)


-- @@ L79-81 verbatim
omit [Finite A] in
theorem IsMaxSV.le {ℓ z : A} (h : IsMaxSV ℓ) (hz : IsSV z) : z ≤ ℓ :=
  not_lt.mp (h.2 z hz)


-- @@ L83-85 verbatim
omit [Finite A] in
theorem isMaxSV_unique {ℓ ℓ' : A} (h : IsMaxSV ℓ) (h' : IsMaxSV ℓ') : ℓ = ℓ' :=
  le_antisymm (h'.le h.isSV) (h.le h'.isSV)


-- @@ L87-92 verbatim
omit [Finite A] in
theorem isPredSV_unique {d d' ℓ : A} (h : IsPredSV d ℓ) (h' : IsPredSV d' ℓ) : d = d' := by
  rcases lt_trichotomy d d' with hlt | heq | hlt
  · exact absurd ⟨hlt, h'.2.2.1⟩ (h.2.2.2 d' h'.1)
  · exact heq
  · exact absurd ⟨hlt, h.2.2.1⟩ (h'.2.2.2 d h.1)


-- @@ L94-97 verbatim
theorem exists_isMinSV {x : A} (hx : IsSV x) : ∃ ℓ : A, IsMinSV ℓ := by
  have : Nonempty {z : A // IsSV z} := ⟨⟨x, hx⟩⟩
  obtain ⟨m, hm⟩ := Finite.exists_min (fun z : {z : A // IsSV z} => (z : A))
  exact ⟨m, m.2, fun z hz hlt => absurd (hm ⟨z, hz⟩) (not_le.mpr hlt)⟩


-- @@ L99-102 verbatim
theorem exists_isMaxSV {x : A} (hx : IsSV x) : ∃ ℓ : A, IsMaxSV ℓ := by
  have : Nonempty {z : A // IsSV z} := ⟨⟨x, hx⟩⟩
  obtain ⟨m, hm⟩ := Finite.exists_max (fun z : {z : A // IsSV z} => (z : A))
  exact ⟨m, m.2, fun z hz hlt => absurd (hm ⟨z, hz⟩) (not_le.mpr hlt)⟩


-- @@ L104-111 verbatim
theorem exists_isPredSV {ℓ : A} (hℓ : IsSV ℓ) (hmin : ¬IsMinSV ℓ) : ∃ d : A, IsPredSV d ℓ := by
  obtain ⟨x, hx, hlt⟩ : ∃ x : A, IsSV x ∧ x < ℓ := by
    by_contra hcon
    exact hmin ⟨hℓ, fun z hz hzl => hcon ⟨z, hz, hzl⟩⟩
  have : Nonempty {z : A // IsSV z ∧ z < ℓ} := ⟨⟨x, hx, hlt⟩⟩
  obtain ⟨d, hd⟩ := Finite.exists_max (fun z : {z : A // IsSV z ∧ z < ℓ} => (z : A))
  refine ⟨d, d.2.1, hℓ, d.2.2, fun z hz hzz => ?_⟩
  exact absurd (hd ⟨z, hz, hzz.2⟩) (not_le.mpr hzz.1)


-- @@ L113-115 verbatim
omit [Finite A] in
theorem IsPredSV.not_isMinSV {d ℓ : A} (h : IsPredSV d ℓ) : ¬IsMinSV ℓ :=
  fun hmin => absurd (hmin.le h.1) (not_le.mpr h.2.2.1)


-- @@ L117-119 verbatim
/-- The number of levels from `ℓ` down to the last one: the depth of the Savitch
recursion that level `ℓ` still has to unfold. -/
noncomputable def svAbove (ℓ : A) : ℕ := Set.ncard {z : A | IsSV z ∧ ℓ ≤ z}


-- @@ L121-128 verbatim
omit [Finite A] in
theorem svAbove_of_isMaxSV {ℓ : A} (h : IsMaxSV ℓ) : svAbove ℓ = 1 := by
  have hset : {z : A | IsSV z ∧ ℓ ≤ z} = {ℓ} := by
    ext z
    refine ⟨fun ⟨hz, hle⟩ => le_antisymm (h.le hz) hle, ?_⟩
    rintro rfl
    exact ⟨h.isSV, le_rfl⟩
  rw [svAbove, hset, Set.ncard_singleton]


-- @@ L130-144 verbatim
theorem svAbove_of_isPredSV {d ℓ : A} (h : IsPredSV d ℓ) : svAbove d = svAbove ℓ + 1 := by
  have hset : {z : A | IsSV z ∧ d ≤ z} = insert d {z : A | IsSV z ∧ ℓ ≤ z} := by
    ext z
    constructor
    · rintro ⟨hz, hle⟩
      rcases hle.lt_or_eq with hlt | heq
      · refine Or.inr ⟨hz, ?_⟩
        by_contra hcon
        exact h.2.2.2 z hz ⟨hlt, not_le.mp hcon⟩
      · exact Or.inl heq.symm
    · rintro (rfl | ⟨hz, hle⟩)
      · exact ⟨h.1, le_rfl⟩
      · exact ⟨hz, h.2.2.1.le.trans hle⟩
  have hnot : d ∉ {z : A | IsSV z ∧ ℓ ≤ z} := fun hd => absurd hd.2 (not_le.mpr h.2.2.1)
  rw [svAbove, hset, Set.ncard_insert_of_notMem hnot (Set.toFinite _), svAbove]


-- @@ L146-152 verbatim
omit [Finite A] in
theorem svAbove_of_isMinSV {ℓ : A} (h : IsMinSV ℓ) : svAbove ℓ = stateDepth A := by
  have hset : {z : A | IsSV z ∧ ℓ ≤ z} = {z : A | IsSV z} := by
    ext z
    exact ⟨fun hz => hz.1, fun hz => ⟨hz, h.le hz⟩⟩
  rw [svAbove, hset, stateDepth, ← Nat.card_coe_set_eq]
  rfl


-- @@ L154-161 verbatim
theorem exists_isSuccSV {ℓ : A} (hℓ : IsSV ℓ) (hmax : ¬IsMaxSV ℓ) : ∃ ℓ' : A, IsPredSV ℓ ℓ' := by
  obtain ⟨x, hx, hlt⟩ : ∃ x : A, IsSV x ∧ ℓ < x := by
    by_contra hcon
    exact hmax ⟨hℓ, fun z hz hzl => hcon ⟨z, hz, hzl⟩⟩
  have : Nonempty {z : A // IsSV z ∧ ℓ < z} := ⟨⟨x, hx, hlt⟩⟩
  obtain ⟨e, he⟩ := Finite.exists_min (fun z : {z : A // IsSV z ∧ ℓ < z} => (z : A))
  refine ⟨e, hℓ, e.2.1, e.2.2, fun z hz hzz => ?_⟩
  exact absurd (he ⟨z, hz, hzz.1⟩) (not_le.mpr hzz.2)


-- @@ L163-164 verbatim
theorem svAbove_pos {ℓ : A} (hℓ : IsSV ℓ) : 0 < svAbove ℓ := by
  refine Set.ncard_pos (Set.toFinite _) |>.mpr ⟨ℓ, hℓ, le_rfl⟩


-- @@ L166-166 verbatim
end Levels


-- @@ L168-168 verbatim
/-! ### What a valuation reads -/


-- @@ L170-170 verbatim
section Readouts


-- @@ L172-172 verbatim
variable {A : Type} [Language.transSys.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

-- @@ L173-173 verbatim
variable (σ : QM A → Prop)


-- @@ L175-176 verbatim
/-- The source endpoint of the walk, as read by a valuation. -/
def stS : A → Prop := fun a => σ (qVar .sS a (qBot A))


-- @@ L178-179 verbatim
/-- The target endpoint of the walk, as read by a valuation. -/
def stT : A → Prop := fun a => σ (qVar .sT a (qBot A))


-- @@ L181-182 verbatim
/-- The midpoint guessed at a level, as read by a valuation. -/
def stZ (ℓ : A) : A → Prop := fun a => σ (qVar .sZ ℓ a)


-- @@ L184-185 verbatim
/-- The first component of the pair passed below a level. -/
def stU (ℓ : A) : A → Prop := fun a => σ (qVar .sU ℓ a)


-- @@ L187-188 verbatim
/-- The second component of the pair passed below a level. -/
def stV (ℓ : A) : A → Prop := fun a => σ (qVar .sV ℓ a)


-- @@ L190-191 verbatim
/-- The universal bit of a level. -/
def bitB (ℓ : A) : Prop := σ (qVar .sB ℓ (qBot A))


-- @@ L193-194 verbatim
/-- The valuation satisfying the source clauses. -/
def valS : A → Prop := fun a => σ (qVar .aS a (qBot A))


-- @@ L196-197 verbatim
/-- The valuation satisfying the target clauses. -/
def valT : A → Prop := fun a => σ (qVar .aT a (qBot A))


-- @@ L199-200 verbatim
/-- The valuation satisfying the transition clauses. -/
def valP : A → Prop := fun a => σ (qVar .aP a (qBot A))


-- @@ L202-203 verbatim
/-- The bit saying that the base case is an equality rather than a step. -/
def bitE : Prop := σ (qVar .sE (qBot A) (qBot A))


-- @@ L205-205 verbatim
end Readouts


-- @@ L207-207 verbatim
end DescriptiveComplexity
