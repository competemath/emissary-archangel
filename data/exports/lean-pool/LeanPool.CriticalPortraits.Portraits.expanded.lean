/-
Copyright (c) 2026 Keston Aquino-Michaels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keston Aquino-Michaels
-/
module

public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.PUnit
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Finset


-- @@ L18-41 verbatim
/-!
# Geometric foundation: the critical-portrait model on `ZMod (d*m)`.

A faithful, proof-friendly port of the bare-Lean verified model
(`LamKit.CriticalCensusGeneral`; native_decide-verified `d = 3..6`).  Mathlib has cyclic
betweenness (`Order.Circular`) but no chords/linking/laminar API, so this is built from scratch.

* `IsCriticalSet`        — subset of one `σ_d`-fiber, `≥ 2` points (weight `|S| - 1`).
* `Linked` / `Unlinked`  — convex hulls cross / don't cross on the `.val`-circle.  `Unlinked`
                           is the negation of an alternating crossing quadruple; it agrees with
                           the bare-Lean `hullsUnlinked` test (`cyclicRuns ≤ 1`) on every
                           instance (verified `#eval`s match the census `5/14/12/55/22/42`).
* `Portrait`             — pairwise vertex-disjoint, pairwise-unlinked critical sets, weight `d-1`.
* `T`                    — delete the lowest-level (= least `.val`) point of each set, union all.

API proved here (sorry-free, native_decide-free, real kernel proofs):
* `T_card` — the weight identity `#T(P) = d - 1`.
* `Decidable` instances throughout; an unconditional `Fintype` for the portrait subtype.
* Downstream hooks: `sep_master` (the master separation inequality (M)), `linked_of_lt`,
  `mem_T`, the `minVal` spec lemmas.

Positions/level/fiber/`LevelCanonical` are reused from `CriticalPortraits.Core`.  The forward goal
`LevelCanonical (T P)` is a LATER brick (3b) and is deliberately NOT stated here.
-/


-- @@ L43-43 verbatim
@[expose] public section


-- @@ L45-45 verbatim
namespace CriticalPortraits


-- @@ L47-47 verbatim
open Finset

-- @@ L48-48 verbatim
open scoped BigOperators


-- @@ L50-50 verbatim
/-! ## 1. Critical sets. -/


-- @@ L52-55 verbatim
/-- `S ⊆ Z_{d*m}` is a **critical set**: it lies in one `σ_d`-fiber (all points share a
    column `r < m`) and has at least `2` points. Its **weight** is `S.card - 1`. -/
def IsCriticalSet (d m : ℕ) (S : Finset (ZMod (d * m))) : Prop :=
  (∃ r, r < m ∧ ∀ x ∈ S, x.val % m = r) ∧ 2 ≤ S.card


-- @@ L57-58 verbatim
instance (d m : ℕ) (S : Finset (ZMod (d * m))) : Decidable (IsCriticalSet d m S) := by
  unfold IsCriticalSet; infer_instance


-- @@ L60-67 verbatim
/-! ## 2. Unlinked: convex hulls don't cross.

`Linked A B` says there are two chords — `(a1, a2)` with endpoints in `A`, `(b1, b2)` with
endpoints in `B` — that **cross** on the circle `Z_N` read by `.val`.  Geometrically the two
crossing patterns (up to relabelling) are `a1 < b1 < a2 < b2` and `b1 < a1 < b2 < a2`
(strict on `.val`).  This is the val-linear form of "the four points alternate cyclically
`a, b, a, b`", which is exactly the negation of "`A` is a single cyclic run" — i.e. the
bare-Lean `hullsUnlinked` test `cyclicRuns ≤ 1`.  `Unlinked A B := ¬ Linked A B`. -/

-- @@ L68-72 verbatim
/-- Two cyclic subsets `A` and `B` are linked when they interleave. -/
def Linked {N : ℕ} (A B : Finset (ZMod N)) : Prop :=
  ∃ a1 ∈ A, ∃ a2 ∈ A, ∃ b1 ∈ B, ∃ b2 ∈ B,
    (a1.val < b1.val ∧ b1.val < a2.val ∧ a2.val < b2.val) ∨
    (b1.val < a1.val ∧ a1.val < b2.val ∧ b2.val < a2.val)


-- @@ L74-75 verbatim
instance {N : ℕ} (A B : Finset (ZMod N)) : Decidable (Linked A B) := by
  unfold Linked; infer_instance


-- @@ L77-78 verbatim
/-- `A` and `B` have unlinked convex hulls (no crossing chords). -/
def Unlinked {N : ℕ} (A B : Finset (ZMod N)) : Prop := ¬ Linked A B


-- @@ L80-81 verbatim
instance {N : ℕ} (A B : Finset (ZMod N)) : Decidable (Unlinked A B) := by
  unfold Unlinked; infer_instance


-- @@ L83-90 verbatim
/-- `Unlinked` is symmetric: crossing chords of `A, B` are crossing chords of `B, A`. -/
theorem Unlinked.symm {N : ℕ} {A B : Finset (ZMod N)} (h : Unlinked A B) : Unlinked B A := by
  intro hL
  apply h
  obtain ⟨b1, hb1, b2, hb2, a1, ha1, a2, ha2, hcase⟩ := hL
  rcases hcase with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact ⟨a1, ha1, a2, ha2, b1, hb1, b2, hb2, Or.inr ⟨h1, h2, h3⟩⟩
  · exact ⟨a1, ha1, a2, ha2, b1, hb1, b2, hb2, Or.inl ⟨h1, h2, h3⟩⟩


-- @@ L92-98 verbatim
/-- The crossing witness Lemma A / Seam / Bridge will call: a strictly-alternating quadruple
    `a1 < b1 < a2 < b2` (linear `.val` order) with `a1,a2 ∈ A`, `b1,b2 ∈ B` contradicts
    `Unlinked A B`. -/
theorem not_unlinked_of_alternating {N : ℕ} {A B : Finset (ZMod N)}
    {a1 a2 b1 b2 : ZMod N} (ha1 : a1 ∈ A) (ha2 : a2 ∈ A) (hb1 : b1 ∈ B) (hb2 : b2 ∈ B)
    (h1 : a1.val < b1.val) (h2 : b1.val < a2.val) (h3 : a2.val < b2.val) :
    ¬ Unlinked A B := fun h => h ⟨a1, ha1, a2, ha2, b1, hb1, b2, hb2, Or.inl ⟨h1, h2, h3⟩⟩


-- @@ L100-100 verbatim
/-! ## 3. Critical portraits. -/


-- @@ L102-108 verbatim
/-- A **critical portrait**: a family of critical sets that is pairwise vertex-disjoint,
    pairwise unlinked, of total weight `∑ (|S| - 1) = d - 1`. -/
def Portrait (d m : ℕ) (P : Finset (Finset (ZMod (d * m)))) : Prop :=
  (∀ S ∈ P, IsCriticalSet d m S) ∧
  (∀ A ∈ P, ∀ B ∈ P, A ≠ B → Disjoint A B) ∧
  (∀ A ∈ P, ∀ B ∈ P, A ≠ B → Unlinked A B) ∧
  (∑ S ∈ P, (S.card - 1) = d - 1)


-- @@ L110-111 verbatim
instance (d m : ℕ) (P : Finset (Finset (ZMod (d * m)))) : Decidable (Portrait d m P) := by
  unfold Portrait; infer_instance


-- @@ L113-113 verbatim
/-! ## 4. The portrait subtype is a Fintype (unconditional, mirroring `instFiniteCanonical`). -/


-- @@ L115-139 verbatim
/-- When `d * m = 0`, no portrait exists. (`m = 0` ⇒ no fiber witness; `d = 0` ⇒ weight
    target `0`, but every critical set has positive weight, so the family is empty.) -/
lemma portrait_eq_empty_of_degenerate (d m : ℕ) (h0 : d * m = 0)
    (P : Finset (Finset (ZMod (d * m)))) (hP : Portrait d m P) : P = ∅ := by
  classical
  obtain ⟨hcrit, _, _, hw⟩ := hP
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · -- m = 0: no fiber witness possible (r < 0 is impossible), so P has no element
    by_contra hne
    obtain ⟨S, hS⟩ := Finset.nonempty_of_ne_empty hne
    obtain ⟨⟨r, hr, _⟩, _⟩ := hcrit S hS
    omega
  · -- m > 0 ⇒ d = 0; weight target d - 1 = 0, but each S has card ≥ 2 ⇒ weight ≥ 1
    have hd0 : d = 0 := by
      rcases Nat.eq_zero_or_pos d with h | h
      · exact h
      · exfalso; have : 0 < d * m := Nat.mul_pos h hmpos; omega
    by_contra hne
    obtain ⟨S, hS⟩ := Finset.nonempty_of_ne_empty hne
    have hcardS : 2 ≤ S.card := (hcrit S hS).2
    have hpos : 0 < ∑ T ∈ P, (T.card - 1) := by
      apply Finset.sum_pos'
      · intro i _; exact Nat.zero_le _
      · exact ⟨S, hS, by omega⟩
    simp_all


-- @@ L141-149 verbatim
instance instFinitePortrait (d m : ℕ) :
    Finite {P : Finset (Finset (ZMod (d * m))) // Portrait d m P} := by
  rcases Nat.eq_zero_or_pos (d * m) with h0 | hpos
  · exact Finite.of_injective (fun _ => (0 : Unit)) (by
      intro a b _
      exact Subtype.ext ((portrait_eq_empty_of_degenerate d m h0 a.1 a.2).trans
        (portrait_eq_empty_of_degenerate d m h0 b.1 b.2).symm))
  · have : NeZero (d * m) := ⟨hpos.ne'⟩
    infer_instance


-- @@ L151-153 verbatim
noncomputable instance instFintypePortrait (d m : ℕ) :
    Fintype {P : Finset (Finset (ZMod (d * m))) // Portrait d m P} :=
  Fintype.ofFinite _


-- @@ L155-159 verbatim
/-! ## 5. The delete-min map `T`.

`ZMod N` has no `LinearOrder`, so we pick the dropped point by minimising `.val` via
`Finset.exists_min_image`.  Within a single fiber `val = level*m + col` is strictly monotone
in level, so least-`.val` = lowest-level = exactly bare-Lean's `S.drop 1`. -/


-- @@ L161-163 verbatim
/-- The least-`.val` element of a nonempty set (the lowest-level point of a critical set). -/
noncomputable def minVal {N : ℕ} (S : Finset (ZMod N)) (h : S.Nonempty) : ZMod N :=
  (Finset.exists_min_image S (fun x => x.val) h).choose


-- @@ L165-166 verbatim
lemma minVal_mem {N : ℕ} (S : Finset (ZMod N)) (h : S.Nonempty) : minVal S h ∈ S :=
  (Finset.exists_min_image S (fun x => x.val) h).choose_spec.1


-- @@ L168-170 verbatim
lemma minVal_le {N : ℕ} (S : Finset (ZMod N)) (h : S.Nonempty) :
    ∀ x ∈ S, (minVal S h).val ≤ x.val :=
  (Finset.exists_min_image S (fun x => x.val) h).choose_spec.2


-- @@ L172-174 verbatim
/-- Drop the lowest-level (least-`.val`) point of `S` (identity on the empty set). -/
noncomputable def eraseMin {N : ℕ} (S : Finset (ZMod N)) : Finset (ZMod N) :=
  if h : S.Nonempty then S.erase (minVal S h) else S


-- @@ L176-180 verbatim
lemma eraseMin_subset {N : ℕ} (S : Finset (ZMod N)) : eraseMin S ⊆ S := by
  unfold eraseMin
  split
  · exact Finset.erase_subset _ _
  · exact subset_rfl


-- @@ L182-185 verbatim
lemma eraseMin_card {N : ℕ} (S : Finset (ZMod N)) (h : S.Nonempty) :
    (eraseMin S).card = S.card - 1 := by
  unfold eraseMin
  rw [dite_eq_left h, Finset.card_erase_of_mem (minVal_mem S h)]


-- @@ L187-193 verbatim
/-- Membership in `eraseMin`: everything of `S` except its `.val`-minimum (nonempty `S`).
    The clean characterization the downstream membership reasoning will use. -/
lemma mem_eraseMin {N : ℕ} (S : Finset (ZMod N)) (h : S.Nonempty) (x : ZMod N) :
    x ∈ eraseMin S ↔ x ∈ S ∧ x ≠ minVal S h := by
  unfold eraseMin
  rw [dite_eq_left h, Finset.mem_erase]
  tauto


-- @@ L195-197 verbatim
/-- `T(P)`: delete the lowest-level point of every set, then take the union. -/
noncomputable def T {N : ℕ} (P : Finset (Finset (ZMod N))) : Finset (ZMod N) :=
  P.sup eraseMin


-- @@ L199-203 verbatim
/-- The erased sets remain pairwise disjoint (erase only shrinks). -/
lemma eraseMin_pairwiseDisjoint {d m : ℕ} (P : Finset (Finset (ZMod (d * m))))
    (hP : Portrait d m P) : (↑P : Set (Finset (ZMod (d * m)))).PairwiseDisjoint eraseMin := by
  intro A hA B hB hAB
  exact (hP.2.1 A hA B hB hAB).mono (eraseMin_subset A) (eraseMin_subset B)


-- @@ L205-205 verbatim
/-! ## 6. BASIC API: the weight identity `#T = d - 1`. -/


-- @@ L207-218 verbatim
/-- **The weight identity.** For a critical portrait, `#T(P) = d - 1`. -/
theorem T_card {d m : ℕ} {P : Finset (Finset (ZMod (d * m)))}
    (hP : Portrait d m P) : (T P).card = d - 1 := by
  classical
  unfold T
  rw [Finset.sup_eq_biUnion, Finset.card_biUnion (eraseMin_pairwiseDisjoint P hP)]
  rw [← hP.2.2.2]
  apply Finset.sum_congr rfl
  intro S hS
  have hcard : 2 ≤ S.card := (hP.1 S hS).2
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  exact eraseMin_card S hne


-- @@ L220-225 verbatim
/-! ## 6b. The min-rule is the min-LEVEL rule (load-bearing for forward/surjectivity).

The bare-Lean `S.drop 1` drops the lowest-LEVEL point.  `minVal` drops the least-`.val` point.
These coincide on a critical set because within one fiber the `.val` order is the level order,
and the level is injective on the set.  This underwrites "survivors = edge tops" and "each
block/component has a unique non-survivor = its lowest-level vertex" (scout risk R2). -/


-- @@ L227-238 verbatim
/-- Within a single fiber (same residue mod `m`), the `.val` order equals the level order. -/
theorem val_le_iff_level_le_of_sameFiber {N m : ℕ} {x y : ZMod N}
    (hxy : x.val % m = y.val % m) :
    x.val ≤ y.val ↔ x.val / m ≤ y.val / m := by
  constructor
  · intro h; exact Nat.div_le_div_right h
  · intro h
    have hx : x.val = (x.val / m) * m + x.val % m := (Nat.div_add_mod' x.val m).symm
    have hy : y.val = (y.val / m) * m + y.val % m := (Nat.div_add_mod' y.val m).symm
    rw [hxy] at hx
    have : (x.val / m) * m ≤ (y.val / m) * m := Nat.mul_le_mul_right m h
    omega


-- @@ L240-247 verbatim
/-- The level is injective on a single fiber: same fiber + same level ⇒ same `.val` ⇒
    same element. -/
theorem level_injOn_fiber {N m : ℕ} [NeZero N] {x y : ZMod N}
    (hxy : x.val % m = y.val % m) (hlev : x.val / m = y.val / m) : x = y := by
  have hx : x.val = (x.val / m) * m + x.val % m := (Nat.div_add_mod' x.val m).symm
  have hy : y.val = (y.val / m) * m + y.val % m := (Nat.div_add_mod' y.val m).symm
  have : x.val = y.val := by rw [hx, hy, hxy, hlev]
  exact ZMod.val_injective _ this


-- @@ L249-258 verbatim
/-- **The min-rule is the min-LEVEL rule.** On a critical set, `minVal S` is the unique point
    of minimum level: its level is `≤` every member's. -/
theorem minVal_level_le {d m : ℕ} {S : Finset (ZMod (d * m))}
    (hS : IsCriticalSet d m S) (h : S.Nonempty) :
    ∀ x ∈ S, (minVal S h).val / m ≤ x.val / m := by
  obtain ⟨⟨r, hr, hfib⟩, _⟩ := hS
  intro x hx
  have hsame : (minVal S h).val % m = x.val % m := by
    rw [hfib _ (minVal_mem S h), hfib _ hx]
  exact (val_le_iff_level_le_of_sameFiber hsame).mp (minVal_le S h x hx)


-- @@ L260-278 verbatim
/-- The dropped point (the minimum) is strictly below — in LEVEL — every survivor of that set.
    This is what makes "survivors = edge tops" hold; each critical set keeps exactly its tops. -/
theorem minVal_lt_survivor {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {S : Finset (ZMod (d * m))} (hS : IsCriticalSet d m S) (h : S.Nonempty) :
    ∀ x ∈ eraseMin S, (minVal S h).val / m < x.val / m := by
  have : NeZero (d * m) := ⟨by positivity⟩
  obtain ⟨⟨r, hr, hfib⟩, hcard⟩ := hS
  intro x hx
  have hxS : x ∈ S := eraseMin_subset S hx
  have hxne : x ≠ minVal S h := by
    unfold eraseMin at hx
    simp_all
  have hsame : (minVal S h).val % m = x.val % m := by
    rw [hfib _ (minVal_mem S h), hfib _ hxS]
  have hle : (minVal S h).val / m ≤ x.val / m :=
    minVal_level_le ⟨⟨r, hr, hfib⟩, hcard⟩ h x hxS
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exact absurd (level_injOn_fiber hsame heq).symm hxne


-- @@ L280-282 verbatim
/-! ## 7. Helper facts the downstream bricks will want.

These pin the model to the verified one and expose the (M)-style arithmetic. -/


-- @@ L284-287 verbatim
/-- Within one fiber, `val` is strictly monotone in level: a point's `.val` equals
    `level * m + col`.  (Used to identify least-`.val` with lowest-level.) -/
lemma val_eq_level_mul_add_col {N : ℕ} (m : ℕ) (i : ZMod N) :
    i.val = (i.val / m) * m + i.val % m := (Nat.div_add_mod' i.val m).symm


-- @@ L289-295 verbatim
/-- **The master separation inequality (M).** One level of separation beats any column
    offset: for columns `p, q < m` and levels `a < c`, `p + a*m < q + c*m`. -/
lemma sep_master {m : ℕ} {p q a c : ℕ} (hp : p < m) (_hq : q < m) (hac : a < c) :
    p + a * m < q + c * m := by
  have hstep : (a + 1) * m ≤ c * m := Nat.mul_le_mul_right m (by omega)
  have : a * m + m ≤ c * m := by rw [Nat.add_mul, Nat.one_mul] at hstep; omega
  omega


-- @@ L297-302 verbatim
/-- A crossing quadruple in strict val-order makes `A, B` linked (the (M)-witness hook). -/
lemma linked_of_lt {N : ℕ} {A B : Finset (ZMod N)} {a1 a2 b1 b2 : ZMod N}
    (ha1 : a1 ∈ A) (ha2 : a2 ∈ A) (hb1 : b1 ∈ B) (hb2 : b2 ∈ B)
    (h1 : a1.val < b1.val) (h2 : b1.val < a2.val) (h3 : a2.val < b2.val) :
    Linked A B :=
  ⟨a1, ha1, a2, ha2, b1, hb1, b2, hb2, Or.inl ⟨h1, h2, h3⟩⟩


-- @@ L304-308 verbatim
/-- Membership in `T P`. -/
lemma mem_T {N : ℕ} {P : Finset (Finset (ZMod N))} {x : ZMod N} :
    x ∈ T P ↔ ∃ S ∈ P, x ∈ eraseMin S := by
  unfold T
  rw [Finset.mem_sup]


-- @@ L310-315 verbatim
/-! ## 8. `T P` lands in the `(d-1)`-subsets (the start of the `Tsub` packaging).

`T_card` gives the cardinality; we package `T P` into the same `{S // S.card = d-1}` subtype
the denominator counts (`Denominator.Asub`).  The remaining `LevelCanonical (T P)` clause —
landing in the FULL `{S // S.card = d-1 ∧ LevelCanonical d m S}` subtype (`Denominator.Csub`) —
is the FORWARD direction (brick 3b) and is deliberately NOT proved here. -/


-- @@ L317-321 verbatim
/-- `T P` packaged as a `(d-1)`-subset; the first half of the eventual `Tsub` into
    `Denominator.Csub`. -/
noncomputable def TsubCard {d m : ℕ} {P : Finset (Finset (ZMod (d * m)))}
    (hP : Portrait d m P) : {S : Finset (ZMod (d * m)) // S.card = d - 1} :=
  ⟨T P, T_card hP⟩


-- @@ L323-323 verbatim
end CriticalPortraits
