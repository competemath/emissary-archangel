/-
Copyright (c) 2026 Wouter Cames van Batenburg, Samuel Korsky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Cames van Batenburg, Samuel Korsky
-/

module

public import LeanPool.MooreBound.DegreeDiameter.HalvedFlags
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas


-- @@ L13-26 verbatim
/-!
# Exact counting of one-step refinements and parity completions

The interval between subspaces `U ⊆ W` whose ranks differ by two is
equivalent to the projective line of `W / U`.  We then prove that the choices
in the `k` disjoint rank-two intervals of a parity partial flag are genuinely
independent by constructing complete flags from arbitrary coordinate tuples.
The resulting equivalences give the exact completion multiplicity
`(|K| + 1)^k`; the neighbor-degree argument at the end deliberately remains
an injection, since a graph neighbor need not have a unique common odd part.

Lean Pool port of wewantmoore commit d59bd80ea93fabb9faf769e790ab47692645e022.
The port adds a namespace and adapts proofs to the current Mathlib APIs and repository style.
-/


-- @@ L28-28 verbatim
@[expose] public section


-- @@ L30-30 verbatim
namespace MooreBound


-- @@ L32-32 verbatim
open Module

-- @@ L33-33 verbatim
open scoped LinearAlgebra.Projectivization


-- @@ L35-35 verbatim
namespace DegreeDiameter


-- @@ L37-37 verbatim
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]


-- @@ L39-45 verbatim
/-- Subspaces one rank above `U` and contained in `W`. -/
structure IntermediateSubspace (U W : Submodule K V) where
  /-- The subspace between the fixed lower and upper endpoints. -/
  space : Submodule K V
  lower : U ≤ space
  upper : space ≤ W
  finrank_space : finrank K space = finrank K U + 1


-- @@ L47-47 verbatim
namespace IntermediateSubspace


-- @@ L49-55 verbatim
@[ext]
theorem ext {U W : Submodule K V} {L L' : IntermediateSubspace U W}
    (h : L.space = L'.space) : L = L' := by
  cases L
  cases L'
  cases h
  rfl


-- @@ L57-60 verbatim
instance {U W : Submodule K V} [Finite V] : Finite (IntermediateSubspace U W) := by
  let : Finite (Submodule K V) :=
    Finite.of_injective (fun S : Submodule K V ↦ (S : Set V)) SetLike.coe_injective
  exact Finite.of_injective (fun L : IntermediateSubspace U W ↦ L.space) fun _ _ h ↦ ext h


-- @@ L62-62 verbatim
end IntermediateSubspace


-- @@ L64-72 verbatim
/-- Rank-nullity for the image of `L` in the quotient by a contained `U`. -/
theorem finrank_map_mkQ_add
    [FiniteDimensional K V] {U L : Submodule K V} (hUL : U ≤ L) :
    finrank K (L.map U.mkQ) + finrank K U = finrank K L := by
  have h := (U.mkQ.domRestrict L).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, Submodule.ker_mkQ] at h
  have hker : finrank K (U.comap L.subtype) = finrank K U :=
    (Submodule.comapSubtypeEquivOfLe hUL).finrank_eq
  simpa [hker] using h


-- @@ L74-74 verbatim
section ProjectiveLine


-- @@ L76-76 verbatim
variable [FiniteDimensional K V]


-- @@ L78-95 verbatim
/-- The image of an intermediate subspace in `W / U`, regarded as a
one-dimensional subspace of the two-dimensional image of `W`. -/
noncomputable def intermediatePoint
    {U W : Submodule K V}
    (_hUW : U ≤ W) (_hW : finrank K W = finrank K U + 2)
    (L : IntermediateSubspace U W) : ℙ K (W.map U.mkQ) := by
  let qW : Submodule K (V ⧸ U) := W.map U.mkQ
  let qL : Submodule K (V ⧸ U) := L.space.map U.mkQ
  have hq : qL ≤ qW := Submodule.map_mono L.upper
  let inside : Submodule K qW := qL.comap qW.subtype
  have hqL := finrank_map_mkQ_add L.lower
  have hqL_one : finrank K qL = 1 := by
    dsimp [qL] at hqL ⊢
    rw [L.finrank_space] at hqL
    omega
  have hins : finrank K inside = finrank K qL :=
    (Submodule.comapSubtypeEquivOfLe hq).finrank_eq
  exact Projectivization.mk'' inside (hins.trans hqL_one)


-- @@ L97-117 verbatim
theorem intermediatePoint_injective
    {U W : Submodule K V}
    (hUW : U ≤ W) (hW : finrank K W = finrank K U + 2) :
    Function.Injective (intermediatePoint hUW hW) := by
  intro L L' hpoint
  apply IntermediateSubspace.ext
  let qW : Submodule K (V ⧸ U) := W.map U.mkQ
  let qL : Submodule K (V ⧸ U) := L.space.map U.mkQ
  let qL' : Submodule K (V ⧸ U) := L'.space.map U.mkQ
  have hq : qL ≤ qW := Submodule.map_mono L.upper
  have hq' : qL' ≤ qW := Submodule.map_mono L'.upper
  have hins : qL.comap qW.subtype = qL'.comap qW.subtype := by
    have := congrArg Projectivization.submodule hpoint
    simpa [intermediatePoint, qW, qL, qL'] using this
  have hquot : qL = qL' := by
    have hm := congrArg (fun S : Submodule K qW ↦ S.map qW.subtype) hins
    simpa [Submodule.map_comap_subtype, inf_eq_right.mpr hq,
      inf_eq_right.mpr hq'] using hm
  have hrecover := congrArg (fun S : Submodule K (V ⧸ U) ↦ S.comap U.mkQ) hquot
  simpa [qL, qL', Submodule.comap_map_mkQ, sup_eq_right.mpr L.lower,
    sup_eq_right.mpr L'.lower] using hrecover


-- @@ L119-165 verbatim
/-- Pull a projective point in `W / U` back to the unique intermediate
subspace of `V`. This explicit pullback is inverse to `intermediatePoint`. -/
noncomputable def intermediateSubspaceOfPoint
    {U W : Submodule K V}
    (hUW : U ≤ W) (p : ℙ K (W.map U.mkQ)) : IntermediateSubspace U W := by
  let qW : Submodule K (V ⧸ U) := W.map U.mkQ
  let T : Submodule K (V ⧸ U) := p.submodule.map qW.subtype
  let L : Submodule K V := T.comap U.mkQ
  have hTqW : T ≤ qW := by
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact y.property
  have hUL : U ≤ L := by
    intro x hx
    change U.mkQ x ∈ T
    have hxker : x ∈ LinearMap.ker U.mkQ := by
      simpa [Submodule.ker_mkQ] using hx
    rw [LinearMap.mem_ker.mp hxker]
    exact T.zero_mem
  have hLW : L ≤ W := by
    intro x hx
    have hxqW : U.mkQ x ∈ qW := hTqW hx
    rcases hxqW with ⟨w, hwW, hw⟩
    have hdiff : x - w ∈ U :=
      (Submodule.Quotient.eq U).mp (by simpa [Submodule.mkQ_apply] using hw.symm)
    have hsum : x - w + w = x := sub_add_cancel x w
    rw [← hsum]
    exact W.add_mem (hUW hdiff) hwW
  have hcomap : T.comap qW.subtype = p.submodule := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      have : y = x := Subtype.ext hxy
      simpa [this] using hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hTfinrank : finrank K T = 1 := by
    have h := (Submodule.comapSubtypeEquivOfLe hTqW).finrank_eq
    rw [hcomap, Projectivization.finrank_submodule] at h
    exact h.symm
  have himage : L.map U.mkQ = T := by
    simpa [L] using
      (Submodule.map_comap_eq_of_surjective U.mkQ_surjective T)
  refine ⟨L, hUL, hLW, ?_⟩
  have hrank := finrank_map_mkQ_add hUL
  rw [himage, hTfinrank] at hrank
  omega


-- @@ L167-194 verbatim
/-- The quotient-image construction and pullback construction are inverse:
rank-two subspace intervals are exactly projective lines. -/
theorem intermediatePoint_surjective
    {U W : Submodule K V}
    (hUW : U ≤ W) (hW : finrank K W = finrank K U + 2) :
    Function.Surjective (intermediatePoint hUW hW) := by
  intro p
  refine ⟨intermediateSubspaceOfPoint hUW p, ?_⟩
  apply Projectivization.submodule_injective
  let qW : Submodule K (V ⧸ U) := W.map U.mkQ
  let T : Submodule K (V ⧸ U) := p.submodule.map qW.subtype
  have hTqW : T ≤ qW := by
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact y.property
  have hcomap : T.comap qW.subtype = p.submodule := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      have : y = x := Subtype.ext hxy
      simpa [this] using hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have himage :
      (intermediateSubspaceOfPoint hUW p).space.map U.mkQ = T := by
    change (T.comap U.mkQ).map U.mkQ = T
    exact Submodule.map_comap_eq_of_surjective U.mkQ_surjective T
  simp [intermediatePoint, qW, himage, hcomap]


-- @@ L196-204 verbatim
/-- The genuine bijection between a rank-two interval and its projective
line. -/
noncomputable def intermediateSubspaceEquivProjectiveLine
    {U W : Submodule K V}
    (hUW : U ≤ W) (hW : finrank K W = finrank K U + 2) :
    IntermediateSubspace U W ≃ ℙ K (W.map U.mkQ) :=
  Equiv.ofBijective (intermediatePoint hUW hW)
    ⟨intermediatePoint_injective hUW hW,
      intermediatePoint_surjective hUW hW⟩


-- @@ L206-222 verbatim
/-- Exactly `|K| + 1` subspaces occur in a rank-two interval. -/
theorem natCard_intermediate_eq
    [Finite K] [Finite V]
    {U W : Submodule K V}
    (hUW : U ≤ W) (hW : finrank K W = finrank K U + 2) :
    Nat.card (IntermediateSubspace U W) = Nat.card K + 1 := by
  let : Fintype V := Fintype.ofFinite V
  let qW : Submodule K (V ⧸ U) := W.map U.mkQ
  have hqW := finrank_map_mkQ_add hUW
  have hqW_two : finrank K qW = 2 := by
    dsimp [qW] at hqW ⊢
    rw [hW] at hqW
    omega
  calc
    Nat.card (IntermediateSubspace U W) = Nat.card (ℙ K qW) :=
      Nat.card_congr (intermediateSubspaceEquivProjectiveLine hUW hW)
    _ = Nat.card K + 1 := Projectivization.card_of_finrank_two K qW hqW_two


-- @@ L224-230 verbatim
/-- There are at most `|K| + 1` possible intermediate subspaces. -/
theorem natCard_intermediate_le
    [Finite K] [Finite V]
    {U W : Submodule K V}
    (hUW : U ≤ W) (hW : finrank K W = finrank K U + 2) :
    Nat.card (IntermediateSubspace U W) ≤ Nat.card K + 1 := by
  exact (natCard_intermediate_eq hUW hW).le


-- @@ L232-232 verbatim
end ProjectiveLine


-- @@ L234-234 verbatim
section PartialFlagCompletions


-- @@ L236-236 verbatim
variable [FiniteDimensional K V] [Finite K] [Finite V]


-- @@ L238-240 verbatim
/-- Consecutive retained even ranks surrounding the `j`-th missing odd rank. -/
def evenLowerRank (k : ℕ) (j : Fin k) : Fin ((2 * k + 1) + 1) :=
  ⟨2 * j.val, by omega⟩


-- @@ L242-244 verbatim
/-- The missing odd rank 2j+1 between consecutive retained even ranks. -/
def oddMiddleRank (k : ℕ) (j : Fin k) : Fin ((2 * k + 1) + 1) :=
  ⟨2 * j.val + 1, by omega⟩


-- @@ L246-248 verbatim
/-- The upper even rank 2j+2 surrounding a missing odd rank. -/
def evenUpperRank (k : ℕ) (j : Fin k) : Fin ((2 * k + 1) + 1) :=
  ⟨2 * j.val + 2, by omega⟩


-- @@ L250-253 verbatim
/-- Consecutive retained odd ranks surrounding the `j`-th missing positive
even rank. -/
def oddLowerRank (k : ℕ) (j : Fin k) : Fin ((2 * k + 1) + 1) :=
  ⟨2 * j.val + 1, by omega⟩


-- @@ L255-257 verbatim
/-- The missing even rank 2j+2 between consecutive retained odd ranks. -/
def evenMiddleRank (k : ℕ) (j : Fin k) : Fin ((2 * k + 1) + 1) :=
  ⟨2 * j.val + 2, by omega⟩


-- @@ L259-261 verbatim
/-- The upper odd rank 2j+3 surrounding a missing even rank. -/
def oddUpperRank (k : ℕ) (j : Fin k) : Fin ((2 * k + 1) + 1) :=
  ⟨2 * j.val + 3, by omega⟩


-- @@ L263-264 verbatim
@[simp] theorem evenLowerRank_val (k : ℕ) (j : Fin k) :
    (evenLowerRank k j).val = 2 * j.val := rfl

-- @@ L265-266 verbatim
@[simp] theorem oddMiddleRank_val (k : ℕ) (j : Fin k) :
    (oddMiddleRank k j).val = 2 * j.val + 1 := rfl

-- @@ L267-268 verbatim
@[simp] theorem evenUpperRank_val (k : ℕ) (j : Fin k) :
    (evenUpperRank k j).val = 2 * j.val + 2 := rfl

-- @@ L269-270 verbatim
@[simp] theorem oddLowerRank_val (k : ℕ) (j : Fin k) :
    (oddLowerRank k j).val = 2 * j.val + 1 := rfl

-- @@ L271-272 verbatim
@[simp] theorem evenMiddleRank_val (k : ℕ) (j : Fin k) :
    (evenMiddleRank k j).val = 2 * j.val + 2 := rfl

-- @@ L273-274 verbatim
@[simp] theorem oddUpperRank_val (k : ℕ) (j : Fin k) :
    (oddUpperRank k j).val = 2 * j.val + 3 := rfl


-- @@ L276-283 verbatim
omit [FiniteDimensional K V] [Finite K] [Finite V] in
theorem ofComplete_space_eq_of_mod
    {n parity : ℕ} {F : CompleteFlag K V n}
    {P : PartialFlag (K := K) (V := V) (n := n) parity}
    (h : PartialFlag.ofComplete parity F = P) (i : Fin (n + 1))
    (hi : i.val % 2 = parity % 2) : F i = P.1 i := by
  have hi' := congrFun (congrArg Subtype.val h) i
  simpa [PartialFlag.ofComplete, flagPart, hi] using hi'


-- @@ L285-293 verbatim
omit [FiniteDimensional K V] [Finite K] [Finite V] in
/-- A represented partial flag is bottom at every erased rank. -/
theorem partialFlag_space_eq_bot_of_mod_ne
    {n parity : ℕ}
    (P : PartialFlag (K := K) (V := V) (n := n) parity)
    (i : Fin (n + 1)) (hi : i.val % 2 ≠ parity % 2) : P.1 i = ⊥ := by
  obtain ⟨F, hF⟩ := P.property
  have hi' := congrFun hF i
  simpa [flagPart, hi] using hi'.symm


-- @@ L295-304 verbatim
omit [FiniteDimensional K V] [Finite K] [Finite V] in
/-- At every retained rank a partial flag has the prescribed dimension. -/
theorem partialFlag_finrank_space_of_mod
    {n parity : ℕ}
    (P : PartialFlag (K := K) (V := V) (n := n) parity)
    (i : Fin (n + 1)) (hi : i.val % 2 = parity % 2) :
    finrank K (P.1 i) = i.val := by
  obtain ⟨F, hF⟩ := P.property
  have hPF : PartialFlag.ofComplete parity F = P := Subtype.ext hF
  rw [← ofComplete_space_eq_of_mod hPF i hi, F.finrank_space]


-- @@ L306-315 verbatim
omit [FiniteDimensional K V] [Finite K] [Finite V] in
/-- The existence of a partial flag already fixes the dimension of the
ambient space. -/
theorem finrank_eq_of_partialFlag
    {n parity : ℕ}
    (P : PartialFlag (K := K) (V := V) (n := n) parity) :
    finrank K V = n := by
  obtain ⟨F, _hF⟩ := P.property
  rw [← finrank_top K V, ← F.space_last, F.finrank_space]
  rfl


-- @@ L317-334 verbatim
/-- Package a ranked adjacent chain as a complete flag.  Strictness follows
from adjacent containment together with the one-rank dimension increase. -/
def completeFlagOfRankedSpaces {n : ℕ}
    (S : Fin (n + 1) → Submodule K V)
    (hrank : ∀ i, finrank K (S i) = i.val)
    (hstep : ∀ i : Fin n, S i.castSucc ≤ S i.succ)
    (hzero : S 0 = ⊥) (hlast : S (Fin.last n) = ⊤) :
    CompleteFlag K V n where
  space := S
  strictMono_space := Fin.strictMono_iff_lt_succ.2 fun i ↦ by
    have hle := hstep i
    exact lt_of_le_of_ne hle fun heq ↦ by
      have h := congrArg (fun T : Submodule K V ↦ finrank K T) heq
      rw [hrank, hrank] at h
      simp at h
  finrank_space := hrank
  space_zero := hzero
  space_last := hlast


-- @@ L336-344 verbatim
omit [FiniteDimensional K V] [Finite K] [Finite V] in
@[simp]
theorem completeFlagOfRankedSpaces_apply {n : ℕ}
    (S : Fin (n + 1) → Submodule K V)
    (hrank : ∀ i, finrank K (S i) = i.val)
    (hstep : ∀ i : Fin n, S i.castSucc ≤ S i.succ)
    (hzero : S 0 = ⊥) (hlast : S (Fin.last n) = ⊤)
    (i : Fin (n + 1)) :
    completeFlagOfRankedSpaces S hrank hstep hzero hlast i = S i := rfl


-- @@ L346-351 verbatim
/-- The product of the `k` projective-line intervals in which an even
partial flag can be completed. -/
abbrev EvenCompletionCoordinates (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :=
  ∀ j : Fin k,
    IntermediateSubspace (P.1 (evenLowerRank k j)) (P.1 (evenUpperRank k j))


-- @@ L353-360 verbatim
/-- The common complete flag selected from a compatible pair.  Its
uniqueness was proved in `compatible_unique`; choice is used only to define
the counting injection. -/
noncomputable def completeOfEvenCompatibility (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (x : {Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q}) :
    CompleteFlag K V (2 * k + 1) :=
  Classical.choose x.property


-- @@ L362-367 verbatim
omit [FiniteDimensional K V] [Finite K] [Finite V] in
theorem completeOfEvenCompatibility_even (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (x : {Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q}) :
    PartialFlag.ofComplete 0 (completeOfEvenCompatibility k P x) = P :=
  (Classical.choose_spec x.property).1


-- @@ L369-374 verbatim
omit [FiniteDimensional K V] [Finite K] [Finite V] in
theorem completeOfEvenCompatibility_odd (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (x : {Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q}) :
    PartialFlag.ofComplete 1 (completeOfEvenCompatibility k P x) = x.1 :=
  (Classical.choose_spec x.property).2


-- @@ L376-397 verbatim
/-- Extract each intermediate subspace from a compatible odd partial flag. -/
noncomputable def evenCompletionCoordinates (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :
    {Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q} →
      EvenCompletionCoordinates k P :=
  fun x j ↦ by
    let F := completeOfEvenCompatibility k P x
    have hEven := completeOfEvenCompatibility_even k P x
    have hlow : F (evenLowerRank k j) = P.1 (evenLowerRank k j) :=
      ofComplete_space_eq_of_mod hEven _ (by simp [evenLowerRank])
    have hhigh : F (evenUpperRank k j) = P.1 (evenUpperRank k j) :=
      ofComplete_space_eq_of_mod hEven _ (by simp [evenUpperRank])
    refine ⟨F (oddMiddleRank k j), ?_, ?_, ?_⟩
    · rw [← hlow]
      exact F.strictMono_space.monotone (by simp [evenLowerRank, oddMiddleRank])
    · rw [← hhigh]
      exact F.strictMono_space.monotone (by simp [oddMiddleRank, evenUpperRank])
    · rw [F.finrank_space]
      have hlowrank := F.finrank_space (evenLowerRank k j)
      rw [hlow] at hlowrank
      rw [hlowrank]
      simp [oddMiddleRank, evenLowerRank]


-- @@ L399-406 verbatim
omit [FiniteDimensional K V] [Finite K] [Finite V] in
@[simp]
theorem evenCompletionCoordinates_space (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (x : {Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q})
    (j : Fin k) :
    (evenCompletionCoordinates k P x j).space =
      completeOfEvenCompatibility k P x (oddMiddleRank k j) := rfl


-- @@ L408-440 verbatim
omit [FiniteDimensional K V] [Finite K] [Finite V] in
theorem evenCompletionCoordinates_injective (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :
    Function.Injective (evenCompletionCoordinates k P) := by
  intro x y hxy
  let F := completeOfEvenCompatibility k P x
  let G := completeOfEvenCompatibility k P y
  have hEvenF := completeOfEvenCompatibility_even k P x
  have hEvenG := completeOfEvenCompatibility_even k P y
  have hFG : F = G := by
    apply CompleteFlag.ext
    intro i
    by_cases hi : i.val % 2 = 0
    · exact (ofComplete_space_eq_of_mod hEvenF i hi).trans
        (ofComplete_space_eq_of_mod hEvenG i hi).symm
    · have hiOdd : i.val % 2 = 1 := by omega
      by_cases hlast : i.val = 2 * k + 1
      · have hiLast : i = Fin.last (2 * k + 1) := by ext; simpa using hlast
        rw [hiLast, F.space_last, G.space_last]
      · have hiLt : i.val < 2 * k + 1 := by omega
        let j : Fin k := ⟨i.val / 2, by omega⟩
        have hij : i = oddMiddleRank k j := by
          apply Fin.ext
          simp [j, oddMiddleRank]
          omega
        have hs := congrArg (fun c ↦ (c j).space) hxy
        simpa [F, G, hij] using hs
  apply Subtype.ext
  calc
    x.1 = PartialFlag.ofComplete 1 F :=
      (completeOfEvenCompatibility_odd k P x).symm
    _ = PartialFlag.ofComplete 1 G := congrArg (PartialFlag.ofComplete 1) hFG
    _ = y.1 := completeOfEvenCompatibility_odd k P y


-- @@ L442-450 verbatim
omit [FiniteDimensional K V] [Finite K] [Finite V] in
theorem evenBoundary_le (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) (j : Fin k) :
    P.1 (evenLowerRank k j) ≤ P.1 (evenUpperRank k j) := by
  obtain ⟨F, hF⟩ := P.property
  have hPF : PartialFlag.ofComplete 0 F = P := Subtype.ext hF
  rw [← ofComplete_space_eq_of_mod hPF _ (by simp [evenLowerRank]),
    ← ofComplete_space_eq_of_mod hPF _ (by simp [evenUpperRank])]
  exact F.strictMono_space.monotone (by simp [evenLowerRank, evenUpperRank])


-- @@ L452-462 verbatim
omit [FiniteDimensional K V] [Finite K] [Finite V] in
theorem evenBoundary_finrank (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) (j : Fin k) :
    finrank K (P.1 (evenUpperRank k j)) =
      finrank K (P.1 (evenLowerRank k j)) + 2 := by
  obtain ⟨F, hF⟩ := P.property
  have hPF : PartialFlag.ofComplete 0 F = P := Subtype.ext hF
  rw [← ofComplete_space_eq_of_mod hPF _ (by simp),
    ← ofComplete_space_eq_of_mod hPF _ (by simp),
    F.finrank_space, F.finrank_space]
  simp [evenLowerRank, evenUpperRank]


-- @@ L464-472 verbatim
/-- Interleave arbitrary rank-one choices in the rank-two intervals of an
even partial flag; the final odd rank is the ambient top space. -/
def evenCompletedSpace (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (c : EvenCompletionCoordinates k P) :
    Fin ((2 * k + 1) + 1) → Submodule K V := fun i ↦
  if hi : i.val % 2 = 0 then P.1 i
  else if _hlast : i.val = 2 * k + 1 then ⊤
  else (c ⟨i.val / 2, by omega⟩).space


-- @@ L474-480 verbatim
omit [FiniteDimensional K V] [Finite K] [Finite V] in
@[simp]
theorem evenCompletedSpace_of_even (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (c : EvenCompletionCoordinates k P) (i : Fin ((2 * k + 1) + 1))
    (hi : i.val % 2 = 0) : evenCompletedSpace k P c i = P.1 i := by
  simp [evenCompletedSpace, hi]


-- @@ L482-500 verbatim
omit [FiniteDimensional K V] [Finite K] [Finite V] in
@[simp]
theorem evenCompletedSpace_oddMiddle (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (c : EvenCompletionCoordinates k P) (j : Fin k) :
    evenCompletedSpace k P c (oddMiddleRank k j) = (c j).space := by
  have hparity : (oddMiddleRank k j).val % 2 ≠ 0 := by
    simp [oddMiddleRank]
  have hlast : (oddMiddleRank k j).val ≠ 2 * k + 1 := by
    simp [oddMiddleRank]
    omega
  have hindex :
      (⟨(oddMiddleRank k j).val / 2, by omega⟩ : Fin k) = j := by
    apply Fin.ext
    change (2 * j.val + 1) / 2 = j.val
    rw [Nat.mul_add_div (by omega)]
    simp
  unfold evenCompletedSpace
  rw [dite_eq_right hparity, dite_eq_right hlast, hindex]


-- @@ L502-508 verbatim
omit [FiniteDimensional K V] [Finite K] [Finite V] in
@[simp]
theorem evenCompletedSpace_last (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (c : EvenCompletionCoordinates k P) :
    evenCompletedSpace k P c (Fin.last (2 * k + 1)) = ⊤ := by
  simp [evenCompletedSpace]


-- @@ L510-574 verbatim
/-- Every coordinate tuple over an even partial flag assembles into a
complete flag.  This is the formal independence assertion for the missing
odd ranks. -/
noncomputable def completeFlagOfEvenCoordinates (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (c : EvenCompletionCoordinates k P) : CompleteFlag K V (2 * k + 1) :=
  completeFlagOfRankedSpaces (evenCompletedSpace k P c) (by
    intro i
    by_cases hi : i.val % 2 = 0
    · rw [evenCompletedSpace_of_even k P c i hi]
      exact partialFlag_finrank_space_of_mod P i hi
    · have hiOdd : i.val % 2 = 1 := by omega
      by_cases hlast : i.val = 2 * k + 1
      · have hiLast : i = Fin.last (2 * k + 1) := by
          apply Fin.ext
          simpa using hlast
        rw [hiLast, evenCompletedSpace_last, finrank_top,
          finrank_eq_of_partialFlag P]
        simp
      · let j : Fin k := ⟨i.val / 2, by omega⟩
        have hij : i = oddMiddleRank k j := by
          apply Fin.ext
          simp [j, oddMiddleRank]
          omega
        rw [hij, evenCompletedSpace_oddMiddle,
          (c j).finrank_space,
          partialFlag_finrank_space_of_mod P (evenLowerRank k j) (by simp)]
        simp [evenLowerRank, oddMiddleRank]) (by
    intro i
    by_cases hi : i.val % 2 = 0
    · have hiNext : (i.val + 1) % 2 ≠ 0 := by omega
      by_cases hlast : i.val + 1 = 2 * k + 1
      · simp [evenCompletedSpace, hi, hlast]
      · let j : Fin k := ⟨i.val / 2, by omega⟩
        have hsource : i.castSucc = evenLowerRank k j := by
          apply Fin.ext
          simp [j, evenLowerRank]
          omega
        have htarget : i.succ = oddMiddleRank k j := by
          apply Fin.ext
          simp [j, oddMiddleRank]
          omega
        rw [hsource, htarget, evenCompletedSpace_of_even,
          evenCompletedSpace_oddMiddle]
        · exact (c j).lower
        · simp [evenLowerRank]
    · have hiOdd : i.val % 2 = 1 := by omega
      let j : Fin k := ⟨i.val / 2, by omega⟩
      have hsource : i.castSucc = oddMiddleRank k j := by
        apply Fin.ext
        simp [j, oddMiddleRank]
        omega
      have htarget : i.succ = evenUpperRank k j := by
        apply Fin.ext
        simp [j, evenUpperRank]
        omega
      rw [hsource, htarget, evenCompletedSpace_oddMiddle,
        evenCompletedSpace_of_even]
      · exact (c j).upper
      · simp [evenUpperRank]) (by
    rw [evenCompletedSpace_of_even]
    · obtain ⟨F, hF⟩ := P.property
      have hPF : PartialFlag.ofComplete 0 F = P := Subtype.ext hF
      rw [← ofComplete_space_eq_of_mod hPF 0 (by simp), F.space_zero]
    · simp) (evenCompletedSpace_last k P c)


-- @@ L576-581 verbatim
omit [FiniteDimensional K V] [Finite K] [Finite V] in
@[simp]
theorem completeFlagOfEvenCoordinates_apply (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (c : EvenCompletionCoordinates k P) (i : Fin ((2 * k + 1) + 1)) :
    completeFlagOfEvenCoordinates k P c i = evenCompletedSpace k P c i := rfl


-- @@ L583-593 verbatim
omit [FiniteDimensional K V] [Finite K] [Finite V] in
theorem completeFlagOfEvenCoordinates_evenPart (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (c : EvenCompletionCoordinates k P) :
    PartialFlag.ofComplete 0 (completeFlagOfEvenCoordinates k P c) = P := by
  apply PartialFlag.ext
  intro i
  by_cases hi : i.val % 2 = 0
  · simp [PartialFlag.ofComplete, flagPart, hi]
  · rw [partialFlag_space_eq_bot_of_mod_ne P i (by simpa using hi)]
    simp [PartialFlag.ofComplete, flagPart, hi]


-- @@ L595-602 verbatim
/-- The compatible odd part assembled from an arbitrary coordinate tuple. -/
noncomputable def oddCompatibleOfEvenCoordinates (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (c : EvenCompletionCoordinates k P) :
    {Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q} :=
  ⟨PartialFlag.ofComplete 1 (completeFlagOfEvenCoordinates k P c),
    completeFlagOfEvenCoordinates k P c,
    completeFlagOfEvenCoordinates_evenPart k P c, rfl⟩


-- @@ L604-619 verbatim
omit [FiniteDimensional K V] [Finite K] [Finite V] in
theorem evenCompletionCoordinates_rightInverse (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :
    Function.RightInverse (oddCompatibleOfEvenCoordinates k P)
      (evenCompletionCoordinates k P) := by
  intro c
  funext j
  apply IntermediateSubspace.ext
  let x := oddCompatibleOfEvenCoordinates k P c
  have hchosen : completeOfEvenCompatibility k P x =
      completeFlagOfEvenCoordinates k P c :=
    compatible_unique
      (completeOfEvenCompatibility_even k P x)
      (completeOfEvenCompatibility_odd k P x)
      (completeFlagOfEvenCoordinates_evenPart k P c) rfl
  simp [x, hchosen]


-- @@ L621-631 verbatim
/-- Compatible odd parts are exactly independent products of the `k`
rank-two intervals. -/
noncomputable def evenCompletionEquiv (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :
    {Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q} ≃
      EvenCompletionCoordinates k P where
  toFun := evenCompletionCoordinates k P
  invFun := oddCompatibleOfEvenCoordinates k P
  left_inv x := (evenCompletionCoordinates_injective k P)
    (evenCompletionCoordinates_rightInverse k P (evenCompletionCoordinates k P x))
  right_inv := evenCompletionCoordinates_rightInverse k P


-- @@ L633-650 verbatim
/-- An even partial flag has exactly `(q+1)^k` compatible odd parts. -/
theorem natCard_odd_compatible_eq (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :
    Nat.card {Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q} =
      (Nat.card K + 1) ^ k := by
  calc
    Nat.card {Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q} =
        Nat.card (EvenCompletionCoordinates k P) :=
      Nat.card_congr (evenCompletionEquiv k P)
    _ = ∏ j : Fin k, Nat.card
          (IntermediateSubspace (P.1 (evenLowerRank k j)) (P.1 (evenUpperRank k j))) :=
      Nat.card_pi
    _ = ∏ _j : Fin k, (Nat.card K + 1) := by
      apply Finset.prod_congr rfl
      intro j _hj
      exact natCard_intermediate_eq
        (evenBoundary_le k P j) (evenBoundary_finrank k P j)
    _ = (Nat.card K + 1) ^ k := by simp


-- @@ L652-659 verbatim
/-- The upper bound as a direct corollary of the exact completion count. -/
theorem natCard_odd_compatible_le (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :
    Nat.card {Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q} ≤
      (Nat.card K + 1) ^ k := by
  exact (natCard_odd_compatible_eq k P).le

/- The dual-parity completion count. -/


-- @@ L661-665 verbatim
/-- Independent intermediate-subspace choices that complete an odd partial flag. -/
abbrev OddCompletionCoordinates (k : ℕ)
    (Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :=
  ∀ j : Fin k,
    IntermediateSubspace (Q.1 (oddLowerRank k j)) (Q.1 (oddUpperRank k j))


-- @@ L667-672 verbatim
/-- Choose the complete flag witnessing compatibility with the given odd partial flag. -/
noncomputable def completeOfOddCompatibility (k : ℕ)
    (Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (x : {P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q}) :
    CompleteFlag K V (2 * k + 1) :=
  Classical.choose x.property


-- @@ L674-679 verbatim
omit [FiniteDimensional K V] [Finite K] [Finite V] in
theorem completeOfOddCompatibility_even (k : ℕ)
    (Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (x : {P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q}) :
    PartialFlag.ofComplete 0 (completeOfOddCompatibility k Q x) = x.1 :=
  (Classical.choose_spec x.property).1


-- @@ L681-686 verbatim
omit [FiniteDimensional K V] [Finite K] [Finite V] in
theorem completeOfOddCompatibility_odd (k : ℕ)
    (Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (x : {P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q}) :
    PartialFlag.ofComplete 1 (completeOfOddCompatibility k Q x) = Q :=
  (Classical.choose_spec x.property).2


-- @@ L688-709 verbatim
/-- Extract each intermediate subspace from a compatible even partial flag. -/
noncomputable def oddCompletionCoordinates (k : ℕ)
    (Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :
    {P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q} →
      OddCompletionCoordinates k Q :=
  fun x j ↦ by
    let F := completeOfOddCompatibility k Q x
    have hOdd := completeOfOddCompatibility_odd k Q x
    have hlow : F (oddLowerRank k j) = Q.1 (oddLowerRank k j) :=
      ofComplete_space_eq_of_mod hOdd _ (by simp [oddLowerRank])
    have hhigh : F (oddUpperRank k j) = Q.1 (oddUpperRank k j) :=
      ofComplete_space_eq_of_mod hOdd _ (by simp [oddUpperRank])
    refine ⟨F (evenMiddleRank k j), ?_, ?_, ?_⟩
    · rw [← hlow]
      exact F.strictMono_space.monotone (by simp [oddLowerRank, evenMiddleRank])
    · rw [← hhigh]
      exact F.strictMono_space.monotone (by simp [evenMiddleRank, oddUpperRank])
    · rw [F.finrank_space]
      have hlowrank := F.finrank_space (oddLowerRank k j)
      rw [hlow] at hlowrank
      rw [hlowrank]
      simp [evenMiddleRank, oddLowerRank]


-- @@ L711-718 verbatim
omit [FiniteDimensional K V] [Finite K] [Finite V] in
@[simp]
theorem oddCompletionCoordinates_space (k : ℕ)
    (Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (x : {P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q})
    (j : Fin k) :
    (oddCompletionCoordinates k Q x j).space =
      completeOfOddCompatibility k Q x (evenMiddleRank k j) := rfl


-- @@ L720-751 verbatim
omit [FiniteDimensional K V] [Finite K] [Finite V] in
theorem oddCompletionCoordinates_injective (k : ℕ)
    (Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :
    Function.Injective (oddCompletionCoordinates k Q) := by
  intro x y hxy
  let F := completeOfOddCompatibility k Q x
  let G := completeOfOddCompatibility k Q y
  have hOddF := completeOfOddCompatibility_odd k Q x
  have hOddG := completeOfOddCompatibility_odd k Q y
  have hFG : F = G := by
    apply CompleteFlag.ext
    intro i
    by_cases hi : i.val % 2 = 1
    · exact (ofComplete_space_eq_of_mod hOddF i hi).trans
        (ofComplete_space_eq_of_mod hOddG i hi).symm
    · have hiEven : i.val % 2 = 0 := by omega
      by_cases hzero : i.val = 0
      · have hiZero : i = 0 := by ext; simpa using hzero
        rw [hiZero, F.space_zero, G.space_zero]
      · let j : Fin k := ⟨i.val / 2 - 1, by omega⟩
        have hij : i = evenMiddleRank k j := by
          apply Fin.ext
          simp [j, evenMiddleRank]
          omega
        have hs := congrArg (fun c ↦ (c j).space) hxy
        simpa [F, G, hij] using hs
  apply Subtype.ext
  calc
    x.1 = PartialFlag.ofComplete 0 F :=
      (completeOfOddCompatibility_even k Q x).symm
    _ = PartialFlag.ofComplete 0 G := congrArg (PartialFlag.ofComplete 0) hFG
    _ = y.1 := completeOfOddCompatibility_even k Q y


-- @@ L753-761 verbatim
omit [FiniteDimensional K V] [Finite K] [Finite V] in
theorem oddBoundary_le (k : ℕ)
    (Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1)) (j : Fin k) :
    Q.1 (oddLowerRank k j) ≤ Q.1 (oddUpperRank k j) := by
  obtain ⟨F, hF⟩ := Q.property
  have hQF : PartialFlag.ofComplete 1 F = Q := Subtype.ext hF
  rw [← ofComplete_space_eq_of_mod hQF _ (by simp [oddLowerRank]),
    ← ofComplete_space_eq_of_mod hQF _ (by simp [oddUpperRank])]
  exact F.strictMono_space.monotone (by simp [oddLowerRank, oddUpperRank])


-- @@ L763-773 verbatim
omit [FiniteDimensional K V] [Finite K] [Finite V] in
theorem oddBoundary_finrank (k : ℕ)
    (Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1)) (j : Fin k) :
    finrank K (Q.1 (oddUpperRank k j)) =
      finrank K (Q.1 (oddLowerRank k j)) + 2 := by
  obtain ⟨F, hF⟩ := Q.property
  have hQF : PartialFlag.ofComplete 1 F = Q := Subtype.ext hF
  rw [← ofComplete_space_eq_of_mod hQF _ (by simp),
    ← ofComplete_space_eq_of_mod hQF _ (by simp),
    F.finrank_space, F.finrank_space]
  simp [oddLowerRank, oddUpperRank]


-- @@ L775-783 verbatim
/-- Interleave arbitrary positive-even-rank choices in the rank-two
intervals of an odd partial flag; rank zero is the bottom space. -/
def oddCompletedSpace (k : ℕ)
    (Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (c : OddCompletionCoordinates k Q) :
    Fin ((2 * k + 1) + 1) → Submodule K V := fun i ↦
  if hi : i.val % 2 = 1 then Q.1 i
  else if _hzero : i.val = 0 then ⊥
  else (c ⟨i.val / 2 - 1, by omega⟩).space


-- @@ L785-791 verbatim
omit [FiniteDimensional K V] [Finite K] [Finite V] in
@[simp]
theorem oddCompletedSpace_of_odd (k : ℕ)
    (Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (c : OddCompletionCoordinates k Q) (i : Fin ((2 * k + 1) + 1))
    (hi : i.val % 2 = 1) : oddCompletedSpace k Q c i = Q.1 i := by
  simp [oddCompletedSpace, hi]


-- @@ L793-810 verbatim
omit [FiniteDimensional K V] [Finite K] [Finite V] in
@[simp]
theorem oddCompletedSpace_evenMiddle (k : ℕ)
    (Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (c : OddCompletionCoordinates k Q) (j : Fin k) :
    oddCompletedSpace k Q c (evenMiddleRank k j) = (c j).space := by
  have hparity : (evenMiddleRank k j).val % 2 ≠ 1 := by
    simp [evenMiddleRank]
  have hzero : (evenMiddleRank k j).val ≠ 0 := by
    simp [evenMiddleRank]
  have hindex :
      (⟨(evenMiddleRank k j).val / 2 - 1, by omega⟩ : Fin k) = j := by
    apply Fin.ext
    change (2 * j.val + 2) / 2 - 1 = j.val
    rw [Nat.mul_add_div (by omega)]
    simp
  unfold oddCompletedSpace
  rw [dite_eq_right hparity, dite_eq_right hzero, hindex]


-- @@ L812-817 verbatim
omit [FiniteDimensional K V] [Finite K] [Finite V] in
@[simp]
theorem oddCompletedSpace_zero (k : ℕ)
    (Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (c : OddCompletionCoordinates k Q) : oddCompletedSpace k Q c 0 = ⊥ := by
  simp [oddCompletedSpace]


-- @@ L819-885 verbatim
/-- Every coordinate tuple over an odd partial flag assembles into a
complete flag.  This is the dual formal independence assertion. -/
noncomputable def completeFlagOfOddCoordinates (k : ℕ)
    (Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (c : OddCompletionCoordinates k Q) : CompleteFlag K V (2 * k + 1) :=
  completeFlagOfRankedSpaces (oddCompletedSpace k Q c) (by
    intro i
    by_cases hi : i.val % 2 = 1
    · rw [oddCompletedSpace_of_odd k Q c i hi]
      exact partialFlag_finrank_space_of_mod Q i hi
    · have hiEven : i.val % 2 = 0 := by omega
      by_cases hzero : i.val = 0
      · have hiZero : i = 0 := by
          apply Fin.ext
          simpa using hzero
        rw [hiZero, oddCompletedSpace_zero, finrank_bot]
        simp
      · let j : Fin k := ⟨i.val / 2 - 1, by omega⟩
        have hij : i = evenMiddleRank k j := by
          apply Fin.ext
          simp [j, evenMiddleRank]
          omega
        rw [hij, oddCompletedSpace_evenMiddle,
          (c j).finrank_space,
          partialFlag_finrank_space_of_mod Q (oddLowerRank k j) (by simp)]
        simp [oddLowerRank, evenMiddleRank]) (by
    intro i
    by_cases hi : i.val % 2 = 0
    · by_cases hzero : i.val = 0
      · have hsource : i.castSucc = 0 := by
          apply Fin.ext
          simpa using hzero
        rw [hsource, oddCompletedSpace_zero]
        exact bot_le
      · let j : Fin k := ⟨i.val / 2 - 1, by omega⟩
        have hsource : i.castSucc = evenMiddleRank k j := by
          apply Fin.ext
          simp [j, evenMiddleRank]
          omega
        have htarget : i.succ = oddUpperRank k j := by
          apply Fin.ext
          simp [j, oddUpperRank]
          omega
        rw [hsource, htarget, oddCompletedSpace_evenMiddle,
          oddCompletedSpace_of_odd]
        · exact (c j).upper
        · simp [oddUpperRank]
    · have hiOdd : i.val % 2 = 1 := by omega
      let j : Fin k := ⟨i.val / 2, by omega⟩
      have hsource : i.castSucc = oddLowerRank k j := by
        apply Fin.ext
        simp [j, oddLowerRank]
        omega
      have htarget : i.succ = evenMiddleRank k j := by
        apply Fin.ext
        simp [j, evenMiddleRank]
        omega
      rw [hsource, htarget, oddCompletedSpace_of_odd,
        oddCompletedSpace_evenMiddle]
      · exact (c j).lower
      · simp [oddLowerRank]) (oddCompletedSpace_zero k Q c) (by
    rw [oddCompletedSpace_of_odd]
    · obtain ⟨F, hF⟩ := Q.property
      have hQF : PartialFlag.ofComplete 1 F = Q := Subtype.ext hF
      rw [← ofComplete_space_eq_of_mod hQF (Fin.last (2 * k + 1)) (by simp),
        F.space_last]
    · simp)


-- @@ L887-892 verbatim
omit [FiniteDimensional K V] [Finite K] [Finite V] in
@[simp]
theorem completeFlagOfOddCoordinates_apply (k : ℕ)
    (Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (c : OddCompletionCoordinates k Q) (i : Fin ((2 * k + 1) + 1)) :
    completeFlagOfOddCoordinates k Q c i = oddCompletedSpace k Q c i := rfl


-- @@ L894-904 verbatim
omit [FiniteDimensional K V] [Finite K] [Finite V] in
theorem completeFlagOfOddCoordinates_oddPart (k : ℕ)
    (Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (c : OddCompletionCoordinates k Q) :
    PartialFlag.ofComplete 1 (completeFlagOfOddCoordinates k Q c) = Q := by
  apply PartialFlag.ext
  intro i
  by_cases hi : i.val % 2 = 1
  · simp [PartialFlag.ofComplete, flagPart, hi]
  · rw [partialFlag_space_eq_bot_of_mod_ne Q i (by simpa using hi)]
    simp [PartialFlag.ofComplete, flagPart, hi]


-- @@ L906-913 verbatim
/-- The compatible even part assembled from an arbitrary coordinate tuple. -/
noncomputable def evenCompatibleOfOddCoordinates (k : ℕ)
    (Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (c : OddCompletionCoordinates k Q) :
    {P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q} :=
  ⟨PartialFlag.ofComplete 0 (completeFlagOfOddCoordinates k Q c),
    completeFlagOfOddCoordinates k Q c, rfl,
    completeFlagOfOddCoordinates_oddPart k Q c⟩


-- @@ L915-930 verbatim
omit [FiniteDimensional K V] [Finite K] [Finite V] in
theorem oddCompletionCoordinates_rightInverse (k : ℕ)
    (Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :
    Function.RightInverse (evenCompatibleOfOddCoordinates k Q)
      (oddCompletionCoordinates k Q) := by
  intro c
  funext j
  apply IntermediateSubspace.ext
  let x := evenCompatibleOfOddCoordinates k Q c
  have hchosen : completeOfOddCompatibility k Q x =
      completeFlagOfOddCoordinates k Q c :=
    compatible_unique
      (completeOfOddCompatibility_even k Q x)
      (completeOfOddCompatibility_odd k Q x) rfl
      (completeFlagOfOddCoordinates_oddPart k Q c)
  simp [x, hchosen]


-- @@ L932-942 verbatim
/-- Compatible even parts are exactly independent products of the `k`
rank-two intervals. -/
noncomputable def oddCompletionEquiv (k : ℕ)
    (Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :
    {P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q} ≃
      OddCompletionCoordinates k Q where
  toFun := oddCompletionCoordinates k Q
  invFun := evenCompatibleOfOddCoordinates k Q
  left_inv x := (oddCompletionCoordinates_injective k Q)
    (oddCompletionCoordinates_rightInverse k Q (oddCompletionCoordinates k Q x))
  right_inv := oddCompletionCoordinates_rightInverse k Q


-- @@ L944-961 verbatim
/-- An odd partial flag has exactly `(q+1)^k` compatible even parts. -/
theorem natCard_even_compatible_eq (k : ℕ)
    (Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :
    Nat.card {P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q} =
      (Nat.card K + 1) ^ k := by
  calc
    Nat.card {P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q} =
        Nat.card (OddCompletionCoordinates k Q) :=
      Nat.card_congr (oddCompletionEquiv k Q)
    _ = ∏ j : Fin k, Nat.card
          (IntermediateSubspace (Q.1 (oddLowerRank k j)) (Q.1 (oddUpperRank k j))) :=
      Nat.card_pi
    _ = ∏ _j : Fin k, (Nat.card K + 1) := by
      apply Finset.prod_congr rfl
      intro j _hj
      exact natCard_intermediate_eq
        (oddBoundary_le k Q j) (oddBoundary_finrank k Q j)
    _ = (Nat.card K + 1) ^ k := by simp


-- @@ L963-968 verbatim
/-- The dual upper bound as a direct corollary of the exact completion count. -/
theorem natCard_even_compatible_le (k : ℕ)
    (Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :
    Nat.card {P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q} ≤
      (Nat.card K + 1) ^ k := by
  exact (natCard_even_compatible_eq k Q).le


-- @@ L970-977 verbatim
/-- A neighbor is encoded by a compatible odd part and then by an even part
compatible with that odd part.  We deliberately keep all such pairs, rather
than assuming that a neighbor has a unique common odd part. -/
abbrev NeighborEncoding (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :=
  Σ q : {Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q},
    {P' : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1) //
      P' ∈ ({R | Compatible R q.1} \ {P} : Set _)}


-- @@ L979-988 verbatim
/-- Encode a graph neighbor by a shared odd flag and a distinct compatible even flag. -/
noncomputable def encodeNeighbor (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :
    (halvedFlagGraph (K := K) (V := V) (n := 2 * k + 1)).neighborSet P →
      NeighborEncoding k P :=
  fun P' ↦ by
    have ha := (halvedFlagGraph_adj_iff (K := K) (V := V)).mp P'.property
    let Q := Classical.choose ha.2
    have hQ := Classical.choose_spec ha.2
    exact ⟨⟨Q, hQ.1⟩, ⟨P'.1, hQ.2, by simpa using ha.1.symm⟩⟩


-- @@ L990-997 verbatim
omit [FiniteDimensional K V] [Finite K] [Finite V] in
theorem encodeNeighbor_injective (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :
    Function.Injective (encodeNeighbor k P) := by
  intro P' P'' h
  apply Subtype.ext
  have hs := congrArg (fun z : NeighborEncoding k P ↦ z.2.1) h
  simpa [encodeNeighbor] using hs


-- @@ L999-1027 verbatim
/-- The paper's neighbor-set cap `A(A-1)`, where `A = (q+1)^k`.  It does not
count a neighbor twice or posit uniqueness of its common odd flag: the
injection chooses one witness, and its second coordinate excludes the original
vertex from the at-most-`A` compatible even parts. -/
theorem halvedFlagGraph_natCard_neighborSet_le_sharp (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :
    Nat.card ((halvedFlagGraph (K := K) (V := V) (n := 2 * k + 1)).neighborSet P) ≤
      ((Nat.card K + 1) ^ k) * (((Nat.card K + 1) ^ k) - 1) := by
  let A := (Nat.card K + 1) ^ k
  let Base := {Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q}
  let : Fintype Base := Fintype.ofFinite _
  calc
    Nat.card ((halvedFlagGraph (K := K) (V := V) (n := 2 * k + 1)).neighborSet P) ≤
        Nat.card (NeighborEncoding k P) :=
      Nat.card_le_card_of_injective (encodeNeighbor k P) (encodeNeighbor_injective k P)
    _ = ∑ q : Base, Nat.card
          {P' : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1) //
            P' ∈ ({R | Compatible R q.1} \ {P} : Set _)} :=
      Nat.card_sigma
    _ ≤ ∑ _q : Base, (A - 1) := by
      exact Finset.sum_le_sum fun q _ ↦ by
        rw [Nat.card_coe_set_eq,
          Set.ncard_sdiff_singleton_of_mem
            (show P ∈ {R | Compatible R q.1} from q.2)]
        exact Nat.sub_le_sub_right (natCard_even_compatible_le k q.1) 1
    _ = Nat.card Base * (A - 1) := by
      simp [Nat.card_eq_fintype_card]
    _ ≤ A * (A - 1) := Nat.mul_le_mul_right (A - 1) (natCard_odd_compatible_le k P)
    _ = ((Nat.card K + 1) ^ k) * (((Nat.card K + 1) ^ k) - 1) := rfl


-- @@ L1029-1035 verbatim
/-- The coarser square cap retained as a convenient corollary. -/
theorem halvedFlagGraph_natCard_neighborSet_le (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :
    Nat.card ((halvedFlagGraph (K := K) (V := V) (n := 2 * k + 1)).neighborSet P) ≤
      ((Nat.card K + 1) ^ k) * ((Nat.card K + 1) ^ k) := by
  exact (halvedFlagGraph_natCard_neighborSet_le_sharp k P).trans
    (Nat.mul_le_mul_left _ (Nat.sub_le _ _))


-- @@ L1037-1044 verbatim
theorem halvedFlagGraph_degree_le (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    [Fintype ((halvedFlagGraph (K := K) (V := V) (n := 2 * k + 1)).neighborSet P)] :
    (halvedFlagGraph (K := K) (V := V) (n := 2 * k + 1)).degree P ≤
      ((Nat.card K + 1) ^ k) * ((Nat.card K + 1) ^ k) := by
  rw [← (halvedFlagGraph (K := K) (V := V) (n := 2 * k + 1)).card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card]
  exact halvedFlagGraph_natCard_neighborSet_le k P


-- @@ L1046-1046 verbatim
end PartialFlagCompletions


-- @@ L1048-1048 verbatim
end DegreeDiameter


-- @@ L1050-1050 verbatim
end MooreBound
