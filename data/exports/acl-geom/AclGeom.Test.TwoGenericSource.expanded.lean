/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Correspondence.GenericExtension
import AclGeom.Reconstruct.TwoGeneric
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.RatFunc.AsPolynomial


-- @@ L12-35 verbatim
/-!
# Validation: the embedded assertions of the original two-generic proof

The original proof of blueprint Lemma `two-generic-intersection` works in an ambient field `Ω`
over `K` with `Ē` the closure of `E = acl_k(x) ∩ K` in `Ω`, and makes the following embedded
assertions (#9).  Each is checked here from the lemma's own hypotheses, `s ∉ acl(x)` and
`t ∉ acl(x, s)` in `K`. No linear-disjointness, transcendence or embedding-extension
conclusion is an input; the embedding `τ` to be extended is an explicit source variable.

* A0: `acl(t, tx) = acl(E(t))` in `Ω`;
* A1: `Ē(t)` and `Ē(s)` are linearly disjoint over `Ē`
  (`linearDisjoint_adjoin_simple_of_transcendental`);
* A2: the closures of `Ē(t)` and `Ē(s)` in `Ω` meet in `Ē` (`racl_insert_inf_racl_insert`);
* A3: for a normal extension `N` of `Ē(t)`, `N` and `Ē(s)` are linearly disjoint over `Ē`, and
  every `Ē(t)`-embedding of `N` extends to `N(s)` fixing `Ē(s)` pointwise.  The source cites the
  linear disjointness A1 for this step; the stronger disjointness of `N` is what is used;
* A4: an element algebraic over both `Ē(t)` and `Ē(s)` lies in `Ē`.  This conclusion is derived
  from A2; the source's conjugate-comparison route to it is not transcribed;
* A5: `Ē ∩ K = E` (`algHom_mem_racl_image_iff`);
* the normal envelope used by A3: in an algebraically closed `Ω`, an element algebraic over
  `Ē(t)` lies in a finite normal extension of `Ē(t)` (`normalClosure` of `Ē(t)⟮z⟯`).

**Status:** validation fixtures (#9).
-/


-- @@ L37-37 verbatim
namespace AclGeom


-- @@ L39-39 verbatim
open IntermediateField


-- @@ L41-41 verbatim
noncomputable section


-- @@ L43-44 verbatim
variable {k K Ω : Type*} [Field k] [Field K] [Field Ω] [Algebra k K] [Algebra k Ω]
  [Algebra K Ω] [IsScalarTower k K Ω]


-- @@ L46-46 verbatim
local notation "ι" => IsScalarTower.toAlgHom k K Ω


-- @@ L48-51 verbatim
/-- A5: `Ē ∩ K = E`. -/
private theorem twoGeneric_A5 (x y : K) :
    ι y ∈ racl k ({ι x} : Set Ω) ↔ y ∈ racl k ({x} : Set K) := by
  rw [← Set.image_singleton, algHom_mem_racl_image_iff]


-- @@ L53-59 verbatim
/-- Closure absorption: `acl(Ē ∪ {a}) = acl(x, a)` in `Ω`. -/
private theorem racl_insert_closure (x : K) (a : Ω) :
    racl k (insert a (racl k ({ι x} : Set Ω) : Set Ω)) = racl k ({a, ι x} : Set Ω) := by
  apply racl_congr_of_subset_racl
  · exact Set.insert_subset (subset_racl k _ (Set.mem_insert _ _))
      (racl_mono (Set.subset_insert a _))
  · exact (Set.insert_subset_insert (subset_racl k _)).trans (subset_racl k _)


-- @@ L61-80 verbatim
/-- A0: `acl(t, tx) = acl(E(t))` in `Ω`. -/
private theorem twoGeneric_A0 {x t : K} (ht0 : t ≠ 0) :
    racl k ({ι t, ι t * ι x} : Set Ω) =
      racl k (insert (ι t) (ι '' (racl k ({x} : Set K) : Set K))) := by
  have ht0' : ι t ≠ 0 := (map_ne_zero ι).2 ht0
  apply racl_congr_of_subset_racl
  · rintro z (rfl | rfl)
    · exact subset_racl k _ (Set.mem_insert _ _)
    · exact mul_mem (subset_racl k _ (Set.mem_insert _ _))
        (subset_racl k _ (Set.mem_insert_of_mem _ ⟨x, subset_racl k _ rfl, rfl⟩))
  · rintro z (rfl | ⟨w, hw, rfl⟩)
    · exact subset_racl k _ (Set.mem_insert _ _)
    · have hx : ι x ∈ racl k ({ι t, ι t * ι x} : Set Ω) := by
        have h1 : ι t * ι x ∈ racl k ({ι t, ι t * ι x} : Set Ω) := subset_racl k _ (by simp)
        have h := div_mem h1 (subset_racl k ({ι t, ι t * ι x} : Set Ω) (Set.mem_insert _ _))
        rwa [mul_div_cancel_left₀ _ ht0'] at h
      have hw' : ι w ∈ racl k ({ι x} : Set Ω) := by
        rw [← Set.image_singleton]
        exact (algHom_mem_racl_image_iff ι).2 hw
      exact racl_le_of_subset_racl (Set.singleton_subset_iff.2 hx) hw'


-- @@ L82-87 verbatim
/-- Independence in `K` gives `t ∉ acl(Ē, s)` in `Ω`. -/
private theorem notMem_racl_insert_closure {x s t : K} (ht : t ∉ racl k ({x, s} : Set K)) :
    ι t ∉ racl k (insert (ι s) (racl k ({ι x} : Set Ω) : Set Ω)) := by
  rw [racl_insert_closure, Set.pair_comm, ← Set.image_singleton, ← Set.image_insert_eq,
    algHom_mem_racl_image_iff]
  exact ht


-- @@ L89-94 verbatim
/-- A2: the closures of `Ē(t)` and `Ē(s)` in `Ω` meet in `Ē`. -/
private theorem twoGeneric_A2 {x s t : K} (ht : t ∉ racl k ({x, s} : Set K)) :
    racl k (insert (ι t) (racl k ({ι x} : Set Ω) : Set Ω)) ⊓
        racl k (insert (ι s) (racl k ({ι x} : Set Ω) : Set Ω)) =
      racl k ({ι x} : Set Ω) := by
  rw [racl_insert_inf_racl_insert (notMem_racl_insert_closure ht), racl_racl]


-- @@ L96-102 verbatim
/-- Exchange: `s ∉ acl(x)` and `t ∉ acl(x, s)` give `s ∉ acl(x, t)`. -/
private theorem notMem_racl_swap {x s t : K} (hs : s ∉ racl k ({x} : Set K))
    (ht : t ∉ racl k ({x, s} : Set K)) : s ∉ racl k ({x, t} : Set K) := by
  intro hst
  refine hs (mem_racl_of_mem_racl_insert (a := s) (b := t) (subset_racl k _ (by simp)) ?_ ?_)
  · rwa [Set.pair_comm] at hst
  · rwa [Set.pair_comm] at ht


-- @@ L104-109 verbatim
/-- Algebraicity over `Ē(a)` is membership in the closure of `Ē ∪ {a}`. -/
private theorem mem_racl_insert_of_isAlgebraic {x : K} {a z : Ω}
    (h : IsAlgebraic (adjoin (racl k ({ι x} : Set Ω)) {a}) z) :
    z ∈ racl k (insert a (racl k ({ι x} : Set Ω) : Set Ω)) := by
  rw [mem_racl_iff, ← Set.union_singleton, ← restrictScalars_adjoin]
  exact h


-- @@ L111-118 verbatim
/-- A4: an element algebraic over both `Ē(t)` and `Ē(s)` lies in `Ē`. -/
private theorem twoGeneric_A4 {x s t : K} (ht : t ∉ racl k ({x, s} : Set K)) {z : Ω}
    (hzt : IsAlgebraic (adjoin (racl k ({ι x} : Set Ω)) {ι t}) z)
    (hzs : IsAlgebraic (adjoin (racl k ({ι x} : Set Ω)) {ι s}) z) :
    z ∈ racl k ({ι x} : Set Ω) := by
  rw [← twoGeneric_A2 ht]
  exact IntermediateField.mem_inf.2
    ⟨mem_racl_insert_of_isAlgebraic hzt, mem_racl_insert_of_isAlgebraic hzs⟩


-- @@ L120-126 verbatim
/-- `s` is transcendental over `Ē(t)`. -/
private theorem transcendental_adjoin_closure {x s t : K} (hs : s ∉ racl k ({x} : Set K))
    (ht : t ∉ racl k ({x, s} : Set K)) :
    Transcendental (adjoin (racl k ({ι x} : Set Ω)) {ι t}) (ι s) := by
  intro halg
  exact notMem_racl_insert_closure (Ω := Ω) (notMem_racl_swap hs ht)
    (mem_racl_insert_of_isAlgebraic halg)


-- @@ L128-133 verbatim
/-- A1: `Ē(t)` and `Ē(s)` are linearly disjoint over `Ē`. -/
private theorem twoGeneric_A1 {x s t : K} (hs : s ∉ racl k ({x} : Set K))
    (ht : t ∉ racl k ({x, s} : Set K)) :
    (adjoin (racl k ({ι x} : Set Ω)) {ι t}).LinearDisjoint
      (adjoin (racl k ({ι x} : Set Ω)) {ι s}) :=
  linearDisjoint_adjoin_simple_of_transcendental _ (transcendental_adjoin_closure hs ht)


-- @@ L135-142 verbatim
/-- `s` stays transcendental over an algebraic extension `N` of `Ē(t)`. -/
private theorem transcendental_of_isAlgebraic {x s t : K} (hs : s ∉ racl k ({x} : Set K))
    (ht : t ∉ racl k ({x, s} : Set K))
    (N : IntermediateField (adjoin (racl k ({ι x} : Set Ω)) {ι t}) Ω)
    (hN : Algebra.IsAlgebraic (adjoin (racl k ({ι x} : Set Ω)) {ι t}) N) :
    Transcendental N (ι s) := by
  have := hN
  exact (transcendental_adjoin_closure hs ht).extendScalars N


-- @@ L144-152 verbatim
/-- A3, linear disjointness: an algebraic extension `N` of `Ē(t)` is linearly disjoint from
`Ē(s)` over `Ē`. -/
private theorem twoGeneric_A3_linearDisjoint {x s t : K} (hs : s ∉ racl k ({x} : Set K))
    (ht : t ∉ racl k ({x, s} : Set K))
    (N : IntermediateField (adjoin (racl k ({ι x} : Set Ω)) {ι t}) Ω)
    [Algebra.IsAlgebraic (adjoin (racl k ({ι x} : Set Ω)) {ι t}) N] :
    (N.restrictScalars (racl k ({ι x} : Set Ω))).LinearDisjoint
      (adjoin (racl k ({ι x} : Set Ω)) {ι s}) :=
  linearDisjoint_adjoin_simple_of_transcendental _ (transcendental_of_isAlgebraic hs ht N ‹_›)


-- @@ L154-217 verbatim
/-- A3, extension of embeddings: every `Ē(t)`-embedding `τ` of a normal extension `N` of `Ē(t)`
extends to `N(s)`, agreeing with `τ` on `N` and fixing `Ē(s)` pointwise.  Normality gives
`τ N = N`; `s` is transcendental over `N`, so `N(s) ≃ N(X)` (`RatFunc.algEquivOfTranscendental`)
and `τ` extends to rational functions.  The fixed elements form a subfield containing `Ē` and `s`.
-/
private theorem twoGeneric_A3_extension {x s t : K} (hs : s ∉ racl k ({x} : Set K))
    (ht : t ∉ racl k ({x, s} : Set K))
    (N : IntermediateField (adjoin (racl k ({ι x} : Set Ω)) {ι t}) Ω)
    [Normal (adjoin (racl k ({ι x} : Set Ω)) {ι t}) N]
    (τ : N →ₐ[adjoin (racl k ({ι x} : Set Ω)) {ι t}] Ω) :
    ∃ τ' : adjoin N {ι s} →+* Ω,
      (∀ n : N, τ' (algebraMap N (adjoin N {ι s}) n) = τ n) ∧
        ∀ (z : Ω) (hz : z ∈ adjoin N {ι s}),
          z ∈ adjoin (racl k ({ι x} : Set Ω)) {ι s} → τ' ⟨z, hz⟩ = z := by
  have hN : Transcendental N (ι s) := transcendental_of_isAlgebraic hs ht N Normal.toIsAlgebraic
  have hrange : ∀ n : N, τ n ∈ N := fun n ↦ by
    have hmem : τ n ∈ τ.fieldRange := ⟨n, rfl⟩
    rwa [AlgHom.fieldRange_of_normal τ] at hmem
  let σ : N →+* N := τ.toRingHom.codRestrict N hrange
  have hσ : (algebraMap N Ω).comp σ = τ.toRingHom := by
    ext n
    rfl
  let φ : Polynomial N →+* Ω := Polynomial.eval₂RingHom τ.toRingHom (ι s)
  have hφ : (nonZeroDivisors (Polynomial N)) ≤ (nonZeroDivisors Ω).comap φ := by
    intro p hp
    rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
    have hp0 : p ≠ 0 := nonZeroDivisors.ne_zero hp
    have hmap : p.map σ ≠ 0 :=
      (Polynomial.map_ne_zero_iff σ.injective).2 hp0
    change Polynomial.eval₂ τ.toRingHom (ι s) p ≠ 0
    rw [← hσ, ← Polynomial.eval₂_map, ← Polynomial.aeval_def]
    exact fun h0 ↦ hmap ((transcendental_iff.1 hN) _ h0)
  let e := RatFunc.algEquivOfTranscendental (K := N) (ι s) hN
  let τ' : adjoin N {ι s} →+* Ω := (RatFunc.liftRingHom φ hφ).comp e.symm.toRingHom
  have hagree : ∀ n : N, τ' (algebraMap N (adjoin N {ι s}) n) = τ n := fun n ↦ by
    have he : e.symm (algebraMap N (adjoin N {ι s}) n) = algebraMap N (RatFunc N) n :=
      e.symm.commutes n
    change RatFunc.liftRingHom φ hφ (e.symm (algebraMap N (adjoin N {ι s}) n)) = τ n
    rw [he, RatFunc.algebraMap_eq_C, ← RatFunc.algebraMap_C, RatFunc.liftRingHom_algebraMap]
    exact Polynomial.eval₂_C _ _
  have hgen : τ' (AdjoinSimple.gen N (ι s)) = ι s := by
    have he : e.symm (AdjoinSimple.gen N (ι s)) = RatFunc.X := by
      rw [AlgEquiv.symm_apply_eq]
      ext
      rw [AdjoinSimple.coe_gen, RatFunc.algEquivOfTranscendental_X]
    change RatFunc.liftRingHom φ hφ (e.symm (AdjoinSimple.gen N (ι s))) = ι s
    rw [he, RatFunc.liftRingHom_X]
    exact Polynomial.eval₂_X _ _
  refine ⟨τ', hagree, fun z hz hzs ↦ ?_⟩
  let S : Subfield Ω := (τ'.eqLocusField (algebraMap (adjoin N {ι s}) Ω)).map
    (algebraMap (adjoin N {ι s}) Ω)
  have hle : (adjoin (racl k ({ι x} : Set Ω)) {ι s}).toSubfield ≤ S := by
    rw [adjoin_toSubfield, Subfield.closure_le]
    rintro w (⟨c, rfl⟩ | rfl)
    · let r := algebraMap (racl k ({ι x} : Set Ω)) (adjoin (racl k ({ι x} : Set Ω)) {ι t}) c
      refine ⟨algebraMap N (adjoin N {ι s}) ⟨_, N.algebraMap_mem r⟩, ?_, rfl⟩
      change τ' (algebraMap N (adjoin N {ι s}) ⟨_, N.algebraMap_mem r⟩) = _
      rw [hagree]
      exact τ.commutes r
    · exact ⟨AdjoinSimple.gen N (ι s), hgen, rfl⟩
  obtain ⟨w, hw, hwz⟩ := Subfield.mem_map.1 (hle hzs)
  have hw' : w = ⟨z, hz⟩ := Subtype.ext hwz
  rw [← hw']
  exact hw.trans hwz


-- @@ L219-231 verbatim
/-- The normal envelope of the source's A3 step: in an algebraically closed `Ω`, an element
algebraic over `F` lies in a finite normal extension of `F` inside `Ω`, namely the normal closure
of `F⟮z⟯`.  The ambient `Ω` is not assumed normal over `F`. -/
private theorem twoGeneric_finite_normal_envelope {F Ω : Type*} [Field F] [Field Ω]
    [Algebra F Ω] [IsAlgClosed Ω] {z : Ω} (hz : IsAlgebraic F z) :
    ∃ N : IntermediateField F Ω, z ∈ N ∧ Normal F N ∧ FiniteDimensional F N := by
  have : FiniteDimensional F F⟮z⟯ :=
    IntermediateField.adjoin.finiteDimensional (isAlgebraic_iff_isIntegral.1 hz)
  have hN : IsNormalClosure F F⟮z⟯ (normalClosure F F⟮z⟯ Ω) :=
    Algebra.IsAlgebraic.isNormalClosure_normalClosure fun _ ↦ IsAlgClosed.splits _
  exact ⟨normalClosure F F⟮z⟯ Ω,
    IntermediateField.le_normalClosure _ (IntermediateField.mem_adjoin_simple_self F z),
    IsNormalClosure.normal (h := hN), inferInstance⟩


-- @@ L233-233 verbatim
end


-- @@ L235-235 verbatim
end AclGeom
