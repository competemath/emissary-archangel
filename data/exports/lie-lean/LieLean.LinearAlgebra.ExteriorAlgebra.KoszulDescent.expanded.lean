/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.LinearAlgebra.ExteriorAlgebra.KoszulExact
import LieLean.LinearAlgebra.ExteriorAlgebra.KoszulSupport


-- @@ L9-32 verbatim
/-!
# Koszul descent for differentials with leading term `-δ`

Let `M` be a module with a basis `b` indexed by `I`, and let `D` be an endomorphism of
`ΛM ⊗ R[I]` with `D ∘ D = 0` whose leading term is minus the Koszul differential: on tensors of
exterior degree `q` with polynomial coefficients of degree at most `n` (and finite exterior
support `s`), `D z + δ_s z` has exterior degree `q - 1` and coefficient degree at most `n`
(`IsLeadingKoszul`). Over a field of characteristic zero, every cycle of `D` of positive
exterior degree is a boundary, with a primitive of coefficient degree one less.

## Main definitions

* `ExteriorAlgebra.Koszul.rectangle`: exterior degree `q`, polynomial degree at most `n`.
* `ExteriorAlgebra.Koszul.supportedTensors`: the same, with exterior support in a finite set.
* `ExteriorAlgebra.Koszul.IsLeadingKoszul`: the leading-term condition on `D`.

## Main results

* `ExteriorAlgebra.Koszul.exists_primitive_of_isLeadingKoszul`: positive-degree exactness.

The argument removes the top coefficient degree of a cycle with a Koszul primitive and inducts on
the coefficient degree (reconstructed; it is the argument used for the Chevalley–Eilenberg
complex of `U(𝔤)` in `LieLean.Algebra.Lie.Homology.RegularAcyclic`).
-/


-- @@ L34-34 verbatim
noncomputable section

-- @@ L35-35 verbatim
open scoped TensorProduct BigOperators

-- @@ L36-36 verbatim
open TensorProduct


-- @@ L38-38 verbatim
namespace MvPolynomial


-- @@ L40-40 verbatim
variable {R I : Type*} [CommRing R]


-- @@ L42-62 verbatim
/-- Removing the degree-`n+1` component lowers the total-degree bound to `n`. -/
theorem sub_homogeneousComponent_mem_restrictTotalDegree (n : ℕ) (p : MvPolynomial I R)
    (hp : p ∈ restrictTotalDegree I R (n + 1)) :
    p - homogeneousComponent (n + 1) p ∈
      restrictTotalDegree I R n := by
  classical
  rw [mem_restrictTotalDegree, totalDegree, Finset.sup_le_iff]
  intro d hd
  have hne := mem_support_iff.mp hd
  change p.coeff d - (homogeneousComponent (n + 1) p).coeff d ≠ 0 at hne
  rw [coeff_homogeneousComponent] at hne
  have hdeg : d.degree ≠ n + 1 := by
    intro h
    exact hne (by simp [h])
  have hcoeff : p.coeff d ≠ 0 := by simpa [hdeg] using hne
  have hbound := (mem_restrictTotalDegree _ _ _).mp hp
  rw [totalDegree, Finset.sup_le_iff] at hbound
  have hdle := hbound d (mem_support_iff.mpr hcoeff)
  change d.degree ≤ n
  change d.degree ≤ n + 1 at hdle
  omega


-- @@ L64-80 verbatim
/-- Multiplication by a variable shifts the polynomial projection by one. -/
theorem homogeneousComponent_X_mul (n : ℕ) (i : I) (p : MvPolynomial I R) :
    homogeneousComponent (n + 1) (X i * p) =
      X i * homogeneousComponent n p := by
  classical
  ext d
  by_cases hi : i ∈ d.support
  · have hle : Finsupp.single i 1 ≤ d := by
      simpa only [Finsupp.single_le_iff, Nat.one_le_iff_ne_zero,
        ← Finsupp.mem_support_iff] using hi
    obtain ⟨a, rfl⟩ := exists_add_of_le hle
    simp only [coeff_homogeneousComponent, coeff_X_mul]
    congr 1
    simp only [map_add, Finsupp.degree_single]
    apply propext
    omega
  · simp [coeff_homogeneousComponent, coeff_X_mul', hi]


-- @@ L82-82 verbatim
end MvPolynomial


-- @@ L84-84 verbatim
namespace ExteriorAlgebra.Koszul


-- @@ L86-86 verbatim
variable {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M]

-- @@ L87-87 verbatim
local notation "P" => MvPolynomial I R

-- @@ L88-88 verbatim
local notation "EP" => ExteriorAlgebra R M ⊗[R] P


-- @@ L90-93 verbatim
/-- Exterior degree `q` and polynomial degree at most `n`. -/
def rectangle (q n : ℕ) : Submodule R EP :=
  Submodule.span R {z | ∃ (e : ExteriorAlgebra R M), e ∈ ⋀[R]^q M ∧
    ∃ p : P, p ∈ MvPolynomial.restrictTotalDegree I R n ∧ z = e ⊗ₜ[R] p}


-- @@ L95-98 verbatim
lemma tmul_mem_rectangle {q n : ℕ} {e : ExteriorAlgebra R M} (he : e ∈ ⋀[R]^q M)
    {p : P} (hp : p ∈ MvPolynomial.restrictTotalDegree I R n) :
    e ⊗ₜ[R] p ∈ rectangle (R := R) (M := M) (I := I) q n :=
  Submodule.subset_span ⟨e, he, p, hp, rfl⟩


-- @@ L100-105 verbatim
/-- Bounded-degree tensors supported in a finite set in the exterior factor.
Polynomial support is unrestricted, and `I` need not be finite. -/
def supportedTensors (b : Module.Basis I R M) (s : Finset I) (q n : ℕ) : Submodule R EP :=
  Submodule.span R {z | ∃ (l : List I) (p : P), l.length = q ∧
    (∀ i ∈ l, i ∈ s) ∧ p ∈ MvPolynomial.restrictTotalDegree I R n ∧
      z = basisWord b l ⊗ₜ[R] p}


-- @@ L107-112 verbatim
/-- The leading term of `D` is minus the Koszul differential: on supported tensors of exterior
degree `q` and coefficient degree at most `n`, `D z + δ_s z` has exterior degree `q - 1` and
coefficient degree at most `n`. -/
def IsLeadingKoszul (b : Module.Basis I R M) (D : Module.End R EP) : Prop :=
  ∀ (s : Finset I) (q n : ℕ) (z : EP), z ∈ supportedTensors b s q n →
    D z + delta b s z ∈ rectangle (q - 1) n


-- @@ L114-116 verbatim
/-- Projection to polynomial degree `n`, leaving exterior degree unchanged. -/
def polynomialTop (n : ℕ) : Module.End R EP :=
  TensorProduct.map LinearMap.id (MvPolynomial.homogeneousComponent n)


-- @@ L118-119 verbatim
@[simp] theorem polynomialTop_tmul (n : ℕ) (e : ExteriorAlgebra R M) (p : P) :
    polynomialTop n (e ⊗ₜ[R] p) = e ⊗ₜ[R] MvPolynomial.homogeneousComponent n p := rfl


-- @@ L121-127 verbatim
/-- Every homogeneous pure-tensor span lies in the corresponding rectangle. -/
theorem homogeneousTensors_le_rectangle (b : Module.Basis I R M) (s : Finset I)
    (n q : ℕ) : homogeneousTensors b s n q ≤ rectangle q n := by
  apply Submodule.span_le.mpr
  rintro z ⟨l, p, hl, _, hp, _, rfl⟩
  exact tmul_mem_rectangle (hl ▸ basisWord_mem_exteriorPower b l)
    ((MvPolynomial.mem_restrictTotalDegree _ _ _).mpr hp.totalDegree_le)


-- @@ L129-141 verbatim
/-- The top component of a rectangle belongs to the full homogeneous tensor span. -/
theorem polynomialTop_mem_iSup (b : Module.Basis I R M) (q m n : ℕ) {z : EP}
    (hz : z ∈ rectangle q m) :
    polynomialTop n z ∈ ⨆ s : Finset I, homogeneousTensors b s n q := by
  rw [iSup_homogeneousTensors]
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨e, he, p, _, rfl⟩ := hz
    exact Submodule.subset_span ⟨e, MvPolynomial.homogeneousComponent n p, he,
      MvPolynomial.homogeneousComponent_isHomogeneous n p, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using add_mem hx hy
  | smul r x _ hx => simpa only [map_smul] using Submodule.smul_mem _ r hx


-- @@ L143-152 verbatim
/-- Projection acts as identity on the supported homogeneous span. -/
theorem polynomialTop_eq_self (b : Module.Basis I R M) (s : Finset I) (n q : ℕ)
    {z : EP} (hz : z ∈ homogeneousTensors b s n q) : polynomialTop n z = z := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨l, p, _, _, hp, _, rfl⟩ := hz
    simp only [polynomialTop_tmul, MvPolynomial.homogeneousComponent_eq_self hp]
  | zero => exact map_zero _
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul r x _ hx => simp only [map_smul, hx]


-- @@ L154-164 verbatim
/-- Projection above the coefficient bound vanishes. -/
theorem polynomialTop_eq_zero {q m n : ℕ} (hmn : m < n) {z : EP}
    (hz : z ∈ rectangle q m) : polynomialTop n z = 0 := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨e, _, p, hp, rfl⟩ := hz
    rw [polynomialTop_tmul, MvPolynomial.homogeneousComponent_eq_zero n p
      (lt_of_le_of_lt ((MvPolynomial.mem_restrictTotalDegree _ _ _).mp hp) hmn), tmul_zero]
  | zero => exact map_zero _
  | add x y _ _ hx hy => simp only [map_add, hx, hy, add_zero]
  | smul r x _ hx => simp only [map_smul, hx, smul_zero]


-- @@ L166-179 verbatim
/-- Removing the top component of a rectangle strictly lowers its coefficient bound. -/
theorem sub_polynomialTop_mem (q n : ℕ) {z : EP} (hz : z ∈ rectangle q (n + 1)) :
    z - polynomialTop (n + 1) z ∈ rectangle q n := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨e, he, p, hp, rfl⟩ := hz
    rw [polynomialTop_tmul, ← tmul_sub]
    exact tmul_mem_rectangle he
      (MvPolynomial.sub_homogeneousComponent_mem_restrictTotalDegree n p hp)
  | zero => simp
  | add x y _ _ hx hy =>
    simpa only [map_add, add_sub_add_comm] using add_mem hx hy
  | smul r x _ hx =>
    simpa only [map_smul, smul_sub] using Submodule.smul_mem _ r hx


-- @@ L181-189 verbatim
/-- The Koszul differential commutes with degree projection with shift one. -/
theorem polynomialTop_delta (b : Module.Basis I R M) (s : Finset I) (n : ℕ) (z : EP) :
    polynomialTop (n + 1) (delta b s z) =
      delta b s (polynomialTop n z) := by
  induction z with
  | tmul e p =>
    simp only [delta, LinearMap.sum_apply, deltaTerm_tmul, map_sum,
      polynomialTop_tmul, MvPolynomial.homogeneousComponent_X_mul]
  | add x y hx hy => simp only [map_add, hx, hy]


-- @@ L191-200 verbatim
/-- The top homogeneous piece of a cycle of a differential with leading term `-δ` is a
Koszul cycle. -/
theorem delta_polynomialTop_eq_zero (b : Module.Basis I R M) {D : Module.End R EP}
    (hD : IsLeadingKoszul b D)
    (s : Finset I) (q n : ℕ) {z : EP} (hz : z ∈ supportedTensors b s q n)
    (hcycle : D z = 0) : delta b s (polynomialTop n z) = 0 := by
  have he := hD s q n z hz
  rw [hcycle, zero_add] at he
  rw [← polynomialTop_delta]
  exact polynomialTop_eq_zero (Nat.lt_succ_self n) he


-- @@ L202-206 verbatim
/-- Positive-degree form of strict coefficient descent. -/
theorem sub_polynomialTop_mem_pred (q n : ℕ) (hn : 0 < n) {z : EP}
    (hz : z ∈ rectangle q n) : z - polynomialTop n z ∈ rectangle q (n - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using sub_polynomialTop_mem q m hz


-- @@ L208-217 verbatim
/-- Every bounded tensor splits into a lower-degree tensor and a supported homogeneous top. -/
theorem rectangle_decomposition (b : Module.Basis I R M) (q n : ℕ) {z : EP}
    (hz : z ∈ rectangle q (n + 1)) :
    ∃ (y t : EP) (s : Finset I), y ∈ rectangle q n ∧
      t ∈ homogeneousTensors b s (n + 1) q ∧ z = y + t := by
  have ht := polynomialTop_mem_iSup b q (n + 1) (n + 1) hz
  rw [iSup_homogeneousTensors] at ht
  obtain ⟨s, hs⟩ := exists_support_of_mem_homogeneous_span b (n + 1) q ht
  exact ⟨z - polynomialTop (n + 1) z, polynomialTop (n + 1) z, s,
    sub_polynomialTop_mem q n hz, hs, (sub_add_cancel z _).symm⟩


-- @@ L219-226 verbatim
/-- Every homogeneous span lies in its concrete coefficient-degree rectangle. -/
theorem iSup_homogeneousTensors_le_rectangle (b : Module.Basis I R M) (q n : ℕ) :
    (⨆ s : Finset I, homogeneousTensors b s n q) ≤ rectangle q n := by
  rw [iSup_homogeneousTensors]
  refine Submodule.span_le.mpr ?_
  rintro z ⟨e, p, he, hp, rfl⟩
  exact tmul_mem_rectangle he
    (by rw [MvPolynomial.mem_restrictTotalDegree]; exact hp.totalDegree_le)


-- @@ L228-241 verbatim
/-- Projection onto degree zero is the identity on the degree-zero rectangle. -/
theorem polynomialTop_zero_eq_self (q : ℕ) {z : EP}
    (hz : z ∈ rectangle q 0) : polynomialTop 0 z = z := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨e, _, p, hp, rfl⟩ := hz
    rw [MvPolynomial.mem_restrictTotalDegree] at hp
    have hp0 : p.IsHomogeneous 0 := by
      rw [← MvPolynomial.totalDegree_zero_iff_isHomogeneous]
      exact Nat.eq_zero_of_le_zero hp
    rw [polynomialTop_tmul, MvPolynomial.homogeneousComponent_eq_self hp0]
  | zero => exact map_zero _
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul r x _ hx => simp only [map_smul, hx]


-- @@ L243-248 verbatim
/-- Bounded exterior support is monotone. -/
theorem supportedTensors_mono (b : Module.Basis I R M) (q n : ℕ)
    {s t : Finset I} (hst : s ⊆ t) : supportedTensors b s q n ≤ supportedTensors b t q n := by
  apply Submodule.span_mono
  rintro z ⟨l, p, hl, hs, hp, hz⟩
  exact ⟨l, p, hl, fun i hi => hst (hs i hi), hp, hz⟩


-- @@ L250-257 verbatim
/-- Every homogeneous supported tensor has the corresponding bounded support. -/
theorem homogeneousTensors_le_supportedTensors (b : Module.Basis I R M)
    (s : Finset I) (n q : ℕ) :
    homogeneousTensors b s n q ≤ supportedTensors b s q n := by
  apply Submodule.span_le.mpr
  rintro z ⟨l, p, hl, hs, hp, _, rfl⟩
  exact Submodule.subset_span ⟨l, p, hl, hs,
    (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr hp.totalDegree_le, rfl⟩


-- @@ L259-287 verbatim
/-- Every bounded rectangle tensor has finite exterior coordinate support. -/
theorem exists_support_rectangle (b : Module.Basis I R M) (q n : ℕ)
    {z : EP} (hz : z ∈ rectangle q n) : ∃ s, z ∈ supportedTensors b s q n := by
  classical
  have hall : rectangle (R := R) (M := M) (I := I) q n ≤ ⨆ s, supportedTensors b s q n := by
    apply Submodule.span_le.mpr
    rintro z ⟨e, he, p, hp, rfl⟩
    rw [← exteriorPower.ιMulti_span_fixedDegree_of_span_eq_top R q M b.span_eq] at he
    induction he using Submodule.span_induction with
    | mem e he =>
      obtain ⟨v, hv, rfl⟩ := he
      have hv' : ∀ j, ∃ i, b i = v j := fun j => hv ⟨j, rfl⟩
      choose f hf using hv'
      let l := List.ofFn f
      have heq : ExteriorAlgebra.ιMulti R q v = basisWord b l := by
        simp only [ExteriorAlgebra.ιMulti_apply, basisWord, l, List.map_ofFn]
        congr 2
        funext j
        exact congrArg (ι R) (hf j).symm
      rw [heq]
      apply Submodule.mem_iSup_of_mem l.toFinset
      exact Submodule.subset_span ⟨l, p, by simp [l], fun i hi => by simpa using hi, hp, rfl⟩
    | zero => simp
    | add e f _ _ he hf => rw [add_tmul]; exact add_mem he hf
    | smul r e _ he => rw [← smul_tmul']; exact Submodule.smul_mem _ r he
  apply (Submodule.mem_iSup_of_directed _ ?_).mp (hall hz)
  intro s t
  exact ⟨s ∪ t, supportedTensors_mono b q n Finset.subset_union_left,
    supportedTensors_mono b q n Finset.subset_union_right⟩


-- @@ L289-300 verbatim
/-- Common finite support for a tensor and its homogeneous top. -/
theorem exists_common_support (b : Module.Basis I R M) (q n : ℕ)
    {z : EP} (hz : z ∈ rectangle q n) :
    ∃ s, z ∈ supportedTensors b s q n ∧
      polynomialTop n z ∈ homogeneousTensors b s n q := by
  classical
  obtain ⟨s, hs⟩ := exists_support_rectangle b q n hz
  have ht := polynomialTop_mem_iSup b q n n hz
  rw [iSup_homogeneousTensors] at ht
  obtain ⟨t, ht⟩ := exists_support_of_mem_homogeneous_span b n q ht
  exact ⟨s ∪ t, supportedTensors_mono b q n Finset.subset_union_left hs,
    homogeneousTensors_mono b n q Finset.subset_union_right ht⟩


-- @@ L302-309 verbatim
/-- Coefficient rectangles are increasing in their degree bound. -/
theorem rectangle_mono (q : ℕ) {n m : ℕ} (hnm : n ≤ m) :
    rectangle (R := R) (M := M) (I := I) q n ≤ rectangle q m := by
  apply Submodule.span_le.mpr
  rintro z ⟨e, he, p, hp, rfl⟩
  apply tmul_mem_rectangle he
  rw [MvPolynomial.mem_restrictTotalDegree] at hp ⊢
  exact hp.trans hnm


-- @@ L311-311 verbatim
section Field


-- @@ L313-314 verbatim
variable {K : Type*} [Field K] [CharZero K] [Module K M] (b : Module.Basis I K M)
  {D : Module.End K (ExteriorAlgebra K M ⊗[K] MvPolynomial I K)}


-- @@ L316-332 verbatim
/-- One step of descent: a Koszul primitive of the top coefficient degree of a cycle leaves a
cycle of smaller coefficient degree. -/
theorem cycle_lowering_of_isLeadingKoszul (hD : IsLeadingKoszul b D) (hD2 : ∀ z, D (D z) = 0)
    (q n : ℕ) (hq : 0 < q) {z : ExteriorAlgebra K M ⊗[K] MvPolynomial I K}
    (hz : z ∈ rectangle q (n + 1)) (hcycle : D z = 0) :
    ∃ y ∈ rectangle (q + 1) n, z - D y ∈ rectangle q n ∧ D (z - D y) = 0 := by
  obtain ⟨s, hs, ht⟩ := exists_common_support b q (n + 1) hz
  have htop := delta_polynomialTop_eq_zero b hD s q (n + 1) hs hcycle
  obtain ⟨y, hy, hdy⟩ := exists_homogeneous_primitive b s (n + 1) q
    (polynomialTop (n + 1) z) ht htop (by omega)
  have hy' : y ∈ homogeneousTensors b s n (q + 1) := by simpa using hy
  have herror := hD s (q + 1) n y (homogeneousTensors_le_supportedTensors b s n (q + 1) hy')
  rw [hdy, Nat.add_sub_cancel] at herror
  refine ⟨-y, neg_mem (homogeneousTensors_le_rectangle b s n (q + 1) hy'), ?_, ?_⟩
  · have hlower := add_mem (sub_polynomialTop_mem q n hz) herror
    simpa only [map_neg, sub_neg_eq_add, sub_add_add_cancel] using hlower
  · simp only [map_sub, hD2, hcycle, sub_zero]


-- @@ L334-341 verbatim
/-- Cycles of positive exterior degree with constant coefficients vanish. -/
theorem cycle_eq_zero_of_isLeadingKoszul (hD : IsLeadingKoszul b D) (q : ℕ) (hq : 0 < q)
    {z : ExteriorAlgebra K M ⊗[K] MvPolynomial I K}
    (hz : z ∈ rectangle q 0) (hcycle : D z = 0) : z = 0 := by
  obtain ⟨s, hs, ht⟩ := exists_common_support b q 0 hz
  have htop := delta_polynomialTop_eq_zero b hD s q 0 hs hcycle
  rw [polynomialTop_zero_eq_self q hz] at ht htop
  exact eq_zero_of_cycle_polynomial_degree_zero b s q z ht htop hq


-- @@ L343-362 verbatim
/-- **Koszul descent.** If `D ∘ D = 0` and the leading term of `D` is `-δ`, every cycle of
positive exterior degree `q` and coefficient degree at most `n` is `D y` for some `y` of
exterior degree `q + 1` and coefficient degree at most `n - 1`. -/
theorem exists_primitive_of_isLeadingKoszul (hD : IsLeadingKoszul b D)
    (hD2 : ∀ z, D (D z) = 0) (q n : ℕ) (hq : 0 < q)
    {z : ExteriorAlgebra K M ⊗[K] MvPolynomial I K}
    (hz : z ∈ rectangle q n) (hcycle : D z = 0) :
    ∃ y ∈ rectangle (q + 1) (n - 1), D y = z := by
  induction n generalizing z with
  | zero =>
    have heq := cycle_eq_zero_of_isLeadingKoszul b hD q hq hz hcycle
    exact ⟨0, Submodule.zero_mem _, by simpa only [map_zero] using heq.symm⟩
  | succ n ih =>
    obtain ⟨y, hy, hr, hrc⟩ := cycle_lowering_of_isLeadingKoszul b hD hD2 q n hq hz hcycle
    obtain ⟨w, hw, hdw⟩ := ih hr hrc
    refine ⟨y + w, ?_, ?_⟩
    · simpa only [Nat.succ_sub_one] using add_mem hy
        (rectangle_mono (q + 1) (Nat.sub_le n 1) hw)
    · rw [map_add, hdw]
      abel


-- @@ L364-364 verbatim
end Field


-- @@ L366-366 verbatim
end ExteriorAlgebra.Koszul
