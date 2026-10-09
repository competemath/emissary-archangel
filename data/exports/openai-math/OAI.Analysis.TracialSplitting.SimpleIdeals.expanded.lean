import OAI.Analysis.TracialSplitting.Diagonalization


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
universe uA uC uι


-- @@ L9-9 verbatim
namespace Pureness


-- @@ L11-11 verbatim
section


-- @@ L13-13 verbatim
open Filter Topology


-- @@ L15-15 verbatim
variable {A : Type uA} [NormedRing A]


-- @@ L17-40 verbatim
def closedTwoSidedIdeal (I : TwoSidedIdeal A) : TwoSidedIdeal A :=
  TwoSidedIdeal.mk' (closure (I : Set A))
    (subset_closure I.zero_mem)
    (by
      intro x y hx hy
      obtain ⟨u, hu, hux⟩ := mem_closure_iff_seq_limit.mp hx
      obtain ⟨v, hv, hvy⟩ := mem_closure_iff_seq_limit.mp hy
      exact isClosed_closure.mem_of_tendsto (hux.add hvy)
        (Eventually.of_forall fun j => subset_closure (I.add_mem (hu j) (hv j))))
    (by
      intro x hx
      obtain ⟨u, hu, hux⟩ := mem_closure_iff_seq_limit.mp hx
      exact isClosed_closure.mem_of_tendsto hux.neg
        (Eventually.of_forall fun j => subset_closure (I.neg_mem (hu j))))
    (by
      intro x y hy
      obtain ⟨u, hu, huy⟩ := mem_closure_iff_seq_limit.mp hy
      exact isClosed_closure.mem_of_tendsto (huy.const_mul x)
        (Eventually.of_forall fun j => subset_closure (I.mul_mem_left x (u j) (hu j))))
    (by
      intro x y hx
      obtain ⟨u, hu, hux⟩ := mem_closure_iff_seq_limit.mp hx
      exact isClosed_closure.mem_of_tendsto (hux.mul_const y)
        (Eventually.of_forall fun j => subset_closure (I.mul_mem_right (u j) y (hu j))))


-- @@ L42-44 verbatim
@[simp] theorem coe_closedTwoSidedIdeal (I : TwoSidedIdeal A) :
    (closedTwoSidedIdeal I : Set A) = closure (I : Set A) := by
  simp [closedTwoSidedIdeal]


-- @@ L46-60 verbatim
theorem closure_span_singleton_eq_univ (hsimple : TopologicallySimple A)
    (h : A) (hh : h ≠ 0) :
    closure (TwoSidedIdeal.span {h} : Set A) = Set.univ := by
  let I : TwoSidedIdeal A := TwoSidedIdeal.span {h}
  have hclosed : IsClosed (closedTwoSidedIdeal I : Set A) := by
    rw [coe_closedTwoSidedIdeal]
    exact isClosed_closure
  have hmem : h ∈ closedTwoSidedIdeal I := by
    rw [← SetLike.mem_coe, coe_closedTwoSidedIdeal]
    exact subset_closure (TwoSidedIdeal.subset_span (Set.mem_singleton h))
  rcases hsimple (closedTwoSidedIdeal I) hclosed with hbot | htop
  · rw [hbot] at hmem
    exact (hh ((TwoSidedIdeal.mem_bot A).mp hmem)).elim
  · have heq := congrArg (fun J : TwoSidedIdeal A => (J : Set A)) htop
    simpa only [coe_closedTwoSidedIdeal, TwoSidedIdeal.coe_top] using heq


-- @@ L62-62 verbatim
end


-- @@ L64-64 verbatim
section


-- @@ L66-66 verbatim
variable {A : Type uA} [Ring A]


-- @@ L68-69 verbatim
def finiteIdealSum (h : A) (l : List (A × A)) : A :=
  (l.map fun p => p.1 * h * p.2).sum


-- @@ L71-100 verbatim
theorem exists_finiteIdealSum {h x : A} (hx : x ∈ TwoSidedIdeal.span {h}) :
    ∃ l : List (A × A), finiteIdealSum h l = x := by
  induction hx using TwoSidedIdeal.span_induction with
  | mem x hx =>
    have : x = h := Set.mem_singleton_iff.mp hx
    subst x
    exact ⟨[(1, 1)], by simp [finiteIdealSum]⟩
  | zero => exact ⟨[], rfl⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨l, rfl⟩ := ihx
    obtain ⟨m, rfl⟩ := ihy
    exact ⟨l ++ m, by simp [finiteIdealSum]⟩
  | neg x hx ih =>
    obtain ⟨l, rfl⟩ := ih
    refine ⟨l.map (fun p => (-p.1, p.2)), ?_⟩
    clear hx
    induction l with
    | nil => simp [finiteIdealSum]
    | cons p l ih =>
      simp_all [finiteIdealSum, List.map_map, Function.comp_def, neg_add_rev, add_comm]
  | left_absorb a x hx ih =>
    obtain ⟨l, rfl⟩ := ih
    refine ⟨l.map (fun p => (a * p.1, p.2)), ?_⟩
    simp [finiteIdealSum, List.map_map, Function.comp_def, mul_assoc, List.sum_map_mul_left]
  | right_absorb b x hx ih =>
    obtain ⟨l, rfl⟩ := ih
    refine ⟨l.map (fun p => (p.1, p.2 * b)), ?_⟩
    simp only [finiteIdealSum, List.map_map, Function.comp_def]
    simpa only [mul_assoc] using
      (List.sum_map_mul_right (l := l) (f := fun p => p.1 * h * p.2) (r := b))


-- @@ L102-102 verbatim
end


-- @@ L104-104 verbatim
section


-- @@ L106-106 verbatim
open Topology


-- @@ L108-108 verbatim
variable {A : Type uA} [NormedRing A] [CompleteSpace A]


-- @@ L110-119 verbatim
theorem exists_invertible_finiteIdealSum (hsimple : TopologicallySimple A)
    (h : A) (hh : h ≠ 0) :
    ∃ l : List (A × A), IsUnit (finiteIdealSum h l) := by
  have h1 : (1 : A) ∈ closure (TwoSidedIdeal.span {h} : Set A) := by
    rw [closure_span_singleton_eq_univ hsimple h hh]
    exact Set.mem_univ _
  have hn : {x : A | IsUnit x} ∈ 𝓝 (1 : A) := Units.isOpen.mem_nhds isUnit_one
  obtain ⟨x, hxunit, hxspan⟩ := mem_closure_iff_nhds.mp h1 _ hn
  obtain ⟨l, hl⟩ := exists_finiteIdealSum hxspan
  exact ⟨l, hl.symm ▸ hxunit⟩


-- @@ L121-121 verbatim
end


-- @@ L123-123 verbatim
section


-- @@ L125-125 verbatim
open Finset


-- @@ L127-127 verbatim
variable {A : Type uA} {C : Type uC} {ι : Type uι} [Ring A] [StarRing A] [AddCommMonoid C]


-- @@ L129-130 verbatim
def traceTransfer (I : Finset ι) (r p : A) (s : ι → A) : A :=
  ∑ i ∈ I, r * s i * p * star (s i) * r


-- @@ L132-151 verbatim
theorem trace_transfer_identity (τ : A →+ C)
    (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    (I : Finset ι) (r p : A) (s : ι → A)
    (hfull : ∑ i ∈ I, star (s i) * (r * r) * s i = 1) :
    τ (traceTransfer I r p s) = τ p := by
  unfold traceTransfer
  rw [map_sum]
  calc
    (∑ i ∈ I, τ (r * s i * p * star (s i) * r)) =
        ∑ i ∈ I, τ ((star (s i) * (r * r) * s i) * p) := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        τ (r * s i * p * star (s i) * r) =
            τ ((r * s i * p) * (star (s i) * r)) := by simp only [mul_assoc]
        _ = τ ((star (s i) * r) * (r * s i * p)) := hτ _ _
        _ = τ ((star (s i) * (r * r) * s i) * p) := by simp only [mul_assoc]
    _ = τ ((∑ i ∈ I, star (s i) * (r * r) * s i) * p) := by
      rw [Finset.sum_mul, map_sum]
    _ = τ p := by rw [hfull, one_mul]


-- @@ L153-155 verbatim
theorem traceTransfer_eq_sandwich (I : Finset ι) (r p : A) (s : ι → A) :
    traceTransfer I r p s = r * (∑ i ∈ I, s i * p * star (s i)) * r := by
  simp only [traceTransfer, Finset.mul_sum, Finset.sum_mul, mul_assoc]


-- @@ L157-160 verbatim
theorem traceTransfer_eq_sum_conjugates (I : Finset ι) (r p : A) (s : ι → A)
    (hr : star r = r) :
    traceTransfer I r p s = ∑ i ∈ I, star (star (s i) * r) * p * (star (s i) * r) := by
  simp only [traceTransfer, star_mul, star_star, hr, mul_assoc]


-- @@ L162-166 verbatim
theorem traceTransfer_nonneg [PartialOrder A] [StarOrderedRing A]
    [IsOrderedAddMonoid A] (I : Finset ι) (r p : A) (s : ι → A)
    (hr : star r = r) (hp : 0 ≤ p) : 0 ≤ traceTransfer I r p s := by
  rw [traceTransfer_eq_sum_conjugates I r p s hr]
  exact Finset.sum_nonneg (fun i _ => star_left_conjugate_nonneg hp _)


-- @@ L168-168 verbatim
end


-- @@ L170-170 verbatim
section


-- @@ L172-172 verbatim
variable {A : Type uA} {ι : Type uι} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]


-- @@ L174-194 verbatim
theorem normalize_fullness_sum (I : Finset ι) (h : A) (hh : 0 ≤ h) (t : ι → A)
    (hunit : IsUnit (∑ i ∈ I, star (t i) * h * t i)) :
    ∃ s : ι → A, ∑ i ∈ I, star (s i) * h * s i = 1 := by
  let q := ∑ i ∈ I, star (t i) * h * t i
  have hq : 0 ≤ q := Finset.sum_nonneg (fun i _ => star_left_conjugate_nonneg hh (t i))
  obtain ⟨u, hu⟩ := (CFC.isUnit_sqrt_iff q hq).mpr hunit
  have hfactor : q = star (u : A) * (u : A) := by
    rw [hu, (CFC.sqrt_nonneg q).star_eq, CFC.sqrt_mul_sqrt_self q hq]
  have hnormalize : star (↑(u⁻¹) : A) * q * (↑(u⁻¹) : A) = 1 := by
    rw [hfactor]
    calc
      star (↑(u⁻¹) : A) * (star (u : A) * (u : A)) * (↑(u⁻¹) : A) =
          star ((u : A) * (↑(u⁻¹) : A)) * ((u : A) * (↑(u⁻¹) : A)) := by
        simp only [star_mul, mul_assoc]
      _ = 1 := by simp
  refine ⟨fun i => t i * (↑(u⁻¹) : A), ?_⟩
  calc
    (∑ i ∈ I, star (t i * (↑(u⁻¹) : A)) * h * (t i * (↑(u⁻¹) : A))) =
        star (↑(u⁻¹) : A) * q * (↑(u⁻¹) : A) := by
      simp only [q, Finset.mul_sum, Finset.sum_mul, star_mul, mul_assoc]
    _ = 1 := hnormalize


-- @@ L196-205 verbatim
theorem sqrt_trace_transfer (I : Finset ι) (h p : A) (hh : 0 ≤ h) (hp : 0 ≤ p)
    (s : ι → A) (hfull : ∑ i ∈ I, star (s i) * h * s i = 1) :
    0 ≤ traceTransfer I (CFC.sqrt h) p s ∧
      ∀ (τ : A →+ ℂ), (∀ a b : A, τ (a * b) = τ (b * a)) →
        τ (traceTransfer I (CFC.sqrt h) p s) = τ p := by
  constructor
  · exact traceTransfer_nonneg I _ p s (CFC.sqrt_nonneg h).star_eq hp
  · intro τ hτ
    apply trace_transfer_identity τ hτ I _ p s
    simpa only [CFC.sqrt_mul_sqrt_self h hh] using hfull


-- @@ L207-207 verbatim
end


-- @@ L209-209 verbatim
section


-- @@ L211-211 verbatim
open scoped WithCStarModule InnerProductSpace


-- @@ L213-213 verbatim
variable {A : Type uA} {ι : Type uι} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Fintype ι]


-- @@ L215-251 verbatim
theorem invertible_positive_sum_of_invertible_sum (h : A) (hh : 0 ≤ h) (r t : ι → A)
    (hS : IsUnit (∑ i, r i * h * t i)) :
    IsUnit (∑ i, star (t i) * h * t i) := by
  nontriviality A
  let S := ∑ i, r i * h * t i
  let q := ∑ i, star (t i) * h * t i
  let x : C⋆ᵐᵒᵈ(A, ι → A) := (WithCStarModule.equiv A _).symm (fun i => r i * CFC.sqrt h)
  let y : C⋆ᵐᵒᵈ(A, ι → A) := (WithCStarModule.equiv A _).symm (fun i => star (t i) * CFC.sqrt h)
  have hsqrt : star (CFC.sqrt h) = CFC.sqrt h := (CFC.sqrt_nonneg h).star_eq
  have hsquare (z : A) : CFC.sqrt h * (CFC.sqrt h * z) = h * z := by
    rw [← mul_assoc, CFC.sqrt_mul_sqrt_self h hh]
  have hxy : ⟪x, y⟫_A = star S := by
    simp [x, y, S, WithCStarModule.pi_inner, WithCStarModule.inner_def,
      hsqrt, hh.star_eq, mul_assoc, hsquare]
  have hyx : ⟪y, x⟫_A = S := by
    simp [x, y, S, WithCStarModule.pi_inner, WithCStarModule.inner_def,
      hsqrt, mul_assoc, hsquare]
  have hyy : ⟪y, y⟫_A = q := by
    simp [y, q, WithCStarModule.pi_inner, WithCStarModule.inner_def,
      hsqrt, mul_assoc, hsquare]
  have hbound : star S * S ≤ ‖x‖ ^ 2 • q := by
    simpa only [hxy, hyx, hyy] using (CStarModule.inner_mul_inner_swap_le (A := A) (x := x) (y := y))
  have hpos : IsStrictlyPositive (star S * S) :=
    IsStrictlyPositive.iff_of_unital.mpr ⟨star_mul_self_nonneg S, hS.star.mul hS⟩
  have hunit : IsUnit (‖x‖ ^ 2 • q) := CStarAlgebra.isUnit_of_le _ hbound hpos
  have hx : x ≠ 0 := by
    intro hx
    have hzero : S = 0 := by simpa [hx] using hyx.symm
    have hS' : IsUnit S := hS
    exact not_isUnit_zero (hzero ▸ hS')
  have hc : ‖x‖ ^ 2 ≠ (0 : ℝ) := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  have hcunit : IsUnit (algebraMap ℝ A (‖x‖ ^ 2)) :=
    (isUnit_iff_ne_zero.mpr hc).map (algebraMap ℝ A)
  rw [Algebra.smul_def] at hunit
  obtain ⟨u, hu⟩ := hcunit
  have huq := u⁻¹.isUnit.mul hunit
  simpa only [← hu, ← mul_assoc, Units.inv_mul, one_mul] using huq


-- @@ L253-253 verbatim
end


-- @@ L255-255 verbatim
section


-- @@ L257-257 verbatim
variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]


-- @@ L259-269 verbatim
theorem fullness (hsimple : TopologicallySimple A) (h : A) (hh : 0 ≤ h) (hne : h ≠ 0) :
    ∃ n : ℕ, ∃ s : Fin n → A, ∑ i, star (s i) * h * s i = 1 := by
  obtain ⟨l, hl⟩ := exists_invertible_finiteIdealSum hsimple h hne
  have hrep : finiteIdealSum h l = ∑ i : Fin l.length, (l.get i).1 * h * (l.get i).2 := by
    have heq := congrArg (fun v : List (A × A) => finiteIdealSum h v) (List.ofFn_get l)
    simpa only [finiteIdealSum, List.map_ofFn, List.sum_ofFn, Function.comp_apply] using heq.symm
  have hunit : IsUnit (∑ i : Fin l.length, star (l.get i).2 * h * (l.get i).2) :=
    invertible_positive_sum_of_invertible_sum h hh
      (fun i : Fin l.length => (l.get i).1) (fun i => (l.get i).2) (hrep ▸ hl)
  obtain ⟨s, hs⟩ := normalize_fullness_sum Finset.univ h hh (fun i : Fin l.length => (l.get i).2) hunit
  exact ⟨l.length, s, hs⟩


-- @@ L271-279 verbatim
theorem exists_positive_trace_transfer (hsimple : TopologicallySimple A)
    (h p : A) (hh : 0 ≤ h) (hne : h ≠ 0) (hp : 0 ≤ p) :
    ∃ c : A, c ∈ Set.range (fun z : A => CFC.sqrt h * z * CFC.sqrt h) ∧
      0 ≤ c ∧ ∀ (τ : A →+ ℂ),
      (∀ a b : A, τ (a * b) = τ (b * a)) → τ c = τ p := by
  obtain ⟨n, s, hs⟩ := fullness hsimple h hh hne
  exact ⟨traceTransfer Finset.univ (CFC.sqrt h) p s,
    ⟨∑ i, s i * p * star (s i), (traceTransfer_eq_sandwich Finset.univ _ p s).symm⟩,
    sqrt_trace_transfer Finset.univ h p hh hp s hs⟩


-- @@ L281-281 verbatim
end


-- @@ L283-283 verbatim
section


-- @@ L285-285 verbatim
open scoped ComplexOrder


-- @@ L287-287 verbatim
variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]


-- @@ L289-289 verbatim
namespace TracialState


-- @@ L291-309 verbatim
theorem conjugate_le (τ : TracialState A) (h : A) (hh : 0 ≤ h) (s : A) :
    τ.functional (star s * h * s) ≤ ‖s * star s‖ • τ.functional h := by
  have hsqrt : star (CFC.sqrt h) = CFC.sqrt h := (CFC.sqrt_nonneg h).star_eq
  have hsquare (z : A) : CFC.sqrt h * (CFC.sqrt h * z) = h * z := by
    rw [← mul_assoc, CFC.sqrt_mul_sqrt_self h hh]
  have heq : τ.functional (star s * h * s) =
      τ.functional (CFC.sqrt h * (s * star s) * CFC.sqrt h) := by
    calc
      τ.functional (star s * h * s) =
          τ.functional ((star s * CFC.sqrt h) * (CFC.sqrt h * s)) := by
        simp only [mul_assoc, hsquare]
      _ = τ.functional ((CFC.sqrt h * s) * (star s * CFC.sqrt h)) := τ.tracial _ _
      _ = τ.functional (CFC.sqrt h * (s * star s) * CFC.sqrt h) := by simp only [mul_assoc]
  have hb : CFC.sqrt h * (s * star s) * CFC.sqrt h ≤ ‖s * star s‖ • h := by
    simpa only [hsqrt, CFC.sqrt_mul_sqrt_self h hh] using
      (CStarAlgebra.star_left_conjugate_le_norm_smul
        (a := CFC.sqrt h) (b := s * star s) (mul_star_self_nonneg s).isSelfAdjoint)
  rw [heq, ← τ.functional.map_smul_of_tower]
  exact τ.functional.monotone hb


-- @@ L311-322 verbatim
theorem faithful (τ : TracialState A) (hsimple : TopologicallySimple A)
    (h : A) (hh : 0 ≤ h) (hzero : τ.functional h = 0) : h = 0 := by
  by_contra hne
  obtain ⟨n, s, hs⟩ := fullness hsimple h hh hne
  have hz (i : Fin n) : τ.functional (star (s i) * h * s i) = 0 := by
    apply le_antisymm
    · simpa only [hzero, smul_zero] using τ.conjugate_le h hh (s i)
    · exact τ.functional.map_nonneg (star_left_conjugate_nonneg hh (s i))
  have h1 : τ.functional 1 = 0 := by
    rw [← hs, map_sum]
    exact Finset.sum_eq_zero (fun i _ => hz i)
  exact one_ne_zero (τ.normalized.symm.trans h1)


-- @@ L324-326 verbatim
theorem map_eq_zero_iff (τ : TracialState A) (hsimple : TopologicallySimple A)
    (h : A) (hh : 0 ≤ h) : τ.functional h = 0 ↔ h = 0 :=
  ⟨τ.faithful hsimple h hh, fun heq => by simp [heq]⟩


-- @@ L328-328 verbatim
end TracialState


-- @@ L330-330 verbatim
end


-- @@ L332-332 verbatim
section


-- @@ L334-334 verbatim
open scoped ComplexOrder ENNReal NNReal


-- @@ L336-336 verbatim
variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]


-- @@ L338-338 verbatim
noncomputable def normalizePositive (a : A) : A := ‖a‖⁻¹ • a


-- @@ L340-341 verbatim
lemma normalizePositive_nonneg (a : A) (ha : 0 ≤ a) : 0 ≤ normalizePositive a :=
  smul_nonneg (inv_nonneg.mpr (norm_nonneg a)) ha


-- @@ L343-345 verbatim
omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma normalizePositive_zero : normalizePositive (0 : A) = 0 := by
  simp [normalizePositive]


-- @@ L347-351 verbatim
omit [PartialOrder A] [StarOrderedRing A] in
lemma normalizePositive_norm_le (a : A) : ‖normalizePositive a‖ ≤ 1 := by
  by_cases ha : a = 0
  · simp [ha]
  · simp [normalizePositive, norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr ha)]


-- @@ L353-358 verbatim
omit [PartialOrder A] [StarOrderedRing A] in
lemma normalizePositive_smul (a : A) (t : ℝ) (ht : 0 < t) :
    normalizePositive (t • a) = normalizePositive a := by
  simp only [normalizePositive, norm_smul, Real.norm_eq_abs, abs_of_pos ht,
    smul_smul, mul_inv_rev]
  rw [mul_assoc, inv_mul_cancel₀ ht.ne', mul_one]


-- @@ L360-361 verbatim
noncomputable def normalizedRoot (a : A) (j : ℕ) : A :=
  CFC.nnrpow (normalizePositive a) (((j : ℝ≥0) + 1)⁻¹)


-- @@ L363-364 verbatim
noncomputable def normalizedRootRank (τ : TracialState A) (a : A) : ℝ≥0∞ :=
  ⨆ j : ℕ, ENNReal.ofReal (τ.functional (normalizedRoot a j)).re


-- @@ L366-366 verbatim
lemma normalizedRoot_nonneg (a : A) (j : ℕ) : 0 ≤ normalizedRoot a j := CFC.nnrpow_nonneg


-- @@ L368-372 verbatim
lemma normalizedRoot_le_one (a : A) (ha : 0 ≤ a) (j : ℕ) : normalizedRoot a j ≤ 1 := by
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (normalizedRoot_nonneg a j)).mp
  unfold normalizedRoot
  rw [CFC.nnrpow_eq_pow, CFC.norm_nnrpow _ (by positivity) (normalizePositive_nonneg a ha)]
  exact Real.rpow_le_one (norm_nonneg _) (normalizePositive_norm_le a) (by positivity)


-- @@ L374-382 verbatim
lemma normalizedRootRank_le_one (τ : TracialState A) (a : A) (ha : 0 ≤ a) :
    normalizedRootRank τ a ≤ 1 := by
  apply iSup_le
  intro j
  have h : τ.functional (normalizedRoot a j) ≤ τ.functional 1 :=
    τ.functional.monotone (normalizedRoot_le_one a ha j)
  rw [τ.normalized] at h
  apply ENNReal.ofReal_le_one.mpr
  exact (Complex.le_def.mp h).1


-- @@ L384-386 verbatim
lemma normalizedRootRank_smul (τ : TracialState A) (a : A) (t : ℝ) (ht : 0 < t) :
    normalizedRootRank τ (t • a) = normalizedRootRank τ a := by
  simp only [normalizedRootRank, normalizedRoot, normalizePositive_smul a t ht]


-- @@ L388-391 verbatim
lemma normalized_trace_le_rank (τ : TracialState A) (a : A) (ha : 0 ≤ a) :
    ENNReal.ofReal (τ.functional (normalizePositive a)).re ≤ normalizedRootRank τ a := by
  have h := le_iSup (fun j : ℕ => ENNReal.ofReal (τ.functional (normalizedRoot a j)).re) 0
  simpa [normalizedRootRank, normalizedRoot, CFC.nnrpow_one _ (normalizePositive_nonneg a ha)] using h


-- @@ L393-417 verbatim
lemma normalizedRoot_monotone (a : A) (ha : 0 ≤ a) : Monotone (normalizedRoot a) := by
  intro j k hjk
  have hjpos : 0 < ((j : ℝ≥0) + 1)⁻¹ := by positivity
  have hkpos : 0 < ((k : ℝ≥0) + 1)⁻¹ := by positivity
  have hexp : ((k : ℝ≥0) + 1)⁻¹ ≤ ((j : ℝ≥0) + 1)⁻¹ := by
    apply inv_anti₀ (by positivity)
    exact_mod_cast Nat.add_le_add_right hjk 1
  simp only [normalizedRoot, CFC.nnrpow_eq_pow, CFC.nnrpow_def]
  apply cfcₙ_mono
  · intro z hz
    have hz1 : z ≤ 1 :=
      (NonUnitalIsometricContinuousFunctionalCalculus.quasispectrum_le _ hz
        (normalizePositive_nonneg a ha)).trans (by exact_mod_cast normalizePositive_norm_le a)
    by_cases hz0 : z = 0
    · subst z
      change (0 : ℝ≥0) ^ (((j : ℝ≥0) + 1)⁻¹ : ℝ) ≤
        (0 : ℝ≥0) ^ (((k : ℝ≥0) + 1)⁻¹ : ℝ)
      rw [NNReal.zero_rpow (by exact_mod_cast (ne_of_gt hjpos)),
        NNReal.zero_rpow (by exact_mod_cast (ne_of_gt hkpos))]
    · apply NNReal.rpow_le_rpow_of_exponent_ge (pos_iff_ne_zero.mpr hz0) hz1
      exact_mod_cast hexp
  · exact (NNReal.continuous_nnrpow_const _).continuousOn
  · exact (NNReal.continuous_nnrpow_const _).continuousOn
  · exact NNReal.zero_rpow (by exact_mod_cast (ne_of_gt hjpos))
  · exact NNReal.zero_rpow (by exact_mod_cast (ne_of_gt hkpos))


-- @@ L419-425 verbatim
lemma normalizedRootRank_tendsto (τ : TracialState A) (a : A) (ha : 0 ≤ a) :
    Filter.Tendsto (fun j : ℕ => ENNReal.ofReal (τ.functional (normalizedRoot a j)).re)
      Filter.atTop (nhds (normalizedRootRank τ a)) := by
  apply tendsto_atTop_iSup
  intro j k hjk
  apply ENNReal.ofReal_le_ofReal
  exact (Complex.le_def.mp (τ.functional.monotone (normalizedRoot_monotone a ha hjk))).1


-- @@ L427-437 verbatim
lemma normalizedRootRank_pos (τ : TracialState A) (hsimple : TopologicallySimple A)
    (a : A) (ha : 0 ≤ a) (hne : a ≠ 0) : 0 < normalizedRootRank τ a := by
  have hn : normalizePositive a ≠ 0 :=
    smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr hne)) hne
  have hτn : τ.functional (normalizePositive a) ≠ 0 := by
    intro hzero
    exact hn (τ.faithful hsimple _ (normalizePositive_nonneg a ha) hzero)
  have hτpos : 0 < τ.functional (normalizePositive a) :=
    lt_of_le_of_ne (τ.functional.map_nonneg (normalizePositive_nonneg a ha)) hτn.symm
  have hreal : 0 < (τ.functional (normalizePositive a)).re := (Complex.pos_iff.mp hτpos).1
  exact (ENNReal.ofReal_pos.mpr hreal).trans_le (normalized_trace_le_rank τ a ha)


-- @@ L439-439 verbatim
end


-- @@ L441-441 verbatim
open Filter Topology


-- @@ L443-443 verbatim
variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]


-- @@ L445-459 verbatim
def sandwichSubalgebra (h : A) (hh : 0 ≤ h) : NonUnitalStarSubalgebra ℝ A where
  carrier := Set.range (fun w : A => h * w * h)
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, by noncomm_ring⟩
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x * h * h * y, by simp only [mul_assoc]⟩
  smul_mem' := by
    rintro t _ ⟨x, rfl⟩
    exact ⟨t • x, by simp only [mul_smul_comm, smul_mul_assoc]⟩
  star_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨star x, by simp only [star_mul, hh.star_eq, mul_assoc]⟩


-- @@ L461-462 verbatim
noncomputable def hereditarySubalgebra (h : A) (hh : 0 ≤ h) : NonUnitalStarSubalgebra ℝ A :=
  (sandwichSubalgebra h hh).topologicalClosure


-- @@ L464-464 verbatim
def hereditaryCarrier (h : A) : Set A := closure (Set.range (fun w : A => h * w * h))


-- @@ L466-467 verbatim
lemma hereditarySubalgebra_coe (h : A) (hh : 0 ≤ h) :
    (hereditarySubalgebra h hh : Set A) = hereditaryCarrier h := rfl


-- @@ L469-470 verbatim
instance hereditarySubalgebra_closed (h : A) (hh : 0 ≤ h) :
    IsClosed (hereditarySubalgebra h hh : Set A) := isClosed_closure


-- @@ L472-476 verbatim
lemma hereditary_sqrt_mem {h a : A} (hh : 0 ≤ h) (ha : 0 ≤ a)
    (ham : a ∈ hereditaryCarrier h) : CFC.sqrt a ∈ hereditaryCarrier h := by
  change CFC.sqrt a ∈ hereditarySubalgebra h hh
  rw [CFC.sqrt_eq_real_sqrt a ha]
  exact cfcₙ_mem Real.sqrt (show a ∈ hereditarySubalgebra h hh from ham)


-- @@ L478-481 verbatim
lemma self_mem_hereditary (h : A) (hh : 0 ≤ h) : h ∈ hereditaryCarrier h := by
  have hm : h * h ∈ hereditaryCarrier h := subset_closure ⟨1, by simp⟩
  have hs := hereditary_sqrt_mem hh (by simpa only [hh.star_eq] using star_mul_self_nonneg h) hm
  simpa only [CFC.sqrt_mul_self h hh] using hs


-- @@ L483-495 verbatim
omit [PartialOrder A] [StarOrderedRing A] in
lemma hereditary_sandwich_mem {h x y : A} (z : A)
    (hx : x ∈ hereditaryCarrier h) (hy : y ∈ hereditaryCarrier h) :
    x * z * y ∈ hereditaryCarrier h := by
  obtain ⟨u, hu, hux⟩ := mem_closure_iff_seq_limit.mp hx
  obtain ⟨v, hv, hvy⟩ := mem_closure_iff_seq_limit.mp hy
  apply isClosed_closure.mem_of_tendsto ((hux.mul_const z).mul hvy)
  apply Eventually.of_forall
  intro j
  obtain ⟨a, ha⟩ := hu j
  obtain ⟨b, hb⟩ := hv j
  apply subset_closure
  exact ⟨a * h * z * h * b, by simp only [← ha, ← hb, mul_assoc]⟩


-- @@ L497-500 verbatim
lemma sqrt_sandwich_mem_hereditary (h z : A) (hh : 0 ≤ h) :
    CFC.sqrt h * z * CFC.sqrt h ∈ hereditaryCarrier h := by
  have hm := hereditary_sqrt_mem hh hh (self_mem_hereditary h hh)
  exact hereditary_sandwich_mem z hm hm


-- @@ L502-509 verbatim
lemma normalizedRoot_mem_hereditary {h a : A} (hh : 0 ≤ h)
    (ha : a ∈ hereditaryCarrier h) (ha0 : 0 ≤ a) (j : ℕ) :
    normalizedRoot a j ∈ hereditaryCarrier h := by
  change normalizedRoot a j ∈ hereditarySubalgebra h hh
  unfold normalizedRoot
  rw [CFC.nnrpow_eq_pow, CFC.nnrpow_def, cfcₙ_nnreal_eq_real _ _ (normalizePositive_nonneg a ha0)]
  apply cfcₙ_mem
  exact (hereditarySubalgebra h hh).smul_mem (‖a‖⁻¹) ha


-- @@ L511-511 verbatim
end Pureness


-- @@ L513-513 verbatim
end


-- @@ L515-515 verbatim
end OAI
