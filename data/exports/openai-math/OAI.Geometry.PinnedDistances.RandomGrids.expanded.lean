import OAI.Geometry.PinnedDistances.Hierarchy


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u1 u2 u3


-- @@ L7-7 verbatim
section

-- @@ L8-8 verbatim
noncomputable section

-- @@ L9-9 verbatim
open NumberField

-- @@ L10-10 verbatim
open scoped BigOperators

-- @@ L11-11 verbatim
noncomputable section

-- @@ L12-12 verbatim
open MeasureTheory

-- @@ L13-15 verbatim
open scoped Topology

/- Square-grid construction and the finite-shift sharing law. -/


-- @@ L17-17 verbatim
noncomputable section

-- @@ L18-18 verbatim
open MeasureTheory

-- @@ L19-19 verbatim
open scoped Topology ENNReal

-- @@ L20-20 verbatim
namespace WeakPinned.Grid


-- @@ L22-22 verbatim
def bin (l s x : ℝ) : ℤ := ⌊(x-s)/l⌋

-- @@ L23-23 verbatim
def shares (l s x y : ℝ) : ℝ := if bin l s x = bin l s y then 1 else 0


-- @@ L25-29 verbatim
lemma bin_period {l : ℝ} (hl : 0 < l) (s x : ℝ) :
    bin l (s+l) x = bin l s x - 1 := by
  unfold bin
  rw [show (x-(s+l))/l = (x-s)/l - 1 by field_simp; ring]
  exact Int.floor_sub_one _


-- @@ L31-34 verbatim
lemma shares_period {l : ℝ} (hl : 0 < l) (x y : ℝ) :
    Function.Periodic (fun s => shares l s x y) l := by
  intro s
  simp [shares, bin_period hl]


-- @@ L36-37 verbatim
lemma shares_symm (l s x y : ℝ) : shares l s x y = shares l s y x := by
  simp only [shares, eq_comm]


-- @@ L39-43 verbatim
lemma measurable_shares (l x y : ℝ) : Measurable (fun s => shares l s x y) := by
  apply Measurable.ite _ measurable_const measurable_const
  exact measurableSet_eq_fun
    (((measurable_const.sub measurable_id).div_const l).floor)
    (((measurable_const.sub measurable_id).div_const l).floor)


-- @@ L45-54 verbatim
lemma bin_small_shift {l x s : ℝ} (hl : 0 < l) (hs : s ∈ Set.Ioc x (x+l)) :
    bin l s x = -1 := by
  apply Int.floor_eq_iff.mpr
  constructor
  · apply (le_div_iff₀ hl).mpr
    norm_num
    linarith [hs.2]
  · apply (div_lt_iff₀ hl).mpr
    norm_num
    linarith [hs.1]


-- @@ L56-74 verbatim
lemma shares_small_shift {l x y s : ℝ} (hl : 0 < l) (hxy : x ≤ y)
    (hs : s ∈ Set.Ioc x (x+l)) : shares l s x y = if y < s then 1 else 0 := by
  have he : bin l s y = -1 ↔ y < s := by
    simp only [bin, Int.floor_eq_iff]
    constructor
    · intro h
      have := (div_lt_iff₀ hl).mp h.2
      norm_num at this
      linarith
    · intro h
      constructor
      · apply (le_div_iff₀ hl).mpr
        norm_num
        linarith [hs.2]
      · apply (div_lt_iff₀ hl).mpr
        norm_num
        linarith
  simp only [shares, bin_small_shift hl hs, eq_comm (a := (-1 : ℤ))]
  simp only [he]


-- @@ L76-102 verbatim
lemma shares_integral {l : ℝ} (hl : 0 < l) (x y : ℝ) :
    (∫ s : ℝ in Set.Ioc 0 l, shares l s x y) = max 0 (l-|x-y|) := by
  wlog hxy : x ≤ y
  · simpa only [shares_symm l _ x y, abs_sub_comm x y] using this hl y x (le_of_not_ge hxy)
  have hp := (shares_period hl x y).intervalIntegral_add_eq 0 x
  simp only [zero_add] at hp
  rw [intervalIntegral.integral_of_le hl.le,
    intervalIntegral.integral_of_le (by linarith : x ≤ x+l)] at hp
  rw [hp]
  have he : (∫ s : ℝ in Set.Ioc x (x+l), shares l s x y) =
      ∫ s : ℝ in Set.Ioc x (x+l), if y < s then (1 : ℝ) else 0 := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    exact shares_small_shift hl hxy hs
  rw [he]
  change (∫ s : ℝ in Set.Ioc x (x+l), (Set.Ioi y).indicator (fun _ => (1 : ℝ)) s) = _
  rw [setIntegral_indicator measurableSet_Ioi]
  rw [show Set.Ioc x (x+l) ∩ Set.Ioi y = Set.Ioc y (x+l) by
    ext s; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioi]; constructor
    · rintro ⟨⟨h₁,h₂⟩,h₃⟩; exact ⟨h₃,h₂⟩
    · intro h; exact ⟨⟨hxy.trans_lt h.1,h.2⟩,h.1⟩]
  rw [setIntegral_const]
  simp only [Measure.real, Real.volume_Ioc, smul_eq_mul, mul_one, ENNReal.toReal_ofReal']
  rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
  rw [max_comm]
  congr 1
  ring


-- @@ L104-107 verbatim
lemma shares_integrableOn (l x y a b : ℝ) :
    IntegrableOn (fun s => shares l s x y) (Set.Ioc a b) := by
  apply IntegrableOn.of_bound measure_Ioc_lt_top (measurable_shares l x y).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun s => by unfold shares; split_ifs <;> norm_num)


-- @@ L109-116 verbatim
/-- Independent uniform shifts in the two axes give a product of overlap lengths.
    This integral is unnormalized planar Lebesgue mass. -/
lemma square_shares_integral {l : ℝ} (hl : 0 < l) (x y : ℝ × ℝ) :
    (∫ s₁ : ℝ in Set.Ioc 0 l, ∫ s₂ : ℝ in Set.Ioc 0 l,
      shares l s₁ x.1 y.1 * shares l s₂ x.2 y.2) =
      max 0 (l-|x.1-y.1|) * max 0 (l-|x.2-y.2|) := by
  simp_rw [integral_const_mul]
  rw [integral_mul_const, shares_integral hl, shares_integral hl]


-- @@ L118-138 verbatim
lemma shares_gap {l : ℝ} (hl : 0 < l) {s x y : ℝ}
    (h : bin l s x = bin l s y) : |x-y| < l := by
  have hx := Int.floor_le ((x-s)/l)
  have hy := Int.lt_floor_add_one ((y-s)/l)
  have hx' := Int.floor_le ((y-s)/l)
  have hy' := Int.lt_floor_add_one ((x-s)/l)
  change (bin l s x : ℝ) ≤ (x-s)/l at hx
  change (y-s)/l < (bin l s y : ℝ) + 1 at hy
  change (bin l s y : ℝ) ≤ (y-s)/l at hx'
  change (x-s)/l < (bin l s x : ℝ) + 1 at hy'
  rw [h] at hx hy'
  rw [abs_lt]
  constructor
  · have : (y-s)/l < (x-s)/l+1 := by linarith
    have hh := (div_lt_iff₀ hl).mp this
    field_simp at hh
    linarith
  · have : (x-s)/l < (y-s)/l+1 := by linarith
    have hh := (div_lt_iff₀ hl).mp this
    field_simp at hh
    linarith


-- @@ L140-146 verbatim
lemma bin_double {l : ℝ} (hl : 0 < l) (s x : ℝ) (b : ℤ) :
    bin (2*l) (s+b*l) x = (bin l s x-b)/2 := by
  unfold bin
  rw [show (x-(s+b*l))/(2*l) = ((x-s)/l-b)/2 by field_simp; ring]
  have hh := Int.floor_div_natCast (((x-s)/l)-(b:ℝ)) 2
  norm_num only [Nat.cast_ofNat, Int.floor_sub_intCast] at hh
  exact hh


-- @@ L148-150 verbatim
lemma nested_bins {l : ℝ} (hl : 0 < l) (s x y : ℝ) (b : ℤ)
    (h : bin l s x = bin l s y) : bin (2*l) (s+b*l) x = bin (2*l) (s+b*l) y := by
  rw [bin_double hl, bin_double hl, h]


-- @@ L152-154 verbatim
/-- Normalized Lebesgue measure on a half-open interval of positive length. -/
def uniformInterval (l : ℝ) : Measure ℝ :=
  (ENNReal.ofReal l)⁻¹ • volume.restrict (Set.Ioc 0 l)


-- @@ L156-161 verbatim
lemma uniformInterval_probability {l : ℝ} (hl : 0 < l) :
    IsProbabilityMeasure (uniformInterval l) := by
  constructor
  simp only [uniformInterval, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, Real.volume_Ioc, sub_zero, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hl)) ENNReal.ofReal_ne_top


-- @@ L163-170 verbatim
instance uniformInterval_finite (l : ℝ) : IsFiniteMeasure (uniformInterval l) := by
  by_cases hl : 0 < l
  · let := uniformInterval_probability hl
    infer_instance
  · have hz : uniformInterval l = 0 := by
      simp [uniformInterval, Set.Ioc_eq_empty_of_le (not_lt.mp hl)]
    rw [hz]
    infer_instance


-- @@ L172-182 verbatim
lemma translate_restrict_Ioc (l : ℝ) :
    (volume.restrict (Set.Ioc 0 l)).map (fun x => x+l) =
      volume.restrict (Set.Ioc l (l+l)) := by
  have hh := (measurePreserving_add_right volume l).restrict_preimage
    (measurableSet_Ioc (a := l) (b := l+l))
  have he : (fun x : ℝ => x+l) ⁻¹' Set.Ioc l (l+l) = Set.Ioc 0 l := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioc]
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  rw [he] at hh
  exact hh.map_eq


-- @@ L184-186 verbatim
open ProbabilityTheory in
/-- A fair binary step of length `l`. -/
def binaryStep (l : ℝ) : Measure ℝ := bernoulliMeasure 0 l ⟨1/2, by norm_num⟩


-- @@ L188-190 verbatim
instance binaryStep_probability (l : ℝ) : IsProbabilityMeasure (binaryStep l) := by
  unfold binaryStep
  infer_instance


-- @@ L192-205 verbatim
lemma binaryStep_eq (l : ℝ) :
    binaryStep l = (2 : ℝ≥0∞)⁻¹ • Measure.dirac 0 + (2 : ℝ≥0∞)⁻¹ • Measure.dirac l := by
  simp only [binaryStep, ProbabilityTheory.bernoulliMeasure_def]
  rw [← Measure.coe_nnreal_smul, ← Measure.coe_nnreal_smul]
  congr 2
  · rw [← ENNReal.ofReal_coe_nnreal]
    change ENNReal.ofReal ((1:ℝ)/2) = _
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  · rw [← ENNReal.ofReal_coe_nnreal]
    change ENNReal.ofReal (1-(1:ℝ)/2) = _
    norm_num only [show (1-(1:ℝ)/2) = 1/2 by norm_num]
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num


-- @@ L207-220 verbatim
lemma uniform_double {l : ℝ} (hl : 0 < l) :
    (uniformInterval l).conv (binaryStep l) = uniformInterval (2*l) := by
  rw [binaryStep_eq, Measure.conv_add, Measure.conv_smul_right,
    Measure.conv_smul_right, Measure.conv_dirac_zero, Measure.conv_dirac]
  rw [uniformInterval, Measure.map_smul _ (by fun_prop), translate_restrict_Ioc]
  have hu : Set.Ioc 0 l ∪ Set.Ioc l (l+l) = Set.Ioc 0 (2*l) := by
    rw [Set.Ioc_union_Ioc_eq_Ioc hl.le (by linarith)]
    congr 1; linarith
  have hd : Disjoint (Set.Ioc 0 l) (Set.Ioc l (l+l)) :=
    Set.disjoint_left.mpr (by intro x h₁ h₂; exact (not_lt_of_ge h₁.2) h₂.1)
  rw [smul_smul, smul_smul, ← smul_add, ← Measure.restrict_union hd measurableSet_Ioc, hu]
  congr 1
  rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
  norm_num [ENNReal.mul_inv]


-- @@ L222-226 verbatim
/-- One initial uniform shift followed by independent fair coarsening bits,
    before introducing phase and orientation. -/
def incrementLaw : ℕ → Measure ℝ
  | 0 => uniformInterval 1
  | n+1 => binaryStep (2^n)


-- @@ L228-231 verbatim
instance incrementLaw_probability (n : ℕ) : IsProbabilityMeasure (incrementLaw n) := by
  cases n with
  | zero => exact uniformInterval_probability zero_lt_one
  | succ n => exact binaryStep_probability _


-- @@ L233-233 verbatim
def axisLaw : Measure (ℕ → ℝ) := Measure.infinitePi incrementLaw

-- @@ L234-236 verbatim
instance axisLaw_probability : IsProbabilityMeasure axisLaw := by
  unfold axisLaw
  infer_instance


-- @@ L238-238 verbatim
def shift (n : ℕ) (ω : ℕ → ℝ) : ℝ := ∑ i ∈ Finset.range (n+1), ω i


-- @@ L240-241 verbatim
lemma measurable_shift (n : ℕ) : Measurable (shift n) := by
  exact Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)


-- @@ L243-243 verbatim
lemma shift_zero (ω : ℕ → ℝ) : shift 0 ω = ω 0 := by simp [shift]

-- @@ L244-245 verbatim
lemma shift_succ (n : ℕ) (ω : ℕ → ℝ) :
    shift (n+1) ω = shift n ω + ω (n+1) := by simp [shift, Finset.sum_range_succ]


-- @@ L247-269 verbatim
lemma map_shift (n : ℕ) : axisLaw.map (shift n) = uniformInterval (2^n) := by
  induction n with
  | zero =>
      simp only [pow_zero]
      rw [show shift 0 = (fun ω => ω 0) by funext ω; exact shift_zero ω]
      exact Measure.infinitePi_map_eval incrementLaw 0
  | succ n ih =>
      have hind := ProbabilityTheory.iIndepFun_infinitePi
        (P := incrementLaw) (X := fun _ => id) (fun _ => measurable_id)
      have hi := hind.indepFun_finsetSum_of_notMem
        (fun i => measurable_pi_apply i) (s := Finset.range (n+1)) (i := n+1) (by simp)
      have he : (∑ j ∈ Finset.range (n+1), (fun ω : ℕ → ℝ => id (ω j))) = shift n := by
        funext ω
        simp [shift]
      rw [he] at hi
      have hm := hi.map_add_eq_map_conv_map₀ (measurable_shift n).aemeasurable
        (measurable_pi_apply (n+1)).aemeasurable
      change axisLaw.map (fun ω => shift n ω + ω (n+1)) = _ at hm
      simp only [← shift_succ] at hm
      change axisLaw.map (shift (n+1)) = (axisLaw.map (shift n)).conv ((Measure.infinitePi incrementLaw).map (fun f => f (n+1))) at hm
      rw [ih, Measure.infinitePi_map_eval incrementLaw (n+1)] at hm
      rw [incrementLaw, uniform_double (by positivity)] at hm
      simpa only [pow_succ, mul_comm (2^n) (2:ℝ)] using hm


-- @@ L271-277 verbatim
lemma integral_uniform_shares {l : ℝ} (hl : 0 < l) (x y : ℝ) :
    (∫ s, shares l s x y ∂uniformInterval l) = max 0 (1-|x-y|/l) := by
  rw [uniformInterval, integral_smul_measure, shares_integral hl]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal hl.le, smul_eq_mul]
  rw [mul_max_of_nonneg _ _ (inv_nonneg.mpr hl.le), mul_zero]
  congr 1
  field_simp


-- @@ L279-284 verbatim
lemma integral_shift_shares (n : ℕ) (x y : ℝ) :
    (∫ ω, shares (2^n) (shift n ω) x y ∂axisLaw) =
      max 0 (1-|x-y|/(2^n)) := by
  rw [← integral_map (measurable_shift n).aemeasurable
    (measurable_shares (2^n) x y).aestronglyMeasurable, map_shift]
  exact integral_uniform_shares (by positivity) x y


-- @@ L286-293 verbatim
lemma integral_shares_nat_periods {l : ℝ} (hl : 0 < l) (k : ℕ) (x y : ℝ) :
    (∫ s in Set.Ioc 0 (k*l), shares l s x y) = (k:ℝ)*max 0 (l-|x-y|) := by
  have hh := (shares_period hl x y).intervalIntegral_add_zsmul_eq (k:ℤ) 0
    (fun a b => ⟨shares_integrableOn l x y a b, shares_integrableOn l x y b a⟩)
  simp only [zero_add, zsmul_eq_mul, Int.cast_natCast,
    intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ k*l),
    intervalIntegral.integral_of_le hl.le, shares_integral hl] at hh
  exact hh


-- @@ L295-311 verbatim
/-- The fine-scale shift is the original unit shift. Its sharing law is still
    the correct uniform-modulo-side law, not a fresh independent grid. -/
lemma integral_fine_shares (n : ℕ) (x y : ℝ) :
    (∫ ω, shares ((2:ℝ)^(- (n:ℤ))) (shift 0 ω) x y ∂axisLaw) =
      max 0 (1-|x-y|/((2:ℝ)^(- (n:ℤ)))) := by
  rw [← integral_map (measurable_shift 0).aemeasurable
    (measurable_shares _ x y).aestronglyMeasurable, map_shift]
  simp only [pow_zero, uniformInterval, ENNReal.ofReal_one, inv_one, one_smul]
  have hl : 0 < (2:ℝ)^(-(n:ℤ)) := by positivity
  have he : ((2^n:ℕ):ℝ)*(2:ℝ)^(-(n:ℤ)) = 1 := by
    simp [zpow_neg, zpow_natCast]
  have hh := integral_shares_nat_periods hl (2^n) x y
  rw [he] at hh
  rw [hh, mul_max_of_nonneg _ _ (by positivity : (0:ℝ) ≤ ((2^n:ℕ):ℝ)), mul_zero]
  congr 1
  simp only [Nat.cast_pow, Nat.cast_ofNat, zpow_neg, zpow_natCast, div_inv_eq_mul]
  field_simp


-- @@ L313-320 verbatim
lemma binaryStep_ae (l : ℝ) : ∀ᵐ x ∂binaryStep l, x = 0 ∨ x = l := by
  rw [binaryStep_eq]
  simp only [ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    exact (ae_dirac_iff (by measurability)).mpr (Or.inl rfl)
  · apply Measure.ae_smul_measure
    exact (ae_dirac_iff (by measurability)).mpr (Or.inr rfl)


-- @@ L322-327 verbatim
lemma axis_increment_ae (n : ℕ) :
    ∀ᵐ ω ∂axisLaw, ω (n+1) = 0 ∨ ω (n+1) = (2:ℝ)^n := by
  have hh : ∀ᵐ x ∂incrementLaw (n+1), x = 0 ∨ x = (2:ℝ)^n := binaryStep_ae _
  apply ae_of_ae_map (μ := axisLaw) (f := fun ω : ℕ → ℝ => ω (n+1))
    (p := fun x : ℝ => x = 0 ∨ x = (2:ℝ)^n) (measurable_pi_apply (n+1)).aemeasurable
  simpa only [axisLaw, Measure.infinitePi_map_eval] using hh


-- @@ L329-338 verbatim
lemma bins_nested_ae (n : ℕ) (x y : ℝ) :
    ∀ᵐ ω ∂axisLaw, bin (2^n) (shift n ω) x = bin (2^n) (shift n ω) y →
      bin (2^(n+1)) (shift (n+1) ω) x = bin (2^(n+1)) (shift (n+1) ω) y := by
  filter_upwards [axis_increment_ae n] with ω hω
  intro h
  rcases hω with hω | hω
  · simpa only [shift_succ, hω, pow_succ, mul_comm (2^n) (2:ℝ),
      Int.cast_zero, zero_mul, add_zero] using nested_bins (by positivity) (shift n ω) x y 0 h
  · simpa only [shift_succ, hω, pow_succ, mul_comm (2^n) (2:ℝ),
      Int.cast_one, one_mul] using nested_bins (by positivity) (shift n ω) x y 1 h


-- @@ L340-341 verbatim
/-- Both independent axis constructions, before phase and rotation. -/
abbrev GridSample := (ℕ → ℝ) × (ℕ → ℝ)

-- @@ L342-342 verbatim
def squareLaw : Measure GridSample := axisLaw.prod axisLaw

-- @@ L343-345 verbatim
instance squareLaw_probability : IsProbabilityMeasure squareLaw := by
  unfold squareLaw
  infer_instance


-- @@ L347-347 verbatim
def shiftZ (m : ℤ) (ω : ℕ → ℝ) : ℝ := shift m.toNat ω


-- @@ L349-351 verbatim
def shareAt (m : ℤ) (ω : GridSample) (x y : ℝ × ℝ) : Prop :=
  bin ((2:ℝ)^m) (shiftZ m ω.1) x.1 = bin ((2:ℝ)^m) (shiftZ m ω.1) y.1 ∧
  bin ((2:ℝ)^m) (shiftZ m ω.2) x.2 = bin ((2:ℝ)^m) (shiftZ m ω.2) y.2


-- @@ L353-362 verbatim
lemma measurableSet_shareAt (m : ℤ) (x y : ℝ × ℝ) :
    MeasurableSet {ω | shareAt m ω x y} := by
  unfold shareAt bin shiftZ
  apply MeasurableSet.inter
  · exact measurableSet_eq_fun
      (((measurable_const.sub ((measurable_shift _).comp measurable_fst)).div_const _).floor)
      (((measurable_const.sub ((measurable_shift _).comp measurable_fst)).div_const _).floor)
  · exact measurableSet_eq_fun
      (((measurable_const.sub ((measurable_shift _).comp measurable_snd)).div_const _).floor)
      (((measurable_const.sub ((measurable_shift _).comp measurable_snd)).div_const _).floor)


-- @@ L364-374 verbatim
lemma integral_shiftZ_shares (m : ℤ) (x y : ℝ) :
    (∫ ω, shares ((2:ℝ)^m) (shiftZ m ω) x y ∂axisLaw) =
      max 0 (1-|x-y|/((2:ℝ)^m)) := by
  cases m with
  | ofNat n =>
      change (∫ ω, shares ((2:ℝ)^(n:ℤ)) (shift n ω) x y ∂axisLaw) =
        max 0 (1-|x-y|/((2:ℝ)^(n:ℤ)))
      simpa only [zpow_natCast] using integral_shift_shares n x y
  | negSucc n =>
      simpa [shiftZ, Int.negSucc_eq, Int.toNat_of_nonpos] using
        integral_fine_shares (n+1) x y


-- @@ L376-390 verbatim
lemma sharing_probability (m : ℤ) (x y : ℝ × ℝ) :
    squareLaw.real {ω | shareAt m ω x y} =
      max 0 (1-|x.1-y.1|/((2:ℝ)^m)) * max 0 (1-|x.2-y.2|/((2:ℝ)^m)) := by
  rw [← integral_indicator_one (measurableSet_shareAt m x y)]
  have he : (fun ω : GridSample => Set.indicator {ω | shareAt m ω x y} 1 ω) =
      (fun ω => shares ((2:ℝ)^m) (shiftZ m ω.1) x.1 y.1 *
        shares ((2:ℝ)^m) (shiftZ m ω.2) x.2 y.2) := by
    funext ω
    simp only [Set.indicator, Set.mem_ofPred_eq, shareAt, shares, Pi.one_apply]
    by_cases h₁ : bin ((2:ℝ)^m) (shiftZ m ω.1) x.1 = bin ((2:ℝ)^m) (shiftZ m ω.1) y.1 <;>
      by_cases h₂ : bin ((2:ℝ)^m) (shiftZ m ω.2) x.2 = bin ((2:ℝ)^m) (shiftZ m ω.2) y.2 <;>
      simp [h₁,h₂]
  rw [he, squareLaw, integral_prod_mul (fun ω : ℕ → ℝ => shares ((2:ℝ)^m) (shiftZ m ω) x.1 y.1)
    (fun ω : ℕ → ℝ => shares ((2:ℝ)^m) (shiftZ m ω) x.2 y.2),
    integral_shiftZ_shares, integral_shiftZ_shares]


-- @@ L392-401 verbatim
lemma max_sharing_bound {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    1 - max 0 (1-a) * max 0 (1-b) ≤ a+b := by
  by_cases ha' : a ≤ 1
  · by_cases hb' : b ≤ 1
    · rw [max_eq_right (by linarith), max_eq_right (by linarith)]
      nlinarith [mul_nonneg ha hb]
    · rw [max_eq_left (show 1-b ≤ 0 by linarith)]
      nlinarith
  · rw [max_eq_left (by linarith)]
    nlinarith


-- @@ L403-409 verbatim
lemma separation_probability_le (m : ℤ) (x y : ℝ × ℝ) :
    squareLaw.real {ω | ¬ shareAt m ω x y} ≤
      (|x.1-y.1|+|x.2-y.2|)/((2:ℝ)^m) := by
  change squareLaw.real {ω | shareAt m ω x y}ᶜ ≤ _
  rw [measureReal_compl (measurableSet_shareAt m x y), probReal_univ,
    sharing_probability, add_div]
  exact max_sharing_bound (by positivity) (by positivity)


-- @@ L411-422 verbatim
lemma share_eventually_exists (x y : ℝ × ℝ) :
    ∀ᵐ ω ∂squareLaw, ∃ n : ℕ, shareAt n ω x y := by
  rw [ae_iff]
  apply (measureReal_eq_zero_iff).mp
  apply le_antisymm _ (measureReal_nonneg)
  have hb (n : ℕ) : squareLaw.real {ω | ¬ ∃ n : ℕ, shareAt n ω x y} ≤
      (|x.1-y.1|+|x.2-y.2|)/((2:ℝ)^n) := by
    refine (measureReal_mono (s₂ := {ω | ¬ shareAt (n:ℤ) ω x y})
      (by intro ω h hn; exact h ⟨n, hn⟩)).trans ?_
    simpa only [zpow_natCast] using separation_probability_le (n:ℤ) x y
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds
    (tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2))) hb


-- @@ L424-438 verbatim
lemma axis_nestedZ_ae (m : ℤ) (x y : ℝ) :
    ∀ᵐ ω ∂axisLaw, bin ((2:ℝ)^m) (shiftZ m ω) x = bin ((2:ℝ)^m) (shiftZ m ω) y →
      bin ((2:ℝ)^(m+1)) (shiftZ (m+1) ω) x = bin ((2:ℝ)^(m+1)) (shiftZ (m+1) ω) y := by
  by_cases hm : 0 ≤ m
  · obtain ⟨n,rfl⟩ := Int.eq_ofNat_of_zero_le hm
    rw [show (n:ℤ)+1 = ((n+1:ℕ):ℤ) by omega]
    simpa only [shiftZ, Int.toNat_natCast, zpow_natCast] using bins_nested_ae n x y
  · have hm' : m+1 ≤ 0 := by omega
    filter_upwards with ω
    intro h
    simp only [shiftZ, Int.toNat_of_nonpos (by omega : m ≤ 0)] at h
    have hh := nested_bins (by positivity : 0 < (2:ℝ)^m) (shift 0 ω) x y 0
    simpa only [shiftZ, Int.toNat_of_nonpos (by omega : m ≤ 0),
      Int.toNat_of_nonpos hm', zpow_add₀ (by norm_num : (2:ℝ)≠0), zpow_one,
      mul_comm ((2:ℝ)^m) (2:ℝ), Int.cast_zero, zero_mul, add_zero] using hh h


-- @@ L440-444 verbatim
lemma shareAt_nested_ae (m : ℤ) (x y : ℝ × ℝ) :
    ∀ᵐ ω ∂squareLaw, shareAt m ω x y → shareAt (m+1) ω x y := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (axis_nestedZ_ae m x.1 y.1),
    Measure.quasiMeasurePreserving_snd.ae (axis_nestedZ_ae m x.2 y.2)] with ω hx hy
  exact fun h => ⟨hx h.1, hy h.2⟩


-- @@ L446-447 verbatim
lemma shareAt_symm (m : ℤ) (ω : GridSample) (x y : ℝ × ℝ) :
    shareAt m ω x y ↔ shareAt m ω y x := by simp [shareAt, eq_comm]

-- @@ L448-450 verbatim
lemma shareAt_trans (m : ℤ) (ω : GridSample) (x y z : ℝ × ℝ)
    (hxy : shareAt m ω x y) (hyz : shareAt m ω y z) : shareAt m ω x z :=
  ⟨hxy.1.trans hyz.1, hxy.2.trans hyz.2⟩


-- @@ L452-463 verbatim
lemma shareAt_bddBelow (ω : GridSample) {x y : ℝ × ℝ} (hxy : x ≠ y) :
    BddBelow {m : ℤ | shareAt m ω x y} := by
  have bound {a b : ℝ} (h : a ≠ b) (f : ℤ → ℝ) :
      BddBelow {m : ℤ | bin ((2:ℝ)^m) (f m) a = bin ((2:ℝ)^m) (f m) b} := by
    obtain ⟨k,hk⟩ := exists_mem_Ico_zpow (abs_pos.mpr (sub_ne_zero.mpr h)) (by norm_num : (1:ℝ)<2)
    refine ⟨k, fun m hm => ?_⟩
    have hh := shares_gap (by positivity : 0 < (2:ℝ)^m) hm
    exact (zpow_le_zpow_iff_right₀ (by norm_num : (1:ℝ)<2)).mp (hk.1.trans hh.le)
  by_cases h₁ : x.1 = y.1
  · have h₂ : x.2 ≠ y.2 := fun h₂ => hxy (Prod.ext h₁ h₂)
    exact (bound h₂ (fun m => shiftZ m ω.2)).mono (fun _ h => h.2)
  · exact (bound h₁ (fun m => shiftZ m ω.1)).mono (fun _ h => h.1)


-- @@ L465-465 verbatim
def minScale (ω : GridSample) (x y : ℝ × ℝ) : ℤ := sInf {m | shareAt m ω x y}


-- @@ L467-468 verbatim
def gridDepth (ω : GridSample) (x y : ℝ × ℝ) : ℝ :=
  -(minScale ω x y : ℝ) * Real.log 2


-- @@ L470-475 verbatim
lemma minScale_symm (ω : GridSample) (x y : ℝ × ℝ) :
    minScale ω x y = minScale ω y x := by
  unfold minScale
  congr 1
  ext m
  exact shareAt_symm m ω x y


-- @@ L477-479 verbatim
lemma minScale_mem {ω : GridSample} {x y : ℝ × ℝ} (hxy : x ≠ y)
    (he : ∃ m, shareAt m ω x y) : shareAt (minScale ω x y) ω x y :=
  Int.csInf_mem he (shareAt_bddBelow ω hxy)


-- @@ L481-483 verbatim
lemma minScale_le {ω : GridSample} {x y : ℝ × ℝ} (hxy : x ≠ y)
    {m : ℤ} (hm : shareAt m ω x y) : minScale ω x y ≤ m :=
  csInf_le (shareAt_bddBelow ω hxy) hm


-- @@ L485-493 verbatim
lemma shareAt_iff_minScale_le {ω : GridSample} {x y : ℝ × ℝ} (hxy : x ≠ y)
    (he : ∃ m, shareAt m ω x y)
    (hn : ∀ m, shareAt m ω x y → shareAt (m+1) ω x y) (m : ℤ) :
    shareAt m ω x y ↔ minScale ω x y ≤ m := by
  constructor
  · exact minScale_le hxy
  · intro hm
    have hmono : Monotone (fun k => shareAt k ω x y) := monotone_int_of_le_succ hn
    exact hmono hm (minScale_mem hxy he)


-- @@ L495-523 verbatim
lemma minScale_eq_iff {ω : GridSample} {x y : ℝ × ℝ} (hxy : x ≠ y) (m : ℤ) :
    minScale ω x y = m ↔
      (shareAt m ω x y ∧ ∀ k : ℤ, k < m → ¬ shareAt k ω x y) ∨
      (m = 0 ∧ ¬ ∃ k : ℤ, shareAt k ω x y) := by
  by_cases he : ∃ k, shareAt k ω x y
  · have hs := minScale_mem hxy he
    constructor
    · intro h
      left
      rw [h] at hs
      refine ⟨hs, fun k hk hks => ?_⟩
      have hh := minScale_le hxy hks
      omega
    · rintro (⟨hm,hmin⟩ | ⟨_,hn⟩)
      · apply le_antisymm (minScale_le hxy hm)
        by_contra h
        exact hmin _ (by omega) hs
      · exact False.elim (hn he)
  · have hz : minScale ω x y = 0 := by
      unfold minScale
      rw [show {m | shareAt m ω x y} = ∅ by ext m; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false]; exact iff_false_intro (fun h => he ⟨m,h⟩)]
      exact Int.csInf_empty
    simp only [hz]
    constructor
    · intro hm
      exact Or.inr ⟨hm.symm,he⟩
    · rintro (⟨hm,_⟩ | ⟨rfl,_⟩)
      · exact False.elim (he ⟨m,hm⟩)
      · rfl


-- @@ L525-551 verbatim
lemma measurable_minScale {x y : ℝ × ℝ} (hxy : x ≠ y) :
    Measurable (fun ω => minScale ω x y) := by
  apply measurable_to_countable'
  intro m
  change MeasurableSet {ω | minScale ω x y = m}
  have he : {ω : GridSample | minScale ω x y = m} =
      ({ω | shareAt m ω x y} ∩ {ω | ∀ k < m, ¬shareAt k ω x y}) ∪
      ({ω | m = 0} ∩ {ω | ¬∃ k, shareAt k ω x y}) := by
    ext ω
    exact minScale_eq_iff hxy m
  rw [he]
  apply MeasurableSet.union
  · apply (measurableSet_shareAt m x y).inter
    have he : {ω : GridSample | ∀ k < m, ¬shareAt k ω x y} =
        ⋂ k : ℤ, ⋂ (_ : k < m), {ω : GridSample | shareAt k ω x y}ᶜ := by
      ext ω
      simp
    rw [he]
    exact MeasurableSet.iInter fun k =>
      MeasurableSet.iInter fun (_ : k < m) => (measurableSet_shareAt k x y).compl
  · apply (MeasurableSet.const (m = 0)).inter
    have he : {ω : GridSample | ¬∃ k, shareAt k ω x y} =
        (⋃ k : ℤ, {ω : GridSample | shareAt k ω x y})ᶜ := by
      ext ω
      simp
    rw [he]
    exact (MeasurableSet.iUnion fun k => measurableSet_shareAt k x y).compl


-- @@ L553-555 verbatim
lemma measurable_gridDepth {x y : ℝ × ℝ} (hxy : x ≠ y) :
    Measurable (fun ω => gridDepth ω x y) := by
  exact (((measurable_of_countable (fun n : ℤ => (n:ℝ))).comp (measurable_minScale hxy)).neg).mul_const _


-- @@ L557-582 verbatim
lemma gridDepth_ultra_ae {x y z : ℝ × ℝ} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    ∀ᵐ ω ∂squareLaw, min (gridDepth ω x y) (gridDepth ω y z) ≤ gridDepth ω x z := by
  have hn : ∀ᵐ ω ∂squareLaw, ∀ m : ℤ,
      (shareAt m ω x y → shareAt (m+1) ω x y) ∧
      (shareAt m ω y z → shareAt (m+1) ω y z) := by
    rw [ae_all_iff]
    intro m
    filter_upwards [shareAt_nested_ae m x y, shareAt_nested_ae m y z] with ω h₁ h₂ using ⟨h₁,h₂⟩
  filter_upwards [share_eventually_exists x y, share_eventually_exists y z, hn] with ω h₁ h₂ hn
  have e₁ : ∃ m : ℤ, shareAt m ω x y := by obtain ⟨n,hn⟩ := h₁; exact ⟨n,hn⟩
  have e₂ : ∃ m : ℤ, shareAt m ω y z := by obtain ⟨n,hn⟩ := h₂; exact ⟨n,hn⟩
  have hm : minScale ω x z ≤ max (minScale ω x y) (minScale ω y z) := by
    apply minScale_le hxz
    apply shareAt_trans _ ω x y z
    · exact (shareAt_iff_minScale_le hxy e₁ (fun m => (hn m).1) _).mpr (le_max_left _ _)
    · exact (shareAt_iff_minScale_le hyz e₂ (fun m => (hn m).2) _).mpr (le_max_right _ _)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold gridDepth
  have hm' : (minScale ω x z : ℝ) ≤ max (minScale ω x y : ℝ) (minScale ω y z : ℝ) := by exact_mod_cast hm
  by_cases hl : (minScale ω x y : ℝ) ≤ minScale ω y z
  · rw [max_eq_right hl] at hm'
    apply (min_le_right _ _).trans
    nlinarith
  · rw [max_eq_left (le_of_not_ge hl)] at hm'
    apply (min_le_left _ _).trans
    nlinarith


-- @@ L584-598 verbatim
/-- Euclidean norm can subsequently be used for `R`: only its elementary
    comparison with the two coordinate gaps is needed for the tail bound. -/
lemma error_upper_ae {x y : ℝ × ℝ} (hxy : x ≠ y) {R : ℝ} (hR : 0 < R)
    (hgap : R ≤ |x.1-y.1|+|x.2-y.2|) :
    ∀ᵐ ω ∂squareLaw, gridDepth ω x y + Real.log R ≤ Real.log 2 := by
  filter_upwards [share_eventually_exists x y] with ω he
  obtain ⟨n,hn⟩ := he
  have hs := minScale_mem hxy ⟨n,hn⟩
  have h₁ := shares_gap (by positivity : 0 < (2:ℝ)^(minScale ω x y)) hs.1
  have h₂ := shares_gap (by positivity : 0 < (2:ℝ)^(minScale ω x y)) hs.2
  have hr : R ≤ 2*(2:ℝ)^(minScale ω x y) := by linarith
  have hh := Real.log_le_log hR hr
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (by positivity), Real.log_zpow] at hh
  unfold gridDepth
  linarith


-- @@ L600-625 verbatim
lemma error_lower_tail {x y : ℝ × ℝ} (hxy : x ≠ y) {R : ℝ} (hR : 0 < R)
    (hgap : |x.1-y.1|+|x.2-y.2| ≤ 2*R) (u : ℝ) :
    squareLaw.real {ω | gridDepth ω x y + Real.log R < -u} ≤ 4*Real.exp (-u) := by
  obtain ⟨m,hm⟩ := exists_mem_Ico_zpow (mul_pos hR (Real.exp_pos u))
    (by norm_num : (1:ℝ)<2)
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hm₁ : (m:ℝ)*Real.log 2 ≤ Real.log R + u := by
    have hh := Real.log_le_log (by positivity : 0 < (2:ℝ)^m) hm.1
    rw [Real.log_zpow, Real.log_mul hR.ne' (Real.exp_ne_zero _), Real.log_exp] at hh
    exact hh
  have hsub : {ω | gridDepth ω x y + Real.log R < -u} ⊆
      {ω | ¬shareAt m ω x y} := by
    intro ω hω hs
    have hk : (minScale ω x y : ℝ) ≤ (m:ℝ) := by exact_mod_cast minScale_le hxy hs
    have := mul_le_mul_of_nonneg_right hk hl.le
    change gridDepth ω x y + Real.log R < -u at hω
    unfold gridDepth at hω
    linarith
  refine (measureReal_mono hsub).trans ((separation_probability_le m x y).trans ?_)
  have hpow : 0 < (2:ℝ)^m := by positivity
  have hm₂ : R*Real.exp u < 2*(2:ℝ)^m := by
    simpa only [zpow_add₀ (by norm_num : (2:ℝ)≠0), zpow_one, mul_comm] using hm.2
  apply (div_le_iff₀ hpow).mpr
  have hex : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  have hh := mul_le_mul_of_nonneg_right hm₂.le (Real.exp_nonneg (-u))
  nlinarith


-- @@ L627-648 verbatim
lemma error_abs_tail {x y : ℝ × ℝ} (hxy : x ≠ y) {R : ℝ} (hR : 0 < R)
    (hgap₁ : R ≤ |x.1-y.1|+|x.2-y.2|)
    (hgap₂ : |x.1-y.1|+|x.2-y.2| ≤ 2*R) {u : ℝ} (_hu : 0 ≤ u) :
    squareLaw.real {ω | u < |gridDepth ω x y + Real.log R|} ≤ 4*Real.exp (-u) := by
  by_cases hsmall : u ≤ Real.log 2
  · have hp : squareLaw.real {ω | u < |gridDepth ω x y + Real.log R|} ≤ 1 :=
      measureReal_le_one
    have hex : (1:ℝ)/2 ≤ Real.exp (-u) := by
      have := Real.exp_le_exp.mpr (neg_le_neg hsmall)
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ)<2)] at this
      simpa only [one_div] using this
    linarith
  · have hle : squareLaw.real {ω | u < |gridDepth ω x y + Real.log R|} ≤
        squareLaw.real {ω | gridDepth ω x y + Real.log R < -u} := by
      apply ENNReal.toReal_mono (measure_ne_top _ _)
      apply measure_mono_ae
      filter_upwards [error_upper_ae hxy hR hgap₁] with ω hω
      intro hh
      rcases lt_abs.mp hh with hh | hh
      · exact False.elim (hsmall (hh.le.trans hω))
      · linarith
    exact hle.trans (error_lower_tail hxy hR hgap₂ u)


-- @@ L650-673 verbatim
lemma error_abs_lintegral_le {x y : ℝ × ℝ} (hxy : x ≠ y) {R : ℝ} (hR : 0 < R)
    (hgap₁ : R ≤ |x.1-y.1|+|x.2-y.2|)
    (hgap₂ : |x.1-y.1|+|x.2-y.2| ≤ 2*R) :
    (∫⁻ ω, ENNReal.ofReal |gridDepth ω x y + Real.log R| ∂squareLaw) ≤ ENNReal.ofReal 4 := by
  rw [lintegral_eq_lintegral_meas_lt squareLaw
    (by filter_upwards with ω; exact abs_nonneg _)
    (((measurable_gridDepth hxy).add_const _).abs.aemeasurable)]
  have he : IntegrableOn (fun u : ℝ => 4 * Real.exp (-u)) (Set.Ioi 0) volume := by
    change Integrable (fun u : ℝ => 4 * Real.exp (-u)) (volume.restrict (Set.Ioi 0))
    simpa only [neg_one_mul] using (integrableOn_exp_mul_Ioi (by norm_num : (-1:ℝ)<0) 0).const_mul 4
  calc
    _ ≤ ∫⁻ u : ℝ in Set.Ioi 0, ENNReal.ofReal (4*Real.exp (-u)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      rw [← ENNReal.ofReal_toReal (measure_ne_top squareLaw _)]
      exact ENNReal.ofReal_le_ofReal (error_abs_tail hxy hR hgap₁ hgap₂ hu.le)
    _ = ENNReal.ofReal 4 := by
      rw [← ofReal_integral_eq_lintegral_ofReal he (by filter_upwards with u; positivity)]
      congr 1
      rw [integral_const_mul]
      have hi := integral_exp_mul_Ioi (by norm_num : (-1:ℝ)<0) (0:ℝ)
      simp only [neg_one_mul, mul_zero, Real.exp_zero, neg_div_neg_eq, div_one] at hi
      rw [hi]
      norm_num


-- @@ L675-685 verbatim
lemma error_integrable {x y : ℝ × ℝ} (hxy : x ≠ y) {R : ℝ} (hR : 0 < R)
    (hgap₁ : R ≤ |x.1-y.1|+|x.2-y.2|)
    (hgap₂ : |x.1-y.1|+|x.2-y.2| ≤ 2*R) :
    Integrable (fun ω => gridDepth ω x y + Real.log R) squareLaw := by
  have hm : AEStronglyMeasurable (fun ω => gridDepth ω x y + Real.log R) squareLaw :=
    ((measurable_gridDepth hxy).add_const (Real.log R)).aestronglyMeasurable
  apply (integrable_norm_iff hm).mp
  refine ⟨hm.norm, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (by filter_upwards with ω; exact norm_nonneg _)).mpr
  simpa only [Real.norm_eq_abs] using
    (error_abs_lintegral_le hxy hR hgap₁ hgap₂).trans_lt ENNReal.ofReal_lt_top


-- @@ L687-696 verbatim
lemma mean_abs_error_le {x y : ℝ × ℝ} (hxy : x ≠ y) {R : ℝ} (hR : 0 < R)
    (hgap₁ : R ≤ |x.1-y.1|+|x.2-y.2|)
    (hgap₂ : |x.1-y.1|+|x.2-y.2| ≤ 2*R) :
    (∫ ω, |gridDepth ω x y + Real.log R| ∂squareLaw) ≤ 4 := by
  have hi := (error_integrable hxy hR hgap₁ hgap₂).abs
  have hh := error_abs_lintegral_le hxy hR hgap₁ hgap₂
  rw [← ofReal_integral_eq_lintegral_ofReal hi (by filter_upwards with ω; exact abs_nonneg _)] at hh
  have hh' := ENNReal.toReal_mono (by simp : ENNReal.ofReal (4:ℝ) ≠ ⊤) hh
  simpa only [ENNReal.toReal_ofReal (integral_nonneg fun ω => abs_nonneg _),
    ENNReal.toReal_ofReal (by norm_num : (0:ℝ)≤4)] using hh'


-- @@ L698-710 verbatim
lemma minScale_cdf {x y : ℝ × ℝ} (hxy : x ≠ y) (m : ℤ) :
    squareLaw.real {ω | minScale ω x y ≤ m} =
      max 0 (1-|x.1-y.1|/((2:ℝ)^m)) * max 0 (1-|x.2-y.2|/((2:ℝ)^m)) := by
  have hn : ∀ᵐ ω ∂squareLaw, ∀ k : ℤ, shareAt k ω x y → shareAt (k+1) ω x y := by
    rw [ae_all_iff]
    exact fun k => shareAt_nested_ae k x y
  have he : {ω | minScale ω x y ≤ m} =ᵐ[squareLaw] {ω | shareAt m ω x y} := by
    filter_upwards [share_eventually_exists x y, hn] with ω he hn
    apply propext
    obtain ⟨n,hn'⟩ := he
    exact (shareAt_iff_minScale_le hxy ⟨n,hn'⟩ hn m).symm
  rw [measureReal_def, measure_congr he]
  exact sharing_probability m x y


-- @@ L712-722 verbatim
lemma minScale_law_same_gaps {x y x' y' : ℝ × ℝ} (hxy : x ≠ y) (hxy' : x' ≠ y')
    (h₁ : |x.1-y.1| = |x'.1-y'.1|) (h₂ : |x.2-y.2| = |x'.2-y'.2|) :
    Measure.map (fun ω => minScale ω x y) squareLaw =
      Measure.map (fun ω => minScale ω x' y') squareLaw := by
  apply Measure.ext_of_Iic
  intro m
  rw [Measure.map_apply (measurable_minScale hxy) measurableSet_Iic,
    Measure.map_apply (measurable_minScale hxy') measurableSet_Iic]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change squareLaw.real {ω | minScale ω x y ≤ m} = squareLaw.real {ω | minScale ω x' y' ≤ m}
  rw [minScale_cdf hxy, minScale_cdf hxy', h₁, h₂]


-- @@ L724-731 verbatim
lemma mean_depth_same_gaps {x y x' y' : ℝ × ℝ} (hxy : x ≠ y) (hxy' : x' ≠ y')
    (h₁ : |x.1-y.1| = |x'.1-y'.1|) (h₂ : |x.2-y.2| = |x'.2-y'.2|) :
    (∫ ω, gridDepth ω x y ∂squareLaw) = ∫ ω, gridDepth ω x' y' ∂squareLaw := by
  have hf : Measurable (fun n : ℤ => -(n:ℝ)*Real.log 2) := measurable_of_countable _
  unfold gridDepth
  rw [← integral_map (measurable_minScale hxy).aemeasurable hf.aestronglyMeasurable,
      ← integral_map (measurable_minScale hxy').aemeasurable hf.aestronglyMeasurable,
      minScale_law_same_gaps hxy hxy' h₁ h₂]


-- @@ L733-756 verbatim
lemma minScale_law_double {x y : ℝ × ℝ} (hxy : x ≠ y) :
    Measure.map (fun ω => minScale ω (2*x.1,2*x.2) (2*y.1,2*y.2)) squareLaw =
      Measure.map (fun ω => minScale ω x y + 1) squareLaw := by
  have hd : (2*x.1,2*x.2) ≠ (2*y.1,2*y.2) := by
    intro h
    apply hxy
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    apply Prod.ext <;> dsimp at h₁ h₂ ⊢ <;> linarith
  apply Measure.ext_of_Iic
  intro m
  rw [Measure.map_apply (measurable_minScale hd) measurableSet_Iic,
    Measure.map_apply ((measurable_minScale hxy).add_const 1) measurableSet_Iic]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change squareLaw.real {ω | minScale ω (2*x.1,2*x.2) (2*y.1,2*y.2) ≤ m} =
    squareLaw.real {ω | minScale ω x y + 1 ≤ m}
  rw [show {ω | minScale ω x y + 1 ≤ m} = {ω | minScale ω x y ≤ m-1} by ext ω; simp only [Set.mem_ofPred_eq]; omega,
    minScale_cdf hd, minScale_cdf hxy]
  have hpow : (2:ℝ)^(m-1) = (2:ℝ)^m / 2 := by rw [zpow_sub₀ (by norm_num), zpow_one]
  have hq (a b : ℝ) : |2*a-2*b| / (2:ℝ)^m = |a-b| / ((2:ℝ)^m/2) := by
    rw [← mul_sub, abs_mul]
    norm_num
    ring
  rw [hpow, hq x.1 y.1, hq x.2 y.2]


-- @@ L758-769 verbatim
lemma gridDepth_integrable {x y : ℝ × ℝ} (hxy : x ≠ y) :
    Integrable (fun ω => gridDepth ω x y) squareLaw := by
  let R := |x.1-y.1|+|x.2-y.2|
  have hR : 0 < R := by
    by_cases h₁ : x.1 = y.1
    · have h₂ : x.2 ≠ y.2 := fun h₂ => hxy (Prod.ext h₁ h₂)
      exact add_pos_of_nonneg_of_pos (abs_nonneg _) (abs_pos.mpr (sub_ne_zero.mpr h₂))
    · exact add_pos_of_pos_of_nonneg (abs_pos.mpr (sub_ne_zero.mpr h₁)) (abs_nonneg _)
  have hi := error_integrable hxy hR (le_refl R) (by linarith : R ≤ 2*R)
  have hh := hi.sub (integrable_const (Real.log R))
  change Integrable (fun ω => (gridDepth ω x y + Real.log R) - Real.log R) squareLaw at hh
  simpa only [add_sub_cancel_right] using hh


-- @@ L771-794 verbatim
lemma mean_depth_double {x y : ℝ × ℝ} (hxy : x ≠ y) :
    (∫ ω, gridDepth ω (2*x.1,2*x.2) (2*y.1,2*y.2) ∂squareLaw) =
      (∫ ω, gridDepth ω x y ∂squareLaw) - Real.log 2 := by
  have hd : (2*x.1,2*x.2) ≠ (2*y.1,2*y.2) := by
    intro h
    apply hxy
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    apply Prod.ext <;> dsimp at h₁ h₂ ⊢ <;> linarith
  have hid : ProbabilityTheory.IdentDistrib
      (fun ω => minScale ω (2*x.1,2*x.2) (2*y.1,2*y.2))
      (fun ω => minScale ω x y + 1) squareLaw squareLaw :=
    ⟨(measurable_minScale hd).aemeasurable,
      ((measurable_minScale hxy).add_const 1).aemeasurable, minScale_law_double hxy⟩
  have hh := (hid.comp (measurable_of_countable (fun n : ℤ => -(n:ℝ)*Real.log 2))).integral_eq
  change (∫ ω, gridDepth ω (2*x.1,2*x.2) (2*y.1,2*y.2) ∂squareLaw) = _ at hh
  rw [hh]
  calc
    _ = ∫ ω, gridDepth ω x y - Real.log 2 ∂squareLaw := by
      apply integral_congr_ae
      filter_upwards with ω
      simp [gridDepth]
      ring
    _ = _ := by rw [integral_sub (gridDepth_integrable hxy) (integrable_const _)]; simp


-- @@ L796-808 verbatim
/-- Parameter measurability, needed before integrating orientation and phase. -/
lemma measurableSet_shareAt_param {T : Type u1} [MeasurableSpace T]
    {W : T → GridSample} {X Y : T → ℝ × ℝ}
    (hW : Measurable W) (hX : Measurable X) (hY : Measurable Y) (m : ℤ) :
    MeasurableSet {t | shareAt m (W t) (X t) (Y t)} := by
  unfold shareAt bin shiftZ
  apply MeasurableSet.inter
  · exact measurableSet_eq_fun
      ((hX.fst.sub ((measurable_shift _).comp hW.fst)).div_const _).floor
      ((hY.fst.sub ((measurable_shift _).comp hW.fst)).div_const _).floor
  · exact measurableSet_eq_fun
      ((hX.snd.sub ((measurable_shift _).comp hW.snd)).div_const _).floor
      ((hY.snd.sub ((measurable_shift _).comp hW.snd)).div_const _).floor


-- @@ L810-830 verbatim
lemma measurable_minScale_param {T : Type u2} [MeasurableSpace T]
    {W : T → GridSample} {X Y : T → ℝ × ℝ}
    (hW : Measurable W) (hX : Measurable X) (hY : Measurable Y) (hne : ∀ t, X t ≠ Y t) :
    Measurable (fun t => minScale (W t) (X t) (Y t)) := by
  apply measurable_to_countable'
  intro m
  change MeasurableSet {t | minScale (W t) (X t) (Y t) = m}
  have he : {t | minScale (W t) (X t) (Y t) = m} =
      ({t | shareAt m (W t) (X t) (Y t)} ∩
        ⋂ k : ℤ, ⋂ (_ : k < m), {t | shareAt k (W t) (X t) (Y t)}ᶜ) ∪
      ({t | m = 0} ∩ (⋃ k : ℤ, {t | shareAt k (W t) (X t) (Y t)})ᶜ) := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_compl_iff, Set.mem_iUnion]
    exact minScale_eq_iff (hne t) m
  rw [he]
  exact ((measurableSet_shareAt_param hW hX hY m).inter
    (MeasurableSet.iInter fun k => MeasurableSet.iInter fun (_ : k < m) =>
      (measurableSet_shareAt_param hW hX hY k).compl)).union
    ((MeasurableSet.const (m = 0)).inter (MeasurableSet.iUnion fun k =>
      measurableSet_shareAt_param hW hX hY k).compl)


-- @@ L832-837 verbatim
lemma measurable_gridDepth_param {T : Type u3} [MeasurableSpace T]
    {W : T → GridSample} {X Y : T → ℝ × ℝ}
    (hW : Measurable W) (hX : Measurable X) (hY : Measurable Y) (hne : ∀ t, X t ≠ Y t) :
    Measurable (fun t => gridDepth (W t) (X t) (Y t)) := by
  exact (((measurable_of_countable (fun n : ℤ => (n:ℝ))).comp
    (measurable_minScale_param hW hX hY hne)).neg).mul_const _


-- @@ L839-839 verbatim
def polarPair (t θ : ℝ) : ℝ × ℝ := (Real.exp t * Real.cos θ, Real.exp t * Real.sin θ)


-- @@ L841-842 verbatim
def polarMean (t θ : ℝ) : ℝ :=
  (∫ ω, gridDepth ω (0,0) (polarPair t θ) ∂squareLaw) + t


-- @@ L844-851 verbatim
lemma zero_ne_polarPair (t θ : ℝ) : (0,0) ≠ polarPair t θ := by
  intro h
  have he : Real.exp t ≠ 0 := Real.exp_ne_zero t
  have h₁ : Real.cos θ = 0 := (mul_eq_zero.mp (congrArg Prod.fst h).symm).resolve_left he
  have h₂ : Real.sin θ = 0 := (mul_eq_zero.mp (congrArg Prod.snd h).symm).resolve_left he
  have hh := Real.sin_sq_add_cos_sq θ
  rw [h₁,h₂] at hh
  norm_num at hh


-- @@ L853-867 verbatim
lemma polarPair_gaps (t θ : ℝ) :
    Real.exp t ≤ |(polarPair t θ).1|+|(polarPair t θ).2| ∧
    |(polarPair t θ).1|+|(polarPair t θ).2| ≤ 2*Real.exp t := by
  have hsum : 1 ≤ |Real.cos θ|+|Real.sin θ| := by
    have hsq := Real.sin_sq_add_cos_sq θ
    have hpos := mul_nonneg (abs_nonneg (Real.cos θ)) (abs_nonneg (Real.sin θ))
    have hc := abs_nonneg (Real.cos θ)
    have hs := abs_nonneg (Real.sin θ)
    nlinarith [sq_abs (Real.cos θ), sq_abs (Real.sin θ)]
  have hsum' : |Real.cos θ|+|Real.sin θ| ≤ 2 := by
    linarith [Real.abs_cos_le_one θ, Real.abs_sin_le_one θ]
  simp only [polarPair, abs_mul, abs_of_pos (Real.exp_pos t)]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hsum (Real.exp_nonneg t)]
  · nlinarith [mul_le_mul_of_nonneg_left hsum' (Real.exp_nonneg t)]


-- @@ L869-872 verbatim
lemma polarMean_integral (t θ : ℝ) :
    polarMean t θ = ∫ ω, gridDepth ω (0,0) (polarPair t θ) + t ∂squareLaw := by
  rw [integral_add (gridDepth_integrable (zero_ne_polarPair t θ)) (integrable_const _)]
  simp [polarMean]


-- @@ L874-885 verbatim
lemma polarMean_bound (t θ : ℝ) : |polarMean t θ| ≤ 4 := by
  rw [polarMean_integral]
  have hg := polarPair_gaps t θ
  have hh := mean_abs_error_le (zero_ne_polarPair t θ) (Real.exp_pos t)
    (by simpa only [zero_sub, abs_neg] using hg.1)
    (by simpa only [zero_sub, abs_neg] using hg.2)
  rw [Real.log_exp] at hh
  have hb : |∫ ω, gridDepth ω (0,0) (polarPair t θ) + t ∂squareLaw| ≤
      ∫ ω, |gridDepth ω (0,0) (polarPair t θ) + t| ∂squareLaw := by
    simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm
      (f := fun ω => gridDepth ω (0,0) (polarPair t θ) + t) (μ := squareLaw))
  exact hb.trans hh


-- @@ L887-889 verbatim
lemma measurable_polarPair : Measurable (fun p : ℝ × ℝ => polarPair p.1 p.2) := by
  exact (measurable_fst.exp.mul measurable_snd.cos).prodMk
    (measurable_fst.exp.mul measurable_snd.sin)


-- @@ L891-899 verbatim
lemma measurable_polarMean : Measurable (fun p : ℝ × ℝ => polarMean p.1 p.2) := by
  have hm : Measurable (fun p : (ℝ × ℝ) × GridSample =>
      gridDepth p.2 (0,0) (polarPair p.1.1 p.1.2)) :=
    measurable_gridDepth_param measurable_snd measurable_const
      (measurable_polarPair.comp measurable_fst) (fun p => zero_ne_polarPair _ _)
  have hi : StronglyMeasurable (fun p : ℝ × ℝ => ∫ ω,
      gridDepth ω (0,0) (polarPair p.1 p.2) ∂squareLaw) :=
    hm.stronglyMeasurable.integral_prod_right
  exact hi.measurable.add measurable_fst


-- @@ L901-904 verbatim
lemma polarPair_double (t θ : ℝ) : polarPair (t+Real.log 2) θ =
    (2*(polarPair t θ).1,2*(polarPair t θ).2) := by
  simp only [polarPair,Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2)]
  congr 1 <;> ring


-- @@ L906-911 verbatim
lemma polarMean_period_phase (θ : ℝ) : Function.Periodic (fun t => polarMean t θ) (Real.log 2) := by
  intro t
  have hm := mean_depth_double (zero_ne_polarPair t θ)
  simp only [mul_zero] at hm
  simp only [polarMean,polarPair_double,hm]
  ring


-- @@ L913-915 verbatim
lemma polarMean_period_angle (t : ℝ) : Function.Periodic (polarMean t) (2*Real.pi) := by
  intro θ
  simp only [polarMean,polarPair,Real.cos_periodic θ,Real.sin_periodic θ]


-- @@ L917-920 verbatim
lemma uniformInterval_integral {l : ℝ} (hl : 0 < l) (f : ℝ → ℝ) :
    (∫ x, f x ∂uniformInterval l) = l⁻¹ * ∫ x in (0:ℝ)..l, f x := by
  rw [uniformInterval, integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hl.le, smul_eq_mul, intervalIntegral.integral_of_le hl.le]


-- @@ L922-928 verbatim
lemma uniformInterval_period_shift {l : ℝ} (hl : 0 < l) {f : ℝ → ℝ}
    (hf : Function.Periodic f l) (a : ℝ) :
    (∫ x, f (x+a) ∂uniformInterval l) = ∫ x, f x ∂uniformInterval l := by
  rw [uniformInterval_integral hl, uniformInterval_integral hl,
    intervalIntegral.integral_comp_add_right]
  congr 1
  simpa only [zero_add, add_comm l a] using hf.intervalIntegral_add_eq a 0


-- @@ L930-937 verbatim
lemma uniformInterval_period_sub {l : ℝ} (hl : 0 < l) {f : ℝ → ℝ}
    (hf : Function.Periodic f l) (a : ℝ) :
    (∫ x, f (a-x) ∂uniformInterval l) = ∫ x, f (-x) ∂uniformInterval l := by
  have hp : Function.Periodic (fun x => f (-x)) l := by
    intro x
    simpa only [neg_add, sub_eq_add_neg] using hf.sub_eq (-x)
  have hh := uniformInterval_period_shift hl hp (-a)
  simpa only [neg_add, neg_neg, sub_eq_add_neg, add_comm] using hh


-- @@ L939-941 verbatim
/-- The universal archimedean error mean, before any configuration is chosen. -/
def kappa : ℝ := ∫ ξ, ∫ θ, polarMean (-ξ) θ
  ∂uniformInterval (2*Real.pi) ∂uniformInterval (Real.log 2)


-- @@ L943-954 verbatim
lemma polar_average_constant (t φ : ℝ) :
    (∫ ξ, ∫ θ, polarMean (t-ξ) (θ+φ)
      ∂uniformInterval (2*Real.pi) ∂uniformInterval (Real.log 2)) = kappa := by
  simp_rw [uniformInterval_period_shift (by positivity : 0 < 2*Real.pi)
    (polarMean_period_angle _) φ]
  have hp : Function.Periodic
      (fun t => ∫ θ, polarMean t θ ∂uniformInterval (2*Real.pi)) (Real.log 2) := by
    intro x
    apply integral_congr_ae
    filter_upwards with θ
    exact polarMean_period_phase θ x
  exact uniformInterval_period_sub (Real.log_pos (by norm_num)) hp t


-- @@ L956-957 verbatim
def rotateC (ξ θ : ℝ) (z : ℂ) : ℂ :=
  (Real.exp (-ξ) : ℂ) * Complex.exp ((θ : ℂ)*Complex.I) * z


-- @@ L959-960 verbatim
def rotatePair (ξ θ : ℝ) (z : ℂ) : ℝ × ℝ :=
  ((rotateC ξ θ z).re, (rotateC ξ θ z).im)


-- @@ L962-964 verbatim
lemma rotateC_sub (ξ θ : ℝ) (z w : ℂ) :
    rotateC ξ θ (z-w) = rotateC ξ θ z - rotateC ξ θ w := by
  exact mul_sub _ _ _


-- @@ L966-969 verbatim
lemma norm_rotateC (ξ θ : ℝ) (z : ℂ) :
    ‖rotateC ξ θ z‖ = Real.exp (-ξ) * ‖z‖ := by
  simp only [rotateC, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Complex.norm_exp_ofReal_mul_I, mul_one]


-- @@ L971-979 verbatim
lemma rotatePair_ne (ξ θ : ℝ) {z w : ℂ} (hne : z ≠ w) :
    rotatePair ξ θ z ≠ rotatePair ξ θ w := by
  intro he
  have h : rotateC ξ θ z = rotateC ξ θ w := Complex.ext
    (congrArg Prod.fst he) (congrArg Prod.snd he)
  have hn := norm_rotateC ξ θ (z-w)
  rw [rotateC_sub, h, sub_self, norm_zero] at hn
  have hz : ‖z-w‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
  exact (mul_ne_zero (Real.exp_ne_zero _) hz) hn.symm


-- @@ L981-992 verbatim
lemma rotatePair_gaps (ξ θ : ℝ) (z w : ℂ) :
    Real.exp (-ξ)*‖z-w‖ ≤
      |(rotatePair ξ θ z).1-(rotatePair ξ θ w).1| +
      |(rotatePair ξ θ z).2-(rotatePair ξ θ w).2| ∧
    |(rotatePair ξ θ z).1-(rotatePair ξ θ w).1| +
      |(rotatePair ξ θ z).2-(rotatePair ξ θ w).2| ≤ 2*(Real.exp (-ξ)*‖z-w‖) := by
  have hh := Complex.norm_le_abs_re_add_abs_im (rotateC ξ θ (z-w))
  have hr := Complex.abs_re_le_norm (rotateC ξ θ (z-w))
  have hi := Complex.abs_im_le_norm (rotateC ξ θ (z-w))
  rw [norm_rotateC, rotateC_sub] at hh hr hi
  simp only [Complex.sub_re, Complex.sub_im] at hh hr hi
  exact ⟨hh, by dsimp only [rotatePair]; linarith⟩


-- @@ L994-1005 verbatim
lemma rotateC_polar (ξ θ : ℝ) {z : ℂ} (hz : z ≠ 0) :
    rotateC ξ θ z = (Real.exp (Real.log ‖z‖-ξ) : ℂ) *
      Complex.exp (((θ+z.arg : ℝ) : ℂ)*Complex.I) := by
  rw [Complex.ofReal_add, add_mul, Complex.exp_add,
    Real.exp_sub, Real.exp_log (norm_pos_iff.mpr hz),
    div_eq_mul_inv, ← Real.exp_neg, Complex.ofReal_mul]
  calc
    _ = (Real.exp (-ξ) : ℂ) * Complex.exp ((θ:ℂ)*Complex.I) *
        ((‖z‖:ℂ) * Complex.exp ((z.arg:ℂ)*Complex.I)) := by
      rw [Complex.norm_mul_exp_arg_mul_I]
      rfl
    _ = _ := by ring


-- @@ L1007-1010 verbatim
lemma exp_polarPair (t θ : ℝ) :
    ((Real.exp t : ℂ) * Complex.exp ((θ:ℂ)*Complex.I)).re = (polarPair t θ).1 ∧
    ((Real.exp t : ℂ) * Complex.exp ((θ:ℂ)*Complex.I)).im = (polarPair t θ).2 := by
  simp [polarPair, Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im]


-- @@ L1012-1022 verbatim
lemma rotated_mean (ξ θ : ℝ) {z w : ℂ} (hne : z ≠ w) :
    (∫ ω, gridDepth ω (rotatePair ξ θ z) (rotatePair ξ θ w) ∂squareLaw)
      - ξ + Real.log ‖z-w‖ = polarMean (Real.log ‖z-w‖-ξ) (θ+(z-w).arg) := by
  have hp := exp_polarPair (Real.log ‖z-w‖-ξ) (θ+(z-w).arg)
  rw [← rotateC_polar ξ θ (sub_ne_zero.mpr hne), rotateC_sub] at hp
  have hm := mean_depth_same_gaps (rotatePair_ne ξ θ hne)
    (zero_ne_polarPair (Real.log ‖z-w‖-ξ) (θ+(z-w).arg))
    (by dsimp only [rotatePair]; simp only [zero_sub, abs_neg, ← hp.1]; rfl)
    (by dsimp only [rotatePair]; simp only [zero_sub, abs_neg, ← hp.2]; rfl)
  rw [hm, polarMean]
  ring


-- @@ L1024-1024 verbatim
abbrev FullSample := (ℝ × ℝ) × GridSample


-- @@ L1026-1027 verbatim
def phaseLaw : Measure (ℝ × ℝ) :=
  (uniformInterval (Real.log 2)).prod (uniformInterval (2*Real.pi))


-- @@ L1029-1029 verbatim
def fullLaw : Measure FullSample := phaseLaw.prod squareLaw


-- @@ L1031-1034 verbatim
instance phaseLaw_probability : IsProbabilityMeasure phaseLaw := by
  let := uniformInterval_probability (Real.log_pos (by norm_num : (1:ℝ) < 2))
  let := uniformInterval_probability (by positivity : 0 < 2*Real.pi)
  exact Measure.prod.instIsProbabilityMeasure _ _


-- @@ L1036-1037 verbatim
instance fullLaw_probability : IsProbabilityMeasure fullLaw := by
  exact Measure.prod.instIsProbabilityMeasure _ _


-- @@ L1039-1041 verbatim
/-- Actual jointly defined hierarchy depth in the original complex plane. -/
def depth (ω : FullSample) (z w : ℂ) : ℝ :=
  gridDepth ω.2 (rotatePair ω.1.1 ω.1.2 z) (rotatePair ω.1.1 ω.1.2 w) - ω.1.1


-- @@ L1043-1043 verbatim
def error (ω : FullSample) (z w : ℂ) : ℝ := depth ω z w + Real.log ‖z-w‖


-- @@ L1045-1047 verbatim
lemma measurable_rotatePair (z : ℂ) : Measurable (fun p : ℝ × ℝ => rotatePair p.1 p.2 z) := by
  unfold rotatePair rotateC
  fun_prop


-- @@ L1049-1054 verbatim
lemma measurable_depth {z w : ℂ} (hne : z ≠ w) : Measurable (fun ω => depth ω z w) := by
  unfold depth
  exact (measurable_gridDepth_param measurable_snd
    ((measurable_rotatePair z).comp measurable_fst)
    ((measurable_rotatePair w).comp measurable_fst)
    (fun p => rotatePair_ne _ _ hne)).sub measurable_fst.fst


-- @@ L1056-1057 verbatim
lemma measurable_error {z w : ℂ} (hne : z ≠ w) : Measurable (fun ω => error ω z w) :=
  (measurable_depth hne).add_const _


-- @@ L1059-1064 verbatim
lemma error_fixed_phase {z w : ℂ} (hne : z ≠ w) (p : ℝ × ℝ) (ω : GridSample) :
    error (p,ω) z w = gridDepth ω (rotatePair p.1 p.2 z) (rotatePair p.1 p.2 w) +
      Real.log (Real.exp (-p.1)*‖z-w‖) := by
  rw [Real.log_mul (Real.exp_ne_zero _) (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)), Real.log_exp]
  simp only [error, depth]
  ring


-- @@ L1066-1071 verbatim
lemma error_integrable_fixed {z w : ℂ} (hne : z ≠ w) (p : ℝ × ℝ) :
    Integrable (fun ω => error (p,ω) z w) squareLaw := by
  simp_rw [error_fixed_phase hne p]
  exact error_integrable (rotatePair_ne _ _ hne)
    (mul_pos (Real.exp_pos _) (norm_pos_iff.mpr (sub_ne_zero.mpr hne)))
    (rotatePair_gaps _ _ _ _).1 (rotatePair_gaps _ _ _ _).2


-- @@ L1073-1078 verbatim
lemma mean_abs_error_fixed {z w : ℂ} (hne : z ≠ w) (p : ℝ × ℝ) :
    (∫ ω, |error (p,ω) z w| ∂squareLaw) ≤ 4 := by
  simp_rw [error_fixed_phase hne p]
  exact mean_abs_error_le (rotatePair_ne _ _ hne)
    (mul_pos (Real.exp_pos _) (norm_pos_iff.mpr (sub_ne_zero.mpr hne)))
    (rotatePair_gaps _ _ _ _).1 (rotatePair_gaps _ _ _ _).2


-- @@ L1080-1088 verbatim
lemma error_integrable_full {z w : ℂ} (hne : z ≠ w) :
    Integrable (fun ω => error ω z w) fullLaw := by
  apply (integrable_prod_iff (measurable_error hne).aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (error_integrable_fixed hne)
  · apply Integrable.of_bound ((measurable_error hne).norm.stronglyMeasurable.integral_prod_right.aestronglyMeasurable) 4
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    simpa only [Real.norm_eq_abs] using mean_abs_error_fixed hne p


-- @@ L1090-1100 verbatim
lemma mean_error_fixed {z w : ℂ} (hne : z ≠ w) (p : ℝ × ℝ) :
    (∫ ω, error (p,ω) z w ∂squareLaw) =
      polarMean (Real.log ‖z-w‖-p.1) (p.2+(z-w).arg) := by
  have hi : Integrable (fun ω => gridDepth ω (rotatePair p.1 p.2 z) (rotatePair p.1 p.2 w)) squareLaw :=
    gridDepth_integrable (rotatePair_ne _ _ hne)
  have his : Integrable (fun ω => gridDepth ω (rotatePair p.1 p.2 z) (rotatePair p.1 p.2 w) - p.1) squareLaw :=
    hi.sub (integrable_const p.1)
  simp only [error, depth]
  rw [integral_add his (integrable_const (Real.log ‖z-w‖)), integral_sub hi (integrable_const p.1)]
  simp only [integral_const, probReal_univ, one_smul]
  exact rotated_mean _ _ hne


-- @@ L1102-1109 verbatim
lemma measurable_shifted_polarMean (t φ : ℝ) :
    Measurable (fun p : ℝ × ℝ => polarMean (t-p.1) (p.2+φ)) := by
  have h₁ : Measurable (fun p : ℝ × ℝ => t-p.1) := measurable_const.sub measurable_fst
  have h₂ : Measurable (fun p : ℝ × ℝ => p.2+φ) := measurable_snd.add_const φ
  change Measurable ((fun p : ℝ × ℝ => polarMean p.1 p.2) ∘
    (fun p : ℝ × ℝ => (t-p.1,p.2+φ)))
  apply Measurable.comp measurable_polarMean
  exact h₁.prodMk h₂


-- @@ L1111-1119 verbatim
lemma mean_error_full {z w : ℂ} (hne : z ≠ w) :
    (∫ ω, error ω z w ∂fullLaw) = kappa := by
  rw [fullLaw, integral_prod _ (error_integrable_full hne)]
  simp_rw [mean_error_fixed hne]
  have hm := measurable_shifted_polarMean (Real.log ‖z-w‖) (z-w).arg
  have hi := Integrable.of_bound (μ := phaseLaw) hm.aestronglyMeasurable 4
    (Filter.Eventually.of_forall (fun p => by simpa only [Real.norm_eq_abs] using polarMean_bound _ _))
  rw [phaseLaw, integral_prod _ hi]
  exact polar_average_constant _ _


-- @@ L1121-1142 verbatim
lemma abs_error_tail_full {z w : ℂ} (hne : z ≠ w) {u : ℝ} (hu : 0 ≤ u) :
    fullLaw.real {ω | u < |error ω z w|} ≤ 4*Real.exp (-u) := by
  have hs : MeasurableSet {ω : FullSample | u < |error ω z w|} :=
    measurableSet_lt measurable_const (measurable_error hne).abs
  have hb : fullLaw {ω | u < |error ω z w|} ≤ ENNReal.ofReal (4*Real.exp (-u)) := by
    rw [fullLaw, Measure.prod_apply hs]
    calc
      _ ≤ ∫⁻ _p, ENNReal.ofReal (4*Real.exp (-u)) ∂phaseLaw := by
        apply lintegral_mono
        intro p
        have he : squareLaw.real {ω | u < |error (p,ω) z w|} ≤ 4*Real.exp (-u) := by
          simp_rw [error_fixed_phase hne p]
          exact error_abs_tail (rotatePair_ne _ _ hne)
            (mul_pos (Real.exp_pos _) (norm_pos_iff.mpr (sub_ne_zero.mpr hne)))
            (rotatePair_gaps _ _ _ _).1 (rotatePair_gaps _ _ _ _).2 hu
        have hh := ENNReal.ofReal_le_ofReal he
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] at hh
        exact hh
      _ = _ := by simp
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [measureReal_def]
  simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 4*Real.exp (-u))] using hh


-- @@ L1144-1151 verbatim
lemma mean_abs_error_full {z w : ℂ} (hne : z ≠ w) :
    (∫ ω, |error ω z w| ∂fullLaw) ≤ 4 := by
  rw [fullLaw, integral_prod _ (error_integrable_full hne).abs]
  calc
    _ ≤ ∫ _p, (4:ℝ) ∂phaseLaw := integral_mono
      (error_integrable_full hne).abs.integral_prod_left (integrable_const _)
      (mean_abs_error_fixed hne)
    _ = _ := by simp


-- @@ L1153-1155 verbatim
lemma depth_symm (ω : FullSample) (z w : ℂ) : depth ω z w = depth ω w z := by
  simp only [depth,gridDepth,minScale_symm ω.2 (rotatePair ω.1.1 ω.1.2 z)
    (rotatePair ω.1.1 ω.1.2 w)]


-- @@ L1157-1165 verbatim
lemma depth_ultra_ae {x y z : ℂ} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    ∀ᵐ ω ∂fullLaw, min (depth ω x y) (depth ω y z) ≤ depth ω x z := by
  have hs : MeasurableSet {ω : FullSample | min (depth ω x y) (depth ω y z) ≤ depth ω x z} :=
    measurableSet_le ((measurable_depth hxy).min (measurable_depth hyz)) (measurable_depth hxz)
  apply (Measure.ae_prod_iff_ae_ae hs).mpr
  filter_upwards with p
  filter_upwards [gridDepth_ultra_ae (rotatePair_ne p.1 p.2 hxy)
    (rotatePair_ne p.1 p.2 hyz) (rotatePair_ne p.1 p.2 hxz)] with ω hh
  simpa only [depth,min_sub_sub_right,sub_le_sub_iff_right] using hh


-- @@ L1167-1167 verbatim
end WeakPinned.Grid


-- @@ L1169-1169 verbatim
end

-- @@ L1170-1170 verbatim
end

-- @@ L1171-1171 verbatim
end

-- @@ L1172-1172 verbatim
end


-- @@ L1174-1174 verbatim
end OAI
