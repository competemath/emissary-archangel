module

public import Mathlib.Algebra.Group.Translate
public import Mathlib.Algebra.Star.Conjneg
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs

import AddCombi.Mathlib.Algebra.Notation.Indicator
import APAP.Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Tactic.DepRewrite


-- @@ L13-15 verbatim
/-!
# Normalised Lp norms
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
open Finset hiding card

-- @@ L20-20 verbatim
open Function ProbabilityTheory Real

-- @@ L21-21 verbatim
open Fintype (card)

-- @@ L22-22 verbatim
open scoped BigOperators ComplexConjugate ENNReal NNReal Indicator translate


-- @@ L24-24 verbatim
local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s


-- @@ L26-26 verbatim
variable {α 𝕜 R E : Type*} [MeasurableSpace α]


-- @@ L28-28 verbatim
/-! ### Lp norm -/


-- @@ L30-30 verbatim
namespace MeasureTheory

-- @@ L31-31 verbatim
section NormedAddCommGroup

-- @@ L32-32 verbatim
variable [NormedAddCommGroup E] {p q : ℝ≥0∞} {f g h : α → E}


-- @@ L34-35 verbatim
/-- The Lp norm of a function with the compact normalisation. -/
noncomputable def cLpNorm (p : ℝ≥0∞) (f : α → E) : ℝ := lpNorm f p (uniformOn .univ)


-- @@ L37-37 verbatim
notation "‖" f "‖ₙ_[" p "]" => cLpNorm p f


-- @@ L39-39 expanded
@[simp]
lemma cLpNorm_nonneg : 0 ≤ cLpNorm p f := by simp [cLpNorm]


-- @@ L41-41 expanded
@[simp]
lemma cLpNorm_exponent_zero (f : α → E) : cLpNorm 0 f = 0 := by simp [cLpNorm]


-- @@ L43-43 expanded
@[simp]
lemma cLpNorm_zero (p : ℝ≥0∞) : cLpNorm p (0 : α → E) = 0 := by simp [cLpNorm]


-- @@ L44-44 expanded
@[simp]
lemma cLpNorm_zero' (p : ℝ≥0∞) : cLpNorm p (fun _ ↦ 0 : α → E) = 0 := by simp [cLpNorm]


-- @@ L46-47 expanded
@[simp]
lemma cLpNorm_of_isEmpty [IsEmpty α] (f : α → E) (p : ℝ≥0∞) : cLpNorm p f = 0 := by simp [cLpNorm]


-- @@ L49-49 expanded
@[simp]
lemma cLpNorm_neg (f : α → E) (p : ℝ≥0∞) : cLpNorm p (-f) = cLpNorm p f := by simp [cLpNorm]


-- @@ L50-51 expanded
@[simp]
lemma cLpNorm_neg' (f : α → E) (p : ℝ≥0∞) : (cLpNorm p fun x ↦ -f x) = cLpNorm p f := by
  simp [cLpNorm]


-- @@ L53-54 expanded
lemma cLpNorm_sub_comm (f g : α → E) (p : ℝ≥0∞) : cLpNorm p (f - g) = cLpNorm p (g - f) := by
  simp [cLpNorm, lpNorm_sub_comm]


-- @@ L56-58 expanded
@[simp]
lemma cLpNorm_norm (hf : StronglyMeasurable f) (p : ℝ≥0∞) :
    (cLpNorm p fun i ↦ ‖f i‖) = cLpNorm p f :=
  lpNorm_norm hf.aestronglyMeasurable _


-- @@ L60-62 expanded
@[simp]
lemma cLpNorm_abs {f : α → ℝ} (hf : StronglyMeasurable f) (p : ℝ≥0∞) :
    cLpNorm p |f| = cLpNorm p f :=
  lpNorm_abs hf.aestronglyMeasurable _


-- @@ L64-67 expanded
@[simp]
lemma cLpNorm_fun_abs {f : α → ℝ} (hf : StronglyMeasurable f) (p : ℝ≥0∞) :
    (cLpNorm p fun i ↦ |f i|) = cLpNorm p f :=
  lpNorm_fun_abs hf.aestronglyMeasurable _


-- @@ L69-69 verbatim
section NormedField

-- @@ L70-70 verbatim
variable [NormedField 𝕜] {p : ℝ≥0∞} {f g : α → 𝕜}


-- @@ L72-73 expanded
lemma cLpNorm_const_smul [Module 𝕜 E] [NormSMulClass 𝕜 E] (c : 𝕜) (f : α → E) :
    cLpNorm p (c • f) = ‖c‖ * cLpNorm p f := by simp [cLpNorm, lpNorm_const_smul]


-- @@ L75-76 expanded
lemma cLpNorm_nsmul [NormedSpace ℝ E] (n : ℕ) (f : α → E) (p : ℝ≥0∞) :
    cLpNorm p (n • f) = n • cLpNorm p f := by simp [cLpNorm, lpNorm_nsmul]


-- @@ L78-78 verbatim
variable [NormedSpace ℝ 𝕜]


-- @@ L80-81 expanded
lemma cLpNorm_natCast_mul (n : ℕ) (f : α → 𝕜) (p : ℝ≥0∞) :
    cLpNorm p ((n : α → 𝕜) * f) = n * cLpNorm p f :=
  lpNorm_natCast_mul ..


-- @@ L83-84 expanded
lemma cLpNorm_fun_natCast_mul (n : ℕ) (f : α → 𝕜) (p : ℝ≥0∞) :
    cLpNorm p (n * f ·) = n * cLpNorm p f :=
  lpNorm_fun_natCast_mul ..


-- @@ L86-87 expanded
lemma cLpNorm_mul_natCast (f : α → 𝕜) (n : ℕ) (p : ℝ≥0∞) :
    cLpNorm p (f * (n : α → 𝕜)) = cLpNorm p f * n :=
  lpNorm_mul_natCast ..


-- @@ L89-90 expanded
lemma cLpNorm_fun_mul_natCast (f : α → 𝕜) (n : ℕ) (p : ℝ≥0∞) :
    cLpNorm p (f · * n) = cLpNorm p f * n :=
  lpNorm_fun_mul_natCast ..


-- @@ L92-93 expanded
lemma cLpNorm_div_natCast [CharZero 𝕜] {n : ℕ} (hn : n ≠ 0) (f : α → 𝕜) (p : ℝ≥0∞) :
    cLpNorm p (f / (n : α → 𝕜)) = cLpNorm p f / n :=
  lpNorm_div_natCast hn ..


-- @@ L95-96 expanded
lemma cLpNorm_fun_div_natCast [CharZero 𝕜] {n : ℕ} (hn : n ≠ 0) (f : α → 𝕜) (p : ℝ≥0∞) :
    cLpNorm p (f · / n) = cLpNorm p f / n :=
  lpNorm_fun_div_natCast hn ..


-- @@ L98-98 verbatim
end NormedField


-- @@ L100-100 verbatim
section RCLike

-- @@ L101-101 verbatim
variable {p : ℝ≥0∞}


-- @@ L103-103 expanded
@[simp]
lemma cLpNorm_conj [RCLike R] (f : α → R) : cLpNorm p (conj f) = cLpNorm p f :=
  lpNorm_conj ..


-- @@ L105-105 verbatim
end RCLike


-- @@ L107-107 verbatim
section DiscreteMeasurableSpace

-- @@ L108-108 verbatim
variable [DiscreteMeasurableSpace α] [Finite α]


-- @@ L110-111 expanded
lemma cLpNorm_add_le (hp : 1 ≤ p) : cLpNorm p (f + g) ≤ cLpNorm p f + cLpNorm p g :=
  lpNorm_add_le .of_discrete hp


-- @@ L113-114 expanded
lemma cLpNorm_sub_le (hp : 1 ≤ p) : cLpNorm p (f - g) ≤ cLpNorm p f + cLpNorm p g :=
  lpNorm_sub_le .of_discrete hp


-- @@ L116-117 expanded
lemma cLpNorm_sum_le {ι : Type*} {s : Finset ι} {f : ι → α → E} (hp : 1 ≤ p) :
    cLpNorm p (∑ i ∈ s, f i) ≤ ∑ i ∈ s, cLpNorm p (f i) :=
  lpNorm_sum_le (fun _ _ ↦ .of_discrete) hp


-- @@ L119-121 expanded
lemma cLpNorm_expect_le [Module ℚ≥0 E] [NormedSpace ℝ E] {ι : Type*} {s : Finset ι} {f : ι → α → E}
    (hp : 1 ≤ p) : cLpNorm p (𝔼 i ∈ s, f i) ≤ 𝔼 i ∈ s, cLpNorm p (f i) :=
  lpNorm_expect_le (fun _ _ ↦ .of_discrete) hp


-- @@ L123-124 expanded
lemma cLpNorm_le_cLpNorm_add_cLpNorm_sub' (hp : 1 ≤ p) :
    cLpNorm p f ≤ cLpNorm p g + cLpNorm p (f - g) :=
  lpNorm_le_lpNorm_add_lpNorm_sub' .of_discrete hp


-- @@ L126-127 expanded
lemma cLpNorm_le_cLpNorm_add_cLpNorm_sub (hp : 1 ≤ p) :
    cLpNorm p f ≤ cLpNorm p g + cLpNorm p (g - f) :=
  lpNorm_le_lpNorm_add_lpNorm_sub .of_discrete hp


-- @@ L129-130 expanded
lemma cLpNorm_le_add_cLpNorm_add (hp : 1 ≤ p) : cLpNorm p f ≤ cLpNorm p (f + g) + cLpNorm p g :=
  lpNorm_le_add_lpNorm_add .of_discrete hp


-- @@ L132-134 expanded
lemma cLpNorm_sub_le_cLpNorm_sub_add_cLpNorm_sub (hp : 1 ≤ p) :
    cLpNorm p (f - h) ≤ cLpNorm p (f - g) + cLpNorm p (g - h) :=
  lpNorm_sub_le_lpNorm_sub_add_lpNorm_sub .of_discrete .of_discrete hp


-- @@ L136-136 verbatim
end DiscreteMeasurableSpace


-- @@ L138-138 verbatim
variable [Finite α]


-- @@ L140-142 expanded
@[simp]
lemma cLpNorm_const [Nonempty α] {p : ℝ≥0∞} (hp : p ≠ 0) (a : E) :
    (cLpNorm p fun _i : α ↦ a) = ‖a‖₊ := by cases nonempty_fintype α;
  simp [cLpNorm, uniformOn, Measure.real, *]


-- @@ L144-144 verbatim
section NormedField

-- @@ L145-145 verbatim
variable [NormedField 𝕜] {p : ℝ≥0∞} {f g : α → 𝕜}


-- @@ L147-148 expanded
@[simp]
lemma cLpNorm_one [Nonempty α] (hp : p ≠ 0) : cLpNorm p (1 : α → 𝕜) = 1 := by
  cases nonempty_fintype α; simp [cLpNorm, uniformOn, Measure.real, *]


-- @@ L150-150 verbatim
end NormedField


-- @@ L152-152 verbatim
omit [Finite α]

-- @@ L153-153 verbatim
variable [DiscreteMeasurableSpace α] [Fintype α]


-- @@ L155-158 expanded
lemma cLpNorm_eq_expect_norm' (hp₀ : p ≠ 0) (hp : p ≠ ∞) (f : α → E) :
    cLpNorm p f = (𝔼 i, ‖f i‖ ^ p.toReal) ^ p.toReal⁻¹ := by
  simp [cLpNorm, uniformOn, lpNorm_eq_integral_norm_rpow_toReal hp₀ hp .of_discrete,
    integral_fintype, cond_apply, expect_eq_sum_div_card, div_eq_inv_mul, ← mul_sum, Measure.real]


-- @@ L160-162 expanded
lemma cLpNorm_toNNReal_eq_expect_norm {p : ℝ} (hp : 0 < p) (f : α → E) :
    cLpNorm p.toNNReal f = (𝔼 i, ‖f i‖ ^ p) ^ p⁻¹ := by
  rw [cLpNorm_eq_expect_norm'] <;> simp [hp.le, hp]


-- @@ L164-166 expanded
lemma cLpNorm_eq_expect_norm {p : ℝ≥0} (hp : p ≠ 0) (f : α → E) :
    cLpNorm p f = (𝔼 i, ‖f i‖ ^ (p : ℝ)) ^ (p⁻¹ : ℝ) :=
  cLpNorm_eq_expect_norm' (by simpa using hp) (by simp) _


-- @@ L168-170 expanded
lemma cLpNorm_rpow_eq_expect_norm {p : ℝ≥0} (hp : p ≠ 0) (f : α → E) :
    cLpNorm p f ^ (p : ℝ) = 𝔼 i, ‖f i‖ ^ (p : ℝ) := by
  rw [cLpNorm_eq_expect_norm hp, Real.rpow_inv_rpow] <;> positivity


-- @@ L172-174 expanded
lemma cLpNorm_pow_eq_expect_norm {p : ℕ} (hp : p ≠ 0) (f : α → E) :
    cLpNorm p f ^ p = 𝔼 i, ‖f i‖ ^ p := by
  simpa using cLpNorm_rpow_eq_expect_norm (Nat.cast_ne_zero.2 hp) f


-- @@ L176-177 expanded
lemma cL2Norm_sq_eq_expect_norm (f : α → E) : cLpNorm 2 f ^ 2 = 𝔼 i, ‖f i‖ ^ 2 := by
  simpa using cLpNorm_pow_eq_expect_norm two_ne_zero _


-- @@ L179-180 expanded
lemma cL2Norm_eq_expect_norm (f : α → E) : cLpNorm 2 f = (𝔼 i, ‖f i‖ ^ 2) ^ (2⁻¹ : ℝ) := by
  simpa [sqrt_eq_rpow] using cLpNorm_eq_expect_norm two_ne_zero _


-- @@ L182-183 expanded
lemma cL1Norm_eq_expect_norm (f : α → E) : cLpNorm 1 f = 𝔼 i, ‖f i‖ := by
  simp [cLpNorm_eq_expect_norm']


-- @@ L185-185 verbatim
omit [Fintype α]

-- @@ L186-186 verbatim
variable [Finite α]


-- @@ L188-189 expanded
lemma cLpNorm_exponent_top_eq_essSup (f : α → E) : cLpNorm ∞ f = ⨆ i, ‖f i‖ := by
  cases isEmpty_or_nonempty α <;> simp [cLpNorm, lpNorm_exponent_top_eq_essSup]


-- @@ L191-193 expanded
@[simp]
lemma cLpNorm_eq_zero (hp : p ≠ 0) : cLpNorm p f = 0 ↔ f = 0 :=
  by
  cases nonempty_fintype α
  simp [cLpNorm, uniformOn, lpNorm_eq_zero .of_discrete hp, ae_eq_top.2, cond_apply]


-- @@ L195-196 expanded
@[simp]
lemma cLpNorm_pos (hp : p ≠ 0) : 0 < cLpNorm p f ↔ f ≠ 0 :=
  lpNorm_nonneg.lt_iff_ne'.trans (cLpNorm_eq_zero hp).not


-- @@ L198-203 expanded
@[gcongr]
lemma cLpNorm_mono_right (hpq : p ≤ q) : cLpNorm p f ≤ cLpNorm q f :=
  by
  cases isEmpty_or_nonempty α
  · simp [cLpNorm]
  rw [cLpNorm, cLpNorm, ← toReal_eLpNorm .of_discrete, ← toReal_eLpNorm .of_discrete]
  exact
    ENNReal.toReal_mono (MemLp.of_discrete (p := q)).eLpNorm_ne_top
      (eLpNorm_le_eLpNorm_of_exponent_le hpq .of_discrete)


-- @@ L205-206 expanded
lemma cLpNorm_mono_real {g : α → ℝ} (h : ∀ x, ‖f x‖ ≤ g x) : cLpNorm p f ≤ cLpNorm p g :=
  lpNorm_mono_real .of_discrete h


-- @@ L208-208 verbatim
omit [Finite α]

-- @@ L209-220 expanded
lemma cLpNorm_two_mul_sum_pow [Fintype α] {ι : Type*} {n : ℕ} (hn : n ≠ 0) (s : Finset ι)
    (f : ι → α → ℂ) :
    cLpNorm (2 * n) (∑ i ∈ s, f i) ^ (2 * n) =
      ∑ x ∈ s ^^ n, ∑ y ∈ s ^^ n, 𝔼 a, (∏ i, conj (f (x i) a)) * ∏ i, f (y i) a :=
  calc
    _ = 𝔼 a, (‖∑ i ∈ s, f i a‖ : ℂ) ^ (2 * n) :=
      by
      norm_cast
      rw [← cLpNorm_pow_eq_expect_norm (by positivity)]
      simp_rw [← Finset.sum_apply]
    _ = 𝔼 a, (∑ i ∈ s, conj (f i a)) ^ n * (∑ j ∈ s, f j a) ^ n := by
      simp_rw [pow_mul, ← Complex.conj_mul', mul_pow, map_sum]
    _ = _ := by simp_rw [sum_pow', sum_mul_sum, expect_sum_comm]


-- @@ L222-222 verbatim
end NormedAddCommGroup

-- @@ L223-223 verbatim
end MeasureTheory


-- @@ L225-225 verbatim
namespace Mathlib.Meta.Positivity

-- @@ L226-226 verbatim
open Lean Meta Qq Function MeasureTheory


-- @@ L228-228 verbatim
alias ⟨_, cLpNorm_pos_of_ne_zero⟩ := cLpNorm_pos


-- @@ L230-255 unexpanded
/-- The `positivity` extension which identifies expressions of the form `‖f‖ₙ_[p]`. -/
@[positivity ‖_‖ₙ_[_]] meta def evalCLpNorm : PositivityExt where eval {u} R _z _p e :=
  match _p with
  | none => pure .none
  | some _ => do
  match u, R, e with
  | 0, ~q(ℝ), ~q(@cLpNorm $α $E $instαmeas $instEnorm $p $f) =>
    assumeInstancesCommute
    try {
      let some pp := (← core q(inferInstance) (some q(inferInstance)) p).toNonzero | failure
      try
        let _pE ← synthInstanceQ q(PartialOrder $E)
        let _ ← synthInstanceQ q(Finite $α)
        let _ ← synthInstanceQ q(DiscreteMeasurableSpace $α)
        let some pf := (← core q(inferInstance) (some q(inferInstance)) f).toNonzero | failure
        return .positive q(@cLpNorm_pos_of_ne_zero $α _ _ _ _ _ _ _ $pp $pf)
      catch _ =>
        assumeInstancesCommute
        let some pf ← findLocalDeclWithType? q($f ≠ 0) | failure
        let pf : Q($f ≠ 0) := .fvar pf
        let _ ← synthInstanceQ q(Fintype $α)
        let _ ← synthInstanceQ q(DiscreteMeasurableSpace $α)
        return .positive q(cLpNorm_pos_of_ne_zero $pp $pf)
    } catch _ =>
      return .nonnegative q(cLpNorm_nonneg)
  | _ => throwError "not cLpNorm"


-- @@ L257-257 verbatim
section Examples

-- @@ L258-258 verbatim
section NormedAddCommGroup

-- @@ L259-259 verbatim
variable [Fintype α] [DiscreteMeasurableSpace α] [NormedAddCommGroup E] [PartialOrder E] {f : α → E}


-- @@ L261-261 expanded
example {p : ℝ≥0∞} : 0 ≤ cLpNorm p f := by positivity


-- @@ L262-262 expanded
example {p : ℝ≥0∞} (hp : p ≠ 0) (hf : f ≠ 0) : 0 < cLpNorm p f := by positivity


-- @@ L263-263 expanded
example {p : ℝ≥0∞} (hp : p ≠ 0) {f : α → ℝ} (hf : 0 < f) : 0 < cLpNorm p f := by positivity


-- @@ L265-265 verbatim
end NormedAddCommGroup


-- @@ L267-267 verbatim
section Complex

-- @@ L268-268 verbatim
variable [Fintype α] [DiscreteMeasurableSpace α] {w : α → ℝ≥0} {f : α → ℂ}


-- @@ L270-270 expanded
example {p : ℝ≥0∞} (hp : p ≠ 0) (hf : f ≠ 0) : 0 < cLpNorm p f := by positivity


-- @@ L271-271 expanded
example {p : ℝ≥0∞} (hp : p ≠ 0) {f : α → ℝ} (hf : 0 < f) : 0 < cLpNorm p f := by positivity


-- @@ L273-273 verbatim
end Complex

-- @@ L274-274 verbatim
end Examples

-- @@ L275-275 verbatim
end Mathlib.Meta.Positivity


-- @@ L277-277 verbatim
/-! ### Hölder inequality -/


-- @@ L279-279 verbatim
namespace MeasureTheory

-- @@ L280-280 verbatim
section Real

-- @@ L281-282 verbatim
variable {α : Type*} {mα : MeasurableSpace α} [DiscreteMeasurableSpace α] [Finite α] {p q : ℝ≥0}
  {f g : α → ℝ}


-- @@ L284-292 expanded
lemma cLpNorm_rpow (hp : p ≠ 0) (hq : q ≠ 0) (hf : 0 ≤ f) :
    cLpNorm p (f ^ (q : ℝ)) = cLpNorm (p * q) f ^ (q : ℝ) :=
  by
  cases nonempty_fintype α
  refine rpow_left_injOn (NNReal.coe_ne_zero.2 hp) (by dsimp; positivity) (by dsimp; positivity) ?_
  dsimp
  rw [← rpow_mul (by positivity), ← mul_comm, ← ENNReal.coe_mul, ← NNReal.coe_mul,
    cLpNorm_rpow_eq_expect_norm hp, cLpNorm_rpow_eq_expect_norm (mul_ne_zero hq hp)]
  simp [abs_rpow_of_nonneg (hf _), rpow_mul]


-- @@ L294-303 expanded
lemma cLpNorm_pow (hp : p ≠ 0) {q : ℕ} (hq : q ≠ 0) (f : α → ℂ) :
    cLpNorm p (f ^ q) = cLpNorm (p * q) f ^ q :=
  by
  cases nonempty_fintype α
  refine rpow_left_injOn (NNReal.coe_ne_zero.2 hp) (by dsimp; positivity) (by dsimp; positivity) ?_
  dsimp
  rw [← rpow_natCast_mul (by positivity), ← mul_comm, ← ENNReal.coe_natCast, ← ENNReal.coe_mul, ←
    NNReal.coe_natCast, ← NNReal.coe_mul, cLpNorm_rpow_eq_expect_norm hp,
    cLpNorm_rpow_eq_expect_norm (by positivity)]
  simp [← rpow_natCast_mul]


-- @@ L305-306 expanded
lemma cL1Norm_rpow (hq : q ≠ 0) (hf : 0 ≤ f) : cLpNorm 1 (f ^ (q : ℝ)) = cLpNorm q f ^ (q : ℝ) := by
  simpa only [ENNReal.coe_one, one_mul] using cLpNorm_rpow one_ne_zero hq hf


-- @@ L308-309 expanded
lemma cL1Norm_pow {q : ℕ} (hq : q ≠ 0) (f : α → ℂ) : cLpNorm 1 (f ^ q) = cLpNorm q f ^ q := by
  simpa only [ENNReal.coe_one, one_mul] using cLpNorm_pow one_ne_zero hq f


-- @@ L311-311 verbatim
end Real


-- @@ L313-313 verbatim
section Hoelder

-- @@ L314-315 verbatim
variable {α : Type*} {mα : MeasurableSpace α} [DiscreteMeasurableSpace α] [Finite α] [RCLike 𝕜]
  {p q : ℝ≥0} {f g : α → 𝕜}


-- @@ L317-321 expanded
lemma cLpNorm_rpow' (hp : p ≠ 0) (hq : q ≠ 0) (f : α → 𝕜) :
    cLpNorm p f ^ (q : ℝ) = cLpNorm (p / q) ((fun a ↦ ‖f a‖) ^ (q : ℝ)) :=
  by
  rw [← ENNReal.coe_div hq, cLpNorm_rpow (div_ne_zero hp hq) hq (fun _ ↦ norm_nonneg _),
    cLpNorm_norm, ← ENNReal.coe_mul, div_mul_cancel₀ _ hq]
  fun_prop


-- @@ L323-323 verbatim
end Hoelder


-- @@ L325-325 verbatim
section

-- @@ L326-326 verbatim
variable {α : Type*} {mα : MeasurableSpace α}


-- @@ L328-333 expanded
@[simp]
lemma RCLike.cLpNorm_coe_comp [RCLike 𝕜] (p) (f : α → ℝ) :
    cLpNorm p (((↑) : ℝ → 𝕜) ∘ f) = cLpNorm p f :=
  by
  simp only [cLpNorm, lpNorm, comp_def]
  rw! (castMode :=
    .all) [RCLike.isUniformEmbedding_ofReal.isEmbedding.aestronglyMeasurable_comp_iff]
  simp [eLpNorm, eLpNorm', eLpNormEssSup]


-- @@ L335-336 expanded
@[simp]
lemma Complex.cLpNorm_coe_comp (p) (f : α → ℝ) : cLpNorm p (((↑) : ℝ → ℂ) ∘ f) = cLpNorm p f :=
  RCLike.cLpNorm_coe_comp ..


-- @@ L338-338 verbatim
end

-- @@ L339-339 verbatim
end MeasureTheory



-- @@ L342-342 verbatim
namespace MeasureTheory

-- @@ L343-343 verbatim
variable {ι G 𝕜 E R : Type*} [Fintype ι] {mι : MeasurableSpace ι} [DiscreteMeasurableSpace ι]


-- @@ L345-345 verbatim
/-! ### Indicator -/


-- @@ L347-347 verbatim
section Indicator

-- @@ L348-348 verbatim
variable [RCLike R] {s : Finset ι} {p : ℝ≥0}


-- @@ L350-358 expanded
lemma cLpNorm_rpow_indicator_one (hp : p ≠ 0) (s : Finset ι) :
    cLpNorm p 𝟭_[(s : Set ι), R] ^ (p : ℝ) = s.dens := by
  classical
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simpa [Real.rpow_eq_zero_iff_of_nonneg]
  have : ∀ x, (ite (x ∈ s) 1 0 : ℝ) ^ (p : ℝ) = ite (x ∈ s) (1 ^ (p : ℝ)) (0 ^ (p : ℝ)) := fun x ↦
    by split_ifs <;> simp
  simp [cLpNorm_rpow_eq_expect_norm, hp, Set.indicator_apply, apply_ite norm, expect_const,
    nnratCast_dens, hs]


-- @@ L360-362 expanded
lemma cLpNorm_indicator_one (hp : p ≠ 0) (s : Finset ι) :
    cLpNorm p 𝟭_[(s : Set ι), R] = s.dens ^ (p⁻¹ : ℝ) := by
  refine (eq_rpow_inv ?_ ?_ ?_).2 (cLpNorm_rpow_indicator_one ?_ _) <;> positivity


-- @@ L364-366 expanded
lemma cLpNorm_pow_indicator_one {p : ℕ} (hp : p ≠ 0) (s : Finset ι) :
    cLpNorm p 𝟭_[(s : Set ι), R] ^ (p : ℝ) = s.dens := by
  simpa using cLpNorm_rpow_indicator_one (Nat.cast_ne_zero.2 hp) s


-- @@ L368-369 expanded
lemma cL2Norm_sq_indicator_one (s : Finset ι) : cLpNorm 2 𝟭_[(s : Set ι), R] ^ 2 = s.dens := by
  simpa using cLpNorm_pow_indicator_one two_ne_zero s


-- @@ L371-373 expanded
@[simp]
lemma cL2Norm_indicator_one (s : Finset ι) : cLpNorm 2 𝟭_[(s : Set ι), R] = Real.sqrt s.dens := by
  rw [eq_comm, sqrt_eq_iff_eq_sq, cL2Norm_sq_indicator_one] <;> positivity


-- @@ L375-376 expanded
@[simp]
lemma cL1Norm_indicator_one (s : Finset ι) : cLpNorm 1 𝟭_[(s : Set ι), R] = s.dens := by
  simpa using cLpNorm_pow_indicator_one one_ne_zero s


-- @@ L378-378 verbatim
end Indicator


-- @@ L380-380 verbatim
/-! ### Translation -/


-- @@ L382-382 verbatim
section cLpNorm

-- @@ L383-384 verbatim
variable {mG : MeasurableSpace G} [DiscreteMeasurableSpace G] [AddCommGroup G] [Finite G]
  {p : ℝ≥0∞}


-- @@ L386-396 expanded
@[simp]
lemma cLpNorm_translate [NormedAddCommGroup E] (a : G) (f : G → E) :
    cLpNorm p (τ a f) = cLpNorm p f :=
  by
  cases nonempty_fintype G
  obtain p | p := p
  · simp only [cLpNorm_exponent_top_eq_essSup, ENNReal.none_eq_top, translate_apply]
    exact (Equiv.subRight _).iSup_congr fun _ ↦ rfl
  obtain rfl | hp := eq_or_ne p 0
  · simp only [cLpNorm_exponent_zero, ENNReal.some_eq_coe, ENNReal.coe_zero]
  · simp only [cLpNorm_eq_expect_norm hp, ENNReal.some_eq_coe, translate_apply]
    congr 1
    exact Fintype.expect_equiv (Equiv.subRight _) _ _ fun _ ↦ rfl


-- @@ L398-408 expanded
@[simp]
lemma cLpNorm_conjneg [RCLike E] (f : G → E) : cLpNorm p (conjneg f) = cLpNorm p f :=
  by
  cases nonempty_fintype G
  simp only [conjneg, cLpNorm_conj]
  obtain p | p := p
  · simp only [cLpNorm_exponent_top_eq_essSup, ENNReal.none_eq_top]
    exact (Equiv.neg _).iSup_congr fun _ ↦ rfl
  obtain rfl | hp := eq_or_ne p 0
  · simp only [cLpNorm_exponent_zero, ENNReal.some_eq_coe, ENNReal.coe_zero]
  · simp only [cLpNorm_eq_expect_norm hp, ENNReal.some_eq_coe]
    congr 1
    exact Fintype.expect_equiv (Equiv.neg _) _ _ fun _ ↦ rfl


-- @@ L410-420 expanded
lemma cLpNorm_translate_sum_sub_le [NormedAddCommGroup E] (hp : 1 ≤ p) {ι : Type*} (s : Finset ι)
    (a : ι → G) (f : G → E) :
    cLpNorm p (τ (∑ i ∈ s, a i) f - f) ≤ ∑ i ∈ s, cLpNorm p (τ (a i) f - f) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s ih hs =>
    calc
      _ = cLpNorm p (τ (∑ j ∈ s, a j) (τ (a i) f - f) + (τ (∑ j ∈ s, a j) f - f)) := by
        rw [sum_cons, translate_add', translate_sub_right, sub_add_sub_cancel]
      _ ≤ cLpNorm p (τ (∑ j ∈ s, a j) (τ (a i) f - f)) + ∑ j ∈ s, cLpNorm p (τ (a j) f - f) := by
        grw [cLpNorm_add_le hp, hs]
      _ = _ := by rw [cLpNorm_translate, sum_cons]


-- @@ L422-422 verbatim
end cLpNorm

-- @@ L423-423 verbatim
end MeasureTheory
