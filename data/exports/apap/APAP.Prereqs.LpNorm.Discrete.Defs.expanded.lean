module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs

import APAP.Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Tactic.DepRewrite
import Mathlib.Tactic.Positivity.Finset


-- @@ L11-13 verbatim
/-!
# Lp norms
-/


-- @@ L15-15 verbatim
@[expose] public section


-- @@ L17-17 verbatim
open Finset Function Real

-- @@ L18-18 verbatim
open scoped BigOperators ComplexConjugate ENNReal NNReal NNRat


-- @@ L20-20 verbatim
local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s


-- @@ L22-22 verbatim
variable {α 𝕜 R E : Type*} [MeasurableSpace α]


-- @@ L24-24 verbatim
namespace MeasureTheory

-- @@ L25-25 verbatim
variable [NormedAddCommGroup E] {p q : ℝ≥0∞} {f g h : α → E}


-- @@ L27-28 verbatim
/-- The Lp norm of a function with the compact normalisation. -/
noncomputable def dLpNorm (p : ℝ≥0∞) (f : α → E) : ℝ := lpNorm f p .count


-- @@ L30-30 verbatim
notation "‖" f "‖_[" p "]" => dLpNorm p f


-- @@ L32-32 expanded
@[simp]
lemma dLpNorm_nonneg : 0 ≤ dLpNorm p f := by simp [dLpNorm]


-- @@ L34-34 expanded
@[simp]
lemma dLpNorm_exponent_zero (f : α → E) : dLpNorm 0 f = 0 := by simp [dLpNorm]


-- @@ L36-36 expanded
@[simp]
lemma dLpNorm_zero (p : ℝ≥0∞) : dLpNorm p (0 : α → E) = 0 := by simp [dLpNorm]


-- @@ L37-37 expanded
@[simp]
lemma dLpNorm_zero' (p : ℝ≥0∞) : dLpNorm p (fun _ ↦ 0 : α → E) = 0 := by simp [dLpNorm]


-- @@ L39-40 expanded
@[simp]
lemma dLpNorm_of_isEmpty [IsEmpty α] (f : α → E) (p : ℝ≥0∞) : dLpNorm p f = 0 := by simp [dLpNorm]


-- @@ L42-42 expanded
@[simp]
lemma dLpNorm_neg (f : α → E) (p : ℝ≥0∞) : dLpNorm p (-f) = dLpNorm p f := by simp [dLpNorm]


-- @@ L43-44 expanded
@[simp]
lemma dLpNorm_neg' (f : α → E) (p : ℝ≥0∞) : (dLpNorm p fun x ↦ -f x) = dLpNorm p f := by
  simp [dLpNorm]


-- @@ L46-47 expanded
lemma dLpNorm_sub_comm (f g : α → E) (p : ℝ≥0∞) : dLpNorm p (f - g) = dLpNorm p (g - f) := by
  simp [dLpNorm, lpNorm_sub_comm]


-- @@ L49-51 expanded
@[simp]
lemma dLpNorm_norm (hf : StronglyMeasurable f) (p : ℝ≥0∞) :
    (dLpNorm p fun i ↦ ‖f i‖) = dLpNorm p f :=
  lpNorm_norm hf.aestronglyMeasurable _


-- @@ L53-55 expanded
@[simp]
lemma dLpNorm_abs {f : α → ℝ} (hf : StronglyMeasurable f) (p : ℝ≥0∞) :
    dLpNorm p |f| = dLpNorm p f :=
  lpNorm_abs hf.aestronglyMeasurable _


-- @@ L57-60 expanded
@[simp]
lemma dLpNorm_fun_abs {f : α → ℝ} (hf : StronglyMeasurable f) (p : ℝ≥0∞) :
    (dLpNorm p fun i ↦ |f i|) = dLpNorm p f :=
  lpNorm_fun_abs hf.aestronglyMeasurable _


-- @@ L62-62 verbatim
section NormedField

-- @@ L63-63 verbatim
variable [NormedField 𝕜] {p : ℝ≥0∞} {f g : α → 𝕜}


-- @@ L65-66 expanded
lemma dLpNorm_const_smul [Module 𝕜 E] [NormSMulClass 𝕜 E] (c : 𝕜) (f : α → E) :
    dLpNorm p (c • f) = ‖c‖ * dLpNorm p f := by simp [dLpNorm, lpNorm_const_smul]


-- @@ L68-69 expanded
lemma dLpNorm_nsmul [NormedSpace ℝ E] (n : ℕ) (f : α → E) (p : ℝ≥0∞) :
    dLpNorm p (n • f) = n • dLpNorm p f := by simp [dLpNorm, lpNorm_nsmul]


-- @@ L71-71 verbatim
variable [NormedSpace ℝ 𝕜]


-- @@ L73-74 expanded
lemma dLpNorm_natCast_mul (n : ℕ) (f : α → 𝕜) (p : ℝ≥0∞) :
    dLpNorm p ((n : α → 𝕜) * f) = n * dLpNorm p f :=
  lpNorm_natCast_mul ..


-- @@ L76-77 expanded
lemma dLpNorm_fun_natCast_mul (n : ℕ) (f : α → 𝕜) (p : ℝ≥0∞) :
    dLpNorm p (n * f ·) = n * dLpNorm p f :=
  lpNorm_fun_natCast_mul ..


-- @@ L79-80 expanded
lemma dLpNorm_mul_natCast (f : α → 𝕜) (n : ℕ) (p : ℝ≥0∞) :
    dLpNorm p (f * (n : α → 𝕜)) = dLpNorm p f * n :=
  lpNorm_mul_natCast ..


-- @@ L82-83 expanded
lemma dLpNorm_fun_mul_natCast (f : α → 𝕜) (n : ℕ) (p : ℝ≥0∞) :
    dLpNorm p (f · * n) = dLpNorm p f * n :=
  lpNorm_fun_mul_natCast ..


-- @@ L85-86 expanded
lemma dLpNorm_div_natCast [CharZero 𝕜] {n : ℕ} (hn : n ≠ 0) (f : α → 𝕜) (p : ℝ≥0∞) :
    dLpNorm p (f / (n : α → 𝕜)) = dLpNorm p f / n :=
  lpNorm_div_natCast hn ..


-- @@ L88-89 expanded
lemma dLpNorm_fun_div_natCast [CharZero 𝕜] {n : ℕ} (hn : n ≠ 0) (f : α → 𝕜) (p : ℝ≥0∞) :
    dLpNorm p (f · / n) = dLpNorm p f / n :=
  lpNorm_fun_div_natCast hn ..


-- @@ L91-91 verbatim
end NormedField


-- @@ L93-94 expanded
lemma dLpNorm_nnqsmul (q : ℚ≥0) (f : α → ℂ) : dLpNorm p (q • f) = q * dLpNorm p f := by
  simpa [NNRat.cast_smul_eq_nnqsmul] using dLpNorm_const_smul (q : ℂ) f


-- @@ L96-96 verbatim
section RCLike

-- @@ L97-97 verbatim
variable {p : ℝ≥0∞}


-- @@ L99-99 expanded
@[simp]
lemma dLpNorm_conj [RCLike R] (f : α → R) : dLpNorm p (conj f) = dLpNorm p f :=
  lpNorm_conj ..


-- @@ L101-101 verbatim
end RCLike


-- @@ L103-103 verbatim
section DiscreteMeasurableSpace

-- @@ L104-104 verbatim
variable [DiscreteMeasurableSpace α] [Finite α]


-- @@ L106-107 expanded
lemma dLpNorm_add_le (hp : 1 ≤ p) : dLpNorm p (f + g) ≤ dLpNorm p f + dLpNorm p g :=
  lpNorm_add_le .of_discrete hp


-- @@ L109-110 expanded
lemma dLpNorm_sub_le (hp : 1 ≤ p) : dLpNorm p (f - g) ≤ dLpNorm p f + dLpNorm p g :=
  lpNorm_sub_le .of_discrete hp


-- @@ L112-113 expanded
lemma dLpNorm_sum_le {ι : Type*} {s : Finset ι} {f : ι → α → E} (hp : 1 ≤ p) :
    dLpNorm p (∑ i ∈ s, f i) ≤ ∑ i ∈ s, dLpNorm p (f i) :=
  lpNorm_sum_le (fun _ _ ↦ .of_discrete) hp


-- @@ L115-117 expanded
lemma dLpNorm_expect_le [Module ℚ≥0 E] [NormedSpace ℝ E] {ι : Type*} {s : Finset ι} {f : ι → α → E}
    (hp : 1 ≤ p) : dLpNorm p (𝔼 i ∈ s, f i) ≤ 𝔼 i ∈ s, dLpNorm p (f i) :=
  lpNorm_expect_le (fun _ _ ↦ .of_discrete) hp


-- @@ L119-120 expanded
lemma dLpNorm_le_dLpNorm_add_dLpNorm_sub' (hp : 1 ≤ p) :
    dLpNorm p f ≤ dLpNorm p g + dLpNorm p (f - g) :=
  lpNorm_le_lpNorm_add_lpNorm_sub' .of_discrete hp


-- @@ L122-123 expanded
lemma dLpNorm_le_dLpNorm_add_dLpNorm_sub (hp : 1 ≤ p) :
    dLpNorm p f ≤ dLpNorm p g + dLpNorm p (g - f) :=
  lpNorm_le_lpNorm_add_lpNorm_sub .of_discrete hp


-- @@ L125-126 expanded
lemma dLpNorm_le_add_dLpNorm_add (hp : 1 ≤ p) : dLpNorm p f ≤ dLpNorm p (f + g) + dLpNorm p g :=
  lpNorm_le_add_lpNorm_add .of_discrete hp


-- @@ L128-130 expanded
lemma dLpNorm_sub_le_dLpNorm_sub_add_dLpNorm_sub (hp : 1 ≤ p) :
    dLpNorm p (f - h) ≤ dLpNorm p (f - g) + dLpNorm p (g - h) :=
  lpNorm_sub_le_lpNorm_sub_add_lpNorm_sub .of_discrete .of_discrete hp


-- @@ L132-132 verbatim
end DiscreteMeasurableSpace


-- @@ L134-134 verbatim
variable [Fintype α]


-- @@ L136-139 expanded
@[simp]
lemma dLpNorm_const [Nonempty α] {p : ℝ≥0∞} (hp : p ≠ 0) (a : E) :
    (dLpNorm p fun _i : α ↦ a) = ‖a‖₊ * Fintype.card α ^ (p.toReal⁻¹ : ℝ) := by
  simp [dLpNorm, Measure.real, *]


-- @@ L141-144 expanded
@[simp]
lemma dLpNorm_const' {p : ℝ≥0∞} (hp₀ : p ≠ 0) (hp : p ≠ ∞) (a : E) :
    (dLpNorm p fun _i : α ↦ a) = ‖a‖₊ * Fintype.card α ^ (p.toReal⁻¹ : ℝ) := by
  simp [dLpNorm, Measure.real, *]


-- @@ L146-146 verbatim
section NormedField

-- @@ L147-147 verbatim
variable [NormedField 𝕜] {p : ℝ≥0∞} {f g : α → 𝕜}


-- @@ L149-150 expanded
@[simp]
lemma dLpNorm_one [Nonempty α] (hp : p ≠ 0) :
    dLpNorm p (1 : α → 𝕜) = Fintype.card α ^ (p.toReal⁻¹ : ℝ) := by simp [dLpNorm, Measure.real, *]


-- @@ L152-153 expanded
@[simp]
lemma dLpNorm_one' (hp₀ : p ≠ 0) (hp : p ≠ ∞) :
    dLpNorm p (1 : α → 𝕜) = Fintype.card α ^ (p.toReal⁻¹ : ℝ) := by simp [dLpNorm, Measure.real, *]


-- @@ L155-155 verbatim
end NormedField


-- @@ L157-157 verbatim
variable [DiscreteMeasurableSpace α]


-- @@ L159-161 expanded
lemma dLpNorm_eq_sum_norm' (hp₀ : p ≠ 0) (hp : p ≠ ∞) (f : α → E) :
    dLpNorm p f = (∑ i, ‖f i‖ ^ p.toReal) ^ p.toReal⁻¹ := by
  simp [dLpNorm, lpNorm_eq_integral_norm_rpow_toReal hp₀ hp .of_discrete, integral_fintype]


-- @@ L163-165 expanded
lemma dLpNorm_toNNReal_eq_sum_norm {p : ℝ} (hp : 0 < p) (f : α → E) :
    dLpNorm p.toNNReal f = (∑ i, ‖f i‖ ^ p) ^ p⁻¹ := by
  rw [dLpNorm_eq_sum_norm'] <;> simp [hp.le, hp]


-- @@ L167-169 expanded
lemma dLpNorm_eq_sum_norm {p : ℝ≥0} (hp : p ≠ 0) (f : α → E) :
    dLpNorm p f = (∑ i, ‖f i‖ ^ (p : ℝ)) ^ (p⁻¹ : ℝ) :=
  dLpNorm_eq_sum_norm' (by simpa using hp) (by simp) _


-- @@ L171-173 expanded
lemma dLpNorm_rpow_eq_sum_norm {p : ℝ≥0} (hp : p ≠ 0) (f : α → E) :
    dLpNorm p f ^ (p : ℝ) = ∑ i, ‖f i‖ ^ (p : ℝ) := by
  rw [dLpNorm_eq_sum_norm hp, Real.rpow_inv_rpow (by positivity) (mod_cast hp)]


-- @@ L175-176 expanded
lemma dLpNorm_pow_eq_sum_norm {p : ℕ} (hp : p ≠ 0) (f : α → E) : dLpNorm p f ^ p = ∑ i, ‖f i‖ ^ p :=
  by simpa using dLpNorm_rpow_eq_sum_norm (Nat.cast_ne_zero.2 hp) f


-- @@ L178-179 expanded
lemma dL2Norm_sq_eq_sum_norm (f : α → E) : dLpNorm 2 f ^ 2 = ∑ i, ‖f i‖ ^ 2 := by
  simpa using dLpNorm_pow_eq_sum_norm two_ne_zero _


-- @@ L181-182 expanded
lemma dL2Norm_eq_sum_norm (f : α → E) : dLpNorm 2 f = (∑ i, ‖f i‖ ^ 2) ^ (2⁻¹ : ℝ) := by
  simpa [sqrt_eq_rpow] using dLpNorm_eq_sum_norm two_ne_zero _


-- @@ L184-184 expanded
lemma dL1Norm_eq_sum_norm (f : α → E) : dLpNorm 1 f = ∑ i, ‖f i‖ := by simp [dLpNorm_eq_sum_norm']


-- @@ L186-186 verbatim
omit [Fintype α]

-- @@ L187-187 verbatim
variable [Finite α]


-- @@ L189-190 expanded
lemma dLinftyNorm_eq_iSup_norm (f : α → E) : dLpNorm ∞ f = ⨆ i, ‖f i‖ := by
  cases isEmpty_or_nonempty α <;> simp [dLpNorm, lpNorm_exponent_top_eq_essSup]


-- @@ L192-193 expanded
lemma norm_le_dLinftyNorm {i : α} : ‖f i‖ ≤ dLpNorm ∞ f := by rw [dLinftyNorm_eq_iSup_norm];
  exact le_ciSup (f := fun i ↦ ‖f i‖) (Finite.bddAbove_range _) i


-- @@ L195-196 expanded
@[simp]
lemma dLpNorm_eq_zero (hp : p ≠ 0) : dLpNorm p f = 0 ↔ f = 0 := by
  simp [dLpNorm, lpNorm_eq_zero .of_discrete hp, ae_eq_top.2]


-- @@ L198-199 expanded
@[simp]
lemma dLpNorm_pos (hp : p ≠ 0) : 0 < dLpNorm p f ↔ f ≠ 0 :=
  lpNorm_nonneg.lt_iff_ne'.trans (dLpNorm_eq_zero hp).not


-- @@ L201-202 expanded
lemma dLpNorm_mono_real {g : α → ℝ} (h : ∀ x, ‖f x‖ ≤ g x) : dLpNorm p f ≤ dLpNorm p g :=
  lpNorm_mono_real .of_discrete h


-- @@ L204-204 verbatim
omit [Finite α]

-- @@ L205-205 verbatim
variable [Fintype α]


-- @@ L207-217 expanded
lemma dLpNorm_two_mul_sum_pow {ι : Type*} {n : ℕ} (hn : n ≠ 0) (s : Finset ι) (f : ι → α → ℂ) :
    dLpNorm (2 * n) (∑ i ∈ s, f i) ^ (2 * n) =
      ∑ x ∈ s ^^ n, ∑ y ∈ s ^^ n, ∑ a, (∏ i, conj (f (x i) a)) * ∏ i, f (y i) a :=
  calc
    _ = ∑ a, (‖∑ i ∈ s, f i a‖ : ℂ) ^ (2 * n) :=
      by
      norm_cast
      rw [← dLpNorm_pow_eq_sum_norm (by positivity)]
      simp_rw [← Finset.sum_apply]
    _ = ∑ a, (∑ i ∈ s, conj (f i a)) ^ n * (∑ j ∈ s, f j a) ^ n := by
      simp_rw [pow_mul, ← Complex.conj_mul', mul_pow, map_sum]
    _ = _ := by simp_rw [sum_pow', sum_mul_sum, sum_comm (s := univ)]


-- @@ L219-219 verbatim
end MeasureTheory


-- @@ L221-221 verbatim
namespace Mathlib.Meta.Positivity

-- @@ L222-222 verbatim
open Lean Meta Qq Function MeasureTheory


-- @@ L224-224 verbatim
alias ⟨_, dLpNorm_pos_of_ne_zero⟩ := dLpNorm_pos


-- @@ L226-251 unexpanded
/-- The `positivity` extension which identifies expressions of the form `‖f‖_[p]`. -/
@[positivity ‖_‖_[_]] meta def evalDLpNorm : PositivityExt where eval {u} R _z _p e :=
  match _p with
  | none => pure .none
  | some _ => do
  match u, R, e with
  | 0, ~q(ℝ), ~q(@dLpNorm $α $E $instαmeas $instEnorm $p $f) =>
    assumeInstancesCommute
    try {
      let some pp := (← core q(inferInstance) (some q(inferInstance)) p).toNonzero | failure
      try
        let _pE ← synthInstanceQ q(PartialOrder $E)
        let _ ← synthInstanceQ q(Finite $α)
        let _ ← synthInstanceQ q(DiscreteMeasurableSpace $α)
        let some pf := (← core q(inferInstance) (some q(inferInstance)) f).toNonzero | failure
        return .positive q(@dLpNorm_pos_of_ne_zero $α _ _ _ _ _ _ _ $pp $pf)
      catch _ =>
        assumeInstancesCommute
        let some pf ← findLocalDeclWithType? q($f ≠ 0) | failure
        let pf : Q($f ≠ 0) := .fvar pf
        let _ ← synthInstanceQ q(Fintype $α)
        let _ ← synthInstanceQ q(DiscreteMeasurableSpace $α)
        return .positive q(dLpNorm_pos_of_ne_zero $pp $pf)
    } catch _ =>
      return .nonnegative q(dLpNorm_nonneg)
  | _ => throwError "not dLpNorm"


-- @@ L253-253 verbatim
section Examples

-- @@ L254-254 verbatim
section NormedAddCommGroup

-- @@ L255-255 verbatim
variable [Fintype α] [DiscreteMeasurableSpace α] [NormedAddCommGroup E] [PartialOrder E] {f : α → E}


-- @@ L257-257 expanded
example {p : ℝ≥0∞} (hp : p ≠ 0) (hf : f ≠ 0) : 0 < dLpNorm p f := by positivity


-- @@ L258-258 expanded
example {p : ℝ≥0∞} (hp : p ≠ 0) {f : α → ℝ} (hf : 0 < f) : 0 < dLpNorm p f := by positivity


-- @@ L260-260 verbatim
end NormedAddCommGroup


-- @@ L262-262 verbatim
section Complex

-- @@ L263-263 verbatim
variable [Fintype α] [DiscreteMeasurableSpace α] {f : α → ℂ}


-- @@ L265-265 expanded
example {p : ℝ≥0∞} (hp : p ≠ 0) (hf : f ≠ 0) : 0 < dLpNorm p f := by positivity


-- @@ L266-266 expanded
example {p : ℝ≥0∞} (hp : p ≠ 0) {f : α → ℝ} (hf : 0 < f) : 0 < dLpNorm p f := by positivity


-- @@ L268-268 verbatim
end Complex

-- @@ L269-269 verbatim
end Examples

-- @@ L270-270 verbatim
end Mathlib.Meta.Positivity


-- @@ L272-272 verbatim
/-! ### Hölder inequality -/


-- @@ L274-274 verbatim
namespace MeasureTheory

-- @@ L275-275 verbatim
section Real

-- @@ L276-277 verbatim
variable {α : Type*} {mα : MeasurableSpace α} [DiscreteMeasurableSpace α] [Finite α] {p q : ℝ≥0}
  {f g : α → ℝ}


-- @@ L279-287 expanded
lemma dLpNorm_rpow (hp : p ≠ 0) (hq : q ≠ 0) (hf : 0 ≤ f) :
    dLpNorm p (f ^ (q : ℝ)) = dLpNorm (p * q) f ^ (q : ℝ) :=
  by
  cases nonempty_fintype α
  refine rpow_left_injOn (NNReal.coe_ne_zero.2 hp) (by dsimp; positivity) (by dsimp; positivity) ?_
  dsimp
  rw [← rpow_mul (by positivity), ← mul_comm, ← ENNReal.coe_mul, ← NNReal.coe_mul,
    dLpNorm_rpow_eq_sum_norm hp, dLpNorm_rpow_eq_sum_norm (mul_ne_zero hq hp)]
  simp [abs_rpow_of_nonneg (hf _), ← rpow_mul]


-- @@ L289-298 expanded
lemma dLpNorm_pow (hp : p ≠ 0) {q : ℕ} (hq : q ≠ 0) (f : α → ℂ) :
    dLpNorm p (f ^ q) = dLpNorm (p * q) f ^ q :=
  by
  cases nonempty_fintype α
  refine rpow_left_injOn (NNReal.coe_ne_zero.2 hp) (by dsimp; positivity) (by dsimp; positivity) ?_
  dsimp
  rw [← rpow_natCast_mul (by positivity), ← mul_comm, ← ENNReal.coe_natCast, ← ENNReal.coe_mul, ←
    NNReal.coe_natCast, ← NNReal.coe_mul, dLpNorm_rpow_eq_sum_norm hp,
    dLpNorm_rpow_eq_sum_norm (by positivity)]
  simp [← rpow_natCast_mul]


-- @@ L300-301 expanded
lemma dL1Norm_rpow (hq : q ≠ 0) (hf : 0 ≤ f) : dLpNorm 1 (f ^ (q : ℝ)) = dLpNorm q f ^ (q : ℝ) := by
  simpa only [ENNReal.coe_one, one_mul] using dLpNorm_rpow one_ne_zero hq hf


-- @@ L303-304 expanded
lemma dL1Norm_pow {q : ℕ} (hq : q ≠ 0) (f : α → ℂ) : dLpNorm 1 (f ^ q) = dLpNorm q f ^ q := by
  simpa only [ENNReal.coe_one, one_mul] using dLpNorm_pow one_ne_zero hq f


-- @@ L306-306 verbatim
end Real


-- @@ L308-308 verbatim
section Hoelder

-- @@ L309-310 verbatim
variable {α : Type*} {mα : MeasurableSpace α} [DiscreteMeasurableSpace α] [Finite α] [RCLike 𝕜]
  {p q : ℝ≥0} {f g : α → 𝕜}


-- @@ L312-315 expanded
lemma dLpNorm_eq_dL1Norm_rpow (hp : p ≠ 0) (f : α → 𝕜) :
    dLpNorm p f = (dLpNorm 1 fun a ↦ ‖f a‖ ^ (p : ℝ)) ^ (p⁻¹ : ℝ) :=
  by
  cases nonempty_fintype α
  simp [dLpNorm_eq_sum_norm hp, dL1Norm_eq_sum_norm, abs_rpow_of_nonneg]


-- @@ L317-322 expanded
lemma dLpNorm_rpow' {p : ℝ≥0∞} (hp₀ : p ≠ 0) (hp : p ≠ ∞) (hq : q ≠ 0) (f : α → 𝕜) :
    dLpNorm p f ^ (q : ℝ) = dLpNorm (p / q) ((fun a ↦ ‖f a‖) ^ (q : ℝ)) :=
  by
  lift p to ℝ≥0 using hp
  simp only [ne_eq, ENNReal.coe_eq_zero] at hp₀
  rw [← ENNReal.coe_div hq, dLpNorm_rpow (div_ne_zero hp₀ hq) hq (fun _ ↦ norm_nonneg _),
    dLpNorm_norm .of_discrete, ← ENNReal.coe_mul, div_mul_cancel₀ _ hq]


-- @@ L324-324 verbatim
end Hoelder


-- @@ L326-326 verbatim
section

-- @@ L327-327 verbatim
variable {α : Type*} {mα : MeasurableSpace α}


-- @@ L329-334 expanded
@[simp]
lemma RCLike.dLpNorm_coe_comp [RCLike 𝕜] (p) (f : α → ℝ) :
    dLpNorm p (((↑) : ℝ → 𝕜) ∘ f) = dLpNorm p f :=
  by
  simp only [dLpNorm, lpNorm, comp_def]
  rw! (castMode :=
    .all) [RCLike.isUniformEmbedding_ofReal.isEmbedding.aestronglyMeasurable_comp_iff]
  simp [eLpNorm, eLpNorm', eLpNormEssSup]


-- @@ L336-337 expanded
@[simp]
lemma Complex.dLpNorm_coe_comp (p) (f : α → ℝ) : dLpNorm p (((↑) : ℝ → ℂ) ∘ f) = dLpNorm p f :=
  RCLike.dLpNorm_coe_comp ..


-- @@ L339-339 verbatim
end

-- @@ L340-340 verbatim
end MeasureTheory
