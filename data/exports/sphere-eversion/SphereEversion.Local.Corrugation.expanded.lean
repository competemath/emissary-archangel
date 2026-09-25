import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import SphereEversion.ToMathlib.Algebra.Ring.Periodic
import SphereEversion.ToMathlib.MeasureTheory.BorelSpace
import SphereEversion.Loops.Basic
import SphereEversion.Local.DualPair


-- @@ L10-31 verbatim
/-! # Theillière's corrugation operation

This files introduces the fundamental calculus tool of convex integration. The version of convex
integration that we formalize is Theillière's corrugation-based convex integration.
It improves a map `f : E → F` by adding to it some corrugation map
`fun x ↦ (1/N) • ∫ t in 0..(N*π x), (γ x t - (γ x).average)` where `γ` is a family of loops in
`F` parametrized by `E` and `N` is some (very large) real number.

Under the assumption that `∀ x, (γ x).average = D f x p.v` for some dual pair `p`, this improved
map will have a derivative which is almost a value of `γ x` in direction `p.v` and almost the
derivative of `f` in direction `ker p.π`. More precisely, its derivative will be almost
`p.update (D f x) (γ x (N*p.π x))`. In addition the improved map will be very close to `f`
in C⁰ topology. All those "almost" and "very close" refer to the asymptotic behavior when `N`
is very large.

The main definition is `corrugation`. The main results are:
* `fderiv_corrugated_map` computing the difference between `D (f + corrugation p.π N γ) x` and
    `p.update (D f x) (γ x (N*p.π x)) + corrugation.remainder p.π N γ x`
* `remainder_c0_small_on` saying this difference is very small
* `corrugation.c0_small_on` saying that corrugations are C⁰-small

-/


-- @@ L33-33 verbatim
noncomputable section


-- @@ L35-35 verbatim
open Set Function Filter MeasureTheory ContinuousLinearMap

-- @@ L36-36 verbatim
open scoped Topology unitInterval


-- @@ L38-42 verbatim
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  {π : E →L[ℝ] ℝ} (N : ℝ) (γ : E → Loop F)


-- @@ L44-44 verbatim
open scoped Borelize


-- @@ L46-48 verbatim
/-- Theillière's corrugations. -/
def corrugation (π : E →L[ℝ] ℝ) (N : ℝ) (γ : E → Loop F) : E → F := fun x ↦
  (1 / N) • ∫ t in (0)..N * π x, γ x t - (γ x).average


-- @@ L50-50 verbatim
@[inherit_doc] local notation "𝒯" => corrugation π


-- @@ L52-69 verbatim
/-- The integral appearing in corrugations is periodic. -/
theorem per_corrugation (γ : Loop F) (hγ : ∀ s t, IntervalIntegrable γ volume s t) :
    OnePeriodic fun s ↦ ∫ t in (0)..s, γ t - γ.average := by
  have int_avg : ∀ s t, IntervalIntegrable (fun _ : ℝ ↦ γ.average) volume s t := fun s t ↦
    intervalIntegrable_const
  intro s
  have int₁ : IntervalIntegrable (fun t ↦ γ t - γ.average) volume 0 s := (hγ _ _).sub (int_avg _ _)
  have int₂ : IntervalIntegrable (fun t ↦ γ t - γ.average) volume s (s + 1) :=
    (hγ _ _).sub (int_avg _ _)
  have int₃ : IntervalIntegrable γ volume s (s + 1) := hγ _ _
  have int₄ : IntervalIntegrable (fun _ ↦ γ.average) volume s (s + 1) := int_avg _ _
  dsimp only
  /- Rmk: Lean doesn't want to rewrite using `intervalIntegral.integral_sub` without being
      given the integrability assumptions :-( -/
  rw [← intervalIntegral.integral_add_adjacent_intervals int₁ int₂,
    intervalIntegral.integral_sub int₃ int₄, γ.periodic.intervalIntegral_add_eq s 0, zero_add,
    Loop.average]
  simp only [add_zero, add_tsub_cancel_left, intervalIntegral.integral_const, one_smul, sub_self]


-- @@ L71-77 expanded
@[simp]
theorem corrugation_const {x : E} (h : (γ x).IsConst) : (corrugation π) N γ x = 0 :=
  by
  unfold corrugation
  rw [Loop.isConst_iff_const_avg] at h
  rw [h]
  simp only [intervalIntegral.integral_const, Loop.const_apply, Loop.average_const, smul_zero,
    sub_self]


-- @@ L79-79 verbatim
variable (π)


-- @@ L81-85 expanded
theorem corrugation.support : support ((corrugation π) N γ) ⊆ Loop.support γ := fun x x_in ↦
  by
  apply subset_closure
  intro h
  apply x_in
  simp [h]


-- @@ L87-88 verbatim
theorem corrugation_eq_zero (x) (H : x ∉ Loop.support γ) : corrugation π N γ x = 0 :=
  notMem_support.mp fun hx ↦ H (corrugation.support π N γ hx)


-- @@ L90-117 expanded
open intervalIntegral in
theorem corrugation.c0_small_on {γ : ℝ → E → Loop F} {K : Set E} (hK : IsCompact K)
    (h_le : ∀ x, ∀ t ≤ 0, γ t x = γ 0 x) (h_ge : ∀ x, ∀ t ≥ 1, γ t x = γ 1 x)
    (hγ_cont : Continuous ↿γ) {ε : ℝ} (ε_pos : 0 < ε) :
    ∀ᶠ N in atTop, ∀ x ∈ K, ∀ (t), ‖(corrugation π) N (γ t) x‖ < ε :=
  by
  set φ := fun (q : ℝ × E) t ↦ ∫ t in (0)..t, (γ q.1 q.2) t - (γ q.1 q.2).average
  have cont' : Continuous ↿φ :=
    by
    refine continuous_parametric_intervalIntegral_of_continuous ?_ continuous_snd
    refine (hγ_cont.comp₃ continuous_fst.fst.fst continuous_fst.fst.snd continuous_snd).sub ?_
    refine Loop.continuous_average ?_
    exact hγ_cont.comp₃ continuous_fst.fst.fst.fst continuous_fst.fst.fst.snd continuous_snd
  have hper : ∀ q, OnePeriodic (φ q) := fun _ ↦
    per_corrugation _ fun _ _ ↦
      (hγ_cont.comp₃ continuous_const continuous_const continuous_id).intervalIntegrable _ _
  rcases cont'.bounded_on_compact_of_onePeriodic hper ((isCompact_Icc : IsCompact I).prod hK) with
    ⟨C, hC⟩
  · apply (const_mul_one_div_lt ε_pos C).mono
    intro N hN x hx t
    rw [corrugation, norm_smul, mul_comm]
    apply (mul_le_mul_of_nonneg_right _ (norm_nonneg <| 1 / N)).trans_lt hN
    obtain (ht | ht) := le_or_gt t 0
    · rw [h_le x t ht]
      apply hC (0, x)
      simp [hx]
    · obtain (ht' | ht') := le_or_gt 1 t
      · rw [h_ge x t ht']
        apply hC (1, x)
        simp [hx]
      · exact hC (t, x) (mk_mem_prod ⟨ht.le, ht'.le⟩ hx) _


-- @@ L119-119 verbatim
variable {γ}


-- @@ L121-129 expanded
theorem corrugation.contDiff' {n : ℕ∞} {γ : G → E → Loop F} (hγ_diff : (ContDiff ℝ) n ↿γ)
    {x : H → E} (hx : (ContDiff ℝ) n x) {g : H → G} (hg : (ContDiff ℝ) n g) :
    (ContDiff ℝ) n fun h ↦ (corrugation π) N (γ <| g h) <| x h :=
  by
  apply ContDiff.const_smul
  apply contDiff_parametric_primitive_of_contDiff
  · apply ContDiff.sub
    · exact hγ_diff.comp₃ hg.fst' hx.fst' contDiff_snd
    · apply contDiff_average
      exact hγ_diff.comp₃ hg.fst'.fst' hx.fst'.fst' contDiff_snd
  · exact contDiff_const.mul (π.contDiff.comp hx)


-- @@ L131-133 expanded
theorem corrugation.contDiff [FiniteDimensional ℝ E] {n : ℕ∞} (hγ_diff : (ContDiff ℝ) n ↿γ) :
    (ContDiff ℝ) n ((corrugation π) N γ) :=
  (contDiff_parametric_primitive_of_contDiff (contDiff_sub_average hγ_diff)
        (π.contDiff.const_smul N) 0).const_smul
    _


-- @@ L135-135 verbatim
notation "∂₁" => partialFDerivFst ℝ


-- @@ L137-140 expanded
/-- The remainder appearing when differentiating a corrugation.
-/
def corrugation.remainder (π : E → ℝ) (N : ℝ) (γ : E → Loop F) : E → E →L[ℝ] F := fun x ↦
  (1 / N) • ∫ t in (0)..N * π x, (partialFDerivFst ℝ) (fun x t ↦ (γ x).normalize t) x t


-- @@ L142-142 verbatim
@[inherit_doc] local notation "R" => corrugation.remainder π


-- @@ L144-144 verbatim
variable [FiniteDimensional ℝ E]


-- @@ L146-151 expanded
theorem remainder_eq (N : ℝ) {γ : E → Loop F} (h : (ContDiff ℝ) 1 ↿γ) :
    (corrugation.remainder π) N γ = fun x ↦
      (1 / N) • ∫ t in (0)..N * π x, (Loop.diff γ x).normalize t :=
  by simp_rw [Loop.diff_normalize h];
  rfl
    -- The next lemma is a restatement of the above to emphasize that remainder is a corrugation
    -- unused


-- @@ L152-154 expanded
theorem remainder_eq_corrugation (N : ℝ) {γ : E → Loop F} (h : (ContDiff ℝ) 1 ↿γ) :
    (corrugation.remainder π) N γ = (corrugation π) N fun x ↦ Loop.diff γ x :=
  remainder_eq _ _ h


-- @@ L156-160 expanded
@[simp]
theorem remainder_eq_zero (N : ℝ) {γ : E → Loop F} (h : (ContDiff ℝ) 1 ↿γ) {x : E}
    (hx : x ∉ Loop.support γ) : (corrugation.remainder π) N γ x = 0 :=
  by
  have hx' : x ∉ Loop.support (Loop.diff γ) := fun h ↦ hx <| Loop.support_diff h
  simp [remainder_eq π N h, Loop.normalize_of_isConst (Loop.isConst_of_not_mem_support hx')]


-- @@ L162-172 expanded
theorem corrugation.fderiv_eq {N : ℝ} (hN : N ≠ 0) (hγ_diff : (ContDiff ℝ) 1 ↿γ) :
    (fderiv ℝ) ((corrugation π) N γ) = fun x : E ↦
      (ContinuousLinearMap.comp
          (ContinuousLinearMap.toSpanSingleton ℝ (γ x (N * π x) - (γ x).average)) π) +
        (corrugation.remainder π) N γ x :=
  by
  ext1 x₀
  have hπ_diff : (ContDiff ℝ) 1 π := π.contDiff
  have diff := contDiff_sub_average hγ_diff
  have key := (hasFDerivAt_parametric_primitive_of_contDiff' diff (hπ_diff.const_smul N) x₀ 0).2
  erw [fderiv_const_smul key.differentiableAt, key.fderiv, smul_add, add_comm]
  congr 1
  rw [fderiv_fun_const_smul (hπ_diff.differentiable (by simp)).differentiableAt N, π.fderiv]
  simp only [smul_smul, inv_mul_cancel₀ hN, one_div, smul_eq_mul, one_smul,
    ContinuousLinearMap.comp_smul]


-- @@ L174-177 expanded
theorem corrugation.fderiv_apply (hN : N ≠ 0) (hγ_diff : (ContDiff ℝ) 1 ↿γ) (x v : E) :
    (fderiv ℝ) ((corrugation π) N γ) x v =
      π v • (γ x (N * π x) - (γ x).average) + (corrugation.remainder π) N γ x v :=
  by
  simp only [corrugation.fderiv_eq _ hN hγ_diff, toSpanSingleton_apply, add_apply,
    ContinuousLinearMap.comp_apply]


-- @@ L179-187 expanded
theorem fderiv_corrugated_map (hN : N ≠ 0) (hγ_diff : (ContDiff ℝ) 1 ↿γ) {f : E → F}
    (hf : (ContDiff ℝ) 1 f) (p : DualPair E) {x} (hfγ : (γ x).average = (fderiv ℝ) f x p.v) :
    (fderiv ℝ) (f + corrugation p.π N γ) x =
      p.update ((fderiv ℝ) f x) (γ x (N * p.π x)) + corrugation.remainder p.π N γ x :=
  by
  ext v
  erw [fderiv_add (hf.differentiable (by simp)).differentiableAt
      ((corrugation.contDiff _ N hγ_diff).differentiable (by simp)).differentiableAt]
  simp_rw [add_apply, corrugation.fderiv_apply _ N hN hγ_diff, hfγ, DualPair.update, add_apply,
    p.π.comp_toSpanSingleton_apply, add_assoc]


-- @@ L189-189 verbatim
open scoped ContDiff


-- @@ L191-202 expanded
theorem Remainder.smooth {γ : G → E → Loop F} (hγ_diff : (ContDiff ℝ) ∞ ↿γ) {x : H → E}
    (hx : (ContDiff ℝ) ∞ x) {g : H → G} (hg : (ContDiff ℝ) ∞ g) :
    (ContDiff ℝ) ∞ fun h ↦ (corrugation.remainder π) N (γ <| g h) <| x h :=
  by
  apply ContDiff.const_smul
  apply contDiff_parametric_primitive_of_contDiff
  · let ψ : E → H × ℝ → F := fun x q ↦ (γ (g q.1) x).normalize q.2
    change (ContDiff ℝ) ∞ fun q : H × ℝ ↦ (partialFDerivFst ℝ) ψ (x q.1) (q.1, q.2)
    refine (ContDiff.contDiff_top_partial_fst ?_).comp₂ hx.fst' (contDiff_fst.prodMk contDiff_snd)
    apply ContDiff.sub
    · apply hγ_diff.comp₃ hg.fst'.snd' contDiff_fst contDiff_snd.snd
    · apply contDiff_average
      exact hγ_diff.comp₃ hg.fst'.snd'.fst' contDiff_fst.fst' contDiff_snd
  · exact contDiff_const.mul (π.contDiff.comp hx)


-- @@ L204-214 expanded
set_option linter.style.multiGoal false in
theorem remainder_c0_small_on {K : Set E} (hK : IsCompact K) (hγ_diff : (ContDiff ℝ) 1 ↿γ) {ε : ℝ}
    (ε_pos : 0 < ε) : ∀ᶠ N in atTop, ∀ x ∈ K, ‖(corrugation.remainder π) N γ x‖ < ε :=
  by
  simp_rw [fun N ↦ remainder_eq π N hγ_diff]
  let g : ℝ → E → Loop (E →L[ℝ] F) := fun _ ↦ Loop.diff γ
  have g_le : ∀ (x) (t : ℝ), t ≤ 0 → g t x = g 0 x := fun _ _ _ ↦ rfl
  have g_ge : ∀ (x) (t : ℝ), t ≥ 1 → g t x = g 1 x := fun _ _ _ ↦ rfl
  have g_cont : Continuous ↿g := (Loop.continuous_diff hγ_diff).snd'
  apply (corrugation.c0_small_on _ hK g_le g_ge g_cont ε_pos).mono
  intro N H x x_in
  exact H x x_in 0

