import Mathlib
import Submission.MorseLemma2D


-- @@ L4-24 verbatim
/-!
# Globalizing a local two-dimensional Morse parameter

The useful construction in this file is a bump-supported extension of a local
Morse parameter.  There is one subtlety in the current Mathlib definition:

`ContDiffAt ℝ ∞ f 0` means that for every finite order there is a (possibly
order-dependent) neighborhood on which that order is available.  It does not
imply the existence of one neighborhood on which `f` is `C^∞`.  Consequently:

* a genuine global `C^∞` extension is constructed from the minimal uniform
  hypothesis `ContDiffOn ℝ ∞ f U` for some `U ∈ 𝓝 0`;
* `ContDiffAt ℝ ω f 0` supplies that hypothesis automatically;
* the existing `LocalMorseNormalForm.param_contDiffAt : ContDiffAt ℝ ∞ ...`
  supplies a global extension of every prescribed finite differentiability
  order.

The output contains a shrunk positive radius, exact agreement on its ball, and
the same literal Morse quadratic equation.  It can itself be converted back to
a `LocalMorseNormalForm` whose parameter is globally smooth.
-/


-- @@ L26-26 verbatim
noncomputable section


-- @@ L28-28 verbatim
open Set Function Filter Metric

-- @@ L29-29 verbatim
open scoped RealInnerProductSpace ContDiff Topology


-- @@ L31-31 verbatim
namespace Submission


-- @@ L33-33 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)


-- @@ L35-48 verbatim
/-- A global parameter agreeing with a local Morse parameter on a smaller ball.
The differentiability order is explicit so that the construction can record
the strongest conclusion justified by the local hypothesis. -/
structure MorseParamGlobalizationOfOrder {f : E₂ → ℝ}
    (M : LocalMorseNormalForm f) (k : ℕ∞ω) where
  radius : ℝ
  radius_pos : 0 < radius
  radius_le : radius ≤ M.radius
  globalParam : E₂ → E₂
  globalParam_contDiff : ContDiff ℝ k globalParam
  agrees : ∀ u, ‖u‖ < radius → globalParam u = M.param u
  param_zero : globalParam 0 = 0
  exact : ∀ u, ‖u‖ < radius →
    f (globalParam u) = f 0 + morseQuadratic M.index (u 0, u 1)


-- @@ L50-52 verbatim
/-- The `C^∞` output used by the signed Morse-position construction. -/
abbrev MorseParamGlobalization {f : E₂ → ℝ} (M : LocalMorseNormalForm f) :=
  MorseParamGlobalizationOfOrder M ∞


-- @@ L54-54 verbatim
namespace MorseParamGlobalizationOfOrder


-- @@ L56-56 verbatim
variable {f : E₂ → ℝ} {M : LocalMorseNormalForm f} {k : ℕ∞ω}


-- @@ L58-68 verbatim
/-- Regard a `C^∞` globalization as a new local normal form.  Its radius is the
safe shrunken radius and its parameter is smooth on the whole plane. -/
def toLocalMorseNormalForm (Q : MorseParamGlobalization M) :
    LocalMorseNormalForm f where
  index := M.index
  radius := Q.radius
  radius_pos := Q.radius_pos
  param := Q.globalParam
  param_zero := Q.param_zero
  param_contDiffAt := Q.globalParam_contDiff.contDiffAt
  exact := Q.exact


-- @@ L70-71 verbatim
@[simp] theorem toLocalMorseNormalForm_index (Q : MorseParamGlobalization M) :
    Q.toLocalMorseNormalForm.index = M.index := rfl


-- @@ L73-74 verbatim
@[simp] theorem toLocalMorseNormalForm_param (Q : MorseParamGlobalization M) :
    Q.toLocalMorseNormalForm.param = Q.globalParam := rfl


-- @@ L76-76 verbatim
end MorseParamGlobalizationOfOrder


-- @@ L78-78 verbatim
/-! ## The bump extension -/


-- @@ L80-162 verbatim
/-- A uniform local `C^k` neighborhood gives a global `C^k` extension which is
identical to the Morse parameter on a smaller positive-radius ball. -/
theorem exists_morseParamGlobalizationOfOrder_of_contDiffOn
    {f : E₂ → ℝ} (M : LocalMorseNormalForm f) {k : ℕ∞ω}
    {U : Set E₂} (hU : U ∈ 𝓝 (0 : E₂))
    (hparam : ContDiffOn ℝ k M.param U) (hk : k ≤ ∞) :
    Nonempty (MorseParamGlobalizationOfOrder M k) := by
  classical
  obtain ⟨V, hVU, hVopen, h0V⟩ :
      ∃ V : Set E₂, V ⊆ U ∧ IsOpen V ∧ (0 : E₂) ∈ V :=
    mem_nhds_iff.mp hU
  have hVnhds : V ∈ 𝓝 (0 : E₂) := hVopen.mem_nhds h0V
  obtain ⟨d, hd, hball⟩ := Metric.mem_nhds_iff.mp hVnhds
  let bump : ContDiffBump (0 : E₂) :=
    { rIn := d / 4
      rOut := d / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  let globalParam : E₂ → E₂ := fun u =>
    if u ∈ V then bump u • M.param u else 0
  have hparamV : ContDiffOn ℝ k M.param V := hparam.mono hVU
  have htsupport : tsupport (bump : E₂ → ℝ) ⊆ V := by
    rw [bump.tsupport_eq]
    intro x hx
    apply hball
    rw [mem_closedBall] at hx
    rw [mem_ball]
    change dist x 0 ≤ d / 2 at hx
    linarith
  have hglobal : ContDiff ℝ k globalParam := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hxV : x ∈ V
    · have hpAt : ContDiffAt ℝ k M.param x :=
        (hparamV x hxV).contDiffAt (hVopen.mem_nhds hxV)
      have hbAt : ContDiffAt ℝ ∞ (bump : E₂ → ℝ) x := bump.contDiffAt
      have hprod : ContDiffAt ℝ k (fun y => bump y • M.param y) x :=
        (hbAt.of_le hk).smul hpAt
      apply hprod.congr_of_eventuallyEq
      filter_upwards [hVopen.mem_nhds hxV] with y hy
      simp [globalParam, hy]
    · have hxTs : x ∉ tsupport (bump : E₂ → ℝ) :=
        fun hx => hxV (htsupport hx)
      have houtside : (tsupport (bump : E₂ → ℝ))ᶜ ∈ 𝓝 x :=
        isClosed_closure.isOpen_compl.mem_nhds hxTs
      have heqzero : globalParam =ᶠ[𝓝 x] (fun _ : E₂ => 0) := by
        filter_upwards [houtside] with y hy
        have hbzero : bump y = 0 := by
          by_contra hb
          exact hy (subset_tsupport (bump : E₂ → ℝ) hb)
        by_cases hyV : y ∈ V <;> simp [globalParam, hyV, hbzero]
      exact (contDiff_const : ContDiff ℝ k (fun _ : E₂ => (0 : E₂))).contDiffAt
        |>.congr_of_eventuallyEq heqzero
  let r : ℝ := min (d / 4) M.radius
  have hr : 0 < r := lt_min (by positivity) M.radius_pos
  have hrle : r ≤ M.radius := min_le_right _ _
  have hagree : ∀ u : E₂, ‖u‖ < r → globalParam u = M.param u := by
    intro u hu
    have hurIn : ‖u‖ ≤ d / 4 :=
      (hu.trans_le (min_le_left _ _)).le
    have huV : u ∈ V := by
      apply hball
      rw [mem_ball, dist_zero_right]
      exact hurIn.trans_lt (by linarith)
    have hbump : bump u = 1 := by
      apply bump.one_of_mem_closedBall
      rw [mem_closedBall, dist_zero_right]
      exact hurIn
    simp [globalParam, huV, hbump]
  refine ⟨{
    radius := r
    radius_pos := hr
    radius_le := hrle
    globalParam := globalParam
    globalParam_contDiff := hglobal
    agrees := hagree
    param_zero := ?_
    exact := ?_ }⟩
  · rw [hagree 0 (by simpa using hr)]
    exact M.param_zero
  · intro u hu
    rw [hagree u hu]
    exact M.exact u (hu.trans_le hrle)


-- @@ L164-164 verbatim
/-! ## Consequences at infinite and finite order -/


-- @@ L166-173 verbatim
/-- Minimal uniform-neighborhood assumption for a genuine global smooth
parameter. -/
theorem exists_morseParamGlobalization_of_contDiffOn
    {f : E₂ → ℝ} (M : LocalMorseNormalForm f)
    {U : Set E₂} (hU : U ∈ 𝓝 (0 : E₂))
    (hparam : ContDiffOn ℝ ∞ M.param U) :
    Nonempty (MorseParamGlobalization M) :=
  exists_morseParamGlobalizationOfOrder_of_contDiffOn M hU hparam (by simp)


-- @@ L175-183 verbatim
/-- Analytic smoothness at the origin supplies one uniform `C^∞` neighborhood,
so no additional neighborhood hypothesis is needed. -/
theorem exists_morseParamGlobalization_of_contDiffAt_omega
    {f : E₂ → ℝ} (M : LocalMorseNormalForm f)
    (hparam : ContDiffAt ℝ ω M.param 0) :
    Nonempty (MorseParamGlobalization M) := by
  obtain ⟨U, hU, hUparam⟩ :=
    hparam.contDiffOn (m := (∞ : ℕ∞ω)) (by simp) (by simp)
  exact exists_morseParamGlobalization_of_contDiffOn M hU hUparam


-- @@ L185-194 verbatim
/-- The existing `param_contDiffAt : ContDiffAt ℝ ∞` is sufficient for a
global extension at every prescribed finite order. -/
theorem exists_morseParamGlobalization_finiteOrder
    {f : E₂ → ℝ} (M : LocalMorseNormalForm f) (k : ℕ) :
    Nonempty (MorseParamGlobalizationOfOrder M (k : ℕ∞ω)) := by
  have hk : ContDiffAt ℝ (k : ℕ∞ω) M.param 0 :=
    contDiffAt_infty.mp M.param_contDiffAt k
  obtain ⟨U, hU, hUparam⟩ := hk.contDiffOn le_rfl (by simp)
  exact exists_morseParamGlobalizationOfOrder_of_contDiffOn M hU hUparam
    (ENat.LEInfty.out : (k : ℕ∞ω) ≤ ∞)


-- @@ L196-196 verbatim
end Submission
