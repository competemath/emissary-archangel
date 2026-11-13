import Mathlib
import Submission.MorseGenericity2D
import Submission.MorseLemma2D


-- @@ L5-13 verbatim
/-!
# Shrinking local Morse normal forms

This file packages the elementary, but repeatedly needed, operation of
shrinking the radius of a `LocalMorseNormalForm`.  Continuity of the local
inverse parameter then lets one choose a single smaller radius satisfying
finitely many parameter-space and lifted ambient-space neighborhood
conditions.
-/


-- @@ L15-15 verbatim
noncomputable section


-- @@ L17-17 verbatim
open Set Function Metric Filter

-- @@ L18-18 verbatim
open scoped RealInnerProductSpace ContDiff Topology


-- @@ L20-20 verbatim
namespace Submission


-- @@ L22-22 verbatim
variable {n : ℕ}


-- @@ L24-24 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

-- @@ L25-25 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))


-- @@ L27-27 verbatim
namespace LocalMorseNormalForm


-- @@ L29-29 verbatim
variable {f : E₂ → ℝ} (M : LocalMorseNormalForm f)


-- @@ L31-31 verbatim
/-! ## Radius restriction -/


-- @@ L33-43 verbatim
/-- Restrict a local normal form to a smaller positive radius.  Its index and
parameter map are unchanged definitionally. -/
def shrink (r : ℝ) (hr : 0 < r) (hrM : r ≤ M.radius) :
    LocalMorseNormalForm f where
  index := M.index
  radius := r
  radius_pos := hr
  param := M.param
  param_zero := M.param_zero
  param_contDiffAt := M.param_contDiffAt
  exact u hu := M.exact u (hu.trans_le hrM)


-- @@ L45-46 verbatim
@[simp] theorem shrink_index (r : ℝ) (hr : 0 < r) (hrM : r ≤ M.radius) :
    (M.shrink r hr hrM).index = M.index := rfl


-- @@ L48-49 verbatim
@[simp] theorem shrink_radius (r : ℝ) (hr : 0 < r) (hrM : r ≤ M.radius) :
    (M.shrink r hr hrM).radius = r := rfl


-- @@ L51-52 verbatim
@[simp] theorem shrink_param (r : ℝ) (hr : 0 < r) (hrM : r ≤ M.radius) :
    (M.shrink r hr hrM).param = M.param := rfl


-- @@ L54-56 verbatim
@[simp] theorem shrink_param_zero (r : ℝ) (hr : 0 < r)
    (hrM : r ≤ M.radius) :
    (M.shrink r hr hrM).param 0 = 0 := M.param_zero


-- @@ L58-62 verbatim
theorem shrink_exact (r : ℝ) (hr : 0 < r) (hrM : r ≤ M.radius)
    (u : E₂) (hu : ‖u‖ < r) :
    f ((M.shrink r hr hrM).param u) =
      f 0 + morseQuadratic (M.shrink r hr hrM).index (u 0, u 1) :=
  (M.shrink r hr hrM).exact u hu


-- @@ L64-64 verbatim
/-! ## One neighborhood -/


-- @@ L66-67 verbatim
theorem param_continuousAt : ContinuousAt M.param 0 :=
  M.param_contDiffAt.continuousAt


-- @@ L69-72 verbatim
theorem param_tendsto_zero : Tendsto M.param (nhds 0) (nhds 0) := by
  have h := M.param_continuousAt
  change Tendsto M.param (nhds 0) (nhds (M.param 0)) at h
  simpa only [M.param_zero] using h


-- @@ L74-86 verbatim
/-- Every neighborhood of zero contains the image of a sufficiently small
normal-form ball, with the new radius still bounded by the original one. -/
theorem exists_radius_param_mem {U : Set E₂} (hU : U ∈ nhds (0 : E₂)) :
    ∃ r > 0, r ≤ M.radius ∧ ∀ u : E₂, ‖u‖ < r → M.param u ∈ U := by
  have hpre : M.param ⁻¹' U ∈ nhds (0 : E₂) := M.param_tendsto_zero hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
  let r := min ε M.radius
  have hr : 0 < r := lt_min hε M.radius_pos
  refine ⟨r, hr, min_le_right _ _, ?_⟩
  intro u hu
  apply hball
  rw [mem_ball, dist_zero_right]
  exact hu.trans_le (min_le_left _ _)


-- @@ L88-95 verbatim
/-- The preceding radius can be returned already packaged as a restricted
normal form. -/
theorem exists_shrink_param_mem {U : Set E₂} (hU : U ∈ nhds (0 : E₂)) :
    ∃ r, ∃ hr : 0 < r, ∃ hrM : r ≤ M.radius,
      ∀ u : E₂, ‖u‖ < (M.shrink r hr hrM).radius →
        (M.shrink r hr hrM).param u ∈ U := by
  obtain ⟨r, hr, hrM, hmem⟩ := M.exists_radius_param_mem hU
  exact ⟨r, hr, hrM, hmem⟩


-- @@ L97-113 verbatim
/-- Although `ContDiffAt ℝ ∞` need not provide one neighborhood that works
uniformly for every finite order, it does provide such a neighborhood for each
fixed finite order.  Shrinking turns that neighborhood into a ball. -/
theorem exists_radius_param_contDiffOn (k : ℕ) :
    ∃ r > 0, r ≤ M.radius ∧
      ContDiffOn ℝ (k : ℕ∞ω) M.param (ball (0 : E₂) r) := by
  have hk : ContDiffAt ℝ (k : ℕ∞ω) M.param 0 :=
    contDiffAt_infty.mp M.param_contDiffAt k
  obtain ⟨U, hU, hparam⟩ := hk.contDiffOn le_rfl (by simp)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  let r := min ε M.radius
  have hr : 0 < r := lt_min hε M.radius_pos
  refine ⟨r, hr, min_le_right _ _, hparam.mono ?_⟩
  intro u hu
  apply hball
  rw [mem_ball] at hu ⊢
  exact hu.trans_le (min_le_left _ _)


-- @@ L115-115 verbatim
/-! ## Critical points of the exact quadratic model -/


-- @@ L117-139 verbatim
/-- Local copy of the scalar-adjoint argument: a zero Euclidean gradient has
zero Fréchet differential.  Kept private to avoid adding a dependency on the
later nondegeneracy bridge module. -/
private theorem fderiv_eq_zero_of_chartGradient_eq_zero_local
    {g : E₂ → ℝ} {p : E₂} (hgrad : chartGradient g p = 0) :
    fderiv ℝ g p = 0 := by
  let A : E₂ →L[ℝ] ℝ := fderiv ℝ g p
  have hA1 : ContinuousLinearMap.adjoint A 1 = 0 := by
    simpa [chartGradient, scalarAdjointCLM, A] using hgrad
  have hAadj : ContinuousLinearMap.adjoint A = 0 := by
    apply ContinuousLinearMap.ext
    intro r
    calc
      ContinuousLinearMap.adjoint A r =
          r • ContinuousLinearMap.adjoint A 1 := by
        rw [← map_smul]
        simp
      _ = 0 := by rw [hA1, smul_zero]
  apply ContinuousLinearMap.ext
  intro v
  have hinner := ContinuousLinearMap.adjoint_inner_left A v (1 : ℝ)
  rw [hAadj] at hinner
  simpa [A] using hinner.symm


-- @@ L141-206 verbatim
/-- The differential of a constant plus any of the three Morse quadratic
models vanishes only at the origin. -/
theorem eq_zero_of_fderiv_const_add_morseQuadratic_eq_zero
    (e : MorseIndexTwo) (c : ℝ) (u : E₂)
    (hzero : fderiv ℝ
      (fun z : E₂ => c + morseQuadratic e (z 0, z 1)) u = 0) :
    u = 0 := by
  let p0 : E₂ →L[ℝ] ℝ := EuclideanSpace.proj 0
  let p1 : E₂ →L[ℝ] ℝ := EuclideanSpace.proj 1
  have hp0 : HasFDerivAt (fun z : E₂ => z 0) p0 u := by
    simpa [p0] using (p0.hasFDerivAt : HasFDerivAt p0 p0 u)
  have hp1 : HasFDerivAt (fun z : E₂ => z 1) p1 u := by
    simpa [p1] using (p1.hasFDerivAt : HasFDerivAt p1 p1 u)
  have hs0 := hp0.mul hp0
  have hs1 := hp1.mul hp1
  have hc : HasFDerivAt (fun _ : E₂ => c) (0 : E₂ →L[ℝ] ℝ) u :=
    hasFDerivAt_const c u
  cases e with
  | minimum =>
      simp only [morseQuadratic, pow_two] at hzero
      have hmodel := hc.add (hs0.add hs1)
      have hfd := hmodel.fderiv
      change fderiv ℝ
        (fun z : E₂ => c + (z 0 * z 0 + z 1 * z 1)) u = _ at hfd
      have h0 := congrArg
        (fun L : E₂ →L[ℝ] ℝ => L (EuclideanSpace.single 0 1)) hzero
      have h1 := congrArg
        (fun L : E₂ →L[ℝ] ℝ => L (EuclideanSpace.single 1 1)) hzero
      rw [hfd] at h0 h1
      simp [p0, p1] at h0 h1
      ext i
      fin_cases i
      · simpa using h0
      · simpa using h1
  | saddle =>
      simp only [morseQuadratic, pow_two] at hzero
      have hmodel := hc.add (hs0.sub hs1)
      have hfd := hmodel.fderiv
      change fderiv ℝ
        (fun z : E₂ => c + (z 0 * z 0 - z 1 * z 1)) u = _ at hfd
      have h0 := congrArg
        (fun L : E₂ →L[ℝ] ℝ => L (EuclideanSpace.single 0 1)) hzero
      have h1 := congrArg
        (fun L : E₂ →L[ℝ] ℝ => L (EuclideanSpace.single 1 1)) hzero
      rw [hfd] at h0 h1
      simp [p0, p1] at h0 h1
      ext i
      fin_cases i
      · simpa using h0
      · simpa using h1
  | maximum =>
      simp only [morseQuadratic, pow_two] at hzero
      have hmodel := hc.add (hs0.neg.sub hs1)
      have hfd := hmodel.fderiv
      change fderiv ℝ
        (fun z : E₂ => c + (-(z 0 * z 0) - z 1 * z 1)) u = _ at hfd
      have h0 := congrArg
        (fun L : E₂ →L[ℝ] ℝ => L (EuclideanSpace.single 0 1)) hzero
      have h1 := congrArg
        (fun L : E₂ →L[ℝ] ℝ => L (EuclideanSpace.single 1 1)) hzero
      rw [hfd] at h0 h1
      simp [p0, p1] at h0 h1
      ext i
      fin_cases i
      · simpa using h0
      · simpa using h1


-- @@ L208-246 verbatim
/-- On a ball where the normal-form parameter is differentiable, the exact
Morse identity rules out every shifted chart-critical point except the center.
The reverse implication uses the recorded criticality of the center. -/
theorem chartGradient_shifted_param_eq_zero_iff
    {g : E₂ → ℝ} {base : E₂}
    (M : LocalMorseNormalForm (recenter g base))
    (hg : Differentiable ℝ g)
    (hcrit : chartGradient g base = 0)
    (r : ℝ) (hrM : r ≤ M.radius)
    (hparam : ∀ z : E₂, ‖z‖ < r → DifferentiableAt ℝ M.param z)
    (u : E₂) (hu : ‖u‖ < r) :
    chartGradient g (base + M.param u) = 0 ↔ u = 0 := by
  constructor
  · intro hgrad
    have hfdg : fderiv ℝ g (base + M.param u) = 0 :=
      fderiv_eq_zero_of_chartGradient_eq_zero_local hgrad
    have hinner : DifferentiableAt ℝ (fun z : E₂ => base + M.param z) u :=
      ((hasFDerivAt_const base u).add (hparam u hu).hasFDerivAt).differentiableAt
    have hcomp := (hg (base + M.param u)).hasFDerivAt.comp u hinner.hasFDerivAt
    have hleft : fderiv ℝ (fun z : E₂ => g (base + M.param z)) u = 0 := by
      change fderiv ℝ (g ∘ fun z : E₂ => base + M.param z) u = 0
      rw [hcomp.fderiv, hfdg]
      simp
    have huball : u ∈ ball (0 : E₂) r := by
      simpa [mem_ball, dist_zero_right]
    have heq : (fun z : E₂ => g (base + M.param z)) =ᶠ[nhds u]
        (fun z : E₂ => g base + morseQuadratic M.index (z 0, z 1)) := by
      filter_upwards [isOpen_ball.mem_nhds huball] with z hz
      have hzr : ‖z‖ < r := by
        simpa [mem_ball, dist_zero_right] using hz
      simpa [recenter] using M.exact z (hzr.trans_le hrM)
    have hright : fderiv ℝ
        (fun z : E₂ => g base + morseQuadratic M.index (z 0, z 1)) u = 0 := by
      rw [← heq.fderiv_eq]
      exact hleft
    exact eq_zero_of_fderiv_const_add_morseQuadratic_eq_zero
      M.index (g base) u hright
  · rintro rfl
    simpa [M.param_zero] using hcrit


-- @@ L248-248 verbatim
/-! ## Simultaneous finite neighborhood control -/


-- @@ L250-261 verbatim
/-- One radius controlling finitely many neighborhoods of the shifted
parameter and finitely many neighborhoods after a continuous lift. -/
structure SimultaneousShrink
    {A : Type*} [TopologicalSpace A]
    (base : E₂) (surface : E₂ → A)
    {ι κ : Type*} (parameterSet : ι → Set E₂) (liftedSet : κ → Set A) where
  radius : ℝ
  radius_pos : 0 < radius
  radius_le : radius ≤ M.radius
  shifted_mem : ∀ i u, ‖u‖ < radius → base + M.param u ∈ parameterSet i
  lifted_mem : ∀ j u, ‖u‖ < radius →
    surface (base + M.param u) ∈ liftedSet j


-- @@ L263-263 verbatim
namespace SimultaneousShrink


-- @@ L265-267 verbatim
variable {A : Type*} [TopologicalSpace A]
  {base : E₂} {surface : E₂ → A}
  {ι κ : Type*} {parameterSet : ι → Set E₂} {liftedSet : κ → Set A}


-- @@ L269-272 verbatim
/-- The normal form restricted to the simultaneous-control radius. -/
def normalForm (S : M.SimultaneousShrink base surface parameterSet liftedSet) :
    LocalMorseNormalForm f :=
  M.shrink S.radius S.radius_pos S.radius_le


-- @@ L274-276 verbatim
@[simp] theorem normalForm_index
    (S : M.SimultaneousShrink base surface parameterSet liftedSet) :
    S.normalForm.index = M.index := rfl


-- @@ L278-280 verbatim
@[simp] theorem normalForm_radius
    (S : M.SimultaneousShrink base surface parameterSet liftedSet) :
    S.normalForm.radius = S.radius := rfl


-- @@ L282-284 verbatim
@[simp] theorem normalForm_param
    (S : M.SimultaneousShrink base surface parameterSet liftedSet) :
    S.normalForm.param = M.param := rfl


-- @@ L286-294 verbatim
/-- Restrict a simultaneous-control package to a smaller positive radius. -/
def shrink (S : M.SimultaneousShrink base surface parameterSet liftedSet)
    (r : ℝ) (hr : 0 < r) (hrS : r ≤ S.radius) :
    M.SimultaneousShrink base surface parameterSet liftedSet where
  radius := r
  radius_pos := hr
  radius_le := hrS.trans S.radius_le
  shifted_mem i u hu := S.shifted_mem i u (hu.trans_le hrS)
  lifted_mem j u hu := S.lifted_mem j u (hu.trans_le hrS)


-- @@ L296-299 verbatim
@[simp] theorem shrink_radius
    (S : M.SimultaneousShrink base surface parameterSet liftedSet)
    (r : ℝ) (hr : 0 < r) (hrS : r ≤ S.radius) :
    (shrink M S r hr hrS).radius = r := rfl


-- @@ L301-312 verbatim
/-- `C¹` control on the open shrink ball supplies ordinary differentiability at
each point of that ball. -/
theorem param_differentiableAt_of_contDiffOn_one
    (S : M.SimultaneousShrink base surface parameterSet liftedSet)
    (hparam : ContDiffOn ℝ (1 : ℕ∞ω) M.param
      (ball (0 : E₂) S.radius))
    (u : E₂) (hu : ‖u‖ < S.radius) :
    DifferentiableAt ℝ M.param u := by
  have huball : u ∈ ball (0 : E₂) S.radius := by
    simpa [mem_ball, dist_zero_right]
  exact ((hparam u huball).contDiffAt
    (isOpen_ball.mem_nhds huball)).differentiableAt_one


-- @@ L314-329 verbatim
/-- The critical-point uniqueness theorem, specialized to a simultaneous
shrink carrying `C¹` control. -/
theorem chartGradient_shifted_param_eq_zero_iff_of_contDiffOn_one
    {g : E₂ → ℝ} {center : E₂}
    (N : LocalMorseNormalForm (recenter g center))
    {B : Type*} [TopologicalSpace B] {surface' : E₂ → B}
    {ι' κ' : Type*} {parameterSet' : ι' → Set E₂}
    {liftedSet' : κ' → Set B}
    (S : N.SimultaneousShrink center surface' parameterSet' liftedSet')
    (hg : Differentiable ℝ g) (hcrit : chartGradient g center = 0)
    (hparam : ContDiffOn ℝ (1 : ℕ∞ω) N.param
      (ball (0 : E₂) S.radius))
    (u : E₂) (hu : ‖u‖ < S.radius) :
    chartGradient g (center + N.param u) = 0 ↔ u = 0 :=
  N.chartGradient_shifted_param_eq_zero_iff hg hcrit S.radius S.radius_le
    (fun z hz => param_differentiableAt_of_contDiffOn_one N S hparam z hz) u hu


-- @@ L331-331 verbatim
end SimultaneousShrink


-- @@ L333-375 verbatim
/-- Finite families of neighborhoods can all be met after one radius shrink. -/
theorem nonempty_simultaneousShrink
    {A : Type*} [TopologicalSpace A]
    (base : E₂) (surface : E₂ → A) (hsurface : ContinuousAt surface base)
    {ι κ : Type*} [Finite ι] [Finite κ]
    (parameterSet : ι → Set E₂) (liftedSet : κ → Set A)
    (hparameter : ∀ i, parameterSet i ∈ nhds base)
    (hlifted : ∀ j, liftedSet j ∈ nhds (surface base)) :
    Nonempty (M.SimultaneousShrink base surface parameterSet liftedSet) := by
  let shifted : E₂ → E₂ := fun u => base + M.param u
  have hshift : Tendsto shifted (nhds (0 : E₂)) (nhds base) := by
    have hc : ContinuousAt shifted 0 :=
      continuousAt_const.add M.param_continuousAt
    change Tendsto shifted (nhds 0) (nhds (shifted 0)) at hc
    simpa only [shifted, M.param_zero, add_zero] using hc
  have hlift : Tendsto (fun u => surface (shifted u)) (nhds (0 : E₂))
      (nhds (surface base)) := by
    have hs : Tendsto surface (nhds base) (nhds (surface base)) := hsurface
    simpa [Function.comp_def] using hs.comp hshift
  have hparameterAll : ∀ᶠ u in nhds (0 : E₂), ∀ i, shifted u ∈ parameterSet i :=
    Filter.eventually_all.mpr fun i => hshift (hparameter i)
  have hliftedAll : ∀ᶠ u in nhds (0 : E₂), ∀ j, surface (shifted u) ∈ liftedSet j :=
    Filter.eventually_all.mpr fun j => hlift (hlifted j)
  have hboth : {u : E₂ | (∀ i, shifted u ∈ parameterSet i) ∧
      (∀ j, surface (shifted u) ∈ liftedSet j)} ∈ nhds (0 : E₂) :=
    hparameterAll.and hliftedAll
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hboth
  let r := min ε M.radius
  have hr : 0 < r := lt_min hε M.radius_pos
  refine ⟨{
    radius := r
    radius_pos := hr
    radius_le := min_le_right _ _
    shifted_mem := ?_
    lifted_mem := ?_ }⟩
  · intro i u hu
    exact (hball (by
      rw [mem_ball, dist_zero_right]
      exact hu.trans_le (min_le_left _ _))).1 i
  · intro j u hu
    exact (hball (by
      rw [mem_ball, dist_zero_right]
      exact hu.trans_le (min_le_left _ _))).2 j


-- @@ L377-398 verbatim
/-- The common radius can additionally be chosen so that the parameter map is
`C^k` on the entire resulting ball. -/
theorem exists_simultaneousShrink_contDiffOn
    {A : Type*} [TopologicalSpace A]
    (k : ℕ) (base : E₂) (surface : E₂ → A)
    (hsurface : ContinuousAt surface base)
    {ι κ : Type*} [Finite ι] [Finite κ]
    (parameterSet : ι → Set E₂) (liftedSet : κ → Set A)
    (hparameter : ∀ i, parameterSet i ∈ nhds base)
    (hlifted : ∀ j, liftedSet j ∈ nhds (surface base)) :
    ∃ S : M.SimultaneousShrink base surface parameterSet liftedSet,
      ContDiffOn ℝ (k : ℕ∞ω) M.param (ball (0 : E₂) S.radius) := by
  obtain ⟨S₀⟩ := M.nonempty_simultaneousShrink base surface hsurface
    parameterSet liftedSet hparameter hlifted
  obtain ⟨r, hr, hrM, hsmooth⟩ := M.exists_radius_param_contDiffOn k
  let r' := min S₀.radius r
  have hr' : 0 < r' := lt_min S₀.radius_pos hr
  let S := SimultaneousShrink.shrink M S₀ r' hr' (min_le_left _ _)
  refine ⟨S, hsmooth.mono ?_⟩
  intro u hu
  rw [mem_ball] at hu ⊢
  exact hu.trans_le (min_le_right _ _)


-- @@ L400-400 verbatim
/-! ## IFT chart and cutoff-core specializations -/


-- @@ L402-407 verbatim
/-- Simultaneous control of one IFT chart domain and one ambient
neighborhood. -/
abbrev IFTChartShrink {C : FramedLevelCobordism n}
    (P : IFTSurfaceChart C) (base : E₂) (ambient : Set E') :=
  M.SimultaneousShrink base P.param
    (fun _ : Unit => P.domain) (fun _ : Unit => ambient)


-- @@ L409-416 verbatim
theorem nonempty_iftChartShrink {C : FramedLevelCobordism n}
    (P : IFTSurfaceChart C) (base : E₂) (ambient : Set E')
    (hdomain : P.domain ∈ nhds base)
    (hambient : ambient ∈ nhds (P.param base)) :
    Nonempty (M.IFTChartShrink P base ambient) := by
  exact M.nonempty_simultaneousShrink base P.param P.param_smooth.continuous.continuousAt
    (fun _ : Unit => P.domain) (fun _ : Unit => ambient)
    (fun _ => hdomain) (fun _ => hambient)


-- @@ L418-424 verbatim
theorem nonempty_iftChartShrink_of_isOpen {C : FramedLevelCobordism n}
    (P : IFTSurfaceChart C) (base : E₂) (ambient : Set E')
    (hdomainOpen : IsOpen P.domain) (hbase : base ∈ P.domain)
    (hambient : ambient ∈ nhds (P.param base)) :
    Nonempty (M.IFTChartShrink P base ambient) :=
  M.nonempty_iftChartShrink P base ambient
    (hdomainOpen.mem_nhds hbase) hambient


-- @@ L426-426 verbatim
namespace SimultaneousShrink


-- @@ L428-432 verbatim
theorem ift_param_mem_domain {C : FramedLevelCobordism n}
    {P : IFTSurfaceChart C} {base : E₂} {ambient : Set E'}
    (S : M.IFTChartShrink P base ambient) (u : E₂) (hu : ‖u‖ < S.radius) :
    base + M.param u ∈ P.domain :=
  S.shifted_mem () u hu


-- @@ L434-439 verbatim
theorem ift_domain_mem_nhds {C : FramedLevelCobordism n}
    {P : IFTSurfaceChart C} {base : E₂} {ambient : Set E'}
    (S : M.IFTChartShrink P base ambient) (hdomainOpen : IsOpen P.domain)
    (u : E₂) (hu : ‖u‖ < S.radius) :
    P.domain ∈ nhds (base + M.param u) :=
  hdomainOpen.mem_nhds (ift_param_mem_domain (M := M) S u hu)


-- @@ L441-445 verbatim
theorem ift_lifted_mem {C : FramedLevelCobordism n}
    {P : IFTSurfaceChart C} {base : E₂} {ambient : Set E'}
    (S : M.IFTChartShrink P base ambient) (u : E₂) (hu : ‖u‖ < S.radius) :
    P.param (base + M.param u) ∈ ambient :=
  S.lifted_mem () u hu


-- @@ L447-447 verbatim
end SimultaneousShrink


-- @@ L449-455 verbatim
/-- At the chart's distinguished parameter origin, `domain_mem_nhds` supplies
the domain hypothesis automatically. -/
theorem nonempty_iftChartShrink_zero {C : FramedLevelCobordism n}
    (P : IFTSurfaceChart C) (ambient : Set E')
    (hambient : ambient ∈ nhds (P.param 0)) :
    Nonempty (M.IFTChartShrink P 0 ambient) :=
  M.nonempty_iftChartShrink P 0 ambient P.domain_mem_nhds hambient


-- @@ L457-467 verbatim
/-- Shrink into the chart domain and the open half-radius ball of a cutoff.
The open ball is the continuity target; it automatically lies in the closed
half-radius core used by the finite installation. -/
theorem nonempty_iftChartCutoffShrink {C : FramedLevelCobordism n}
    (P : IFTSurfaceChart C) (base : E₂) (hdomain : P.domain ∈ nhds base)
    (radius : ℝ) (hradius : 0 < radius) :
    Nonempty (M.IFTChartShrink P base
      (ball (P.param base) (radius / 2))) := by
  apply M.nonempty_iftChartShrink P base
  · exact hdomain
  · exact ball_mem_nhds _ (half_pos hradius)


-- @@ L469-481 verbatim
/-- Cutoff-core control together with a fixed finite differentiability order on
the whole normal-form ball. -/
theorem exists_iftChartCutoffShrink_contDiffOn {C : FramedLevelCobordism n}
    (k : ℕ) (P : IFTSurfaceChart C) (base : E₂)
    (hdomain : P.domain ∈ nhds base)
    (radius : ℝ) (hradius : 0 < radius) :
    ∃ S : M.IFTChartShrink P base
        (ball (P.param base) (radius / 2)),
      ContDiffOn ℝ (k : ℕ∞ω) M.param (ball (0 : E₂) S.radius) := by
  apply M.exists_simultaneousShrink_contDiffOn k base P.param
    P.param_smooth.continuous.continuousAt
  · exact fun _ : Unit => hdomain
  · exact fun _ : Unit => ball_mem_nhds _ (half_pos hradius)


-- @@ L483-490 verbatim
theorem nonempty_iftChartCutoffShrink_of_isOpen {C : FramedLevelCobordism n}
    (P : IFTSurfaceChart C) (base : E₂)
    (hdomainOpen : IsOpen P.domain) (hbase : base ∈ P.domain)
    (radius : ℝ) (hradius : 0 < radius) :
    Nonempty (M.IFTChartShrink P base
      (ball (P.param base) (radius / 2))) :=
  M.nonempty_iftChartCutoffShrink P base
    (hdomainOpen.mem_nhds hbase) radius hradius


-- @@ L492-501 verbatim
theorem exists_iftChartCutoffShrink_contDiffOn_of_isOpen
    {C : FramedLevelCobordism n}
    (k : ℕ) (P : IFTSurfaceChart C) (base : E₂)
    (hdomainOpen : IsOpen P.domain) (hbase : base ∈ P.domain)
    (radius : ℝ) (hradius : 0 < radius) :
    ∃ S : M.IFTChartShrink P base
        (ball (P.param base) (radius / 2)),
      ContDiffOn ℝ (k : ℕ∞ω) M.param (ball (0 : E₂) S.radius) :=
  M.exists_iftChartCutoffShrink_contDiffOn k P base
    (hdomainOpen.mem_nhds hbase) radius hradius


-- @@ L503-503 verbatim
namespace SimultaneousShrink


-- @@ L505-510 verbatim
theorem ift_lifted_mem_closedBall {C : FramedLevelCobordism n}
    {P : IFTSurfaceChart C} {base : E₂} {radius : ℝ}
    (S : M.IFTChartShrink P base (ball (P.param base) (radius / 2)))
    (u : E₂) (hu : ‖u‖ < S.radius) :
    P.param (base + M.param u) ∈ closedBall (P.param base) (radius / 2) :=
  ball_subset_closedBall (ift_lifted_mem (M := M) S u hu)


-- @@ L512-512 verbatim
end SimultaneousShrink


-- @@ L514-519 verbatim
/-- Origin-centered cutoff specialization using `IFTSurfaceChart.domain_mem_nhds`. -/
theorem nonempty_iftChartCutoffShrink_zero {C : FramedLevelCobordism n}
    (P : IFTSurfaceChart C) (radius : ℝ) (hradius : 0 < radius) :
    Nonempty (M.IFTChartShrink P 0
      (ball (P.param 0) (radius / 2))) :=
  M.nonempty_iftChartCutoffShrink P 0 P.domain_mem_nhds radius hradius


-- @@ L521-528 verbatim
theorem exists_iftChartCutoffShrink_contDiffOn_zero
    {C : FramedLevelCobordism n}
    (k : ℕ) (P : IFTSurfaceChart C) (radius : ℝ) (hradius : 0 < radius) :
    ∃ S : M.IFTChartShrink P 0
        (ball (P.param 0) (radius / 2)),
      ContDiffOn ℝ (k : ℕ∞ω) M.param (ball (0 : E₂) S.radius) :=
  M.exists_iftChartCutoffShrink_contDiffOn k P 0
    P.domain_mem_nhds radius hradius


-- @@ L530-530 verbatim
end LocalMorseNormalForm


-- @@ L532-532 verbatim
end Submission
