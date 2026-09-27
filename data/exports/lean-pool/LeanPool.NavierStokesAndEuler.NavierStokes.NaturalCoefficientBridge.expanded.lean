/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSlowAxis
public import LeanPool.NavierStokesAndEuler.NavierStokes.SlowResidualMatching
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder


-- @@ L13-20 verbatim
/-!
# The natural core solves the actual order-zero residual equations

The natural solution is the one retained by `NaturalEntrance.CoefficientProfile`.
Its scalar swirl is normalized as `phi = C*f`, its pressure is unchanged, and
its radial flux is `X*beta`.  The two residual equations below are derived from
the constructed natural equations, not assumed as slow-order hypotheses.
-/


-- @@ L22-22 verbatim
@[expose] public section



-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-27 verbatim
open Set Filter

-- @@ L28-28 verbatim
open scoped Topology ContDiff


-- @@ L30-30 verbatim
namespace NavierStokes.NaturalCoefficientBridge


-- @@ L32-32 verbatim
open SimilarityProfile (InnerPoint InnerProfile partialX partialEta T Z)

-- @@ L33-33 verbatim
open SlowExpansionResidual


-- @@ L35-36 verbatim
theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  WithTop.coe_le_coe.mpr le_top


-- @@ L38-43 verbatim
theorem partialX_eq_slice {f : InnerProfile} {w : InnerPoint}
    (hf : DifferentiableAt ℝ f w) :
    partialX f w = deriv (fun x => f (x, w.2)) w.1 := by
  symm
  exact (hf.hasFDerivAt.comp_hasDerivAt w.1
    ((hasDerivAt_id w.1).prodMk (hasDerivAt_const w.1 w.2))).deriv


-- @@ L45-50 verbatim
theorem partialEta_eq_slice {f : InnerProfile} {w : InnerPoint}
    (hf : DifferentiableAt ℝ f w) :
    partialEta f w = deriv (fun η => f (w.1, η)) w.2 := by
  symm
  exact (hf.hasFDerivAt.comp_hasDerivAt w.2
    ((hasDerivAt_const w.2 w.1).prodMk (hasDerivAt_id w.2))).deriv


-- @@ L52-66 verbatim
theorem secondX_eq_slice {f : InnerProfile} {w : InnerPoint}
    (hf : ContDiffAt ℝ ∞ f w) :
    partialX (partialX f) w = iteratedDeriv 2 (fun x => f (x, w.2)) w.1 := by
  have hfx : DifferentiableAt ℝ (partialX f) w :=
    (SimilarityProfile.partialX_smoothAt hf (m := 1)
      (by norm_num)).differentiableAt (by norm_num)
  rw [partialX_eq_slice hfx, iteratedDeriv_succ, iteratedDeriv_one]
  have he : (fun x => partialX f (x, w.2)) =ᶠ[𝓝 w.1]
      deriv (fun x => f (x, w.2)) := by
    have hn := (continuous_id.prodMk continuous_const).continuousAt
      ((hf.of_le (nat_le_infty 1)).eventually (by norm_num))
    filter_upwards [hn] with x hx
    exact partialX_eq_slice
      ((show ContDiffAt ℝ 1 f (x, w.2) from hx).differentiableAt (by norm_num))
  exact he.deriv_eq


-- @@ L68-73 verbatim
theorem radialDifferential_eq {f : InnerProfile} {w : InnerPoint}
    (hf : ContDiffAt ℝ ∞ f w) (m : ℕ) :
    NaturalAxisBridge.radialDifferential m f w =
      w.1 * partialX (partialX f) w + m * partialX f w := by
  rw [secondX_eq_slice hf, partialX_eq_slice (hf.differentiableAt (by simp))]
  rfl


-- @@ L75-78 verbatim
theorem partialX_const_mul (C : ℝ) {f : InnerProfile} {w : InnerPoint}
    (hf : DifferentiableAt ℝ f w) :
    partialX (fun p => C * f p) w = C * partialX f w := by
  simp only [partialX, fderiv_const_mul hf, _root_.smul_apply, smul_eq_mul]


-- @@ L80-83 verbatim
theorem partialEta_const_mul (C : ℝ) {f : InnerProfile} {w : InnerPoint}
    (hf : DifferentiableAt ℝ f w) :
    partialEta (fun p => C * f p) w = C * partialEta f w := by
  simp only [partialEta, fderiv_const_mul hf, _root_.smul_apply, smul_eq_mul]


-- @@ L85-90 verbatim
theorem secondX_const_mul (C : ℝ) {f : InnerProfile} {w : InnerPoint}
    (hf : ContDiffAt ℝ ∞ f w) :
    partialX (partialX (fun p => C * f p)) w = C * partialX (partialX f) w := by
  rw [secondX_eq_slice (contDiffAt_const.mul hf), secondX_eq_slice hf]
  exact iteratedDeriv_const_mul
    C ((hf.comp w.1 (contDiffAt_id.prodMk contDiffAt_const)).of_le (nat_le_infty 2))


-- @@ L92-96 verbatim
/-- Flux reconstructed from the actual natural radial average. -/
noncomputable def naturalFlux (h : ℝ) (U V : InnerProfile) (w : InnerPoint) : ℝ :=
  w.1 / CoordinateAlgebra.L h w.2 *
    (2 * w.2 * U w - 2 * CoordinateAlgebra.D h * w.2 * V w -
      CoordinateAlgebra.d w.2 * NaturalAxisBridge.partialEta V w)


-- @@ L98-100 verbatim
/-- Zero sequence, with branches according to `n = 0`. -/
noncomputable def zeroSequence (f : InnerProfile) (n : ℕ) : InnerProfile :=
  if n = 0 then f else fun _ => 0


-- @@ L102-107 verbatim
/-- Natural profiles, bundling `phi`, `axial`, `flux`, `pressure`. -/
noncomputable def naturalProfiles (h C : ℝ) (f U V P : InnerProfile) : SlowProfiles where
  phi := zeroSequence (fun w => C * f w)
  axial := zeroSequence U
  flux := zeroSequence (naturalFlux h U V)
  pressure := zeroSequence P


-- @@ L109-116 verbatim
theorem angular_zero_formula (h : ℝ) (f : SlowProfiles) (w : InnerPoint) :
    angularCoefficient h f 0 w =
      T h (angularExponent h) (f.phi 0) w -
        2 * (w.1 * partialX (partialX (f.phi 0)) w + 2 * partialX (f.phi 0) w) +
        (f.flux 0 w * (partialX (f.phi 0) w + f.phi 0 w / w.1) +
          f.axial 0 w * Z h (angularExponent h) (f.phi 0) w) := by
  simp [angularCoefficient, transportCoefficient, recurrence, transportLinear, transportPair,
    slowOrder, convolution, previous]


-- @@ L118-126 verbatim
theorem axial_zero_formula (h : ℝ) (f : SlowProfiles) (w : InnerPoint) :
    axialCoefficient h f 0 w =
      T h (axialExponent h) (f.axial 0) w -
        2 * (w.1 * partialX (partialX (f.axial 0)) w + partialX (f.axial 0) w) +
        Z h (pressureExponent h) (f.pressure 0) w +
        (f.flux 0 w * partialX (f.axial 0) w +
          f.axial 0 w * Z h (axialExponent h) (f.axial 0) w) := by
  simp [axialCoefficient, transportCoefficient, recurrence, transportLinear, transportPair,
    slowOrder, convolution, previous, axialPressureSource]


-- @@ L128-153 verbatim
theorem natural_angular_zero {h j Λ : ℝ} {P0 a0 : ℝ → ℝ} {f U V P : InnerProfile}
    (hs : NaturalProfile.IsNaturalSolution h j Λ P0 a0 f U V P)
    (C : ℝ) {w : InnerPoint} (hw : w ∈ NaturalProfile.domain Λ)
    (hX : w.1 ≠ 0) (hL : CoordinateAlgebra.L h w.2 ≠ 0) :
    angularCoefficient h (naturalProfiles h C f U V P) 0 w = 0 := by
  have hf := hs.f_smooth.contDiffAt ((NaturalProfile.domain_isOpen Λ).mem_nhds hw)
  have hn := hs.angular_equation w hw
  rw [radialDifferential_eq hf 2] at hn
  rw [angular_zero_formula]
  simp only [naturalProfiles, zeroSequence, ↓reduceIte]
  unfold T Z CoordinateAlgebra.timeCoeff CoordinateAlgebra.axialCoeff
  rw [partialX_const_mul C (hf.differentiableAt (by simp)), secondX_const_mul C hf,
    partialEta_const_mul C (hf.differentiableAt (by simp))]
  have hx : NaturalAxisBridge.partialY f w = partialX f w :=
    (partialX_eq_slice (hf.differentiableAt (by simp))).symm
  have he : NaturalAxisBridge.partialEta f w = partialEta f w :=
    (partialEta_eq_slice (hf.differentiableAt (by simp))).symm
  rw [hx, he] at hn
  dsimp only [naturalFlux, angularExponent, CoordinateAlgebra.A, CoordinateAlgebra.D,
      CoordinateAlgebra.d,
    NaturalProfile.transportW, NaturalProfile.transportH, NaturalAxisData.A, NaturalAxisData.D,
    NaturalAxisData.d] at hn ⊢
  change _ ≠ 0 at hL
  change 2 * CoordinateAlgebra.L h w.2 * _ = _ at hn
  field_simp [hL, hX]
  linear_combination -2 * C * hn


-- @@ L155-182 verbatim
theorem natural_axial_zero {h j Λ : ℝ} {P0 a0 : ℝ → ℝ} {f U V P : InnerProfile}
    (hs : NaturalProfile.IsNaturalSolution h j Λ P0 a0 f U V P)
    (C : ℝ) {w : InnerPoint} (hw : w ∈ NaturalProfile.domain Λ)
    (hL : CoordinateAlgebra.L h w.2 ≠ 0) :
    axialCoefficient h (naturalProfiles h C f U V P) 0 w = 0 := by
  have hu := hs.U_smooth.contDiffAt ((NaturalProfile.domain_isOpen Λ).mem_nhds hw)
  have hp := hs.pressure_smooth.contDiffAt ((NaturalProfile.domain_isOpen Λ).mem_nhds hw)
  have hn := hs.axial_equation w hw
  rw [radialDifferential_eq hu 1] at hn
  rw [axial_zero_formula]
  simp only [naturalProfiles, zeroSequence, ↓reduceIte]
  unfold T Z CoordinateAlgebra.timeCoeff CoordinateAlgebra.axialCoeff
  have hx : NaturalAxisBridge.partialY U w = partialX U w :=
    (partialX_eq_slice (hu.differentiableAt (by simp))).symm
  have he : NaturalAxisBridge.partialEta U w = partialEta U w :=
    (partialEta_eq_slice (hu.differentiableAt (by simp))).symm
  have hpx : NaturalAxisBridge.partialY P w = partialX P w :=
    (partialX_eq_slice (hp.differentiableAt (by simp))).symm
  have hpe : NaturalAxisBridge.partialEta P w = partialEta P w :=
    (partialEta_eq_slice (hp.differentiableAt (by simp))).symm
  rw [hx, he, hpx, hpe] at hn
  dsimp only [naturalFlux, axialExponent, pressureExponent, CoordinateAlgebra.A,
      CoordinateAlgebra.D,
    CoordinateAlgebra.d, NaturalProfile.transportW, NaturalProfile.transportH, NaturalAxisData.A,
    NaturalAxisData.D, NaturalAxisData.d] at hn ⊢
  change 2 * CoordinateAlgebra.L h w.2 * _ = _ at hn
  field_simp [hL]
  linear_combination -2 * hn


-- @@ L184-195 verbatim
/-- The natural average is the genuine radial average, including the axis. -/
theorem natural_average_eq {h j Λ : ℝ} {P0 a0 : ℝ → ℝ} {f U V P : InnerProfile}
    (hs : NaturalProfile.IsNaturalSolution h j Λ P0 a0 f U V P)
    {w : InnerPoint} (hw : w ∈ NaturalProfile.domain Λ) :
    V w = ProfileHistories.average U w := by
  by_cases hX : w.1 = 0
  · rcases w with ⟨X, η⟩
    dsimp only at hX
    subst X
    rw [ProfileHistories.average_at_axis, hs.average_axis η hw.2, hs.U_axis η hw.2]
  · apply mul_left_cancel₀ hX
    exact (hs.average_integral w hw).trans (ProfileHistories.primitive_eq_mul_average U w)


-- @@ L197-213 verbatim
/-- The flux in the natural equations is precisely the canonical divergence
primitive used by the slow recursion. -/
theorem naturalFlux_eq_radialFlux {h j Λ : ℝ} {P0 a0 : ℝ → ℝ} {f U V P : InnerProfile}
    (hs : NaturalProfile.IsNaturalSolution h j Λ P0 a0 f U V P)
    {w : InnerPoint} (hw : w ∈ NaturalProfile.domain Λ) :
    naturalFlux h U V w = SlowDivergence.radialFlux h 0 U w := by
  have he : V =ᶠ[𝓝 w] ProfileHistories.average U := by
    filter_upwards [(NaturalProfile.domain_isOpen Λ).mem_nhds hw] with p hp
    exact natural_average_eq hs hp
  have hv := hs.average_smooth.contDiffAt ((NaturalProfile.domain_isOpen Λ).mem_nhds hw)
  have hd : NaturalAxisBridge.partialEta V w =
      partialEta (ProfileHistories.average U) w := by
    change deriv (fun η => V (w.1, η)) w.2 = _
    rw [← partialEta_eq_slice (hv.differentiableAt (by simp))]
    exact congrArg (fun L : InnerPoint →L[ℝ] ℝ => L (0, 1)) he.fderiv_eq
  simp only [naturalFlux, SlowDivergence.radialFlux, he.eq_of_nhds, hd, add_zero]
  ring


-- @@ L215-227 verbatim
/-- The same unscaled pressure solves the normalized slow pressure equation;
the `C⁻²` in that equation cancels the square of `C*f`. -/
theorem natural_pressure_zero {h j Λ C : ℝ} {P0 a0 : ℝ → ℝ} {f U V P : InnerProfile}
    (hs : NaturalProfile.IsNaturalSolution h j Λ P0 a0 f U V P)
    (hC : C ≠ 0) {w : InnerPoint} (hw : w ∈ NaturalProfile.domain Λ) :
    pressureCoefficient h C (naturalProfiles h C f U V P) 0 w = 0 := by
  have hp := hs.pressure_smooth.contDiffAt ((NaturalProfile.domain_isOpen Λ).mem_nhds hw)
  have hd : partialX P w = f w ^ 2 :=
    (partialX_eq_slice (hp.differentiableAt (by simp))).trans (hs.pressure_equation w hw)
  simp only [pressureCoefficient, naturalProfiles, zeroSequence, ↓reduceIte,
    convolution, Finset.Nat.antidiagonal_zero, Finset.sum_singleton, previous_zero,
    zero_div, add_zero, hd]
  field_simp; ring


-- @@ L229-257 verbatim
/-- Germ transfer to any actual slow sequence. Higher coefficients are
irrelevant at order zero. No order-zero residual equation is a hypothesis. -/
theorem zero_of_natural_germs {h j Λ C : ℝ} {P0 a0 : ℝ → ℝ} {f U V P : InnerProfile}
    (hs : NaturalProfile.IsNaturalSolution h j Λ P0 a0 f U V P)
    {g : SlowProfiles} {w : InnerPoint} (hw : w ∈ NaturalProfile.domain Λ)
    (hX : w.1 ≠ 0) (hL : CoordinateAlgebra.L h w.2 ≠ 0)
    (hphi : g.phi 0 =ᶠ[𝓝 w] fun p => C * f p)
    (hu : g.axial 0 =ᶠ[𝓝 w] U)
    (hv : g.flux 0 =ᶠ[𝓝 w] naturalFlux h U V)
    (hp : g.pressure 0 =ᶠ[𝓝 w] P) :
    angularCoefficient h g 0 w = 0 ∧ axialCoefficient h g 0 w = 0 := by
  have hvg : ∀ n ≤ 0, g.flux n =ᶠ[𝓝 w] (naturalProfiles h C f U V P).flux n := by
    intro n hn
    obtain rfl := Nat.le_zero.mp hn
    simpa only [naturalProfiles, zeroSequence, ↓reduceIte] using hv
  have hug : ∀ n ≤ 0, g.axial n =ᶠ[𝓝 w] (naturalProfiles h C f U V P).axial n := by
    intro n hn
    obtain rfl := Nat.le_zero.mp hn
    simpa only [naturalProfiles, zeroSequence, ↓reduceIte] using hu
  have hfg : ∀ n ≤ 0, g.phi n =ᶠ[𝓝 w] (naturalProfiles h C f U V P).phi n := by
    intro n hn
    obtain rfl := Nat.le_zero.mp hn
    simpa only [naturalProfiles, zeroSequence, ↓reduceIte] using hphi
  have hpg : g.pressure 0 =ᶠ[𝓝 w] (naturalProfiles h C f U V P).pressure 0 := by
    simpa only [naturalProfiles, zeroSequence, ↓reduceIte] using hp
  exact ⟨(SlowResidualMatching.angularCoefficient_congr_germ h 0 hvg hug hfg).trans
    (natural_angular_zero hs C hw hX hL),
    (SlowResidualMatching.axialCoefficient_congr_germ h 0 hvg hug hpg).trans
      (natural_axial_zero hs C hw hL)⟩


-- @@ L259-271 verbatim
theorem zero_of_radialFlux_germs {h j Λ C : ℝ} {P0 a0 : ℝ → ℝ} {f U V P : InnerProfile}
    (hs : NaturalProfile.IsNaturalSolution h j Λ P0 a0 f U V P)
    {g : SlowProfiles} {w : InnerPoint} (hw : w ∈ NaturalProfile.domain Λ)
    (hX : w.1 ≠ 0) (hL : CoordinateAlgebra.L h w.2 ≠ 0)
    (hphi : g.phi 0 =ᶠ[𝓝 w] fun p => C * f p)
    (hu : g.axial 0 =ᶠ[𝓝 w] U)
    (hv : g.flux 0 =ᶠ[𝓝 w] SlowDivergence.radialFlux h 0 U)
    (hp : g.pressure 0 =ᶠ[𝓝 w] P) :
    angularCoefficient h g 0 w = 0 ∧ axialCoefficient h g 0 w = 0 := by
  apply zero_of_natural_germs hs hw hX hL hphi hu _ hp
  apply hv.trans
  filter_upwards [(NaturalProfile.domain_isOpen Λ).mem_nhds hw] with p hp
  exact (naturalFlux_eq_radialFlux hs hp).symm


-- @@ L273-276 verbatim
/-- The closed initial segment on which ACT and the stock continuation retain
the natural fields. Its parameter interval is open and contains `[-1,1]`. -/
noncomputable def initialBand (Λ : ℝ) : Set InnerPoint :=
  Icc (0 : ℝ) (4 / Λ) ×ˢ ReferencePath.parameterInterval


-- @@ L278-280 verbatim
/-- Initial core, given by `Ioo (0 : ℝ) (4 / Λ) ×ˢ ReferencePath.parameterInterval`. -/
noncomputable def initialCore (Λ : ℝ) : Set InnerPoint :=
  Ioo (0 : ℝ) (4 / Λ) ×ˢ ReferencePath.parameterInterval


-- @@ L282-283 verbatim
theorem initialCore_open (Λ : ℝ) : IsOpen (initialCore Λ) :=
  isOpen_Ioo.prod ReferencePath.parameterInterval_open


-- @@ L285-286 verbatim
theorem initialCore_subset_band (Λ : ℝ) : initialCore Λ ⊆ initialBand Λ :=
  Set.prod_mono Ioo_subset_Icc_self Subset.rfl


-- @@ L288-295 verbatim
theorem initialBand_mem_domain {Λ : ℝ} (hΛ : 0 < Λ) {w : InnerPoint}
    (hw : w ∈ initialBand Λ) : w ∈ NaturalProfile.domain Λ := by
  change (-20 < Λ * w.1 ∧ Λ * w.1 < 20) ∧ w.2 ∈ ReferencePath.parameterInterval
  have hlo := mul_nonneg hΛ.le hw.1.1
  have hhi : Λ * w.1 ≤ 4 := by
    have ht := (le_div_iff₀ hΛ).mp hw.1.2
    nlinarith
  exact ⟨⟨by linarith, by linarith⟩, hw.2⟩


-- @@ L297-302 verbatim
theorem radialFlux_congr_germ (h lam : ℝ) {U V : InnerProfile} {w : InnerPoint}
    (hu : U =ᶠ[𝓝 w] V)
    (ha : ProfileHistories.average U =ᶠ[𝓝 w] ProfileHistories.average V) :
    SlowDivergence.radialFlux h lam U =ᶠ[𝓝 w] SlowDivergence.radialFlux h lam V := by
  filter_upwards [hu, ha, ha.fderiv (𝕜 := ℝ)] with p hp hpa hpd
  simp only [SlowDivergence.radialFlux, hp, hpa, partialEta, hpd]


-- @@ L304-304 verbatim
section ConstructedFamily


-- @@ L306-306 verbatim
variable {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}

-- @@ L307-307 verbatim
variable {d : NaturalAxisCoefficients.AnalyticInputs h j σ P0}

-- @@ L308-308 verbatim
variable (F : NaturalProfile.ProfileFamily d Λ C) (hΛ : 0 < Λ)

-- @@ L309-309 verbatim
variable (hP0 : ContDiff ℝ ∞ P0)


-- @@ L311-311 verbatim
include hΛ hP0


-- @@ L313-330 verbatim
/-- Initial field agreement determines the actual integral histories; no
pressure or average matching is postulated separately. -/
theorem initial_histories {D : ProfileHistories.RadialDomain}
    (Q : ProfileHistories.Profiles D) (hq0 : Q.pressure0 = P0)
    (hf : EqOn Q.f F.f (initialBand Λ)) (hu : EqOn Q.U F.U (initialBand Λ))
    {w : InnerPoint} (hw : w ∈ initialBand Λ) :
    Q.Ubar w = F.Ubar w ∧ Q.pressure w = F.Pi w := by
  have hh := ActualSlowAxis.histories_congr_below Q
    (ActivationStocks.naturalHistories F hΛ hP0) hw.1.1
    (congrFun hq0 w.2)
    (fun Y hY => hf (show (Y, w.2) ∈ initialBand Λ from
      ⟨⟨hY.1, hY.2.trans hw.1.2⟩, hw.2⟩))
    (fun Y hY => hu (show (Y, w.2) ∈ initialBand Λ from
      ⟨⟨hY.1, hY.2.trans hw.1.2⟩, hw.2⟩))
  exact ⟨hh.1.trans (ActivationStocks.naturalHistories_average F hΛ hP0
      (initialBand_mem_domain hΛ hw)),
    hh.2.trans (ActivationStocks.naturalHistories_pressure F hΛ hP0
      (initialBand_mem_domain hΛ hw))⟩


-- @@ L332-356 verbatim
theorem initial_germs {D : ProfileHistories.RadialDomain}
    (Q : ProfileHistories.Profiles D) (hq0 : Q.pressure0 = P0)
    (hf : EqOn Q.f F.f (initialBand Λ)) (hu : EqOn Q.U F.U (initialBand Λ))
    {w : InnerPoint} (hw : w ∈ initialCore Λ) :
    (Q.f =ᶠ[𝓝 w] F.f) ∧ (Q.U =ᶠ[𝓝 w] F.U) ∧
      (Q.Ubar =ᶠ[𝓝 w] F.Ubar) ∧ (Q.pressure =ᶠ[𝓝 w] F.Pi) ∧
      (SlowDivergence.radialFlux h 0 Q.U =ᶠ[𝓝 w] SlowDivergence.radialFlux h 0 F.U) := by
  have hn := (initialCore_open Λ).mem_nhds hw
  have hfg : Q.f =ᶠ[𝓝 w] F.f := by
    filter_upwards [hn] with p hp
    exact hf (initialCore_subset_band Λ hp)
  have hug : Q.U =ᶠ[𝓝 w] F.U := by
    filter_upwards [hn] with p hp
    exact hu (initialCore_subset_band Λ hp)
  have havg : Q.Ubar =ᶠ[𝓝 w] F.Ubar := by
    filter_upwards [hn] with p hp
    exact (initial_histories F hΛ hP0 Q hq0 hf hu (initialCore_subset_band Λ hp)).1
  have hpg : Q.pressure =ᶠ[𝓝 w] F.Pi := by
    filter_upwards [hn] with p hp
    exact (initial_histories F hΛ hP0 Q hq0 hf hu (initialCore_subset_band Λ hp)).2
  have havg' : ProfileHistories.average Q.U =ᶠ[𝓝 w] ProfileHistories.average F.U := by
    apply havg.trans
    filter_upwards [hn] with p hp
    exact natural_average_eq F.natural (initialBand_mem_domain hΛ (initialCore_subset_band Λ hp))
  exact ⟨hfg, hug, havg, hpg, radialFlux_congr_germ h 0 hug havg'⟩


-- @@ L358-377 verbatim
/-- The generic assembly interface: the natural equations are derived for
any slow sequence whose order-zero fields are the same initial construction. -/
theorem zero_of_initial_profiles (hsmall : NaturalAxisData.SmallParameters h j)
    {D : ProfileHistories.RadialDomain} (Q : ProfileHistories.Profiles D)
    (hq0 : Q.pressure0 = P0)
    (hf : EqOn Q.f F.f (initialBand Λ)) (hu : EqOn Q.U F.U (initialBand Λ))
    {g : SlowProfiles} {w : InnerPoint} (hw : w ∈ initialCore Λ)
    (hphi : g.phi 0 =ᶠ[𝓝 w] fun p => C * Q.f p)
    (haxial : g.axial 0 =ᶠ[𝓝 w] Q.U)
    (hflux : g.flux 0 =ᶠ[𝓝 w] SlowDivergence.radialFlux h 0 Q.U)
    (hpressure : g.pressure 0 =ᶠ[𝓝 w] Q.pressure) :
    angularCoefficient h g 0 w = 0 ∧ axialCoefficient h g 0 w = 0 := by
  obtain ⟨hfg, hug, -, hpg, hvg⟩ := initial_germs F hΛ hP0 Q hq0 hf hu hw
  apply zero_of_radialFlux_germs F.natural
    (initialBand_mem_domain hΛ (initialCore_subset_band Λ hw)) hw.1.1.ne'
    (TransitionRamp.L_pos_parameterInterval hsmall hw.2).ne'
  · exact hphi.trans (hfg.fun_comp (fun x => C * x))
  · exact haxial.trans hug
  · exact hflux.trans hvg
  · exact hpressure.trans hpg


-- @@ L379-379 verbatim
end ConstructedFamily


-- @@ L381-388 verbatim
/-- The order-zero profile sequence formed from genuine histories.  The
stored radial component is beta; `ofBeta` inserts its required factor `X`. -/
noncomputable def historiesProfiles {D : ProfileHistories.RadialDomain}
    (h C : ℝ) (Q : ProfileHistories.Profiles D) : SlowProfiles :=
  SlowResidualMatching.ofBeta (zeroSequence (fun p => C * Q.f p))
    (zeroSequence Q.U)
    (zeroSequence (fun p => SlowDivergence.radialFlux h 0 Q.U p / p.1))
    (zeroSequence Q.pressure)


-- @@ L390-397 verbatim
theorem historiesProfiles_flux {D : ProfileHistories.RadialDomain}
    (h C : ℝ) (Q : ProfileHistories.Profiles D) :
    (historiesProfiles h C Q).flux 0 = SlowDivergence.radialFlux h 0 Q.U := by
  funext p
  change p.1 * (SlowDivergence.radialFlux h 0 Q.U p / p.1) = _
  by_cases hp : p.1 = 0
  · simp [SlowDivergence.radialFlux, hp]
  · rw [mul_comm, div_mul_cancel₀ _ hp]


-- @@ L399-399 verbatim
section Transition


-- @@ L401-401 verbatim
variable {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}

-- @@ L402-402 verbatim
variable {d : NaturalAxisCoefficients.AnalyticInputs h j σ P0}

-- @@ L403-403 verbatim
variable (F : NaturalProfile.ProfileFamily d Λ C) (hΛ : 0 < Λ)

-- @@ L404-404 verbatim
variable (hsmall : NaturalAxisData.SmallParameters h j)

-- @@ L405-405 verbatim
variable {T δ κ w₁ w₂ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < ReferencePath.rampLimit)

-- @@ L406-406 verbatim
variable (hP0 : ContDiff ℝ ∞ P0) (hT : 0 < T)

-- @@ L407-407 verbatim
variable (hb : δ ≤ (TransitionRamp.ofNatural F hΛ hsmall hδ hδT hP0).bigTime)

-- @@ L408-408 verbatim
variable (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)


-- @@ L410-422 verbatim
/-- Concrete matching for the exact stock continuation later used by the
nominal profile. -/
theorem transition_initial_fields :
    let Q := TransitionRamp.physicalProfiles F hΛ hsmall hδ hδT hP0
      (κ := κ) hT hb hw₁ hw₂
    EqOn Q.f F.f (initialBand Λ) ∧ EqOn Q.U F.U (initialBand Λ) := by
  constructor
  · intro p hp
    exact (TransitionRamp.physical_fields_natural F hΛ hsmall hδ hδT hP0
      T κ w₁ w₂ hp.1.2).1
  · intro p hp
    exact (TransitionRamp.physical_fields_natural F hΛ hsmall hδ hδT hP0
      T κ w₁ w₂ hp.1.2).2


-- @@ L424-437 verbatim
theorem transition_coefficients_zero {p : InnerPoint} (hp : p ∈ initialCore Λ) :
    let Q := TransitionRamp.physicalProfiles F hΛ hsmall hδ hδT hP0
      (κ := κ) hT hb hw₁ hw₂
    angularCoefficient h (historiesProfiles h C Q) 0 p = 0 ∧
      axialCoefficient h (historiesProfiles h C Q) 0 p = 0 := by
  let Q := TransitionRamp.physicalProfiles F hΛ hsmall hδ hδT hP0
    (κ := κ) hT hb hw₁ hw₂
  obtain ⟨hf, hu⟩ := transition_initial_fields F hΛ hsmall hδ hδT hP0
    (κ := κ) hT hb hw₁ hw₂
  apply zero_of_initial_profiles F hΛ hP0 hsmall Q rfl hf hu hp
  · exact Filter.EventuallyEq.rfl
  · exact Filter.EventuallyEq.rfl
  · rw [historiesProfiles_flux]
  · exact Filter.EventuallyEq.rfl


-- @@ L439-439 verbatim
end Transition


-- @@ L441-441 verbatim
section ActualHierarchy


-- @@ L443-443 verbatim
variable {N : ReferencePath.Input} {h R : ℝ} {P0 : ℝ → ℝ} {Ω : Set ℂ}

-- @@ L444-444 verbatim
variable (E : ActivationHolomorphic.InitialTube N h P0 R Ω)

-- @@ L445-445 verbatim
variable {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)

-- @@ L446-446 verbatim
variable (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ)

-- @@ L447-447 verbatim
variable (hP0 : ContDiff ℝ ∞ P0) (C : ℝ)


-- @@ L449-467 verbatim
/-- At zero slow order the actual recursion's stored beta reconstructs the
canonical flux of its own axial field, with no missing `X` factor. -/
theorem hierarchy_flux_zero {X η : ℝ}
    (hX : X ∈ Ioo (0 : ℝ) (ActualSlowAxis.axisRadius N δ ^ 2))
    (hη : (η : ℂ) ∈ ActualSlowAxis.parameterDomain Ω) :
    let A := ActualSlowAxis.hierarchy E hT hδ hδT κ hP0 C
    let Q := StressActivation.FromReference.histories N hT hδ hδT κ P0 hP0
    (SlowResidualMatching.hierarchyProfiles A).flux 0 (X, η) =
      SlowDivergence.radialFlux h 0 Q.U (X, η) := by
  let A := ActualSlowAxis.hierarchy E hT hδ hδT κ hP0 C
  have hr := ActualSlowAxis.axisRadius_pos N δ
  have hs := SlowRecursion.core_lt_radius (core := ActualSlowAxis.axisRadius N δ)
    (buffer := 1) zero_lt_one 0
  have hsq : X < SlowRecursion.radius (ActualSlowAxis.axisRadius N δ) 1 0 ^ 2 := by
    nlinarith [hX.2]
  change X * SlowRecursion.profile (A.coefficients 0 4) (X, η) = _
  rw [A.starts]
  rw [ActualSlowAxis.base_beta_value E hT hδ hδT κ hP0 C _ ⟨hX.1, hsq⟩ hη]
  rw [mul_comm, div_mul_cancel₀ _ hX.1.ne']


-- @@ L469-469 verbatim
end ActualHierarchy


-- @@ L471-471 verbatim
section RadialPrimitives


-- @@ L473-473 verbatim
variable {h C r a : ℝ} {f : SlowProfiles} {S : Set ℝ}

-- @@ L474-474 verbatim
variable (ha : a ^ 2 / 2 < r)

-- @@ L475-476 verbatim
variable (hzero : ∀ p ∈ Ioo (0 : ℝ) r ×ˢ S,
  angularCoefficient h f 0 p = 0 ∧ axialCoefficient h f 0 p = 0)


-- @@ L478-478 verbatim
include ha hzero


-- @@ L480-492 verbatim
theorem radial_densities_zero {R η : ℝ} (hR : R ∈ Icc (0 : ℝ) a) (hη : η ∈ S) :
    SlowResidualMatching.thetaDensity h C f 0 (R, η) = 0 ∧
      SlowResidualMatching.zDensity h f 0 (R, η) = 0 := by
  by_cases hz : R = 0
  · subst R
    simp [SlowResidualMatching.thetaDensity, SlowResidualMatching.zDensity]
  · have hp : 0 < R := lt_of_le_of_ne hR.1 (Ne.symm hz)
    have hsum : 0 ≤ a + R := by linarith [hR.2]
    have hsq : R ^ 2 / 2 < r := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hR.2) hsum]
    have he := hzero (R ^ 2 / 2, η) ⟨⟨by positivity, hsq⟩, hη⟩
    simp only [SlowResidualMatching.thetaDensity, SlowResidualMatching.zDensity,
      SlowResidualMatching.radiusPoint, he.1, he.2, mul_zero, and_self]


-- @@ L494-510 verbatim
/-- Both defining radial integrals vanish. This proves the integration
constants are zero, rather than only proving a derivative equation. -/
theorem radial_primitives_zero {R η : ℝ} (hR : R ∈ Icc (0 : ℝ) a) (hη : η ∈ S) :
    ProfileHistories.primitive (SlowResidualMatching.thetaDensity h C f 0) (R, η) = 0 ∧
      ProfileHistories.primitive (SlowResidualMatching.zDensity h f 0) (R, η) = 0 := by
  have hint (F : InnerProfile) (hF : ∀ ρ ∈ Icc (0 : ℝ) a, F (ρ, η) = 0) :
      ProfileHistories.primitive F (R, η) = 0 := by
    change (∫ ρ in (0 : ℝ)..R, F (ρ, η)) = 0
    calc
      _ = ∫ _ρ in (0 : ℝ)..R, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro ρ hρ
        rw [uIcc_of_le hR.1] at hρ
        exact hF ρ ⟨hρ.1, hρ.2.trans hR.2⟩
      _ = 0 := by simp
  exact ⟨hint _ (fun ρ hρ => (radial_densities_zero (C := C) ha hzero hρ hη).1),
    hint _ (fun ρ hρ => (radial_densities_zero (C := C) ha hzero hρ hη).2)⟩


-- @@ L512-520 verbatim
/-- The canonical negative stress primitives are zero on the entire inner
half-line, including their defined zero extension across the axis. -/
theorem radial_stresses_zero {R η : ℝ} (hR : R ≤ a) (hη : η ∈ S) :
    SlowStressSupport.stress 2 (SlowResidualMatching.thetaDensity h C f 0) (R, η) = 0 ∧
      SlowStressSupport.stress 1 (SlowResidualMatching.zDensity h f 0) (R, η) = 0 := by
  exact ⟨SlowStressSupport.stress_inner 2
      (fun η hη R hR => (radial_densities_zero (C := C) ha hzero hR hη).1) hR hη,
    SlowStressSupport.stress_inner 1
      (fun η hη R hR => (radial_densities_zero (C := C) ha hzero hR hη).2) hR hη⟩


-- @@ L522-522 verbatim
end RadialPrimitives


-- @@ L524-524 verbatim
section ActualNatural


-- @@ L526-544 verbatim
theorem activation_initial_fields {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}
    {d : NaturalAxisCoefficients.AnalyticInputs h j σ P0}
    (F : NaturalProfile.ProfileFamily d Λ C) (hΛ : 0 < Λ)
    (hP0 : ContDiff ℝ ∞ P0) {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) :
    let Q := StressActivation.FromReference.histories (ReferencePath.Input.ofNatural hΛ F)
      hT hδ hδT κ P0 hP0
    EqOn Q.f F.f (initialBand Λ) ∧ EqOn Q.U F.U (initialBand Λ) := by
  constructor
  · intro p hp
    change StressActivation.FromReference.f _ T κ δ p = _
    rw [StressActivation.FromReference.f_eq_reference _ T κ δ hp.1.2,
      ReferencePath.Input.refF_eq_natural_initial _ δ hp.1.2]
    rfl
  · intro p hp
    change StressActivation.FromReference.U _ T κ δ p = _
    rw [StressActivation.FromReference.U_eq_reference _ T κ δ hp.1.2,
      ReferencePath.Input.refU_eq_natural_initial _ δ hp.1.2]
    rfl


-- @@ L546-546 verbatim
variable {h j σ Λ C : ℝ} {g a : ℝ → ℝ} {cap : ℝ} {P0 : ℝ → ℝ}

-- @@ L547-547 verbatim
variable (hp : PressureDatum.Admissible g a cap) (hP0 : P0 = PressureDatum.pressure g a)

-- @@ L548-548 verbatim
variable {d : NaturalAxisCoefficients.AnalyticInputs h j σ P0}

-- @@ L549-549 verbatim
variable (F : NaturalEntrance.CoefficientProfile d Λ C) (hΛ : 0 < Λ)

-- @@ L550-550 verbatim
variable (hsmall : NaturalAxisData.SmallParameters h j) (hσ : 0 < σ)

-- @@ L551-551 verbatim
variable {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)

-- @@ L552-552 verbatim
variable (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ)


-- @@ L554-595 verbatim
/-- The actual `ActualSlowAxis.fromNatural` hierarchy solves both order-zero
equations on its natural core. This uses its constructed beta and recomputed
pressure, not additional equations supplied to the hierarchy. -/
theorem fromNatural_coefficients_zero {p : InnerPoint} (hp0 : p ∈ initialCore Λ)
    (hpη : (p.2 : ℂ) ∈ ActualSlowAxis.parameterDomain
      (AxisHolomorphic.parameterTube ActivationHolomorphic.parameterWindow
        (ActualSlowAxis.tubeWidth hp hP0 F hΛ hsmall hσ))) :
    let A := ActualSlowAxis.fromNatural hp hP0 F hΛ hsmall hσ hT hδ hδT κ
    angularCoefficient h (SlowResidualMatching.hierarchyProfiles A) 0 p = 0 ∧
      axialCoefficient h (SlowResidualMatching.hierarchyProfiles A) 0 p = 0 := by
  let N := ReferenceJetBounds.referenceInput F hΛ
  let Q := StressActivation.FromReference.histories N hT hδ hδT κ P0
    (ActualSlowAxis.actualPressure_smooth hp hP0)
  let E := ActualSlowAxis.constructedTube hp hP0 F hΛ hsmall hσ
  let A := ActualSlowAxis.fromNatural hp hP0 F hΛ hsmall hσ hT hδ hδT κ
  obtain ⟨hf, hu⟩ := activation_initial_fields F.family hΛ
    (ActualSlowAxis.actualPressure_smooth hp hP0) hT hδ hδT κ
  have hn := (initialCore_open Λ).mem_nhds hp0
  have hdomain : ∀ᶠ q : InnerPoint in 𝓝 p, (q.2 : ℂ) ∈
      ActualSlowAxis.parameterDomain
        (AxisHolomorphic.parameterTube ActivationHolomorphic.parameterWindow
          (ActualSlowAxis.tubeWidth hp hP0 F hΛ hsmall hσ)) :=
    (Complex.continuous_ofReal.comp continuous_snd).continuousAt
      ((ActualSlowAxis.parameterDomain_open E.isOpen).mem_nhds hpη)
  have he : N.endpoint ≤ N.endpoint * Real.exp δ :=
    le_mul_of_one_le_right N.endpoint_pos.le (Real.one_le_exp hδ.le)
  have hr : 4 / Λ < ActualSlowAxis.axisRadius N δ ^ 2 :=
    he.trans_lt (ActualSlowAxis.collar_lt_square N δ)
  apply zero_of_initial_profiles F.family hΛ (ActualSlowAxis.actualPressure_smooth hp hP0)
    hsmall Q rfl hf hu hp0
  · filter_upwards [hn] with q hq
    exact (ActualSlowAxis.fromNatural_base_values hp hP0 F hΛ hsmall hσ
      hT hδ hδT κ hq.1.1.le hq.2).1
  · filter_upwards [hn] with q hq
    exact (ActualSlowAxis.fromNatural_base_values hp hP0 F hΛ hsmall hσ
      hT hδ hδT κ hq.1.1.le hq.2).2.1
  · filter_upwards [hn, hdomain] with q hq hqη
    exact hierarchy_flux_zero E hT hδ hδT κ (ActualSlowAxis.actualPressure_smooth hp hP0)
      C ⟨hq.1.1, hq.1.2.trans hr⟩ hqη
  · filter_upwards [hn] with q hq
    exact (ActualSlowAxis.fromNatural_base_values hp hP0 F hΛ hsmall hσ
      hT hδ hδT κ hq.1.1.le hq.2).2.2.2


-- @@ L597-627 verbatim
/-- For the same constructed natural/ACT hierarchy, the defining integrals
and both canonical stresses vanish on a fixed positive neighborhood of the
axis. The radius here is strictly inside the natural coefficient core. -/
theorem fromNatural_primitives_and_stresses_zero {R η : ℝ}
    (hR : R ∈ Icc (0 : ℝ) (Real.sqrt (4 / Λ)))
    (hη : (η : ℂ) ∈ ActualSlowAxis.parameterDomain
      (AxisHolomorphic.parameterTube ActivationHolomorphic.parameterWindow
        (ActualSlowAxis.tubeWidth hp hP0 F hΛ hsmall hσ))) :
    let A := ActualSlowAxis.fromNatural hp hP0 F hΛ hsmall hσ hT hδ hδT κ
    let f := SlowResidualMatching.hierarchyProfiles A
    ProfileHistories.primitive (SlowResidualMatching.thetaDensity h C f 0) (R, η) = 0 ∧
      ProfileHistories.primitive (SlowResidualMatching.zDensity h f 0) (R, η) = 0 ∧
      SlowStressSupport.stress 2 (SlowResidualMatching.thetaDensity h C f 0) (R, η) = 0 ∧
      SlowStressSupport.stress 1 (SlowResidualMatching.zDensity h f 0) (R, η) = 0 := by
  let A := ActualSlowAxis.fromNatural hp hP0 F hΛ hsmall hσ hT hδ hδT κ
  let f := SlowResidualMatching.hierarchyProfiles A
  let S : Set ℝ := {η | (η : ℂ) ∈ ActualSlowAxis.parameterDomain
    (AxisHolomorphic.parameterTube ActivationHolomorphic.parameterWindow
      (ActualSlowAxis.tubeWidth hp hP0 F hΛ hsmall hσ))}
  have hz : ∀ p ∈ Ioo (0 : ℝ) (4 / Λ) ×ˢ S,
      angularCoefficient h f 0 p = 0 ∧ axialCoefficient h f 0 p = 0 := by
    intro p hp'
    exact fromNatural_coefficients_zero hp hP0 F hΛ hsmall hσ hT hδ hδT κ
      ⟨hp'.1, ActualSlowAxis.parameterDomain_real_interval hp'.2⟩ hp'.2
  have hpos : 0 < (4 : ℝ) / Λ := div_pos (by norm_num) hΛ
  have ha : Real.sqrt (4 / Λ) ^ 2 / 2 < 4 / Λ := by
    rw [Real.sq_sqrt hpos.le]
    linarith
  obtain ⟨hθ, hz'⟩ := radial_primitives_zero (C := C) ha hz hR hη
  obtain ⟨hsθ, hsz⟩ := radial_stresses_zero (C := C) ha hz hR.2 hη
  exact ⟨hθ, hz', hsθ, hsz⟩


-- @@ L629-629 verbatim
end ActualNatural


-- @@ L631-631 verbatim
end NavierStokes.NaturalCoefficientBridge
