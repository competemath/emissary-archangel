/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.RouteAAssembly
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SourceMorreyGradient
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SourceMorreyGradientInstances
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.BallBootstrap
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CarrierLocalAE


-- @@ L14-18 verbatim
/-!
# Route AOne Round Final

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
section


-- @@ L24-28 verbatim
/-!
# Route AOne Round

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/


-- @@ L30-30 verbatim
open MeasureTheory MeasureTheory.Measure Set Filter Metric

-- @@ L31-31 verbatim
open scoped BigOperators ENNReal NNReal Topology

-- @@ L32-32 verbatim
open CKN.Foundation.Parabolic

-- @@ L33-33 verbatim
open CKN.Foundation.Parabolic.Morrey

-- @@ L34-34 verbatim
open CKN.Core.HeatPotential

-- @@ L35-35 verbatim
open CKN.Core.Step3

-- @@ L36-36 verbatim
open CKN.Core.Endgame


-- @@ L38-38 verbatim
noncomputable section


-- @@ L40-44 verbatim
namespace CKN.Core.Step4

/- This is the exact representation binder consumed by the local producer
   theorem.  Its test functions are supported in the same local product box
   as the cutoff. -/

-- @@ L45-65 verbatim
/-- Heat-potential representation interface with an explicitly selected weak pressure gradient. -/
def routeAGradientSlotRepresentation : Prop :=
  ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
    IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
    ∀ {φ : Vec3 × ℝ → ℝ}, φ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
    ∀ {Ω' : Set Vec3} {J : Set ℝ}, localBox Ω I Ω' J →
    tsupport φ ⊆ Ω' ×ˢ J →
    ∀ {Dp : ParabolicPoint → Vec3},
    (∀ i, Integrable (fun z => Dp z i)
      (volume.restrict (spaceTimeSet Ω' J))) →
    (∀ i : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
      tsupport ψ ⊆ Ω' ×ˢ J →
      (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
        -(∫ z : ParabolicPoint, Dp z i * ψ z)) →
    localizedVelocity φ u =ᵐ[volume]
      (fun z i => heatPotential
        (fun w => localizedGradientSourceG φ u Du f Dp w i)
        (fun j w => localizedGradientSourceH φ u j w i) z)


-- @@ L67-67 verbatim
end CKN.Core.Step4

-- @@ L68-68 verbatim
end


-- @@ L70-70 verbatim
end


-- @@ L72-72 verbatim
open MeasureTheory MeasureTheory.Measure Set Filter Metric

-- @@ L73-73 verbatim
open scoped BigOperators ENNReal NNReal Topology

-- @@ L74-74 verbatim
open CKN.Foundation.Parabolic

-- @@ L75-75 verbatim
open CKN.Foundation.Parabolic.Morrey

-- @@ L76-76 verbatim
open CKN.Core.HeatPotential

-- @@ L77-77 verbatim
open CKN.Core.Step3

-- @@ L78-78 verbatim
open CKN.Core.Endgame


-- @@ L80-80 verbatim
noncomputable section


-- @@ L82-86 verbatim
namespace CKN.Core.Step4

/- The arbitrary-centre/radius first-round source producer is kept at this
   boundary until its general construction lands.  Its two support fields are
   deliberately symmetric-ball fields, matching BallBootstrap. -/

-- @@ L87-128 verbatim
/-- Final localized-source integrability and Morrey estimates required by the bootstrap route. -/
def routeAFinalSourcePackage : Prop :=
  ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
    IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
    ∀ (z₀ : ParabolicPoint) (R : ℝ), 0 < R →
    Metric.ball z₀ (2 * R) ⊆ spaceTimeSet Ω I →
    morreyVecMem 3 (25 / 3 : ℝ) (Metric.ball z₀ R) u →
    (∀ i : Fin 3, morreyVecMem 2 (25 / 8 : ℝ)
      (Metric.ball z₀ R) (fun z => Du z i)) →
    ∀ {Dp : ParabolicPoint → Vec3},
    (∀ i : Fin 3, AEMeasurable (fun z => Dp z i)
      (volume.restrict (Metric.ball z₀ (R / 2)))) →
    morreyVecMem (6 / 5 : ℝ) (min q (25 / 11 : ℝ))
      (Metric.ball z₀ (R / 2)) Dp →
    ∃ (φ : Vec3 × ℝ → ℝ) (U : Set Vec3) (J : Set ℝ)
      (KF KG : ℝ≥0∞),
      φ ∈ spaceTimeTestFunction (V := ℝ) Ω I ∧
      localBox Ω I U J ∧
      tsupport φ ⊆ U ×ˢ J ∧
      (U ×ˢ J) ⊆ parabolicHomeomorph.symm ⁻¹' Metric.ball z₀ (R / 2) ∧
      (∀ z ∈ Metric.ball z₀ (R / 4), φ (z.1, z.2) = 1) ∧
      (∀ i : Fin 3, Integrable (fun z => Dp z i)
        (volume.restrict (spaceTimeSet U J))) ∧
      (∀ i : Fin 3, AEMeasurable
        (fun z => localizedGradientSourceG φ u Du f Dp z i) volume) ∧
      (∀ j i : Fin 3, AEMeasurable
        (fun z => localizedGradientSourceH φ u j z i) volume) ∧
      (∀ i : Fin 3, HasCompactSupport
        (fun z => localizedGradientSourceG φ u Du f Dp z i)) ∧
      (∀ j i : Fin 3, HasCompactSupport
        (fun z => localizedGradientSourceH φ u j z i)) ∧
      KF < ⊤ ∧ KG < ⊤ ∧
      (∀ i : Fin 3, morreyNorm (6 / 5 : ℝ) (25 / 11)
        (fun z => localizedGradientSourceG φ u Du f Dp z i) ≤ KF) ∧
      (∀ j i : Fin 3, morreyNorm 3 (25 / 6)
        (fun z => localizedGradientSourceH φ u j z i) ≤ KG) ∧
      (∀ z ∉ Metric.ball z₀ (R / 2),
        localizedGradientSourceG φ u Du f Dp z = 0) ∧
      (∀ j z, z ∉ Metric.ball z₀ (R / 2) →
        localizedGradientSourceH φ u j z = 0)


-- @@ L130-227 verbatim
theorem routeA_one_round_velocity_improvement_of_producers_final
    (hG : routeAGradientProducer)
    (hL : routeAGradientSlotRepresentation)
    (hS : routeAFinalSourcePackage) :
    ∀ q : ℝ, 5 / 2 < q →
      ∀ {Ω : Set Vec3} {I : Set ℝ}
        {u : ParabolicPoint → Vec3}
        {Du : ParabolicPoint → Fin 3 → Vec3}
        {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ (z₀ : ParabolicPoint) (R : ℝ), 0 < R →
        Metric.ball z₀ (2 * R) ⊆ spaceTimeSet Ω I →
        morreyVecMem 3 (25 / 3 : ℝ) (Metric.ball z₀ R) u →
        (∀ i : Fin 3, morreyVecMem 2 (25 / 8 : ℝ)
          (Metric.ball z₀ R) (fun z => Du z i)) →
        morreyVecMem 3 25 (Metric.ball z₀ (R / 4)) u := by
  intro q hq Ω I u Du p f hsol z₀ R hR hdom hu hDu
  obtain ⟨Dp, hDpAE, hDpWeak, hDpN⟩ := hG q hq hsol z₀ R hR hdom hu hDu
  have hDpN' : morreyVecMem (6 / 5 : ℝ) (min q (25 / 11 : ℝ))
      (Metric.ball z₀ (R / 2)) Dp := by
    norm_num only [show ((1 / (25 / 3 : ℝ) + 8 / 25)⁻¹) = 25 / 11 by norm_num]
      at hDpN
    simpa only [min_comm] using hDpN
  obtain ⟨φ, U, J, KF, KG, hφ, hbox, hφbox, hboxsub, hφone, hDpInt,
      hGae, hHae, hGcompact, hHcompact, hKF, hKG, hGN, hHN, hGzero,
      hHzero⟩ := hS hsol z₀ R hR hdom hu hDu hDpAE hDpN'
  have hweak : ∀ i : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
      tsupport ψ ⊆ U ×ˢ J →
      (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
        -(∫ z : ParabolicPoint, Dp z i * ψ z) := by
    intro i ψ hψ hs
    exact hDpWeak i ψ hψ (hs.trans hboxsub)
  have hrepHeat := hL hsol hφ hbox hφbox hDpInt hweak
  let g : ParabolicPoint → Vec3 := fun z i =>
    localizedGradientSourceG φ u Du f Dp z i
  let h : Fin 3 → ParabolicPoint → Vec3 := fun j z i =>
    -localizedGradientSourceH φ u j z i
  have hg : ∀ i, AEMeasurable (fun z => g z i) volume := by
    intro i
    exact hGae i
  have hh : ∀ j i, AEMeasurable (fun z => h j z i) volume := by
    intro j i
    change AEMeasurable (fun z => -localizedGradientSourceH φ u j z i) volume
    exact (hHae j i).neg
  have hNF : ∀ i, morreyNorm (6 / 5 : ℝ) (25 / 11)
      (fun z => g z i) ≤ KF := by
    intro i
    exact hGN i
  have hNG : ∀ j i, morreyNorm 3 (25 / 6)
      (fun z => h j z i) ≤ KG := by
    intro j i
    simpa only [h, morreyNorm, morreyCell, cylinderPowerIntegral, abs_neg] using hHN j i
  have hgsupp : ∀ z ∉ Metric.ball z₀ (R / 2), g z = 0 := by
    intro z hz
    exact hGzero z hz
  have hhsupp : ∀ j z, z ∉ Metric.ball z₀ (R / 2) → h j z = 0 := by
    intro j z hz
    funext i
    have hz0 := congrFun (hHzero j z hz) i
    simp [h, hz0]
  have hrep : localizedVelocity φ u =ᵐ[volume]
      duhamelPotential g h := by
    filter_upwards [hrepHeat] with z hz
    let H : Fin 3 → ParabolicPoint → Vec3 := fun j w i =>
      localizedGradientSourceH φ u j w i
    have hz' := hz
    change localizedVelocity φ u z = vectorHeatPotential g H z at hz'
    have hsign := vectorHeatPotential_eq_duhamelPotential_neg z
      (F := g) (G := H)
    have hneg : (fun j w => -H j w) = h := by
      funext j w i
      rfl
    calc
      localizedVelocity φ u z = vectorHeatPotential g H z := hz'
      _ = duhamelPotential g h z := by
        rw [← hneg]
        exact hsign
  have hcore_le := bootstrap_morrey_le_of_component_sources_on_ball KF KG hKF hKG
    (by positivity : 0 < R / 2) hg hh hNF hNG hgsupp hhsupp hrep
  have hcore : morreyNorm 3 25
      (fun z => vec3EuclideanNorm (localizedVelocity φ u z)) < ∞ :=
    lt_of_le_of_lt hcore_le
      (bootstrapSourceMorreyBound_lt_top
        (ENNReal.mul_lt_top (by norm_num) hKF)
        (ENNReal.mul_lt_top (by norm_num) hKG))
  let Q : Set ParabolicPoint := Metric.ball z₀ (R / 4)
  have hone : ∀ z ∈ Q, u z = localizedVelocity φ u z := by
    intro z hz
    have hφz := hφone z hz
    symm
    change φ (z.1, z.2) • u z = u z
    rw [hφz, one_smul]
  have hlocal : u =ᵐ[volume.restrict Q] localizedVelocity φ u := by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz
    exact hone z hz
  exact CKN.Core.Endgame.morreyVecMem_three_twentyFive_of_ae_eq_restrict
    Metric.isOpen_ball.measurableSet hlocal hcore


-- @@ L229-229 verbatim
end CKN.Core.Step4
