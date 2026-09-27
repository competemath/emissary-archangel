/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolutionIntegrable
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod


-- @@ L12-16 verbatim
/-!
# Slice Integrability

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
open MeasureTheory MeasureTheory.Measure Set Filter

-- @@ L21-21 verbatim
open scoped ENNReal NNReal Topology

-- @@ L22-22 verbatim
open CKN.Foundation.Parabolic



-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-27 verbatim
namespace CKN


-- @@ L29-52 verbatim
private theorem integrable_sq_of_local_energy
    {Ω' : Set Vec3} {J : Set ℝ} {E : Type}
    [NormedAddCommGroup E] {v : ParabolicPoint → E}
    (hv : AEStronglyMeasurable v (volume.restrict (spaceTimeSet Ω' J)))
    (hvlt : (∫⁻ z in spaceTimeSet Ω' J, ‖v z‖ₑ ^ (2 : ℝ)) < ⊤) :
    Integrable (fun z => (‖v z‖ : ℝ) ^ (2 : ℕ))
      (volume.restrict (spaceTimeSet Ω' J)) := by
  have hvmeas : AEStronglyMeasurable
      (fun z => (‖v z‖ : ℝ) ^ (2 : ℕ))
      (volume.restrict (spaceTimeSet Ω' J)) := hv.norm.pow 2
  have hvfin : ∫⁻ z in spaceTimeSet Ω' J,
      ENNReal.ofReal ((‖v z‖ : ℝ) ^ (2 : ℕ)) ≠ ⊤ := by
    convert ne_of_lt hvlt using 1
    congr 1
    funext z
    calc
      ENNReal.ofReal ((‖v z‖ : ℝ) ^ (2 : ℕ)) =
          ENNReal.ofReal ((‖v z‖ : ℝ) ^ (2 : ℝ)) := by
            norm_num [Real.rpow_natCast]
      _ = ENNReal.ofReal ‖v z‖ ^ (2 : ℝ) :=
        (ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)).symm
      _ = ‖v z‖ₑ ^ (2 : ℝ) := by rw [ofReal_norm]
  exact (lintegral_ofReal_ne_top_iff_integrable hvmeas
    (Filter.Eventually.of_forall fun z => sq_nonneg _)).mp hvfin


-- @@ L54-64 verbatim
private theorem integrable_sq_of_local_energy_prod
    {Ω' : Set Vec3} {J : Set ℝ} {E : Type}
    [NormedAddCommGroup E] {v : ParabolicPoint → E}
    (hv : AEStronglyMeasurable v (volume.restrict (spaceTimeSet Ω' J)))
    (hvlt : (∫⁻ z in spaceTimeSet Ω' J, ‖v z‖ₑ ^ (2 : ℝ)) < ⊤) :
    Integrable (fun z => (‖v z‖ : ℝ) ^ (2 : ℕ))
      (((volume : Measure Vec3).restrict Ω').prod (volume.restrict J)) := by
  rw [Measure.prod_restrict Ω' J]
  exact integrable_sq_of_local_energy hv hvlt

/- The next theorem is public. -/

-- @@ L65-110 verbatim
/-- The velocity and gradient have square-integrable spatial slices almost everywhere
in every local space-time box. -/
theorem slice_memLp_ae_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (h : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {Ω' : Set Vec3} {J : Set ℝ} (hbox : localBox Ω I Ω' J) :
    ∀ᵐ s ∂volume.restrict J,
      MemLp (fun x : Vec3 => u (x, s)) 2 (volume.restrict Ω') ∧
      MemLp (fun x : Vec3 => Du (x, s)) 2 (volume.restrict Ω') := by
  rcases h with ⟨_hΩ, _hI, _hIord, _hq, _hf, hdata, _hS2, _hS3, _hS4⟩
  obtain ⟨hu, hDu, _hpmeas, _hfmeas, _hessSup, henergy, _hp, _hf, _hgrad⟩ :=
    hdata Ω' J hbox
  have hu_lt : (∫⁻ z in spaceTimeSet Ω' J, ‖u z‖ₑ ^ (2 : ℝ)) < ⊤ :=
    lt_of_le_of_lt (lintegral_mono (fun z => le_add_right le_rfl)) henergy
  have hDu_lt : (∫⁻ z in spaceTimeSet Ω' J, ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤ :=
    lt_of_le_of_lt (lintegral_mono (fun z => le_add_left le_rfl)) henergy
  have hu_sq := integrable_sq_of_local_energy_prod hu hu_lt
  have hDu_sq := integrable_sq_of_local_energy_prod hDu hDu_lt
  have hu_meas : AEStronglyMeasurable u
      (((volume : Measure Vec3).restrict Ω').prod (volume.restrict J)) := by
    rw [Measure.prod_restrict Ω' J]
    exact hu
  have hDu_meas : AEStronglyMeasurable Du
      (((volume : Measure Vec3).restrict Ω').prod (volume.restrict J)) := by
    rw [Measure.prod_restrict Ω' J]
    exact hDu
  have hu_meas_slice : ∀ᵐ s ∂volume.restrict J,
      AEStronglyMeasurable (fun x : Vec3 => u (x, s)) (volume.restrict Ω') :=
    hu_meas.prodMk_right
  have hDu_meas_slice : ∀ᵐ s ∂volume.restrict J,
      AEStronglyMeasurable (fun x : Vec3 => Du (x, s)) (volume.restrict Ω') :=
    hDu_meas.prodMk_right
  have hu_sq_slice : ∀ᵐ s ∂volume.restrict J,
      Integrable (fun x : Vec3 => (‖u (x, s)‖ : ℝ) ^ (2 : ℕ))
        (volume.restrict Ω') :=
    hu_sq.prod_left_ae
  have hDu_sq_slice : ∀ᵐ s ∂volume.restrict J,
      Integrable (fun x : Vec3 => (‖Du (x, s)‖ : ℝ) ^ (2 : ℕ))
        (volume.restrict Ω') :=
    hDu_sq.prod_left_ae
  filter_upwards [hu_meas_slice, hDu_meas_slice, hu_sq_slice, hDu_sq_slice]
    with s hu_meas_s hDu_meas_s hu_sq_s hDu_sq_s
  exact ⟨(memLp_two_iff_integrable_sq_norm hu_meas_s).2 hu_sq_s,
    (memLp_two_iff_integrable_sq_norm hDu_meas_s).2 hDu_sq_s⟩


-- @@ L112-112 verbatim
end CKN
