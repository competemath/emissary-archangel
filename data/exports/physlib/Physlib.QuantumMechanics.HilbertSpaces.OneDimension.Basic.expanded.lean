/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Physlib.Meta.TODO.Basic

-- @@ L12-16 verbatim
/-!

# Hilbert space for one dimension quantum mechanics

-/


-- @@ L18-18 verbatim
TODO "Remove 1d Hilbert space once dependencies are moved over to SpaceDHilbertSpace."


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
namespace QuantumMechanics


-- @@ L24-24 verbatim
namespace OneDimension


-- @@ L26-26 verbatim
noncomputable section


-- @@ L28-31 verbatim
/-- The Hilbert space for a one dimensional quantum system is defined as
  the space of almost-everywhere equal equivalence classes of square integrable functions
  from `ℝ` to `ℂ`. -/
abbrev HilbertSpace := MeasureTheory.Lp (α := ℝ) ℂ 2


-- @@ L33-33 verbatim
namespace HilbertSpace

-- @@ L34-34 verbatim
open Module MeasureTheory

-- @@ L35-35 verbatim
open InnerProductSpace


-- @@ L37-39 verbatim
/-- The anti-linear map from the Hilbert space to it's dual. -/
def toBra : HilbertSpace →ₛₗ[starRingEnd ℂ] StrongDual ℂ HilbertSpace :=
  InnerProductSpace.toDual ℂ HilbertSpace


-- @@ L41-41 verbatim
@[simp] lemma toBra_apply (f g : HilbertSpace) : toBra f g = ⟪f, g⟫_ℂ := rfl


-- @@ L43-46 verbatim
/-- The anti-linear map, `toBra`, taking a ket to it's corresponding
  bra is surjective. -/
lemma toBra_surjective : Function.Surjective toBra :=
  (InnerProductSpace.toDual ℂ HilbertSpace).surjective


-- @@ L48-52 verbatim
/-- The anti-linear map, `toBra`, taking a ket to it's corresponding
  bra is injective. -/
lemma toBra_injective : Function.Injective toBra := by
  intro f g h
  simpa [toBra] using h


-- @@ L54-58 verbatim
/-!

## Member of the Hilbert space as a property

-/


-- @@ L60-62 verbatim
/-- The proposition `MemHS f` for a function `f : ℝ → ℂ` is defined
  to be true if the function `f` can be lifted to the Hilbert space. -/
def MemHS (f : ℝ → ℂ) : Prop := MemLp f 2 MeasureTheory.volume


-- @@ L64-64 verbatim
lemma aeStronglyMeasurable_of_memHS {f : ℝ → ℂ} (h : MemHS f) : AEStronglyMeasurable f := h.1


-- @@ L66-77 verbatim
/-- A function `f` satisfies `MemHS f` if and only if it is almost everywhere
  strongly measurable, and square integrable. -/
lemma memHS_iff {f : ℝ → ℂ} : MemHS f ↔
    AEStronglyMeasurable f ∧ Integrable (fun x => ‖f x‖ ^ 2) := by
  rw [MemHS, MemLp, and_congr_right_iff]
  intro h1
  rw [MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (Ne.symm (NeZero.ne' 2)) ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat, Integrable]
  have h0 : MeasureTheory.AEStronglyMeasurable (fun x => norm (f x) ^ 2) MeasureTheory.volume :=
    MeasureTheory.AEStronglyMeasurable.pow (continuous_norm.comp_aestronglyMeasurable h1) ..
  simp [h0, HasFiniteIntegral]


-- @@ L79-85 verbatim
@[simp]
lemma zero_memHS : MemHS 0 := by
  change MemHS (fun x => (0 : ℂ))
  rw [memHS_iff]
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    integrable_fun_zero, and_true]
  fun_prop


-- @@ L87-88 verbatim
@[simp]
lemma zero_fun_memHS : MemHS (fun _ : ℝ => (0 : ℂ)) := zero_memHS


-- @@ L90-91 verbatim
lemma memHS_add {f g : ℝ → ℂ} (hf : MemHS f) (hg : MemHS g) :
    MemHS (f + g) := MeasureTheory.MemLp.add hf hg


-- @@ L93-94 verbatim
lemma memHS_smul {f : ℝ → ℂ} {c : ℂ} (hf : MemHS f) :
    MemHS (c • f) := MeasureTheory.MemLp.const_smul hf c


-- @@ L96-97 verbatim
lemma memHS_of_ae {g : ℝ → ℂ} (f : ℝ → ℂ) (hf : MemHS f) (hfg : f =ᵐ[MeasureTheory.volume] g) :
    MemHS g := MemLp.ae_eq hfg hf


-- @@ L99-103 verbatim
/-!

# Construction of elements of the Hilbert space

-/


-- @@ L105-108 verbatim
lemma aeEqFun_mk_mem_iff (f : ℝ → ℂ) (hf : AEStronglyMeasurable f volume) :
    AEEqFun.mk f hf ∈ HilbertSpace ↔ MemHS f := by
  simp only [Lp.mem_Lp_iff_memLp]
  exact MeasureTheory.memLp_congr_ae (AEEqFun.coeFn_mk f hf)


-- @@ L110-113 verbatim
/-- Given a function `f : ℝ → ℂ` such that `MemHS f` is true via `hf`, then `HilbertSpace.mk hf`
  is the element of the `HilbertSpace` defined by `f`. -/
def mk {f : ℝ → ℂ} (hf : MemHS f) : HilbertSpace :=
  ⟨AEEqFun.mk f hf.1, (aeEqFun_mk_mem_iff f hf.1).mpr hf⟩


-- @@ L115-118 verbatim
lemma coe_hilbertSpace_memHS (f : HilbertSpace) : MemHS (f : ℝ → ℂ) := by
  rw [← aeEqFun_mk_mem_iff f.1 (Lp.aestronglyMeasurable f)]
  have hf : f = AEEqFun.mk f.1 (Lp.aestronglyMeasurable f) := (AEEqFun.mk_coeFn _).symm
  exact hf ▸ f.2


-- @@ L120-122 verbatim
lemma mk_surjective (f : HilbertSpace) : ∃ (g : ℝ → ℂ), ∃ (hg : MemHS g), mk hg = f := by
  use f, coe_hilbertSpace_memHS f
  simp [mk]


-- @@ L124-125 verbatim
lemma coe_mk_ae {f : ℝ → ℂ} (hf : MemHS f) : (mk hf : ℝ → ℂ) =ᵐ[MeasureTheory.volume] f :=
  AEEqFun.coeFn_mk f hf.1


-- @@ L127-131 verbatim
lemma inner_mk_mk {f g : ℝ → ℂ} {hf : MemHS f} {hg : MemHS g} :
    inner ℂ (mk hf) (mk hg) = ∫ x : ℝ, starRingEnd ℂ (f x) * g x := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards [coe_mk_ae hf, coe_mk_ae hg] with _ hf hg
  simp [hf, hg, mul_comm]


-- @@ L133-135 verbatim
@[simp]
lemma eLpNorm_mk {f : ℝ → ℂ} {hf : MemHS f} : eLpNorm (mk hf) 2 volume = eLpNorm f 2 volume :=
  MeasureTheory.eLpNorm_congr_ae (coe_mk_ae hf)


-- @@ L137-149 verbatim
lemma mem_iff' {f : ℝ → ℂ} (hf : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume) :
    MeasureTheory.AEEqFun.mk f hf ∈ HilbertSpace
    ↔ MeasureTheory.Integrable (fun x => ‖f x‖ ^ 2) := by
  simp only [Lp.mem_Lp_iff_memLp, MemLp, eLpNorm_aeeqFun]
  have h1 : MeasureTheory.AEStronglyMeasurable
      (MeasureTheory.AEEqFun.mk f hf) MeasureTheory.volume :=
    MeasureTheory.AEEqFun.aestronglyMeasurable ..
  simp only [h1,
    MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (Ne.symm (NeZero.ne' 2))
      ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat, ENNReal.rpow_ofNat, true_and, Integrable]
  have h0 : MeasureTheory.AEStronglyMeasurable (fun x => norm (f x) ^ 2) MeasureTheory.volume :=
    MeasureTheory.AEStronglyMeasurable.pow (continuous_norm.comp_aestronglyMeasurable hf) ..
  simp [h0, HasFiniteIntegral]


-- @@ L151-152 verbatim
lemma mk_add {f g : ℝ → ℂ} {hf : MemHS f} {hg : MemHS g} :
    mk (memHS_add hf hg) = mk hf + mk hg := rfl


-- @@ L154-155 verbatim
lemma mk_smul {f : ℝ → ℂ} {c : ℂ} {hf : MemHS f} :
    mk (memHS_smul (c := c) hf) = c • mk hf := rfl


-- @@ L157-159 verbatim
lemma mk_eq_iff {f g : ℝ → ℂ} {hf : MemHS f} {hg : MemHS g} :
    mk hf = mk hg ↔ f =ᵐ[volume] g := by
  simp [mk]


-- @@ L161-163 verbatim
lemma ext_iff {f g : HilbertSpace} :
    f = g ↔ (f : ℝ → ℂ) =ᶠ[ae volume] (g : ℝ → ℂ) := by
  exact Lp.ext_iff


-- @@ L165-165 verbatim
end HilbertSpace

-- @@ L166-166 verbatim
end

-- @@ L167-167 verbatim
end OneDimension

-- @@ L168-168 verbatim
end QuantumMechanics
