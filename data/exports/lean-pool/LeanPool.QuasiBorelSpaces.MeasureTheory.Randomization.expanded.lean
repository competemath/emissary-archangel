/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import LeanPool.QuasiBorelSpaces.MeasureTheory.Pack
public import LeanPool.QuasiBorelSpaces.MeasureTheory.Quantile
import Mathlib.Tactic.Positivity.Finset


-- @@ L12-16 verbatim
/-!
# LeanPool.QuasiBorelSpaces.MeasureTheory.Randomization

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.MeasureTheory.Randomization`.
-/


-- @@ L18-18 verbatim
@[expose] public section



-- @@ L21-21 verbatim
open scoped unitInterval


-- @@ L23-23 verbatim
namespace MeasureTheory.Measure


-- @@ L25-25 verbatim
variable {A B} [MeasurableSpace A] [MeasurableSpace B]


-- @@ L27-30 verbatim
/-- `normalize` is the canonical injection from `[0, r)` to `[0, 1]`. -/
noncomputable def normalize {r : ℝ} (x : Set.Ico 0 r) : I where
  val := x / r
  property := by rw [Set.mem_Icc, le_div_iff₀, div_le_iff₀] <;> grind


-- @@ L32-35 verbatim
@[simp, fun_prop]
lemma measurable_normalize (r) : Measurable (normalize (r := r)) := by
  unfold normalize
  fun_prop


-- @@ L37-43 verbatim
lemma injective_normalize (r) : Function.Injective (normalize (r := r)) := by
  intro i₁ i₂ hi
  simp only [normalize, Subtype.mk.injEq] at hi
  rw [div_left_inj'] at hi
  · ext
    exact hi
  · grind


-- @@ L45-47 verbatim
noncomputable instance instMeasureSpaceElemRealIcoOfNatLeanPool (r : ℝ) :
    MeasureSpace (Set.Ico 0 r) where
  volume := ENNReal.ofReal r • volume.comap normalize


-- @@ L49-49 verbatim
instance : IsEmpty (Set.Ico 0 (0 : ℝ)) := by simp


-- @@ L51-57 verbatim
@[simp]
lemma volume_zero : (volume : Measure (Set.Ico 0 (0 : ℝ))) = 0 := by
  ext s
  have hs : s = ∅ := by
    ext a
    simpa using a.property
  simp only [hs, measure_empty]


-- @@ L59-83 verbatim
@[simp]
lemma measurableEmbedding_normalize (r) : MeasurableEmbedding (normalize (r := r)) where
  injective := injective_normalize r
  measurable := measurable_normalize r
  measurableSet_image' := by
    intro s hs
    apply MeasurableSet.of_subtype_image
    simp only [normalize, ← Set.image_comp, Function.comp_apply]
    replace hs := MeasurableSet.subtype_image (by simp) hs
    have : ((fun a ↦ ↑a / r) '' s) = (· / r) '' (Subtype.val '' s) := by
      simp only [← Set.image_comp]
      rfl
    change MeasurableSet ((fun a : Set.Ico 0 r ↦ (a : ℝ) / r) '' s)
    rw [this]
    generalize ht : Subtype.val '' s = t
    rw [ht] at hs
    clear ht this s
    wlog! hr : r ≠ 0
    · subst hr
      simp only [Set.image, div_zero, exists_and_right, measurableSet_setOfPred]
      fun_prop
    have : (fun x ↦ x / r) '' t = (· * r) ⁻¹' t := by grind
    rw [this]
    apply MeasurableMul.measurable_mul_const
    exact hs


-- @@ L85-98 verbatim
@[simp]
lemma range_normalize {r} (hr : 0 < r) : Set.range (normalize (r := r)) = Set.Ico 0 1 := by
  ext x
  simp only [Set.mem_range, normalize, Subtype.exists, Set.mem_Ico, zero_le, true_and]
  refine ⟨?_, ?_⟩
  · rintro ⟨y, ⟨hy₁, hy₂⟩, rfl⟩
    rw [Subtype.mk_lt_mk, Set.Icc.coe_one, div_lt_one] <;> grind
  · intro h
    use x * r
    have : 0 ≤ x * r := by apply mul_nonneg <;> grind
    have : x * r < r := by rw [mul_lt_iff_lt_one_left] <;> grind
    simp only [and_self, exists_true_left, *]
    rw [Subtype.mk_eq_mk, MulDivCancelClass.mul_div_cancel]
    grind


-- @@ L100-105 verbatim
@[simp]
lemma volume_restrict_normalize : volume.restrict (Set.Ico 0 (1 : I)) = volume := by
  ext s hs
  simp only [hs, restrict_apply]
  apply MeasureTheory.measure_inter_conull
  simp_all


-- @@ L107-108 verbatim
/-- Encode a standard Borel space into the unit interval. -/
noncomputable def packI [StandardBorelSpace A] : A → I := unpack ∘ pack

-- @@ L109-110 verbatim
/-- Decode the unit-interval representation of a nonempty standard Borel space. -/
noncomputable def unpackI [StandardBorelSpace A] [Nonempty A] : I → A := unpack ∘ pack


-- @@ L112-115 verbatim
@[local simp, local fun_prop]
private lemma measurable_packI [StandardBorelSpace A] : Measurable (packI (A := A)) := by
  unfold packI
  fun_prop


-- @@ L117-122 verbatim
@[local simp, local fun_prop]
private lemma measurable_unpackI
    [StandardBorelSpace A] [Nonempty A]
    : Measurable (unpackI (A := A)) := by
  unfold unpackI
  fun_prop


-- @@ L124-129 verbatim
@[local simp]
private lemma unpackI_packI
    [StandardBorelSpace A] [Nonempty A] {x : A}
    : unpackI (packI x) = x := by
  unfold unpackI packI
  simp_all


-- @@ L131-133 verbatim
private instance [StandardBorelSpace A]
    {μ : Measure A} [IsProbabilityMeasure μ]
    : IsProbabilityMeasure (μ.map packI) := inferInstance


-- @@ L135-138 verbatim
/-- The function `det μ` is a function such that `volume.map (det μ) = μ`. -/
noncomputable def det [StandardBorelSpace A] (μ : Measure A) [IsProbabilityMeasure μ] : I → A :=
  have := MeasureTheory.nonempty_of_isProbabilityMeasure μ
  unpackI ∘ quantile (μ.map packI)


-- @@ L140-151 verbatim
@[fun_prop]
lemma measurable_det
    [StandardBorelSpace B]
    {μ : A → Measure B} [∀ x, IsProbabilityMeasure (μ x)] (hμ : Measurable μ)
    {i : A → I} (hi : Measurable i)
    : Measurable fun x ↦ det (μ x) (i x) := by
  wlog hA : Nonempty A
  · simp only [not_nonempty_iff] at hA
    apply measurable_of_empty
  have hB := MeasureTheory.nonempty_of_isProbabilityMeasure (μ hA.some)
  apply Measurable.comp (measurable_unpackI (A := B))
  fun_prop


-- @@ L153-163 verbatim
@[simp]
lemma eq_det_volume
    [StandardBorelSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    : volume.map (det μ) = μ := by
  rw [det, ← Measure.map_map]
  · rw [eq_quantile_volume, Measure.map_map]
    · simp +unfoldPartialApp only [Function.comp, unpackI_packI, map_id']
    · fun_prop
    · fun_prop
  · fun_prop
  · apply measurable_quantile <;> fun_prop


-- @@ L165-173 verbatim
/-- The function `detf μ` is a function such that `volume.map (detf μ) = μ`. -/
noncomputable def detf [StandardBorelSpace A]
    (μ : Measure A) [IsFiniteMeasure μ]
    (r : Set.Ico 0 (μ Set.univ).toReal) : A :=
  have : NeZero μ := by
    constructor
    rintro rfl
    simpa using r.property
  det ((μ Set.univ)⁻¹ • μ) (normalize r)


-- @@ L175-187 verbatim
@[fun_prop]
lemma measurable_detf
    [StandardBorelSpace A]
    {μ : Measure A} [IsFiniteMeasure μ]
    : Measurable (detf μ) := by
  unfold detf
  simp only
  wlog! hμ : μ ≠ 0
  · subst hμ
    simp only [coe_zero, Pi.ofNat_apply, ENNReal.toReal_zero, ENNReal.inv_zero, smul_zero]
    apply measurable_of_empty
  have : NeZero μ := ⟨hμ⟩
  apply measurable_det <;> fun_prop


-- @@ L189-220 verbatim
@[simp]
lemma eq_detf_volume
    [StandardBorelSpace A] (μ : Measure A) [IsFiniteMeasure μ]
    : volume.map (detf μ) = μ := by
  wlog! hμ : μ ≠ 0
  · subst hμ
    have hIE : IsEmpty (Set.Ico (0 : ℝ) ((0 : Measure A) Set.univ).toReal) := by
      simp_all
    have : (volume : Measure (Set.Ico (0 : ℝ) ((0 : Measure A) Set.univ).toReal)) = 0 := by
      ext s _
      simp only [Measure.coe_zero, Pi.zero_apply]
      rw [show s = ∅ from Set.eq_empty_of_isEmpty s]
      simp only [measure_empty]
    rw [this]
    simp only [Measure.map_zero]
  have : NeZero μ := ⟨hμ⟩
  change map (((μ Set.univ)⁻¹ • μ).det ∘ normalize) (_ • comap normalize volume) = μ
  simp only [ne_eq, measure_ne_top, not_false_eq_true, ENNReal.ofReal_toReal]
  rw [Measure.map_smul _ (by fun_prop), ← map_map, MeasurableEmbedding.map_comap]
  · have : 0 < (μ Set.univ).toReal := by
      rw [(by simp : 0 = ENNReal.toReal 0), ENNReal.toReal_lt_toReal]
      · simp only [measure_univ_pos, ne_eq, hμ, not_false_eq_true]
      · simp only [ne_eq, ENNReal.zero_ne_top, not_false_eq_true]
      · simp only [ne_eq, measure_ne_top, not_false_eq_true]
    simp only [this, range_normalize, volume_restrict_normalize, eq_det_volume]
    rw [smul_smul, ENNReal.mul_inv_cancel]
    · simp only [one_smul]
    · simp only [ne_eq, measure_univ_eq_zero, hμ, not_false_eq_true]
    · simp only [ne_eq, measure_ne_top, not_false_eq_true]
  · apply measurableEmbedding_normalize
  · apply measurable_det <;> fun_prop
  · fun_prop


-- @@ L222-222 verbatim
end MeasureTheory.Measure


-- @@ L224-224 verbatim
namespace MeasureTheory


-- @@ L226-228 verbatim
/-- Splits `I` into two independent copies of `I` via the determinizing map of the
product Lebesgue measure on `I × I`. -/
noncomputable def splitI : I → I × I := Measure.det volume


-- @@ L230-233 verbatim
@[simp, fun_prop]
lemma measurable_splitI : Measurable splitI := by
  unfold splitI
  apply Measure.measurable_det <;> fun_prop


-- @@ L235-237 verbatim
lemma measurePreserving_splitI : MeasurePreserving splitI where
  measurable := by fun_prop
  map_eq := by simp only [splitI, Measure.eq_det_volume]


-- @@ L239-239 verbatim
end MeasureTheory
