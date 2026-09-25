/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.Operators.Multiplication
public import Physlib.QuantumMechanics.HilbertSpaces.SpaceD.PolyBddSchwartzSubmodule
public import Physlib.SpaceAndTime.Space.Norm.Regularized

-- @@ L11-50 verbatim
/-!

# Position operators

## i. Overview

In this module we introduce several position operators for quantum mechanics on `Space d`.

## ii. Key results

Definitions:
- `positionCLM` : (components of) the position vector operator acting on Schwartz maps
    `𝓢(Space d, ℂ)` by multiplication by `xᵢ`.
- `radiusRegPowCLM` : operator acting on Schwartz maps by multiplication by
    `(‖x‖² + ε²)^(s/2)`, a smooth regularization of `‖x‖ˢ`.
- `positionOperator` : a self-adjoint multiplication operator acting on `SpaceDHilbertSpace d`.
- `readiusRegPowOperator` : a self-adjoint multiplication operator acting on `SpaceDHilbertSpace d`.

Notation:
- `𝐱` for `positionCLM`
- `𝐫₀` for `radiusRegPowCLM`
- `𝐫` for `radiusPowLM`

## iii. Table of contents

- A. Schwartz operators
  - A.1. Position vector
  - A.2. Radius powers (regularized)
  - A.3. Radius powers
    - A.3.1. As limit of regularized operators
- B. Unbounded operators
  - B.1. Position vector
  - B.2. Radius powers (regularized)
  - B.3. Radius powers
    - B.3.1. As limit of regularized operators

## iv. References

* None.
-/


-- @@ L52-52 verbatim
@[expose] public section


-- @@ L54-54 verbatim
namespace QuantumMechanics


-- @@ L56-56 verbatim
open Filter

-- @@ L57-57 verbatim
open MeasureTheory

-- @@ L58-58 verbatim
open SchwartzMap

-- @@ L59-59 verbatim
open SpaceDHilbertSpace

-- @@ L60-60 verbatim
open SchwartzSubmodule PolyBddSchwartzSubmodule


-- @@ L62-62 verbatim
variable {d : ℕ} (μ : Measure (Space d)) (i : Fin d)


-- @@ L64-66 verbatim
/-!
## A. Schwartz operators
-/


-- @@ L68-68 verbatim
noncomputable section

-- @@ L69-69 verbatim
open Space Function


-- @@ L71-73 verbatim
/-!
### A.1. Position vector
-/


-- @@ L75-78 verbatim
/-- Component `i` of the position operator is the continuous linear map
  from `𝓢(Space d, ℂ)` to itself which maps `ψ` to `xᵢψ`. -/
def positionCLM : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (Complex.ofRealCLM ∘L coordCLM i)


-- @@ L80-81 verbatim
@[inherit_doc positionCLM]
notation "𝐱" => positionCLM


-- @@ L83-84 verbatim
@[inherit_doc positionCLM]
notation "𝐱[" d' "]" => positionCLM (d := d')


-- @@ L86-90 expanded
lemma positionCLM_apply_fun (ψ : 𝓢(Space d, ℂ)) : positionCLM i ψ = (fun x : Space d ↦ x i) • ⇑ψ :=
  by
  ext
  simp only [positionCLM]
  erw [smulLeftCLM_apply_apply (g := Complex.ofRealCLM ∘ (coordCLM i)) (by fun_prop)]
  simp [coordCLM_apply, coord_apply]


-- @@ L92-94 expanded
@[simp]
lemma positionCLM_apply (ψ : 𝓢(Space d, ℂ)) (x : Space d) : positionCLM i ψ x = x i * ψ x := by
  simp [positionCLM_apply_fun]


-- @@ L96-98 verbatim
/-!
### A.2. Radius powers (regularized)
-/


-- @@ L100-103 verbatim
/-- The radius operator to power `s`, regularized by `ε ≠ 0`, is the continuous linear map
  from `𝓢(Space d, ℂ)` to itself which maps `ψ` to `(‖x‖² + ε²)^(s/2) • ψ`. -/
def radiusRegPowCLM {d : ℕ} (ε : ℝˣ) (s : ℝ) : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (Complex.ofReal ∘ normRegularizedPow d ε s)


-- @@ L105-106 verbatim
@[inherit_doc radiusRegPowCLM]
notation "𝐫₀" => radiusRegPowCLM


-- @@ L108-109 verbatim
@[inherit_doc radiusRegPowCLM]
notation "𝐫₀[" d' "]" => radiusRegPowCLM (d := d')


-- @@ L111-116 expanded
lemma radiusRegPowCLM_apply_fun {d : ℕ} (ε : ℝˣ) (s : ℝ) (ψ : 𝓢(Space d, ℂ)) :
    radiusRegPowCLM ε s ψ = fun x ↦ (‖x‖ ^ 2 + ε ^ 2) ^ (s / 2) • ψ x :=
  by
  ext x
  dsimp [radiusRegPowCLM]
  refine smulLeftCLM_apply_apply ?_ ψ x
  exact HasTemperateGrowth.comp (by fun_prop) (normRegularizedPow_hasTemperateGrowth d ε s)


-- @@ L118-121 expanded
@[simp]
lemma radiusRegPowCLM_apply {d : ℕ} (ε : ℝˣ) (s : ℝ) (ψ : 𝓢(Space d, ℂ)) (x : Space d) :
    radiusRegPowCLM ε s ψ x = (‖x‖ ^ 2 + ε ^ 2) ^ (s / 2) • ψ x := by rw [radiusRegPowCLM_apply_fun]


-- @@ L123-127 expanded
@[simp]
lemma radiusRegPowCLM_comp_eq {d : ℕ} (ε : ℝˣ) (s t : ℝ) :
    (radiusRegPowCLM (d := d)) ε s ∘L radiusRegPowCLM ε t = radiusRegPowCLM ε (s + t) :=
  by
  ext ψ x
  simp [add_div, Real.rpow_add (norm_sq_add_unit_sq_pos ε x), mul_assoc]


-- @@ L129-133 expanded
@[simp]
lemma radiusRegPowCLM_zero {d : ℕ} (ε : ℝˣ) :
    radiusRegPowCLM ε 0 = ContinuousLinearMap.id ℂ 𝓢(Space d, ℂ) :=
  by
  ext
  simp


-- @@ L135-138 expanded
lemma positionSqCLM_eq {d : ℕ} (ε : ℝˣ) :
    ∑ i, positionCLM i ∘L positionCLM i =
      radiusRegPowCLM ε 2 - ε.1 ^ 2 • ContinuousLinearMap.id ℂ 𝓢(Space d, ℂ) :=
  by
  ext
  simp [Space.norm_sq_eq, add_mul, ← mul_assoc, ← pow_two, Finset.sum_mul]


-- @@ L140-142 verbatim
/-!
### A.3. Radius powers
-/


-- @@ L144-149 verbatim
/-- The radius operator to power `s` is the linear map from `𝓢(Space d, ℂ)` to `Space d → ℂ` that
  maps `ψ` to `x ↦ ‖x‖ˢψ(x)` (which is 'nearly' Schwartz for general `s`). -/
def radiusPowLM {d : ℕ} (s : ℝ) : 𝓢(Space d, ℂ) →ₗ[ℂ] Space d → ℂ where
  toFun ψ := (fun x : Space d ↦ ‖x‖ ^ s) • ψ
  map_add' _ _ := by rw [← smul_add]; rfl
  map_smul' _ _ := by rw [smul_comm]; rfl


-- @@ L151-152 verbatim
@[inherit_doc radiusPowLM]
notation "𝐫" => radiusPowLM


-- @@ L154-155 verbatim
@[inherit_doc radiusPowLM]
notation "𝐫[" d' "]" => radiusPowLM (d := d')


-- @@ L157-158 expanded
lemma radiusPowLM_apply_fun {d : ℕ} (s : ℝ) (ψ : 𝓢(Space d, ℂ)) :
    radiusPowLM s ψ = fun x ↦ ‖x‖ ^ s • ψ x :=
  rfl


-- @@ L160-163 expanded
@[simp]
lemma radiusPowLM_apply {d : ℕ} (s : ℝ) (ψ : 𝓢(Space d, ℂ)) (x : Space d) :
    radiusPowLM s ψ x = ‖x‖ ^ s • ψ x := by rw [radiusPowLM_apply_fun]


-- @@ L165-173 expanded
/-- `x ↦ ‖x‖ˢψ(x)` is smooth away from `x = 0`. -/
@[fun_prop]
lemma radiusPowLM_apply_contDiffAt {d : ℕ} (s : ℝ) (n : ℕ∞) (ψ : 𝓢(Space d, ℂ)) {x : Space d}
    (hx : x ≠ 0) : ContDiffAt ℝ n (radiusPowLM s ψ) x :=
  by
  refine ContDiffAt.smul ?_ (ψ.contDiffAt n)
  have h (x : Space d) : ‖x‖ ^ s = (inner ℝ x x) ^ (s / 2) := by
    simp [← Real.rpow_natCast_mul, mul_div_cancel₀]
  simp only [h]
  exact ContDiffAt.rpow_const_of_ne (by fun_prop) (inner_self_ne_zero.mpr hx)


-- @@ L175-181 expanded
/-- `x ↦ ‖x‖ˢψ(x)` is strongly measurable. -/
@[fun_prop]
lemma radiusPowLM_apply_stronglyMeasurable {d : ℕ} (s : ℝ) (ψ : 𝓢(Space d, ℂ)) :
    StronglyMeasurable (radiusPowLM s ψ) :=
  by
  rw [radiusPowLM_apply_fun]
  exact
    StronglyMeasurable.smul (f := fun x : Space d => ‖x‖ ^ s) (by measurability)
      ψ.continuous.stronglyMeasurable


-- @@ L183-253 expanded
/-- `x ↦ ‖x‖ˢψ(x)` is square-integrable provided `s` is not too negative. -/
lemma radiusPowLM_apply_memHS {d : ℕ} (s : ℝ) (ψ : 𝓢(Space d, ℂ)) (a : ℕ)
    (hψ : ψ ∈ PolyBddSchwartzMap d a) (h : 0 < d + 2 * (a + s)) : MemHS (radiusPowLM s ψ) :=
  by
  rcases Nat.eq_zero_or_pos d with (rfl | hd)
  · simp only [MemHS, MemLp.of_discrete]
  · have : NeZero d := ⟨hd.ne'⟩
    refine (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr ⟨by fun_prop, ?_⟩
    suffices ∫⁻ (x : Space d), ‖‖ψ x‖ ^ 2 * ‖x‖ ^ (2 * s)‖ₑ < ⊤
      by
      have hInt (x : Space d) : ‖radiusPowLM s ψ x‖ ^ 2 = ‖ψ x‖ ^ 2 * ‖x‖ ^ (2 * s) := by
        simp [radiusPowLM, mul_pow, mul_comm, Real.rpow_mul]
      simpa only [HasFiniteIntegral, hInt]
    have lintegral_lt_top_aux :
      ∀ {S : Set (Space d)} {C p : ℝ},
        IntegrableOn (fun x ↦ ‖x‖ ^ p) S →
          ∀ {G : Space d → ENNReal},
            ∫⁻ x in S, G x ≤ ∫⁻ x in S, ‖C ^ 2‖ₑ * ‖‖x‖ ^ p‖ₑ → ∫⁻ x in S, G x < ⊤ :=
      by
      intro S C p hp G hG
      refine hG.trans_lt ?_
      rw [lintegral_const_mul _ (by fun_prop)]
      exact ENNReal.mul_lt_top enorm_lt_top hp.hasFiniteIntegral
    rw [← lintegral_add_compl _ (measurableSet_ball (x := 0) (ε := 1)), ENNReal.add_lt_top]
    constructor
    · -- `‖x‖ < 1`: bound `‖ψ x‖` by `‖x‖ᵃ`
      
      obtain ⟨C, hC_pos, hC⟩ := hψ a (le_refl _)
      suffices hBound : ∀ᵐ x, ‖‖ψ x‖ ^ 2 * ‖x‖ ^ (2 * s)‖ₑ ≤ ‖C ^ 2‖ₑ * ‖‖x‖ ^ (2 * (a + s))‖ₑ by
        exact
          lintegral_lt_top_aux ((integrableOn_norm_rpow_ball_iff Real.zero_lt_one _).mpr h)
            (setLIntegral_mono_ae' measurableSet_ball (Eventually.mono hBound fun _ h' _ ↦ h'))
      apply ae_iff.mpr
      refine measure_mono_null ?_ (measure_singleton 0)
      intro x hx
      by_contra hx'
      apply hx
      apply norm_pos_iff.mpr at hx'
      simp_rw [← enorm_mul, enorm_le_iff_norm_le, mul_add, Real.rpow_add hx', norm_mul, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      simp_rw [← Nat.cast_two (R := ℝ), mul_comm, Real.rpow_mul_natCast hx'.le, norm_pow, ← mul_pow,
        norm_norm, Real.norm_eq_abs, abs_of_pos hC_pos, abs_of_nonneg (Real.rpow_nonneg hx'.le _)]
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
      apply (inv_mul_le_iff₀' (by positivity)).mp
      rw [← Real.rpow_neg_one, ← Real.rpow_mul hx'.le, mul_comm _ (-1), neg_mul, one_mul,
        Real.rpow_neg_natCast]
      exact hC x
    · -- `1 ≤ ‖x‖`: bound `‖ψ x‖` by a suitable power of `‖x‖`
      
      obtain ⟨C, hC_pos, hC⟩ := ψ.decay (⌈s⌉.toNat + d) 0
      simp only [norm_iteratedFDeriv_zero, ← Real.rpow_natCast, Nat.cast_add] at hC
      suffices hBound :
        ∀ x ∈ (Metric.ball 0 1)ᶜ, ‖‖ψ x‖ ^ 2 * ‖x‖ ^ (2 * s)‖ₑ ≤ ‖C ^ 2‖ₑ * ‖‖x‖ ^ (-2 * d : ℝ)‖ₑ
        by
        have hd' : (d + -2 * d : ℝ) < 0 := by simp [hd]
        exact
          lintegral_lt_top_aux ((integrableOn_norm_rpow_ball_compl_iff zero_lt_one _).mpr hd')
            (setLIntegral_mono' (by measurability) hBound)
      intro x hx
      simp only [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] at hx
      simp_rw [← enorm_mul, enorm_le_iff_norm_le, norm_mul, norm_pow, Real.norm_eq_abs, sq_abs,
        Real.abs_rpow_of_nonneg (norm_nonneg _), abs_norm]
      have hx' : 0 < ‖x‖ := by linarith
      have hψ : ‖ψ x‖ ≤ C * ‖x‖ ^ (-(⌈s⌉.toNat + d) : ℝ) :=
        by
        rw [Real.rpow_neg hx'.le]
        exact (le_mul_inv_iff₀' <| Real.rpow_pos_of_pos hx' _).mpr (hC x)
      calc
        _ ≤ (C * ‖x‖ ^ (-(⌈s⌉.toNat + d) : ℝ)) ^ 2 * ‖x‖ ^ (2 * s) :=
          by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hx'.le _)
          exact pow_le_pow_left₀ (norm_nonneg _) hψ 2
        _ = C ^ 2 * ‖x‖ ^ (-2 * d : ℝ) * ‖x‖ ^ (2 * (s - ⌈s⌉.toNat) : ℝ) :=
          by
          simp_rw [mul_pow, ← Real.rpow_mul_natCast hx'.le, mul_assoc, ← Real.rpow_add hx']
          ring_nf
      suffices s ≤ ⌈s⌉.toNat
        by
        have h' : 0 < C ^ 2 * ‖x‖ ^ (-2 * d : ℝ) :=
          mul_pos (sq_pos_of_pos hC_pos) (Real.rpow_pos_of_pos hx' _)
        apply (mul_le_iff_le_one_right h').mpr
        exact Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)
      exact (Int.le_ceil s).trans (by exact_mod_cast Int.self_le_toNat ⌈s⌉)


-- @@ L255-257 verbatim
/-!
#### A.3.1. As limit of regularized operators
-/


-- @@ L259-261 verbatim
/-- Neighborhoods of "0" in the non-zero reals, i.e. those sets containing `(-ε,0) ∪ (0,ε) ⊆ ℝˣ`
  for some `ε > 0`. -/
abbrev nhdsZeroUnits : Filter ℝˣ := comap (Units.coeHom ℝ) (nhds 0)


-- @@ L263-267 verbatim
instance : NeBot nhdsZeroUnits := by
  refine comap_neBot fun t ht ↦ ?_
  obtain ⟨ε, hε_pos, hε⟩ := Metric.mem_nhds_iff.mp ht
  use Units.mk0 (ε / 2) (by linarith)
  exact hε (by simp [abs_of_pos, hε_pos])


-- @@ L269-277 expanded
/-- `𝐫[ε,s] ψ` converges pointwise to `𝐫[s] ψ` as `ε → 0` except perhaps at `x = 0`. -/
lemma radiusRegPow_tendsto_radiusPow {d : ℕ} (s : ℝ) (ψ : 𝓢(Space d, ℂ)) {x : Space d}
    (hx : x ≠ 0) :
    Tendsto (fun ε ↦ radiusRegPowCLM ε s ψ x) nhdsZeroUnits (nhds (radiusPowLM s ψ x)) :=
  by
  have hpow : ‖x‖ ^ s = (‖x‖ ^ 2 + 0 ^ 2) ^ (s / 2) := by
    simp [← Real.rpow_natCast_mul, mul_div_cancel₀]
  simp only [radiusRegPowCLM_apply, radiusPowLM_apply, Complex.real_smul, hpow]
  refine Tendsto.mul_const (ψ x) <| Tendsto.ofReal ?_
  refine Tendsto.rpow_const ?_ (Or.inl <| by simp [hx])
  exact Tendsto.const_add _ <| Tendsto.pow tendsto_comap 2


-- @@ L279-293 expanded
/-- `𝐫[ε,s] ψ` converges pointwise to `𝐫[s] ψ` as `ε → 0` provided `𝐫[ε,s] ψ 0` is bounded. -/
lemma radiusRegPow_tendsto_radiusPow' {d : ℕ} (s : ℝ) (ψ : 𝓢(Space d, ℂ)) (h : 0 ≤ s ∨ ψ 0 = 0) :
    Tendsto (fun ε ↦ ⇑(radiusRegPowCLM ε s ψ)) nhdsZeroUnits (nhds (radiusPowLM s ψ)) :=
  by
  refine tendsto_pi_nhds.mpr fun x ↦ ?_
  rcases eq_zero_or_neZero x with (rfl | hx)
  · rcases h with (hs | hψ)
    · simp only [radiusRegPowCLM_apply, radiusPowLM_apply, Complex.real_smul, norm_zero, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add]
      have : (0 : ℝ) ^ s = (0 ^ 2) ^ (s / 2) := by
        rw [← Real.rpow_natCast_mul (le_refl 0), Nat.cast_ofNat, mul_div_cancel₀ s (by norm_num)]
      rw [this]
      refine Tendsto.mul_const (ψ 0) <| Tendsto.ofReal ?_
      exact Tendsto.rpow_const (Tendsto.pow tendsto_comap 2) (Or.inr <| by linarith)
    · simp [hψ]
  · exact radiusRegPow_tendsto_radiusPow s ψ hx.ne


-- @@ L295-303 expanded
/-- a.e. version of `radiusRegPow_tendsto_radiusPow` -/
lemma radiusRegPow_ae_tendsto_radiusPow {d : ℕ} [NeZero d] (s : ℝ) (ψ : 𝓢(Space d, ℂ)) :
    ∀ᵐ x, Tendsto (fun ε ↦ radiusRegPowCLM ε s ψ x) nhdsZeroUnits (nhds (radiusPowLM s ψ x)) :=
  by
  apply ae_iff.mpr
  suffices h :
    {x | ¬Tendsto (fun ε ↦ radiusRegPowCLM ε s ψ x) nhdsZeroUnits (nhds (radiusPowLM s ψ x))} ⊆ {0}
    by exact measure_mono_null h (measure_singleton 0)
  intro x hx
  by_contra hx'
  exact hx <| radiusRegPow_tendsto_radiusPow s ψ hx'


-- @@ L305-320 expanded
lemma radiusRegPow_ae_tendsto_iff {d : ℕ} [NeZero d] {s : ℝ} {ψ : 𝓢(Space d, ℂ)} {φ : Space d → ℂ} :
    (∀ᵐ x, Tendsto (fun ε ↦ radiusRegPowCLM ε s ψ x) nhdsZeroUnits (nhds (φ x))) ↔
      φ =ᵐ[volume] radiusPowLM s ψ :=
  by
  let t₁ := {x | ¬Tendsto (fun ε ↦ radiusRegPowCLM ε s ψ x) nhdsZeroUnits (nhds (φ x))}
  let t₂ := {x | φ x ≠ radiusPowLM s ψ x}
  show volume t₁ = 0 ↔ volume t₂ = 0
  suffices heq : t₁ ∪ {0} = t₂ ∪ {0}
    by
    have hUnion : ∀ t : Set (Space d), volume t = 0 ↔ volume (t ∪ {0}) = 0 := fun _ ↦ by
      simp only [measure_union_null_iff, measure_singleton, and_true]
    rw [hUnion t₁, hUnion t₂, heq]
  ext x
  rcases eq_zero_or_neZero x with (rfl | hx)
  · simp
  · simp only [Set.union_singleton, Set.mem_insert_iff, hx.ne, false_or]
    have hLim := radiusRegPow_tendsto_radiusPow s ψ hx.ne
    exact not_congr ⟨fun h ↦ tendsto_nhds_unique h hLim, fun h ↦ h ▸ hLim⟩


-- @@ L322-322 verbatim
end


-- @@ L324-326 verbatim
/-!
## B. Unbounded operators
-/


-- @@ L328-328 verbatim
noncomputable section

-- @@ L329-329 verbatim
open Space


-- @@ L331-333 verbatim
/-!
### B.1. Position vector
-/


-- @@ L335-337 expanded
/-- The operator on `SpaceDHilbertSpace d` acting by multiplication by `fun x ↦ xᵢ`. -/
def positionOperator : SpaceDHilbertSpace d μ →ₗ.[ℂ] SpaceDHilbertSpace d μ :=
  mulOperator μ (Complex.ofRealCLM ∘L Space.coordCLM i)


-- @@ L339-340 verbatim
@[inherit_doc positionOperator]
notation "𝓧" => positionOperator


-- @@ L342-343 expanded
lemma positionOperator_hasDenseDomain : (positionOperator μ i).HasDenseDomain :=
  mulOperator_hasDenseDomain (by fun_prop)


-- @@ L345-346 expanded
lemma positionOperator_isSelfAdjoint [IsFiniteMeasureOnCompacts μ] :
    IsSelfAdjoint (positionOperator μ i) :=
  mulOperator_isSelfAdjoint_ofReal (by fun_prop) (by ext; simp)


-- @@ L348-349 expanded
lemma positionOperator_isUnbounded [IsFiniteMeasureOnCompacts μ] :
    (positionOperator μ i).IsUnbounded :=
  LinearPMap.IsSelfAdjoint.isUnbounded (positionOperator_isSelfAdjoint μ i)


-- @@ L351-353 verbatim
/-!
### B.2. Radius powers (regularized)
-/


-- @@ L355-359 expanded
/-- The operator on `SpaceDHilbertSpace d` acting by multiplication by
  `fun x ↦ (‖x‖² + ε²)^(s/2)`. -/
def radiusRegPowOperator (ε : ℝˣ) (s : ℝ) : SpaceDHilbertSpace d μ →ₗ.[ℂ] SpaceDHilbertSpace d μ :=
  mulOperator μ (Complex.ofReal ∘ normRegularizedPow d ε s)


-- @@ L361-362 verbatim
@[inherit_doc radiusRegPowOperator]
notation "𝓡₀" => radiusRegPowOperator


-- @@ L364-365 expanded
lemma radiusRegPowOperator_hasDenseDomain (ε : ℝˣ) (s : ℝ) :
    (radiusRegPowOperator μ ε s).HasDenseDomain :=
  mulOperator_hasDenseDomain (by fun_prop)


-- @@ L367-369 expanded
lemma radiusRegPowOperator_isSelfAdjoint [IsFiniteMeasureOnCompacts μ] (ε : ℝˣ) (s : ℝ) :
    IsSelfAdjoint (radiusRegPowOperator μ ε s) :=
  mulOperator_isSelfAdjoint_ofReal (by fun_prop) (by ext; simp)


-- @@ L371-373 expanded
lemma radiusRegPowOperator_isUnbounded [IsFiniteMeasureOnCompacts μ] (ε : ℝˣ) (s : ℝ) :
    (radiusRegPowOperator μ ε s).IsUnbounded :=
  LinearPMap.IsSelfAdjoint.isUnbounded (radiusRegPowOperator_isSelfAdjoint μ ε s)


-- @@ L375-377 verbatim
/-!
### B.3. Radius powers
-/


-- @@ L379-381 expanded
/-- The operator on `SpaceDHilbertSpace d` acting by multiplication by `fun x ↦ ‖x‖ˢ`. -/
def radiusPowOperator (s : ℝ) : SpaceDHilbertSpace d μ →ₗ.[ℂ] SpaceDHilbertSpace d μ :=
  mulOperator μ (Complex.ofReal ∘ fun x ↦ ‖x‖ ^ s)


-- @@ L383-384 verbatim
@[inherit_doc radiusPowOperator]
notation "𝓡" => radiusPowOperator


-- @@ L386-387 expanded
lemma radiusPowOperator_hasDenseDomain (s : ℝ) : (radiusPowOperator μ s).HasDenseDomain :=
  mulOperator_hasDenseDomain (Measurable.aestronglyMeasurable (by fun_prop))


-- @@ L389-391 expanded
lemma radiusPowOperator_isSelfAdjoint [IsFiniteMeasureOnCompacts μ] (s : ℝ) :
    IsSelfAdjoint (radiusPowOperator μ s) :=
  mulOperator_isSelfAdjoint_ofReal (Measurable.aestronglyMeasurable (by fun_prop)) (by ext; simp)


-- @@ L393-394 expanded
lemma radiusPowOperator_isUnbounded [IsFiniteMeasureOnCompacts μ] (s : ℝ) :
    (radiusPowOperator μ s).IsUnbounded :=
  LinearPMap.IsSelfAdjoint.isUnbounded (radiusPowOperator_isSelfAdjoint μ s)


-- @@ L396-396 verbatim
open Complex


-- @@ L398-403 verbatim
private lemma add_floor_toNat_pos_aux (d : ℕ) (s : ℝ) :
    0 < d + 2 * (⌊1 - d / 2 - s⌋.toNat + s) := by
  let n : ℤ := ⌊1 - d / 2 - s⌋
  have hn₁ : 1 - d / 2 - s < n + 1 := Int.lt_floor_add_one _
  have hn₂ : (n : ℝ) ≤ n.toNat := Int.cast_le.mpr (Int.self_le_toNat _)
  linarith


-- @@ L405-409 expanded
lemma radiusPowLM_apply_polyBddSchwartz_memHS {d : ℕ} {s : ℝ}
    (ψ : PolyBddSchwartzSubmodule d ⌊1 - d / 2 - s⌋.toNat) :
    MemHS ((radiusPowLM (d := d)) s ((polyBddSchwartzEquiv volume).symm ψ)) :=
  let f := (polyBddSchwartzEquiv volume).symm ψ
  radiusPowLM_apply_memHS s f.1 ⌊1 - d / 2 - s⌋.toNat f.2 (add_floor_toNat_pos_aux d s)


-- @@ L411-419 expanded
lemma radiusPowOperator_domain_ge {d : ℕ} (s : ℝ) :
    PolyBddSchwartzSubmodule d ⌊1 - d / 2 - s⌋.toNat ≤ (radiusPowOperator volume s).domain :=
  by
  intro ψ hψ
  let f := (polyBddSchwartzEquiv volume).symm ⟨ψ, hψ⟩
  apply mem_mulOperator_domain_iff.mpr
  refine MemHS.ae_eq (f := radiusPowLM s f.1) ?_ ?_
  · filter_upwards [polyBddSchwartzEquiv_coe_ae f]
    simp_all [f]
  · exact radiusPowLM_apply_memHS s f.1 _ f.2 (add_floor_toNat_pos_aux d s)


-- @@ L421-421 verbatim
end

-- @@ L422-422 verbatim
end QuantumMechanics
