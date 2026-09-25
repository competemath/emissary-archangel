/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Physlib.StatisticalMechanics.BoltzmannConstant

-- @@ L11-23 verbatim
/-!

# Temperature

In this module we define the type `Temperature`, corresponding to the temperature in a given
(but arbitrary) set of units which have absolute zero at zero.

This is the version of temperature most often used in undergraduate and
non-mathematical physics.

The choice of units can be made on a case-by-case basis, as long as they are done consistently.

-/


-- @@ L25-25 verbatim
@[expose] public section


-- @@ L27-27 verbatim
open NNReal


-- @@ L29-33 verbatim
/-- The type `Temperature` represents the temperature in a given (but arbitrary) set of units
  (preserving zero). It currently wraps `ℝ≥0`, i.e., absolute temperature in nonnegative reals. -/
structure Temperature where
  /-- The nonnegative real value of the temperature. -/
  val : ℝ≥0


-- @@ L35-35 verbatim
namespace Temperature

-- @@ L36-36 verbatim
open Constants


-- @@ L38-39 verbatim
/-- Coercion to `ℝ≥0`. -/
instance : Coe Temperature ℝ≥0 := ⟨fun T => T.val⟩


-- @@ L41-42 verbatim
/-- The underlying real-number associated with the temperature. -/
noncomputable def toReal (T : Temperature) : ℝ := NNReal.toReal T.val


-- @@ L44-45 verbatim
/-- Coercion to `ℝ`. -/
noncomputable instance : Coe Temperature ℝ := ⟨toReal⟩


-- @@ L47-49 verbatim
/-- Topology on `Temperature` induced from `ℝ≥0`. -/
instance : TopologicalSpace Temperature :=
  TopologicalSpace.induced (fun T : Temperature => (T.val : ℝ≥0)) inferInstance


-- @@ L51-51 verbatim
instance : Zero Temperature := ⟨⟨0⟩⟩


-- @@ L53-54 verbatim
@[ext] lemma ext {T₁ T₂ : Temperature} (h : T₁.val = T₂.val) : T₁ = T₂ := by
  cases T₁; cases T₂; cases h; rfl


-- @@ L56-59 verbatim
/-- The inverse temperature defined as `1/(kB * T)` in a given, but arbitrary set of units.
  This has dimensions equivalent to `Energy`. -/
noncomputable def β (T : Temperature) : ℝ≥0 :=
  ⟨1 / (kB * (T : ℝ)), div_nonneg zero_le_one (mul_nonneg kB_nonneg T.val.2)⟩


-- @@ L61-61 verbatim
lemma β_toReal (T : Temperature) : (β T : ℝ) = 1 / (kB * (T : ℝ)) := rfl


-- @@ L63-65 verbatim
/-- The temperature associated with a given inverse temperature `β`. -/
noncomputable def ofβ (β : ℝ≥0) : Temperature :=
  ⟨⟨1 / (kB * β), div_nonneg zero_le_one (mul_nonneg kB_nonneg β.2)⟩⟩


-- @@ L67-73 verbatim
lemma ofβ_eq : ofβ = fun β => ⟨⟨1 / (kB * β), by
    apply div_nonneg
    · exact zero_le_one
    · apply mul_nonneg
      · exact kB_nonneg
      · exact β.2⟩⟩ := by
  rfl


-- @@ L75-79 verbatim
@[simp]
lemma β_ofβ (β' : ℝ≥0) : β (ofβ β') = β' := by
  apply NNReal.coe_injective
  show 1 / (kB * (1 / (kB * ↑β'))) = ↑β'
  rw [mul_one_div, one_div_div, mul_div_cancel_left₀ _ kB_ne_zero]


-- @@ L81-81 verbatim
lemma ofβ_toReal (β : ℝ≥0) : (ofβ β).toReal = 1 / (kB * (β : ℝ)) := rfl


-- @@ L83-88 verbatim
@[simp]
lemma ofβ_β (T : Temperature) : ofβ (β T) = T := by
  apply Temperature.ext
  apply NNReal.coe_injective
  show 1 / (kB * (1 / (kB * (T : ℝ)))) = (T : ℝ)
  rw [mul_one_div, one_div_div, mul_div_cancel_left₀ _ kB_ne_zero]


-- @@ L90-93 verbatim
/-- Positivity of `β` from positivity of temperature. -/
lemma beta_pos (T : Temperature) (hT_pos : 0 < T.val) : 0 < (T.β : ℝ) := by
  rw [β_toReal]
  exact one_div_pos.mpr (mul_pos kB_pos (by exact_mod_cast hT_pos))


-- @@ L95-95 verbatim
/-! ### Regularity of `ofβ` -/


-- @@ L97-97 verbatim
open Filter Topology


-- @@ L99-108 verbatim
lemma ofβ_continuousOn : ContinuousOn (ofβ : ℝ≥0 → Temperature) (Set.Ioi 0) := by
  have hg : ContinuousOn (fun b : ℝ≥0 => (1 : ℝ) / (kB * (b : ℝ))) (Set.Ioi 0) := by
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro b hb
    exact ne_of_gt (mul_pos kB_pos (by exact_mod_cast hb))
  have hind : Topology.IsInducing (fun T : Temperature => (T.val : ℝ≥0)) := ⟨rfl⟩
  rw [hind.continuousOn_iff]
  refine (continuous_real_toNNReal.comp_continuousOn hg).congr ?_
  intro b hb
  exact (Real.toNNReal_of_nonneg (div_nonneg zero_le_one (mul_nonneg kB_nonneg b.2))).symm


-- @@ L110-120 verbatim
lemma ofβ_differentiableOn :
    DifferentiableOn ℝ (fun (x : ℝ) => ((ofβ (Real.toNNReal x)).val : ℝ)) (Set.Ioi 0) := by
  refine DifferentiableOn.congr (f := fun x => 1 / (kB * x)) ?_ ?_
  · refine DifferentiableOn.fun_div ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · intro x hx
      exact mul_ne_zero kB_ne_zero (ne_of_gt hx)
  · intro x hx
    rw [show ((ofβ (Real.toNNReal x)).val : ℝ) = (ofβ (Real.toNNReal x)).toReal from rfl,
        ofβ_toReal, Real.coe_toNNReal x hx.le]


-- @@ L122-122 verbatim
/-! ### Convergence -/


-- @@ L124-124 verbatim
open Filter Topology


-- @@ L126-130 verbatim
/-- Eventually, `ofβ β` is positive as β → ∞`. -/
lemma eventually_pos_ofβ : ∀ᶠ b : ℝ≥0 in atTop, ((Temperature.ofβ b : Temperature) : ℝ) > 0 := by
  filter_upwards [eventually_gt_atTop 0] with b hb
  have : 0 < (1 : ℝ) / (kB * (b : ℝ)) := one_div_pos.mpr (mul_pos kB_pos (by exact_mod_cast hb))
  simpa [ofβ_toReal] using this


-- @@ L132-138 verbatim
/-- General helper: for any `a > 0`, we have `1 / (a * b) → 0` as `b → ∞` in `ℝ≥0`. -/
private lemma tendsto_const_inv_mul_atTop (a : ℝ) (ha : 0 < a) :
    Tendsto (fun b : ℝ≥0 => (1 : ℝ) / (a * (b : ℝ))) atTop (𝓝 (0 : ℝ)) := by
  have h : Tendsto (fun b : ℝ≥0 => a * (b : ℝ)) atTop atTop :=
    (NNReal.tendsto_coe_atTop.2 tendsto_id).const_mul_atTop ha
  simp only [one_div]
  exact h.inv_tendsto_atTop


-- @@ L140-144 verbatim
/-- Core convergence: as β → ∞, `toReal (ofβ β) → 0` in `ℝ`. -/
lemma tendsto_toReal_ofβ_atTop :
    Tendsto (fun b : ℝ≥0 => (Temperature.ofβ b : ℝ))
      atTop (𝓝 (0 : ℝ)) :=
  tendsto_const_inv_mul_atTop kB kB_pos


-- @@ L146-151 verbatim
/-- As β → ∞, T = ofβ β → 0+ in ℝ (within Ioi 0). -/
lemma tendsto_ofβ_atTop :
    Tendsto (fun b : ℝ≥0 => (Temperature.ofβ b : ℝ))
      atTop (nhdsWithin 0 (Set.Ioi 0)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨tendsto_toReal_ofβ_atTop, ?_⟩
  simpa using eventually_pos_ofβ


-- @@ L153-153 verbatim
/-! ### Conversion to and from `ℝ≥0` -/


-- @@ L155-155 verbatim
open Constants


-- @@ L157-158 verbatim
/-- Build a `Temperature` directly from a nonnegative real. -/
@[simp] def ofNNReal (t : ℝ≥0) : Temperature := ⟨t⟩


-- @@ L160-161 verbatim
@[simp]
lemma ofNNReal_val (t : ℝ≥0) : (ofNNReal t).val = t := rfl


-- @@ L163-164 verbatim
@[simp]
lemma coe_ofNNReal_coe (t : ℝ≥0) : ((ofNNReal t : Temperature) : ℝ≥0) = t := rfl


-- @@ L166-167 verbatim
@[simp]
lemma coe_ofNNReal_real (t : ℝ≥0) : ((⟨t⟩ : Temperature) : ℝ) = t := rfl


-- @@ L169-172 verbatim
/-- Convenience: build a temperature from a real together with a proof of nonnegativity. -/
@[simp]
noncomputable def ofRealNonneg (t : ℝ) (ht : 0 ≤ t) : Temperature :=
  ofNNReal ⟨t, ht⟩


-- @@ L174-176 verbatim
@[simp]
lemma ofRealNonneg_val {t : ℝ} (ht : 0 ≤ t) :
    (ofRealNonneg t ht).val = ⟨t, ht⟩ := rfl


-- @@ L178-178 verbatim
/-! ### Calculus relating T and β -/


-- @@ L180-180 verbatim
open Set

-- @@ L181-181 verbatim
open scoped ENNReal


-- @@ L183-186 verbatim
/-- Map a real `t` to the inverse temperature `β` corresponding to the temperature `Real.toNNReal t`
(`max t 0`), returned as a real number. -/
noncomputable def betaFromReal (t : ℝ) : ℝ :=
  ((Temperature.ofNNReal (Real.toNNReal t)).β : ℝ)


-- @@ L188-191 verbatim
/-- Explicit closed-form for `Beta_fun_T t` when `t > 0`. -/
lemma beta_fun_T_formula (t : ℝ) (ht : 0 < t) :
    betaFromReal t = 1 / (kB * t) := by
  simp only [betaFromReal, β_toReal, Temperature.toReal, ofNNReal_val, Real.coe_toNNReal t ht.le]


-- @@ L193-197 verbatim
/-- On `Ioi 0`, `Beta_fun_T t` equals `1 / (kB * t)`. -/
lemma beta_fun_T_eq_on_Ioi :
    EqOn betaFromReal (fun t : ℝ => 1 / (kB * t)) (Set.Ioi 0) := by
  intro t ht
  exact beta_fun_T_formula t ht


-- @@ L199-214 verbatim
lemma deriv_beta_wrt_T (T : Temperature) (hT_pos : 0 < T.val) :
    HasDerivWithinAt betaFromReal (-1 / (kB * (T.val : ℝ)^2)) (Set.Ioi 0) (T.val : ℝ) := by
  have hTne : (T.val : ℝ) ≠ 0 := ne_of_gt hT_pos
  have hg : HasDerivAt (fun t : ℝ => kB * t) kB (T.val : ℝ) := by
    simpa using (hasDerivAt_id (T.val : ℝ)).const_mul kB
  have h_deriv : HasDerivAt (fun t : ℝ => 1 / (kB * t))
      (-1 / (kB * (T.val : ℝ) ^ 2)) (T.val : ℝ) := by
    have h := (hasDerivAt_const (T.val : ℝ) (1 : ℝ)).div hg (mul_ne_zero kB_ne_zero hTne)
    have hval : (-1 : ℝ) / (kB * (T.val : ℝ) ^ 2)
        = (0 * (kB * (T.val : ℝ)) - 1 * kB) / (kB * (T.val : ℝ)) ^ 2 := by
      rw [mul_pow]
      field_simp
      ring
    rw [hval]
    exact h
  exact (h_deriv.hasDerivWithinAt).congr beta_fun_T_eq_on_Ioi (beta_fun_T_eq_on_Ioi hT_pos)


-- @@ L216-233 verbatim
/-- Chain rule for β(T) : d/dT F(β(T)) = F'(β(T)) * (-1 / (kB * T^2)), within `Ioi 0`. -/
lemma chain_rule_T_beta {F : ℝ → ℝ} {F' : ℝ}
    (T : Temperature) (hT_pos : 0 < T.val)
    (hF_deriv : HasDerivWithinAt F F' (Set.Ioi 0) (T.β : ℝ)) :
    HasDerivWithinAt (fun t : ℝ => F (betaFromReal t))
      (F' * (-1 / (kB * (T.val : ℝ)^2))) (Set.Ioi 0) (T.val : ℝ) := by
  have h_map : Set.MapsTo betaFromReal (Set.Ioi 0) (Set.Ioi 0) := by
    intro t ht
    show 0 < betaFromReal t
    rw [beta_fun_T_eq_on_Ioi ht]
    exact one_div_pos.mpr (mul_pos kB_pos ht)
  have h_beta_at_T : betaFromReal (T.val : ℝ) = (T.β : ℝ) := by
    rw [beta_fun_T_eq_on_Ioi (show (T.val : ℝ) ∈ Set.Ioi 0 from hT_pos), β_toReal]
    rfl
  have hF_deriv' : HasDerivWithinAt F F' (Set.Ioi 0) (betaFromReal (T.val : ℝ)) := by
    rw [h_beta_at_T]
    exact hF_deriv
  exact hF_deriv'.comp (T.val : ℝ) (deriv_beta_wrt_T (T := T) hT_pos) h_map


-- @@ L235-235 verbatim
end Temperature
