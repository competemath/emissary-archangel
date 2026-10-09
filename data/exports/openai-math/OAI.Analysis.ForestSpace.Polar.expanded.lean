import OAI.Analysis.ForestSpace.Completion


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
open scoped BigOperators

-- @@ L6-6 verbatim
open Finset


-- @@ L8-8 verbatim
namespace ForestSpace


-- @@ L10-10 verbatim
noncomputable section

-- @@ L11-11 verbatim
attribute [local instance] Classical.propDecidable


-- @@ L13-13 verbatim
section PolarTests

-- @@ L14-14 verbatim
variable {V : Type} [PartialOrder V]


-- @@ L16-17 verbatim
noncomputable def rawRestriction (x : FullDual V) : TestVector V →L[ℝ] ℝ :=
  x.comp UniformSpace.Completion.toComplL


-- @@ L19-20 verbatim
@[simp] theorem rawRestriction_apply (x : FullDual V) (u : TestVector V) :
    rawRestriction x u = x (u : J V) := rfl

 
-- @@ L22-34 verbatim
theorem norm_rawRestriction (x : FullDual V) : ‖rawRestriction x‖ = ‖x‖ := by
  apply le_antisymm
  · apply (rawRestriction x).opNorm_le_bound (norm_nonneg x)
    intro u
    simpa only [rawRestriction_apply, UniformSpace.Completion.norm_coe]
      using x.le_opNorm (u : J V)
  · apply x.opNorm_le_bound (norm_nonneg _)
    intro u
    refine UniformSpace.Completion.induction_on u
      (isClosed_le x.continuous.norm (continuous_const.mul continuous_norm)) ?_
    intro v
    simpa only [← rawRestriction_apply, UniformSpace.Completion.norm_coe]
      using (rawRestriction x).le_opNorm v


-- @@ L36-50 verbatim
/-- Norming tests can always be chosen finitely supported, with a positive
rather than absolute pairing. -/
 theorem exists_raw_test (x : FullDual V) {r : ℝ} (hr : r < ‖x‖) :
    ∃ u : TestVector V, ‖u‖ ≤ 1 ∧ r < x (u : J V) := by
  have hr' : r < ‖rawRestriction x‖ := by simpa only [norm_rawRestriction] using hr
  obtain ⟨u,hu,hr⟩ := (rawRestriction x).exists_lt_apply_of_lt_opNorm hr'
  rw [Real.norm_eq_abs] at hr
  by_cases hpos : 0 ≤ rawRestriction x u
  · refine ⟨u,hu.le, ?_⟩
    rw [abs_of_nonneg hpos] at hr
    exact hr
  · refine ⟨-u, by simpa only [norm_neg] using hu.le, ?_⟩
    have ha : rawRestriction x (-u) = -rawRestriction x u := map_neg _ _
    rw [abs_of_neg (lt_of_not_ge hpos), ← ha] at hr
    exact hr


-- @@ L52-54 verbatim
/-- Vanishing on all finite tests in a specified coordinate region. -/
def Annihilates (x : FullDual V) (A : Set V) : Prop :=
  ∀ u : TestVector V, SupportedOn u A → x (u : J V) = 0

 
-- @@ L56-64 verbatim
theorem exists_head_test (H : Set V) (hH : IsLowerSet H) (x : FullDual V)
    (hx : Annihilates x Hᶜ) {r : ℝ} (hr : r < ‖x‖) :
    ∃ f : TestVector V, SupportedOn f H ∧ ‖f‖ ≤ 1 ∧ r < x (f : J V) := by
  obtain ⟨u,hu,hr⟩ := exists_raw_test x hr
  have he := congrArg (rawRestriction x) (TestVector.cut_add_compl H u)
  have hz := hx (TestVector.cut Hᶜ u) (TestVector.cut_supported Hᶜ u)
  simp only [map_add, rawRestriction_apply, hz, add_zero] at he
  exact ⟨TestVector.cut H u, TestVector.cut_supported H u,
    (TestVector.norm_cut_le H hH u).trans hu, by simpa only [he] using hr⟩

 
-- @@ L66-74 verbatim
theorem exists_tail_test (H : Set V) (hH : IsLowerSet H) (x : FullDual V)
    (hx : Annihilates x H) {r : ℝ} (hr : r < ‖x‖) :
    ∃ k : TestVector V, SupportedOn k Hᶜ ∧ ‖k‖ ≤ 1 ∧ r < x (k : J V) := by
  obtain ⟨u,hu,hr⟩ := exists_raw_test x hr
  have he := congrArg (rawRestriction x) (TestVector.cut_add_compl H u)
  have hz := hx (TestVector.cut H u) (TestVector.cut_supported H u)
  simp only [map_add, rawRestriction_apply, hz, zero_add] at he
  exact ⟨TestVector.cut Hᶜ u, TestVector.cut_supported Hᶜ u,
    (TestVector.norm_cut_compl_le H hH u).trans hu, by simpa only [he] using hr⟩


-- @@ L76-98 verbatim
/-- The cancellation of the same gate correction in the two dual evaluations. -/
 theorem paired_polar_test (H : Set V) {x y : FullDual V}
    (hx : Annihilates x Hᶜ) (hy : Annihilates y H)
    {f k c : TestVector V} (hf : SupportedOn f H) (hk : SupportedOn k Hᶜ)
    (hc : SupportedOn c Hᶜ) (s d : ℝ)
    (hp : ‖f + s • (c + k)‖ ≤ d) (hm : ‖f + s • (c - k)‖ ≤ d) :
    x (f : J V) + s * y (k : J V) ≤ (‖x+y‖ + ‖x-y‖) / 2 * d := by
  have hb (z : FullDual V) (u : TestVector V) (hu : ‖u‖ ≤ d) :
      rawRestriction z u ≤ ‖z‖ * d := by
    calc
      rawRestriction z u ≤ |rawRestriction z u| := le_abs_self _
      _ ≤ ‖z‖ * ‖u‖ := by
        simpa only [Real.norm_eq_abs, norm_rawRestriction] using (rawRestriction z).le_opNorm u
      _ ≤ ‖z‖ * d := mul_le_mul_of_nonneg_left hu (norm_nonneg _)
  have hp' := hb (x+y) (f+s•(c+k)) hp
  have hm' := hb (x-y) (f+s•(c-k)) hm
  have he : rawRestriction (x+y) (f+s•(c+k)) + rawRestriction (x-y) (f+s•(c-k)) =
      2 * (x (f : J V) + s * y (k : J V)) := by
    simp only [map_add, map_sub, map_smul, rawRestriction_apply,
      _root_.add_apply, _root_.sub_apply, smul_eq_mul,
      hx k hk, hx c hc, hy f hf]
    ring
  linarith

 
-- @@ L100-118 verbatim
theorem paired_parameter (hF : ForestOrder V) (hAnc : ∀ v : V, (Set.Iic v).Finite)
    (H : Set V) (hH : IsLowerSet H) (x y : FullDual V)
    (hx : Annihilates x Hᶜ) (hy : Annihilates y H) (s : ℝ) (hs : 0 < s) :
    (‖x‖ + s * ‖y‖) / Real.sqrt (1 + 12 * s ^ 2) ≤ (‖x+y‖ + ‖x-y‖) / 2 := by
  have hd : 0 < Real.sqrt (1 + 12 * s ^ 2) := Real.sqrt_pos.mpr (by positivity)
  apply (div_le_iff₀ hd).mpr
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨f,hf,hf₁,hfx⟩ := exists_head_test H hH x hx (show ‖x‖-ε/2 < ‖x‖ by linarith)
  obtain ⟨k,hk,hk₁,hky⟩ := exists_tail_test H hH y hy
    (show ‖y‖-ε/(2*s) < ‖y‖ by
      have : 0 < ε/(2*s) := by positivity
      linarith)
  obtain ⟨c,hc,hc₁,hp,hm⟩ := TestVector.paired_correction hF hAnc H hH f k hf hk hf₁ hk₁ s hs
  have ht := paired_polar_test H hx hy hf hk hc s (Real.sqrt (1+12*s^2)) hp hm
  have hm' := mul_lt_mul_of_pos_left hky hs
  have he : s * (ε / (2*s)) = ε/2 := by field_simp
  rw [mul_sub, he] at hm'
  linarith

 
-- @@ L120-123 verbatim
theorem Annihilates.smul {x : FullDual V} {A : Set V} (hx : Annihilates x A) (t : ℝ) :
    Annihilates (t • x) A := by
  intro u hu
  simp [hx u hu]

 
-- @@ L125-156 verbatim
theorem paired_estimate (hF : ForestOrder V) (hAnc : ∀ v : V, (Set.Iic v).Finite)
    (H : Set V) (hH : IsLowerSet H) (x y : FullDual V)
    (hx : Annihilates x Hᶜ) (hy : Annihilates y H) :
    Real.sqrt (‖x‖ ^ 2 + ‖y‖ ^ 2 / 12) ≤ (‖x+y‖ + ‖x-y‖) / 2 := by
  by_cases hx0 : x = 0
  · subst x
    simp only [norm_zero, zero_pow (by decide : (2:ℕ) ≠ 0), zero_add, zero_sub, norm_neg]
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [sq_nonneg ‖y‖]
  by_cases hy0 : y = 0
  · subst y
    simp only [norm_zero, zero_pow (by decide : (2:ℕ) ≠ 0), zero_div, add_zero, sub_zero]
    rw [Real.sqrt_sq (norm_nonneg _)]
    linarith
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  let s := ‖y‖ / (12 * ‖x‖)
  have hs : 0 < s := by dsimp [s]; positivity
  have hd : 0 < Real.sqrt (1+12*s^2) := Real.sqrt_pos.mpr (by positivity)
  have hh := (div_le_iff₀ hd).mp (paired_parameter hF hAnc H hH x y hx hy s hs)
  have he : (‖x‖+s*‖y‖)^2 = (‖x‖^2+‖y‖^2/12)*(1+12*s^2) := by
    dsimp [s]
    field_simp

  have hh' : (‖x‖+s*‖y‖)^2 ≤ ((‖x+y‖+‖x-y‖)/2 * Real.sqrt (1+12*s^2))^2 :=
    sq_le_sq₀ (by positivity) (by positivity) |>.mpr hh
  rw [he, mul_pow, Real.sq_sqrt (by positivity)] at hh'
  have hden : 0 < 1+12*s^2 := by positivity
  apply Real.sqrt_le_iff.mpr
  exact ⟨by positivity, (mul_le_mul_iff_left₀ hden).mp (by simpa only [mul_comm] using hh')⟩

 
-- @@ L158-163 verbatim
theorem paired_two_parameters (hF : ForestOrder V) (hAnc : ∀ v : V, (Set.Iic v).Finite)
    (H : Set V) (hH : IsLowerSet H) (x y : FullDual V)
    (hx : Annihilates x Hᶜ) (hy : Annihilates y H) (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    (‖x‖ + s*t*‖y‖) / Real.sqrt (1+12*s^2) ≤ (‖x+t•y‖ + ‖x-t•y‖)/2 := by
  simpa only [norm_smul, Real.norm_of_nonneg ht.le, mul_assoc]
    using paired_parameter hF hAnc H hH x (t•y) hx (hy.smul t) s hs


-- @@ L165-165 verbatim
end PolarTests


-- @@ L167-167 verbatim
section CoordinateCompletion

-- @@ L168-168 verbatim
variable {W : Type} [PartialOrder W]

-- @@ L169-170 verbatim
instance fullDualAddCommGroup : AddCommGroup (FullDual W) :=
  inferInstanceAs (AddCommGroup (StrongDual ℝ (J W)))


-- @@ L172-172 verbatim
variable {V : Type} [PartialOrder V]


-- @@ L174-174 verbatim
noncomputable def e (v : V) : J V := (TestVector.single v 1 : TestVector V)


-- @@ L176-178 verbatim
/-- The coordinate functional on J(T). -/
noncomputable def eStar (v : V) : FullDual V :=
  (TestVector.eval v).extend UniformSpace.Completion.toComplL


-- @@ L180-182 verbatim
@[simp] theorem eStar_coe (v : V) (u : TestVector V) : eStar v (u : J V) = u v := by
  exact (TestVector.eval v).extend_eq UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe (TestVector V)) u


-- @@ L184-185 verbatim
@[simp] theorem norm_e (v : V) : ‖e v‖ = 1 := by
  simp [e, UniformSpace.Completion.norm_coe, TestVector.norm_single]


-- @@ L187-188 verbatim
@[simp] theorem eStar_e (v w : V) : eStar v (e w) = if w = v then 1 else 0 := by
  simp [e]

 
-- @@ L190-195 verbatim
theorem eStar_norm_le (v : V) : ‖eStar v‖ ≤ 1 := by
  have h := (TestVector.eval v).opNorm_extend_le (N := 1)
    (e := UniformSpace.Completion.toComplL) UniformSpace.Completion.denseRange_coe
    (by intro u; simp)
  have hh : ‖eStar v‖ ≤ ‖TestVector.eval v‖ := by simpa [eStar] using h
  exact hh.trans (TestVector.eval_norm_le v)


-- @@ L197-200 verbatim
@[simp] theorem norm_eStar (v : V) : ‖eStar v‖ = 1 := by
  apply le_antisymm (eStar_norm_le v)
  have h := (eStar v).unit_le_opNorm (e v) (by simp)
  simpa using h


-- @@ L202-205 verbatim
/-- The norm-closed coordinate span inside J(T)*. No identification with the
full dual is made for a general forest. -/
@[reducible] noncomputable def coordinateSubspace (V : Type) [PartialOrder V] : Submodule ℝ (FullDual V) :=
  (Submodule.span ℝ (Set.range (eStar (V := V)))).topologicalClosure


-- @@ L207-207 verbatim
abbrev X (V : Type) [PartialOrder V] : Type := ↥(coordinateSubspace V)



-- @@ L210-210 verbatim
end CoordinateCompletion


-- @@ L212-212 verbatim
end


-- @@ L214-214 verbatim
end ForestSpace


-- @@ L216-216 verbatim
end OAI
