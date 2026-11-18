import OAI.NumberTheory.DirichletL.Energy.NaturalLowSourceBound


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical BigOperators SchwartzMap

-- @@ L7-7 verbatim
open Filter


-- @@ L9-9 verbatim
namespace SevenEighths.CenteredMomentEnergyNaturalSourceAdmission

-- @@ L10-10 verbatim
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound

-- @@ L11-11 verbatim
open CenteredMomentCommonRadialData CenteredMomentEnergyNaturalInputMatches

-- @@ L12-12 verbatim
open CenteredMomentEnergyNaturalLowSourceBound CenteredMomentEnergyState

-- @@ L13-13 verbatim
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyZeroComparison

-- @@ L14-14 verbatim
open CenteredMomentEnergyOriginalSource CenteredMomentEnergyOriginalProfileControl

-- @@ L15-15 verbatim
open CenteredMomentEnergyInputParentCapacity CenteredMomentAmplificationChildInput

-- @@ L16-16 verbatim
open CenteredMomentEnergyBands CenteredMomentSecondHeightFamily

-- @@ L17-17 verbatim
open CenteredMomentPrimeSlot CenteredMomentNaturalFixedRaySource HeckeDyadic HeckePrimeAnnular

-- @@ L18-18 verbatim
open CenteredMomentInductionEnergy CenteredMomentSourceRow CenteredMomentRetainedEnergy

-- @@ L19-19 verbatim
open CenteredMomentSourceInputTailUniform CenteredMomentSourceMass

-- @@ L20-20 verbatim
open CenteredMomentSourceProfileMass CenteredMomentHeckeExpansion CenteredMomentHeckeHeight

-- @@ L21-21 verbatim
local notation "O" => HeckeFamily.O

-- @@ L22-22 verbatim
variable {ι : Type*} [Fintype ι]

-- @@ L23-23 verbatim
local instance : DecidableEq (ι ⊕ Fin 2) := energyOriginalSourceDecidableSum


-- @@ L25-25 verbatim
def lowerProduct (N : ℕ) (aslot a : ℝ) : ℝ := (min 1 aslot)^N*a*a


-- @@ L27-28 verbatim
lemma lowerProduct_pos (N : ℕ) {aslot a : ℝ} (hs : 0 < aslot) (ha : 0 < a) :
    0 < lowerProduct N aslot a := by unfold lowerProduct; positivity


-- @@ L30-30 verbatim
section Source

-- @@ L31-31 verbatim
variable (Q : Ideal O) [NeZero Q]

-- @@ L32-32 verbatim
variable (H : Subgroup (O ⧸ Q)ˣ) (hH : RayOrthogonality.globalUnits Q ≤ H)

-- @@ L33-33 verbatim
variable (η₀ : Character) (θ : ι → RayQuotient.Characters Q H)

-- @@ L34-34 verbatim
variable (W : ℝ → ℂ) (hW : Continuous W) (aslot bslot lo hi : ℝ)

-- @@ L35-35 verbatim
variable (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot)

-- @@ L36-36 verbatim
variable (w σ freq : ι → ℝ) (hσ : ∀ i, σ i ∈ Set.Icc lo hi)

-- @@ L37-37 verbatim
variable {Z Bmask bΦ a b : ℝ} (state : NaturalState Z Bmask bΦ)

-- @@ L38-38 verbatim
variable (p : Profiles a b) (ha : 0 < a) (t X₁ X₂ : ℝ)

-- @@ L39-39 verbatim
variable (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)

-- @@ L40-41 verbatim
local notation "s" => sourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂

-- @@ L42-43 verbatim
local notation "s₀" => zeroSourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂


-- @@ L45-48 verbatim
theorem both_matches :
    CenteredMomentAllocatedRayDictionary.Matches Q H hH s η₀ θ w σ freq W bslot Z ∧
    CenteredMomentAllocatedRayDictionary.Matches Q H hH s₀ η₀ θ w σ freq W bslot Z := by
  constructor <;> constructor <;> intros <;> rfl


-- @@ L50-57 verbatim
lemma source_fields :
    (s).η = state.character ∧ (s₀).η = state.character ∧
    (s).m = state.mask ∧ (s₀).m = state.mask ∧ (s).A = 1 ∧ (s₀).A = 1 ∧
    (s).t = t ∧ (s₀).t = t ∧
    (s).W₁ = p.profile 0 ∧ (s₀).W₁ = p.profile 0 ∧
    (s).W₂ = p.profile 1 ∧ (s₀).W₂ = p.profile 1 ∧
    (s).lower = aslot ∧ (s₀).lower = aslot ∧ (s).upper = bslot ∧ (s₀).upper = bslot := by
  repeat' constructor


-- @@ L59-65 verbatim
lemma slot_fields (i : ι) :
    (s).P i = Z^(w i) ∧ (s₀).P i = Z^(w i) ∧
    (s).lo i = aslot ∧ (s₀).lo i = aslot ∧ (s).hi i = bslot ∧ (s₀).hi i = bslot ∧
    (s).M i = profileBound W hW aslot bslot lo hi haslot hWs ∧
    (s₀).M i = profileBound W hW aslot bslot lo hi haslot hWs ∧
    (s).slots i = primePool Q H bslot (Z^(w i)) ∧
    (s₀).slots i = primePool Q H bslot (Z^(w i)) := by repeat' constructor


-- @@ L67-70 verbatim
lemma slot_coefficient (i : ι) (I : Ideal O) :
    (s).toData.coefficient i I = idealCoeff (relativeCharacter Q H hH η₀ (θ i)) I *
      annularWeight W (Z^(w i)) (σ i) (freq i) I ∧
    (s₀).toData.coefficient i I = (s).toData.coefficient i I := ⟨rfl, rfl⟩


-- @@ L72-78 verbatim
lemma rectangles :
    (s).X₁ = X₁ ∧ (s).X₂ = X₂ ∧ (s).Y₁ = X₁ ∧ (s).Y₂ = X₂ ∧
    (s₀).X₁ = X₁ ∧ (s₀).X₂ = X₂ ∧
    (s₀).Y₁ = smallScale b ∧ (s₀).Y₂ = X₁*X₂/smallScale b ∧
    (s₀).Y₁*(s₀).Y₂ = X₁*X₂ := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
  exact (s₀).same_product


-- @@ L80-80 verbatim
lemma raw_volume : volume s = X₁*X₂*∏ i, Z^(w i) ∧ volume s₀ = volume s := ⟨rfl,rfl⟩


-- @@ L82-89 verbatim
lemma volume_log (hZ : 1 < Z) :
    Real.logb Z (volume s) = Real.logb Z X₁ + Real.logb Z X₂ + ∑ i, w i ∧
    Real.logb Z (volume s₀) = Real.logb Z X₁ + Real.logb Z X₂ + ∑ i, w i := by
  have hh := input_volume_log s Z
  change Real.logb Z (volume s) = Real.logb Z X₁ + Real.logb Z X₂ +
    ∑ i, Real.logb Z (Z^(w i)) at hh
  simp only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hh
  exact ⟨hh,hh⟩


-- @@ L91-100 verbatim
theorem capacity_admission (hZ : 1 < Z) (hw : ∀ i, 0 ≤ w i) (κ : ℝ)
    (hκ : 1/6 ≤ κ)
    (hcap : length Z X₁ + length Z X₂ + 6*κ*(∑ i, w i) ≤ state.width) :
    (∀ i, 1 ≤ (s).P i ∧ 1 ≤ (s₀).P i) ∧
    volume s ≤ Z^state.width ∧ volume s₀ ≤ Z^state.width := by
  have hPi : ∀ i, 1 ≤ (s).P i := fun i => Real.one_le_rpow hZ.le (hw i)
  have hv := original_volume_cap s Z κ state.width hZ hκ hPi (by
    change length Z X₁ + length Z X₂ + 6*κ*(∑ i, Real.logb Z (Z^(w i))) ≤ _
    simpa only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hcap)
  exact ⟨fun i => ⟨hPi i,hPi i⟩,hv,hv⟩


-- @@ L102-110 verbatim
theorem low_admission (hZ : 1 < Z)
    (hlow : length Z X₁ + length Z X₂ + ∑ i, w i ≤ 5*state.width/6) :
    Real.logb Z (volume s) ≤ 5*state.width/6 ∧
    Real.logb Z (volume s₀) ≤ 5*state.width/6 := by
  have hv := volume_log Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂ hZ
  have h1 := raw_log_le_length Z X₁ hZ hX₁
  have h2 := raw_log_le_length Z X₂ hZ hX₂
  constructor <;> linarith [hv.1,hv.2]


-- @@ L112-118 verbatim
theorem lower_product_admission (N : ℕ) (hN : Fintype.card ι ≤ N) :
    0 < lowerProduct N aslot a ∧
    lowerProduct N aslot a ≤ (∏ i, (s).lo i)*a*a ∧
    lowerProduct N aslot a ≤ (∏ i, (s₀).lo i)*a*a := by
  have hh := lower_product s N aslot haslot hN (fun _ => le_rfl)
  have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh ha.le) ha.le
  exact ⟨lowerProduct_pos N haslot ha,hb,hb⟩


-- @@ L120-130 verbatim
theorem profile_control_admission (N : ℕ) (hN : Fintype.card ι ≤ N)
    (S : Finset (ℕ×ℕ)) :
    (plainControl s (p.profile 0) (p.profile 1))^2 ≤
      (profileBound W hW aslot bslot lo hi haslot hWs)^(2*N)*
        (p.control (insert (0,0) S))^2 ∧
    (plainControl s₀ (p.profile 0) (p.profile 1))^2 ≤
      (profileBound W hW aslot bslot lo hi haslot hWs)^(2*N)*
        (p.control (insert (0,0) S))^2 := by
  have hh := plain_control_sq_le s p S N _
    (profileBound_ge_one W hW aslot bslot lo hi haslot hWs) hN (fun _ => le_rfl)
  exact ⟨hh,hh⟩


-- @@ L132-149 verbatim
theorem normalized_zero_source (R : Ideal O) (z : O) :
    positiveSlotRow state.character (fixedBadMask*idealGenerator R) 1 z
      (p.profile 0) (p.profile 1) (s).slots (s).toData.coefficient (s).P t X₁ X₂ =
    (Real.sqrt (volume s) : ℂ)⁻¹ *
      ∑ I ∈ finiteColumns (Fintype.piFinset (s₀).pools),
        CenteredMomentOriginalCommonHarmonic.coefficient s₀ R 1 I * rowWeight state.character fixedBadMask 1 z t I := by
  have hh := normalized_input_difference s₀ R z
  have hz := comparison_row_zero s
    (CenteredMomentDetectorPlainSource.support_zero _ a b ha (p.support 0))
    (CenteredMomentDetectorPlainSource.support_zero _ a b ha (p.support 1)) R z
  change positiveSlotRow state.character (fixedBadMask*idealGenerator R) 1 z
      (p.profile 0) (p.profile 1) (s).slots (s).toData.coefficient (s).P t X₁ X₂ -
    positiveSlotRow (s).η (fixedBadMask*idealGenerator R) 1 z (s).W₁ (s).W₂ (s).slots
      (s).toData.coefficient (s).P (s).t (s₀).Y₁ (s₀).Y₂ = _ at hh
  change positiveSlotRow (s).η (fixedBadMask*idealGenerator R) 1 z (s).W₁ (s).W₂ (s).slots
    (s).toData.coefficient (s).P (s).t (s₀).Y₁ (s₀).Y₂ = 0 at hz
  rw [hz,sub_zero] at hh
  exact hh


-- @@ L151-151 verbatim
end Source


-- @@ L153-160 verbatim
theorem radial_admission {Z Bmask bΦ : ℝ} (state : NaturalState Z Bmask bΦ) :
    1 ≤ state.radial.scale ∧ state.radial.scale⁻¹ ≤ 1 ∧
    state.radial.scale⁻¹ ≤ Z^state.width := by
  have hs : 1 ≤ state.radial.scale := by
    rw [state.scale_eq]
    exact Real.one_le_rpow state.base_ge_one state.row_nonneg
  have hi := inv_le_one_of_one_le₀ hs
  exact ⟨hs,hi,hi.trans (Real.one_le_rpow state.base_ge_one state.width_nonneg)⟩


-- @@ L162-175 verbatim
theorem original_scale_caps {Z X₁ X₂ M L κ : ℝ} (w : ι → ℝ)
    (hZ : 1 < Z) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hw : ∀ i, 0 ≤ w i) (hκ : 1/6 ≤ κ)
    (hcap : length Z X₁ + length Z X₂ + 6*κ*(∑ i, w i) ≤ M)
    (hM : M ≤ L) : X₁ ≤ Z^L ∧ X₂ ≤ Z^L := by
  have hn : 0 ≤ 6*κ*(∑ i, w i) :=
    mul_nonneg (by linarith) (Finset.sum_nonneg (fun i _ => hw i))
  have h1 := raw_log_le_length Z X₁ hZ hX₁
  have h2 := raw_log_le_length Z X₂ hZ hX₂
  constructor
  · apply (Real.logb_le_iff_le_rpow hZ hX₁).mp
    linarith [length_nonneg Z X₂ hZ]
  · apply (Real.logb_le_iff_le_rpow hZ hX₂).mp
    linarith [length_nonneg Z X₁ hZ]


-- @@ L177-215 verbatim
theorem eventually_scale_admission (b L ε : ℝ) (hL : 0 ≤ L) (hε : 0 < ε) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (ι : Type*) [Fintype ι] [DecidableEq ι],
    ∀ (Q : Ideal O) [NeZero Q] (H : Subgroup (O ⧸ Q)ˣ)
      (hH : RayOrthogonality.globalUnits Q ≤ H) (η₀ : Character)
      (θ : ι → RayQuotient.Characters Q H),
    ∀ (W : ℝ → ℂ) (hW : Continuous W) (aslot bslot lo hi : ℝ)
      (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot),
    ∀ (w σ freq : ι → ℝ) (hσ : ∀ i, σ i ∈ Set.Icc lo hi),
    ∀ (Bmask bΦ a : ℝ) (state : NaturalState Z Bmask bΦ) (p : Profiles a b)
      (ha : 0 < a) (t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (κ : ℝ),
    (∀ i, 0 ≤ w i) → 1/6 ≤ κ → state.width ≤ L →
    length Z X₁ + length Z X₂ + 6*κ*(∑ i, w i) ≤ state.width →
    let s := sourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂
    let s₀ := zeroSourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂
    (s).X₁ ≤ Z^L ∧ (s).X₂ ≤ Z^L ∧ (s).Y₁ ≤ Z^L ∧ (s).Y₂ ≤ Z^L ∧
    (s₀).X₁ ≤ Z^L ∧ (s₀).X₂ ≤ Z^L ∧
    (s₀).Y₁ ≤ Z^(2*L+ε) ∧ (s₀).Y₂ ≤ Z^(2*L+ε) := by
  filter_upwards [(Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) (2*max 1 b),
    eventually_gt_atTop (1 : ℝ)] with Z hc hZ
  refine ⟨hZ,?_⟩
  intro ι _ _ Q _ H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ Bmask bΦ a state p ha t X₁ X₂ hX₁ hX₂ κ hw hκ hM hcap
  dsimp only
  have hx := original_scale_caps w hZ hX₁ hX₂ hw hκ hcap hM
  refine ⟨hx.1,hx.2,hx.1,hx.2,hx.1,hx.2,?_,?_⟩
  · exact (smallScale_le_one b).trans (Real.one_le_rpow hZ.le (by positivity))
  · change X₁*X₂/smallScale b ≤ _
    have hp : X₁*X₂ ≤ Z^(2*L) := by
      have hh := mul_le_mul hx.1 hx.2 hX₂.le (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) L).le
      rw [←Real.rpow_add (zero_lt_one.trans hZ)] at hh
      simpa only [two_mul] using hh
    unfold smallScale
    rw [div_div_eq_mul_div,div_one]
    exact (mul_le_mul hp hc (by positivity)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _).le).trans_eq
        (Real.rpow_add (zero_lt_one.trans hZ) _ _).symm


-- @@ L217-217 verbatim
end SevenEighths.CenteredMomentEnergyNaturalSourceAdmission


-- @@ L219-219 verbatim
end


-- @@ L221-221 verbatim
end OAI
