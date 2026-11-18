import OAI.NumberTheory.DirichletL.Energy.OriginalSource
import OAI.NumberTheory.DirichletL.Moments.AllocatedRayDictionary


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators SchwartzMap


-- @@ L9-9 verbatim
namespace SevenEighths.CenteredMomentEnergyNaturalInputMatches

-- @@ L10-10 verbatim
open HeckeFamily HeckePrimeAnnular CenteredMomentPrimeSlot

-- @@ L11-11 verbatim
open CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional

-- @@ L12-12 verbatim
open CenteredMomentCommonRadialData CenteredMomentNaturalFixedRaySource

-- @@ L13-13 verbatim
open CenteredMomentInductionEnergy CenteredMomentHeckeSlots CenteredMomentRetainedEnergy

-- @@ L14-14 verbatim
local notation "O" => HeckeFamily.O


-- @@ L16-17 verbatim
def profile (W : ℝ → ℂ) (σ freq y : ℝ) : ℂ :=
  W y * (y : ℂ)^(-HeckeDyadic.shift σ freq)


-- @@ L19-25 verbatim
lemma profile_support (W : ℝ → ℂ) (a b : ℝ)
    (hWs : Function.support W ⊆ Set.Icc a b) (σ freq : ℝ) :
    Function.support (profile W σ freq) ⊆ Set.Icc a b := by
  intro y hy
  apply hWs
  intro hz
  exact hy (by simp only [profile, hz, zero_mul])


-- @@ L27-31 verbatim
lemma profile_zero (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hWs : Function.support W ⊆ Set.Icc a b) (σ freq : ℝ) :
    profile W σ freq 0 = 0 := by
  by_contra hn
  exact (not_le_of_gt ha) ((profile_support W a b hWs σ freq hn).1)


-- @@ L33-40 verbatim
lemma profile_norm (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hWs : Function.support W ⊆ Set.Icc a b) (σ freq y : ℝ) :
    ‖profile W σ freq y‖ = ‖W y‖ * y^(-σ) := by
  by_cases hz : W y = 0
  · simp only [profile, hz, zero_mul, norm_zero]
  · have hy : 0 < y := ha.trans_le (hWs hz).1
    simp only [profile, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy,
      Complex.neg_re, HeckeDyadic.shift_re]


-- @@ L42-54 verbatim
theorem exists_profile_bound (W : ℝ → ℂ) (hW : Continuous W)
    (a b lo hi : ℝ) (ha : 0 < a)
    (hWs : Function.support W ⊆ Set.Icc a b) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ σ ∈ Set.Icc lo hi, ∀ freq y : ℝ,
      ‖profile W σ freq y‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := fixed_profile_norm_bound W hW a b lo hi ha
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro σ hσ freq y
  by_cases hz : W y = 0
  · simpa only [profile, hz, zero_mul, norm_zero] using
      (zero_le_one.trans (le_max_left 1 C))
  · rw [profile_norm W a b ha hWs]
    exact (hb σ hσ y (hWs hz)).trans (le_max_right _ _)


-- @@ L56-59 verbatim
def profileBound (W : ℝ → ℂ) (hW : Continuous W)
    (a b lo hi : ℝ) (ha : 0 < a)
    (hWs : Function.support W ⊆ Set.Icc a b) : ℝ :=
  (exists_profile_bound W hW a b lo hi ha hWs).choose


-- @@ L61-65 verbatim
lemma profileBound_ge_one (W : ℝ → ℂ) (hW : Continuous W)
    (a b lo hi : ℝ) (ha : 0 < a)
    (hWs : Function.support W ⊆ Set.Icc a b) :
    1 ≤ profileBound W hW a b lo hi ha hWs :=
  (exists_profile_bound W hW a b lo hi ha hWs).choose_spec.1


-- @@ L67-72 verbatim
lemma norm_profile_le (W : ℝ → ℂ) (hW : Continuous W)
    (a b lo hi : ℝ) (ha : 0 < a)
    (hWs : Function.support W ⊆ Set.Icc a b)
    (σ : ℝ) (hσ : σ ∈ Set.Icc lo hi) (freq y : ℝ) :
    ‖profile W σ freq y‖ ≤ profileBound W hW a b lo hi ha hWs :=
  (exists_profile_bound W hW a b lo hi ha hWs).choose_spec.2 σ hσ freq y


-- @@ L74-74 verbatim
section Input

-- @@ L75-75 verbatim
variable {ι : Type*} [Fintype ι]

-- @@ L76-76 verbatim
variable (Q : Ideal O) [NeZero Q]

-- @@ L77-77 verbatim
local instance : Finite (O ⧸ Q) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne Q)

-- @@ L78-78 verbatim
variable (H : Subgroup (O ⧸ Q)ˣ) (hH : RayOrthogonality.globalUnits Q ≤ H)

-- @@ L79-79 verbatim
variable (η₀ : Character) (θ : ι → RayQuotient.Characters Q H)

-- @@ L80-80 verbatim
variable (W : ℝ → ℂ) (hW : Continuous W)

-- @@ L81-81 verbatim
variable (aslot bslot lo hi : ℝ) (haslot : 0 < aslot)

-- @@ L82-82 verbatim
variable (hWs : Function.support W ⊆ Set.Icc aslot bslot)

-- @@ L83-83 verbatim
variable (w σ freq : ι → ℝ) (hσ : ∀ i, σ i ∈ Set.Icc lo hi)

-- @@ L84-84 verbatim
variable {Z Bmask bΦ a b : ℝ}

-- @@ L85-85 verbatim
variable (state : NaturalState Z Bmask bΦ) (p : Profiles a b) (ha : 0 < a)

-- @@ L86-86 verbatim
variable (t X₁ X₂ Y₁ Y₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)

-- @@ L87-87 verbatim
variable (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) (hsame : Y₁ * Y₂ = X₁ * X₂)


-- @@ L89-100 verbatim
def input : Input ι :=
  CenteredMomentEnergyOriginalSource.naturalInput state p ha
    (fun i => primePool Q H bslot (Z^(w i)))
    (fun _ _ hI => (Finset.mem_filter.mp hI).2.1)
    (fun i => relativeCharacter Q H hH η₀ (θ i))
    (fun i => profile W (σ i) (freq i)) (fun i => Z^(w i))
    (fun _ => profileBound W hW aslot bslot lo hi haslot hWs)
    (fun _ => Real.rpow_pos_of_pos (zero_lt_one.trans_le state.base_ge_one) _)
    (fun _ => profileBound_ge_one W hW aslot bslot lo hi haslot hWs)
    aslot bslot haslot (fun i => profile_support W aslot bslot hWs (σ i) (freq i))
    (fun i => norm_profile_le W hW aslot bslot lo hi haslot hWs (σ i) (hσ i) (freq i))
    t X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hsame


-- @@ L102-103 verbatim
local notation "inp" => input Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ state p ha t X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hsame


-- @@ L105-107 verbatim
theorem input_matches :
    CenteredMomentAllocatedRayDictionary.Matches Q H hH inp η₀ θ w σ freq W bslot Z := by
  constructor <;> intros <;> rfl


-- @@ L109-109 verbatim
lemma lower_eq : (inp).lower = aslot := rfl

-- @@ L110-110 verbatim
lemma upper_eq : (inp).upper = bslot := rfl

-- @@ L111-112 verbatim
lemma slot_control_eq (i : ι) :
    (inp).M i = profileBound W hW aslot bslot lo hi haslot hWs := rfl

-- @@ L113-113 verbatim
lemma character_eq : (inp).η = state.character := rfl

-- @@ L114-114 verbatim
lemma mask_eq : (inp).m = state.mask := rfl

-- @@ L115-115 verbatim
lemma height_eq : (inp).t = t := rfl

-- @@ L116-116 verbatim
lemma first_rectangle_eq : (inp).X₁ = X₁ ∧ (inp).X₂ = X₂ := ⟨rfl, rfl⟩

-- @@ L117-117 verbatim
lemma second_rectangle_eq : (inp).Y₁ = Y₁ ∧ (inp).Y₂ = Y₂ := ⟨rfl, rfl⟩


-- @@ L119-122 verbatim
theorem coefficient_eq (i : ι) (I : Ideal O) :
    (inp).toData.coefficient i I =
      idealCoeff (relativeCharacter Q H hH η₀ (θ i)) I *
        annularWeight W (Z^(w i)) (σ i) (freq i) I := rfl


-- @@ L124-131 verbatim
theorem positive_row_eq (z : O) :
    positiveSlotRow (inp).η state.mask 1 z (inp).W₁ (inp).W₂ (inp).slots
      (inp).toData.coefficient (inp).P (inp).t (inp).X₁ (inp).X₂ =
    positiveSlotRow state.character state.mask 1 z (p.profile 0) (p.profile 1)
      (fun i => primePool Q H bslot (Z^(w i)))
      (fun i I => idealCoeff (relativeCharacter Q H hH η₀ (θ i)) I *
        annularWeight W (Z^(w i)) (σ i) (freq i) I)
      (fun i => Z^(w i)) t X₁ X₂ := rfl


-- @@ L133-142 verbatim
theorem energy_eq :
    energy (inp).η state.mask 1 (inp).t (inp).W₁ (inp).W₂ (inp).slots
      (inp).toData.coefficient (inp).P (inp).X₁ (inp).X₂
      state.radial.keep state.radial.profile state.radial.scale =
    energy state.character state.mask 1 t (p.profile 0) (p.profile 1)
      (fun i => primePool Q H bslot (Z^(w i)))
      (fun i I => idealCoeff (relativeCharacter Q H hH η₀ (θ i)) I *
        annularWeight W (Z^(w i)) (σ i) (freq i) I)
      (fun i => Z^(w i)) X₁ X₂
      state.radial.keep state.radial.profile state.radial.scale := rfl


-- @@ L144-153 verbatim
theorem reference_energy_eq :
    energy (inp).η state.mask 1 (inp).t (inp).W₁ (inp).W₂ (inp).slots
      (inp).toData.coefficient (inp).P (inp).Y₁ (inp).Y₂
      state.radial.keep state.radial.profile state.radial.scale =
    energy state.character state.mask 1 t (p.profile 0) (p.profile 1)
      (fun i => primePool Q H bslot (Z^(w i)))
      (fun i I => idealCoeff (relativeCharacter Q H hH η₀ (θ i)) I *
        annularWeight W (Z^(w i)) (σ i) (freq i) I)
      (fun i => Z^(w i)) Y₁ Y₂
      state.radial.keep state.radial.profile state.radial.scale := rfl


-- @@ L155-155 verbatim
end Input

-- @@ L156-156 verbatim
end SevenEighths.CenteredMomentEnergyNaturalInputMatches


-- @@ L158-158 verbatim
end


-- @@ L160-160 verbatim
end OAI
