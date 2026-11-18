import OAI.NumberTheory.DirichletL.Energy.FirstLiveAdmission
import OAI.NumberTheory.DirichletL.Moments.FirstMixedRightTransport


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators SchwartzMap

-- @@ L8-8 verbatim
open Filter


-- @@ L10-10 verbatim
namespace SevenEighths.CenteredMomentEnergyFirstRightAdmission

-- @@ L11-11 verbatim
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT ConcretePrimeRowBridge

-- @@ L12-12 verbatim
open ActualEisensteinCubic CenteredMomentCanonicalFirst CenteredMomentSourceMass

-- @@ L13-13 verbatim
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum

-- @@ L14-14 verbatim
open CenteredMomentCommonProfile CenteredMomentAmplificationChildInput

-- @@ L15-15 verbatim
open CenteredMomentAmplificationChildSourceCaps CenteredMomentOriginalCommonHarmonic

-- @@ L16-16 verbatim
open CenteredMomentFirstSecondInputGates CenteredMomentFirstSecondActiveErrorGates

-- @@ L17-17 verbatim
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicRows

-- @@ L18-18 verbatim
open CenteredMomentFirstAmplifiedRadiusLower CenteredMomentFirstScale

-- @@ L19-19 verbatim
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius

-- @@ L20-20 verbatim
open CenteredMomentFirstAnnularInput CenteredMomentSectorLocalization

-- @@ L21-21 verbatim
open CenteredMomentSecondInputCapacitySource CenteredMomentFirstSourceConductorCaps

-- @@ L22-22 verbatim
open CenteredMomentEnergyInputParentCapacity CenteredMomentEnergyBands

-- @@ L23-23 verbatim
open CenteredMomentEnergyAmplifiedChildWidth CenteredMomentSecondHeightFamily

-- @@ L24-24 verbatim
open CenteredMomentSourceLiveColumn CenteredMomentActiveSource

-- @@ L25-25 verbatim
open CenteredMomentPrimePool CenteredMomentPrimeElements

-- @@ L26-26 verbatim
open CenteredMomentAmplificationRadicalFamily CenteredMomentAmplificationActiveFactor

-- @@ L27-27 verbatim
open CenteredMomentChildRows CompletedGauss RayFourExpansion

-- @@ L28-28 verbatim
open CenteredMomentLogDyadic CenteredMomentRowNorm

-- @@ L29-29 verbatim
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentFirstMixedRightTransport

-- @@ L30-30 verbatim
local notation "O" => HeckeFamily.O

-- @@ L31-31 verbatim
local instance {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _


-- @@ L33-38 verbatim
lemma main_radius_right (C D : Ideal O) (E : Finset (CommonIndex C D))
    (K V Z σ δ reserve : ℝ) :
    columnMainRadius C D E K V Z σ δ reserve true =
      mainRadius D C (swapSubset C D E) K V Z σ δ reserve := by
  simp only [columnMainRadius, columnIdeal, oppositeIdeal, ite_true,
    mainRadius, swapSubset_generator, nominal_swap]


-- @@ L40-45 verbatim
lemma error_radius_right (C D : Ideal O) (E : Finset (CommonIndex C D))
    (K V Z σ δ reserve : ℝ) (p : O) (k : ℕ) :
    columnErrorRadius C D E K V Z σ δ reserve true p k =
      errorRadius D C (swapSubset C D E) K V Z σ δ reserve p k := by
  simp only [columnErrorRadius, columnIdeal, oppositeIdeal, ite_true,
    errorRadius, swapSubset_generator, nominal_swap]


-- @@ L47-101 verbatim
theorem eventually_right_main_packet (N : ℕ) (b b₁ b₂ l a A P : ℝ)
    (hb : 1 ≤ b) (hb₁ : 1 ≤ b₁) (hb₂ : 1 ≤ b₂)
    (hl : 0 < l) (ha : 0 < a) (hA : 0 ≤ A) (hP : 0 ≤ P) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι],
      ∀ s : Input ι, Fintype.card ι ≤ N → Endpoints b b₁ b₂ s → l ≤ s.lower →
      (∀ x, s.W₁ x ≠ 0 → a ≤ x) → (∀ x, s.W₂ x ≠ 0 → a ≤ x) →
      ∀ κ : ℝ, 1/6 ≤ κ → (∀ i, 1 ≤ s.P i) →
      length Z s.X₁ + length Z s.X₂ + 6*κ*(∑ i, Real.logb Z (s.P i)) ≤ A →
      (s.η.modulus.absNorm : ℝ) ≤ Z^A →
      ∀ R seed0 : Ideal O, R ≠ 0 → (R.absNorm : ℝ) ≤ Z^P → Squarefree seed0 →
      ∀ C D : Ideal O, ∀ hC : Supported C, ∀ hD : Supported D,
      (C,D) ∈ CenteredMomentFirstSectors.commonLabels
        (CenteredMomentSourceRow.supportedColumns (activeSource
          (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed0)))
        (CenteredMomentSourceRow.supportedColumns (activeSource
          (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed0))) →
      ∀ E : Finset (CommonIndex C D), ∀ ξ₁ ξ₂ : RayCharacter,
      ∀ F : FixedPair s.η C D hC E ξ₁ ξ₂,
      ∀ K Csec Tsec σ ξ reserve : ℝ, 0 < K → 0 < Csec → 0 ≤ σ → 0 ≤ ξ → ξ ≤ 1 →
      0 ≤ reserve →
      Tsec ≤ Csec * firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun Q : CommonIndex C D => Q.val) E}) K (volume s) →
      ∀ rows : Finset O, ∀ W : 𝓢(ℝ,ℂ), ∀ n : Fin 4 → ℤ,
      Retained (frequencyRadius Tsec Z ξ) (n 1) →
      block s.η (fixedBadMask*idealGenerator R) 1 s.t
        (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed0)
        C D hC hD E rows W (fun _ => logAnnulus) K
        (dyadicScale (n 0)) (dyadicScale (n 1))
        (dyadicScale (n 2)) (dyadicScale (n 3)) ≠ 0 →
      ∀ B : actualAllocations s.pools D, ∀ t : ℝ, ∀ innerL : Ideal O,
      frozenCoefficient B.val D R s.ν s.W s.P ≠ 0 →
      let Km := mainRadius D C (swapSubset C D E) K (volume s) Z σ (frequencyLoss Z (32*Csec) ξ) reserve
      F.right.modulus = s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
        Ideal.span {primeSubsetGenerator (fun P : CommonIndex D C => P.val)
          (swapSubset C D E)*activeConductor D C} ∧
      Ready (child s D R B F.right t) (R*D) Km Z ξ (readyBudget A P) ∧
      (∀ I : Ideal O, coefficient (child s D R B F.right t) (R*D) innerL I ≠ 0 →
        lowerFactor N l a * volume (child s D R B F.right t) ≤ (I.absNorm : ℝ)) := by
  filter_upwards [eventually_main_packet N b b₁ b₂ l a A P hb hb₁ hb₂ hl ha hA hP] with Z hz
  refine ⟨hz.1, ?_⟩
  intro ι _ _ s hc he hs hW₁ hW₂ κ hκ hPs hcapacity hη R seed0 hR hRN hseed
    C D hC hD hlabel E ξ₁ ξ₂ F K Csec Tsec σ ξ reserve hK hCsec hσ hξ hξ1
    hreserve hsec rows W n hn hblock B t innerL hB
  dsimp only
  have hh := hz.2 s hc he hs hW₁ hW₂ κ hκ hPs hcapacity hη R seed0 hR hRN hseed
    C D hC hD hlabel E ξ₁ ξ₂ F F.right (Or.inr rfl)
    K Csec Tsec σ ξ reserve hK hCsec hσ hξ hξ1 hreserve hsec rows W n hn hblock
    true B t hB
  refine ⟨right_modulus s.η C D hC E ξ₁ ξ₂ F, ?_,
    main_lower_support N l a hl ha s hc hs hW₁ hW₂ D R innerL B F.right t⟩
  have hr : Ready (child s D R B F.right t) (R*D)
      (columnMainRadius C D E K (volume s) Z σ (frequencyLoss Z (32*Csec) ξ) reserve true)
      Z ξ (readyBudget A P) := hh.1
  rw [main_radius_right] at hr
  exact hr


-- @@ L103-208 verbatim
theorem eventually_right_error_packet (N : ℕ) (b b₁ b₂ l a A P : ℝ)
    (hb : 1 ≤ b) (hb₁ : 1 ≤ b₁) (hb₂ : 1 ≤ b₂)
    (hl : 0 < l) (ha : 0 < a) (hA : 0 ≤ A) (hP : 0 ≤ P) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι],
      ∀ s : Input ι, Fintype.card ι ≤ N → Endpoints b b₁ b₂ s → l ≤ s.lower →
      (∀ x, s.W₁ x ≠ 0 → a ≤ x) → (∀ x, s.W₂ x ≠ 0 → a ≤ x) →
      ∀ κ : ℝ, 1/6 ≤ κ → (∀ i, 1 ≤ s.P i) →
      length Z s.X₁ + length Z s.X₂ + 6*κ*(∑ i, Real.logb Z (s.P i)) ≤ A →
      (s.η.modulus.absNorm : ℝ) ≤ Z^A →
      ∀ R seed0 : Ideal O, R ≠ 0 → (R.absNorm : ℝ) ≤ Z^P → Squarefree seed0 →
      ∀ C D : Ideal O, ∀ hC : Supported C, ∀ hD : Supported D,
      (C,D) ∈ CenteredMomentFirstSectors.commonLabels
        (CenteredMomentSourceRow.supportedColumns (activeSource
          (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed0)))
        (CenteredMomentSourceRow.supportedColumns (activeSource
          (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed0))) →
      ∀ E : Finset (CommonIndex C D), ∀ ξ₁ ξ₂ : RayCharacter,
      ∀ F : FixedPair s.η C D hC E ξ₁ ξ₂,
      ∀ K Csec Tsec σ ξ reserve : ℝ, 0 < K → 0 < Csec → 0 ≤ σ → σ ≤ 1 →
      0 ≤ ξ → ξ ≤ 1 → 0 ≤ reserve →
      Tsec ≤ Csec * firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun Q : CommonIndex C D => Q.val) E}) K (volume s) →
      ∀ rows : Finset O, ∀ W : 𝓢(ℝ,ℂ), ∀ n : Fin 4 → ℤ,
      Retained (frequencyRadius Tsec Z ξ) (n 1) →
      block s.η (fixedBadMask*idealGenerator R) 1 s.t
        (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed0)
        C D hC hD E rows W (fun _ => logAnnulus) K
        (dyadicScale (n 0)) (dyadicScale (n 1))
        (dyadicScale (n 2)) (dyadicScale (n 3)) ≠ 0 →
      ∀ B : actualAllocations s.pools D, ∀ t : ℝ, ∀ innerL : Ideal O,
      frozenCoefficient B.val D R s.ν s.W s.P ≠ 0 →
      ∀ (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ) (Sbad : Finset (Ideal O)),
      fixedBadPrimes ⊆ Sbad →
      ∀ p ∈ elementPool (primePool M H Sbad (1/2) 1 (Z^(σ/3))),
      ∀ k : ℕ, k = 1 ∨ k = 6 ∨ k = 7 →
      (∀ i, ∀ I ∈ (activeInput (child s D R B F.right t)).slots i, IsCoprime (Ideal.span {p}) I) →
      ∀ Bp : actualAllocations (activeInput (child s D R B F.right t)).pools ((Ideal.span {p})^k),
      ∀ (χ : RayCharacter) (υ : Character) (v : ℝ),
      υ.modulus.absNorm ≤ radicalBound (childCharacter F.right χ) fixedBadMask p (errorMovingExponent (k-1)) →
      let d := errorInput s D R B F.right t (Ideal.span {p}) k Bp υ v
      let Re := (R*D)*(Ideal.span {p})^k
      let Ke := errorRadius D C (swapSubset C D E) K (volume s) Z σ (frequencyLoss Z (32*Csec) ξ) reserve p k
      F.right.modulus = s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
        Ideal.span {primeSubsetGenerator (fun P : CommonIndex D C => P.val)
          (swapSubset C D E)*activeConductor D C} ∧
      (((∀ I : Ideal O, coefficient d Re innerL I = 0) ∧ normalizedGaussSource d Re innerL ballProfile Ke = 0) ∨
      (Ready d Re Ke Z ξ (readyBudget A P) ∧
        (∀ I : Ideal O, coefficient d Re innerL I ≠ 0 →
          lowerFactor N l a * volume d ≤ (I.absNorm : ℝ)))) := by
  filter_upwards [eventually_active_error_ready N b b₁ b₂ 1 hb hb₁ hb₂ (by norm_num),
    eventual_parent_radius N b b₁ b₂ hb hb₁ hb₂,
    eventually_caps 1 (by norm_num)] with Z hready hradius hchars
  refine ⟨hready.1, ?_⟩
  intro ι _ _ s hc he hs hW₁ hW₂ κ hκ hPs hcapacity hη R seed0 hR hRN hseed
    C D hC hD hlabel E ξ₁ ξ₂ F K Csec Tsec σ ξ reserve hK hCsec hσ hσ1
    hξ hξ1 hreserve hsec rows W n hn hblock B t innerL hB M _ H Sbad hbad p hp k _hk
    hslot Bp χ υ v hυ
  dsimp only
  refine ⟨right_modulus s.η C D hC E ξ₁ ξ₂ F, ?_⟩
  let d := errorInput s D R B F.right t (Ideal.span {p}) k Bp υ v
  let Re := (R*D)*(Ideal.span {p})^k
  let Ke := errorRadius D C (swapSubset C D E) K (volume s) Z σ (frequencyLoss Z (32*Csec) ξ) reserve p k
  by_cases hdead : ∀ I : Ideal O, coefficient d Re innerL I = 0
  · exact Or.inl ⟨hdead, normalized_zero d Re innerL hdead ballProfile Ke⟩
  right
  have hlive : ∃ I : Ideal O, (original d Re innerL).beta I ≠ 0 := by
    simpa only [original_beta,not_forall] using hdead
  have hz := hready.1
  have hV := original_volume_cap s Z κ A hz hκ hPs hcapacity
  have hH := hradius.2 s hc he A hV
  have hz₁ := lower_profile_zero s.W₁ a ha hW₁
  have hz₂ := lower_profile_zero s.W₂ a ha hW₂
  have hcdata := actual_common_gates s R seed0 hseed hz₁ hz₂ C D hlabel
  have hCN := hcdata.2.2.2.2.2.1.trans hH
  have hJN : (D.absNorm : ℝ) ≤ Z^(A+1) := by
    exact hcdata.2.2.2.2.2.2.trans hH
  have hd := elementPool_data _
    (fun Q hQ => (primePool_data M H Sbad hbad (1/2) 1 (Z^(σ/3)) Q hQ).1)
    (fun Q hQ => (primePool_data M H Sbad hbad (1/2) 1 (Z^(σ/3)) Q hQ).2) p hp
  have hp0 : p ≠ 0 := hd.1.ne_zero
  have hQ : Ideal.span {p} ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr hp0
  have hpupper := (pool_prime_log_range M H Sbad hbad Z σ hz p hp).2
  have hPN : ((Ideal.span {p}).absNorm : ℝ) ≤ Z^(σ/3) := by
    have hh := Real.rpow_le_rpow_of_exponent_le hz.le hpupper
    rwa [Real.rpow_logb (zero_lt_one.trans hz) (ne_of_gt hz) (normValue_pos p hp0)] at hh
  have ht := hchars.2 s.η C D hC E ξ₁ ξ₂ F A (A+1) hη hCN
  have hv : (υ.modulus.absNorm : ℝ) ≤ Z^(3*A+3+σ/3) := by
    have hh := ht.2.2 F.right υ (Or.inr rfl) χ p hp0 (errorMovingExponent (k-1)) (σ/3) hυ hPN
    simpa only [show A+2*(A+1)+σ/3+1 = 3*A+3+σ/3 by ring] using hh
  have hE : Ideal.span {primeSubsetGenerator (fun Q : CommonIndex C D => Q.val) E} ≠ 0 :=
    Ideal.span_singleton_eq_bot.not.mpr (primeSubsetGenerator_ne_zero _ _)
  have hne := first_block_active_rows_nonempty s.η (fixedBadMask*idealGenerator R) 1 s.t
    _ _ C D hC hD E rows W K n hblock
  have hrec := (active_row_reciprocals C D _ hE K (volume s) Z Csec Tsec ξ
    (Real.logb Z (C.absNorm : ℝ))
    (Real.logb Z (D.absNorm : ℝ)) σ reserve
    hK (volume_pos s) hz hCsec hσ hreserve hsec rows n hn hne p k).2
  have hKe : 0 < Ke := by
    dsimp [Ke,errorRadius,errorCommonRadius]
    positivity
  have hKeInv : Ke⁻¹ ≤ Z^(0 : ℝ) := by
    simpa only [Ke,errorRadius,swapSubset_generator,nominal_swap,nominalLog,Real.rpow_zero] using hrec
  have hr := hready.2 s hc he D R innerL B F.right t hR hB _ hQ k hslot Bp υ v Ke
    A 0 P (3*A+3+σ/3) ξ hKe hξ hz₁ hz₂ hV hKeInv hRN hv hlive
  exact ⟨ready_mono _ _ Ke Z ξ _ _ hz.le (error_exponent_le A P σ ξ hA hP hσ1 hξ1) hr,
    error_lower_support N l a hl ha s hc hs hW₁ hW₂ D R innerL B F.right t _ k Bp υ v⟩


-- @@ L210-210 verbatim
end SevenEighths.CenteredMomentEnergyFirstRightAdmission


-- @@ L212-212 verbatim
end


-- @@ L214-214 verbatim
end OAI
