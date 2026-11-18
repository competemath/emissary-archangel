import OAI.NumberTheory.DirichletL.CubicSieve.IntegratedTransfer


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
open scoped BigOperators

-- @@ L8-8 verbatim
open MulChar AddChar

-- @@ L9-9 verbatim
open scoped BigOperators

-- @@ L10-10 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L11-11 verbatim
open scoped Topology

-- @@ L12-12 verbatim
open MeasureTheory Real

-- @@ L13-13 verbatim
open scoped FourierTransform SchwartzMap

-- @@ L14-14 verbatim
open Finset Complex

-- @@ L15-15 verbatim
open scoped Classical

-- @@ L16-16 verbatim
open scoped Classical

-- @@ L17-17 verbatim
open Filter Real Asymptotics

-- @@ L18-18 verbatim
open ActualEisensteinCubic

-- @@ L19-19 verbatim
open Filter

-- @@ L20-20 verbatim
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount

-- @@ L21-21 verbatim
open ActualEisensteinCubic ShortDraftLatticeCount

-- @@ L22-22 verbatim
open Filter

-- @@ L23-23 verbatim
open scoped Topology

-- @@ L24-24 verbatim
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic

-- @@ L25-25 verbatim
open MulChar AddChar

-- @@ L26-26 verbatim
open Filter Asymptotics

-- @@ L27-27 verbatim
open scoped LSeries.notation ArithmeticFunction.Moebius

-- @@ L28-28 verbatim
open Filter

-- @@ L29-29 verbatim
open MulChar AddChar

-- @@ L30-30 verbatim
open MulChar AddChar

-- @@ L31-31 verbatim
open scoped LSeries.notation ArithmeticFunction.Moebius

-- @@ L32-32 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L33-33 verbatim
open scoped Topology

-- @@ L34-34 verbatim
open Filter Asymptotics

-- @@ L35-35 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L36-36 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L37-37 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L38-38 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L39-39 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L40-40 verbatim
open Filter Asymptotics

-- @@ L41-41 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L42-42 verbatim
open scoped Topology

-- @@ L43-43 verbatim
open Filter Asymptotics Ideal NumberField

-- @@ L44-44 verbatim
open Filter

-- @@ L45-45 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L46-46 verbatim
open scoped Topology

-- @@ L47-47 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L48-48 verbatim
open scoped Topology

-- @@ L49-49 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L50-50 verbatim
open scoped Topology

-- @@ L51-51 verbatim
open MeasureTheory Real

-- @@ L52-52 verbatim
open scoped ContDiff FourierTransform SchwartzMap

-- @@ L53-53 verbatim
open scoped BigOperators Classical

-- @@ L54-54 verbatim
open scoped BigOperators Classical

-- @@ L55-55 verbatim
open scoped BigOperators Classical

-- @@ L56-56 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L57-57 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L58-58 verbatim
open scoped BigOperators Classical

-- @@ L59-59 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L60-60 verbatim
open scoped BigOperators Classical

-- @@ L61-61 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L62-62 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L63-63 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L64-64 verbatim
open scoped BigOperators Classical

-- @@ L65-65 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L66-66 verbatim
open MeasureTheory Set

-- @@ L67-67 verbatim
open scoped BigOperators

-- @@ L68-68 verbatim
open scoped BigOperators Classical

-- @@ L69-69 verbatim
open scoped BigOperators Classical

-- @@ L70-70 verbatim
open ActualEisensteinCubic UniqueFactorizationMonoid

-- @@ L71-71 verbatim
open scoped BigOperators


-- @@ L73-73 verbatim
open scoped BigOperators Classical SchwartzMap

-- @@ L74-74 verbatim
namespace SecondPassArithmetic


-- @@ L76-76 verbatim
section

-- @@ L77-77 verbatim
open ActualEisensteinCubic

-- @@ L78-78 verbatim
open FirstPassCubeLabels (actualFirstKernel originalLabelColumn cubeActiveSupport dilationLabel)

-- @@ L79-79 verbatim
open ConcreteTraceCRT (eisEmbedding)


-- @@ L81-144 verbatim
theorem first_passage_transfer_input_family {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F B : Finset ι) (hFB : Disjoint F B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ j ∈ B, 0 < v j)
    (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (H₁ H₂ : Finset ι → ℂ)
    (hΨ₁ : ∀ D ∈ F.powerset, ‖Ψ₁ (∏ i ∈ D, p i)‖ ≤ 1)
    (hΨ₂ : ∀ D ∈ F.powerset, ‖Ψ₂ (∏ i ∈ D, p i)‖ ≤ 1)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ)
    (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ x, V₁ x ≠ 0 → |x| ≤ M₁) (hV₂ : ∀ y, V₂ y ≠ 0 → |y| ≤ M₂)
    (J : ℕ) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ lengthScale : ℝ, 0 < lengthScale → ∀ c d : O, d ≠ 0 →
      ∀ (s : Finset (Ideal O × O)) (T : Finset O) (w : Ideal O × O → ℂ) (M Y : ℝ),
      0 ≤ M → 0 ≤ Y → (∀ x ∈ s, Squarefree x.1) → (∀ x ∈ s, x.2 ≠ 0) →
      (∀ x ∈ s, DescentWeightedCauchy.firstElementRowMap (dilationLabel p B v ε₁ ε₂) x ∈ T) →
      (∀ z ∈ T, z ≠ 0) → (∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) →
      (∀ x ∈ s, ‖w x‖ ≤ M) →
      ‖∑ x ∈ s, w x * actualFirstKernel p hp hcop hg F B v ε₁ ε₂
        (originalLabelColumn p hg B ε₁ ε₂ true (multiplicativeCoreColumn p Ψ₁ m₁ H₁)
          c (ConcretePrimeRowBridge.idealGenerator x.1))
        (originalLabelColumn p hg B ε₁ ε₂ false (multiplicativeCoreColumn p Ψ₂ m₂ H₂)
          c (ConcretePrimeRowBridge.idealGenerator x.1))
        W V₁ V₂ X₁ X₂ lengthScale d x.2‖ ≤
      (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) * (M * K * Y ^ deltaLoss) *
        Real.sqrt (firstInputFamilyEnergy p hg F B v ε₁ ε₂ true Ψ₁ m₁ H₁ V₁ X₁ c d J T) *
        Real.sqrt (firstInputFamilyEnergy p hg F B v ε₁ ε₂ false Ψ₂ m₂ H₂ V₂ X₂ c d J T) := by
  obtain ⟨K, hK, hb⟩ := FirstPassCubeLabels.first_passage_transfer p hp hinj hcop hg hc hpr F B hFB
    v ε₁ ε₂ hv (multiplicativeCoreColumn p Ψ₁ m₁ H₁) (multiplicativeCoreColumn p Ψ₂ m₂ H₂)
    W V₁ V₂ X₁ X₂ hX₁ hX₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ J deltaLoss hδ
  refine ⟨(32 * 512) * K, mul_nonneg (by norm_num) hK, ?_⟩
  intro lengthScale hL c d hd s T w M Y hM hY hs hnonzero hmap hT hnorm hw
  have hf := hb lengthScale hL c d hd s T w M Y hM hY hs hnonzero hmap hT hnorm hw
  have h₁ := firstOutputEnergy_le_input_family p hp hcop hg hc hpr F B v ε₁ ε₂ true
    Ψ₁ m₁ H₁ V₁ X₁ c d J T hΨ₁
  have h₂ := firstOutputEnergy_le_input_family p hp hcop hg hc hpr F B v ε₁ ε₂ false
    Ψ₂ m₂ H₂ V₂ X₂ c d J T hΨ₂
  have hq : 0 ≤ lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖ :=
    div_nonneg hL.le (norm_nonneg _)
  have hfactor : 0 ≤ M * K * Y ^ deltaLoss :=
    mul_nonneg (mul_nonneg hM hK) (Real.rpow_nonneg hY deltaLoss)
  calc
    _ ≤ (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) * (M * K * Y ^ deltaLoss) *
        Real.sqrt (FirstPassCubeLabels.firstOutputEnergy p hp hcop hg F B v ε₁ ε₂ true
          (multiplicativeCoreColumn p Ψ₁ m₁ H₁) V₁ X₁ c d J T) *
        Real.sqrt (FirstPassCubeLabels.firstOutputEnergy p hp hcop hg F B v ε₁ ε₂ false
          (multiplicativeCoreColumn p Ψ₂ m₂ H₂) V₂ X₂ c d J T) := hf
    _ ≤ (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) * (M * K * Y ^ deltaLoss) *
        Real.sqrt ((32 * 512) * firstInputFamilyEnergy p hg F B v ε₁ ε₂ true Ψ₁ m₁ H₁ V₁ X₁ c d J T) *
        Real.sqrt ((32 * 512) * firstInputFamilyEnergy p hg F B v ε₁ ε₂ false Ψ₂ m₂ H₂ V₂ X₂ c d J T) := by
      gcongr
    _ = _ := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 32 * 512),
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 32 * 512)]
      calc
        _ = (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) * (M * K * Y ^ deltaLoss) *
            (Real.sqrt (32 * 512)) ^ 2 *
            Real.sqrt (firstInputFamilyEnergy p hg F B v ε₁ ε₂ true Ψ₁ m₁ H₁ V₁ X₁ c d J T) *
            Real.sqrt (firstInputFamilyEnergy p hg F B v ε₁ ε₂ false Ψ₂ m₂ H₂ V₂ X₂ c d J T) := by ring
        _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 32 * 512)]; ring


-- @@ L146-146 verbatim
end

-- @@ L147-147 verbatim
section


-- @@ L149-149 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L150-150 verbatim
open MeasureTheory

-- @@ L151-151 verbatim
open ActualEisensteinCubic

-- @@ L152-152 verbatim
open ConcreteTraceCRT (eisEmbedding)

-- @@ L153-153 verbatim
open RayFourExpansion (RayCharacter)


-- @@ L155-180 verbatim
theorem exists_rowMajorant : ∃ W : 𝓢(ℝ, ℂ),
    (∀ s : ℝ, 0 ≤ (W s).re) ∧
    (∀ s : ℝ, |s| ≤ 1 → W s = 1) ∧
    (∀ s : ℝ, 2 < s → W s = 0) := by
  obtain ⟨U, hUc, hUs, hUone, hUts, hUzero⟩ :=
    FourierBridge.exists_complex_smooth_cutoff 1 (by norm_num)
  let f : ℝ → ℂ := fun s => U s * star (U s)
  have hfc : HasCompactSupport f := hUc.mul_right
  have hfs : ContDiff ℝ ∞ f := hUs.mul (Complex.conjCLE.contDiff.comp hUs)
  refine ⟨hfc.toSchwartzMap hfs, ?_, ?_, ?_⟩
  · intro s
    change 0 ≤ (U s * star (U s)).re
    simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
    nlinarith [sq_nonneg (U s).re, sq_nonneg (U s).im]
  · intro s hs
    change U s * star (U s) = 1
    rw [hUone s hs]
    norm_num
  · intro s hs
    change U s * star (U s) = 0
    have hUz : U s = 0 := by
      by_contra hne
      have hu := hUts (subset_tsupport U (by exact hne))
      norm_num at hu
      linarith [hu.2]
    simp [hUz]


-- @@ L182-182 verbatim
def rowMajorant : 𝓢(ℝ, ℂ) := Classical.choose exists_rowMajorant


-- @@ L184-185 verbatim
lemma rowMajorant_nonneg (s : ℝ) : 0 ≤ (rowMajorant s).re :=
  (Classical.choose_spec exists_rowMajorant).1 s


-- @@ L187-188 verbatim
lemma rowMajorant_one (s : ℝ) (hs : |s| ≤ 1) : rowMajorant s = 1 :=
  (Classical.choose_spec exists_rowMajorant).2.1 s hs


-- @@ L190-191 verbatim
lemma rowMajorant_zero (s : ℝ) (hs : 2 < s) : rowMajorant s = 0 :=
  (Classical.choose_spec exists_rowMajorant).2.2 s hs


-- @@ L193-193 verbatim
def rowMajorantBall (Y : ℝ) : Finset O := ShortDraftLatticeCount.rowNormBall (Nat.ceil (2 * Y))


-- @@ L195-205 verbatim
lemma rowMajorant_zero_outside (Y : ℝ) (hY : 0 < Y) (z : O)
    (hz : z ∉ rowMajorantBall Y) : rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) = 0 := by
  have hn : Nat.ceil (2 * Y) < Ideal.absNorm (Ideal.span {z}) := by
    apply Nat.lt_of_not_ge
    intro hn
    exact hz (ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le _ z hn)
  have hn' : (Nat.ceil (2 * Y) : ℝ) < (Ideal.absNorm (Ideal.span {z}) : ℝ) := by exact_mod_cast hn
  apply rowMajorant_zero
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  apply (lt_div_iff₀ hY).2
  linarith [Nat.le_ceil (2 * Y)]


-- @@ L207-212 verbatim
lemma rowMajorant_tsum_eq_sum (P : O → ℂ) (Y : ℝ) (hY : 0 < Y) :
    (∑' z : O, rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) * (↑(‖P z‖ ^ 2) : ℂ)) =
      ∑ z ∈ rowMajorantBall Y, rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) * (↑(‖P z‖ ^ 2) : ℂ) := by
  apply tsum_eq_sum
  intro z hz
  rw [rowMajorant_zero_outside Y hY z hz, zero_mul]


-- @@ L214-218 verbatim
lemma rowMajorant_summable (P : O → ℂ) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun z : O => rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) * (↑(‖P z‖ ^ 2) : ℂ)) := by
  apply (hasSum_sum_of_ne_finset_zero (s := rowMajorantBall Y) ?_).summable
  intro z hz
  rw [rowMajorant_zero_outside Y hY z hz, zero_mul]


-- @@ L220-241 verbatim
theorem finite_row_energy_le_rowMajorant (P : O → ℂ) (T : Finset O)
    (Y : ℝ) (hY : 0 < Y)
    (hT : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) :
    (∑ z ∈ T, ‖P z‖ ^ 2) ≤
      (∑' z : O, rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) * (↑(‖P z‖ ^ 2) : ℂ)).re := by
  have hs := rowMajorant_summable P Y hY
  rw [Complex.re_tsum hs]
  calc
    _ = ∑ z ∈ T, (rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) * (↑(‖P z‖ ^ 2) : ℂ)).re := by
      apply Finset.sum_congr rfl
      intro z hz
      have hratio : |‖eisEmbedding z‖ ^ 2 / Y| ≤ 1 := by
        rw [abs_of_nonneg (div_nonneg (sq_nonneg _) hY.le)]
        apply (div_le_one hY).2
        rw [eisEmbedding_norm_sq_eq_absNorm_span]
        exact hT z hz
      rw [rowMajorant_one _ hratio, one_mul, Complex.ofReal_re]
    _ ≤ _ := by
      apply (Complex.hasSum_re hs.hasSum).summable.sum_le_tsum
      intro z hz
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      exact mul_nonneg (rowMajorant_nonneg _) (sq_nonneg _)


-- @@ L243-245 verbatim
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})


-- @@ L247-267 verbatim
theorem firstCoreInputRow_finite_le_second_poisson
    (hp : ∀ i, p i ≠ 0)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (r : FirstCoreIndex) (t : ℝ) (T : Finset O) (Y : ℝ) (hY : 0 < Y)
    (hT : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) :
    (∑ z ∈ T, ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2) ≤
      (∑ G ∈ (F \ D).powerset, ∑ U ∈ ((F \ D) \ G).powerset, ∑ V' ∈ ((F \ D) \ G).powerset,
        if Disjoint U V' then
          overlapPairWeight p hg (firstCoreTwist negative χ Ψ r)
            (m * FirstPassCubeLabels.b0Label p B v ε₁ ε₂) (c * FirstPassCubeLabels.jLabel p B v ε₁ ε₂) d
            (firstCoreTest H V y negative t D) G U V' *
            maskedSecondDual p hg hp hinj G U V' rowMajorant Y
        else 0).re := by
  have he := firstCoreInputRow_smoothed_second_poisson p hg hp hinj hc F D B v ε₁ ε₂
    negative χ Ψ m H V y c d r t rowMajorant Y hY
  rw [← he]
  exact finite_row_energy_le_rowMajorant _ T Y hY hT


-- @@ L269-286 verbatim
theorem firstCoreInputRow_majorant_integrable
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (r : FirstCoreIndex) (Y : ℝ) (hY : 0 < Y)
    {k : ℝ → ℝ} (hk : Integrable k volume) :
    Integrable (fun t : ℝ => k t *
      (∑' z : O, rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) *
        (↑(‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2) : ℂ)).re) volume := by
  simp_rw [rowMajorant_tsum_eq_sum _ Y hY, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  simp only [Finset.mul_sum]
  apply integrable_finsetSum
  intro z hz
  convert (firstCoreInputRow_integrable p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r z hk).const_mul
    (rowMajorant (‖eisEmbedding z‖ ^ 2 / Y)).re using 1
  funext t
  ring


-- @@ L288-306 verbatim
theorem firstCoreInputRow_integrated_le_majorant
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (r : FirstCoreIndex) (T : Finset O) (Y : ℝ) (hY : 0 < Y)
    (hT : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y)
    {k : ℝ → ℝ} (hk : Integrable k volume) (hk0 : ∀ t, 0 ≤ k t) :
    (∫ t : ℝ, k t * ∑ z ∈ T,
      ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2) ≤
    ∫ t : ℝ, k t *
      (∑' z : O, rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) *
        (↑(‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2) : ℂ)).re := by
  apply integral_mono
  · simp only [Finset.mul_sum]
    exact integrable_finsetSum _ (fun z hz =>
      firstCoreInputRow_integrable p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r z hk)
  · exact firstCoreInputRow_majorant_integrable p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r Y hY hk
  · intro t
    exact mul_le_mul_of_nonneg_left (finite_row_energy_le_rowMajorant _ T Y hY hT) (hk0 t)


-- @@ L308-308 verbatim
end


-- @@ L310-310 verbatim
open ActualEisensteinCubic

-- @@ L311-311 verbatim
open FirstCauchyArithmetic (supportMobius)


-- @@ L313-316 verbatim
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})


-- @@ L318-322 verbatim
def secondPreKernelPair (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (m r c d e k₁ k₂ : O) (K : Finset ι → Finset ι → ℂ) : ℂ :=
  ∑ S ∈ F.powerset, ∑ T ∈ F.powerset, if Disjoint S T then
    star (secondPreColumn p hp hcop hg Ψ₁ (m * (e * r)) c d e k₁ (fun _ => 1) S) *
      secondPreColumn p hp hcop hg Ψ₂ (m * (e * r)) c d e k₂ (fun _ => 1) T * K S T else 0


-- @@ L324-330 verbatim
def secondChildKernelPair (F V : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (m r c d e k₁ k₂ : O) (K : Finset ι → Finset ι → ℂ) : ℂ :=
  ∑ N ∈ (F \ V).powerset, ∑ M ∈ (F \ V).powerset,
    star (secondChildColumn p hp hcop hg Ψ₁ (m * r) (c * e * ∏ i ∈ V, p i)
      (d * e * k₁) (fun _ => 1) N) *
    secondChildColumn p hp hcop hg Ψ₂ (m * r) (c * e * ∏ i ∈ V, p i)
      (d * e * k₂) (fun _ => 1) M * K (V ∪ N) (V ∪ M)


-- @@ L332-358 verbatim
theorem secondPreKernelPair_eq_children
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k₁ k₂ : O)
    (K : Finset ι → Finset ι → ℂ) :
    secondPreKernelPair p hp hcop hg F Ψ₁ Ψ₂ m r c d e k₁ k₂ K =
      ∑ V ∈ F.powerset, secondCommonWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k₁ k₂ V *
        secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k₁ k₂ K := by
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  unfold secondPreKernelPair
  rw [CoprimeMobiusExtension.double_sum_disjoint_reindexed]
  apply Finset.sum_congr rfl
  intro V hV
  rw [secondCommonWeight, supportMobius, prime_product_moebius _ hprime hinj]
  simp only [secondChildKernelPair, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro M hM
  have hdN : Disjoint V N := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hN) disjoint_sdiff_self_right
  have hdM : Disjoint V M := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hM) disjoint_sdiff_self_right
  rw [secondPreColumn_union p hp hcop hg hpr Ψ₁ m r c d e k₁ (fun _ => 1) V N hdN,
    secondPreColumn_union p hp hcop hg hpr Ψ₂ m r c d e k₂ (fun _ => 1) V M hdM, star_mul]
  ring


-- @@ L360-364 verbatim
def secondKernelPair (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (K : Finset ι → Finset ι → ℂ) : ℂ :=
  ∑ S ∈ F.powerset, ∑ T ∈ F.powerset, if Disjoint S T then
    secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k (fun _ => 1) (fun _ => 1) S T * K S T else 0


-- @@ L366-402 verbatim
theorem secondKernelPair_eq_pre
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (K : Finset ι → Finset ι → ℂ) :
    secondKernelPair p hp hg hinj F Ψ₁ Ψ₂ m r c d e k K =
      ∑ z : SecondRayIndex, secondRayCoefficient z *
        secondPreKernelPair p hp hcop hg F (secondRayMinus Ψ₁ z) (secondRayPlus Ψ₂ z)
          m r c d e k (-k) K := by
  have hterm (S T : Finset ι) :
      (if Disjoint S T then secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k
        (fun _ => 1) (fun _ => 1) S T * K S T else 0) =
      ∑ z : SecondRayIndex, secondRayCoefficient z * (if Disjoint S T then
        star (secondPreColumn p hp hcop hg (secondRayMinus Ψ₁ z) (m * (e * r)) c d e k (fun _ => 1) S) *
        secondPreColumn p hp hcop hg (secondRayPlus Ψ₂ z) (m * (e * r)) c d e (-k) (fun _ => 1) T * K S T else 0) := by
    by_cases hd : Disjoint S T
    · simp only [ite_eq_left hd, secondGaussTerm]
      have h := congrArg (fun a : ℂ => a * K S T)
        (second_gauss_ray_expansion p hp hcop hg hinj hc hpr Ψ₁ Ψ₂
          (m * (e * r)) c d e k (fun _ => 1) (fun _ => 1) S T hd)
      simpa only [Fintype.sum_prod_type, secondRayCoefficient, secondRayMinus,
        secondRayPlus, Finset.sum_mul, mul_assoc] using h
    · simp [hd]
  unfold secondKernelPair
  simp_rw [hterm]
  calc
    _ = ∑ S ∈ F.powerset, ∑ z : SecondRayIndex, ∑ T ∈ F.powerset,
        secondRayCoefficient z * (if Disjoint S T then
        star (secondPreColumn p hp hcop hg (secondRayMinus Ψ₁ z) (m * (e * r)) c d e k (fun _ => 1) S) *
        secondPreColumn p hp hcop hg (secondRayPlus Ψ₂ z) (m * (e * r)) c d e (-k) (fun _ => 1) T * K S T else 0) := by
      apply Finset.sum_congr rfl
      intro S hS
      exact Finset.sum_comm
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [secondPreKernelPair, Finset.mul_sum]


-- @@ L404-417 verbatim
theorem secondKernelPair_eq_children
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (K : Finset ι → Finset ι → ℂ) :
    secondKernelPair p hp hg hinj F Ψ₁ Ψ₂ m r c d e k K =
      ∑ z : SecondRayIndex, ∑ V ∈ F.powerset,
        secondTotalWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k (z,V) *
          secondChildKernelPair p hp hcop hg F V (secondRayMinus Ψ₁ z) (secondRayPlus Ψ₂ z)
            m r c d e k (-k) K := by
  rw [secondKernelPair_eq_pre p hp hcop hg hinj hc hpr]
  simp only [secondPreKernelPair_eq_children p hp hcop hg hinj hpr,
    secondTotalWeight, Finset.mul_sum, mul_assoc]


-- @@ L419-419 verbatim
end SecondPassArithmetic


-- @@ L421-421 verbatim
namespace CubicEisenstein

-- @@ L422-422 verbatim
open scoped BigOperators Classical MatrixGroups Matrix


-- @@ L424-424 verbatim
open ActualEisensteinCubic CubicKubota ConcreteTraceCRT CubicJacobiGlobal


-- @@ L426-426 verbatim
def denominatorCondition (c d : O) : Prop := IsCoprime c d ∧ (3 : O) ∣ d-1

-- @@ L427-427 verbatim
abbrev AdmissibleDenominator (c : O) := {d : O // denominatorCondition c d}

-- @@ L428-428 verbatim
abbrev LevelLower := {c : O // (3 : O) ∣ c}


-- @@ L430-440 verbatim
lemma denominatorCondition_shift (c d n : O) :
    denominatorCondition c (d+3*c*n) ↔ denominatorCondition c d := by
  constructor
  · rintro ⟨⟨a,b,h⟩,hd⟩
    refine ⟨⟨a+b*3*n,b,by linear_combination h⟩, ?_⟩
    have h3 : (3 : O) ∣ 3*c*n := ⟨c*n,by ring⟩
    convert dvd_sub hd h3 using 1 ; ring
  · rintro ⟨⟨a,b,h⟩,hd⟩
    refine ⟨⟨a-b*3*n,b,by linear_combination h⟩, ?_⟩
    have h3 : (3 : O) ∣ 3*c*n := ⟨c*n,by ring⟩
    convert dvd_add hd h3 using 1 ; ring


-- @@ L442-451 verbatim
lemma row_symbol_shift (c d n : O) (hc : (3 : O) ∣ c) (hd : (3 : O) ∣ d-1) :
    symbol c (d+3*c*n)=symbol c d := by
  have hdn : (3 : O) ∣ d+3*c*n-1 := by
    convert dvd_add hd (show (3 : O) ∣ 3*c*n from ⟨c*n,by ring⟩) using 1 ; ring
  have h9 : (9 : O) ∣ d+3*c*n-d := by
    obtain ⟨c0,rfl⟩ := hc
    exact ⟨c0*n,by ring⟩
  exact symbol_denominator_congr c (d+3*c*n) d
    (lambda_sq_dvd_three.trans hdn) (lambda_sq_dvd_three.trans hd) h9
    ⟨3*n,by ring⟩


-- @@ L453-460 verbatim
def primitiveSigmaEquiv : PrimitiveRow ≃ Σ c : LevelLower, AdmissibleDenominator c.1 where
  toFun r := ⟨⟨r.1 0,r.2.2.1⟩,⟨r.1 1,r.2.1,r.2.2.2⟩⟩
  invFun p := ⟨![p.1.1,p.2.1],p.2.2.1,p.1.2,p.2.2.2⟩
  left_inv r := by
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  right_inv p := by rfl


-- @@ L462-462 verbatim
abbrev DenominatorResidue (c : O) := O ⧸ Ideal.span {3*c}

-- @@ L463-464 verbatim
def denominatorRep (c : O) (r : DenominatorResidue c) : O :=
  GaussianShiftedPartition.representative (3*c) r

-- @@ L465-467 verbatim
lemma denominatorRep_spec (c : O) (r : DenominatorResidue c) :
    Ideal.Quotient.mk (Ideal.span {3*c}) (denominatorRep c r)=r :=
  GaussianShiftedPartition.representative_spec (3*c) r

-- @@ L468-469 verbatim
abbrev AdmissibleResidue (c : O) :=
  {r : DenominatorResidue c // denominatorCondition c (denominatorRep c r)}


-- @@ L471-473 verbatim
lemma finite_admissibleResidue (c : O) (hc : c ≠ 0) : Finite (AdmissibleResidue c) := by
  let : Finite (DenominatorResidue c) := finite_quotient_span (mul_ne_zero (by norm_num) hc)
  infer_instance


-- @@ L475-476 verbatim
def residueDenominatorMap (c : O) (p : AdmissibleResidue c × O) : AdmissibleDenominator c :=
  ⟨denominatorRep c p.1.1+3*c*p.2,(denominatorCondition_shift c _ _).2 p.1.2⟩


-- @@ L478-512 verbatim
lemma residueDenominatorMap_bijective (c : O) (hc : c ≠ 0) :
    Function.Bijective (residueDenominatorMap c) := by
  have h3c : 3*c ≠ 0 := mul_ne_zero (by norm_num) hc
  have hq (r : DenominatorResidue c) (n : O) :
      Ideal.Quotient.mk (Ideal.span {3*c}) (denominatorRep c r+3*c*n)=r := by
    have hzero : Ideal.Quotient.mk (Ideal.span {3*c}) (3*c)=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    rw [map_add, map_mul, hzero, zero_mul, add_zero, denominatorRep_spec]
  constructor
  · rintro ⟨r,n⟩ ⟨t,m⟩ heq
    have h := congrArg Subtype.val heq
    change denominatorRep c r.1+3*c*n=denominatorRep c t.1+3*c*m at h
    have hrt : r=t := by
      apply Subtype.ext
      simpa only [hq] using congrArg (Ideal.Quotient.mk (Ideal.span {3*c})) h
    subst t
    have hnm : n=m := mul_left_cancel₀ h3c (add_left_cancel h)
    subst m
    rfl
  · intro d
    let r : DenominatorResidue c := Ideal.Quotient.mk (Ideal.span {3*c}) d.1
    have hr : Ideal.Quotient.mk (Ideal.span {3*c}) (denominatorRep c r)=r := denominatorRep_spec c r
    have hdiv : 3*c ∣ d.1-denominatorRep c r := by
      apply Ideal.mem_span_singleton.mp
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
      exact hr.symm
    obtain ⟨n,hn⟩ := hdiv
    have hd : d.1=denominatorRep c r+3*c*n := by linear_combination hn
    have hrcond : denominatorCondition c (denominatorRep c r) := by
      apply (denominatorCondition_shift c _ n).1
      rw [← hd]
      exact d.2
    refine ⟨(⟨r,hrcond⟩,n), ?_⟩
    apply Subtype.ext
    exact hd.symm


-- @@ L514-516 verbatim
def residueDenominatorEquiv (c : O) (hc : c ≠ 0) :
    AdmissibleResidue c × O ≃ AdmissibleDenominator c :=
  Equiv.ofBijective (residueDenominatorMap c) (residueDenominatorMap_bijective c hc)


-- @@ L518-519 verbatim
lemma residueDenominatorEquiv_val (c : O) (hc : c ≠ 0) (p : AdmissibleResidue c × O) :
    ((residueDenominatorEquiv c hc) p).1=denominatorRep c p.1.1+3*c*p.2 := rfl


-- @@ L521-523 verbatim
def primitiveTerm (z : ℂ) (v : ℝ) (s : ℂ) (c d : O) : ℂ :=
  eisEmbedding (symbol c d) *
    ((v/(‖eisEmbedding c*z+eisEmbedding d‖^2+‖eisEmbedding c‖^2*v^2):ℝ):ℂ)^s


-- @@ L525-529 verbatim
theorem primitive_terms_summable (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re) :
    Summable (fun p : Σ c : LevelLower, AdmissibleDenominator c.1 =>
      primitiveTerm z v s p.1.1 p.2.1) := by
  apply primitiveSigmaEquiv.summable_iff.mp
  exact (primitive_rows_summable_norm z v hv s hs).of_norm


-- @@ L531-536 verbatim
theorem upperEisenstein_eq_by_lower (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re) :
    upperEisenstein z v hv s=
      ∑' c : LevelLower, ∑' d : AdmissibleDenominator c.1, primitiveTerm z v s c.1 d.1 := by
  rw [upperEisenstein_eq_primitive_rows]
  exact (primitiveSigmaEquiv.tsum_eq (fun p : Σ c : LevelLower, AdmissibleDenominator c.1 =>
    primitiveTerm z v s p.1.1 p.2.1)).trans (primitive_terms_summable z v hv s hs).tsum_sigma


-- @@ L538-544 verbatim
theorem denominator_sum_residues (c : O) (hc : c ≠ 0) (f : O → ℂ)
    (hf : Summable (fun d : AdmissibleDenominator c => f d.1)) :
    (∑' d : AdmissibleDenominator c, f d.1)=
      ∑' r : AdmissibleResidue c, ∑' n : O, f (denominatorRep c r.1+3*c*n) := by
  have hsum := (residueDenominatorEquiv c hc).summable_iff.mpr hf
  exact ((residueDenominatorEquiv c hc).tsum_eq
    (fun d : AdmissibleDenominator c => f d.1)).symm.trans hsum.tsum_prod


-- @@ L546-556 verbatim
lemma primitiveTerm_shift (z : ℂ) (v : ℝ) (s : ℂ) (c d n : O)
    (hc : (3 : O) ∣ c) (hd : (3 : O) ∣ d-1) :
    primitiveTerm z v s c (d+3*c*n)=
      primitiveTerm (z+3*eisEmbedding n) v s c d := by
  unfold primitiveTerm
  rw [row_symbol_shift c d n hc hd]
  have harg : eisEmbedding c*z+eisEmbedding (d+3*c*n)=
      eisEmbedding c*(z+3*eisEmbedding n)+eisEmbedding d := by
    simp only [map_add,map_mul,map_ofNat]
    ring
  rw [harg]


-- @@ L558-560 verbatim
lemma denominator_zero_unique (d : AdmissibleDenominator 0) : d.1=1 := by
  apply A3_primary_unit_eq_one _ _ (lambda_sq_dvd_three.trans d.2.2)
  simpa only [isCoprime_zero_left] using d.2.1


-- @@ L562-570 verbatim
lemma zero_lower_sum (z : ℂ) (v : ℝ) (s : ℂ) :
    (∑' d : AdmissibleDenominator 0, primitiveTerm z v s 0 d.1)=(v:ℂ)^s := by
  let d0 : AdmissibleDenominator 0 := ⟨1,isCoprime_one_right,by simp⟩
  rw [tsum_eq_single d0]
  · simp [primitiveTerm,d0,symbol_one]
  · intro d hd
    exfalso
    apply hd
    exact Subtype.ext (denominator_zero_unique d)


-- @@ L572-574 verbatim
def residueSeries (z : ℂ) (v : ℝ) (s : ℂ) (c : O) : ℂ :=
  ∑' r : AdmissibleResidue c, ∑' n : O,
    primitiveTerm (z+3*eisEmbedding n) v s c (denominatorRep c r.1)


-- @@ L576-594 verbatim
theorem upperEisenstein_eq_residue_series (z : ℂ) (v : ℝ) (hv : 0 < v)
    (s : ℂ) (hs : 2 < s.re) :
    upperEisenstein z v hv s =
      ∑' c : LevelLower, if c.1=0 then (v:ℂ)^s else residueSeries z v s c.1 := by
  rw [upperEisenstein_eq_by_lower z v hv s hs]
  apply tsum_congr
  rintro ⟨c,hlevel⟩
  dsimp only
  split_ifs with hc
  · subst c
    exact zero_lower_sum z v s
  · have hsum : Summable (fun d : AdmissibleDenominator c => primitiveTerm z v s c d.1) :=
      (primitive_terms_summable z v hv s hs).sigma_factor ⟨c, hlevel⟩
    rw [denominator_sum_residues c hc (fun d : O => primitiveTerm z v s c d) hsum]
    apply tsum_congr
    intro r
    apply tsum_congr
    intro n
    exact primitiveTerm_shift z v s c (denominatorRep c r.1) n hlevel r.2.2


-- @@ L596-601 verbatim
lemma residueSeries_finite (z : ℂ) (v : ℝ) (s : ℂ) (c : O) (hc : c ≠ 0) :
    letI : Fintype (AdmissibleResidue c) := @Fintype.ofFinite _ (finite_admissibleResidue c hc)
    residueSeries z v s c = ∑ r : AdmissibleResidue c, ∑' n : O,
      primitiveTerm (z+3*eisEmbedding n) v s c (denominatorRep c r.1) := by
  let : Fintype (AdmissibleResidue c) := @Fintype.ofFinite _ (finite_admissibleResidue c hc)
  exact tsum_fintype _


-- @@ L603-603 verbatim
end CubicEisenstein


-- @@ L605-605 verbatim
open MeasureTheory Set Module

-- @@ L606-606 verbatim
open scoped BigOperators Classical ENNReal


-- @@ L608-608 verbatim
namespace CubicEisenstein

-- @@ L609-609 verbatim
open ActualEisensteinCubic ConcreteTraceCRT EisensteinEmbedding EisensteinSchwartzPoisson

-- @@ L610-610 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L612-613 verbatim
def periodBasis : Basis (Fin 2) ℝ ℂ :=
  Complex.basisOneI.map (eisensteinLatticeMap 3 (by norm_num)).toLinearEquiv

-- @@ L614-615 verbatim
lemma periodBasis_zero : periodBasis 0=3 := by
  simp [periodBasis,eisensteinLatticeMap,scaledBasisEquiv_apply]

-- @@ L616-617 verbatim
lemma periodBasis_one : periodBasis 1=3*omega3 := by
  simp [periodBasis,eisensteinLatticeMap,scaledBasisEquiv_apply]


-- @@ L619-619 verbatim
def periodLattice : Submodule ℤ ℂ := Submodule.span ℤ (Set.range periodBasis)

-- @@ L620-620 verbatim
def periodDomain : Set ℂ := ZSpan.fundamentalDomain periodBasis


-- @@ L622-622 verbatim
instance : Countable periodLattice := by unfold periodLattice; infer_instance

-- @@ L623-624 verbatim
instance : VAddInvariantMeasure periodLattice ℂ volume :=
  inferInstanceAs (VAddInvariantMeasure periodLattice.toAddSubgroup ℂ volume)


-- @@ L626-627 verbatim
lemma periodDomain_fundamental : IsAddFundamentalDomain periodLattice periodDomain volume :=
  ZSpan.isAddFundamentalDomain periodBasis volume

-- @@ L628-629 verbatim
lemma periodDomain_measurable : MeasurableSet periodDomain :=
  ZSpan.fundamentalDomain_measurableSet periodBasis


-- @@ L631-641 verbatim
lemma three_embedding_mem (n : O) : 3*eisEmbedding n ∈ periodLattice := by
  have hzero : periodBasis 0 ∈ periodLattice := Submodule.subset_span ⟨0,rfl⟩
  have hone : periodBasis 1 ∈ periodLattice := Submodule.subset_span ⟨1,rfl⟩
  have h := periodLattice.add_mem
    (periodLattice.smul_mem (ActualEisensteinCoordinates.coords n).1 hzero)
    (periodLattice.smul_mem (ActualEisensteinCoordinates.coords n).2 hone)
  rw [periodBasis_zero,periodBasis_one] at h
  convert h using 1
  conv_lhs => rw [← ActualEisensteinCoordinates.eval_coords n,eisEmbedding_eval]
  simp only [zsmul_eq_mul,]
  ring


-- @@ L643-643 verbatim
def periodPoint (n : O) : periodLattice := ⟨3*eisEmbedding n,three_embedding_mem n⟩

-- @@ L644-644 verbatim
lemma periodPoint_val (n : O) : (periodPoint n : ℂ)=3*eisEmbedding n := rfl

-- @@ L645-662 verbatim
lemma periodPoint_bijective : Function.Bijective periodPoint := by
  constructor
  · intro n m h
    apply eisEmbedding_injective
    exact mul_left_cancel₀ (by norm_num : (3:ℂ)≠0) (congrArg Subtype.val h)
  · intro p
    have h := (periodBasis.mem_span_iff_repr_mem ℤ p.1).mp p.2
    obtain ⟨a,ha⟩ := h 0
    obtain ⟨b,hb⟩ := h 1
    change (a:ℝ)=_ at ha
    change (b:ℝ)=_ at hb
    refine ⟨ActualEisensteinCoordinates.eval a b, ?_⟩
    apply Subtype.ext
    change 3*eisEmbedding (ActualEisensteinCoordinates.eval a b)=p.1
    rw [← periodBasis.sum_repr p.1,Fin.sum_univ_two,← ha,← hb,
      periodBasis_zero,periodBasis_one,eisEmbedding_eval]
    simp only [Complex.real_smul,Complex.ofReal_intCast]
    ring


-- @@ L664-664 verbatim
def periodEquiv : O ≃ periodLattice := Equiv.ofBijective _ periodPoint_bijective


-- @@ L666-675 verbatim
theorem integral_eq_period_integrals (f : ℂ → ℂ) (hf : Integrable f) :
    (∫ z : ℂ, f z)=∑' n : O,∫ z in periodDomain,f (z+3*eisEmbedding n) := by
  rw [periodDomain_fundamental.integral_eq_tsum'' f hf]
  rw [← periodEquiv.tsum_eq]
  apply tsum_congr
  intro n
  apply setIntegral_congr_fun periodDomain_measurable
  intro z hz
  change f (3*eisEmbedding n+z)=f (z+3*eisEmbedding n)
  rw [add_comm]


-- @@ L677-686 verbatim
theorem lintegral_eq_period_lintegrals (f : ℂ → ℝ≥0∞) :
    (∫⁻ z : ℂ, f z)=∑' n : O,∫⁻ z in periodDomain,f (z+3*eisEmbedding n) := by
  rw [periodDomain_fundamental.lintegral_eq_tsum'' f]
  rw [← periodEquiv.tsum_eq]
  apply tsum_congr
  intro n
  apply setLIntegral_congr_fun periodDomain_measurable
  intro z hz
  change f (3*eisEmbedding n+z)=f (z+3*eisEmbedding n)
  rw [add_comm]


-- @@ L688-698 verbatim
lemma periodDomain_volume : volume periodDomain=ENNReal.ofReal (9*Real.sqrt 3/2) := by
  have hunit : volume (ZSpan.fundamentalDomain Complex.basisOneI)=1 := by
    rw [measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped Complex.basisOneI volume)]
    exact Complex.orthonormalBasisOneI.volume_parallelepiped
  rw [periodDomain,ZSpan.measure_fundamentalDomain periodBasis volume Complex.basisOneI,hunit,mul_one]
  congr 1
  rw [Basis.det_apply,Matrix.det_fin_two]
  norm_num [Basis.toMatrix_apply,periodBasis_zero,periodBasis_one,
    Complex.coe_basisOneI_repr,EisensteinEmbedding.omega3_im]
  rw [abs_of_nonneg (by positivity)]
  ring


-- @@ L700-703 verbatim
lemma periodization_lintegral_norm_ne_top (f : ℂ → ℂ) (hf : Integrable f) :
    (∑' n : O,∫⁻ z in periodDomain,‖f (z+3*eisEmbedding n)‖ₑ) ≠ ⊤ := by
  rw [← lintegral_eq_period_lintegrals (fun z => ‖f z‖ₑ)]
  exact hf.hasFiniteIntegral.ne


-- @@ L705-712 verbatim
theorem integral_periodization (f : ℂ → ℂ) (hf : Integrable f) :
    (∫ z in periodDomain,∑' n : O,f (z+3*eisEmbedding n))=∫ z : ℂ,f z := by
  let : Countable O := latticeCoordEquiv.injective.countable
  rw [integral_tsum]
  · exact (integral_eq_period_integrals f hf).symm
  · intro n
    exact (hf.comp_add_right (3*eisEmbedding n)).aestronglyMeasurable.restrict
  · exact periodization_lintegral_norm_ne_top f hf


-- @@ L714-714 verbatim
end CubicEisenstein


-- @@ L716-716 verbatim
end


-- @@ L718-718 verbatim
end OAI
