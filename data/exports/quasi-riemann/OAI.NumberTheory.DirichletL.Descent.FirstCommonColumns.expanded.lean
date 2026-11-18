import OAI.NumberTheory.DirichletL.Descent.FirstCommonMeasure


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace SevenEighths.InverseMoment

-- @@ L6-6 verbatim
open scoped BigOperators Classical SchwartzMap

-- @@ L7-7 verbatim
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion

-- @@ L8-8 verbatim
open JointLogSeparation FourierBridge MeasureTheory

-- @@ L9-9 verbatim
open ConcreteTraceCRT (eisEmbedding)

-- @@ L10-10 verbatim
noncomputable section

-- @@ L11-11 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L12-14 verbatim
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})


-- @@ L16-22 verbatim
def firstCommonColumn (F D : Finset ι) (C : Finset ι → ℂ) (negative : Bool)
    (χ : RayCharacter) (ω : ℝ → ℂ) (X t : ℝ) (h : Eis) : ℂ :=
  supportConjugateSum (fun i => Ideal.span {p i}) hg (F\D)
    (fun U => (if negative then star (supportRay p χ (D∪U)) else supportRay p χ (D∪U)) *
      C (D∪U) * (if negative then star (ω (primeProductNorm p U/X)*
        logPhase t (Real.log (primeProductNorm p U/X))) else
        ω (primeProductNorm p U/X)*logPhase t (Real.log (primeProductNorm p U/X)))) h


-- @@ L24-39 verbatim
theorem firstCommonColumn_pair (F D : Finset ι) (C₁ C₂ : Finset ι → ℂ)
    (r : RayCharacter × RayCharacter) (ω₁ ω₂ : ℝ → ℂ) (X₁ X₂ t₁ t₂ : ℝ) (h : Eis) :
    (∑ U ∈ (F\D).powerset, ∑ V ∈ (F\D).powerset,
      firstCommonCoefficient p hg C₁ C₂ r D U V h *
        (ω₁ (primeProductNorm p U/X₁)*ω₂ (primeProductNorm p V/X₂)) *
        logPhase t₁ (Real.log (primeProductNorm p U/X₁)) *
        logPhase t₂ (Real.log (primeProductNorm p V/X₂))) =
    star (firstCommonColumn p hg F D C₁ true r.1 ω₁ X₁ t₁ h) *
      firstCommonColumn p hg F D C₂ false r.2 ω₂ X₂ t₂ h := by
  simp only [firstCommonColumn,supportConjugateSum,star_sum,Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  simp only [firstCommonCoefficient,Bool.false_eq_true,ite_false,ite_true,star_mul,star_star]
  ring


-- @@ L41-43 verbatim
def firstCommonOuterLog (A₁ A₂ C R : ℝ) (d h : Eis) (D : Finset ι) (s : Fin 9 → ℝ) : Fin 7 → ℝ :=
  ![Real.log (A₁/s 0),Real.log (A₂/s 1),Real.log (C/s 2),Real.log (‖eisEmbedding d‖^2/s 3),
    Real.log (R/s 4),Real.log (primeProductNorm p D/s 5),Real.log (‖eisEmbedding h‖^2/s 6)]


-- @@ L45-62 verbatim
omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem first_common_source_mode (A₁ A₂ C R : ℝ) (d h : Eis) (s : Fin 9 → ℝ)
    (j : FirstCommonIndex ι) (z : Frequency × (Fin 9 → ℝ)) :
    pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope
      (firstRelativeLog (firstCommonNorms p A₁ A₂ C R d h j) s) z.1 z.2 =
    firstOuterPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2)
      (firstCommonOuterLog p A₁ A₂ C R d h j.2.1 s) *
    logPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7)
      (Real.log (primeProductNorm p j.2.2.1/s 7)) *
    logPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8)
      (Real.log (primeProductNorm p j.2.2.2/s 8)) := by
  have hy : firstRelativeLog (firstCommonNorms p A₁ A₂ C R d h j) s =
      firstCoordinates (firstCommonOuterLog p A₁ A₂ C R d h j.2.1 s)
        (Real.log (primeProductNorm p j.2.2.1/s 7))
        (Real.log (primeProductNorm p j.2.2.2/s 8)) := by
    funext i
    fin_cases i <;> rfl
  rw [hy,first_mode_split]


-- @@ L64-72 verbatim
def firstCommonSeparatedRow (F : Finset ι) (C₁ C₂ : Finset ι → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (A₁ A₂ C R : ℝ) (d h : Eis) (s : Fin 9 → ℝ)
    (z : Frequency × (Fin 9 → ℝ)) : ℂ :=
  let H := profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2
  ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2 *
    ∑ D ∈ F.powerset, supportMobius (fun i => Ideal.span {p i}) D * rowCoprimeMask (fun i => Ideal.span {p i}) D h *
      firstOuterPhase H (firstCommonOuterLog p A₁ A₂ C R d h D s) *
      star (firstCommonColumn p hg F D C₁ true r.1 ω₁ (s 7) (H 7) h) *
      firstCommonColumn p hg F D C₂ false r.2 ω₂ (s 8) (H 8) h


-- @@ L74-109 verbatim
theorem first_common_modes_eq_columns (F : Finset ι) (C₁ C₂ : Finset ι → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (A₁ A₂ C R : ℝ) (d h : Eis) (s : Fin 9 → ℝ)
    (z : Frequency × (Fin 9 → ℝ)) :
    (∑ j ∈ firstCommonIndices F,firstCommonWeight p hg C₁ C₂ h j *
      (ω₁ (primeProductNorm p j.2.2.1/s 7)*ω₂ (primeProductNorm p j.2.2.2/s 8)) *
      pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope
        (firstRelativeLog (firstCommonNorms p A₁ A₂ C R d h j) s) z.1 z.2) =
    firstCommonSeparatedRow p hg F C₁ C₂ ω₁ ω₂ A₁ A₂ C R d h s z := by
  simp only [firstCommonIndices,Finset.sum_product,Finset.sum_sigma,
    firstCommonWeight,firstCommonSeparatedRow,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro D hD
  let H := profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2
  calc
    _ = crossCoeff r.1 r.2 *
        (supportMobius (fun i => Ideal.span {p i}) D * rowCoprimeMask (fun i => Ideal.span {p i}) D h *
          firstOuterPhase H (firstCommonOuterLog p A₁ A₂ C R d h D s)) *
        (∑ U ∈ (F\D).powerset, ∑ V ∈ (F\D).powerset,
          firstCommonCoefficient p hg C₁ C₂ r D U V h *
            (ω₁ (primeProductNorm p U/s 7)*ω₂ (primeProductNorm p V/s 8)) *
            logPhase (H 7) (Real.log (primeProductNorm p U/s 7)) *
            logPhase (H 8) (Real.log (primeProductNorm p V/s 8))) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro U hU
      apply Finset.sum_congr rfl
      intro V hV
      rw [first_common_source_mode]
      dsimp only [H]
      ring
    _ = _ := by
      rw [firstCommonColumn_pair]
      dsimp only [H]
      ring


-- @@ L111-111 verbatim
end

-- @@ L112-112 verbatim
end SevenEighths.InverseMoment


-- @@ L114-114 verbatim
end OAI
