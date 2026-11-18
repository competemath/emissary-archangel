import OAI.NumberTheory.DirichletL.Descent.SecondSourceAttachment
import OAI.NumberTheory.DirichletL.Inversion.SecondPrincipalCaller


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
namespace SevenEighths.InverseMoment

-- @@ L7-7 verbatim
open scoped BigOperators Classical SchwartzMap

-- @@ L8-8 verbatim
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers RayFourExpansion

-- @@ L9-9 verbatim
open InverseInitialArithmetic (sourceIdeal)

-- @@ L10-10 verbatim
noncomputable section

-- @@ L11-11 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L12-14 verbatim
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})


-- @@ L16-29 verbatim
omit [DecidableEq ι] in
theorem secondInputCoefficient_old_divisor_mask (Ψ : Eis →* ℂ) (m c d : Eis)
    (H : Finset ι → ℂ) (S : Finset ι) :
    secondInputCoefficient p hg Ψ (m*d) c d H S = secondInputCoefficient p hg Ψ m c d H S := by
  rw [secondInputCoefficient_fixed_mask p hg Ψ m d c d H S]
  have hd := row_power_mul_mask_power (fun i => Ideal.span {p i}) hg S d 1 1 (by decide)
  simp only [pow_one] at hd
  unfold secondInputCoefficient
  calc
    _ = Ψ (∏ i∈S,p i)*rowCoprimeMask (fun i => Ideal.span {p i}) S m*
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S c^4*
      (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S d*
        rowCoprimeMask (fun i => Ideal.span {p i}) S d)*H S := by ring
    _ = _ := by rw [hd]


-- @@ L31-34 verbatim
theorem inputConjugateRow_old_divisor_mask (F : Finset ι) (Ψ : Eis →* ℂ) (m c d : Eis)
    (H : Finset ι → ℂ) (k : Eis) :
    inputConjugateRow p hg F Ψ (m*d) c d H k = inputConjugateRow p hg F Ψ m c d H k := by
  simp only [inputConjugateRow,FirstCauchyArithmetic.supportConjugateSum,secondInputCoefficient_old_divisor_mask]


-- @@ L36-40 verbatim
theorem inputConjugateRow_puncture_span (F : Finset ι) (Ψ : Eis →* ℂ) (m₁ m₂ c d : Eis)
    (hspan : Ideal.span {m₁} = (Ideal.span {m₂} : Ideal Eis)) (H : Finset ι → ℂ) (k : Eis) :
    inputConjugateRow p hg F Ψ m₁ c d H k = inputConjugateRow p hg F Ψ m₂ c d H k := by
  simp only [inputConjugateRow,FirstCauchyArithmetic.supportConjugateSum,secondInputCoefficient,
    rowCoprimeMask_eq_of_span_eq (fun i => Ideal.span {p i}) _ hspan]


-- @@ L42-62 verbatim
theorem fresh_input_parent_mask {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (F D : Finset ι) (hq : parent.quotient = sourceIdeal p D)
    (Ψ : Eis →* ℂ) (m : Eis) (H : Finset ι → ℂ) (k : Eis) :
    inputConjugateRow p hg F Ψ
      ((m*b0Label p parent.cube.support (fun i => parent.cube.leftExponent i+parent.cube.rightExponent i)
        parent.cube.leftBit parent.cube.rightBit)*∏ i∈D,p i)
      (secondParentLabel p parent) (secondParentDivisor p parent) H k =
    inputConjugateRow p hg F Ψ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) H k := by
  rw [←inputConjugateRow_old_divisor_mask]
  apply inputConjugateRow_puncture_span
  let b := b0Label p parent.cube.support (fun i => parent.cube.leftExponent i+parent.cube.rightExponent i)
    parent.cube.leftBit parent.cube.rightBit
  let d := secondParentDivisor p parent
  change Ideal.span {((m*b)*(∏ i∈D,p i))*d} =
    (Ideal.span {(m*ConcretePrimeRowBridge.idealGenerator parent.quotient)*b*d} : Ideal Eis)
  rw [show ((m*b)*(∏ i∈D,p i))*d = (m*b*d)*(∏ i∈D,p i) by ring,
    show (m*ConcretePrimeRowBridge.idealGenerator parent.quotient)*b*d =
      (m*b*d)*ConcretePrimeRowBridge.idealGenerator parent.quotient by ring]
  simp only [←Ideal.span_singleton_mul_span_singleton,
    ConcretePrimeRowBridge.span_idealGenerator,hq,sourceIdeal]


-- @@ L64-93 verbatim
theorem first_fresh_parent_truncated
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (parent : SecondParentSource ι Jo) (F D : Finset ι)
    (hq : parent.quotient = sourceIdeal p D)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis)
    (H : Finset ι → ℂ) (ω : ℝ → ℂ) (X t Y : ℝ) (hY : 0 < Y) (core : FirstCoreIndex)
    (K : Finset ι → Finset ι → Finset Eis) :
    let Ψ₀ := firstCoreTwist negative χ Ψ core
    let H₀ := firstCoreTest H (fun u => ω (Real.exp u))
      (columnLog p (primeProductNorm p D*X)) negative (-t) D
    firstFreshSecondPoisson p hp hg hinj F D parent.cube.support
      (fun i => parent.cube.leftExponent i+parent.cube.rightExponent i)
      parent.cube.leftBit parent.cube.rightBit negative χ Ψ m H ω X
      (∏ i∈parent.firstCommon,p i) (secondParentDivisor p parent) core t Y =
    truncatedSecondSource p hp hg hinj F Ψ₀ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y K +
    secondSourceTail p hp hg hinj F Ψ₀ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y K := by
  intro Ψ₀ H₀
  rw [firstFreshSecondPoisson_fixed_pool p hp hg hinj hc (hY:=hY)]
  rw [←inputConjugateRow_smoothed_second_poisson p hg hp hinj hc _ _ _ _ _ _ _ _ hY]
  change (∑' k : Eis,rowMajorant (‖ConcreteTraceCRT.eisEmbedding k‖^2/Y)*
    (‖inputConjugateRow p hg F Ψ₀
      ((m*b0Label p parent.cube.support (fun i => parent.cube.leftExponent i+parent.cube.rightExponent i)
        parent.cube.leftBit parent.cube.rightBit)*∏ i∈D,p i)
      (secondParentLabel p parent) (secondParentDivisor p parent) H₀ k‖^2 : ℝ)) = _
  simp_rw [fresh_input_parent_mask p hg parent F D hq Ψ₀ m H₀]
  exact inputConjugateRow_eq_truncated_add_tail p hp hg hinj hc F Ψ₀ (secondParentPuncture p m parent)
    (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y hY K


-- @@ L95-95 verbatim
end

-- @@ L96-96 verbatim
end SevenEighths.InverseMoment


-- @@ L98-98 verbatim
end OAI
