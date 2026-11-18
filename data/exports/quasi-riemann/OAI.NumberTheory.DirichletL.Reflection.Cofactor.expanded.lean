import OAI.NumberTheory.DirichletL.Reflection.Local


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace SevenEighths.InverseReflectedPhase

-- @@ L6-6 verbatim
open scoped BigOperators Classical

-- @@ L7-7 verbatim
open ActualEisensteinCubic CubicEisenstein CompletedGauss ConcreteTraceCRT

-- @@ L8-8 verbatim
open LocalReflectionBrackets FiniteGaussPhase

-- @@ L9-9 verbatim
noncomputable section

-- @@ L10-10 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L11-11 verbatim
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

-- @@ L12-12 verbatim
noncomputable local instance phaseField (P : Ideal Eis) [P.IsMaximal] : Field (Eis ⧸ P) := Ideal.Quotient.field P

-- @@ L13-13 verbatim
noncomputable local instance phaseFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _


-- @@ L15-19 verbatim
def markedPrimeScalar (p c0 : Eis) [hP : (Ideal.span {p}).IsMaximal]
    (hp : p ≠ 0) (hg : λ₀ ∉ Ideal.span {p}) : ℂ :=
  let χ := actualSextic (Ideal.span {p}) hg
  (-tau χ (quotientTrace p hp) 2)*(χ (-1))⁻¹^2*
    (χ (Ideal.Quotient.mk _ (ramifiedTraceLambda^3*c0)))^2


-- @@ L21-26 verbatim
def residualPrimeScalar (p c0 : Eis) [hP : (Ideal.span {p}).IsMaximal]
    (hp : p ≠ 0) (hg : λ₀ ∉ Ideal.span {p}) : ℂ :=
  let χ := actualSextic (Ideal.span {p}) hg
  (tau χ ((quotientTrace p hp).mulShift (-1)) 1*tau χ (quotientTrace p hp) 3)*
    (χ (-1))⁻¹^3*(χ (Ideal.Quotient.mk _ (ramifiedTraceLambda^2*c0)))*
      (χ (Ideal.Quotient.mk _ (ramifiedTraceLambda^3*c0)))^3


-- @@ L28-28 verbatim
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a0 c0 : Eis} {mode : Bool}


-- @@ L30-44 verbatim
theorem controlled_marked_phase [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a0 c0 mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (i : ι) :
    (((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
      phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) 0 (D.epsilon i) =
        markedPrimeScalar (p i) c0 (hp i) (hg i)*
          ∏ k ∈ Finset.univ.erase i, MixedCrossSeparation.crossSymbol p hg i k ^ 2 := by
  have he : Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^3*c0)*
      Ideal.Quotient.mk _ (cofactor p i)*(D.sigma i : Eis ⧸ Ideal.span {p i})*
      (D.epsilon i : Eis ⧸ Ideal.span {p i}) = -1 := by
    simpa only [map_mul] using D.epsilon_value i
  rw [marked_local_phase _ _ _ _ _ _ he]
  change _ = _
  simp only [markedPrimeScalar, cofactor, map_prod, Finset.prod_pow,
    MixedCrossSeparation.crossSymbol]


-- @@ L46-62 verbatim
theorem controlled_residual_phase [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a0 c0 mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (i : ι) :
    (((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
      phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) 1 (D.epsilon i) =
        residualPrimeScalar (p i) c0 (hp i) (hg i)*
          ∏ k ∈ Finset.univ.erase i, MixedCrossSeparation.crossSymbol p hg i k ^ 4 := by
  have hs : (D.sigma i : Eis ⧸ Ideal.span {p i}) =
      Ideal.Quotient.mk _ (ramifiedTraceLambda^2*c0)*Ideal.Quotient.mk _ (cofactor p i) := by
    simpa only [map_mul] using D.sigma_value i
  have he : Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^3*c0)*
      Ideal.Quotient.mk _ (cofactor p i)*(D.sigma i : Eis ⧸ Ideal.span {p i})*
      (D.epsilon i : Eis ⧸ Ideal.span {p i}) = -1 := by
    simpa only [map_mul] using D.epsilon_value i
  rw [residual_local_phase _ _ _ _ _ _ _ hs he]
  simp only [residualPrimeScalar, cofactor, map_prod, Finset.prod_pow,
    MixedCrossSeparation.crossSymbol]


-- @@ L64-64 verbatim
end

-- @@ L65-65 verbatim
end SevenEighths.InverseReflectedPhase


-- @@ L67-67 verbatim
end OAI
