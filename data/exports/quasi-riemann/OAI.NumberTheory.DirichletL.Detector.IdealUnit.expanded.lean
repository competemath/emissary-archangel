import OAI.NumberTheory.DirichletL.Detector.IdealMultiplicative
import OAI.NumberTheory.DirichletL.Detector.SourcePrime


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
namespace SevenEighths.ProbePhysical

-- @@ L8-8 verbatim
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss

-- @@ L9-9 verbatim
open CubicEisenstein ProbePhase ConcretePrimeRowBridge ConcreteTraceCRT

-- @@ L10-10 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L12-15 verbatim
lemma supported_one_ideal : Supported (1 : Ideal O) := by
  refine ⟨one_ne_zero,?_⟩
  intro P hP
  simp only [UniqueFactorizationMonoid.normalizedFactors_one,Multiset.notMem_zero] at hP


-- @@ L17-29 verbatim
lemma G_one : G (1:O)=1 := by
  have hs : Supported (Ideal.span {(1:O)}) := by
    rw [Ideal.span_singleton_one,←Ideal.one_eq_top]
    exact supported_one_ideal
  have ho := supported_residue_odd (1:O) hs
  have hn : G (1:O)≠0 := by
    intro hz
    have hh := G_norm_one_of_odd (1:O) ho
    rw [hz,norm_zero] at hh
    norm_num at hh
  have he := G_mul (1:O) 1 ho ho
  rw [one_mul,reciprocitySign_one_left (1:O) ho,mul_one] at he
  exact mul_left_cancel₀ hn (by simpa only [mul_one] using he.symm)


-- @@ L31-32 verbatim
lemma angularFactor_one : FiniteGaussPhase.angularFactor (1:O)=1 := by
  simp only [FiniteGaussPhase.angularFactor,map_one,norm_one,Complex.ofReal_one,div_one]


-- @@ L34-48 verbatim
@[simp] theorem bareIdealHighCoefficient_one (η : HeckeFamily.Character) :
    bareIdealHighCoefficient η 1 1 1 1 1=1 := by
  have hs := supported_one_ideal
  have hg : Squarefree (1:Ideal O) ∧ Supported 1 ∧ Supported 1 ∧ Supported 1 ∧ Supported 1 :=
    ⟨squarefree_one,hs,hs,hs,hs⟩
  unfold bareIdealHighCoefficient
  rw [dite_eq_left hg]
  simp only [primaryGenerator_one,one_pow,one_mul]
  unfold bareSourceCoefficient correctedFiniteCoefficient reciprocityCoefficient
  rw [gaussTwo_one,G_one,angularFactor_one]
  have ho := supported_residue_odd (1:O) (by
    rw [Ideal.span_singleton_one,←Ideal.one_eq_top];exact hs)
  rw [reciprocitySign_one_left (1:O) ho,
    bareCongruenceCoefficient_inner_one 1 one_ne_zero,outerQuotient_mk]
  simp only [map_one,star_one,one_mul,Ideal.span_singleton_one,←Ideal.one_eq_top]


-- @@ L50-53 verbatim
@[simp] theorem bareIdealHighSummand_one (η : HeckeFamily.Character) (x w z : ℂ) :
    bareIdealHighSummand η 1 x w z 1 1 1 1=1 := by
  have hw (t : ℂ) : fullIdealWeight t (1:Ideal O)=1 := (IdealEuler.normWeight t).map_one
  simp only [bareIdealHighSummand,bareIdealHighCoefficient_one,hw,one_mul]


-- @@ L55-55 verbatim
end SevenEighths.ProbePhysical

-- @@ L56-56 verbatim
end


-- @@ L58-58 verbatim
end OAI
