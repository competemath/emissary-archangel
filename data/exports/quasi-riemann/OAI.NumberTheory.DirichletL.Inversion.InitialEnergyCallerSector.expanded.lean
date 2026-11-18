import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerSource
import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerAssignedCanonical
import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerWeights


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
noncomputable section


-- @@ L9-9 verbatim
open scoped BigOperators Classical

-- @@ L10-10 verbatim
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic

-- @@ L11-11 verbatim
namespace SevenEighths.InverseInitialEnergyCallerSector

-- @@ L12-12 verbatim
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialKernelBridge

-- @@ L13-13 verbatim
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource

-- @@ L14-14 verbatim
open InverseInitialEnergyCallerCanonical InverseInitialEnergyCallerOpposite InverseInitialProfile

-- @@ L15-15 verbatim
local notation "Eis"=>ActualEisensteinCubic.O

-- @@ L16-19 verbatim
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis)(hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})


-- @@ L21-37 verbatim
theorem markedModeColumn_sector
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (x:Source (ι:=ι) 0)(hdiv:x.divisor⊆x.common)(u:Eisˣ)
    (hu:unitSector p hp hpr (sourcePoint x ∅ ∅)=u)
    (pool:Finset ι)(Ψ:Eis→*ℂ)(j:Eis)(slots:Finset σ)
    (lists:σ→Finset ι)(a:σ→ι→ℂ)(W:ℝ→ℂ)(Z D B v:ℝ) :
    markedModeColumn p hp hcop hg hpr pool Ψ j x.frequency x slots lists a W Z D B v=
      ∑J∈slots.powerset,primeMark J lists a (x.common∪x.overlap)*
        child p hp hcop hg pool Ψ j (slots\J) lists a W (Z^(columnCenter D B v))
          (initialChild (toTuple p (sectorSource u x))) := by
  unfold markedModeColumn
  rw [hu]
  apply Finset.sum_congr rfl
  intro J hJ
  simp only [child,initialChild,toTuple,sectorSource,sourceTuple]
  rw [source_quotient p hp x.common x.divisor hdiv]
  rfl


-- @@ L39-55 verbatim
theorem markedModeColumn_negative_sector
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (x:Source (ι:=ι) 0)(hdiv:x.divisor⊆x.common)(u:Eisˣ)
    (hu:unitSector p hp hpr (sourcePoint x ∅ ∅)=u)
    (pool:Finset ι)(Ψ:Eis→*ℂ)(j:Eis)(slots:Finset σ)
    (lists:σ→Finset ι)(a:σ→ι→ℂ)(W:ℝ→ℂ)(Z D B v:ℝ) :
    markedModeColumn p hp hcop hg hpr pool Ψ j (-x.frequency) x slots lists a W Z D B v=
      ∑J∈slots.powerset,primeMark J lists a (x.common∪x.overlap)*
        child p hp hcop hg pool Ψ j (slots\J) lists a W (Z^(columnCenter D B v))
          (negativeChild (initialChild (toTuple p (sectorSource u x)))) := by
  unfold markedModeColumn
  rw [hu]
  apply Finset.sum_congr rfl
  intro J hJ
  simp only [child,negativeChild,initialChild,toTuple,sectorSource,sourceTuple]
  rw [source_quotient p hp x.common x.divisor hdiv]
  simp only [quotient,sourcePoint,mul_neg]


-- @@ L57-57 verbatim
end SevenEighths.InverseInitialEnergyCallerSector


-- @@ L59-59 verbatim
end


-- @@ L61-61 verbatim
end OAI
