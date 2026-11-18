import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerAssignedPair


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
open scoped BigOperators Classical

-- @@ L8-8 verbatim
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum

-- @@ L9-9 verbatim
namespace SevenEighths.InverseInitialEnergyCallerAssignedCanonical

-- @@ L10-10 verbatim
open InverseMoment InverseInitialArithmetic InverseInitialQuotientGeometry

-- @@ L11-11 verbatim
open InverseInitialEnergyCallerAssigned InverseInitialEnergyCallerOpposite

-- @@ L12-12 verbatim
open InverseInitialEnergyCallerCanonical InverseInitialClippedColumns

-- @@ L13-13 verbatim
local notation "Eis"=>ActualEisensteinCubic.O

-- @@ L14-17 verbatim
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis)(hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})


-- @@ L19-70 verbatim
theorem original_assigned_canonical_pair
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (S:Finset (Source (ι:=ι) 0))(u:Eisˣ)
    (J₁ J₂:Finset σ)(L₁ L₂:σ→Finset ι)(a₁ a₂:σ→ι→ℂ)
    (ha₁:∀i∈J₁,∀q∈L₁ i,‖a₁ i q‖≤1)
    (ha₂:∀i∈J₂,∀q∈L₂ i,‖a₂ i q‖≤1)
    (hdiv:∀x∈S,x.divisor⊆x.common)
    (labels:Finset (Ideal Eis))(rows:Finset Eis)
    (hlabels:∀f∈labels,f≠0)(hneg:∀k∈rows,-k∈rows)
    (hchild:∀x∈S,(initialChild (toTuple p (sectorSource u x))).2.1∈labels ∧
      (initialChild (toTuple p (sectorSource u x))).2.2∈rows)
    (c:Source (ι:=ι) 0→ℂ)(A:ℝ)(hA:0≤A)(hc:∀x∈S,‖c x‖≤A)
    (pool:Finset ι)(Ψ₁ Ψ₂:Eis→*ℂ)(j:Eis)(slots₁ slots₂:Finset σ)
    (W₁ W₂:ℝ→ℂ)(X₁ X₂:ℝ){Z:ℝ}(hZ:0<Z)(F B₁ B₂:ℝ)
    (hmoment₁:∀t∈quotientSet p (assignedSource S J₁ J₂ L₁ L₂),
      normalizedColumnEnergy p hp hcop hg pool Ψ₁ (j*primaryGenerator t)
        slots₁ L₁ a₁ labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
        W₁ X₁ Z F≤B₁)
    (hmoment₂:∀t∈quotientSet p (assignedSource S J₁ J₂ L₁ L₂),
      normalizedColumnEnergy p hp hcop hg pool Ψ₂ (j*primaryGenerator t)
        slots₂ L₂ a₂ labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
        W₂ X₂ Z F≤B₂) :
    ‖∑x∈S,c x*(star (primeMark J₁ L₁ a₁ (x.common∪x.overlap))*
      primeMark J₂ L₂ a₂ (x.common∪x.overlap))*
      (star (child p hp hcop hg pool Ψ₁ j slots₁ L₁ a₁ W₁ X₁
          (initialChild (toTuple p (sectorSource u x))))*
        child p hp hcop hg pool Ψ₂ j slots₂ L₂ a₂ W₂ X₂
          (negativeChild (initialChild (toTuple p (sectorSource u x)))))‖≤
      A*(Z^F*∑t∈quotientSet p (assignedSource S J₁ J₂ L₁ L₂),
        ((idealDivisors t).card:ℝ)^(J₁.card+J₂.card))*(Real.sqrt B₁*Real.sqrt B₂) := by
  let T := quotientSet p (assignedSource S J₁ J₂ L₁ L₂)
  let f := child p hp hcop hg pool Ψ₁ j slots₁ L₁ a₁ W₁ X₁
  let g := child p hp hcop hg pool Ψ₂ j slots₂ L₂ a₂ W₂ X₂
  have h₁ := energy_le_moment p hp hcop hg pool Ψ₁ j slots₁ L₁ a₁ W₁ X₁
    (J₁.card+J₂.card) T labels rows hZ F B₁ hmoment₁
  have h₂ := energy_le_moment p hp hcop hg pool Ψ₂ j slots₂ L₂ a₂ W₂ X₂
    (J₁.card+J₂.card) T labels rows hZ F B₂ hmoment₂
  rw [←energy_neg_rows T labels rows hneg (J₁.card+J₂.card) g] at h₂
  have hh := InverseInitialEnergyCallerAssignedPair.original_assigned_pair p hp hinj hpr
    S u J₁ J₂ L₁ L₂ a₁ a₂ ha₁ ha₂ hdiv labels rows hlabels hchild c A hA hc f
    (fun k=>g (negativeChild k))
  apply hh.trans
  calc
    _≤A*(Real.sqrt ((Z^F*∑t∈T,((idealDivisors t).card:ℝ)^(J₁.card+J₂.card))*B₁)*
      Real.sqrt ((Z^F*∑t∈T,((idealDivisors t).card:ℝ)^(J₁.card+J₂.card))*B₂)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul (Real.sqrt_le_sqrt h₁)
        (Real.sqrt_le_sqrt h₂) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hA
    _=_ := by
      rw [sqrt_pair_mass _ B₁ B₂ (mul_nonneg (Real.rpow_nonneg hZ.le _)
        (Finset.sum_nonneg fun t ht=>by positivity))]
      ring


-- @@ L72-72 verbatim
end SevenEighths.InverseInitialEnergyCallerAssignedCanonical


-- @@ L74-74 verbatim
end


-- @@ L76-76 verbatim
end OAI
