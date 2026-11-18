import OAI.NumberTheory.DirichletL.Moments.FirstReferenceEnergy


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical BigOperators SchwartzMap


-- @@ L8-8 verbatim
namespace SevenEighths.CenteredMomentEnergyFirstColumnPairing

-- @@ L9-9 verbatim
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss RayFourExpansion

-- @@ L10-10 verbatim
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic

-- @@ L11-11 verbatim
open CenteredMomentFirstReferenceSource CenteredMomentFirstReferenceEnergy

-- @@ L12-12 verbatim
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily CenteredMomentCanonicalFirst

-- @@ L13-13 verbatim
open CenteredMomentAmplificationChildInput CenteredMomentGaussEnergy

-- @@ L14-14 verbatim
open CenteredMomentFirstMixedAllowance CenteredMomentSectorLocalization CenteredMomentLogDyadic

-- @@ L15-15 verbatim
open CenteredMomentSecondRetainedAggregate CenteredMomentChildAssembly

-- @@ L16-16 verbatim
open CenteredMomentFirstNonexceptionalWeightSum

-- @@ L17-17 verbatim
local notation "O"=>HeckeFamily.O

-- @@ L18-18 verbatim
variable {ι:Type*}[Fintype ι][DecidableEq ι]

-- @@ L19-19 verbatim
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _


-- @@ L21-29 verbatim
lemma fixed_pair_moduli (η:Character)(C D:Ideal O)(hC:Supported C)
    (E:Finset (CommonIndex C D))(χ:RayCharacter):
    (fixedPair η C D hC E χ χ).left.modulus=(fixedPair η C D hC E 1 1).left.modulus ∧
    (fixedPair η C D hC E χ χ).right.modulus=(fixedPair η C D hC E 1 1).right.modulus:=by
  constructor
  · rw [(fixedPair η C D hC E χ χ).left_modulus,
      (fixedPair η C D hC E 1 1).left_modulus]
  · rw [(fixedPair η C D hC E χ χ).right_modulus,
      (fixedPair η C D hC E 1 1).right_modulus]


-- @@ L31-36 verbatim
lemma reference_sum (ref seed front Z:ℝ)(loss:Fin 4→ℝ)(v:ℝ)(J:ℕ):
    (ref/seed)*(front*∑j:Fin 4,Z^(loss j))*(1+|v|)^(2*J)=
      ((∑j:Fin 4,ref*(front*Z^(loss j)))/seed)*(1+‖v‖)^(2*J):=by
  rw [Real.norm_eq_abs]
  simp only [←Finset.mul_sum]
  ring


-- @@ L38-69 verbatim
omit [DecidableEq ι] in
theorem column_bounds_of_reference_sums
    (s:Input ι)(R seed:Ideal O)(Z:ℝ)(Jleft Jright:ℕ)
    (frontLeft frontRight:ℝ)(lossLeft lossRight:Fin 4→ℝ)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))(n:Fin 4→ℤ)
    (hleft:∀L:Ideal O,(L.absNorm:ℝ)≤sourceRadius s/(p.val.2.absNorm:ℝ)→
      Squarefree L→∀χ:RayCharacter,∀v:ℝ,
      (commonEnergy (original s R seed) p.val.1 (supported s R seed p).1
        (fixedPair s.η p.val.1 p.val.2 (supported s R seed p).1 E χ χ).left v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re≤
        (((fixedPair s.η p.val.1 p.val.2 (supported s R seed p).1 E χ χ).left.modulus.absNorm:ℝ)*
            (CenteredMomentExceptionalAmplitudePair.volume s.toData/(p.val.1.absNorm:ℝ))^2*Z^(allowance p.val.1 p.val.2 Z)/(L.absNorm:ℝ))*
          (frontLeft*∑j:Fin 4,Z^(lossLeft j))*(1+|v|)^(2*Jleft))
    (hright:∀L:Ideal O,(L.absNorm:ℝ)≤sourceRadius s/(p.val.2.absNorm:ℝ)→
      Squarefree L→∀χ:RayCharacter,∀v:ℝ,
      (commonEnergy (original s R seed) p.val.2 (supported s R seed p).2
        (fixedPair s.η p.val.1 p.val.2 (supported s R seed p).1 E χ χ).right v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re≤
        (((fixedPair s.η p.val.1 p.val.2 (supported s R seed p).1 E χ χ).right.modulus.absNorm:ℝ)*
            (CenteredMomentExceptionalAmplitudePair.volume s.toData/(p.val.2.absNorm:ℝ))^2*Z^(allowance p.val.2 p.val.1 Z)/(L.absNorm:ℝ))*
          (frontRight*∑j:Fin 4,Z^(lossRight j))*(1+|v|)^(2*Jright)):
    ColumnBounds s R seed Z Jleft Jright
      (fun j=>frontLeft*Z^(lossLeft j)) (fun j=>frontRight*Z^(lossRight j)) p E n:=by
  constructor
  · intro L _ hcap hL χ v
    have hh:=hleft L hcap hL χ v
    rw [(fixed_pair_moduli s.η p.val.1 p.val.2 (supported s R seed p).1 E χ).1] at hh
    exact hh.trans_eq (reference_sum _ _ _ _ _ _ _)
  · intro L _ hcap hL χ v
    have hh:=hright L hcap hL χ v
    rw [(fixed_pair_moduli s.η p.val.1 p.val.2 (supported s R seed p).1 E χ).2] at hh
    exact hh.trans_eq (reference_sum _ _ _ _ _ _ _)


-- @@ L71-71 verbatim
end SevenEighths.CenteredMomentEnergyFirstColumnPairing


-- @@ L73-73 verbatim
end


-- @@ L75-75 verbatim
end OAI
