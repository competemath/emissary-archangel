import OAI.NumberTheory.DirichletL.Descent.WholePriorityCollapse


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped BigOperators Classical SchwartzMap


-- @@ L8-8 verbatim
namespace SevenEighths.InverseMoment

-- @@ L9-9 verbatim
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic

-- @@ L10-10 verbatim
open InverseInitialArithmetic InverseFirstPriorityParents InverseMomentWholePriorityParents

-- @@ L11-11 verbatim
open InverseWholePriorityValidSource InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic

-- @@ L12-12 verbatim
open InverseMomentWholePriorityPhysical InversePrioritySecondSource InverseSecondPrincipalCaller

-- @@ L13-13 verbatim
local notation "Eis"=>ActualEisensteinCubic.O

-- @@ L14-14 verbatim
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ] {Jo:ℕ}

-- @@ L15-16 verbatim
variable (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})


-- @@ L18-26 verbatim
def priorityZeroParent (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (negative:Bool) (Ψ:Eis→*ℂ) (m:Eis) (slots assigned:Finset σ)
    (lists:σ→Finset ι) (a:σ→ι→ℂ) (V:𝓢(ℝ,ℂ)) (X Y:ℝ)
    (R:Finset ι→Finset ι→ℝ) (y:SecondParentSource ι Jo):ℂ:=
  truncatedSecondZero p hg pool Ψ (secondParentPuncture p m y)
    (secondParentLabel p y) (secondParentDivisor p y)
    (InversePrincipalEnergy.markedRadial p (slots\assigned)
      (residualLists p negative (fun i=>lists i\extra y.cube) y) a ∅ V X)
    rowMajorant Y (secondVariableCutoff p y R)


-- @@ L28-37 verbatim
def priorityTailParent (hp:∀i,p i≠0) (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (negative:Bool) (Ψ:Eis→*ℂ) (m:Eis) (slots assigned:Finset σ)
    (lists:σ→Finset ι) (a:σ→ι→ℂ) (V:𝓢(ℝ,ℂ)) (X Y:ℝ)
    (R:Finset ι→Finset ι→ℝ) (y:SecondParentSource ι Jo):ℂ:=
  secondSourceTail p hp hg hinj pool Ψ (secondParentPuncture p m y)
    (secondParentLabel p y) (secondParentDivisor p y)
    (InversePrincipalEnergy.markedRadial p (slots\assigned)
      (residualLists p negative (fun i=>lists i\extra y.cube) y) a ∅ V X)
    rowMajorant Y (secondVariableCutoff p y R)


-- @@ L39-76 verbatim
theorem whole_priority_signed_branches
    (hp:∀i,p i≠0) (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (cube:CubeCoordinates ι) (C E:Finset ι) (old:Fin Jo→SmoothMobiusCorrection.PrimeIdeal)
    (selector:Finset ι→ℂ) (negative:Bool) (Ψ:Eis→*ℂ) (m:Eis)
    (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo) (hs:Function.support om⊆Set.Icc lo hi)
    (X t Y:ℝ) (hX:0<X) (hY:0<Y) (R:Finset ι→Finset ι→ℝ):
    let V:=principalWindow om lo hi hlo hs negative t
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    let parents:=activeParents p extra pool cube C E old selector negative assigned lists
    let source:=unifiedSource p pool parents (fun _=>R)
    (∑D∈pool.powerset,(priorityOuter p hg cube negative Ψ m selector ray core D:ℂ)*
      (‖primeMark assigned lists a ((extra cube∪((if negative then cube.rightDivisor else cube.leftDivisor)∪C))∪D)‖^2:ℝ)*
      wholePriorityPoisson p hp hg hinj pool cube C E (extra cube) negative Ψ m slots assigned lists a om X t Y ray core D)=
    (∑D∈pool.powerset,(priorityOuter p hg cube negative Ψ m selector ray core D:ℂ)*
      (‖primeMark assigned lists a ((extra cube∪((if negative then cube.rightDivisor else cube.leftDivisor)∪C))∪D)‖^2:ℝ)*
      priorityZeroParent p hg extra pool negative Ψ₀ m slots assigned lists a V X Y R (parent p (fixedPoint cube C E old D)))+
    (∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z * ∑x∈source,
      sourceWeight p hg cube negative Ψ m selector ray core assigned a x *
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a V X Y z x)+
    (∑D∈pool.powerset,(priorityOuter p hg cube negative Ψ m selector ray core D:ℂ)*
      (‖primeMark assigned lists a ((extra cube∪((if negative then cube.rightDivisor else cube.leftDivisor)∪C))∪D)‖^2:ℝ)*
      priorityTailParent p hg hp hinj extra pool negative Ψ₀ m slots assigned lists a V X Y R (parent p (fixedPoint cube C E old D))) := by
  intro V Ψ₀ parents source
  rw [whole_priority_complex_slice p hp hg hcop hinj hc hpr pool cube C E extra old negative Ψ m
    slots assigned lists a selector om lo hi hlo hs X t Y hX hY ray core R (fun _ _=>())]
  rw [fullPhysical_unified p hg hp hcop hinj extra pool]
  dsimp only
  rw [←whole_assigned_source_original p hg hinj extra pool cube C E old selector negative Ψ m ray core assigned lists a
      (priorityZeroParent p hg extra pool negative Ψ₀ m slots assigned lists a V X Y R),
    ←whole_assigned_source_original p hg hinj extra pool cube C E old selector negative Ψ m ray core assigned lists a
      (priorityTailParent p hg hp hinj extra pool negative Ψ₀ m slots assigned lists a V X Y R)]
  rfl


-- @@ L78-119 verbatim
theorem whole_priority_slice_bound
    (hp:∀i,p i≠0) (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (cube:CubeCoordinates ι) (C E:Finset ι) (old:Fin Jo→SmoothMobiusCorrection.PrimeIdeal)
    (selector:Finset ι→ℂ) (negative:Bool) (Ψ:Eis→*ℂ) (m:Eis)
    (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo) (hs:Function.support om⊆Set.Icc lo hi)
    (X t Y:ℝ) (hX:0<X) (hY:0<Y) (R:Finset ι→Finset ι→ℝ):
    let V:=principalWindow om lo hi hlo hs negative t
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    let parents:=activeParents p extra pool cube C E old selector negative assigned lists
    let source:=unifiedSource p pool parents (fun _=>R)
    ‖∑D∈pool.powerset,(priorityOuter p hg cube negative Ψ m selector ray core D:ℂ)*
      (‖primeMark assigned lists a ((extra cube∪((if negative then cube.rightDivisor else cube.leftDivisor)∪C))∪D)‖^2:ℝ)*
      wholePriorityPoisson p hp hg hinj pool cube C E (extra cube) negative Ψ m slots assigned lists a om X t Y ray core D‖≤
    (∑D∈pool.powerset,priorityOuter p hg cube negative Ψ m selector ray core D*
      ‖primeMark assigned lists a ((extra cube∪((if negative then cube.rightDivisor else cube.leftDivisor)∪C))∪D)‖^2*
      ‖priorityZeroParent p hg extra pool negative Ψ₀ m slots assigned lists a V X Y R (parent p (fixedPoint cube C E old D))‖)+
    ‖∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z * ∑x∈source,
      sourceWeight p hg cube negative Ψ m selector ray core assigned a x *
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a V X Y z x‖+
    (∑D∈pool.powerset,priorityOuter p hg cube negative Ψ m selector ray core D*
      ‖primeMark assigned lists a ((extra cube∪((if negative then cube.rightDivisor else cube.leftDivisor)∪C))∪D)‖^2*
      ‖priorityTailParent p hg hp hinj extra pool negative Ψ₀ m slots assigned lists a V X Y R (parent p (fixedPoint cube C E old D))‖) := by
  intro V Ψ₀ parents source
  rw [whole_priority_signed_branches p hg hp hcop hinj hc hpr extra pool cube C E old selector negative
    Ψ m ray core slots assigned lists a om lo hi hlo hs X t Y hX hY R]
  have hn (H:Finset ι→ℂ):
      ‖∑D∈pool.powerset,(priorityOuter p hg cube negative Ψ m selector ray core D:ℂ)*
        (‖primeMark assigned lists a ((extra cube∪((if negative then cube.rightDivisor else cube.leftDivisor)∪C))∪D)‖^2:ℝ)*H D‖≤
      ∑D∈pool.powerset,priorityOuter p hg cube negative Ψ m selector ray core D*
        ‖primeMark assigned lists a ((extra cube∪((if negative then cube.rightDivisor else cube.leftDivisor)∪C))∪D)‖^2*‖H D‖:=by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro D hD
    rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,
      Real.norm_of_nonneg (by unfold priorityOuter;positivity),Real.norm_of_nonneg (sq_nonneg _)]
  exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (hn _) (le_refl _))) (hn _))


-- @@ L121-121 verbatim
end SevenEighths.InverseMoment


-- @@ L123-123 verbatim
end


-- @@ L125-125 verbatim
end OAI
