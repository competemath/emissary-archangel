import OAI.NumberTheory.DirichletL.Descent.WholeRetainedSource


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped BigOperators Classical SchwartzMap


-- @@ L8-8 verbatim
namespace SevenEighths.InverseWholePriorityValidSource

-- @@ L9-9 verbatim
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic

-- @@ L10-10 verbatim
open InverseMoment InverseInitialArithmetic InverseFirstPriorityParents InversePrioritySecondSource

-- @@ L11-11 verbatim
open InverseMomentWholePriorityParents InverseMomentWholePriorityPhysical

-- @@ L12-12 verbatim
open RayFourExpansion InversePrincipalEnergy InverseSecondPrincipalCaller

-- @@ L13-13 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L14-14 verbatim
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ]

-- @@ L15-15 verbatim
variable {Jo : ℕ}


-- @@ L17-20 verbatim
def activeFixedSource (pool : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (selector : Finset ι→ℂ) :
    Finset (Source ι Jo) :=
  (fixedSource pool b C E old).filter (fun x=>selector x.quotientSupport≠0)


-- @@ L22-28 verbatim
omit [DecidableEq ι] in
theorem activeFixedSource_eq_image (pool : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (selector : Finset ι→ℂ) :
    activeFixedSource pool b C E old selector=
      (pool.powerset.filter (fun D=>selector D≠0)).image (fixedPoint b C E old) := by
  rw [activeFixedSource,fixedSource,Finset.filter_image]
  rfl


-- @@ L30-37 verbatim
omit [DecidableEq ι] in
theorem mem_activeFixedSource (pool : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (selector : Finset ι→ℂ) (x : Source ι Jo) :
    x∈activeFixedSource pool b C E old selector ↔
      ∃ D∈pool.powerset,selector D≠0 ∧ fixedPoint b C E old D=x := by
  rw [activeFixedSource_eq_image]
  simp only [Finset.mem_image,Finset.mem_filter]
  aesop


-- @@ L39-45 verbatim
omit [DecidableEq ι] in
theorem sum_activeFixedSource {A : Type*} [AddCommMonoid A]
    (pool : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (selector : Finset ι→ℂ) (H : Source ι Jo→A) :
    ∑ x∈activeFixedSource pool b C E old selector,H x=
      ∑ D∈pool.powerset.filter (fun D=>selector D≠0),H (fixedPoint b C E old D) := by
  rw [activeFixedSource_eq_image,Finset.sum_image (fun _ _ _ _ h=>fixedPoint_injective b C E old h)]


-- @@ L47-47 verbatim
variable (p : ι→O) [∀ i,(Ideal.span {p i}).IsMaximal]


-- @@ L49-59 verbatim
omit [∀ i,(Ideal.span {p i}).IsMaximal] in

theorem activeFixedSource_valid (pool : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (selector : Finset ι→ℂ)
    (hb : b.Admissible) (hC : Disjoint C b.support) (hE : E⊆C∪b.support)
    (hold : ∀ D∈pool.powerset,selector D≠0 → ∀ i,(old i).val∣
      sourceIdeal p b.support*sourceIdeal p C*sourceIdeal p D) :
    ∀ x∈activeFixedSource pool b C E old selector,SourceValid p x := by
  intro x hx
  obtain ⟨D,hD,hs,rfl⟩ := (mem_activeFixedSource pool b C E old selector x).mp hx
  exact ⟨hb,hC,hE,hold D hD hs⟩


-- @@ L61-68 verbatim
omit [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem activeFixedSource_extra (pool : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (selector : Finset ι→ℂ)
    (extra : CubeCoordinates ι→Finset ι) (he : extra b⊆b.support) :
    ∀ x∈activeFixedSource pool b C E old selector,extra x.cube⊆x.cube.support := by
  intro x hx
  obtain ⟨D,hD,hs,rfl⟩ := (mem_activeFixedSource pool b C E old selector x).mp hx
  exact he


-- @@ L70-86 verbatim
theorem active_retained_conditions (hp : ∀ i,p i≠0)
    (pool : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (selector : Finset ι→ℂ)
    (hb : b.Admissible) (hC : Disjoint C b.support) (hE : E⊆C∪b.support)
    (hold : ∀ D∈pool.powerset,selector D≠0 → ∀ i,(old i).val∣
      sourceIdeal p b.support*sourceIdeal p C*sourceIdeal p D)
    (extra : CubeCoordinates ι→Finset ι) (he : extra b⊆b.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) :
    ActualSecondSourceConditions p
      (retainedPool p pool (wholeAssignedParents p (fun x=>extra x.cube)
        (activeFixedSource pool b C E old selector) negative J lists) R label residual j) :=
  InverseMomentWholeRetainedSource.retained_conditions p hp extra _
    (activeFixedSource_valid p pool b C E old selector hb hC hE hold)
    (activeFixedSource_extra pool b C E old selector extra he) negative J lists pool R label residual j


-- @@ L88-106 verbatim
theorem active_retained_deleted_support
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (selector : Finset ι→ℂ)
    (hb : b.Admissible) (hC : Disjoint C b.support) (hE : E⊆C∪b.support)
    (hold : ∀ D∈pool.powerset,selector D≠0 → ∀ i,(old i).val∣
      sourceIdeal p b.support*sourceIdeal p C*sourceIdeal p D)
    (extra : CubeCoordinates ι→Finset ι) (he : extra b⊆b.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) (x : MarkedSecondSource ι (Jo+(J.card+J.card)) 0)
    (hx : x∈retainedPool p pool (wholeAssignedParents p (fun x=>extra x.cube)
      (activeFixedSource pool b C E old selector) negative J lists) R label residual j) :
    ∀ i∈InverseMomentWholeRetainedSource.deleted p extra negative x,
      i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal O)∣x.quotient :=
  InverseMomentWholeRetainedSource.retained_deleted_support p hinj extra _
    (activeFixedSource_valid p pool b C E old selector hb hC hE hold)
    (activeFixedSource_extra pool b C E old selector extra he) negative J lists pool R label residual j x hx


-- @@ L108-108 verbatim
variable (hp : ∀ i,p i≠0) (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})


-- @@ L110-113 verbatim
theorem priorityOuter_zero (b : CubeCoordinates ι) (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (selector : Finset ι→ℂ) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (D : Finset ι) (hD : selector D=0) : priorityOuter p hg b negative Ψ m selector r core D=0 := by
  simp only [priorityOuter,hD,norm_zero,mul_zero,zero_mul]


-- @@ L115-124 verbatim
def wholePriorityPoisson (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (b : CubeCoordinates ι) (C E extra : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m : O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (om : ℝ→ℂ) (X t Y : ℝ) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex) (D : Finset ι) : ℂ :=
  firstFreshSecondPoisson p hp hg hinj pool D b.support
    (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative
    (if negative then r.1 else r.2) Ψ m
    (fun U=>primeMark (slots\J)
      (fun i=>lists i\((extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C))∪D)) a U)
    om X (∏ i∈C,p i) (primeSubsetGenerator (fun i=>Ideal.span {p i}) E) core t Y


-- @@ L126-146 verbatim
theorem parentPoisson_fixed_whole (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (b : CubeCoordinates ι) (C E extra D : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (negative : Bool)
    (Ψ : O→*ℂ) (m : O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (om : ℝ→ℂ) (X t Y : ℝ) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex) :
    parentPoisson p hp hg hinj pool negative Ψ m slots J (fun i=>lists i\extra) a om X t Y r core
      (parent p (fixedPoint b C E old D)) =
    wholePriorityPoisson p hp hg hinj pool b C E extra negative Ψ m slots J lists a om X t Y r core D := by
  have hl : residualLists p negative (fun i=>lists i\extra)
      (parent p (fixedPoint b C E old D)) =
      (fun i=>lists i\((extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C))∪D)) := by
    funext i
    unfold residualLists
    rw [quotientSupport_parent p hinj]
    change (lists i\extra)\(((if negative then b.rightDivisor else b.leftDivisor)∪C)∪D)=_
    ext k
    simp only [Finset.mem_sdiff,Finset.mem_union]
    tauto
  unfold parentPoisson wholePriorityPoisson
  rw [quotientSupport_parent p hinj,hl]
  rfl


-- @@ L148-148 verbatim
variable (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))


-- @@ L150-192 verbatim
theorem whole_priority_complex_slice [Fintype κ]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (extra : CubeCoordinates ι→Finset ι) (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal)
    (negative : Bool) (Ψ : O→*ℂ) (m : O) (slots J : Finset σ)
    (lists : σ→Finset ι) (a : σ→ι→ℂ) (selector : Finset ι→ℂ)
    (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo) (hs : Function.support om⊆Set.Icc lo hi)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (R : Finset ι→Finset ι→ℝ) (label : Finset ι→SecondExpansionData ι→κ) :
    (∑ D∈pool.powerset,(priorityOuter p hg b negative Ψ m selector r core D:ℂ)*
      (‖primeMark J lists a ((extra b∪((if negative then b.rightDivisor else b.leftDivisor)∪C))∪D)‖^2:ℝ)*
      wholePriorityPoisson p hp hg hinj pool b C E (extra b) negative Ψ m slots J lists a om X t Y r core D) =
    ∑ y∈wholeAssignedParents p (fun x=>extra x.cube) (activeFixedSource pool b C E old selector) negative J lists,
      coefficient p J a (fun x=>(priorityOuter p hg b negative Ψ m selector r core x.quotientSupport:ℂ)) y *
        fullPhysical p hp hcop hg hinj extra pool negative Ψ m slots J lists a
          (principalWindow om lo hi hlo hs negative t) X Y r core R label y := by
  let H (D : Finset ι) : ℂ := (priorityOuter p hg b negative Ψ m selector r core D:ℂ)*
    (‖primeMark J lists a ((extra b∪((if negative then b.rightDivisor else b.leftDivisor)∪C))∪D)‖^2:ℝ)*
    wholePriorityPoisson p hp hg hinj pool b C E (extra b) negative Ψ m slots J lists a om X t Y r core D
  have hfilter : ∑ D∈pool.powerset,H D=∑ D∈pool.powerset.filter (fun D=>selector D≠0),H D := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro D hD
    by_cases hn : selector D≠0
    · rw [ite_eq_left hn]
    · have hz : selector D=0 := not_ne_iff.mp hn
      simp only [ite_eq_right hn,H,priorityOuter_zero p hg b negative Ψ m selector r core D hz,
        Complex.ofReal_zero,zero_mul]
  calc
    _ = ∑ D∈pool.powerset.filter (fun D=>selector D≠0),H D := hfilter
    _ = ∑ x∈activeFixedSource pool b C E old selector,
        (priorityOuter p hg b negative Ψ m selector r core x.quotientSupport:ℂ)*
        (‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
        parentPoisson p hp hg hinj pool negative Ψ m slots J (fun i=>lists i\extra x.cube) a om X t Y r core (parent p x) := by
      rw [sum_activeFixedSource]
      apply Finset.sum_congr rfl
      intro D hD
      rw [parentPoisson_fixed_whole p hp hg hinj]
      simp only [H,fixedPoint,wholeExtractedSupport,extractedSupport,Finset.union_assoc]
    _ = _ := whole_signed_source_full p hp hcop hg hinj hc hpr extra pool _ _ negative Ψ m slots J lists a
      om lo hi hlo hs X t Y hX hY r core R label


-- @@ L194-215 verbatim
theorem whole_priority_real_slice [Fintype κ]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (extra : CubeCoordinates ι→Finset ι) (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal)
    (negative : Bool) (Ψ : O→*ℂ) (m : O) (slots J : Finset σ)
    (lists : σ→Finset ι) (a : σ→ι→ℂ) (selector : Finset ι→ℂ)
    (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo) (hs : Function.support om⊆Set.Icc lo hi)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (R : Finset ι→Finset ι→ℝ) (label : Finset ι→SecondExpansionData ι→κ) :
    (∑ D∈pool.powerset,priorityOuter p hg b negative Ψ m selector r core D*
      ‖primeMark J lists a ((extra b∪((if negative then b.rightDivisor else b.leftDivisor)∪C))∪D)‖^2*
      (wholePriorityPoisson p hp hg hinj pool b C E (extra b) negative Ψ m slots J lists a om X t Y r core D).re) =
    (∑ y∈wholeAssignedParents p (fun x=>extra x.cube) (activeFixedSource pool b C E old selector) negative J lists,
      coefficient p J a (fun x=>(priorityOuter p hg b negative Ψ m selector r core x.quotientSupport:ℂ)) y *
        fullPhysical p hp hcop hg hinj extra pool negative Ψ m slots J lists a
          (principalWindow om lo hi hlo hs negative t) X Y r core R label y).re := by
  have h := congrArg Complex.re (whole_priority_complex_slice p hp hg hcop hinj hc hpr pool b C E
    extra old negative Ψ m slots J lists a selector om lo hi hlo hs X t Y hX hY r core R label)
  simpa only [Complex.re_sum,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero] using h


-- @@ L217-253 verbatim
theorem whole_priority_energy_reassembly [Fintype κ]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (extra : CubeCoordinates ι→Finset ι) (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal)
    (negative : Bool) (Ψ : O→*ℂ) (m : O) (slots : Finset σ)
    (lists : σ→Finset ι) (a : σ→ι→ℂ) (selector : Finset ι→ℂ)
    (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo) (hs : Function.support om⊆Set.Icc lo hi)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y)
    (R : Finset ι→Finset ι→ℝ) (label : Finset ι→SecondExpansionData ι→κ) :
    firstWholePrioritySecondEnergy p hp hg hinj pool b C (extra b) negative Ψ m
      (primeSubsetGenerator (fun i=>Ideal.span {p i}) E) slots lists a selector om X t Y =
    (32*512)*(2:ℝ)^slots.card * ∑ r : RayCharacter×RayCharacter,
      ∑ core : FirstCoreIndex,∑ J∈slots.powerset,
        (∑ y∈wholeAssignedParents p (fun x=>extra x.cube) (activeFixedSource pool b C E old selector) negative J lists,
          coefficient p J a (fun x=>(priorityOuter p hg b negative Ψ m selector r core x.quotientSupport:ℂ)) y *
            fullPhysical p hp hcop hg hinj extra pool negative Ψ m slots J lists a
              (principalWindow om lo hi hlo hs negative t) X Y r core R label y).re := by
  simp_rw [←whole_priority_real_slice p hp hg hcop hinj hc hpr pool b C E extra old negative Ψ m slots
    _ lists a selector om lo hi hlo hs X t Y hX hY _ _ R label]
  unfold firstWholePrioritySecondEnergy
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro core hcore
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J hJ
  apply Finset.sum_congr rfl
  intro D hD
  unfold priorityOuter wholePriorityPoisson
  ring


-- @@ L255-255 verbatim
end SevenEighths.InverseWholePriorityValidSource


-- @@ L257-257 verbatim
end


-- @@ L259-259 verbatim
end OAI
