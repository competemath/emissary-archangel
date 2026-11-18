import OAI.NumberTheory.DirichletL.Descent.SecondPhysicalRecursive


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace SevenEighths.InverseMoment

-- @@ L6-6 verbatim
open scoped BigOperators Classical SchwartzMap

-- @@ L7-7 verbatim
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers

-- @@ L8-8 verbatim
open InverseInitialArithmetic (sourceIdeal)

-- @@ L9-9 verbatim
noncomputable section

-- @@ L10-10 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L11-11 verbatim
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]


-- @@ L13-18 verbatim
@[ext] structure SecondParentSource (ι : Type*) (Jo : ℕ) where
  cube : CubeCoordinates ι
  firstCommon : Finset ι
  firstDivisor : Finset ι
  quotient : Ideal Eis
  oldAssigned : Fin Jo → SmoothMobiusCorrection.PrimeIdeal


-- @@ L20-28 verbatim
def attachSecondExpansion {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (x : SecondExpansionData ι) : MarkedSecondSource ι Jo 0 where
  cube := parent.cube
  firstCommon := parent.firstCommon
  firstDivisor := parent.firstDivisor
  second := x
  quotient := parent.quotient
  oldAssigned := parent.oldAssigned
  newAssigned := Fin.elim0


-- @@ L30-35 verbatim
def secondParentOf {Jo : ℕ} (x : MarkedSecondSource ι Jo 0) : SecondParentSource ι Jo where
  cube := x.cube
  firstCommon := x.firstCommon
  firstDivisor := x.firstDivisor
  quotient := x.quotient
  oldAssigned := x.oldAssigned


-- @@ L37-41 verbatim
omit [DecidableEq ι] in
theorem attachSecondExpansion_injective {Jo : ℕ} (parent : SecondParentSource ι Jo) :
    Function.Injective (attachSecondExpansion parent) := by
  intro x y h
  exact congrArg MarkedSecondSource.second h


-- @@ L43-48 verbatim
omit [DecidableEq ι] in
theorem attachSecondExpansion_recover {Jo : ℕ} (x : MarkedSecondSource ι Jo 0) :
    attachSecondExpansion (secondParentOf x) x.second = x := by
  apply MarkedSecondSource.ext <;> try rfl
  funext i
  exact Fin.elim0 i


-- @@ L50-55 verbatim
def secondSourceParentEquiv {Jo : ℕ} :
    SecondParentSource ι Jo × SecondExpansionData ι ≃ MarkedSecondSource ι Jo 0 where
  toFun x := attachSecondExpansion x.1 x.2
  invFun x := (secondParentOf x,x.second)
  left_inv x := by cases x; rfl
  right_inv := attachSecondExpansion_recover


-- @@ L57-59 verbatim
variable (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})


-- @@ L61-64 verbatim
def secondParentLabel {Jo : ℕ} (parent : SecondParentSource ι Jo) : Eis :=
  (∏ i∈parent.firstCommon,p i)*jLabel p parent.cube.support
    (fun i => parent.cube.leftExponent i+parent.cube.rightExponent i)
    parent.cube.leftBit parent.cube.rightBit


-- @@ L66-67 verbatim
def secondParentDivisor {Jo : ℕ} (parent : SecondParentSource ι Jo) : Eis :=
  primeSubsetGenerator (fun i => Ideal.span {p i}) parent.firstDivisor


-- @@ L69-72 verbatim
def secondParentPuncture {Jo : ℕ} (m : Eis) (parent : SecondParentSource ι Jo) : Eis :=
  (m*ConcretePrimeRowBridge.idealGenerator parent.quotient)*
    b0Label p parent.cube.support (fun i => parent.cube.leftExponent i+parent.cube.rightExponent i)
      parent.cube.leftBit parent.cube.rightBit*secondParentDivisor p parent


-- @@ L74-104 verbatim
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem attached_source_conditions {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (source : Finset (SecondExpansionData ι))
    (ha : parent.cube.Admissible) (hC : Disjoint parent.firstCommon parent.cube.support)
    (hD : parent.firstDivisor ⊆ parent.firstCommon∪parent.cube.support)
    (hE : ∀ x∈source,x.divisor ⊆ x.sourceCommon)
    (hold : ∀ i,(parent.oldAssigned i).val ∣
      sourceIdeal p parent.cube.support*sourceIdeal p parent.firstCommon*parent.quotient)
    (hq : parent.quotient ≠ 0) :
    ActualSecondSourceConditions p (source.image (attachSecondExpansion parent)) := by
  constructor
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact ha
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact hC
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact hD
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact hE y hy
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact hold
  · intro x hx i
    exact Fin.elim0 i
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact hq


-- @@ L106-111 verbatim
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem attached_inherited_profile {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (x : SecondExpansionData ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex) :
    secondInheritedProfile p (attachSecondExpansion parent x) Ψ m z =
      expansionProfileData p Ψ (secondParentPuncture p m parent)
        (secondParentLabel p parent) (secondParentDivisor p parent) z ∅ ∅ x := rfl


-- @@ L113-119 verbatim
theorem attached_signed_weight {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (x : SecondExpansionData ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex) :
    actualSecondSignedWeight p hp hcop hg Ψ
      (m*ConcretePrimeRowBridge.idealGenerator (attachSecondExpansion parent x).quotient) z
      (attachSecondExpansion parent x) =
    secondSignedSourceWeight p hp hcop hg Ψ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) z x := rfl


-- @@ L121-147 verbatim
theorem secondExpansionSource_attached
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (source : Finset (SecondExpansionData ι)) (hE : ∀ x∈source,x.divisor ⊆ x.sourceCommon)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (X Y : ℝ) :
    secondExpansionSource p hp hcop hg pool Ψ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) z source
      (fun U => primeMark slots₁ lists₁ a₁ U*W₁ (primeProductNorm p U/X))
      (fun U => primeMark slots₂ lists₂ a₂ U*W₂ (primeProductNorm p U/X)) Φ Y =
    (Y : ℂ)*secondRayCoefficient z *
      ∑ x∈source.image (attachSecondExpansion parent),
        actualSecondSignedWeight p hp hcop hg Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y X := by
  have he := secondExpansionSource_signed_profile p hp hcop hg hinj hpr pool Ψ
    (secondParentPuncture p m parent) (secondParentLabel p parent) (secondParentDivisor p parent)
    z source hE ∅ ∅ slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ X Y
  simp only [Finset.empty_union] at he
  rw [he]
  congr 1
  rw [Finset.sum_image (fun x hx y hy h => attachSecondExpansion_injective parent h)]
  apply Finset.sum_congr rfl
  intro x hx
  rw [attached_inherited_profile,attached_signed_weight]


-- @@ L149-149 verbatim
end

-- @@ L150-150 verbatim
end SevenEighths.InverseMoment


-- @@ L152-152 verbatim
end OAI
