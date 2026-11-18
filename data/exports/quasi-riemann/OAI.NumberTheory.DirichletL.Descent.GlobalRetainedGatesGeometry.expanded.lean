import OAI.NumberTheory.DirichletL.Descent.GlobalRetainedGates


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical BigOperators SchwartzMap

-- @@ L7-7 verbatim
namespace SevenEighths.InverseMomentGlobalRetainedGates

-- @@ L8-8 verbatim
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents

-- @@ L9-9 verbatim
open InverseWholePriorityRetainedSource InversePrioritySecondSource InverseInitialArithmetic

-- @@ L10-10 verbatim
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks

-- @@ L11-11 verbatim
open ConcreteTraceCRT (eisEmbedding)

-- @@ L12-12 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L13-13 verbatim
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

-- @@ L14-14 verbatim
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]


-- @@ L16-37 verbatim
lemma actual_profile_zero_of_geometry
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (F : Finset ι) (x : SecondProfileData ι) (slots₁ slots₂ : Finset σ)
    (lists₁ lists₂ : σ→Finset ι) (a₁ a₂ : σ→ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y X b : ℝ) (hX : 0<X)
    (hW : ∀y,W₁ y≠0 → y≤b)
    (hgeom : b*X<primeProductNorm p x.common*primeProductNorm p x.overlap) :
    actualSecondProfileRow p hp hcop hg F x slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y X=0 := by
  rw [actualSecondProfileRow_eq_whole]
  apply Finset.sum_eq_zero
  intro N hN
  apply Finset.sum_eq_zero
  intro M hM
  have hzero : W₁ (primeProductNorm p x.common*primeProductNorm p x.overlap*primeProductNorm p N/X)=0 := by
    by_contra hn
    have hh := (div_le_iff₀ hX).mp (hW _ hn)
    have hlo := le_mul_of_one_le_right
      (mul_nonneg (primeProductNorm_pos p hp x.common).le (primeProductNorm_pos p hp x.overlap).le)
      (primeProductNorm_ge_one p hp N)
    linarith
  simp [secondNormProfile,secondActualNorms,hzero]


-- @@ L39-52 verbatim
lemma wholeRow_zero_of_geometry
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    {Jo : ℕ} (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m : O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (W : ℝ→ℂ) (X Y b : ℝ) (hX : 0<X) (hW : ∀y,W y≠0 → y≤b)
    (ray : SecondRayIndex) (x : MarkedSecondSource ι Jo 0)
    (hgeom : b*X<primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap) :
    wholeRow p hp hcop hg extra pool negative Ψ m slots J lists a W X Y ray x=0 := by
  rw [wholeRow_eq]
  have hh := actual_profile_zero_of_geometry p hp hcop hg pool (secondInheritedProfile p x Ψ m ray)
    (slots\J) (slots\J) (fun i=>lists i\InverseMomentWholeRetainedSource.deleted p extra negative x)
    (fun i=>lists i\InverseMomentWholeRetainedSource.deleted p extra negative x) a a W W rowMajorant Y X b hX hW hgeom
  rw [hh,mul_zero]


-- @@ L54-57 verbatim
omit hp [∀i,(Ideal.span {p i}).IsMaximal] in
def geometrySource {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn)) (b X : ℝ) :
    Finset (MarkedSecondSource ι Jo Jn) :=
  source.filter (fun x=>primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X)


-- @@ L59-62 verbatim
omit hp [∀i,(Ideal.span {p i}).IsMaximal] in
omit [DecidableEq ι] in
lemma geometrySource_subset {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn)) (b X : ℝ) :
    geometrySource p source b X⊆source := Finset.filter_subset _ _


-- @@ L64-69 verbatim
omit hp [∀i,(Ideal.span {p i}).IsMaximal] in
omit [DecidableEq ι] in
lemma geometrySource_gate {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn)) (b X : ℝ) :
    ∀x∈geometrySource p source b X,
      primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X :=
  fun _x hx=>(Finset.mem_filter.mp hx).2


-- @@ L71-87 verbatim
lemma original_retained_geometry_sum
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    {Jo : ℕ} (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι)
    (source : Finset (MarkedSecondSource ι Jo 0)) (w : MarkedSecondSource ι Jo 0→ℂ)
    (negative : Bool) (Ψ : O→*ℂ) (m : O) (slots J : Finset σ)
    (lists : σ→Finset ι) (a : σ→ι→ℂ) (W : ℝ→ℂ) (X Y b : ℝ)
    (hX : 0<X) (hW : ∀y,W y≠0 → y≤b) (ray : SecondRayIndex) :
    (∑x∈source,w x*wholeRow p hp hcop hg extra pool negative Ψ m slots J lists a W X Y ray x)=
    ∑x∈geometrySource p source b X,w x*wholeRow p hp hcop hg extra pool negative Ψ m slots J lists a W X Y ray x := by
  rw [geometrySource,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  split_ifs with hg₀
  · rfl
  · rw [wholeRow_zero_of_geometry p hp hcop hg extra pool negative Ψ m slots J lists a W X Y b hX hW
      ray x (lt_of_not_ge hg₀),mul_zero]


-- @@ L89-89 verbatim
end SevenEighths.InverseMomentGlobalRetainedGates

-- @@ L90-90 verbatim
end


-- @@ L92-92 verbatim
end OAI
