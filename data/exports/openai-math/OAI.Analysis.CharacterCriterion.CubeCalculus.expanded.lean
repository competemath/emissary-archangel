import OAI.Analysis.CharacterCriterion.ConePauli


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped TensorProduct

-- @@ L7-7 verbatim
open scoped InnerProductSpace

-- @@ L8-8 verbatim
open scoped BigOperators

-- @@ L9-9 verbatim
open Set Module

-- @@ L10-10 verbatim
open Topology

-- @@ L11-11 verbatim
open NormedSpace

-- @@ L12-12 verbatim
open scoped ComplexOrder

-- @@ L13-13 verbatim
open scoped ComplexOrder

-- @@ L14-14 verbatim
open scoped InnerProductSpace

-- @@ L15-15 verbatim
open scoped InnerProductSpace

-- @@ L16-16 verbatim
open NormedSpace

-- @@ L17-17 verbatim
open scoped TensorProduct InnerProductSpace

-- @@ L18-18 verbatim
open UniformSpace

-- @@ L19-19 verbatim
variable [instSize : KirchbergRordam.GenericRW.Size]

-- @@ L20-20 verbatim
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n

-- @@ L21-21 verbatim
variable [instPauliData : KirchbergRordam.GenericRW.PauliData]



-- @@ L24-24 verbatim
namespace KirchbergRordam.GenericRW.JointCalculus

-- @@ L25-25 verbatim
open WeakDual

-- @@ L26-26 verbatim
variable {S : Type*} [CommCStarAlgebra S]

-- @@ L27-27 verbatim
variable {I X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]

-- @@ L28-28 verbatim
variable (φ : I → C(X,ℂ) →⋆ₐ[ℂ] S)


-- @@ L30-33 verbatim
def coordinates : C(characterSpace ℂ S,I→X) where
  toFun χ i := (CharacterSpace.homeoEval X ℂ).symm (CharacterSpace.compContinuousMap (φ i) χ)
  continuous_toFun := continuous_pi fun i => (CharacterSpace.homeoEval X ℂ).symm.continuous.comp
    (CharacterSpace.compContinuousMap (φ i)).continuous


-- @@ L35-36 verbatim
def hom : C(I→X,ℂ) →⋆ₐ[ℂ] S :=
  (gelfandStarTransform S).symm.toStarAlgHom.comp ((coordinates φ).compStarAlgHom' ℂ ℂ)


-- @@ L38-38 verbatim
def coordinate (i : I) (f : C(X,ℂ)) : C(I→X,ℂ) := f.comp ⟨fun t => t i,continuous_apply i⟩


-- @@ L40-60 verbatim
omit instSize instPauliData in
lemma hom_coordinate.{contextLevel1, contextLevel2, contextLevel3}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {S : Type contextLevel1}
    [CommCStarAlgebra S]
    {I : Type contextLevel2}
    {X : Type contextLevel3}
    [TopologicalSpace X]
    [CompactSpace X]
    [T2Space X]
    (φ : I → C(X, ℂ) →⋆ₐ[ℂ] S)
    (i : I) (f : C(X,ℂ)) : hom φ (coordinate i f)=φ i f := by
  apply (gelfandStarTransform S).injective
  change gelfandStarTransform S ((gelfandStarTransform S).symm _) = _
  rw [StarAlgEquiv.apply_symm_apply]
  ext χ
  change f ((CharacterSpace.homeoEval X ℂ).symm (CharacterSpace.compContinuousMap (φ i) χ)) = χ (φ i f)
  have h := congrArg (fun ψ : characterSpace ℂ C(X,ℂ) => ψ f)
    ((CharacterSpace.homeoEval X ℂ).apply_symm_apply (CharacterSpace.compContinuousMap (φ i) χ))
  exact h


-- @@ L62-62 verbatim
end KirchbergRordam.GenericRW.JointCalculus


-- @@ L64-64 verbatim
namespace KirchbergRordam.GenericRW.CentralCalculus

-- @@ L65-65 verbatim
variable (A : Type*) [CStarAlgebra A]

-- @@ L66-66 verbatim
def center : StarSubalgebra ℂ A := StarSubalgebra.centralizer ℂ Set.univ

-- @@ L67-69 verbatim
instance centerClosed : IsClosed (center A : Set A) := by
  change IsClosed (Set.univ ∪ star Set.univ).centralizer
  exact Set.isClosed_centralizer _

-- @@ L70-71 verbatim
instance centerComm : CommCStarAlgebra (center A) where
  mul_comm a b := Subtype.ext (((StarSubalgebra.mem_centralizer_iff ℂ).mp b.property) a.1 (Set.mem_univ _)).1


-- @@ L73-73 verbatim
def inclusion : center A →⋆ₐ[ℂ] A := (center A).subtype

-- @@ L74-74 verbatim
variable {A}

-- @@ L75-84 verbatim
omit instSize instPauliData in
lemma mem_center.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    {a : A} (ha : ∀ b,Commute a b) : a∈center A := by
  apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
  intro b _
  exact ⟨(ha b).eq.symm,(ha (star b)).eq.symm⟩

-- @@ L85-92 verbatim
omit instSize instPauliData in
lemma commute.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    (a : center A) (b : A) : Commute (a:A) b :=
  (((StarSubalgebra.mem_centralizer_iff ℂ).mp a.property) b (Set.mem_univ _)).1.symm


-- @@ L94-94 verbatim
variable {I X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]

-- @@ L95-95 verbatim
variable (φ : I→C(X,ℂ)→⋆ₐ[ℂ] A) (hc : ∀ i f a,Commute (φ i f) a)

-- @@ L96-97 verbatim
def family (i : I) : C(X,ℂ) →⋆ₐ[ℂ] center A :=
  (φ i).codRestrict (center A) fun f => mem_center (hc i f)

-- @@ L98-99 verbatim
def hom : C(I→X,ℂ) →⋆ₐ[ℂ] A :=
  (inclusion A).comp (JointCalculus.hom (family φ hc))

-- @@ L100-104 verbatim
lemma hom_coordinate (i : I) (f : C(X,ℂ)) :
    hom φ hc (JointCalculus.coordinate i f)=φ i f := by
  change ((JointCalculus.hom (family φ hc) _ : center A):A)=_
  rw [JointCalculus.hom_coordinate]
  rfl

-- @@ L105-105 verbatim
lemma hom_commute (f : C(I→X,ℂ)) (a : A) : Commute (hom φ hc f) a := commute _ _

-- @@ L106-106 verbatim
end KirchbergRordam.GenericRW.CentralCalculus


-- @@ L108-108 verbatim
namespace KirchbergRordam.GenericRW.CubeCalculus

-- @@ L109-109 verbatim
open scoped CStarAlgebra

-- @@ L110-110 verbatim
variable {I A : Type*} [CStarAlgebra A]

-- @@ L111-112 verbatim
def coord (i : I) : C(I→unitInterval,ℂ) :=
  ⟨fun t => ((t i:ℝ):ℂ),by fun_prop⟩

-- @@ L113-138 verbatim
omit instSize instPauliData in
lemma ext_coord.{contextLevel1, contextLevel2}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {I : Type contextLevel1}
    {A : Type contextLevel2}
    [CStarAlgebra A]
    (φ ψ : C(I→unitInterval,ℂ) →⋆ₐ[ℂ] A)
    (h : ∀ i,φ (coord i)=ψ (coord i)) : φ=ψ := by
  let S : StarSubalgebra ℂ C(I→unitInterval,ℂ) := StarAlgHom.equalizer φ ψ
  have hc : IsClosed (S : Set C(I→unitInterval,ℂ)) := isClosed_eq (map_continuous φ) (map_continuous ψ)
  have hs : S.SeparatesPoints := by
    intro x y hxy
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hxy
    refine ⟨coord i,⟨coord i,h i,rfl⟩,?_⟩
    intro he
    apply hi
    apply Subtype.ext
    change ((x i:ℝ):ℂ)=((y i:ℝ):ℂ) at he
    exact_mod_cast he
  have ht : S=⊤ := by
    rw [← le_antisymm (StarSubalgebra.topologicalClosure_minimal le_rfl hc) S.le_topologicalClosure]
    exact ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints S hs
  apply StarAlgHom.ext
  intro f
  exact show f∈S from ht ▸ trivial

-- @@ L139-139 verbatim
end KirchbergRordam.GenericRW.CubeCalculus



-- @@ L142-142 verbatim
namespace KirchbergRordam.GenericRW.CubeFrame

-- @@ L143-143 verbatim
open scoped BigOperators CStarAlgebra

-- @@ L144-144 verbatim
variable {X B T I : Type*} [TopologicalSpace X] [CompactSpace X]

-- @@ L145-145 verbatim
variable [CStarAlgebra B] [CStarAlgebra T] [Fintype I] [DecidableEq I]

-- @@ L146-146 verbatim
variable (κ : C(X,ℂ) →⋆ₐ[ℂ] B) (ρ : B →⋆ₐ[ℂ] C(X,T))

-- @@ L147-147 verbatim
variable (p : I→C(X,ℂ)) (u : I→B) (e : I→T)

-- @@ L148-148 verbatim
variable (hc : ∀ f a,Commute (κ f) a)

-- @@ L149-149 verbatim
variable (hu : ∀ i,star (u i)*u i=κ (star (p i)*p i))


-- @@ L151-178 verbatim
omit hc hu in
omit [Fintype I] [DecidableEq I] in
omit instSize instPauliData in
lemma term_norm.{contextLevel1, contextLevel2, contextLevel3}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {X : Type contextLevel1}
    {B : Type contextLevel2}
    {I : Type contextLevel3}
    [TopologicalSpace X]
    [CompactSpace X]
    [CStarAlgebra B]
    (κ : C(X, ℂ) →⋆ₐ[ℂ] B)
    (p : I → C(X, ℂ))
    (u : I → B)
    (hc : ∀ (f : C(X, ℂ)) (a : B), Commute (κ f) a)
    (hu : ∀ (i : I), Star.star (u i) * u i = κ (Star.star (p i) * p i))
    (f : C(X,ℂ)) (i : I) : ‖κ f*u i‖≤‖f*p i‖ := by
  have he : star (κ f*u i)*(κ f*u i)=κ (star (f*p i)*(f*p i)) := by
    rw [star_mul,← map_star,mul_assoc,← mul_assoc (κ (star f)),← map_mul]
    rw [← mul_assoc,← (hc (star f*f) (star (u i))).eq,mul_assoc,hu,← map_mul]
    congr 1
    simp only [star_mul]
    ring
  have hn : ‖κ f*u i‖*‖κ f*u i‖≤‖f*p i‖*‖f*p i‖ := by
    rw [← CStarRing.norm_star_mul_self,he,← CStarRing.norm_star_mul_self]
    exact NonUnitalStarAlgHom.norm_apply_le κ _
  nlinarith [norm_nonneg (κ f*u i),norm_nonneg (f*p i)]


-- @@ L180-180 verbatim
def expansion (f : I→C(X,ℂ)) : B := ∑ i,κ (f i)*u i

-- @@ L181-181 verbatim
variable (hκ : ∀ f t,ρ (κ f) t=algebraMap ℂ T (f t))

-- @@ L182-182 verbatim
variable (hρ : ∀ i t,ρ (u i) t=p i t • e i)

-- @@ L183-183 verbatim
variable (ℓ : I→T →L[ℂ] ℂ) (hℓ : ∀ i j,ℓ i (e j)=if i=j then 1 else 0)


-- @@ L185-213 verbatim
omit hκ hρ hℓ in
omit [CompactSpace X] in
omit instSize instPauliData in
lemma coefficient.{contextLevel1, contextLevel2, contextLevel3, contextLevel4}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {X : Type contextLevel1}
    {B : Type contextLevel2}
    {T : Type contextLevel3}
    {I : Type contextLevel4}
    [TopologicalSpace X]
    [CStarAlgebra B]
    [CStarAlgebra T]
    [Fintype I]
    [DecidableEq I]
    (κ : C(X, ℂ) →⋆ₐ[ℂ] B)
    (ρ : B →⋆ₐ[ℂ] C(X, T))
    (p : I → C(X, ℂ))
    (u : I → B)
    (e : I → T)
    (hκ : ∀ (f : C(X, ℂ)) (t : X), (ρ (κ f)) t = (Algebra.algebraMap ℂ T) (f t))
    (hρ : ∀ (i : I) (t : X), (ρ (u i)) t = (p i) t • e i)
    (ℓ : I → T →L[ℂ] ℂ)
    (hℓ : ∀ (i j : I), (ℓ i) (e j) = if i = j then 1 else 0)
    (f : I→C(X,ℂ)) (i : I) (t : X) :
    ℓ i (ρ (expansion κ u f) t)= (f i*p i) t := by
  simp only [expansion,map_sum,ContinuousMap.sum_apply,map_mul,ContinuousMap.mul_apply,hκ,hρ,
    Algebra.algebraMap_eq_smul_one,smul_mul_smul_comm,one_mul,map_smul,hℓ]
  simp


-- @@ L215-229 verbatim
include hc hu hκ hρ hℓ in
lemma expansion_norm (f : I→C(X,ℂ)) :
    ‖expansion κ u f‖≤(∑ i,‖ℓ i‖)*‖ρ (expansion κ u f)‖ := by
  apply (norm_sum_le _ _).trans
  calc
    ∑ i,‖κ (f i)*u i‖ ≤ ∑ i,‖f i*p i‖ := Finset.sum_le_sum fun i _ => term_norm κ p u hc hu _ i
    _ ≤ ∑ i,‖ℓ i‖*‖ρ (expansion κ u f)‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
      intro t
      rw [← coefficient κ ρ p u e hκ hρ ℓ hℓ f i t]
      exact ((ℓ i).le_opNorm _).trans (mul_le_mul_of_nonneg_left
        (ContinuousMap.norm_coe_le_norm _ t) (norm_nonneg _))
    _ = _ := (Finset.sum_mul ..).symm


-- @@ L231-244 verbatim
include hc hu hκ hρ hℓ in


theorem faithful (hd : DenseRange (expansion κ u)) : Function.Injective ρ := by
  have hb (x : B) : ‖x‖≤(∑ i,‖ℓ i‖)*‖ρ x‖ := by
    apply hd.induction_on (p:=fun x => ‖x‖≤(∑ i,‖ℓ i‖)*‖ρ x‖) x
    · exact isClosed_le continuous_norm (continuous_const.mul (map_continuous ρ).norm)
    · exact expansion_norm κ ρ p u e hc hu hκ hρ ℓ hℓ
  intro x y hxy
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  have hz : ρ (x-y)=0 := by rw [map_sub,hxy,sub_self]
  simpa only [hz,norm_zero,mul_zero] using hb (x-y)


-- @@ L246-248 verbatim
include hc hu hκ hρ hℓ in
lemma closed_range (hd : DenseRange (expansion κ u)) : IsClosed (Set.range ρ) :=
  (NonUnitalStarAlgHom.isometry ρ (faithful κ ρ p u e hc hu hκ hρ ℓ hℓ hd)).isClosedEmbedding.isClosed_range

-- @@ L249-249 verbatim
end KirchbergRordam.GenericRW.CubeFrame


-- @@ L251-251 verbatim
namespace KirchbergRordam.GenericRW.CubeFrame

-- @@ L252-252 verbatim
open scoped BigOperators

-- @@ L253-253 verbatim
variable {X B T I : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]

-- @@ L254-254 verbatim
variable [CStarAlgebra B] [CStarAlgebra T] [Fintype I] [DecidableEq I]


-- @@ L256-259 verbatim
def scalarSection (a : T) : C(X,ℂ) →ₗ[ℂ] C(X,T) where
  toFun f := ⟨fun t => f t • a,by fun_prop⟩
  map_add' f g := by ext t; simp [add_smul]
  map_smul' c f := by ext t; simp [smul_smul]


-- @@ L261-272 verbatim
omit [CompactSpace X] [T2Space X] in
omit instSize instPauliData in
lemma scalarSection_continuous.{contextLevel1, contextLevel2}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {X : Type contextLevel1}
    {T : Type contextLevel2}
    [TopologicalSpace X]
    [CStarAlgebra T]
    (a : T) : Continuous (scalarSection (X:=X) a) := by
  let g : C(ℂ,T) := ⟨fun c => c • a,by fun_prop⟩
  exact g.continuous_postcomp


-- @@ L274-274 verbatim
variable (κ : C(X,ℂ) →⋆ₐ[ℂ] B) (ρ : B →⋆ₐ[ℂ] C(X,T))

-- @@ L275-275 verbatim
variable (p : I→C(X,ℂ)) (u : I→B) (e : I→T)

-- @@ L276-276 verbatim
variable (hκ : ∀ f t,ρ (κ f) t=algebraMap ℂ T (f t))

-- @@ L277-277 verbatim
variable (hρ : ∀ i t,ρ (u i) t=p i t • e i)

-- @@ L278-297 verbatim
include hκ hρ in
omit [Fintype I] [DecidableEq I] in


lemma coefficient_mem_range (hclosed : IsClosed (Set.range ρ)) (i : I)
    (f : C(X,ℂ)) (hf : ∀ t,p i t=0 → f t=0) :
    scalarSection (e i) f ∈ Set.range ρ := by
  let f' : Vanish.Functions {t | p i t=0} := ⟨f,hf⟩
  have h (g : Vanish.Functions {t | p i t=0}) :
      scalarSection (e i) g.val ∈ Set.range ρ := by
    refine (Vanish.multiplier_dense (p i)).induction_on g
      (hclosed.preimage ((scalarSection_continuous (e i)).comp continuous_subtype_val)) ?_
    intro a
    refine ⟨κ a*u i,?_⟩
    ext t
    simp only [map_mul,ContinuousMap.mul_apply,hκ,hρ,
      Algebra.algebraMap_eq_smul_one,smul_mul_smul_comm,one_mul]
    change (a t*p i t) • e i = (p i t*a t) • e i
    rw [mul_comm]
  exact h f'


-- @@ L299-299 verbatim
variable (ℓ : I→T →L[ℂ] ℂ)

-- @@ L300-300 verbatim
variable (hspan : ∀ a : T,∑ i,ℓ i a • e i=a)

-- @@ L301-316 verbatim
include hκ hρ hspan in
omit [DecidableEq I] in


theorem section_mem_range (hclosed : IsClosed (Set.range ρ)) (f : C(X,T))
    (hf : ∀ i t,p i t=0 → ℓ i (f t)=0) : f∈Set.range ρ := by
  let c (i : I) : C(X,ℂ) := ⟨fun t => ℓ i (f t),(ℓ i).continuous.comp f.continuous⟩
  have hm (i : I) : scalarSection (e i) (c i) ∈ Set.range ρ :=
    coefficient_mem_range κ ρ p u e hκ hρ hclosed i (c i) (hf i)
  have hs : ∑ i,scalarSection (e i) (c i)=f := by
    ext t
    simp only [ContinuousMap.sum_apply]
    exact hspan (f t)
  rw [← hs]
  change (∑ i,scalarSection (e i) (c i)) ∈ ρ.range
  exact sum_mem fun i _ => hm i


-- @@ L318-318 verbatim
variable (hc : ∀ f a,Commute (κ f) a)

-- @@ L319-319 verbatim
variable (hu : ∀ i,star (u i)*u i=κ (star (p i)*p i))

-- @@ L320-320 verbatim
variable (hℓ : ∀ i j,ℓ i (e j)=if i=j then 1 else 0)

-- @@ L321-335 verbatim
include hc hu hκ hρ hℓ hspan in


theorem exists_unique_lift (hd : DenseRange (expansion κ u)) (f : C(X,T))
    (hf : ∀ i t,p i t=0 → ℓ i (f t)=0) :
    ∃! b : B,ρ b=f ∧ ‖b‖=‖f‖ := by
  have hi := faithful κ ρ p u e hc hu hκ hρ ℓ hℓ hd
  obtain ⟨b,hb⟩ := section_mem_range κ ρ p u e hκ hρ ℓ hspan
    (closed_range κ ρ p u e hc hu hκ hρ ℓ hℓ hd) f hf
  refine ⟨b,⟨hb,?_⟩,?_⟩
  · rw [← hb]
    simpa only [map_zero,dist_zero_right] using
      ((NonUnitalStarAlgHom.isometry ρ hi).dist_eq b 0).symm
  · intro a ha
    exact hi (ha.1.trans hb.symm)

-- @@ L336-336 verbatim
end KirchbergRordam.GenericRW.CubeFrame

-- @@ L337-337 verbatim
end


-- @@ L339-339 verbatim
end OAI
