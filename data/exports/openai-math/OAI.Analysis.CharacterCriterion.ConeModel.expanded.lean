import OAI.Analysis.CharacterCriterion.HereditaryTransport


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



-- @@ L23-23 verbatim
namespace KirchbergRordam.GenericRW.ConeModel

-- @@ L24-24 verbatim
open scoped ComplexOrder ContinuousMapZero BigOperators

-- @@ L25-25 verbatim
open IntervalCalculus HereditaryTransport


-- @@ L27-29 verbatim
instance coneSubringClass : SubringClass
    (StarSubalgebra ℂ C(unitInterval,M2)) C(unitInterval,M2) :=
  StarSubalgebra.subringClass (R := ℂ) (A := C(unitInterval,M2))


-- @@ L31-31 verbatim
instance : CStarAlgebra Cone := StarSubalgebra.cstarAlgebra coneSubalgebra


-- @@ L33-42 verbatim
def scalar : C(unitInterval,ℂ) →⋆ₐ[ℂ] Cone where
  toFun f := ⟨⟨fun t => algebraMap ℂ M2 (f t),by fun_prop⟩,by
    change algebraMap ℂ M2 (f 0) ∈ (⊥ : StarSubalgebra ℂ M2)
    exact StarSubalgebra.algebraMap_mem _ (f 0)⟩
  map_zero' := by apply Subtype.ext; apply ContinuousMap.ext; intro t; exact map_zero (algebraMap ℂ M2)
  map_one' := by apply Subtype.ext; apply ContinuousMap.ext; intro t; exact map_one (algebraMap ℂ M2)
  map_add' f g := by apply Subtype.ext; apply ContinuousMap.ext; intro t; exact map_add (algebraMap ℂ M2) (f t) (g t)
  map_mul' f g := by apply Subtype.ext; apply ContinuousMap.ext; intro t; exact map_mul (algebraMap ℂ M2) (f t) (g t)
  commutes' c := by ext t; rfl
  map_star' f := by apply Subtype.ext; apply ContinuousMap.ext; intro t; exact map_star (StarAlgHom.ofId ℂ M2) (f t)


-- @@ L44-45 verbatim
@[simp] lemma scalar_apply (f : C(unitInterval,ℂ)) (t : unitInterval) :
    (scalar f : C(unitInterval,M2)) t=algebraMap ℂ M2 (f t) := rfl


-- @@ L47-47 verbatim
abbrev tip : Cone := scalar (1-coord)

-- @@ L48-51 verbatim
lemma tip_selfAdjoint : IsSelfAdjoint tip := by
  apply IsSelfAdjoint.map
  ext t
  simp [coord]


-- @@ L53-56 verbatim
lemma scalar_continuous : Continuous scalar := by
  apply Continuous.subtype_mk
  let g : C(ℂ,M2) := ⟨algebraMap ℂ M2,(algebraMapCLM ℂ M2).continuous⟩
  exact g.continuous_postcomp



-- @@ L59-63 verbatim
def entry (i j : Fin rankNum) (f : C(unitInterval,ℂ)₀) : Cone :=
  ⟨⟨fun t => f t • CStarMatrix.ofMatrix (Matrix.single i j (1:ℂ)),by fun_prop⟩,by
    change f 0 • _ ∈ (⊥ : StarSubalgebra ℂ M2)
    rw [map_zero,zero_smul]
    exact zero_mem _⟩


-- @@ L65-68 verbatim
lemma entry_continuous (i j : Fin rankNum) : Continuous (entry i j) := by
  apply Continuous.subtype_mk
  let g : C(ℂ,M2) := ⟨fun c => c • CStarMatrix.ofMatrix (Matrix.single i j (1:ℂ)),by fun_prop⟩
  exact g.continuous_postcomp.comp ContinuousMapZero.isEmbedding_toContinuousMap.continuous


-- @@ L70-92 verbatim
lemma scalar_tip_mem (f : C(unitInterval,ℂ)) (hf : f 1=0) : scalar f ∈ HereditaryTransport.corner tip tip_selfAdjoint := by
  let p : C(unitInterval,ℂ) := (1-coord)^2
  have hzero (t : unitInterval) (ht : p t=0) : t=1 := by
    have h : (1-((t:ℝ):ℂ))^2=0 := ht
    have hc : ((t:ℝ):ℂ)=1 := by
      have := sq_eq_zero_iff.mp h
      exact (sub_eq_zero.mp this).symm
    apply Subtype.ext
    exact_mod_cast hc
  let f' : Vanish.Functions {t | p t=0} := ⟨f,by intro t ht; rw [hzero t ht]; exact hf⟩
  have hh (x : Vanish.Functions {t | p t=0}) : scalar x.val ∈ HereditaryTransport.corner tip tip_selfAdjoint := by
    refine (Vanish.multiplier_dense p).induction_on x
      ((cornerClosed tip tip_selfAdjoint).preimage (scalar_continuous.comp continuous_subtype_val)) ?_
    intro g
    have he : scalar ((Vanish.multiplier p g).val)=tip*scalar g*tip := by
      change scalar (p*g)=scalar (1-coord)*scalar g*scalar (1-coord)
      rw [← map_mul,← map_mul]
      congr 1
      dsimp [p]
      ring
    rw [he]
    exact HereditaryTransport.mem_corner tip tip_selfAdjoint (scalar g)
  exact hh f'


-- @@ L94-94 verbatim
private def entryWeight : C(unitInterval,ℂ) := coord*(1-coord)^2


-- @@ L96-99 verbatim
omit instSize in
private lemma weight_zero
    [KirchbergRordam.GenericRW.Size]
    : entryWeight 0=0 := by simp [entryWeight,coord]


-- @@ L101-102 verbatim
private def fromWeight (f : Vanish.Functions {t | entryWeight t=0}) : C(unitInterval,ℂ)₀ :=
  ⟨f.val,f.property 0 weight_zero⟩


-- @@ L104-106 verbatim
private lemma fromWeight_continuous : Continuous fromWeight := by
  rw [ContinuousMapZero.isEmbedding_toContinuousMap.continuous_iff]
  exact continuous_subtype_val


-- @@ L108-141 verbatim
lemma entry_tip_mem (i j : Fin rankNum) (f : C(unitInterval,ℂ)₀) (hf : f 1=0) :
    entry i j f ∈ HereditaryTransport.corner tip tip_selfAdjoint := by
  have hzero (t : unitInterval) (ht : entryWeight t=0) : t=0 ∨ t=1 := by
    change ((t:ℝ):ℂ)*(1-((t:ℝ):ℂ))^2=0 at ht
    rcases mul_eq_zero.mp ht with h|h
    · left; apply Subtype.ext; exact_mod_cast h
    · right; apply Subtype.ext
      have hc : ((t:ℝ):ℂ)=1 := (sub_eq_zero.mp (sq_eq_zero_iff.mp h)).symm
      exact_mod_cast hc
  let f' : Vanish.Functions {t | entryWeight t=0} := ⟨(f:C(unitInterval,ℂ)),by
    intro t ht
    rcases hzero t ht with rfl|rfl
    · exact map_zero f
    · exact hf⟩
  have hh (x : Vanish.Functions {t | entryWeight t=0}) :
      entry i j (fromWeight x) ∈ HereditaryTransport.corner tip tip_selfAdjoint := by
    refine (Vanish.multiplier_dense entryWeight).induction_on x
      ((cornerClosed tip tip_selfAdjoint).preimage ((entry_continuous i j).comp fromWeight_continuous)) ?_
    intro g
    have he : entry i j (fromWeight (Vanish.multiplier entryWeight g))=
        tip*entry i j (coordMul g)*tip := by
      apply Subtype.ext
      apply ContinuousMap.ext
      intro t
      change ((((t:ℝ):ℂ)*(1-((t:ℝ):ℂ))^2)*g t) • CStarMatrix.ofMatrix (Matrix.single i j (1:ℂ))=
        (algebraMap ℂ M2 (1-((t:ℝ):ℂ)))*
          ((((t:ℝ):ℂ)*g t) • CStarMatrix.ofMatrix (Matrix.single i j (1:ℂ)))*
          (algebraMap ℂ M2 (1-((t:ℝ):ℂ)))
      simp only [Algebra.algebraMap_eq_smul_one,smul_mul_assoc,mul_smul_comm,one_mul,mul_one,smul_smul]
      congr 1
      ring
    rw [he]
    exact HereditaryTransport.mem_corner tip tip_selfAdjoint _
  exact hh f'



-- @@ L144-171 verbatim
lemma vanish_one_mem {f : Cone} (hf : (f:C(unitInterval,M2)) 1=0) :
    f ∈ HereditaryTransport.corner tip tip_selfAdjoint := by
  let c : C(unitInterval,ℂ) := ⟨fun t => (f:C(unitInterval,M2)) t 0 0,by fun_prop⟩
  have hc1 : c 1=0 := by change (f:C(unitInterval,M2)) 1 0 0=0; rw [hf]; rfl
  have hsc := scalar_tip_mem c hc1
  obtain ⟨z,hz⟩ := f.property
  have hz' : (f:C(unitInterval,M2)) 0=algebraMap ℂ M2 z := hz.symm
  let r (i j : Fin rankNum) : C(unitInterval,ℂ)₀ := ⟨⟨fun t =>
      (f:C(unitInterval,M2)) t i j-(algebraMap ℂ M2 (c t)) i j,by fun_prop⟩,by
    change (f:C(unitInterval,M2)) 0 i j-(algebraMap ℂ M2 ((f:C(unitInterval,M2)) 0 0 0)) i j=0
    rw [hz']
    have hz00 : (algebraMap ℂ M2 z) 0 0=z := by simp [Algebra.algebraMap_eq_smul_one]
    rw [hz00]
    exact sub_self _⟩
  have hr (i j : Fin rankNum) : r i j 1=0 := by
    change (f:C(unitInterval,M2)) 1 i j-(algebraMap ℂ M2 (c 1)) i j=0
    rw [hf,hc1,map_zero]; exact sub_self _
  have he : f=scalar c+∑ i,∑ j,entry i j (r i j) := by
    apply Subtype.ext
    ext t u v
    simp only [evaluate_add,evaluate_sum,CStarMatrix.add_apply,matrixSum_entry]
    change (f:C(unitInterval,M2)) t u v = (algebraMap ℂ M2 (c t)) u v +
      ∑ i, ∑ j, (r i j t) * (Matrix.single i j (1:ℂ)) u v
    simp [Matrix.single, ite_and, mul_ite, r]
  rw [he]
  exact (HereditaryTransport.corner tip tip_selfAdjoint).add_mem hsc
    ((HereditaryTransport.corner tip tip_selfAdjoint).sum_mem fun i _ =>
      (HereditaryTransport.corner tip tip_selfAdjoint).sum_mem fun j _ => entry_tip_mem i j (r i j) (hr i j))


-- @@ L173-173 verbatim
end KirchbergRordam.GenericRW.ConeModel


-- @@ L175-175 verbatim
namespace KirchbergRordam.GenericRW.IntervalCalculus

-- @@ L176-176 verbatim
open scoped CStarAlgebra

-- @@ L177-177 verbatim
variable {A : Type*} [CStarAlgebra A]



-- @@ L180-201 verbatim
omit instSize in
lemma ext_coord.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    (φ ψ : C(unitInterval,ℂ) →⋆ₐ[ℂ] A) (h : φ coord=ψ coord) : φ=ψ := by
  let S : StarSubalgebra ℂ C(unitInterval,ℂ) := StarAlgHom.equalizer φ ψ
  have hc : IsClosed (S : Set C(unitInterval,ℂ)) := isClosed_eq (map_continuous φ) (map_continuous ψ)
  have hs : S.SeparatesPoints := by
    intro x y hxy
    refine ⟨coord,⟨coord,h,rfl⟩,?_⟩
    intro he
    apply hxy
    apply Subtype.ext
    change ((x:ℝ):ℂ)=((y:ℝ):ℂ) at he
    exact_mod_cast he
  have ht : S=⊤ := by
    rw [← le_antisymm (StarSubalgebra.topologicalClosure_minimal le_rfl hc) S.le_topologicalClosure]
    exact ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints S hs
  apply StarAlgHom.ext
  intro f
  exact show f∈S from ht ▸ trivial

-- @@ L202-202 verbatim
end KirchbergRordam.GenericRW.IntervalCalculus


-- @@ L204-204 verbatim
namespace KirchbergRordam.GenericRW.ConeModel

-- @@ L205-205 verbatim
open scoped ComplexOrder BigOperators

-- @@ L206-206 verbatim
open IntervalCalculus

-- @@ L207-217 verbatim
lemma scalar_coord : scalar coord = ∑ i : Fin rankNum, corner i i := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  rw [evaluate_sum]
  change algebraMap ℂ M2 (coord t) = ∑ i : Fin rankNum, (corner i i:C(unitInterval,M2)) t
  simp only [corner_apply]
  ext i j
  rw [matrixSum_entry]
  change (algebraMap ℂ M2 (coord t)) i j = ∑ k : Fin rankNum, (t:ℂ) * (Matrix.single k k (1:ℂ)) i j
  simp [coord, Algebra.algebraMap_eq_smul_one, Matrix.single, ite_and, mul_ite, CStarMatrix.one_apply]

-- @@ L218-218 verbatim
end KirchbergRordam.GenericRW.ConeModel


-- @@ L220-220 verbatim
namespace KirchbergRordam.GenericRW.SquareZeroCone.WeightedMatrix

-- @@ L221-221 verbatim
open scoped CStarAlgebra

-- @@ L222-222 verbatim
variable {A : Type*} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]

-- @@ L223-223 verbatim
variable (W : WeightedMatrix A)


-- @@ L225-232 verbatim
lemma coneHom_scalar (f : C(unitInterval,ℂ)) : W.coneHom (ConeModel.scalar f)=W.eval f := by
  have he : W.coneHom.comp ConeModel.scalar=W.eval := by
    apply IntervalCalculus.ext_coord
    change W.coneHom (ConeModel.scalar IntervalCalculus.coord)=W.eval _
    rw [ConeModel.scalar_coord,map_sum]
    simp only [W.coneHom_corner,W.diagonal]
    exact (IntervalCalculus.hom_coord W.h_nonneg W.norm_h_le).symm
  exact DFunLike.congr_fun he f


-- @@ L234-235 verbatim
lemma coneHom_tip : W.coneHom ConeModel.tip=1-W.h := by
  rw [coneHom_scalar,map_sub,map_one,IntervalCalculus.hom_coord]


-- @@ L237-247 verbatim
lemma coneHom_hereditary (f : HereditaryTransport.corner ConeModel.tip ConeModel.tip_selfAdjoint) :
    W.coneHom f ∈ HereditaryTransport.corner (1-W.h)
      ((IsSelfAdjoint.one A).sub (IsSelfAdjoint.of_nonneg W.h_nonneg)) := by
  let ha := (IsSelfAdjoint.one A).sub (IsSelfAdjoint.of_nonneg W.h_nonneg)
  refine (HereditaryTransport.dense ConeModel.tip ConeModel.tip_selfAdjoint).induction_on f
    ((HereditaryTransport.cornerClosed (1-W.h) ha).preimage
      ((map_continuous W.coneHom).comp continuous_subtype_val)) ?_
  intro x
  change W.coneHom (ConeModel.tip*x*ConeModel.tip) ∈ _
  rw [map_mul,map_mul,W.coneHom_tip]
  exact HereditaryTransport.mem_corner (1-W.h) ha (W.coneHom x)


-- @@ L249-249 verbatim
end KirchbergRordam.GenericRW.SquareZeroCone.WeightedMatrix

-- @@ L250-250 verbatim
namespace KirchbergRordam.GenericRW.ConeModel

-- @@ L251-251 verbatim
open scoped ComplexOrder CStarAlgebra



-- @@ L254-260 verbatim
def defectSubalgebra : NonUnitalStarSubalgebra ℂ Cone where
  carrier := {f | (f:C(unitInterval,M2)) 1=0}
  zero_mem' := rfl
  add_mem' := by intro f g hf hg; change (f:C(unitInterval,M2)) 1+(g:C(unitInterval,M2)) 1=0; rw [hf,hg,add_zero]
  mul_mem' := by intro f g hf hg; change (f:C(unitInterval,M2)) 1*(g:C(unitInterval,M2)) 1=0; rw [hf,zero_mul]
  smul_mem' := by intro c f hf; change c • (f:C(unitInterval,M2)) 1=0; rw [hf,smul_zero]
  star_mem' := by intro f hf; change star ((f:C(unitInterval,M2)) 1)=0; rw [hf,star_zero]


-- @@ L262-262 verbatim
abbrev Defect := defectSubalgebra

-- @@ L263-263 verbatim
instance defectZero : Zero Defect := ⟨⟨0, rfl⟩⟩


-- @@ L265-266 verbatim
instance defectClosed : IsClosed (defectSubalgebra : Set Cone) :=
  isClosed_singleton.preimage ((continuous_eval_const (1:unitInterval)).comp continuous_subtype_val)

-- @@ L267-267 verbatim
instance : NonUnitalCStarAlgebra Defect := inferInstance



-- @@ L270-276 verbatim
def toHereditary : Defect →⋆ₙₐ[ℂ] HereditaryTransport.corner tip tip_selfAdjoint where
  toFun f := ⟨f,vanish_one_mem f.property⟩
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl



-- @@ L279-280 verbatim
def scalarDefect (f : C(unitInterval,ℂ)) (hf : f 1=0) : Defect :=
  ⟨scalar f,by change algebraMap ℂ M2 (f 1)=0; rw [hf,map_zero]⟩


-- @@ L282-282 verbatim
end KirchbergRordam.GenericRW.ConeModel


-- @@ L284-284 verbatim
namespace KirchbergRordam.GenericRW.SquareZeroCone.WeightedMatrix

-- @@ L285-285 verbatim
variable {A : Type*} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]

-- @@ L286-286 verbatim
variable (W : WeightedMatrix A)



-- @@ L289-296 verbatim
def defectHom : ConeModel.Defect →⋆ₙₐ[ℂ] HereditaryTransport.corner (1-W.h)
    ((IsSelfAdjoint.one A).sub (IsSelfAdjoint.of_nonneg W.h_nonneg)) where
  toFun f := ⟨W.coneHom (f:ConeModel.Cone),W.coneHom_hereditary (ConeModel.toHereditary f)⟩
  map_zero' := Subtype.ext (map_zero W.coneHom)
  map_add' _ _ := Subtype.ext (map_add W.coneHom _ _)
  map_mul' _ _ := Subtype.ext (map_mul W.coneHom _ _)
  map_smul' c _ := Subtype.ext (map_smul W.coneHom c _)
  map_star' _ := Subtype.ext (map_star W.coneHom _)


-- @@ L298-299 verbatim
lemma defectHom_scalar (f : C(unitInterval,ℂ)) (hf : f 1=0) :
    (W.defectHom (ConeModel.scalarDefect f hf):A)=W.eval f := W.coneHom_scalar f


-- @@ L301-301 verbatim
end KirchbergRordam.GenericRW.SquareZeroCone.WeightedMatrix

-- @@ L302-302 verbatim
end


-- @@ L304-304 verbatim
end OAI
