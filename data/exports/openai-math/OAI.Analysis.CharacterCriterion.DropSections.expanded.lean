import OAI.Analysis.CharacterCriterion.FieldCalculus


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
namespace KirchbergRordam.GenericRW.DropSections

-- @@ L24-24 verbatim
open scoped Matrix Kronecker BigOperators ComplexOrder

-- @@ L25-25 verbatim
open IntervalCalculus

-- @@ L26-26 verbatim
abbrev Ix := Fin rankNum × Fin (rankNum+1)

-- @@ L27-27 verbatim
abbrev Scalar := C(unitInterval,ℂ)

-- @@ L28-28 verbatim
abbrev Mat := Matrix Ix Ix Scalar

-- @@ L29-29 verbatim
abbrev Small2 := Matrix (Fin rankNum) (Fin rankNum) ℂ

-- @@ L30-30 verbatim
abbrev Small3 := Matrix (Fin (rankNum+1)) (Fin (rankNum+1)) ℂ



-- @@ L33-46 verbatim
def entries : C(unitInterval,M6) →⋆ₐ[ℂ] Mat where
  toFun f i j := ⟨fun t => f t i j, by
    exact (continuous_apply j).comp ((continuous_apply i).comp
      f.continuous)⟩
  map_zero' := by ext i j t; rfl
  map_one' := by ext i j t; by_cases h : i=j <;> simp [Matrix.one_apply,h]
  map_add' _ _ := by ext i j t; rfl
  map_mul' f g := by
    ext i j t
    change (∑ k, f t i k * g t k j) = ((∑ k, _ * _) : Scalar) t
    simp only [ContinuousMap.sum_apply, ContinuousMap.mul_apply]
    rfl
  commutes' c := by ext i j t; by_cases h : i=j <;> simp [Algebra.algebraMap_eq_smul_one,h]
  map_star' f := by ext i j t; rfl


-- @@ L48-49 verbatim
lemma entries_apply (f : C(unitInterval,M6)) (i j : Ix) (t : unitInterval) :
    entries f i j t = f t i j := rfl



-- @@ L52-63 verbatim
def constMat : Matrix Ix Ix ℂ →⋆ₐ[ℂ] Mat where
  toFun a i j := ContinuousMap.const _ (a i j)
  map_zero' := by ext i j t; rfl
  map_one' := by ext i j t; by_cases h : i=j <;> simp [Matrix.one_apply,h]
  map_add' _ _ := by ext i j t; rfl
  map_mul' a b := by
    ext i j t
    change (∑ k, a i k * b k j) =
      ((∑ k, ContinuousMap.const _ (a i k) * ContinuousMap.const _ (b k j)) : Scalar) t
    simp only [ContinuousMap.sum_apply, ContinuousMap.mul_apply, ContinuousMap.const_apply]
  commutes' c := by ext i j t; by_cases h : i=j <;> simp [Algebra.algebraMap_eq_smul_one,h]
  map_star' _ := by ext i j t; rfl


-- @@ L65-65 verbatim
def leftConst : Small2 →⋆ₐ[ℂ] Mat := constMat.comp leftMatrixAlgebra


-- @@ L67-67 verbatim
def rightConst : Small3 →⋆ₐ[ℂ] Mat := constMat.comp rightMatrixAlgebra



-- @@ L70-73 verbatim
def times (p : Scalar) : Mat →ₗ[ℂ] Mat where
  toFun a i j := p*a i j
  map_add' a b := by ext i j t; change p t*(a i j t+b i j t)=p t*a i j t+p t*b i j t; ring
  map_smul' c a := by ext i j t; change p t*(c*a i j t)=c*(p t*a i j t); ring


-- @@ L75-83 verbatim
lemma times_mul (p q : Scalar) (a b : Mat) : times p a*times q b=times (p*q) (a*b) := by
  ext i j t
  change ((∑ k, (p * a i k) * (q * b k j)) : Scalar) t =
    ((p * q) * (∑ k, a i k * b k j)) t
  simp only [ContinuousMap.mul_apply, ContinuousMap.sum_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring


-- @@ L85-86 verbatim
lemma mul_times (p : Scalar) (a b : Mat) : a*times p b=times p (a*b) := by
  simpa only [one_mul,show times 1 a=a from by ext i j; exact one_mul _] using times_mul 1 p a b


-- @@ L88-89 verbatim
lemma times_mul_left (p : Scalar) (a b : Mat) : times p a*b=times p (a*b) := by
  simpa only [mul_one,show times 1 b=b from by ext i j; exact one_mul _] using times_mul p 1 a b


-- @@ L91-92 verbatim
lemma times_times (p q : Scalar) (a : Mat) : times p (times q a)=times (p*q) a := by
  ext i j; exact (mul_assoc _ _ _).symm


-- @@ L94-94 verbatim
def leftPart : Small2 →ₗ[ℂ] Mat := (times (1-coord)).comp leftConst.toLinearMap

-- @@ L95-95 verbatim
def rightPart : Small3 →ₗ[ℂ] Mat := (times coord).comp rightConst.toLinearMap



-- @@ L98-101 verbatim
def endLeft : DimensionDrop23 →ₗ[ℂ] Small2 where
  toFun f i j := entries f.val (i,0) (j,0) 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


-- @@ L103-106 verbatim
def endRight : DimensionDrop23 →ₗ[ℂ] Small3 where
  toFun f i j := entries f.val (0,i) (0,j) 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


-- @@ L108-119 verbatim
lemma at_zero (f : DimensionDrop23) (i j : Ix) :
    entries f.val i j 0 = leftMatrixAlgebra (endLeft f) i j := by
  obtain ⟨a,ha⟩ := f.property.1
  change leftMatrix a = f.val 0 at ha
  have he : endLeft f = CStarMatrix.ofMatrixL.symm a := by
    ext u v
    change CStarMatrix.ofMatrixL.symm (f.val 0) (u,0) (v,0) = _
    rw [← ha]
    change (CStarMatrix.ofMatrixL.symm a u v)*(1:ℂ)=_
    exact mul_one _
  rw [he,entries_apply,← ha]
  rfl


-- @@ L121-132 verbatim
lemma at_one (f : DimensionDrop23) (i j : Ix) :
    entries f.val i j 1 = rightMatrixAlgebra (endRight f) i j := by
  obtain ⟨a,ha⟩ := f.property.2
  change rightMatrix a = f.val 1 at ha
  have he : endRight f = CStarMatrix.ofMatrixL.symm a := by
    ext u v
    change CStarMatrix.ofMatrixL.symm (f.val 1) (0,u) (0,v) = _
    rw [← ha]
    change (1:ℂ)*(CStarMatrix.ofMatrixL.symm a u v)=_
    exact one_mul _
  rw [he,entries_apply,← ha]
  rfl




-- @@ L136-136 verbatim
def weight : Scalar := (1-coord)*coord

-- @@ L137-137 verbatim
abbrev InteriorScalar := Vanish.Functions {t | weight t=0}

-- @@ L138-138 verbatim
abbrev Interior := Matrix Ix Ix InteriorScalar


-- @@ L140-154 verbatim
omit instSize in
lemma weight_zero
    [KirchbergRordam.GenericRW.Size]
    (t : unitInterval) : weight t=0 ↔ t=0 ∨ t=1 := by
  change (1-(t:ℝ):ℂ)*(t:ℝ)=0 ↔ _
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h|h
    · right
      apply Subtype.ext
      exact_mod_cast (sub_eq_zero.mp h).symm
    · left
      apply Subtype.ext
      exact_mod_cast h
  · rintro (rfl|rfl) <;> simp



-- @@ L157-160 verbatim
def embed : Interior →ₗ[ℂ] Mat where
  toFun m i j := m i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


-- @@ L162-166 verbatim
lemma embed_injective : Function.Injective embed := by
  intro a b h
  funext i j
  apply Subtype.ext
  exact congr_fun (congr_fun h i) j


-- @@ L168-172 verbatim
lemma embed_mul (m n : Interior) : embed (m*n)=embed m*embed n := by
  ext i j t
  change ((∑ k, m i k*n k j : InteriorScalar) : Scalar) t =
    (∑ k, (m i k : Scalar)*(n k j : Scalar)) t
  simp


-- @@ L174-174 verbatim
lemma embed_star (m : Interior) : embed (star m)=star (embed m) := rfl


-- @@ L176-177 verbatim
lemma interior_at_zero (m : Interior) (i j : Ix) : embed m i j 0 = 0 :=
  (m i j).property 0 ((weight_zero 0).mpr (Or.inl rfl))


-- @@ L179-180 verbatim
lemma interior_at_one (m : Interior) (i j : Ix) : embed m i j 1 = 0 :=
  (m i j).property 1 ((weight_zero 1).mpr (Or.inr rfl))


-- @@ L182-184 verbatim
def residual : DimensionDrop23 →ₗ[ℂ] Mat :=
  entries.toLinearMap.comp dimensionDropSubalgebra.subtype.toLinearMap -
    leftPart.comp endLeft - rightPart.comp endRight



-- @@ L187-204 verbatim
def interior : DimensionDrop23 →ₗ[ℂ] Interior where
  toFun f i j := ⟨residual f i j, by
    intro t ht
    rcases (weight_zero t).mp ht with rfl|rfl
    · change entries f.val i j 0 - (1-coord 0)*leftMatrixAlgebra (endLeft f) i j -
        coord 0*rightMatrixAlgebra (endRight f) i j = 0
      simp [at_zero]
    · change entries f.val i j 1 - (1-coord 1)*leftMatrixAlgebra (endLeft f) i j -
        coord 1*rightMatrixAlgebra (endRight f) i j = 0
      simp [at_one]⟩
  map_add' f g := by
    funext i j
    apply Subtype.ext
    exact congr_fun (congr_fun (map_add residual f g) i) j
  map_smul' c f := by
    funext i j
    apply Subtype.ext
    exact congr_fun (congr_fun (map_smul residual c f) i) j


-- @@ L206-210 verbatim
lemma decomposition (f : DimensionDrop23) :
    entries f.val = leftPart (endLeft f)+rightPart (endRight f)+embed (interior f) := by
  change entries f.val = leftPart (endLeft f)+rightPart (endRight f)+
    (entries f.val-leftPart (endLeft f)-rightPart (endRight f))
  abel




-- @@ L214-217 verbatim
lemma endLeft_mul (f g : DimensionDrop23) : endLeft (f*g)=endLeft f*endLeft g := by
  ext i j
  change ∑ u : Ix, entries f.val (i,0) u 0*entries g.val u (j,0) 0 = _
  simp [at_zero,leftMatrixAlgebra,Fintype.sum_prod_type,Matrix.mul_apply,Matrix.one_apply]


-- @@ L219-222 verbatim
lemma endRight_mul (f g : DimensionDrop23) : endRight (f*g)=endRight f*endRight g := by
  ext i j
  change ∑ u : Ix, entries f.val (0,i) u 1*entries g.val u (0,j) 1 = _
  simp [at_one,rightMatrixAlgebra,Fintype.sum_prod_type,Matrix.mul_apply,Matrix.one_apply]


-- @@ L224-227 verbatim
lemma endLeft_one : endLeft 1=1 := by
  ext i j
  change (1 : M6) (i,0) (j,0) = (1 : Small2) i j
  simp [CStarMatrix.one_apply,Matrix.one_apply]


-- @@ L229-232 verbatim
lemma endRight_one : endRight 1=1 := by
  ext i j
  change (1 : M6) (0,i) (0,j) = (1 : Small3) i j
  simp [CStarMatrix.one_apply,Matrix.one_apply]


-- @@ L234-234 verbatim
lemma endLeft_star (f : DimensionDrop23) : endLeft (star f)=star (endLeft f) := rfl

-- @@ L235-235 verbatim
lemma endRight_star (f : DimensionDrop23) : endRight (star f)=star (endRight f) := rfl


-- @@ L237-240 verbatim
lemma times_star (p : Scalar) (m : Mat) : star (times p m)=times (star p) (star m) := by
  ext i j t
  change star (p t*m j i t)=star (p t)*star (m j i t)
  rw [star_mul,mul_comm]


-- @@ L242-246 verbatim
lemma leftPart_star (a : Small2) : leftPart (star a)=star (leftPart a) := by
  change times (1-coord) (leftConst (star a))=star (times (1-coord) (leftConst a))
  rw [times_star,map_star]
  have hc : star coord=coord := by ext t; simp [coord]
  rw [star_sub,star_one,hc]


-- @@ L248-252 verbatim
lemma rightPart_star (a : Small3) : rightPart (star a)=star (rightPart a) := by
  change times coord (rightConst (star a))=star (times coord (rightConst a))
  rw [times_star,map_star]
  have hc : star coord=coord := by ext t; simp [coord]
  rw [hc]


-- @@ L254-258 verbatim
lemma interior_star (f : DimensionDrop23) : interior (star f)=star (interior f) := by
  apply embed_injective
  change entries (star f.val)-leftPart (endLeft (star f))-rightPart (endRight (star f)) =
    star (entries f.val-leftPart (endLeft f)-rightPart (endRight f))
  rw [map_star,endLeft_star,endRight_star,leftPart_star,rightPart_star,star_sub,star_sub]


-- @@ L260-269 verbatim
lemma interior_one : interior 1=0 := by
  apply embed_injective
  change entries 1-leftPart (endLeft 1)-rightPart (endRight 1)=0
  simp only [show entries 1=1 from entries.map_one',endLeft_one,endRight_one]
  change 1-times (1-coord) (leftConst 1)-times coord (rightConst 1)=0
  rw [show leftConst 1=1 from leftConst.map_one',show rightConst 1=1 from rightConst.map_one']
  ext i j t
  change (1:Mat) i j t-((1-coord)* (1:Mat) i j) t-(coord*(1:Mat) i j) t=0
  simp only [ContinuousMap.mul_apply,ContinuousMap.sub_apply,ContinuousMap.one_apply]
  ring



-- @@ L272-272 verbatim
local instance : SMul ℂ InteriorScalar := (NonUnitalStarSubalgebra.instModule InteriorScalar).toSMul


-- @@ L274-277 verbatim
def weighted : Matrix Ix Ix ℂ →ₗ[ℂ] Interior where
  toFun m u v := Vanish.multiplier weight (ContinuousMap.const _ (m u v))
  map_add' m n := by ext u v t; change weight t*(m u v+n u v)=weight t*m u v+weight t*n u v; ring
  map_smul' z m := by ext u v t; change weight t*(z*m u v)=z*(weight t*m u v); ring


-- @@ L279-279 verbatim
lemma embed_weighted (m : Matrix Ix Ix ℂ) : embed (weighted m)=times weight (constMat m) := rfl


-- @@ L281-282 verbatim
def scalarMul (p : Scalar) (f : InteriorScalar) : InteriorScalar :=
  ⟨p*f.val,by intro t ht; simp [f.property t ht]⟩


-- @@ L284-285 verbatim
def actionLeft (a : Small2) (m : Interior) : Interior :=
  fun u v => ∑ j, (a u.1 j) • scalarMul (1-coord) (m (j,u.2) v)


-- @@ L287-288 verbatim
def actionRight (a : Small3) (m : Interior) : Interior :=
  fun u v => ∑ j, (a u.2 j) • scalarMul coord (m (u.1,j) v)


-- @@ L290-296 verbatim
lemma embed_actionLeft (a : Small2) (m : Interior) :
    embed (actionLeft a m)=leftPart a*embed m := by
  ext u v t
  change ((∑ j, (a u.1 j) • scalarMul (1-coord) (m (j,u.2) v) : InteriorScalar) : Scalar) t =
    ((∑ k : Ix, ((1-coord) * ContinuousMap.const _ (a u.1 k.1 * (1 : Small3) u.2 k.2)) *
      (m k v).val) : Scalar) t
  simp [scalarMul, Fintype.sum_prod_type, Matrix.one_apply, mul_left_comm, mul_comm]


-- @@ L298-305 verbatim
lemma embed_actionRight (a : Small3) (m : Interior) :
    embed (actionRight a m)=rightPart a*embed m := by
  ext u v t
  change ((∑ j, (a u.2 j) • scalarMul coord (m (u.1,j) v) : InteriorScalar) : Scalar) t =
    ((∑ k : Ix, (coord * ContinuousMap.const _ ((1 : Small2) u.1 k.1 * a u.2 k.2)) *
      (m k v).val) : Scalar) t
  rcases u with ⟨u1,u2⟩
  simp [scalarMul, Fintype.sum_prod_type, Matrix.one_apply, mul_left_comm, mul_comm]


-- @@ L307-307 verbatim
def actionLeftRev (m : Interior) (a : Small2) : Interior := star (actionLeft (star a) (star m))

-- @@ L308-308 verbatim
def actionRightRev (m : Interior) (a : Small3) : Interior := star (actionRight (star a) (star m))


-- @@ L310-313 verbatim
lemma embed_actionLeftRev (m : Interior) (a : Small2) :
    embed (actionLeftRev m a)=embed m*leftPart a := by
  rw [actionLeftRev,embed_star,embed_actionLeft,embed_star,leftPart_star]
  exact (star_mul (star (leftPart a)) (star (embed m))).trans (by rw [star_star,star_star])


-- @@ L315-318 verbatim
lemma embed_actionRightRev (m : Interior) (a : Small3) :
    embed (actionRightRev m a)=embed m*rightPart a := by
  rw [actionRightRev,embed_star,embed_actionRight,embed_star,rightPart_star]
  exact (star_mul (star (rightPart a)) (star (embed m))).trans (by rw [star_star,star_star])


-- @@ L320-328 verbatim
lemma leftPart_mul (a c : Small2) :
    leftPart a*leftPart c=leftPart (a*c)-embed (weighted ((a*c) ⊗ₖ (1:Small3))) := by
  change times (1-coord) (leftConst a)*times (1-coord) (leftConst c)=
    times (1-coord) (leftConst (a*c))-times weight (constMat ((a*c) ⊗ₖ (1:Small3)))
  rw [times_mul,← map_mul]
  ext i j t
  change ((1-coord t)*(1-coord t))*leftMatrixAlgebra (a*c) i j =
    (1-coord t)*leftMatrixAlgebra (a*c) i j-((1-coord t)*coord t)*leftMatrixAlgebra (a*c) i j
  ring


-- @@ L330-338 verbatim
lemma rightPart_mul (b d : Small3) :
    rightPart b*rightPart d=rightPart (b*d)-embed (weighted ((1:Small2) ⊗ₖ (b*d))) := by
  change times coord (rightConst b)*times coord (rightConst d)=
    times coord (rightConst (b*d))-times weight (constMat ((1:Small2) ⊗ₖ (b*d)))
  rw [times_mul,← map_mul]
  ext i j t
  change (coord t*coord t)*rightMatrixAlgebra (b*d) i j =
    coord t*rightMatrixAlgebra (b*d) i j-((1-coord t)*coord t)*rightMatrixAlgebra (b*d) i j
  ring


-- @@ L340-343 verbatim
lemma leftConst_rightConst (a : Small2) (b : Small3) :
    leftConst a*rightConst b=constMat (a ⊗ₖ b) := by
  change constMat (a ⊗ₖ (1:Small3))*constMat ((1:Small2) ⊗ₖ b)=_
  rw [← map_mul,← Matrix.mul_kronecker_mul,mul_one,one_mul]


-- @@ L345-348 verbatim
lemma rightConst_leftConst (a : Small2) (b : Small3) :
    rightConst b*leftConst a=constMat (a ⊗ₖ b) := by
  change constMat ((1:Small2) ⊗ₖ b)*constMat (a ⊗ₖ (1:Small3))=_
  rw [← map_mul,← Matrix.mul_kronecker_mul,mul_one,one_mul]


-- @@ L350-354 verbatim
lemma leftPart_rightPart (a : Small2) (b : Small3) :
    leftPart a*rightPart b=embed (weighted (a ⊗ₖ b)) := by
  change times (1-coord) (leftConst a)*times coord (rightConst b)=times weight (constMat (a ⊗ₖ b))
  rw [times_mul,leftConst_rightConst]
  rfl


-- @@ L356-360 verbatim
lemma rightPart_leftPart (a : Small2) (b : Small3) :
    rightPart b*leftPart a=embed (weighted (a ⊗ₖ b)) := by
  change times coord (rightConst b)*times (1-coord) (leftConst a)=times weight (constMat (a ⊗ₖ b))
  rw [times_mul,rightConst_leftConst,mul_comm coord]
  rfl



-- @@ L363-377 verbatim
lemma interior_mul (f g : DimensionDrop23) :
    interior (f*g) = -weighted ((endLeft f*endLeft g) ⊗ₖ (1:Small3))-
      weighted ((1:Small2) ⊗ₖ (endRight f*endRight g))+
      weighted (endLeft f ⊗ₖ endRight g)+weighted (endLeft g ⊗ₖ endRight f)+
      actionLeft (endLeft f) (interior g)+actionRight (endRight f) (interior g)+
      actionLeftRev (interior f) (endLeft g)+actionRightRev (interior f) (endRight g)+
      interior f*interior g := by
  apply embed_injective
  change entries ((f*g).val)-leftPart (endLeft (f*g))-rightPart (endRight (f*g)) = _
  rw [show entries ((f*g).val)=entries f.val*entries g.val from entries.map_mul' f.val g.val,
    endLeft_mul,endRight_mul,decomposition f,decomposition g]
  simp only [map_add,map_sub,map_neg,embed_actionLeft,embed_actionRight,
    embed_actionLeftRev,embed_actionRightRev,embed_mul,mul_add,add_mul,
    leftPart_mul,rightPart_mul,leftPart_rightPart,rightPart_leftPart]
  abel


-- @@ L379-379 verbatim
end KirchbergRordam.GenericRW.DropSections

-- @@ L380-380 verbatim
end


-- @@ L382-382 verbatim
end OAI
