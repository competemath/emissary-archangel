import OAI.Analysis.CharacterCriterion.ConeModel


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
namespace KirchbergRordam.GenericRW.FlipPath

-- @@ L24-24 verbatim
open scoped BigOperators


-- @@ L26-26 verbatim
abbrev M2 := Matrix (Fin rankNum) (Fin rankNum) ℂ

-- @@ L27-27 verbatim
abbrev M4 := Matrix (Fin rankNum × Fin rankNum) (Fin rankNum × Fin rankNum) ℂ


-- @@ L29-29 verbatim
def flip : M4 := fun i j => if i.1=j.2 ∧ i.2=j.1 then 1 else 0


-- @@ L31-34 verbatim
lemma flip_star : star flip=flip := by
  ext i j
  simp only [Matrix.star_apply,flip]
  split_ifs <;> simp_all


-- @@ L36-39 verbatim
lemma flip_mul : flip*flip=1 := by
  ext ⟨i,j⟩ ⟨k,l⟩
  simp only [Matrix.mul_apply,flip,Fintype.sum_prod_type]
  simp [Matrix.one_apply,Prod.mk.injEq,ite_and]


-- @@ L41-41 verbatim
def left (a : M2) : M4 := fun i j => a i.1 j.1 * if i.2=j.2 then 1 else 0

-- @@ L42-42 verbatim
def right (a : M2) : M4 := fun i j => (if i.1=j.1 then 1 else 0) * a i.2 j.2


-- @@ L44-47 verbatim
lemma flip_exchange (a : M2) : right a*flip=flip*left a := by
  ext ⟨i,j⟩ ⟨k,l⟩
  simp only [Matrix.mul_apply,Fintype.sum_prod_type,left,right,flip]
  simp [ite_and,mul_ite,ite_mul,eq_comm]



-- @@ L50-50 verbatim
def angle : C(unitInterval,ℝ) := ⟨fun t => min (max (3*(t:ℝ)-1) 0) 1,by fun_prop⟩


-- @@ L52-53 verbatim
def phase : C(unitInterval,ℂ) :=
  ⟨fun t => Complex.exp (((Real.pi*angle t : ℝ):ℂ)*Complex.I),by fun_prop⟩


-- @@ L55-58 verbatim
omit instSize in
lemma phase_zero
    [KirchbergRordam.GenericRW.Size]
    : phase 0=1 := by simp [phase,angle]

-- @@ L59-64 verbatim
omit instSize in
lemma phase_top
    [KirchbergRordam.GenericRW.Size]
    {t : unitInterval} (ht : 2/3 ≤ (t:ℝ)) : phase t= -1 := by
  have h : angle t=1 := by change min (max (3*(t:ℝ)-1) 0) 1=1; rw [min_eq_right]; exact le_max_of_le_left (by linarith)
  simp [phase,h,Complex.exp_pi_mul_I]


-- @@ L66-72 verbatim
omit instSize in
lemma phase_unitary
    [KirchbergRordam.GenericRW.Size]
    (t : unitInterval) : star (phase t)*phase t=1 := by
  have hn : ‖phase t‖=1 := Complex.norm_exp_ofReal_mul_I _
  rw [Complex.star_def,← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq,hn]
  norm_num



-- @@ L75-75 verbatim
def path (t : unitInterval) : M4 := ((1+phase t)/2) • (1:M4)+((1-phase t)/2) • flip


-- @@ L77-77 verbatim
lemma path_zero : path 0=1 := by simp [path,phase_zero]

-- @@ L78-78 verbatim
lemma path_top {t : unitInterval} (ht : 2/3 ≤ (t:ℝ)) : path t=flip := by simp [path,phase_top ht]


-- @@ L80-80 verbatim
lemma path_continuous : Continuous path := by unfold path; fun_prop


-- @@ L82-101 verbatim
lemma path_star_mul (t : unitInterval) : star (path t)*path t=1 := by
  have hz := phase_unitary t
  have hs : star (2:ℂ)=2 := by simp
  simp only [path,star_add,star_smul,star_one,flip_star,star_div₀,hs,star_add,star_sub,
    smul_add,add_mul,mul_add,smul_mul_assoc,mul_smul_comm,smul_smul,one_mul,mul_one,flip_mul]
  have h1 : (star ((1:ℂ)+phase t)/2)*((1+phase t)/2)+
      (star ((1:ℂ)-phase t)/2)*((1-phase t)/2)=1 := by
    simp only [star_add,star_sub,star_one]; calc
      _=(1+star (phase t)*phase t)/2 := by ring
      _=1 := by rw [hz]; norm_num
  have h2 : (star ((1:ℂ)+phase t)/2)*((1-phase t)/2)+
      (star ((1:ℂ)-phase t)/2)*((1+phase t)/2)=0 := by
    simp only [star_add,star_sub,star_one]; calc
      _=(1-star (phase t)*phase t)/2 := by ring
      _=0 := by rw [hz]; norm_num
  calc
    _=(((1+star (phase t))/2)*((1+phase t)/2)+((1-star (phase t))/2)*((1-phase t)/2)) • (1:M4)+
      (((1+star (phase t))/2)*((1-phase t)/2)+((1-star (phase t))/2)*((1+phase t)/2)) • flip := by
        rw [add_smul,add_smul]; module
    _=1 := by simp only [star_add,star_sub,star_one] at h1 h2; rw [h1,h2,one_smul,zero_smul,add_zero]


-- @@ L103-104 verbatim
lemma path_mul_star (t : unitInterval) : path t*star (path t)=1 := by
  exact mul_eq_one_comm.mp (path_star_mul t)




-- @@ L108-126 verbatim
def block : M4 →+* Matrix (Fin rankNum) (Fin rankNum) ConeModel.M2 where
  toFun m j k := CStarMatrix.ofMatrix (fun r s => m (r,j) (s,k))
  map_zero' := rfl
  map_add' _ _ := rfl
  map_one' := by
    ext j k r s
    change (if (r,j)=(s,k) then (1:ℂ) else 0)=((1 : Matrix (Fin rankNum) (Fin rankNum) ConeModel.M2) j k) r s
    by_cases hjk : j=k
    · subst k; simp [Prod.mk.injEq,CStarMatrix.one_apply]
    · simp [hjk,Prod.mk.injEq,CStarMatrix.zero_apply]
  map_mul' m n := by
    ext j k r s
    change (∑ u : Fin rankNum × Fin rankNum,m (r,j) u*n u (s,k))=
      ((∑ l : Fin rankNum,(CStarMatrix.ofMatrix (fun r s => m (r,j) (s,l)))*
        (CStarMatrix.ofMatrix (fun r s => n (r,l) (s,k)))) r s)
    simp only [Fintype.sum_prod_type, ConeModel.matrixSum_entry, CStarMatrix.mul_apply]
    change (∑ a : Fin rankNum, ∑ b : Fin rankNum, m (r,j) (a,b) * n (a,b) (s,k)) =
      ∑ b : Fin rankNum, ∑ a : Fin rankNum, m (r,j) (a,b) * n (a,b) (s,k)
    exact Finset.sum_comm


-- @@ L128-128 verbatim
lemma block_star (m : M4) : block (star m)=star (block m) := rfl



-- @@ L131-140 verbatim
def conePath (j k : Fin rankNum) : ConeModel.Cone :=
  ⟨⟨fun t => block (path t) j k,by
      change Continuous (fun t : unitInterval => (fun r s => path t (r,j) (s,k)))
      exact continuous_pi fun r => continuous_pi fun s =>
        (continuous_apply (s,k)).comp ((continuous_apply (r,j)).comp path_continuous)⟩,by
    change block (path 0) j k ∈ (⊥ : StarSubalgebra ℂ ConeModel.M2)
    rw [path_zero,map_one,Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _⟩


-- @@ L142-153 verbatim
lemma conePath_star_mul (i j : Fin rankNum) :
    ∑ k,star (conePath k i)*conePath k j=if i=j then 1 else 0 := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  have h := congrArg (fun m => block m i j) (path_star_mul t)
  rw [map_mul,block_star,map_one] at h
  simp only [Matrix.mul_apply,Matrix.star_apply,Matrix.one_apply] at h
  rw [ConeModel.evaluate_sum]
  by_cases hij : i=j
  · rw [ite_eq_left hij] at h ⊢; exact h
  · rw [ite_eq_right hij] at h ⊢; exact h


-- @@ L155-166 verbatim
lemma conePath_mul_star (i j : Fin rankNum) :
    ∑ k,conePath i k*star (conePath j k)=if i=j then 1 else 0 := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  have h := congrArg (fun m => block m i j) (path_mul_star t)
  rw [map_mul,block_star,map_one] at h
  simp only [Matrix.mul_apply,Matrix.star_apply,Matrix.one_apply] at h
  rw [ConeModel.evaluate_sum]
  by_cases hij : i=j
  · rw [ite_eq_left hij] at h ⊢; exact h
  · rw [ite_eq_right hij] at h ⊢; exact h


-- @@ L168-168 verbatim
end KirchbergRordam.GenericRW.FlipPath


-- @@ L170-170 verbatim
namespace KirchbergRordam.GenericRW.RWFunctions


-- @@ L172-172 verbatim
def realG : C(unitInterval,ℝ) := ⟨fun t => min 1 (3*(1-(t:ℝ))),by fun_prop⟩

-- @@ L173-173 verbatim
def g : C(unitInterval,ℂ) := ⟨fun t => (realG t : ℂ),by fun_prop⟩

-- @@ L174-174 verbatim
def q : C(unitInterval,ℂ) := ⟨fun t => (Real.sqrt (realG t) : ℂ),by fun_prop⟩


-- @@ L176-177 verbatim
def realJ : C(unitInterval,ℝ) := ⟨fun t => (max (t:ℝ) (2/3))⁻¹,
  Continuous.inv₀ (by fun_prop) (fun _ => ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<2/3) (le_max_right _ _)))⟩

-- @@ L178-178 verbatim
def j : C(unitInterval,ℂ) := ⟨fun t => (realJ t : ℂ),by fun_prop⟩


-- @@ L180-183 verbatim
omit instSize in
lemma g_nonneg
    [KirchbergRordam.GenericRW.Size]
    (t : unitInterval) : 0≤realG t := le_min (by norm_num) (mul_nonneg (by norm_num) (sub_nonneg.mpr t.property.2))

-- @@ L184-187 verbatim
omit instSize in
lemma g_le_one
    [KirchbergRordam.GenericRW.Size]
    (t : unitInterval) : realG t≤1 := min_le_left _ _

-- @@ L188-194 verbatim
omit instSize in
lemma g_ge_defect
    [KirchbergRordam.GenericRW.Size]
    (t : unitInterval) : 1-(t:ℝ)≤realG t := by
  apply le_min
  · linarith [t.property.1]
  · linarith [t.property.2]


-- @@ L196-199 verbatim
omit instSize in
@[simp] lemma g_zero
    [KirchbergRordam.GenericRW.Size]
    : g 0=1 := by norm_num [g,realG]

-- @@ L200-203 verbatim
omit instSize in
@[simp] lemma g_one
    [KirchbergRordam.GenericRW.Size]
    : g 1=0 := by norm_num [g,realG]

-- @@ L204-207 verbatim
omit instSize in
@[simp] lemma q_one
    [KirchbergRordam.GenericRW.Size]
    : q 1=0 := by norm_num [q,realG]

-- @@ L208-211 verbatim
omit instSize in
@[simp] lemma j_one
    [KirchbergRordam.GenericRW.Size]
    : j 1=1 := by norm_num [j,realJ]


-- @@ L213-218 verbatim
omit instSize in
lemma g_low
    [KirchbergRordam.GenericRW.Size]
    {t : unitInterval} (ht : (t:ℝ)≤2/3) : g t=1 := by
  have h : realG t=1 := min_eq_left (by linarith)
  simp [g,h]


-- @@ L220-225 verbatim
lemma g_norm : ‖g‖≤1 := by
  apply (ContinuousMap.norm_le _ (by norm_num)).mpr
  intro t
  change ‖(realG t : ℂ)‖≤1
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (g_nonneg t)]
  exact g_le_one t


-- @@ L227-230 verbatim
omit instSize in
lemma q_star
    [KirchbergRordam.GenericRW.Size]
    : star q=q := by ext t; exact Complex.conj_ofReal _

-- @@ L231-234 verbatim
omit instSize in
lemma g_star
    [KirchbergRordam.GenericRW.Size]
    : star g=g := by ext t; exact Complex.conj_ofReal _

-- @@ L235-238 verbatim
omit instSize in
lemma j_star
    [KirchbergRordam.GenericRW.Size]
    : star j=j := by ext t; exact Complex.conj_ofReal _

-- @@ L239-242 verbatim
lemma q_sq : q*q=g := by
  ext t
  change ((Real.sqrt (realG t):ℝ):ℂ)*((Real.sqrt (realG t):ℝ):ℂ)=(realG t:ℂ)
  rw [← Complex.ofReal_mul,Real.mul_self_sqrt (g_nonneg t)]



-- @@ L245-252 verbatim
lemma residual_inverse (t : unitInterval) :
    (1-g t)*j t*((t:ℝ):ℂ)=1-g t := by
  by_cases ht : (t:ℝ)≤2/3
  · rw [g_low ht]; simp
  · have hp : (0:ℝ)<t := lt_trans (by norm_num) (lt_of_not_ge ht)
    have he : realJ t=(t:ℝ)⁻¹ := max_eq_left (le_of_lt (lt_of_not_ge ht)) ▸ rfl
    change (1-g t)*(realJ t : ℂ)*((t:ℝ):ℂ)=_
    rw [he,mul_assoc,← Complex.ofReal_mul,inv_mul_cancel₀ (ne_of_gt hp),Complex.ofReal_one,mul_one]



-- @@ L255-256 verbatim
lemma overlap_zero {t : unitInterval} (ht : ¬ (2/3:ℝ)≤t) : g t*(1-g t)=0 := by
  rw [g_low (le_of_lt (lt_of_not_ge ht))]; simp


-- @@ L258-258 verbatim
end KirchbergRordam.GenericRW.RWFunctions

-- @@ L259-259 verbatim
namespace KirchbergRordam.GenericRW.ConeModel

-- @@ L260-264 verbatim
lemma scalar_commute (f : C(unitInterval,ℂ)) (x : Cone) : Commute (scalar f) x := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  exact Algebra.commutes (f t) ((x:C(unitInterval,M2)) t)

-- @@ L265-265 verbatim
end KirchbergRordam.GenericRW.ConeModel


-- @@ L267-267 verbatim
namespace KirchbergRordam.GenericRW.FlipPath

-- @@ L268-268 verbatim
open scoped BigOperators

-- @@ L269-269 verbatim
open ConeModel RWFunctions


-- @@ L271-271 verbatim
def flatK (i j : Fin rankNum) : Cone := scalar q*star (conePath j i)


-- @@ L273-275 verbatim
def weightedK : Matrix (Fin rankNum) (Fin rankNum) Defect := fun i j => ⟨flatK i j,by
  change algebraMap ℂ ConeModel.M2 (q 1)*star ((conePath j i : C(unitInterval,ConeModel.M2)) 1)=0
  rw [q_one,map_zero,zero_mul]⟩


-- @@ L277-277 verbatim
def scalarG : Defect := scalarDefect g g_one


-- @@ L279-279 verbatim
def scalarQ : Defect := scalarDefect q q_one


-- @@ L281-284 verbatim
lemma scalarQ_star : star scalarQ=scalarQ := by
  apply Subtype.ext
  change star (scalar q)=scalar q
  rw [← map_star,q_star]


-- @@ L286-289 verbatim
lemma scalarQ_sq : scalarQ*scalarQ=scalarG := by
  apply Subtype.ext
  change scalar q*scalar q=scalar g
  rw [← map_mul,q_sq]


-- @@ L291-295 verbatim
lemma weighted_mul (x y : Cone) : (x*scalar q)*(scalar q*y)=scalar g*(x*y) := by
  calc
    _=x*(scalar q*scalar q)*y := by noncomm_ring
    _=x*scalar g*y := by rw [← map_mul,q_sq]
    _=_ := by rw [← (scalar_commute g x).eq]; noncomm_ring


-- @@ L297-299 verbatim
lemma weighted_mul' (x y : Cone) : (scalar q*x)*(y*scalar q)=scalar g*(x*y) := by
  rw [(scalar_commute q x).eq,← (scalar_commute q y).eq]
  exact weighted_mul x y


-- @@ L301-305 verbatim
lemma flatK_star_mul (i j : Fin rankNum) :
    ∑ k,star (flatK k i)*flatK k j=if i=j then scalar g else 0 := by
  simp only [flatK,star_mul,star_star,← map_star,q_star,weighted_mul]
  rw [← Finset.mul_sum,conePath_mul_star]
  split_ifs <;> simp


-- @@ L307-311 verbatim
lemma flatK_mul_star (i j : Fin rankNum) :
    ∑ k,flatK i k*star (flatK j k)=if i=j then scalar g else 0 := by
  simp only [flatK,star_mul,star_star,← map_star,q_star,weighted_mul']
  rw [← Finset.mul_sum,conePath_star_mul]
  split_ifs <;> simp


-- @@ L313-315 verbatim
lemma coe_defect_sum {ι : Type*} (s : Finset ι) (f : ι → Defect) :
    ((∑ i ∈ s, f i : Defect):Cone) = ∑ i ∈ s, (f i:Cone) :=
  map_sum (NonUnitalStarSubalgebraClass.subtype Defect) f s


-- @@ L317-327 verbatim
lemma weightedK_star_mul :
    (star weightedK*weightedK : Matrix (Fin rankNum) (Fin rankNum) Defect) =
      Matrix.diagonal (fun _ => scalarG) := by
  apply Matrix.ext; intro i j
  apply Subtype.ext
  have h := flatK_star_mul i j
  simp only [Matrix.mul_apply,Matrix.star_apply,Matrix.diagonal_apply]
  rw [coe_defect_sum]
  by_cases hij : i=j
  · rw [ite_eq_left hij] at h ⊢; exact h
  · rw [ite_eq_right hij] at h ⊢; exact h


-- @@ L329-339 verbatim
lemma weightedK_mul_star :
    (weightedK*star weightedK : Matrix (Fin rankNum) (Fin rankNum) Defect) =
      Matrix.diagonal (fun _ => scalarG) := by
  apply Matrix.ext; intro i j
  apply Subtype.ext
  have h := flatK_mul_star i j
  simp only [Matrix.mul_apply,Matrix.star_apply,Matrix.diagonal_apply]
  rw [coe_defect_sum]
  by_cases hij : i=j
  · rw [ite_eq_left hij] at h ⊢; exact h
  · rw [ite_eq_right hij] at h ⊢; exact h


-- @@ L341-341 verbatim
end KirchbergRordam.GenericRW.FlipPath

-- @@ L342-342 verbatim
end


-- @@ L344-344 verbatim
end OAI
