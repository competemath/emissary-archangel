import OAI.Analysis.CharacterCriterion.ConeCube


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
namespace KirchbergRordam.GenericRW.MatrixMix

-- @@ L25-25 verbatim
open scoped BigOperators

-- @@ L26-26 verbatim
variable {A : Type*} [CStarAlgebra A]

-- @@ L27-27 verbatim
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

-- @@ L28-28 verbatim
abbrev Mat (ι : Type*) := Matrix ι ι ℂ

-- @@ L29-29 verbatim
def e (i j : ι) : Mat ι := Matrix.single i j 1

-- @@ L30-39 verbatim
omit [Fintype ι] in
omit instSize instPauliData in
lemma e_star.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {ι : Type contextLevel1}
    [DecidableEq ι]
    (i j : ι) : star (e i j)=e j i := by
  change (Matrix.single i j (1:ℂ)).conjTranspose=_
  simp [Matrix.conjTranspose_single,e]

-- @@ L40-50 verbatim
omit instSize instPauliData in
lemma e_mul.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {ι : Type contextLevel1}
    [Fintype ι]
    [DecidableEq ι]
    (i j k l : ι) : e i j*e k l=if j=k then e i l else 0 := by
  by_cases h : j=k
  · subst k; simp [e]
  · simp [e,h]

-- @@ L51-60 verbatim
omit instSize instPauliData in
lemma e_sum.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {ι : Type contextLevel1}
    [Fintype ι]
    [DecidableEq ι]
    : ∑ i : ι,e i i=1 := by
  ext i j
  simp [e,Matrix.sum_apply,Matrix.single_apply,Matrix.one_apply,ite_and]


-- @@ L62-62 verbatim
variable (φ : Mat ι →⋆ₐ[ℂ] A) (ψ : Mat κ →⋆ₐ[ℂ] A)

-- @@ L63-63 verbatim
variable (hc : ∀ a b,Commute (φ a) (ψ b))

-- @@ L64-64 verbatim
def x (i j : ι×κ) : A := φ (e i.1 j.1)*ψ (e i.2 j.2)

-- @@ L65-68 verbatim
include hc in
lemma x_star (i j : ι×κ) : star (x φ ψ i j)=x φ ψ j i := by
  simp only [x,star_mul,← map_star,e_star]
  exact (hc _ _).eq.symm

-- @@ L69-78 verbatim
include hc in
lemma x_mul (i j k l : ι×κ) : x φ ψ i j*x φ ψ k l=if j=k then x φ ψ i l else 0 := by
  unfold x
  calc
    _=φ (e i.1 j.1)*φ (e k.1 l.1)*(ψ (e i.2 j.2)*ψ (e k.2 l.2)) := by
      rw [mul_assoc,← mul_assoc (ψ _),← (hc _ _).eq]; noncomm_ring
    _=_ := by
      rw [← map_mul,← map_mul,e_mul,e_mul]
      by_cases h1 : j.1=k.1 <;> by_cases h2 : j.2=k.2 <;>
        simp [h1,h2,Prod.ext_iff]

-- @@ L79-80 verbatim
lemma x_sum : ∑ i : ι×κ,x φ ψ i i=1 := by
  simp only [x,Fintype.sum_prod_type,← Finset.mul_sum,← map_sum,e_sum,map_one,mul_one]


-- @@ L82-85 verbatim
def linear : Mat (ι×κ) →ₗ[ℂ] A where
  toFun a := ∑ i,∑ j,a i j • x φ ψ i j
  map_add' a b := by simp [add_smul,Finset.sum_add_distrib]
  map_smul' c a := by simp [Finset.smul_sum,smul_smul]

-- @@ L86-101 verbatim
omit instSize instPauliData in
lemma linear_single.{contextLevel1, contextLevel2, contextLevel3}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    {ι : Type contextLevel2}
    {κ : Type contextLevel3}
    [Fintype ι]
    [Fintype κ]
    [DecidableEq ι]
    [DecidableEq κ]
    (φ : KirchbergRordam.GenericRW.MatrixMix.Mat ι →⋆ₐ[ℂ] A)
    (ψ : KirchbergRordam.GenericRW.MatrixMix.Mat κ →⋆ₐ[ℂ] A)
    (i j : ι×κ) (z : ℂ) : linear φ ψ (Matrix.single i j z)=z • x φ ψ i j := by
  simp [linear,Matrix.single,ite_and]

-- @@ L102-102 verbatim
lemma linear_one : linear φ ψ 1=1 := by simpa [linear,Matrix.one_apply] using x_sum φ ψ

-- @@ L103-106 verbatim
include hc in
lemma linear_star (a : Mat (ι×κ)) : linear φ ψ (star a)=star (linear φ ψ a) := by
  simp only [linear,LinearMap.coe_mk,AddHom.coe_mk,star_sum,star_smul,x_star φ ψ hc]
  exact Finset.sum_comm

-- @@ L107-122 verbatim
include hc in
lemma linear_mul (a b : Mat (ι×κ)) : linear φ ψ (a*b)=linear φ ψ a*linear φ ψ b := by
  induction a using Matrix.induction_on' with
  | h_zero => simp
  | h_add a a' ha ha' => simp only [add_mul,map_add,ha,ha']
  | h_std_basis i j z =>
    induction b using Matrix.induction_on' with
    | h_zero => simp
    | h_add b b' hb hb' => simp only [mul_add,map_add,hb,hb']
    | h_std_basis k l w =>
      by_cases h : j=k
      · subst k
        rw [Matrix.single_mul_single_same,linear_single,linear_single,linear_single]
        simp [smul_smul,x_mul φ ψ hc,mul_comm]
      · rw [Matrix.single_mul_single_of_ne (h:=h)]
        simp [linear_single,x_mul φ ψ hc,h]


-- @@ L124-132 verbatim
def tensor : Mat (ι×κ) →⋆ₐ[ℂ] A where
  toFun := linear φ ψ
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one,map_smul,linear_one,Algebra.algebraMap_eq_smul_one]
  map_one' := linear_one φ ψ
  map_mul' := linear_mul φ ψ hc
  map_star' := linear_star φ ψ hc


-- @@ L134-151 verbatim
lemma tensor_kronecker (a : Mat ι) (b : Mat κ) :
    tensor φ ψ hc (Matrix.kronecker a b)=φ a*ψ b := by
  simp only [Matrix.kronecker]
  induction a using Matrix.induction_on' with
  | h_zero => simp
  | h_add a a' ha ha' => simp only [Matrix.add_kronecker,map_add,add_mul,ha,ha']
  | h_std_basis i j z =>
    induction b using Matrix.induction_on' with
    | h_zero => simp
    | h_add b b' hb hb' => simp only [Matrix.kronecker_add,map_add,mul_add,hb,hb']
    | h_std_basis k l w =>
      rw [Matrix.single_kronecker_single]
      change linear φ ψ (Matrix.single (i,k) (j,l) (z*w))=_
      rw [linear_single]
      have he (i j : ι) (z : ℂ) : Matrix.single i j z=z • e i j := by simp [e]
      have hf (i j : κ) (z : ℂ) : Matrix.single i j z=z • e i j := by simp [e]
      rw [he,hf,map_smul,map_smul,smul_mul_smul_comm]
      rfl


-- @@ L153-153 verbatim
variable {φ ψ}

-- @@ L154-157 verbatim
lemma tensor_mem (S : StarSubalgebra ℂ A) (hφ : ∀ a,φ a∈S) (hψ : ∀ b,ψ b∈S)
    (a : Mat (ι×κ)) : tensor φ ψ hc a∈S := by
  change (∑ i,∑ j,a i j • x φ ψ i j)∈S
  exact S.sum_mem fun i _ => S.sum_mem fun j _ => S.smul_mem (S.mul_mem (hφ _) (hψ _)) _

-- @@ L158-158 verbatim
end KirchbergRordam.GenericRW.MatrixMix



-- @@ L161-161 verbatim
namespace KirchbergRordam.GenericRW.MatrixMix

-- @@ L162-162 verbatim
open scoped BigOperators

-- @@ L163-163 verbatim
variable {A : Type*} [CStarAlgebra A]

-- @@ L164-164 verbatim
variable {ι κ X : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

-- @@ L165-165 verbatim
variable [TopologicalSpace X]

-- @@ L166-176 verbatim
lemma tensor_continuous (φ : X → Mat ι →⋆ₐ[ℂ] A) (ψ : X → Mat κ →⋆ₐ[ℂ] A)
    (hc : ∀ z a b,Commute (φ z a) (ψ z b))
    (hφ : ∀ a,Continuous fun z => φ z a) (hψ : ∀ b,Continuous fun z => ψ z b)
    (a : X → Mat (ι×κ)) (ha : Continuous a) :
    Continuous fun z => tensor (φ z) (ψ z) (hc z) (a z) := by
  change Continuous fun z => ∑ i,∑ j,a z i j • (φ z (e i.1 j.1)*ψ z (e i.2 j.2))
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact ((continuous_apply j).comp ((continuous_apply i).comp ha)).smul ((hφ _).mul (hψ _))


-- @@ L178-178 verbatim
variable (φ ψ : Mat (Fin Size.n) →⋆ₐ[ℂ] A) (hc : ∀ a b,Commute (φ a) (ψ b))

-- @@ L179-181 verbatim
lemma tensor_left (a : Mat (Fin Size.n)) : tensor φ ψ hc (FlipPath.left a)=φ a := by
  have he : FlipPath.left a=Matrix.kronecker a 1 := by ext i j; simp [FlipPath.left,Matrix.one_apply]
  rw [he,tensor_kronecker,map_one,mul_one]

-- @@ L182-184 verbatim
lemma tensor_right (a : Mat (Fin Size.n)) : tensor φ ψ hc (FlipPath.right a)=ψ a := by
  have he : FlipPath.right a=Matrix.kronecker 1 a := by ext i j; simp [FlipPath.right,Matrix.one_apply]
  rw [he,tensor_kronecker,map_one,one_mul]


-- @@ L186-186 verbatim
def u (t : unitInterval) : A := tensor φ ψ hc (FlipPath.path t)

-- @@ L187-188 verbatim
lemma u_star_mul (t : unitInterval) : star (u φ ψ hc t)*u φ ψ hc t=1 := by
  rw [u,← map_star,← map_mul,FlipPath.path_star_mul,map_one]

-- @@ L189-190 verbatim
lemma u_mul_star (t : unitInterval) : u φ ψ hc t*star (u φ ψ hc t)=1 := by
  rw [u,← map_star,← map_mul,FlipPath.path_mul_star,map_one]

-- @@ L191-191 verbatim
lemma u_zero : u φ ψ hc 0=1 := by rw [u,FlipPath.path_zero,map_one]


-- @@ L193-205 verbatim
def interpolate (t : unitInterval) : Mat (Fin Size.n) →⋆ₐ[ℂ] A where
  toFun a := u φ ψ hc t*φ a*star (u φ ψ hc t)
  map_zero' := by simp
  map_add' a b := by simp [mul_add,add_mul]
  map_one' := by rw [map_one,mul_one,u_mul_star]
  map_mul' a b := by
    rw [map_mul]
    calc
      _=u φ ψ hc t*φ a*(star (u φ ψ hc t)*u φ ψ hc t)*φ b*star (u φ ψ hc t) := by rw [u_star_mul]; noncomm_ring
      _=_ := by noncomm_ring
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one,map_smul,map_one,Algebra.algebraMap_eq_smul_one,mul_smul_comm,mul_one,smul_mul_assoc,u_mul_star]
  map_star' a := by rw [map_star,star_mul,star_mul,star_star]; noncomm_ring


-- @@ L207-209 verbatim
lemma interpolate_zero (a : Mat (Fin Size.n)) : interpolate φ ψ hc 0 a=φ a := by
  change u φ ψ hc 0*φ a*star (u φ ψ hc 0)=_
  rw [u_zero,star_one,one_mul,mul_one]

-- @@ L210-218 verbatim
lemma interpolate_top {t : unitInterval} (ht : 2/3≤(t:ℝ)) (a : Mat (Fin Size.n)) :
    interpolate φ ψ hc t a=ψ a := by
  calc
    _=tensor φ ψ hc (FlipPath.path t*FlipPath.left a*star (FlipPath.path t)) := by
      rw [map_mul,map_mul,map_star,tensor_left]; rfl
    _=tensor φ ψ hc (FlipPath.right a) := by
      congr 1
      rw [FlipPath.path_top ht,FlipPath.flip_star,← FlipPath.flip_exchange,mul_assoc,FlipPath.flip_mul,mul_one]
    _=_ := tensor_right φ ψ hc a


-- @@ L220-223 verbatim
lemma interpolate_mem (S : StarSubalgebra ℂ A) (hφ : ∀ a,φ a∈S) (hψ : ∀ b,ψ b∈S)
    (t : unitInterval) (a : Mat (Fin Size.n)) : interpolate φ ψ hc t a∈S := by
  have hu : u φ ψ hc t∈S := tensor_mem hc S hφ hψ _
  exact S.mul_mem (S.mul_mem hu (hφ a)) (S.star_mem' hu)


-- @@ L225-232 verbatim
lemma interpolate_continuous
    (φ ψ : X → Mat (Fin Size.n) →⋆ₐ[ℂ] A) (hc : ∀ z a b,Commute (φ z a) (ψ z b))
    (hφ : ∀ a,Continuous fun z => φ z a) (hψ : ∀ b,Continuous fun z => ψ z b)
    (t : X → unitInterval) (ht : Continuous t) (a : Mat (Fin Size.n)) :
    Continuous fun z => interpolate (φ z) (ψ z) (hc z) (t z) a := by
  have hu : Continuous fun z => u (φ z) (ψ z) (hc z) (t z) :=
    tensor_continuous φ ψ hc hφ hψ _ (FlipPath.path_continuous.comp ht)
  exact (hu.mul (hφ a)).mul hu.star

-- @@ L233-233 verbatim
end KirchbergRordam.GenericRW.MatrixMix

-- @@ L234-234 verbatim
namespace KirchbergRordam.GenericRW


-- @@ L236-237 verbatim
def CoordinateSimplex (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  {weights | (∀ index, 0 ≤ weights index) ∧ ∑ index, weights index = 1}


-- @@ L239-239 verbatim
namespace CoordinateSimplex


-- @@ L241-241 verbatim
variable {ι : Type*} [Fintype ι]


-- @@ L243-245 verbatim
instance : FunLike (CoordinateSimplex ι) ι ℝ where
  coe weights := weights.val
  coe_injective := Subtype.val_injective


-- @@ L247-255 verbatim
omit instSize instPauliData in
@[ext] lemma ext.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {ι : Type contextLevel1}
    [Fintype ι]
    {weights other : CoordinateSimplex ι}
    (heq : ∀ index, weights index = other index) : weights = other :=
  Subtype.ext (funext heq)


-- @@ L257-264 verbatim
omit instSize instPauliData in
@[simp] lemma zero_le.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {ι : Type contextLevel1}
    [Fintype ι]
    (weights : CoordinateSimplex ι) (index : ι) :
    0 ≤ weights index := weights.2.1 index


-- @@ L266-273 verbatim
omit instSize instPauliData in
@[simp] lemma sum_eq_one.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {ι : Type contextLevel1}
    [Fintype ι]
    (weights : CoordinateSimplex ι) :
    ∑ index, weights index = 1 := weights.2.2


-- @@ L275-277 verbatim
lemma le_one (weights : CoordinateSimplex ι) (index : ι) : weights index ≤ 1 := by
  rw [← sum_eq_one weights]
  exact Finset.single_le_sum (fun entry _ => zero_le weights entry) (Finset.mem_univ index)


-- @@ L279-285 verbatim
abbrev vertex [DecidableEq ι] (index : ι) : CoordinateSimplex ι :=
  ⟨Pi.single index 1, by
    constructor
    · intro entry
      simp only [Pi.single_apply]
      split_ifs <;> norm_num
    · simp⟩


-- @@ L287-294 verbatim
omit instSize instPauliData in
@[simp] lemma vertex_coe.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {ι : Type contextLevel1}
    [Fintype ι]
    [DecidableEq ι] (index : ι) :
    ⇑(vertex index) = Pi.single index 1 := rfl


-- @@ L296-296 verbatim
end CoordinateSimplex

-- @@ L297-297 verbatim
end KirchbergRordam.GenericRW

-- @@ L298-298 verbatim
namespace KirchbergRordam.GenericRW.MatrixSimplex

-- @@ L299-299 verbatim
open scoped BigOperators

-- @@ L300-300 verbatim
open MatrixMix

-- @@ L301-301 verbatim
variable {A : Type*} [CStarAlgebra A]

-- @@ L302-302 verbatim
abbrev Simplex (n : ℕ) := CoordinateSimplex (Fin (n+1))


-- @@ L304-305 verbatim
def last {n : ℕ} (r : Simplex (n+1)) : unitInterval :=
  ⟨r (Fin.last (n+1)),CoordinateSimplex.zero_le r _,CoordinateSimplex.le_one r _⟩

-- @@ L306-306 verbatim
def den {n : ℕ} (r : Simplex (n+1)) : ℝ := max (1-last r) (1/3)

-- @@ L307-308 verbatim
include instSize instPauliData in
lemma den_pos {n : ℕ} (r : Simplex (n+1)) : 0<den r := lt_of_lt_of_le (by norm_num) (le_max_right _ _)

-- @@ L309-315 verbatim
include instSize instPauliData in
lemma prev_sum {n : ℕ} (r : Simplex (n+1)) :
    ∑ i : Fin (n+1),r i.castSucc=1-(last r:ℝ) := by
  have h := CoordinateSimplex.sum_eq_one r
  rw [Fin.sum_univ_castSucc] at h
  change _+ (last r:ℝ)=1 at h
  linarith


-- @@ L317-327 verbatim
def prev {n : ℕ} (r : Simplex (n+1)) : Simplex n :=
  ⟨fun i => r i.castSucc/den r + if i=0 then 1-(1-last r)/den r else 0,by
    constructor
    · intro i
      apply add_nonneg (div_nonneg (CoordinateSimplex.zero_le r _) (den_pos r).le)
      split_ifs
      · apply sub_nonneg.mpr
        exact (div_le_one (den_pos r)).mpr (le_max_left _ _)
      · exact le_rfl
    · rw [Finset.sum_add_distrib,← Finset.sum_div,prev_sum]
      simp⟩

-- @@ L328-333 verbatim
lemma prev_apply {n : ℕ} (r : Simplex (n+1)) (h : (last r:ℝ)≤2/3) (i : Fin (n+1)) :
    prev r i=r i.castSucc/(1-last r) := by
  have hd : den r=1-last r := max_eq_left (by linarith)
  have hn : (1-(last r:ℝ))≠0 := by linarith
  change r i.castSucc / den r + (if i=0 then 1-(1-last r)/den r else 0)=_
  simp [hd,div_self hn]

-- @@ L334-337 verbatim
lemma prev_pos {n : ℕ} (r : Simplex (n+1)) (h : (last r:ℝ)≤2/3) (i : Fin (n+1))
    (hi : 0<prev r i) : 0<r i.castSucc := by
  rw [prev_apply r h] at hi
  exact (div_pos_iff.mp hi).elim (fun h => h.1) (fun h => False.elim (by linarith [CoordinateSimplex.zero_le r i.castSucc]))

-- @@ L338-341 verbatim
include instSize instPauliData in
lemma last_continuous {n : ℕ} : Continuous (last (n:=n)) := by
  apply Continuous.subtype_mk
  exact (continuous_apply _).comp continuous_subtype_val

-- @@ L342-355 verbatim
lemma prev_continuous {n : ℕ} : Continuous (prev (n:=n)) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  have hd : Continuous (den (n:=n)) := by
    exact (continuous_const.sub (continuous_subtype_val.comp last_continuous)).max continuous_const
  have hq : Continuous fun r : Simplex (n+1) => (1-(last r:ℝ))/den r :=
    (continuous_const.sub (continuous_subtype_val.comp last_continuous)).div hd (fun r => (den_pos r).ne')
  apply Continuous.add
  · exact ((continuous_apply _).comp continuous_subtype_val).div hd (fun r => (den_pos r).ne')
  · by_cases hi : i=0
    · simp only [ite_eq_left hi]
      exact (show Continuous (fun _ : Simplex (n+1) => (1:ℝ)) from continuous_const).sub hq
    · simp only [ite_eq_right hi]; exact continuous_const


-- @@ L357-361 verbatim
structure Family {n : ℕ} (φ : Fin (n+1) → Mat (Fin Size.n) →⋆ₐ[ℂ] A) where
  hom : Simplex n → Mat (Fin Size.n) →⋆ₐ[ℂ] A
  continuous : ∀ a,Continuous fun r => hom r a
  support : ∀ r (S : StarSubalgebra ℂ A), (∀ i,0<r i → ∀ a,φ i a∈S) → ∀ a,hom r a∈S
  vertex : ∀ i a,hom (CoordinateSimplex.vertex i) a=φ i a


-- @@ L363-363 verbatim
variable {n : ℕ} {φ : Fin (n+2) → Mat (Fin Size.n) →⋆ₐ[ℂ] A}

-- @@ L364-364 verbatim
variable (hc : ∀ i j,i≠j → ∀ a b,Commute (φ i a) (φ j b))

-- @@ L365-365 verbatim
variable (F : Family (fun i : Fin (n+1) => φ i.castSucc))


-- @@ L367-379 verbatim
include hc in
lemma family_commute (r : Simplex (n+1)) (a b : Mat (Fin Size.n)) :
    Commute (F.hom (prev r) a) (φ (Fin.last (n+1)) b) := by
  let S := StarSubalgebra.centralizer ℂ (Set.range (φ (Fin.last (n+1))))
  have hm : F.hom (prev r) a∈S := F.support _ S (by
    intro i _ c
    rw [StarSubalgebra.mem_centralizer_iff]
    rintro _ ⟨d,rfl⟩
    constructor
    · exact (hc i.castSucc (Fin.last _) (Fin.castSucc_ne_last i) c d).eq.symm
    · rw [← map_star]
      exact (hc i.castSucc (Fin.last _) (Fin.castSucc_ne_last i) c (star d)).eq.symm) a
  exact (((StarSubalgebra.mem_centralizer_iff ℂ).mp hm) _ ⟨b,rfl⟩).1.symm


-- @@ L381-382 verbatim
def extendHom (r : Simplex (n+1)) : Mat (Fin Size.n) →⋆ₐ[ℂ] A :=
  interpolate (F.hom (prev r)) (φ (Fin.last (n+1))) (family_commute hc F r) (last r)


-- @@ L384-395 verbatim
lemma extend_support (r : Simplex (n+1)) (S : StarSubalgebra ℂ A)
    (hs : ∀ i,0<r i → ∀ a,φ i a∈S) (a : Mat (Fin Size.n)) : extendHom hc F r a∈S := by
  by_cases ht : 2/3≤(last r:ℝ)
  · rw [extendHom,interpolate_top _ _ _ ht]
    exact hs _ (by change 0<(last r:ℝ); linarith) a
  · have ht' : (last r:ℝ)≤2/3 := (lt_of_not_ge ht).le
    have hp : ∀ a,F.hom (prev r) a∈S := F.support _ S (fun i hi => hs _ (prev_pos r ht' i hi))
    by_cases hz : last r=0
    · rw [extendHom,hz,interpolate_zero]; exact hp a
    · apply interpolate_mem _ _ _ S hp (hs _ ?_) _ a
      have hne : (last r:ℝ)≠0 := fun h => hz (Subtype.ext h)
      exact lt_of_le_of_ne (last r).2.1 hne.symm


-- @@ L397-404 verbatim
lemma prev_vertex (i : Fin (n+1)) :
    prev (CoordinateSimplex.vertex i.castSucc)=CoordinateSimplex.vertex i := by
  have hz : last (CoordinateSimplex.vertex i.castSucc)=0 := by
    apply Subtype.ext
    simp [last,Fin.castSucc_ne_last,eq_comm]
  ext j
  rw [prev_apply _ (by rw [hz]; norm_num)]
  simp [hz,Pi.single_apply,Fin.castSucc_inj]


-- @@ L406-414 verbatim
lemma extend_vertex (i : Fin (n+2)) (a : Mat (Fin Size.n)) :
    extendHom hc F (CoordinateSimplex.vertex i) a=φ i a := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · apply interpolate_top
    norm_num [last]
  · have hz : last (CoordinateSimplex.vertex j.castSucc)=0 := by
      apply Subtype.ext
      simp [last,Fin.castSucc_ne_last,eq_comm]
    rw [extendHom,hz,interpolate_zero,prev_vertex,F.vertex]


-- @@ L416-421 verbatim
def extend : Family φ where
  hom := extendHom hc F
  continuous a := interpolate_continuous _ _ _ (fun b => (F.continuous b).comp prev_continuous)
    (fun _ => continuous_const) last last_continuous a
  support := extend_support hc F
  vertex := extend_vertex hc F



-- @@ L424-442 verbatim
theorem exists_family (n : ℕ) (φ : Fin (n+1) → Mat (Fin Size.n) →⋆ₐ[ℂ] A)
    (hc : ∀ i j,i≠j → ∀ a b,Commute (φ i a) (φ j b)) : Nonempty (Family φ) := by
  induction n with
  | zero =>
    refine ⟨{hom := fun _ => φ 0
             continuous := fun _ => continuous_const
             support := ?_
             vertex := ?_}⟩
    · intro r S hs a
      have coordinate_one : r 0 = 1 := by
        simpa using CoordinateSimplex.sum_eq_one r
      exact hs 0 (by rw [coordinate_one]; norm_num) a
    · intro i a
      have : i=0 := Fin.eq_zero i
      subst i
      rfl
  | succ n ih =>
    obtain ⟨F⟩ := ih (fun i => φ i.castSucc) (fun i j hij => hc _ _ (fun h => hij (Fin.castSucc_inj.mp h)))
    exact ⟨extend hc F⟩

-- @@ L443-443 verbatim
end KirchbergRordam.GenericRW.MatrixSimplex

-- @@ L444-444 verbatim
namespace KirchbergRordam.GenericRW.CubeWeights

-- @@ L445-445 verbatim
open scoped BigOperators

-- @@ L446-446 verbatim
abbrev Cube (n : ℕ) := Fin (n+1) → unitInterval

-- @@ L447-447 verbatim
abbrev Punctured (n : ℕ) := {t : Cube n // t≠0}

-- @@ L448-448 verbatim
variable {n : ℕ}

-- @@ L449-449 verbatim
def radius (t : Cube n) : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun i => (t i:ℝ))

-- @@ L450-456 verbatim
omit instSize instPauliData in
lemma coord_le_radius
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {n : ℕ}
    (t : Cube n) (i : Fin (n+1)) : (t i:ℝ)≤radius t :=
  Finset.le_sup' (fun i => (t i:ℝ)) (Finset.mem_univ i)

-- @@ L457-457 verbatim
lemma radius_nonneg (t : Cube n) : 0≤radius t := (t 0).2.1.trans (coord_le_radius t 0)

-- @@ L458-465 verbatim
lemma radius_pos (t : Punctured n) : 0<radius t.1 := by
  by_contra! h
  have ht : t.1=0 := by
    ext i
    apply le_antisymm
    · exact (coord_le_radius t.1 i).trans h
    · exact (t.1 i).2.1
  exact t.2 ht

-- @@ L466-472 verbatim
omit instSize instPauliData in
lemma radius_continuous
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {n : ℕ}
    : Continuous (radius (n:=n)) :=
  Continuous.finset_sup'_apply _ (fun i _ => continuous_subtype_val.comp (continuous_apply i))

-- @@ L473-480 verbatim
omit instSize instPauliData in
lemma radius_attained
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {n : ℕ}
    (t : Cube n) : ∃ i,radius t=(t i:ℝ) := by
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => (t i:ℝ))
  exact ⟨i,hi⟩


-- @@ L482-482 verbatim
def weight (t : Punctured n) (i : Fin (n+1)) : ℝ := max ((t.1 i:ℝ)/radius t.1-1/2) 0

-- @@ L483-483 verbatim
def total (t : Punctured n) : ℝ := ∑ i,weight t i

-- @@ L484-489 verbatim
omit instSize instPauliData in
lemma weight_nonneg
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {n : ℕ}
    (t : Punctured n) (i : Fin (n+1)) : 0≤weight t i := le_max_right _ _

-- @@ L490-494 verbatim
lemma total_pos (t : Punctured n) : 0<total t := by
  obtain ⟨i,hi⟩ := radius_attained t.1
  have hw : weight t i=1/2 := by
    rw [weight,← hi,div_self (radius_pos t).ne']; norm_num
  exact lt_of_lt_of_le (by rw [hw]; norm_num) (Finset.single_le_sum (fun j _ => weight_nonneg t j) (Finset.mem_univ i))


-- @@ L496-498 verbatim
def normalized (t : Punctured n) : CoordinateSimplex (Fin (n+1)) :=
  ⟨fun i => weight t i/total t,fun i => div_nonneg (weight_nonneg t i) (total_pos t).le,by
    rw [← Finset.sum_div,← total,div_self (total_pos t).ne']⟩

-- @@ L499-499 verbatim
lemma normalized_apply (t : Punctured n) (i : Fin (n+1)) : normalized t i=weight t i/total t := rfl

-- @@ L500-506 verbatim
lemma normalized_continuous : Continuous (normalized (n:=n)) := by
  have hw (i : Fin (n+1)) : Continuous fun t : Punctured n => weight t i :=
    (((continuous_subtype_val.comp ((continuous_apply i).comp continuous_subtype_val)).div
      (radius_continuous.comp continuous_subtype_val) (fun t => (radius_pos t).ne')).sub continuous_const).max continuous_const
  have ht : Continuous (total (n:=n)) := continuous_finsetSum _ fun i _ => hw i
  apply Continuous.subtype_mk
  exact continuous_pi fun i => (hw i).div ht (fun t => (total_pos t).ne')

-- @@ L507-509 verbatim
lemma normalized_zero (t : Punctured n) (i : Fin (n+1)) (hi : t.1 i=0) : normalized t i=0 := by
  rw [normalized_apply,weight,hi]
  norm_num

-- @@ L510-514 verbatim
lemma normalized_support (t : Punctured n) (i : Fin (n+1)) (hi : 0<normalized t i) : 0<(t.1 i:ℝ) := by
  by_contra! h
  have hz : t.1 i=0 := Subtype.ext (le_antisymm h (t.1 i).2.1)
  rw [normalized_zero t i hz] at hi
  exact (lt_irrefl _ hi)


-- @@ L516-539 verbatim
lemma localized_normalized (t : Punctured n) {δ : ℝ} (hδ : 0<δ) (j : Fin (n+1))
    (hj : δ<(t.1 j:ℝ)) (hi : ∀ i,i≠j → (t.1 i:ℝ)<δ/2) :
    normalized t=CoordinateSimplex.vertex j := by
  have hd : radius t.1=(t.1 j:ℝ) := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro i _
      by_cases he : i=j
      · subst i; exact le_rfl
      · linarith [hi i he]
    · exact coord_le_radius _ _
  have hpos : 0<(t.1 j:ℝ) := hδ.trans hj
  have hw (i : Fin (n+1)) : weight t i=if i=j then 1/2 else 0 := by
    unfold weight
    rw [hd]
    by_cases he : i=j
    · subst i; rw [div_self hpos.ne']; norm_num
    · rw [ite_eq_right he,max_eq_right]
      have hh : (t.1 i:ℝ)/(t.1 j:ℝ)<1/2 := (div_lt_iff₀ hpos).mpr (by linarith [hi i he])
      linarith
  have htotal : total t=1/2 := by simp [total,hw]
  ext i
  rw [normalized_apply,hw,htotal]
  by_cases he : i=j <;> simp [he,eq_comm]


-- @@ L541-541 verbatim
def g (δ : ℝ) (t : unitInterval) : ℝ := max (1-2*(t:ℝ)/δ) 0

-- @@ L542-546 verbatim
omit instSize instPauliData in
lemma g_continuous
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    (δ : ℝ) : Continuous (g δ) := by unfold g; fun_prop

-- @@ L547-551 verbatim
omit instSize instPauliData in
lemma g_nonneg
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    (δ : ℝ) (t : unitInterval) : 0≤g δ t := le_max_right _ _

-- @@ L552-559 verbatim
omit instSize instPauliData in
lemma g_le_one
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {δ : ℝ} (hδ : 0<δ) (t : unitInterval) : g δ t≤1 := by
  apply max_le _ zero_le_one
  have : 0≤2*(t:ℝ)/δ := div_nonneg (mul_nonneg (by norm_num) t.2.1) hδ.le
  linarith

-- @@ L560-564 verbatim
omit instSize instPauliData in
lemma g_zero
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    (δ : ℝ) : g δ 0=1 := by simp [g]

-- @@ L565-573 verbatim
omit instSize instPauliData in
lemma g_pos
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {δ : ℝ} (hδ : 0<δ) (t : unitInterval) (h : 0<g δ t) : (t:ℝ)<δ/2 := by
  have hp : 0<1-2*(t:ℝ)/δ := (lt_max_iff.mp h).resolve_right (lt_irrefl _)
  have hh : 2*(t:ℝ)/δ<1 := by linarith
  have := (div_lt_one hδ).mp hh
  linarith

-- @@ L574-581 verbatim
omit instSize instPauliData in
lemma g_of_large
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {δ : ℝ} (hδ : 0<δ) (t : unitInterval) (h : δ≤(t:ℝ)) : g δ t=0 := by
  apply max_eq_right
  have : 1≤2*(t:ℝ)/δ := (one_le_div hδ).mpr (by linarith)
  linarith


-- @@ L583-583 verbatim
def H (δ : ℝ) (t : Cube n) : ℝ := 1-∏ i,g δ (t i)

-- @@ L584-585 verbatim
lemma H_continuous (δ : ℝ) : Continuous (H (n:=n) δ) :=
  continuous_const.sub (continuous_finsetProd _ fun i _ => (g_continuous δ).comp (continuous_apply i))

-- @@ L586-586 verbatim
lemma H_zero (δ : ℝ) : H (n:=n) δ 0=0 := by simp [H,g_zero]

-- @@ L587-589 verbatim
lemma H_nonneg {δ : ℝ} (hδ : 0<δ) (t : Cube n) : 0≤H δ t := by
  apply sub_nonneg.mpr
  exact Finset.prod_le_one₀ (fun i _ => g_nonneg δ (t i)) (fun i _ => g_le_one hδ (t i))

-- @@ L590-592 verbatim
lemma H_le_one (δ : ℝ) (t : Cube n) : H δ t≤1 := by
  have hp : 0≤∏ i,g δ (t i) := Finset.prod_nonneg (fun i _ => g_nonneg δ (t i))
  unfold H; linarith

-- @@ L593-595 verbatim
lemma H_of_large {δ : ℝ} (hδ : 0<δ) (t : Cube n) (j : Fin (n+1)) (h : δ≤(t j:ℝ)) : H δ t=1 := by
  have hz : ∏ i,g δ (t i)=0 := Finset.prod_eq_zero (Finset.mem_univ j) (g_of_large hδ _ h)
  simp [H,hz]

-- @@ L596-596 verbatim
end KirchbergRordam.GenericRW.CubeWeights

-- @@ L597-597 verbatim
end


-- @@ L599-599 verbatim
end OAI
