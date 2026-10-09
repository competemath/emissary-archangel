import OAI.Analysis.CharacterCriterion.MatrixSimplex


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
variable [KirchbergRordam.GenericRW.Size]

-- @@ L20-20 verbatim
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n

-- @@ L21-21 verbatim
variable [KirchbergRordam.GenericRW.PauliData]


-- @@ L23-23 verbatim
namespace KirchbergRordam.GenericRW.CubeField

-- @@ L24-24 verbatim
open scoped BigOperators Topology

-- @@ L25-25 verbatim
open Filter MatrixMix MatrixSimplex CubeWeights

-- @@ L26-26 verbatim
variable {A : Type*} [CStarAlgebra A]

-- @@ L27-27 verbatim
variable {n : ℕ} {φ : Fin (n+1) → Mat (Fin Size.n) →⋆ₐ[ℂ] A}

-- @@ L28-28 verbatim
variable (F : Family φ)


-- @@ L30-35 verbatim
lemma norm_matrix_unit (ψ : Mat (Fin Size.n) →⋆ₐ[ℂ] A) (i j : Fin Size.n) : ‖ψ (e i j)‖≤1 := by
  have hp : IsStarProjection (ψ (e j j)) := ⟨by change ψ _*ψ _=ψ _; rw [← map_mul,e_mul,ite_eq_left rfl],by change star (ψ _) = ψ _; rw [← map_star,e_star]⟩
  have hn := hp.norm_le _
  have he : ‖ψ (e i j)‖*‖ψ (e i j)‖=‖ψ (e j j)‖ := by
    rw [← CStarRing.norm_star_mul_self,← map_star,← map_mul,e_star,e_mul,ite_eq_left rfl]
  nlinarith [norm_nonneg (ψ (e i j))]


-- @@ L37-38 verbatim
def dampedFun (f : C(Cube n,ℝ)) (i j : Fin Size.n) (t : Cube n) : A :=
  if ht : t≠0 then f t • F.hom (normalized ⟨t,ht⟩) (e i j) else 0

-- @@ L39-39 verbatim
lemma damped_zero (f : C(Cube n,ℝ)) (i j : Fin Size.n) : dampedFun F f i j 0=0 := by simp [dampedFun]

-- @@ L40-45 verbatim
lemma damped_norm (f : C(Cube n,ℝ)) (i j : Fin Size.n) (t : Cube n) : ‖dampedFun F f i j t‖≤‖f t‖ := by
  unfold dampedFun
  split_ifs
  · rw [norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_matrix_unit _ _ _)
  · simp only [norm_zero]; exact norm_nonneg (f t)

-- @@ L46-62 verbatim
lemma damped_continuous (f : C(Cube n,ℝ)) (hf : f 0=0) (i j : Fin Size.n) :
    Continuous (dampedFun F f i j) := by
  have ho : ContinuousOn (dampedFun F f i j) {t | t≠0} := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun t : Punctured n => dampedFun F f i j t.1)
    have hh := ((f.continuous.comp continuous_subtype_val).smul
      ((F.continuous (e i j)).comp normalized_continuous))
    exact hh.congr (fun t => by simp [dampedFun,t.2])
  rw [continuous_iff_continuousAt]
  intro t
  by_cases ht : t=0
  · subst t
    change Tendsto (dampedFun F f i j) _ (𝓝 (dampedFun F f i j 0))
    rw [damped_zero]
    apply squeeze_zero_norm (damped_norm F f i j)
    simpa [ContinuousAt,hf] using f.continuous.norm.continuousAt (x:=0)
  · exact ho.continuousAt (isOpen_ne.mem_nhds ht)


-- @@ L64-65 verbatim
def damped (f : C(Cube n,ℝ)) (hf : f 0=0) (i j : Fin Size.n) : C(Cube n,A) :=
  ⟨dampedFun F f i j,damped_continuous F f hf i j⟩


-- @@ L67-67 verbatim
def scalarH (δ : ℝ) : C(Cube n,ℝ) := ⟨H δ,H_continuous δ⟩

-- @@ L68-68 verbatim
def scalarSqrt (δ : ℝ) : C(Cube n,ℝ) := ⟨fun t => Real.sqrt (H δ t),(H_continuous δ).sqrt⟩

-- @@ L69-69 verbatim
def x (δ : ℝ) (i j : Fin Size.n) : C(Cube n,A) := damped F (scalarH δ) (H_zero δ) i j

-- @@ L70-70 verbatim
def v (δ : ℝ) : C(Cube n,A) := damped F (scalarSqrt δ) (by simp [scalarSqrt,H_zero]) 1 0


-- @@ L72-72 verbatim
def h (δ : ℝ) : C(Cube n,A) := ⟨fun t => H δ t • (1:A),(H_continuous δ).smul continuous_const⟩

-- @@ L73-74 verbatim
lemma x_apply (δ : ℝ) (i j : Fin Size.n) (t : Punctured n) :
    x F δ i j t.1=H δ t.1 • F.hom (normalized t) (e i j) := by simp [x,damped,dampedFun,t.2,scalarH]

-- @@ L75-75 verbatim
lemma x_zero (δ : ℝ) (i j : Fin Size.n) : x F δ i j 0=0 := damped_zero F _ _ _

-- @@ L76-77 verbatim
lemma v_apply (δ : ℝ) (t : Punctured n) :
    v F δ t.1=Real.sqrt (H δ t.1) • F.hom (normalized t) (e 1 0) := by simp [v,damped,dampedFun,t.2,scalarSqrt]

-- @@ L78-78 verbatim
lemma v_zero (δ : ℝ) : v F δ 0=0 := damped_zero F _ _ _


-- @@ L80-85 verbatim
lemma x_star (δ : ℝ) (i j : Fin Size.n) : star (x F δ i j)=x F δ j i := by
  ext t
  by_cases ht : t=0
  · subst t; simp [x_zero]
  · change star (x F δ i j t)=_
    rw [x_apply F δ i j ⟨t,ht⟩,x_apply F δ j i ⟨t,ht⟩,star_smul,star_trivial,← map_star,e_star]

-- @@ L86-97 verbatim
lemma x_mul (δ : ℝ) (i j k l : Fin Size.n) :
    x F δ i j*x F δ k l=if j=k then h δ*x F δ i l else 0 := by
  ext t
  by_cases ht : t=0
  · subst t; by_cases hjk : j=k <;> simp [hjk,x_zero,h,H_zero]
  · change x F δ i j t*x F δ k l t=_
    rw [x_apply F δ i j ⟨t,ht⟩,x_apply F δ k l ⟨t,ht⟩,smul_mul_smul_comm,← map_mul,e_mul]
    by_cases hjk : j=k
    · rw [ite_eq_left hjk,ite_eq_left hjk]
      change _=H δ t • (1:A)*x F δ i l t
      rw [x_apply F δ i l ⟨t,ht⟩,smul_mul_smul_comm,one_mul]
    · simp [hjk]

-- @@ L98-105 verbatim
lemma x_diagonal (δ : ℝ) : ∑ i : Fin Size.n,x F δ i i=h δ := by
  ext t
  by_cases ht : t=0
  · subst t; simp [x_zero,h,H_zero]
  · simp only [ContinuousMap.sum_apply]
    simp_rw [x_apply F δ _ _ ⟨t,ht⟩]
    rw [← Finset.smul_sum,← map_sum,e_sum,map_one]
    rfl

-- @@ L106-112 verbatim
lemma v_star_mul {δ : ℝ} (hδ : 0<δ) : star (v F δ)*v F δ=x F δ 0 0 := by
  ext t
  by_cases ht : t=0
  · subst t; simp [v_zero,x_zero]
  · change star (v F δ t)*v F δ t=_
    rw [v_apply F δ ⟨t,ht⟩,x_apply F δ 0 0 ⟨t,ht⟩,star_smul,star_trivial,← map_star,
      e_star,smul_mul_smul_comm,Real.mul_self_sqrt (H_nonneg hδ t),← map_mul,e_mul,ite_eq_left rfl]

-- @@ L113-119 verbatim
lemma v_mul_star {δ : ℝ} (hδ : 0<δ) : v F δ*star (v F δ)=x F δ 1 1 := by
  ext t
  by_cases ht : t=0
  · subst t; simp [v_zero,x_zero]
  · change v F δ t*star (v F δ t)=_
    rw [v_apply F δ ⟨t,ht⟩,x_apply F δ 1 1 ⟨t,ht⟩,star_smul,star_trivial,← map_star,
      e_star,smul_mul_smul_comm,Real.mul_self_sqrt (H_nonneg hδ t),← map_mul,e_mul,ite_eq_left rfl]


-- @@ L121-126 verbatim
lemma x_support (δ : ℝ) (t : Cube n) (S : StarSubalgebra ℂ A)
    (hs : ∀ k,0<(t k:ℝ) → ∀ a,φ k a∈S) (i j : Fin Size.n) : x F δ i j t∈S := by
  by_cases ht : t=0
  · subst t; rw [x_zero]; exact S.zero_mem
  · rw [x_apply F δ i j ⟨t,ht⟩]
    exact S.smul_mem (F.support _ S (fun k hk => hs k (normalized_support ⟨t,ht⟩ k hk)) _) _


-- @@ L128-131 verbatim
lemma x_localized {δ : ℝ} (hδ : 0<δ) (t : Punctured n) (j : Fin (n+1))
    (hj : δ<(t.1 j:ℝ)) (hi : ∀ i,i≠j → (t.1 i:ℝ)<δ/2) (a b : Fin Size.n) :
    x F δ a b t.1=φ j (e a b) := by
  rw [x_apply,localized_normalized t hδ j hj hi,F.vertex,H_of_large hδ t.1 j hj.le,one_smul]

-- @@ L132-132 verbatim
end KirchbergRordam.GenericRW.CubeField


-- @@ L134-134 verbatim
namespace KirchbergRordam.GenericRW.CubeField

-- @@ L135-135 verbatim
open scoped BigOperators CStarAlgebra

-- @@ L136-136 verbatim
open MatrixMix MatrixSimplex CubeWeights

-- @@ L137-137 verbatim
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

-- @@ L138-138 verbatim
variable {n : ℕ} {φ : Fin (n+1) → Mat (Fin Size.n) →⋆ₐ[ℂ] A} (F : Family φ)

-- @@ L139-141 verbatim
lemma h_nonneg {δ : ℝ} (hδ : 0<δ) : 0≤(h δ : C(Cube n,A)) := by
  intro t
  exact smul_nonneg (H_nonneg hδ t) zero_le_one

-- @@ L142-149 verbatim
omit [PartialOrder A] [StarOrderedRing A] in
lemma h_norm {δ : ℝ} (hδ : 0<δ) : ‖(h δ : C(Cube n,A))‖≤1 := by
  apply (ContinuousMap.norm_le _ (by norm_num)).mpr
  intro t
  change ‖H δ t • (1:A)‖≤1
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (H_nonneg hδ t)]
  have hn : ‖(1:A)‖≤1 := (IsStarProjection.one (R:=A)).norm_le _
  exact (mul_le_of_le_one_right (H_nonneg hδ t) hn).trans (H_le_one δ t)


-- @@ L151-158 verbatim
def weighted {δ : ℝ} (hδ : 0<δ) : OrderZero.WeightedUnits (Fin Size.n) C(Cube n,A) where
  h := h δ
  x := x F δ
  nonneg := h_nonneg hδ
  norm_le := h_norm hδ
  star_x := x_star F δ
  mul_x := x_mul F δ
  diagonal := x_diagonal F δ


-- @@ L160-163 verbatim
lemma first_nonneg {δ : ℝ} (hδ : 0<δ) : 0≤x F δ 0 0 := by
  rw [← v_star_mul F hδ]
  intro t
  exact star_mul_self_nonneg (v F δ t)

-- @@ L164-167 verbatim
lemma second_nonneg {δ : ℝ} (hδ : 0<δ) : 0≤x F δ 1 1 := by
  rw [← v_mul_star F hδ]
  intro t
  exact mul_star_self_nonneg (v F δ t)

-- @@ L168-176 verbatim
omit [PartialOrder A] [StarOrderedRing A] in
lemma pair_orthogonal (δ : ℝ) : x F δ 0 0*x F δ 1 1=0 := by
  have hn : 1 < Size.n := by have := PauliData.two_le; omega
  have h01 : (0:Fin Size.n) ≠ 1 := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_zero,Fin.val_one',Nat.mod_eq_of_lt hn] at hv
    omega
  rw [x_mul,ite_eq_right h01]

-- @@ L177-184 verbatim
omit [PartialOrder A] [StarOrderedRing A] in
lemma entry_norm {δ : ℝ} (hδ : 0<δ) (i j : Fin Size.n) : ‖x F δ i j‖≤1 := by
  apply (ContinuousMap.norm_le _ (by norm_num)).mpr
  intro t
  exact (damped_norm F (scalarH δ) i j t).trans (by
    change ‖H δ t‖≤1
    rw [Real.norm_eq_abs,abs_of_nonneg (H_nonneg hδ t)]
    exact H_le_one δ t)

-- @@ L185-185 verbatim
end KirchbergRordam.GenericRW.CubeField


-- @@ L187-187 verbatim
namespace KirchbergRordam.GenericRW.ConeCube

-- @@ L188-188 verbatim
open scoped CStarAlgebra ComplexOrder BigOperators

-- @@ L189-189 verbatim
open ConeModel MatrixSimplex

-- @@ L190-190 verbatim
local instance (n : ℕ) : PartialOrder (Tensor n) := CStarAlgebra.spectralOrder _

-- @@ L191-191 verbatim
local instance (n : ℕ) : StarOrderedRing (Tensor n) := CStarAlgebra.spectralOrderedRing _


-- @@ L193-193 verbatim
def family (n : ℕ) : Family (matLeg n) := (exists_family n (matLeg n) (matLeg_commute n)).some


-- @@ L195-207 verbatim
lemma x_face_commute (n : ℕ) (δ : ℝ) (i l : Fin Size.n) (t : Cube n) (j : Fin (n+1))
    (hj : t j=0) (b : M2) : Commute (matLeg n j b) (CubeField.x (family n) δ i l t) := by
  let S := StarSubalgebra.centralizer ℂ (Set.range (matLeg n j))
  have hm : CubeField.x (family n) δ i l t∈S := CubeField.x_support _ _ _ S (by
    intro k hk a
    have hkj : k≠j := by intro h; subst k; rw [hj] at hk; exact (lt_irrefl (0:ℝ)) hk
    rw [StarSubalgebra.mem_centralizer_iff]
    rintro _ ⟨c,rfl⟩
    constructor
    · exact (matLeg_commute n j k hkj.symm c a).eq
    · rw [← map_star]
      exact (matLeg_commute n j k hkj.symm (star c) a).eq) i l
  exact (((StarSubalgebra.mem_centralizer_iff ℂ).mp hm) _ ⟨b,rfl⟩).1


-- @@ L209-215 verbatim
lemma x_liftable (n : ℕ) (δ : ℝ) (i j : Fin Size.n) :
    ∃! b : Tensor n,repr n b=CubeField.x (family n) δ i j ∧
      ‖b‖=‖CubeField.x (family n) δ i j‖ := by
  apply exists_unique_lift
  intro a t ha
  obtain ⟨k,hk,hne⟩ := p_zero n a t ha
  exact ccoeff_zero n a k hne _ (x_face_commute n δ i j t k hk)


-- @@ L217-217 verbatim
def x (n : ℕ) (δ : ℝ) (i j : Fin Size.n) : Tensor n := (x_liftable n δ i j).exists.choose

-- @@ L218-219 verbatim
lemma repr_x (n : ℕ) (δ : ℝ) (i j : Fin Size.n) :
    repr n (x n δ i j)=CubeField.x (family n) δ i j := ((x_liftable n δ i j).exists.choose_spec).1


-- @@ L221-222 verbatim
def hScalar (n : ℕ) (δ : ℝ) : C(Cube n,ℂ) :=
  ⟨fun t => ((CubeWeights.H δ t:ℝ):ℂ),Complex.continuous_ofReal.comp (CubeWeights.H_continuous δ)⟩

-- @@ L223-223 verbatim
def h (n : ℕ) (δ : ℝ) : Tensor n := κ n (hScalar n δ)

-- @@ L224-230 verbatim
lemma repr_h (n : ℕ) (δ : ℝ) : repr n (h n δ)=CubeField.h δ := by
  apply ContinuousMap.ext
  intro t
  rw [h,repr_κ]
  change algebraMap ℂ (Fiber n) (((CubeWeights.H δ t):ℝ):ℂ)=CubeWeights.H δ t • (1:Fiber n)
  rw [Algebra.algebraMap_eq_smul_one]
  exact Complex.coe_smul _ _

-- @@ L231-234 verbatim
lemma h_nonneg (n : ℕ) {δ : ℝ} (hδ : 0<δ) : 0≤h n δ := by
  apply map_nonneg (κ n)
  intro t
  exact Complex.zero_le_real.mpr (CubeWeights.H_nonneg hδ t)

-- @@ L235-239 verbatim
lemma h_norm (n : ℕ) {δ : ℝ} (hδ : 0<δ) : ‖h n δ‖≤1 := by
  have hn : ‖h n δ‖=‖repr n (h n δ)‖ := by
    exact (NonUnitalStarAlgHom.norm_map (repr n) (faithful n) _).symm
  rw [hn,repr_h]
  exact CubeField.h_norm hδ



-- @@ L242-258 verbatim
def weighted (n : ℕ) {δ : ℝ} (hδ : 0<δ) : OrderZero.WeightedUnits (Fin Size.n) (Tensor n) where
  h := h n δ
  x := x n δ
  nonneg := h_nonneg n hδ
  norm_le := h_norm n hδ
  star_x i j := by apply faithful n; rw [map_star,repr_x,repr_x]; exact CubeField.x_star _ _ _ _
  mul_x i j k l := by
    have product_eq := CubeField.x_mul (family n) δ i j k l
    apply faithful n
    rw [map_mul,repr_x,repr_x]
    refine product_eq.trans ?_
    split_ifs <;> simp [map_mul,repr_h,repr_x]
  diagonal := by
    apply faithful n
    rw [map_sum,repr_h]
    simp_rw [repr_x]
    exact CubeField.x_diagonal _ _

-- @@ L259-259 verbatim
end KirchbergRordam.GenericRW.ConeCube

-- @@ L260-260 verbatim
end


-- @@ L262-262 verbatim
end OAI
