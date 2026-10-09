import OAI.Analysis.CharacterCriterion.CubeField


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
namespace KirchbergRordam.GenericRW.ClosedRightRange

-- @@ L25-25 verbatim
open scoped CStarAlgebra

-- @@ L26-26 verbatim
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

-- @@ L27-43 verbatim
omit instSize instPauliData in
lemma map_mem.{contextLevel1, contextLevel2}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {A : Type contextLevel1}
    {B : Type contextLevel2}
    [CStarAlgebra A]
    [CStarAlgebra B]
    (φ : A →⋆ₐ[ℂ] B) {a z : A} (hz : z ∈ space a) :
    φ z ∈ space (φ a) := by
  have hh (z : space a) : φ (z : A) ∈ space (φ a) := by
    refine (dense a).induction_on z ((closed (φ a)).preimage ((map_continuous φ).comp continuous_subtype_val)) ?_
    intro x
    change φ (a*x) ∈ space (φ a)
    rw [map_mul]
    exact mem_space _ _
  exact hh ⟨z,hz⟩

-- @@ L44-44 verbatim
end KirchbergRordam.GenericRW.ClosedRightRange


-- @@ L46-46 verbatim
namespace KirchbergRordam.GenericRW.CuntzBelow

-- @@ L47-47 verbatim
open scoped CStarAlgebra

-- @@ L48-48 verbatim
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]



-- @@ L51-72 verbatim
omit instSize instPauliData in
lemma of_right_range.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    [PartialOrder A]
    [StarOrderedRing A]
    {b z : A} (hb : 0≤b) (hz : z ∈ ClosedRightRange.space b) :
    CuntzBelow (star z*z) b := by
  have hh (z : ClosedRightRange.space (CFC.sqrt b)) : CuntzBelow (star (z:A)*(z:A)) b := by
    refine (ClosedRightRange.dense (CFC.sqrt b)).induction_on z
      (isClosed_closure.preimage (by fun_prop)) ?_
    intro x
    apply of_eq (x:=x)
    change star x*b*x=star (CFC.sqrt b*x)*(CFC.sqrt b*x)
    rw [star_mul,(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg b)).star_eq]
    calc
      _ = star x*(CFC.sqrt b*CFC.sqrt b)*x := by rw [CFC.sqrt_mul_sqrt_self b hb]
      _ = _ := by noncomm_ring
  rw [← Domination.sqrt_right_range_eq b hb] at hz
  exact hh ⟨z,hz⟩

-- @@ L73-73 verbatim
end KirchbergRordam.GenericRW.CuntzBelow


-- @@ L75-75 verbatim
namespace KirchbergRordam.GenericRW.AmplifiedComparison

-- @@ L76-76 verbatim
open scoped CStarAlgebra

-- @@ L77-77 verbatim
open scoped BigOperators

-- @@ L78-78 verbatim
variable {P R B : Type*} [CStarAlgebra P] [CStarAlgebra R] [CStarAlgebra B]

-- @@ L79-79 verbatim
variable {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]

-- @@ L80-80 verbatim
variable (φ : P →⋆ₐ[ℂ] B) (ψ : R →⋆ₐ[ℂ] B)

-- @@ L81-81 verbatim
variable (hc : ∀ a b, Commute (φ a) (ψ b))


-- @@ L83-83 verbatim
def pair (a : P) (b : R) : B := φ a*ψ b

-- @@ L84-103 verbatim
omit hc in
omit instSize instPauliData in
lemma pair_mul.{contextLevel1, contextLevel2, contextLevel3}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {P : Type contextLevel1}
    {R : Type contextLevel2}
    {B : Type contextLevel3}
    [CStarAlgebra P]
    [CStarAlgebra R]
    [CStarAlgebra B]
    (φ : P →⋆ₐ[ℂ] B)
    (ψ : R →⋆ₐ[ℂ] B)
    (hc : ∀ (a : P) (b : R), Commute (φ a) (ψ b))
    (a c : P) (b d : R) : pair φ ψ a b*pair φ ψ c d=pair φ ψ (a*c) (b*d) := by
  simp only [pair,map_mul]
  calc
    (φ a*ψ b)*(φ c*ψ d)=φ a*(ψ b*φ c)*ψ d := by noncomm_ring
    _=φ a*(φ c*ψ b)*ψ d := by rw [← (hc c b).eq]
    _=_ := by noncomm_ring

-- @@ L104-120 verbatim
omit hc in
omit instSize instPauliData in
lemma pair_star.{contextLevel1, contextLevel2, contextLevel3}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {P : Type contextLevel1}
    {R : Type contextLevel2}
    {B : Type contextLevel3}
    [CStarAlgebra P]
    [CStarAlgebra R]
    [CStarAlgebra B]
    (φ : P →⋆ₐ[ℂ] B)
    (ψ : R →⋆ₐ[ℂ] B)
    (hc : ∀ (a : P) (b : R), Commute (φ a) (ψ b))
    (a : P) (b : R) : star (pair φ ψ a b)=pair φ ψ (star a) (star b) := by
  simp only [pair,star_mul,map_star]
  simpa only [map_star] using (hc (star a) (star b)).eq.symm

-- @@ L121-133 verbatim
omit instSize instPauliData in
lemma pair_zero_left.{contextLevel1, contextLevel2, contextLevel3}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {P : Type contextLevel1}
    {R : Type contextLevel2}
    {B : Type contextLevel3}
    [CStarAlgebra P]
    [CStarAlgebra R]
    [CStarAlgebra B]
    (φ : P →⋆ₐ[ℂ] B)
    (ψ : R →⋆ₐ[ℂ] B)
    (b : R) : pair φ ψ 0 b=0 := by simp [pair]

-- @@ L134-146 verbatim
omit instSize instPauliData in
lemma pair_zero_right.{contextLevel1, contextLevel2, contextLevel3}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {P : Type contextLevel1}
    {R : Type contextLevel2}
    {B : Type contextLevel3}
    [CStarAlgebra P]
    [CStarAlgebra R]
    [CStarAlgebra B]
    (φ : P →⋆ₐ[ℂ] B)
    (ψ : R →⋆ₐ[ℂ] B)
    (a : P) : pair φ ψ a 0=0 := by simp [pair]

-- @@ L147-163 verbatim
omit [DecidableEq I] in
omit instSize instPauliData in
lemma pair_sum_left.{contextLevel1, contextLevel2, contextLevel3, contextLevel4}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {P : Type contextLevel1}
    {R : Type contextLevel2}
    {B : Type contextLevel3}
    [CStarAlgebra P]
    [CStarAlgebra R]
    [CStarAlgebra B]
    {I : Type contextLevel4}
    [Fintype I]
    (φ : P →⋆ₐ[ℂ] B)
    (ψ : R →⋆ₐ[ℂ] B)
    (a : I→P) (b : R) : (∑ i,pair φ ψ (a i) b)=pair φ ψ (∑ i,a i) b := by
  simp only [pair,map_sum,Finset.sum_mul]

-- @@ L164-180 verbatim
omit [DecidableEq J] in
omit instSize instPauliData in
lemma pair_sum_right.{contextLevel1, contextLevel2, contextLevel3, contextLevel4}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {P : Type contextLevel1}
    {R : Type contextLevel2}
    {B : Type contextLevel3}
    [CStarAlgebra P]
    [CStarAlgebra R]
    [CStarAlgebra B]
    {J : Type contextLevel4}
    [Fintype J]
    (φ : P →⋆ₐ[ℂ] B)
    (ψ : R →⋆ₐ[ℂ] B)
    (a : P) (b : J→R) : (∑ j,pair φ ψ a (b j))=pair φ ψ a (∑ j,b j) := by
  simp only [pair,map_sum,Finset.mul_sum]


-- @@ L182-182 verbatim
variable [PartialOrder P] [StarOrderedRing P]

-- @@ L183-183 verbatim
variable (y : J→P) (hy : ∀ j,0≤y j) (horth : ∀ j k,j≠k → y j*y k=0)

-- @@ L184-184 verbatim
variable (u : J→I→P) (z : I→R) (v : J→R) (e : R)

-- @@ L185-185 verbatim
variable (hz : ∀ i l,star (z i)*z l=if i=l then e else 0)


-- @@ L187-187 verbatim
def gramVector (j : J) (i : I) : B := pair φ ψ (CFC.sqrt (y j)*u j i) (z i*v j)

-- @@ L188-203 verbatim
omit hy horth in
omit [Fintype J] [DecidableEq J] in
omit instSize instPauliData in
lemma sqrt_orthogonal.{contextLevel1, contextLevel2}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {P : Type contextLevel1}
    [CStarAlgebra P]
    {J : Type contextLevel2}
    [PartialOrder P]
    [StarOrderedRing P]
    (y : J → P)
    (hy : ∀ (j : J), 0 ≤ y j)
    (horth : ∀ (j k : J), j ≠ k → y j * y k = 0)
    (j k : J) (hjk : j≠k) : CFC.sqrt (y j)*CFC.sqrt (y k)=0 := by
  exact Intertwining.mul_sqrt_eq_zero (hy k) (Intertwining.sqrt_mul_eq_zero (hy j) (horth j k hjk))


-- @@ L205-223 verbatim
include hc hy horth hz in
omit [Fintype I] [Fintype J] in
lemma gram_inner (j k : J) (i l : I) :
    star (gramVector φ ψ y u z v j i)*gramVector φ ψ y u z v k l =
      if j=k ∧ i=l then pair φ ψ (star (u j i)*y j*u j i) (star (v j)*e*v j) else 0 := by
  simp only [gramVector,pair_star φ ψ hc,pair_mul φ ψ hc,star_mul,
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (y j))).star_eq]
  have hleft : (star (u j i)*CFC.sqrt (y j))*(CFC.sqrt (y k)*u k l)=
      star (u j i)*(CFC.sqrt (y j)*CFC.sqrt (y k))*u k l := by noncomm_ring
  have hright : (star (v j)*star (z i))*(z l*v k)=star (v j)*(star (z i)*z l)*v k := by noncomm_ring
  rw [hleft,hright,hz]
  by_cases hjk : j=k
  · subst k
    rw [CFC.sqrt_mul_sqrt_self (y j) (hy j)]
    by_cases hil : i=l
    · subst l; simp
    · simp [hil,pair_zero_right]
  · rw [sqrt_orthogonal y hy horth j k hjk]
    simp [hjk,pair_zero_left]


-- @@ L225-225 verbatim
variable [PartialOrder B] [StarOrderedRing B]

-- @@ L226-256 verbatim
include ψ hc hy horth z hz in


theorem compare (X : P)
    (hu : ∀ j,∑ i,star (u j i)*y j*u j i=X)
    (hv : ∑ j,star (v j)*e*v j=1) :
    CuntzBelow (φ X) (φ (∑ j,y j)) := by
  let w : B := ∑ j,∑ i,gramVector φ ψ y u z v j i
  have hww : star w*w=φ X := by
    dsimp only [w]
    simp only [star_sum,Finset.sum_mul,Finset.mul_sum]
    simp_rw [gram_inner φ ψ hc y hy horth u z v e hz]
    simp only [ite_and]
    simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    simp_rw [pair_sum_left,hu]
    rw [pair_sum_right,hv]
    simp [pair]
  have hY : 0≤∑ j,y j := Finset.sum_nonneg (fun j _ => hy j)
  have hw : w ∈ ClosedRightRange.space (φ (∑ j,y j)) := by
    apply (ClosedRightRange.space _).sum_mem
    intro j _
    apply (ClosedRightRange.space _).sum_mem
    intro i _
    apply ClosedRightRange.mul_right_mem
    apply ClosedRightRange.map_mem
    apply ClosedRightRange.mul_right_mem
    apply Domination.sqrt_mem_right_range (hy j) hY (by norm_num : (0:ℝ)≤1)
    simp only [one_smul]
    exact Finset.single_le_sum (fun k _ => hy k) (Finset.mem_univ j)
  rw [← hww]
  exact CuntzBelow.of_right_range (map_nonneg φ hY) hw

-- @@ L257-257 verbatim
end KirchbergRordam.GenericRW.AmplifiedComparison

-- @@ L258-258 verbatim
namespace KirchbergRordam.GenericRW.MaxTensor

-- @@ L259-259 verbatim
open scoped BigOperators

-- @@ L260-260 verbatim
universe u

-- @@ L261-261 verbatim
variable {P Q : Type u} [CStarAlgebra P] [CStarAlgebra Q]


-- @@ L263-263 verbatim
def pure (a : P) (b : Q) : Algebra P Q := includeLeft a*includeRight b

-- @@ L264-265 verbatim
lemma pure_mul (a c : P) (b d : Q) : pure a b*pure c d=pure (a*c) (b*d) :=
  AmplifiedComparison.pair_mul includeLeft includeRight legs_commute a c b d

-- @@ L266-267 verbatim
lemma pure_star (a : P) (b : Q) : star (pure a b)=pure (star a) (star b) :=
  AmplifiedComparison.pair_star includeLeft includeRight legs_commute a b

-- @@ L268-276 verbatim
omit instSize instPauliData in
@[simp] lemma pure_zero_left
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {P : Type u}
    {Q : Type u}
    [CStarAlgebra P]
    [CStarAlgebra Q]
    (b : Q) : pure (0:P) b=0 := by simp [pure]

-- @@ L277-285 verbatim
omit instSize instPauliData in
@[simp] lemma pure_zero_right
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {P : Type u}
    {Q : Type u}
    [CStarAlgebra P]
    [CStarAlgebra Q]
    (a : P) : pure a (0:Q)=0 := by simp [pure]

-- @@ L286-294 verbatim
omit instSize instPauliData in
@[simp] lemma pure_one
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {P : Type u}
    {Q : Type u}
    [CStarAlgebra P]
    [CStarAlgebra Q]
    : pure (1:P) (1:Q)=1 := by simp [pure]

-- @@ L295-304 verbatim
omit instSize instPauliData in
lemma pure_sum_left
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {P : Type u}
    {Q : Type u}
    [CStarAlgebra P]
    [CStarAlgebra Q]
    {I : Type*} [Fintype I] (f : I→P) (b : Q) :
    pure (∑ i,f i) b=∑ i,pure (f i) b := by simp only [pure,map_sum,Finset.sum_mul]

-- @@ L305-314 verbatim
omit instSize instPauliData in
lemma pure_sum_right
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {P : Type u}
    {Q : Type u}
    [CStarAlgebra P]
    [CStarAlgebra Q]
    {I : Type*} [Fintype I] (a : P) (f : I→Q) :
    pure a (∑ i,f i)=∑ i,pure a (f i) := by simp only [pure,map_sum,Finset.mul_sum]


-- @@ L316-318 verbatim
def word : (n : ℕ) → (Fin (n+1)→P) → powerPack P n
  | 0,f => f 0
  | n+1,f => pure (f 0) (word n (fun i => f i.succ))


-- @@ L320-324 verbatim
lemma word_mul (n : ℕ) (f g : Fin (n+1)→P) :
    word n f*word n g=word n (fun i => f i*g i) := by
  induction n with
  | zero => rfl
  | succ n ih => exact (pure_mul _ _ _ _).trans (congrArg (pure (f 0*g 0)) (ih _ _))

-- @@ L325-328 verbatim
lemma word_star (n : ℕ) (f : Fin (n+1)→P) : star (word n f)=word n (fun i => star (f i)) := by
  induction n with
  | zero => rfl
  | succ n ih => exact (pure_star _ _).trans (congrArg (pure (star (f 0))) (ih _))

-- @@ L329-332 verbatim
lemma word_one (n : ℕ) : word n (fun _ => (1:P))=1 := by
  induction n with
  | zero => rfl
  | succ n ih => change pure 1 (word n fun _ => (1:P))=1; rw [ih,pure_one]

-- @@ L333-343 verbatim
lemma word_zero_coordinate (n : ℕ) (f : Fin (n+1)→P) (i : Fin (n+1)) (hi : f i=0) : word n f=0 := by
  induction n with
  | zero =>
    have he : i=0 := by omega
    change f 0=0
    simpa only [he] using hi
  | succ n ih =>
    change pure (f 0) (word n (fun j => f j.succ))=0
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j,rfl⟩
    · rw [hi,pure_zero_left]
    · rw [ih _ j hi,pure_zero_right]


-- @@ L345-345 verbatim
variable {I : Type*} [Fintype I]

-- @@ L346-357 verbatim
lemma sum_word (n : ℕ) (f : I→P) :
    (∑ σ : Fin (n+1)→I,word n (fun i => f (σ i)))=word n (fun _ => ∑ a,f a) := by
  induction n with
  | zero =>
    exact (Equiv.funUnique (Fin 1) I).sum_comp f
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n+1+1) => I)).sum_comp]
    rw [Fintype.sum_prod_type]
    change (∑ a,∑ σ : Fin (n+1)→I,pure (f a) (word n (fun i => f (σ i))))=
      pure (∑ a,f a) (word n (fun _ => ∑ a,f a))
    simp_rw [← pure_sum_right,ih]
    rw [pure_sum_left]



-- @@ L360-365 verbatim
lemma word_full_comparison (n : ℕ) (c : P) (v : I→P)
    (hv : ∑ i,star (v i)*c*v i=1) :
    ∑ σ : Fin (n+1)→I,star (word n (fun i => v (σ i)))*word n (fun _ => c)*
      word n (fun i => v (σ i))=1 := by
  simp_rw [word_star,word_mul]
  rw [sum_word n (fun i => star (v i)*c*v i),hv,word_one]


-- @@ L367-367 verbatim
variable [DecidableEq I]

-- @@ L368-380 verbatim
omit [Fintype I] in
lemma word_gram (n : ℕ) (c : P) (z : I→P)
    (hz : ∀ i j,star (z i)*z j=if i=j then c else 0)
    (σ τ : Fin (n+1)→I) :
    star (word n (fun i => z (σ i)))*word n (fun i => z (τ i))=
      if σ=τ then word n (fun _ => c) else 0 := by
  rw [word_star,word_mul]
  simp_rw [hz]
  by_cases h : σ=τ
  · subst τ; simp
  · rw [ite_eq_right h]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    exact word_zero_coordinate n _ i (ite_eq_right hi)



-- @@ L383-401 verbatim
theorem auxiliary {N : ℕ} (c : P) (v : Fin N→P)
    (hv : ∑ i,star (v i)*c*v i=1) (z : Fin 2→P)
    (hz : ∀ i j,star (z i)*z j=if i=j then c else 0) :
    ∃ L : ℕ, ∃ e : powerPack P L,
      ∃ a : Fin N→powerPack P L,
      ∃ b : (Fin (L+1)→Fin N)→powerPack P L,
        (∀ i j,star (a i)*a j=if i=j then e else 0) ∧
        (∑ j,star (b j)*e*b j=1) := by
  classical
  let L := Nat.log 2 N
  have hcard : Fintype.card (Fin N) ≤ Fintype.card (Fin (L+1)→Fin 2) := by
    simp only [Fintype.card_fin,Fintype.card_fun]
    exact (Nat.lt_pow_succ_log_self (by norm_num : 1<2) N).le
  obtain ⟨ι⟩ := Function.Embedding.nonempty_of_card_le hcard
  refine ⟨L,word L (fun _ => c),fun i => word L (fun j => z (ι i j)),
    fun σ => word L (fun i => v (σ i)),?_,word_full_comparison L c v hv⟩
  intro i j
  rw [word_gram L c z hz]
  simp only [EmbeddingLike.apply_eq_iff_eq]

-- @@ L402-402 verbatim
end KirchbergRordam.GenericRW.MaxTensor

-- @@ L403-403 verbatim
namespace KirchbergRordam.GenericRW.MaxTensor

-- @@ L404-404 verbatim
open scoped BigOperators CStarAlgebra

-- @@ L405-405 verbatim
variable {P : Type*} [CStarAlgebra P]

-- @@ L406-421 verbatim
lemma word_single (n : ℕ) (j : Fin (n+1)) (a : P) :
    word n (fun i => if i=j then a else 1)=leg P n j a := by
  induction n with
  | zero => rw [Fin.eq_zero j]; rfl
  | succ n ih =>
    induction j using Fin.cases with
    | zero =>
      have he : (fun i : Fin (n+1) => if i.succ=(0:Fin (n+2)) then a else 1)=fun _=>1 := by simp
      change pure a (word n _)=includeLeft a
      rw [he,word_one]
      simp [pure]
    | succ j =>
      have he : (fun i : Fin (n+1) => if i.succ=j.succ then a else 1)=fun i=>if i=j then a else 1 := by simp
      change pure 1 (word n _)=includeRight (leg P n j a)
      rw [he,ih]
      simp [pure]

-- @@ L422-427 verbatim
lemma leg_word_mul (n : ℕ) (j : Fin (n+1)) (a : P) (f : Fin (n+1)→P) :
    leg P n j a*word n f=word n (fun i => if i=j then a*f i else f i) := by
  rw [← word_single,word_mul]
  congr 1
  funext i
  split_ifs <;> simp

-- @@ L428-428 verbatim
end KirchbergRordam.GenericRW.MaxTensor


-- @@ L430-430 verbatim
namespace KirchbergRordam.GenericRW.ConeCube

-- @@ L431-431 verbatim
open scoped CStarAlgebra BigOperators ComplexOrder

-- @@ L432-432 verbatim
open _root_.OAI.KirchbergRordam.GenericRW.MaxTensor ConeModel

-- @@ L433-440 verbatim
omit instSize instPauliData in
lemma left_fixed
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    (n : ℕ) (a b : M2) (c : Fiber n) (hab : a*b=b) :
    MatrixTensor.leftMatrix a * (MatrixTensor.leftMatrix b * MatrixTensor.rightMatrix c)=
      MatrixTensor.leftMatrix b * MatrixTensor.rightMatrix c := by
  rw [← mul_assoc,← map_mul,hab]

-- @@ L441-444 verbatim
lemma right_fixed (n : ℕ) (a : M2) (b c : Fiber n) (hbc : b*c=c) :
    MatrixTensor.rightMatrix b * (MatrixTensor.leftMatrix a * MatrixTensor.rightMatrix c)=
      MatrixTensor.leftMatrix a * MatrixTensor.rightMatrix c := by
  rw [← mul_assoc,← (MatrixTensor.legs_commute _ _).eq,mul_assoc,← map_mul,hbc]

-- @@ L445-452 verbatim
lemma repr_word_succ (n : ℕ) (f : Fin (n+2) → ConeModel.Cone) (t : Cube (n+1)) :
    repr (n+1) (word (n+1) f) t=
      MatrixTensor.leftMatrix ((f 0:C(unitInterval,M2)) (t 0))*
        MatrixTensor.rightMatrix (repr n (word n (fun i=>f i.succ)) (tail n t)) := by
  have product_eq := congrArg (fun field : C(Cube (n+1),Fiber (n+1)) => field t)
    ((repr (n+1)).map_mul (includeLeft (f 0)) (includeRight (word n (fun i=>f i.succ))))
  exact product_eq.trans (congrArg₂ (· * ·) (repr_left n (f 0) t)
    (repr_right n (word n (fun i=>f i.succ)) t))


-- @@ L454-468 verbatim
lemma repr_word_zero (n : ℕ) (f : Fin (n+1) → ConeModel.Cone) (t : Cube n) (j : Fin (n+1))
    (hj : (f j:C(unitInterval,M2)) (t j)=0) : repr n (word n f) t=0 := by
  induction n with
  | zero =>
    rw [Fin.eq_zero j] at hj
    exact hj
  | succ n ih =>
    have product_zero :
        MatrixTensor.leftMatrix (κ := PauliPower.Row n) ((f 0 : C(unitInterval,M2)) (t 0)) *
          MatrixTensor.rightMatrix (ι := Fin Size.n)
            (repr n (word n (fun index => f index.succ)) (tail n t)) = 0 := by
      induction j using Fin.cases with
      | zero => rw [hj,map_zero,zero_mul]
      | succ j => rw [ih _ (tail n t) j hj,map_zero,mul_zero]
    exact (repr_word_succ n f t).trans product_zero


-- @@ L470-481 verbatim
lemma repr_word_fix (n : ℕ) (f : Fin (n+1) → ConeModel.Cone) (t : Cube n) (j : Fin (n+1)) (b : M2)
    (hj : b*(f j:C(unitInterval,M2)) (t j)=(f j:C(unitInterval,M2)) (t j)) :
    matLeg n j b*repr n (word n f) t=repr n (word n f) t := by
  induction n with
  | zero =>
    rw [Fin.eq_zero j] at hj
    exact hj
  | succ n ih =>
    simp only [repr_word_succ]
    induction j using Fin.cases with
    | zero => exact left_fixed n _ _ _ hj
    | succ j => exact right_fixed n _ _ _ (ih _ (tail n t) j hj)

-- @@ L482-482 verbatim
end KirchbergRordam.GenericRW.ConeCube


-- @@ L484-484 verbatim
namespace KirchbergRordam.GenericRW.ConeCut

-- @@ L485-485 verbatim
open scoped CStarAlgebra ComplexOrder BigOperators

-- @@ L486-486 verbatim
open ConeModel MatrixMix

-- @@ L487-487 verbatim
local instance : PartialOrder Cone := CStarAlgebra.spectralOrder _

-- @@ L488-488 verbatim
local instance : LE Cone := (CStarAlgebra.spectralOrder Cone).toLE

-- @@ L489-489 verbatim
local instance : StarOrderedRing Cone := CStarAlgebra.spectralOrderedRing _


-- @@ L491-491 verbatim
def unit (i j : Fin Size.n) : M2 := CStarMatrix.ofMatrix (e i j)

-- @@ L492-493 verbatim
lemma unit_star (i j : Fin Size.n) : star (unit i j)=unit j i := by
  exact (map_star CStarMatrix.ofMatrixStarAlgEquiv (e i j)).symm.trans (congrArg CStarMatrix.ofMatrix (e_star i j))

-- @@ L494-499 verbatim
lemma unit_mul (i j k l : Fin Size.n) : unit i j*unit k l=if j=k then unit i l else 0 := by
  change CStarMatrix.ofMatrixStarAlgEquiv (e i j)*CStarMatrix.ofMatrixStarAlgEquiv (e k l)=_
  rw [← map_mul,e_mul]
  split_ifs
  · rfl
  · exact map_zero CStarMatrix.ofMatrixStarAlgEquiv


-- @@ L501-501 verbatim
def coeff (δ : ℝ) (t : unitInterval) : ℝ := max ((t:ℝ)-δ) 0

-- @@ L502-506 verbatim
omit instSize instPauliData in
lemma coeff_continuous
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    (δ : ℝ) : Continuous (coeff δ) := by unfold coeff; fun_prop

-- @@ L507-511 verbatim
omit instSize instPauliData in
lemma coeff_zero
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {δ : ℝ} (hδ : 0≤δ) : coeff δ 0=0 := by simp [coeff,max_eq_right (neg_nonpos.mpr hδ)]

-- @@ L512-516 verbatim
omit instSize instPauliData in
lemma coeff_nonneg
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    (δ : ℝ) (t : unitInterval) : 0≤coeff δ t := le_max_right _ _


-- @@ L518-522 verbatim
def q (δ : ℝ) (hδ : 0≤δ) : Cone :=
  ⟨⟨fun t=>coeff δ t • unit 0 0,(coeff_continuous δ).smul continuous_const⟩,by
    change coeff δ 0 • unit 0 0∈(⊥:StarSubalgebra ℂ M2)
    rw [coeff_zero hδ,zero_smul]
    exact zero_mem _⟩

-- @@ L523-527 verbatim
def z (δ : ℝ) (hδ : 0≤δ) (i : Fin Size.n) : Cone :=
  ⟨⟨fun t=>Real.sqrt (coeff δ t) • unit i 0,(coeff_continuous δ).sqrt.smul continuous_const⟩,by
    change Real.sqrt (coeff δ 0) • unit i 0∈(⊥:StarSubalgebra ℂ M2)
    rw [coeff_zero hδ,Real.sqrt_zero,zero_smul]
    exact zero_mem _⟩

-- @@ L528-535 verbatim
lemma z_gram (δ : ℝ) (hδ : 0≤δ) (i j : Fin Size.n) :
    star (z δ hδ i)*z δ hδ j=if i=j then q δ hδ else 0 := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  change star (Real.sqrt (coeff δ t) • unit i 0)*(Real.sqrt (coeff δ t) • unit j 0)=_
  rw [star_smul,star_trivial,unit_star,smul_mul_smul_comm,Real.mul_self_sqrt (coeff_nonneg δ t),unit_mul]
  split_ifs <;> simp [q]

-- @@ L536-540 verbatim
lemma q_nonneg (δ : ℝ) (hδ : 0≤δ) : 0≤q δ hδ := by
  have hz := z_gram δ hδ 0 0
  rw [ite_eq_left rfl] at hz
  rw [← hz]
  exact star_mul_self_nonneg (z δ hδ (0:Fin Size.n))


-- @@ L542-542 verbatim
def g (δ : ℝ) : Cone := scalar ⟨fun t => (CubeWeights.g δ t:ℂ),Complex.continuous_ofReal.comp (CubeWeights.g_continuous δ)⟩

-- @@ L543-551 verbatim
lemma g_nonneg (δ : ℝ) : 0≤g δ := by
  let f : C(unitInterval,ℂ) := ⟨fun t => (CubeWeights.g δ t:ℂ),Complex.continuous_ofReal.comp (CubeWeights.g_continuous δ)⟩
  have hf : 0≤f := fun t => Complex.zero_le_real.mpr (CubeWeights.g_nonneg δ t)
  have he : star (scalar (CFC.sqrt f))*scalar (CFC.sqrt f)=g δ := by
    rw [← map_star,← map_mul,(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg f)).star_eq,
      CFC.sqrt_mul_sqrt_self f hf]
    rfl
  rw [← he]
  exact star_mul_self_nonneg _

-- @@ L552-559 verbatim
lemma qg_zero {δ : ℝ} (hδ : 0<δ) : q δ hδ.le*g δ=0 := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  change (coeff δ t • unit 0 0)*(algebraMap ℂ M2 (↑(CubeWeights.g δ t)))=0
  by_cases ht : (t:ℝ)≤δ
  · rw [show coeff δ t=0 by simp [coeff,max_eq_right (sub_nonpos.mpr ht)],zero_smul,zero_mul]
  · rw [CubeWeights.g_of_large hδ t (le_of_not_ge ht),Complex.ofReal_zero,map_zero,mul_zero]

-- @@ L560-565 verbatim
lemma q_support {δ : ℝ} (hδ : 0≤δ) (t : unitInterval)
    (hq : (q δ hδ:C(unitInterval,M2)) t≠0) : δ<(t:ℝ) := by
  by_contra ht
  apply hq
  change coeff δ t • unit 0 0=0
  rw [show coeff δ t=0 by simp [coeff,max_eq_right (sub_nonpos.mpr (le_of_not_gt ht))],zero_smul]

-- @@ L566-573 verbatim
lemma g_support {δ : ℝ} (hδ : 0<δ) (t : unitInterval)
    (hg : (g δ:C(unitInterval,M2)) t≠0) : (t:ℝ)<δ/2 := by
  apply CubeWeights.g_pos hδ
  apply lt_of_le_of_ne (CubeWeights.g_nonneg δ t)
  intro hz
  apply hg
  change algebraMap ℂ M2 (↑(CubeWeights.g δ t))=0
  rw [← hz,Complex.ofReal_zero,map_zero]

-- @@ L574-577 verbatim
lemma q_fix (δ : ℝ) (hδ : 0≤δ) (t : unitInterval) :
    unit 0 0*(q δ hδ:C(unitInterval,M2)) t=(q δ hδ:C(unitInterval,M2)) t := by
  change unit 0 0*(coeff δ t • unit 0 0)=coeff δ t • unit 0 0
  rw [mul_smul_comm,unit_mul,ite_eq_left rfl]

-- @@ L578-578 verbatim
end KirchbergRordam.GenericRW.ConeCut


-- @@ L580-580 verbatim
namespace KirchbergRordam.GenericRW.ConeCube

-- @@ L581-581 verbatim
open scoped CStarAlgebra ComplexOrder BigOperators

-- @@ L582-582 verbatim
open ConeModel _root_.OAI.KirchbergRordam.GenericRW.MaxTensor


-- @@ L584-585 verbatim
def y (n : ℕ) (δ : ℝ) (hδ : 0≤δ) (j : Fin (n+1)) : Tensor n :=
  word n (fun i => if i=j then ConeCut.q δ hδ else ConeCut.g δ)

-- @@ L586-586 verbatim
local instance (n : ℕ) : PartialOrder (Tensor n) := CStarAlgebra.spectralOrder _

-- @@ L587-587 verbatim
local instance (n : ℕ) : StarOrderedRing (Tensor n) := CStarAlgebra.spectralOrderedRing _


-- @@ L589-611 verbatim
lemma x_fixes_y (n : ℕ) {δ : ℝ} (hδ : 0<δ) (j : Fin (n+1)) :
    x n δ 0 0*y n δ hδ.le j=y n δ hδ.le j := by
  apply faithful n
  rw [map_mul,repr_x]
  apply ContinuousMap.ext
  intro t
  rw [ContinuousMap.mul_apply]
  by_cases hy : repr n (y n δ hδ.le j) t=0
  · rw [hy,mul_zero]
  · have hf (i : Fin (n+1)) :
        ((if i=j then ConeCut.q δ hδ.le else ConeCut.g δ : Cone) : C(unitInterval,M2)) (t i)≠0 := by
      intro hi
      exact hy (repr_word_zero n _ t i hi)
    have hj : δ<(t j:ℝ) := ConeCut.q_support hδ.le _ (by simpa using hf j)
    have hi (i : Fin (n+1)) (hij : i≠j) : (t i:ℝ)<δ/2 :=
      ConeCut.g_support hδ _ (by simpa [hij] using hf i)
    have ht : t≠0 := by
      intro hz
      have he : (t j:ℝ)=0 := by rw [hz]; rfl
      linarith
    rw [CubeField.x_localized (family n) hδ ⟨t,ht⟩ j hj hi]
    apply repr_word_fix n _ t j (ConeCut.unit 0 0)
    simpa only [ite_true] using ConeCut.q_fix δ hδ.le (t j)


-- @@ L613-622 verbatim
omit instSize instPauliData in
lemma matrix_scalar_product
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    (n : ℕ) (a b : ℂ) :
    MatrixTensor.leftMatrix (κ:=PauliPower.Row n) (algebraMap ℂ M2 a) *
      MatrixTensor.rightMatrix (ι:=Fin Size.n) (algebraMap ℂ (Fiber n) b)=
        algebraMap ℂ (Fiber (n+1)) (a*b) := by
  rw [AlgHomClass.commutes,AlgHomClass.commutes,← map_mul]
  rfl


-- @@ L624-625 verbatim
lemma repr_one (n : ℕ) : repr n (1:Tensor n)=1 :=
  (repr n).toAlgHom.map_one


-- @@ L627-640 verbatim
lemma repr_scalar_word (n : ℕ) (f : Fin (n+1) → C(unitInterval,ℂ)) (t : Cube n) :
    repr n (word n (fun i => scalar (f i))) t = algebraMap ℂ (Fiber n) (∏ i,f i (t i)) := by
  induction n with
  | zero =>
    rw [Fin.prod_univ_succ]
    simp only [Finset.univ_eq_empty,Finset.prod_empty,mul_one]
    rfl
  | succ n ih =>
    rw [repr_word_succ,ih]
    rw [scalar_apply]
    have product_eq := matrix_scalar_product n (f 0 (t 0))
      (∏ index : Fin (n+1), f index.succ (t index.succ))
    exact product_eq.trans (congrArg (algebraMap ℂ (Fiber (n+1)))
      (Fin.prod_univ_succ (fun i => f i (t i))).symm)


-- @@ L642-653 verbatim
lemma defect_word (n : ℕ) (δ : ℝ) : 1-h n δ=word n (fun _=>ConeCut.g δ) := by
  apply faithful n
  rw [map_sub,repr_one,repr_h]
  apply ContinuousMap.ext
  intro t
  rw [ContinuousMap.sub_apply]
  change 1-CubeWeights.H δ t • (1:Fiber n)=repr n (word n (fun _=>ConeCut.g δ)) t
  rw [ConeCut.g,repr_scalar_word]
  simp only [ContinuousMap.coe_mk,← Complex.ofReal_prod]
  rw [CubeWeights.H]
  rw [Algebra.algebraMap_eq_smul_one,Complex.coe_smul]
  module

-- @@ L654-654 verbatim
end KirchbergRordam.GenericRW.ConeCube

-- @@ L655-655 verbatim
end


-- @@ L657-657 verbatim
end OAI
