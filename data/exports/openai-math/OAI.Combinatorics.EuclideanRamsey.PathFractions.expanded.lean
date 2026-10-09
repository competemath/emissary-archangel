import OAI.Combinatorics.EuclideanRamsey.FiniteEuclidean


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe uGroup uIndex


-- @@ L7-7 verbatim
noncomputable section


-- @@ L9-9 verbatim
open scoped TensorProduct RealInnerProductSpace

-- @@ L10-10 verbatim
open scoped BigOperators

-- @@ L11-11 verbatim
open Real Filter Topology MeasureTheory Polynomial

-- @@ L12-12 verbatim
open Matrix MeasureTheory

-- @@ L13-13 verbatim
open MeasureTheory

-- @@ L14-14 verbatim
open Matrix

-- @@ L15-15 verbatim
open scoped MatrixOrder Matrix.Norms.L2Operator

-- @@ L16-16 verbatim
open MeasureTheory Matrix

-- @@ L17-17 verbatim
open scoped TensorProduct

-- @@ L18-18 verbatim
open scoped BigOperators Pointwise Topology

-- @@ L19-19 verbatim
open MeasureTheory Filter

-- @@ L20-20 verbatim
open scoped BigOperators Pointwise

-- @@ L21-21 verbatim
open scoped BigOperators Topology

-- @@ L22-22 verbatim
open scoped TensorProduct BigOperators

-- @@ L23-23 verbatim
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

-- @@ L24-24 verbatim
open scoped BigOperators RealInnerProductSpace


-- @@ L26-26 verbatim
open scoped BigOperators

-- @@ L27-27 verbatim
namespace EuclideanRamsey

-- @@ L28-28 verbatim
section Fractions

-- @@ L29-29 verbatim
variable {G : Type uGroup} {ι : Type uIndex} [Group G] [DecidableEq ι]


-- @@ L31-32 verbatim
def RightFraction (M : Submonoid (ι → G)) (z : ι → G) : Prop :=
  ∃ u ∈ M,∃ v ∈ M,z=u*v⁻¹


-- @@ L34-34 verbatim
def HasDiagonal (M : Submonoid (ι → G)) : Prop := ∀ g : G,(fun _ => g)∈M


-- @@ L36-37 verbatim
def PairInverse (M : Submonoid (ι → G)) : Prop :=
  ∀ i j : ι,i≠j → ∀ v∈M,∃ b∈M,v i*b i=1 ∧ v j*b j=1


-- @@ L39-41 verbatim
omit [DecidableEq ι] in
lemma RightFraction.one (M : Submonoid (ι → G)) : RightFraction M 1 :=
  ⟨1,M.one_mem,1,M.one_mem,by simp⟩

-- @@ L42-46 verbatim
omit [DecidableEq ι] in
lemma RightFraction.inv {M : Submonoid (ι → G)} {z : ι → G}
    (h : RightFraction M z) : RightFraction M z⁻¹ := by
  obtain ⟨u,hu,v,hv,rfl⟩ := h
  exact ⟨v,hv,u,hu,by group⟩

-- @@ L47-55 verbatim
omit [DecidableEq ι] in
lemma RightFraction.conjugate {M : Submonoid (ι → G)} (hM : HasDiagonal M)
    {z : ι → G} (h : RightFraction M z) (g : G) :
    RightFraction M (fun i => g*z i*g⁻¹) := by
  obtain ⟨u,hu,v,hv,rfl⟩ := h
  refine ⟨(fun _ => g)*u,M.mul_mem (hM g) hu,(fun _ => g)*v,M.mul_mem (hM g) hv,?_⟩
  ext i
  simp only [Pi.mul_apply,Pi.inv_apply]
  group


-- @@ L57-60 verbatim
lemma conjugate_single (i : ι) (g h : G) :
    (fun j => g*(Pi.mulSingle i h : ι → G) j*g⁻¹)=Pi.mulSingle i (g*h*g⁻¹) := by
  ext j
  by_cases hj : j=i <;> simp [hj]


-- @@ L62-76 verbatim
lemma RightFraction.mul_single {M : Submonoid (ι → G)} (hM : HasDiagonal M)
    {z : ι → G} (hz : RightFraction M z) (i : ι) {g : G}
    (hg : RightFraction M (Pi.mulSingle i g)) : RightFraction M (z*Pi.mulSingle i g) := by
  obtain ⟨u,hu,v,hv,rfl⟩ := hz
  have hh := hg.conjugate hM (v i)⁻¹
  rw [conjugate_single,inv_inv] at hh
  obtain ⟨a,ha,b,hb,he⟩ := hh
  refine ⟨u*a,M.mul_mem hu ha,v*b,M.mul_mem hv hb,?_⟩
  have ht : v⁻¹*Pi.mulSingle i g = Pi.mulSingle i ((v i)⁻¹*g*v i)*v⁻¹ := by
    ext j
    by_cases hj : j=i
    · subst j; simp
    · simp [Pi.mulSingle_eq_of_ne hj]
  rw [mul_assoc,ht,he]
  group


-- @@ L78-88 verbatim
def singleFractions (M : Submonoid (ι → G)) (hM : HasDiagonal M) (i : ι) : Subgroup G where
  carrier := {g | RightFraction M (Pi.mulSingle i g)}
  one_mem' := by simpa using RightFraction.one M
  mul_mem' {a b} ha hb := by
    change RightFraction M (Pi.mulSingle i (a*b))
    rw [Pi.mulSingle_mul]
    exact ha.mul_single hM i hb
  inv_mem' {a} ha := by
    change RightFraction M (Pi.mulSingle i a⁻¹)
    rw [Pi.mulSingle_inv]
    exact ha.inv


-- @@ L90-95 verbatim
instance singleFractions_normal (M : Submonoid (ι → G)) (hM : HasDiagonal M) (i : ι) :
    (singleFractions M hM i).Normal where
  conj_mem g hg k := by
    change RightFraction M (Pi.mulSingle i (k*g*k⁻¹))
    rw [← conjugate_single]
    exact hg.conjugate hM k


-- @@ L97-117 verbatim
lemma RightFraction.mul_pair {M : Submonoid (ι → G)} (hM : PairInverse M)
    {z t : ι → G} (hz : RightFraction M z) (ht : RightFraction M t)
    (i j : ι) (hij : i≠j) (hs : ∀ l,l≠i → l≠j → t l=1) :
    RightFraction M (z*t) := by
  obtain ⟨u,hu,v,hv,rfl⟩ := hz
  obtain ⟨c,hc,d,hd,rfl⟩ := ht
  obtain ⟨b,hb,hi,hj⟩ := hM i j hij v hv
  have hcomm : Commute (v*b) (c*d⁻¹) := by
    ext l
    by_cases hli : l=i
    · subst l; simp only [Pi.mul_apply,Pi.inv_apply] at *; rw [hi]; simp
    by_cases hlj : l=j
    · subst l; simp only [Pi.mul_apply,Pi.inv_apply] at *; rw [hj]; simp
    · have hh := hs l hli hlj
      change v l*b l*(c l*(d l)⁻¹) = (c l*(d l)⁻¹)*(v l*b l)
      change c l*(d l)⁻¹=1 at hh
      rw [hh]; simp
  refine ⟨u*b*c,M.mul_mem (M.mul_mem hu hb) hc,(v*b)*d,M.mul_mem (M.mul_mem hv hb) hd,?_⟩
  have he : u*v⁻¹ = (u*b)*(v*b)⁻¹ := by group
  rw [he,mul_assoc,hcomm.inv_left.eq]
  group

-- @@ L118-118 verbatim
end Fractions

-- @@ L119-119 verbatim
end EuclideanRamsey

-- @@ L120-120 verbatim
namespace EuclideanRamsey

-- @@ L121-121 verbatim
open scoped BigOperators

-- @@ L122-122 verbatim
variable {G : Type uGroup} {ι : Type uIndex} [Group G] [DecidableEq ι]


-- @@ L124-127 verbatim
structure GradedPaths (ι : Type uIndex) (G : Type uGroup) [Group G] where
  Holds : (ι → G) → ℕ → Prop
  diag : ∀ g,Holds (fun _ => g) 0
  mul : ∀ {u v m n},Holds u m → Holds v n → Holds (u*v) (m+n)

-- @@ L128-128 verbatim
namespace GradedPaths

-- @@ L129-129 verbatim
variable (P : GradedPaths ι G)

-- @@ L130-133 verbatim
def monoid : Submonoid (ι → G) where
  carrier := {u | ∃ n,P.Holds u n}
  one_mem' := ⟨0,P.diag 1⟩
  mul_mem' := by rintro u v ⟨m,hm⟩ ⟨n,hn⟩; exact ⟨m+n,P.mul hm hn⟩

-- @@ L134-135 verbatim
omit [DecidableEq ι] in
lemma diagonal : HasDiagonal P.monoid := fun g => ⟨0,P.diag g⟩


-- @@ L137-138 verbatim
def BoundedFraction (z : ι → G) (c : ℕ) : Prop :=
  ∃ (u v : ι → G) (m n : ℕ),P.Holds u m ∧ P.Holds v n ∧ z=u*v⁻¹ ∧ m+n≤c

-- @@ L139-143 verbatim
omit [DecidableEq ι] in
lemma bounded_exists {z : ι → G} (h : RightFraction P.monoid z) :
    ∃ c,P.BoundedFraction z c := by
  obtain ⟨u,⟨m,hm⟩,v,⟨n,hn⟩,he⟩ := h
  exact ⟨m+n,u,v,m,n,hm,hn,he,le_rfl⟩

-- @@ L144-148 verbatim
omit [DecidableEq ι] in
lemma bounded_fraction {z : ι → G} {c : ℕ} (h : P.BoundedFraction z c) :
    RightFraction P.monoid z := by
  obtain ⟨u,v,m,n,hm,hn,he,_⟩ := h
  exact ⟨u,⟨m,hm⟩,v,⟨n,hn⟩,he⟩

-- @@ L149-151 verbatim
omit [DecidableEq ι] in
lemma bounded_one : P.BoundedFraction 1 0 :=
  ⟨1,1,0,0,P.diag 1,P.diag 1,by simp,le_rfl⟩

-- @@ L152-156 verbatim
omit [DecidableEq ι] in
lemma bounded_mono {z : ι → G} {c d : ℕ} (h : P.BoundedFraction z c) (hc : c≤d) :
    P.BoundedFraction z d := by
  obtain ⟨u,v,m,n,hm,hn,he,hc'⟩ := h
  exact ⟨u,v,m,n,hm,hn,he,hc'.trans hc⟩

-- @@ L157-161 verbatim
omit [DecidableEq ι] in
lemma bounded_inv {z : ι → G} {c : ℕ} (h : P.BoundedFraction z c) :
    P.BoundedFraction z⁻¹ c := by
  obtain ⟨u,v,m,n,hm,hn,rfl,hc⟩ := h
  exact ⟨v,u,n,m,hn,hm,by group,by omega⟩

-- @@ L162-169 verbatim
omit [DecidableEq ι] in
lemma bounded_conjugate {z : ι → G} {c : ℕ} (h : P.BoundedFraction z c) (g : G) :
    P.BoundedFraction (fun i => g*z i*g⁻¹) c := by
  obtain ⟨u,v,m,n,hm,hn,rfl,hc⟩ := h
  refine ⟨(fun _ => g)*u,(fun _ => g)*v,m,n,?_,?_,?_,hc⟩
  · simpa using P.mul (P.diag g) hm
  · simpa using P.mul (P.diag g) hn
  · ext i; simp only [Pi.mul_apply,Pi.inv_apply]; group

-- @@ L170-184 verbatim
lemma bounded_mul_single {z : ι → G} {c d : ℕ} (hz : P.BoundedFraction z c)
    (i : ι) {g : G} (hg : P.BoundedFraction (Pi.mulSingle i g) d) :
    P.BoundedFraction (z*Pi.mulSingle i g) (c+d) := by
  obtain ⟨u,v,m,n,hm,hn,rfl,hc⟩ := hz
  have hh := P.bounded_conjugate hg (v i)⁻¹
  rw [conjugate_single,inv_inv] at hh
  obtain ⟨a,b,k,l,hk,hl,he,hd⟩ := hh
  refine ⟨u*a,v*b,m+k,n+l,P.mul hm hk,P.mul hn hl,?_,by omega⟩
  have ht : v⁻¹*Pi.mulSingle i g = Pi.mulSingle i ((v i)⁻¹*g*v i)*v⁻¹ := by
    ext j
    by_cases hj : j=i
    · subst j; simp
    · simp [Pi.mulSingle_eq_of_ne hj]
  rw [mul_assoc,ht,he]
  group


-- @@ L186-186 verbatim
def singleCost (i : ι) (g : G) : ℕ := sInf {c | P.BoundedFraction (Pi.mulSingle i g) c}

-- @@ L187-189 verbatim
lemma singleCost_bounded (i : ι) {g : G} (hg : g∈singleFractions P.monoid P.diagonal i) :
    P.BoundedFraction (Pi.mulSingle i g) (P.singleCost i g) :=
  Nat.sInf_mem (P.bounded_exists hg)

-- @@ L190-191 verbatim
lemma singleCost_le (i : ι) {g : G} {c : ℕ} (hc : P.BoundedFraction (Pi.mulSingle i g) c) :
    P.singleCost i g ≤ c := Nat.sInf_le hc

-- @@ L192-195 verbatim
lemma singleCost_one (i : ι) : P.singleCost i 1=0 := by
  apply Nat.eq_zero_of_le_zero
  apply P.singleCost_le
  simpa using P.bounded_one

-- @@ L196-204 verbatim
lemma singleCost_inv (i : ι) {g : G} (hg : g∈singleFractions P.monoid P.diagonal i) :
    P.singleCost i g⁻¹=P.singleCost i g := by
  apply Nat.le_antisymm
  · apply P.singleCost_le
    rw [Pi.mulSingle_inv]
    exact P.bounded_inv (P.singleCost_bounded i hg)
  · apply P.singleCost_le
    have he := P.bounded_inv (P.singleCost_bounded i ((singleFractions _ _ i).inv_mem hg))
    simpa only [Pi.mulSingle_inv,inv_inv] using he

-- @@ L205-214 verbatim
lemma singleCost_conjugate (i : ι) {g : G} (hg : g∈singleFractions P.monoid P.diagonal i) (k : G) :
    P.singleCost i (k*g*k⁻¹)=P.singleCost i g := by
  have hle {g : G} (hg : g∈singleFractions P.monoid P.diagonal i) (k : G) :
      P.singleCost i (k*g*k⁻¹) ≤ P.singleCost i g := by
    apply P.singleCost_le
    rw [← conjugate_single]
    exact P.bounded_conjugate (P.singleCost_bounded i hg) k
  apply Nat.le_antisymm (hle hg k)
  have he := hle ((singleFractions_normal P.monoid P.diagonal i).conj_mem g hg k) k⁻¹
  simpa only [inv_inv,inv_mul_cancel_left,mul_assoc,mul_inv_cancel_right,inv_mul_cancel,mul_one] using he

-- @@ L215-220 verbatim
lemma singleCost_mul (i : ι) {g h : G}
    (hg : g∈singleFractions P.monoid P.diagonal i) (hh : h∈singleFractions P.monoid P.diagonal i) :
    P.singleCost i (g*h)≤P.singleCost i g+P.singleCost i h := by
  apply P.singleCost_le
  rw [Pi.mulSingle_mul]
  exact P.bounded_mul_single (P.singleCost_bounded i hg) i (P.singleCost_bounded i hh)


-- @@ L222-241 verbatim
lemma bounded_tuple_list (l : List ι) (z : ι → G) (c : ι → ℕ)
    (h : ∀ i∈l,P.BoundedFraction (Pi.mulSingle i (z i)) (c i)) :
    P.BoundedFraction ((l.map (fun i => Pi.mulSingle i (z i))).prod) ((l.map c).sum) := by
  induction l with
  | nil => simpa using P.bounded_one
  | cons i l ih =>
    have ht := (P.bounded_mul_single (ih (by intro j hj; exact h j (by simp [hj]))) i (h i (by simp)))
    have he : (l.map (fun j => Pi.mulSingle j (z j))).prod*Pi.mulSingle i (z i)=
        Pi.mulSingle i (z i)*(l.map (fun j => Pi.mulSingle j (z j))).prod := by
      apply Commute.symm
      apply Commute.list_prod_right
      intro y hy
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp hy
      by_cases hji : j=i
      · subst j; exact Commute.refl _
      · ext k
        by_cases hki : k=i
        · subst k; simp [Pi.mulSingle_eq_of_ne (Ne.symm hji)]
        · simp [Pi.mulSingle_eq_of_ne hki]
    simpa [he,Nat.add_comm] using ht

-- @@ L242-242 verbatim
end GradedPaths

-- @@ L243-243 verbatim
end EuclideanRamsey


-- @@ L245-245 verbatim
end


-- @@ L247-247 verbatim
end OAI
