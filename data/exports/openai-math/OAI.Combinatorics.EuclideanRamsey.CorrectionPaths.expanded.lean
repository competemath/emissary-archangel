import OAI.Combinatorics.EuclideanRamsey.OrbitAveraging


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe uGroup uIndex uAction uPoint


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

-- @@ L25-25 verbatim
open Filter

-- @@ L26-26 verbatim
open Set


-- @@ L28-28 verbatim
namespace EuclideanRamsey

-- @@ L29-29 verbatim
open scoped BigOperators

-- @@ L30-30 verbatim
variable {G : Type uGroup} {ι : Type uIndex} [Group G] [Fintype ι] [DecidableEq ι]

-- @@ L31-31 verbatim
namespace GradedPaths

-- @@ L32-32 verbatim
variable (P : GradedPaths ι G) (L : Subgroup G) [L.Normal]

-- @@ L33-33 verbatim
variable (hL : ∀ i,L ≤ singleFractions P.monoid P.diagonal i)


-- @@ L35-35 verbatim
def maxCost (g : G) : ℕ := Finset.univ.sup (fun i => P.singleCost i g)

-- @@ L36-37 verbatim
lemma single_le_maxCost (i : ι) (g : G) : P.singleCost i g ≤ P.maxCost g :=
  Finset.le_sup (f := fun j => P.singleCost j g) (Finset.mem_univ i)

-- @@ L38-58 verbatim
noncomputable def normalCost : NormalCost L where
  cost g := P.maxCost g
  nonneg g := Nat.cast_nonneg _
  one := by simp [maxCost,P.singleCost_one]
  inv g hg := by
    congr 1
    apply Finset.sup_congr rfl
    intro i _
    exact P.singleCost_inv i (hL i hg)
  conj g hg k := by
    congr 1
    apply Finset.sup_congr rfl
    intro i _
    exact P.singleCost_conjugate i (hL i hg) k
  mul g hg h hh := by
    rw [← Nat.cast_add]
    apply Nat.cast_le.mpr
    apply Finset.sup_le
    intro i _
    exact (P.singleCost_mul i (hL i hg) (hL i hh)).trans
      (add_le_add (P.single_le_maxCost i g) (P.single_le_maxCost i h))


-- @@ L60-70 verbatim
omit [Fintype ι] in
lemma prod_single_eq (l : List ι) (hl : l.Nodup) (g : ι → G) (i : ι) :
    ((l.map (fun j => Pi.mulSingle j (g j))).prod) i=if i∈l then g i else 1 := by
  induction l with
  | nil => simp
  | cons j l ih =>
    obtain ⟨hj,hl⟩ := List.nodup_cons.mp hl
    rw [List.map_cons,List.prod_cons,Pi.mul_apply,ih hl]
    by_cases h : i=j
    · subst j; simp [hj]
    · simp [h]


-- @@ L72-83 verbatim
include hL in
omit [L.Normal] in
lemma bounded_tuple (g : ι → G) (hg : ∀ i,g i∈L) :
    P.BoundedFraction g (∑ i,P.singleCost i (g i)) := by
  classical
  have hb := P.bounded_tuple_list (Finset.univ.toList) g (fun i => P.singleCost i (g i))
    (fun i _ => P.singleCost_bounded i (hL i (hg i)))
  have he : ((Finset.univ.toList.map (fun i => Pi.mulSingle i (g i))).prod)=g := by
    ext i
    simpa using prod_single_eq Finset.univ.toList (Finset.nodup_toList _) g i
  rw [he] at hb
  simpa using hb


-- @@ L85-96 verbatim
omit [L.Normal] in
lemma correction_cost (g : ι → G) (hg : ∀ i,g i∈L) (B : ℝ)
    (hc : ∀ i,(P.normalCost L hL).cost (g i)≤B) :
    ∃ u v m n,P.Holds u m ∧ P.Holds v n ∧ g=u*v⁻¹ ∧
      (m+n:ℕ)≤(Fintype.card ι:ℝ)*B := by
  obtain ⟨u,v,m,n,hu,hv,he,hn⟩ := P.bounded_tuple L hL g hg
  refine ⟨u,v,m,n,hu,hv,he,?_⟩
  calc
    ((m+n:ℕ):ℝ) ≤ ∑ i,(P.singleCost i (g i):ℝ) := by exact_mod_cast hn
    _ ≤ ∑ i,B := Finset.sum_le_sum (fun i _ =>
      (Nat.cast_le.mpr (P.single_le_maxCost i (g i))).trans (hc i))
    _ = _ := by simp

-- @@ L97-97 verbatim
end GradedPaths

-- @@ L98-98 verbatim
end EuclideanRamsey

-- @@ L99-99 verbatim
namespace EuclideanRamsey

-- @@ L100-100 verbatim
open scoped BigOperators

-- @@ L101-101 verbatim
variable {ι : Type uIndex} {H : Type uAction} {X : Type uPoint} [Fintype ι] [DecidableEq ι]

-- @@ L102-102 verbatim
variable [Group H] [MulAction H X] [Fintype H] [Fintype X]


-- @@ L104-112 verbatim
omit [Fintype ι] [DecidableEq ι] [Fintype H] [Fintype X] in
lemma OrbitWords.path {a : ι → FiniteEuclidean} (z : X → FiniteEuclidean)
    (f : ι → X) (q : ℝ) (hq : ∀ h : H,CopyPath a q (fun i => z (h • f i)))
    {w : X → LetterGroup} {m : ℕ} (hw : OrbitWords (H:=H) (fun x => FreeGroup.of (z x)) w m) :
    Path a (fun i => w (f i)) (q*m) := by
  induction hw with
  | diag g => simpa using (Path.diag (a:=a) g)
  | point h => simpa using (Path.copy (a:=a) _ (hq h))
  | mul _ _ ihu ihv => simpa only [Nat.cast_add,mul_add,Pi.mul_def] using ihu.mul ihv


-- @@ L114-159 verbatim
theorem averaged_equal_endpoints (a : ι → FiniteEuclidean) (ha : Function.Injective a)
    (z : X → FiniteEuclidean) (f g : ι → X) (q δ : ℝ) (hq : 0 < q) (hδ : 0 < δ)
    (hf : ∀ h : H,CopyPath a 1 (fun i => z (h • f i)))
    (hg : ∀ h : H,CopyPath a q (fun i => z (h • g i)))
    (horbit : ∀ i,SameOrbit (H:=H) (f i) (g i)) :
    ∃ w lmb μ,Path a w lmb ∧ Path a w μ ∧ 0 < lmb ∧ 0 ≤ μ ∧
      μ/lmb ≤ q+(Fintype.card ι:ℝ)*δ := by
  let N := AugKernel FiniteEuclidean
  let L := Derived N (Fintype.card ι-2)
  let P := unitGraded a
  have hL : ∀ i,L ≤ singleFractions P.monoid P.diagonal i := by
    apply derived_subset_single N (Fintype.card ι-2) ι P.monoid P.diagonal
      (unit_pair_inverse a) (unit_pair_coverage a ha)
    omega
  let c := P.normalCost L hL
  obtain ⟨w,m,hw,hm,hwm⟩ := finite_group_averaging (H:=H) N (Fintype.card ι-2)
    c (fun x => FreeGroup.of (z x)) (fun x y => letter_difference_mem (z x) (z y)) δ hδ
  let Dp : ι → LetterGroup := fun i => w (f i)
  let Dm : ι → LetterGroup := fun i => w (g i)
  have hp : Path a Dp (m:ℝ) := by simpa using hw.path z f 1 hf
  have hn : Path a Dm (q*m) := hw.path z g q hg
  let r : ι → LetterGroup := Dp⁻¹*Dm
  have hrc : ∀ i,r i∈L ∧ c.cost (r i) ≤ δ*m := by
    intro i
    obtain ⟨hmem,hcost⟩ := hwm (f i) (g i) (horbit i)
    have he : r i=(w (f i))⁻¹*(w (f i)*(w (g i))⁻¹)⁻¹*((w (f i))⁻¹)⁻¹ := by
      dsimp [r,Dp,Dm]; group
    rw [he]
    refine ⟨(inferInstance : L.Normal).conj_mem _ (L.inv_mem hmem) _,?_⟩
    rw [c.conj _ (L.inv_mem hmem),c.inv _ hmem]
    exact hcost
  obtain ⟨u,v,b,e,hu,hv,he,hbe⟩ := P.correction_cost L hL r (fun i => (hrc i).1)
    (δ*m) (fun i => (hrc i).2)
  have heq : Dp*u=Dm*v := by
    have ht := congrArg (fun t => Dp*t*v) he
    simpa [r,mul_assoc] using ht.symm
  have h₁ : Path a (Dp*u) ((m:ℝ)+b) := hp.mul (UnitWords.path hu)
  have h₂ : Path a (Dp*u) (q*m+e) := by rw [heq]; exact hn.mul (UnitWords.path hv)
  have hm' : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hb : (0:ℝ) ≤ b := Nat.cast_nonneg _
  have he' : (0:ℝ) ≤ e := Nat.cast_nonneg _
  refine ⟨_,_,_,h₁,h₂,by positivity,by positivity,?_⟩
  apply (div_le_iff₀ (by positivity : (0:ℝ) < m+b)).mpr
  have hc' : (b:ℝ)+e ≤ (Fintype.card ι:ℝ)*(δ*m) := by simpa only [Nat.cast_add] using hbe
  have hcd : 0 ≤ (Fintype.card ι:ℝ)*δ := mul_nonneg (Nat.cast_nonneg _) hδ.le
  nlinarith

-- @@ L160-160 verbatim
end EuclideanRamsey

-- @@ L161-161 verbatim
namespace EuclideanRamsey

-- @@ L162-162 verbatim
open scoped BigOperators


-- @@ L164-166 verbatim
noncomputable def permute {ℓ : ℕ} (σ : Equiv.Perm (Fin ℓ)) :
    EuclideanSpace ℝ (Fin ℓ) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin ℓ) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ

-- @@ L167-168 verbatim
@[simp] lemma permute_apply {ℓ : ℕ} (σ : Equiv.Perm (Fin ℓ))
    (x : EuclideanSpace ℝ (Fin ℓ)) (j : Fin ℓ) : permute σ x j=x (σ.symm j) := rfl

-- @@ L169-170 verbatim
lemma permute_mul {ℓ : ℕ} (σ τ : Equiv.Perm (Fin ℓ)) (x : EuclideanSpace ℝ (Fin ℓ)) :
    permute (σ*τ) x=permute σ (permute τ x) := by ext j; rfl

-- @@ L171-172 verbatim
@[simp] lemma permute_one {ℓ : ℕ} (x : EuclideanSpace ℝ (Fin ℓ)) :
    permute 1 x=x := by ext j; rfl


-- @@ L174-218 verbatim
theorem permutation_equal_endpoints {s d ℓ : ℕ} (a : Fin s → EuclideanSpace ℝ (Fin d))
    (ha : Function.Injective a) (f g : Fin s → EuclideanSpace ℝ (Fin ℓ))
    (q δ : ℝ) (hq : 0 < q) (hδ : 0 < δ)
    (hf : ∀ i j,‖f i-f j‖^2=‖a i-a j‖^2)
    (hg : ∀ i j,‖g i-g j‖^2=q*‖a i-a j‖^2)
    (hperm : ∀ i,∃ σ : Equiv.Perm (Fin ℓ),∀ x,g i (σ x)=f i x) :
    ∃ w lmb μ,Path (fun i => FiniteEuclidean.embed d (a i)) w lmb ∧
      Path (fun i => FiniteEuclidean.embed d (a i)) w μ ∧ 0 < lmb ∧ 0 ≤ μ ∧ μ/lmb ≤ q+s*δ := by
  classical
  choose σ hσ using hperm
  let H := Equiv.Perm (Fin ℓ)
  let X := H×Fin s
  let : MulAction H X :=
    { smul := fun h x => (h*x.1,x.2)
      one_smul := by intro x; exact Prod.ext (one_mul _) rfl
      mul_smul := by intro h k x; exact Prod.ext (mul_assoc _ _ _) rfl }
  let z : X → FiniteEuclidean := fun x => FiniteEuclidean.embed ℓ (permute x.1 (f x.2))
  have hσ' (i : Fin s) : permute (σ i) (f i)=g i := by
    ext j
    simpa using (hσ i ((σ i).symm j)).symm
  have hcopy (h : H) (i : Fin s) :
      z (h • ((σ i,i):X))=FiniteEuclidean.embed ℓ (permute h (g i)) := by
    change FiniteEuclidean.embed ℓ (permute (h*σ i) (f i))=_
    rw [permute_mul,hσ']
  have ht := averaged_equal_endpoints (H:=H) (X:=X) (fun i => FiniteEuclidean.embed d (a i))
    ((FiniteEuclidean.embed d).injective.comp ha) z (fun i => (1,i)) (fun i => (σ i,i))
    q δ hq hδ
  simp only [Fintype.card_fin] at ht
  apply ht
  · intro h
    refine ⟨zero_le_one,?_⟩
    intro i j
    change ‖FiniteEuclidean.embed ℓ (permute (h*1) (f i))-
      FiniteEuclidean.embed ℓ (permute (h*1) (f j))‖^2=_
    simp only [mul_one,← map_sub,LinearIsometry.norm_map,LinearIsometryEquiv.norm_map,one_mul]
    exact hf i j
  · intro h
    refine ⟨hq.le,?_⟩
    intro i j
    dsimp only
    rw [hcopy h i,hcopy h j]
    simp only [← map_sub,LinearIsometry.norm_map,LinearIsometryEquiv.norm_map]
    exact hg i j
  · intro i
    exact ⟨σ i,by change (σ i*1,i)=(σ i,i); simp⟩

-- @@ L219-219 verbatim
end EuclideanRamsey


-- @@ L221-221 verbatim
end


-- @@ L223-223 verbatim
end OAI
