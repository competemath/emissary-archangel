import OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileLiveSource
import OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileAssembly


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators SchwartzMap

-- @@ L8-8 verbatim
namespace SevenEighths.InverseMomentFirstOriginalProfile

-- @@ L9-9 verbatim
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic

-- @@ L10-10 verbatim
open InverseMomentFirstChildWindows InverseSecondSourceBlocks

-- @@ L11-11 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L12-12 verbatim
variable {ι : Type*} [DecidableEq ι]

-- @@ L13-13 verbatim
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]


-- @@ L15-15 verbatim
abbrev JointKey := SourceIndex × ℕ × ℕ


-- @@ L17-19 verbatim
def jointKey (x : OriginalIndex ι) (j : FirstCommonIndex ι) : JointKey :=
  (sourceIndex (originalNorms p) x,dyadIndex (primeProductNorm p j.2.1),
    dyadIndex (InverseFirstGlobalCaps.jNorm p x.1))


-- @@ L21-24 verbatim
def liveJointKeys (S : Finset (OriginalIndex ι)) (pool : Finset ι)
    (term : OriginalIndex ι→FirstCommonIndex ι→ℂ) : Finset JointKey :=
  ((S×ˢfirstCommonIndices pool).filter (fun x=>term x.1 x.2≠0)).image
    (fun x=>jointKey p x.1 x.2)


-- @@ L26-42 verbatim
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma sum_live_joint_cells (S : Finset (OriginalIndex ι)) (pool : Finset ι)
    (term : OriginalIndex ι→FirstCommonIndex ι→ℂ) :
    (∑x∈S,∑j∈firstCommonIndices pool,term x j)=
      ∑k∈liveJointKeys p S pool term,∑x∈S,∑j∈firstCommonIndices pool,
        if jointKey p x j=k then term x j else 0 := by
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hz : term x j=0
  · simp [hz]
  · have hk : jointKey p x j∈liveJointKeys p S pool term :=
      Finset.mem_image.mpr ⟨(x,j),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx,hj⟩,hz⟩,rfl⟩
    simp [hk]


-- @@ L44-51 verbatim
lemma sourceSummand_zero_of_weight (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (β : Ideal O→(ι→₀ℕ)→ℂ) (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (x : OriginalIndex ι) (j : FirstCommonIndex ι) (hx : firstOriginalWeight p β cutoff x.1 x.2=0) :
    sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K x j=0 := by
  simp [sourceSummand,weight,retainedCubeWeight,hx]


-- @@ L53-76 verbatim
lemma joint_cell_eq_refined (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O→(ι→₀ℕ)→ℂ) (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K Y : ℝ)
    (k : JointKey) :
    let S := firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y
    let term := sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K
    (∑x∈S,∑j∈firstCommonIndices pool,if jointKey p x j=k then term x j else 0)=
      ∑x∈refinedSource p pool Q labels β cutoff Y k.1 (labelGate p k.2.2),
        ∑j∈firstCommonIndices pool,commonSelector p (fun _=>1) k.2.1 j.2.1*term x j := by
  intro S term
  simp only [refinedSource,sourceCell,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hw : firstOriginalWeight p β cutoff x.1 x.2=0
  · have ht : ∀j,term x j=0 := fun j=>sourceSummand_zero_of_weight p hp hcop hg β cutoff Ψ m mark W Φ K x j hw
    simp [ht,hw]
  · by_cases hs : sourceIndex (originalNorms p) x=k.1
    · by_cases hj : dyadIndex (InverseFirstGlobalCaps.jNorm p x.1)=k.2.2
      · simp [jointKey,hs,hj,labelGate,hw,Prod.ext_iff,commonSelector,ite_mul]
      · simp [jointKey,hs,hj,labelGate,Prod.ext_iff]
    · simp [jointKey,hs,Prod.ext_iff]


-- @@ L78-96 verbatim
theorem original_retained_joint_partition (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O→(ι→₀ℕ)→ℂ) (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K Y : ℝ)
    (s : Fin 9→ℝ) (hs : ∀i,0<s i) :
    let S := firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y
    let term := sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K
    originalRetainedFamily p hp hcop hg pool Q labels β Ψ m mark W Φ K Y cutoff s=
      ∑k∈liveJointKeys p S pool term,
        ∑x∈refinedSource p pool Q labels β cutoff Y k.1 (labelGate p k.2.2),
          ∑j∈firstCommonIndices pool,commonSelector p (fun _=>1) k.2.1 j.2.1*term x j := by
  intro S term
  rw [original_retained_sum p hp hcop hg pool Q labels β Ψ m mark W Φ K Y cutoff s hs,
    sum_live_joint_cells p S pool term]
  apply Finset.sum_congr rfl
  intro k hk
  exact joint_cell_eq_refined p hp hcop hg pool Q labels β cutoff Ψ m mark W Φ K Y k


-- @@ L98-98 verbatim
end SevenEighths.InverseMomentFirstOriginalProfile

-- @@ L99-99 verbatim
end


-- @@ L101-101 verbatim
end OAI
