import OAI.Geometry.PinnedDistances.BoundedContradiction


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u1 u2 u3


-- @@ L7-7 verbatim
section

-- @@ L8-8 verbatim
noncomputable section

-- @@ L9-9 verbatim
open Filter

-- @@ L10-10 verbatim
open scoped Topology

-- @@ L11-11 verbatim
namespace WeakPinned


-- @@ L13-20 verbatim
lemma sequence_bounded_subsequence (W : ℕ → ℝ) (hW : ¬Tendsto W atTop atTop)
    (p : ℕ → Prop) (hp : ∀ᶠ n in atTop,p n) :
    ∃ (φ : ℕ → ℕ) (C : ℝ),Tendsto φ atTop atTop ∧ 0≤C ∧ ∀ n,W (φ n)≤C ∧ p (φ n) := by
  rw [tendsto_atTop] at hW
  push Not at hW
  obtain ⟨C,hC⟩ := hW
  obtain ⟨φ,hφ,hφC⟩ := exists_seq_forall_of_frequently (hC.and_eventually hp)
  exact ⟨φ,max C 0,hφ,le_max_right _ _,fun n => ⟨(hφC n).1.le.trans (le_max_left _ _),(hφC n).2⟩⟩


-- @@ L22-22 verbatim
end WeakPinned


-- @@ L24-24 verbatim
end

-- @@ L25-25 verbatim
end

-- @@ L26-26 verbatim
section

-- @@ L27-27 verbatim
noncomputable section

-- @@ L28-28 verbatim
open Filter

-- @@ L29-29 verbatim
open scoped Topology

-- @@ L30-30 verbatim
namespace WeakPinned

-- @@ L31-31 verbatim
open Global


-- @@ L33-34 verbatim
variable {V : ℕ → Type u1} {I : ℕ → Type u2} {K : ℕ → Type u3} [∀ j,Fintype (V j)] [∀ j,Fintype (I j)] [∀ j,DecidableEq (V j)]
  [∀ j,Field (K j)] [∀ j,NumberField (K j)]


-- @@ L36-62 verbatim
/-- Both alternatives of the genuine arithmetic sequence have been eliminated. -/
theorem arithmetic_sequence_impossible
    (G : ∀ j,Core.Fibers (V j) (I j)) (θ γ c : ℝ) (η : ℕ → ℝ)
    (Z₁ Z₂ : ∀ j,V j → K j) (h₁ : ∀ j,Function.Injective (Z₁ j)) (h₂ : ∀ j,Function.Injective (Z₂ j))
    (hθ : 0<θ) (hγ : 0<γ) (hγ1 : γ<1) (hc : 0<c) (hcγ : c<γ)
    (hn : Tendsto (fun j => (Fintype.card (V j):ℝ)) atTop atTop)
    (hη : Tendsto η atTop (𝓝 0)) (hη0 : ∀ j,0≤η j) (hηb : ∀ j,η j≤θ/2)
    (hG : ∀ j,PreparedGraph (V j) (I j) (G j) θ γ c (η j))
    (t : ∀ j,I j → K j) (ht : ∀ j e y,y∈(G j).targets e →
      (Z₁ j ((G j).source e)-Z₁ j y)*(Z₂ j ((G j).source e)-Z₂ j y)=t j e) : False := by
  let W := fun j => overlapScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)
  let A := fun j => potentialScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)
  by_cases htop : Tendsto W atTop atTop
  · exact arithmetic_no_unbounded G θ γ c η Z₁ Z₂ h₁ h₂ hθ hγ hγ1 hc hcγ hn hη hη0 hηb hG t ht htop
  have hcomp := arithmetic_scale_comparison G θ γ c η Z₁ Z₂ h₁ h₂ hθ hγ hγ1 hcγ hn hη hη0 hηb hG t ht
  obtain ⟨φ,C,hφ,hC,hbound⟩ := sequence_bounded_subsequence W htop
    (fun j => A j≤(64+8/θ)*(W j+1)) hcomp
  apply arithmetic_no_bounded (fun j => G (φ j)) θ γ c (η ∘ φ)
    (fun j => Z₁ (φ j)) (fun j => Z₂ (φ j)) (fun j => h₁ (φ j)) (fun j => h₂ (φ j))
    hθ hγ hγ1 hc hcγ (hn.comp hφ) (hη.comp hφ) (fun j => hη0 (φ j)) (fun j => hηb (φ j))
    (fun j => hG (φ j)) (fun j => t (φ j)) (fun j => ht (φ j))
    (C+(64+8/θ)*(C+1)) (by positivity)
  intro j
  change W (φ j)+A (φ j)≤_
  have hA := (hbound j).2.trans (mul_le_mul_of_nonneg_left
    (show W (φ j)+1≤C+1 by linarith [(hbound j).1]) (by positivity : 0≤64+8/θ))
  linarith [(hbound j).1]


-- @@ L64-64 verbatim
end WeakPinned


-- @@ L66-66 verbatim
end

-- @@ L67-67 verbatim
end


-- @@ L69-69 verbatim
end OAI
