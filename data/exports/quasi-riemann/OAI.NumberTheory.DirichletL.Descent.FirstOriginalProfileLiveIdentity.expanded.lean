import OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileLiveEnergy


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical BigOperators SchwartzMap

-- @@ L7-7 verbatim
namespace SevenEighths.InverseMomentFirstOriginalProfile

-- @@ L8-8 verbatim
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic

-- @@ L9-9 verbatim
open InverseMomentFirstChildWindows InverseMomentFirstProfileUniform CompletedHeight

-- @@ L10-10 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L11-11 verbatim
variable {ι : Type*} [DecidableEq ι]

-- @@ L12-12 verbatim
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

-- @@ L13-13 verbatim
variable (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))

-- @@ L14-14 verbatim
variable (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})


-- @@ L16-51 verbatim
theorem original_refined_cell_profile_identity (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (β : Ideal O→(ι→₀ℕ)→ℂ)
    (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hsom : Function.support om⊆Set.Icc a b)
    (Φ : 𝓢(ℝ,ℂ)) (K Y X theta : ℝ) (hX : 0<X)
    (k : SourceIndex) (l : ℕ) (gate : FirstOriginalOuter ι→Prop) (s : Fin 9→ℝ) (hs : ∀i,0<s i)
    (hleft : s 0*s 2*s 5*s 7=X) (hright : s 1*s 2*s 5*s 8=X) :
    let source := refinedSource p pool Q labels β cutoff Y k gate
    (∑x∈source,∑j∈firstCommonIndices pool,commonSelector p (fun _=>1) l j.2.1*
      sourceSummand p hp hcop hg β cutoff Ψ m mark
        (fun y=>normTwistedSource om theta (y/X)) Φ K x j)=
    refinedCellRows p hp hcop hg pool Q labels β cutoff Ψ m mark k l gate
      (positiveSource (priorityLogWindow om a b ha hsom true) 1 (-theta))
      (positiveSource (priorityLogWindow om a b ha hsom false) 1 theta) Φ K Y s := by
  intro source
  let W₁ := fun y=>star (normTwistedSource om theta ((s 0*s 2*s 5*s 7)*y/X))
  let W₂ := fun y=>normTwistedSource om theta ((s 1*s 2*s 5*s 8)*y/X)
  have he := original_family_profiles p hp hg source pool (fun _=>commonSelector p (fun _=>1) l)
    (coefficient p hp hcop hg Ψ m mark true) (coefficient p hp hcop hg Ψ m mark false)
    (weight p hp hcop hg β cutoff Ψ m) om a b ha hsom Φ
    (leftNorm p) (rightNorm p) (commonNorm p) (activeNorm p) K X theta
    (fun x=>divisorElement p x.1) (fun x=>x.2.2) s hs
    (by intro x hx;have hh:=original_source_positive p hp pool Q labels Y x (Finset.mem_filter.mp (refinedSource_subset p pool Q labels β cutoff Y k gate hx)).1
        exact ⟨hh.1,hh.2.1,hh.2.2.1⟩) hX hleft hright
  change _=firstFamilyPhysicalRows p hg source pool _ _ _ _ _ _ Φ _ _ _ _ K _ _ s
  rw [←he]
  have hl : s 0*s 2*s 5*s 7≠0 := hleft.trans_ne (ne_of_gt hX)
  have hr : s 1*s 2*s 5*s 8≠0 := hright.trans_ne (ne_of_gt hX)
  simp only [firstFamilyPhysicalRows,firstBlockedPhysicalRows,sourceSummand,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro j hj
  simp only [firstNormProfile,mul_div_cancel₀ _ hl,mul_div_cancel₀ _ hr]
  ring


-- @@ L53-53 verbatim
end SevenEighths.InverseMomentFirstOriginalProfile

-- @@ L54-54 verbatim
end


-- @@ L56-56 verbatim
end OAI
