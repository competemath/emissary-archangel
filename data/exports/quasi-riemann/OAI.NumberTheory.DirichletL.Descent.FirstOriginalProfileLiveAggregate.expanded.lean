import OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileLiveIdentity
import OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileLiveCount
import OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileScales


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open scoped Classical BigOperators SchwartzMap

-- @@ L9-9 verbatim
namespace SevenEighths.InverseMomentFirstOriginalProfile

-- @@ L10-10 verbatim
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic

-- @@ L11-11 verbatim
open InverseMomentFirstChildWindows InverseMomentFirstProfileUniform CompletedHeight

-- @@ L12-12 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L13-13 verbatim
variable {ι : Type*} [DecidableEq ι]

-- @@ L14-14 verbatim
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

-- @@ L15-15 verbatim
variable (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))

-- @@ L16-16 verbatim
variable (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})


-- @@ L18-41 verbatim
theorem original_retained_joint_profile_bound (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (β : Ideal O→(ι→₀ℕ)→ℂ)
    (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hsom : Function.support om⊆Set.Icc a b)
    (Φ : 𝓢(ℝ,ℂ)) (K Y X theta : ℝ) (hX : 0<X)
    (reference : Fin 9→ℝ) (href : ∀i,0<reference i) :
    let source := firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y
    let W := fun y=>normTwistedSource om theta (y/X)
    let term := sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K
    ‖originalRetainedFamily p hp hcop hg pool Q labels β Ψ m mark W Φ K Y cutoff reference‖≤
      ∑k∈liveJointKeys p source pool term,
        ‖refinedCellRows p hp hcop hg pool Q labels β cutoff Ψ m mark k.1 k.2.1 (labelGate p k.2.2)
          (positiveSource (priorityLogWindow om a b ha hsom true) 1 (-theta))
          (positiveSource (priorityLogWindow om a b ha hsom false) 1 theta) Φ K Y (physicalScales X k.1 k.2.1)‖ := by
  intro source W term
  rw [original_retained_joint_partition p hp hcop hg pool Q labels β cutoff Ψ m mark W Φ K Y reference href]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  have hp₁ := (physicalScales_products X k.1 k.2.1).1
  have hp₂ := (physicalScales_products X k.1 k.2.1).2
  rw [original_refined_cell_profile_identity p hp hcop hg pool Q labels β cutoff Ψ m mark om a b ha hsom
    Φ K Y X theta hX k.1 k.2.1 (labelGate p k.2.2) (physicalScales X k.1 k.2.1) (physicalScales_pos X hX k.1 k.2.1) hp₁ hp₂]


-- @@ L43-43 verbatim
end SevenEighths.InverseMomentFirstOriginalProfile

-- @@ L44-44 verbatim
end


-- @@ L46-46 verbatim
end OAI
