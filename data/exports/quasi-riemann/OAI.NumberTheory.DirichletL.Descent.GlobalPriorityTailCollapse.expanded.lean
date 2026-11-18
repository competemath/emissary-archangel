import OAI.NumberTheory.DirichletL.Descent.WholePriorityParentBounds
import OAI.NumberTheory.DirichletL.Descent.GlobalPrioritySource


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators SchwartzMap

-- @@ L8-8 verbatim
namespace SevenEighths.InverseMomentGlobalPriorityTail

-- @@ L9-9 verbatim
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents

-- @@ L10-10 verbatim
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion

-- @@ L11-11 verbatim
open InversePrioritySecondSource InverseSecondPrincipalCaller InversePrincipalEnergy

-- @@ L12-12 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L13-13 verbatim
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}

-- @@ L14-15 verbatim
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})


-- @@ L17-24 verbatim
lemma tail_forget (hp : ∀i,p i≠0) (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m : O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (V : 𝓢(ℝ,ℂ)) (X Y : ℝ) (R : Finset ι→Finset ι→ℝ)
    (y : SecondParentSource ι (Jo+(J.card+J.card))) :
    priorityTailParent p hg hp hinj extra pool negative Ψ m slots J lists a V X Y R
      (forgetAppended (Jo:=Jo) y)=
    priorityTailParent p hg hp hinj extra pool negative Ψ m slots J lists a V X Y R y := rfl


-- @@ L26-37 verbatim
theorem original_paired_tail (hp : ∀i,p i≠0)
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι) (source : Finset (Source ι Jo))
    (negative : Bool) (Ψ : O→*ℂ) (m : O) (slots J : Finset σ)
    (lists : σ→Finset ι) (a : σ→ι→ℂ) (w : Source ι Jo→ℂ)
    (V : 𝓢(ℝ,ℂ)) (X Y : ℝ) (R : Finset ι→Finset ι→ℝ) :
    (∑y∈wholeAssignedParents p (fun x=>extra x.cube) source negative J lists,
      coefficient p J a w y*priorityTailParent p hg hp hinj extra pool negative Ψ m slots J lists a V X Y R y)=
    ∑x∈source,w x*(‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      priorityTailParent p hg hp hinj extra pool negative Ψ m slots J lists a V X Y R (parent p x) := by
  rw [wholePaired_parent_sq_sum p (fun x=>extra x.cube) hinj]
  simp only [tail_forget]


-- @@ L39-39 verbatim
end SevenEighths.InverseMomentGlobalPriorityTail

-- @@ L40-40 verbatim
end


-- @@ L42-42 verbatim
end OAI
