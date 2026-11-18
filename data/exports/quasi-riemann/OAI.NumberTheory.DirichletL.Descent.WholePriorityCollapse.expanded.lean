import OAI.NumberTheory.DirichletL.Descent.WholePriorityRays
import OAI.NumberTheory.DirichletL.Descent.WholePriorityPrincipal
import OAI.NumberTheory.DirichletL.Inversion.WholePriorityRapidTail


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open scoped BigOperators Classical SchwartzMap


-- @@ L10-10 verbatim
namespace SevenEighths.InverseMoment

-- @@ L11-11 verbatim
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic

-- @@ L12-12 verbatim
open InverseInitialArithmetic InverseFirstPriorityParents InverseMomentWholePriorityParents

-- @@ L13-13 verbatim
open InverseWholePriorityValidSource InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic

-- @@ L14-14 verbatim
local notation "Eis"=>ActualEisensteinCubic.O

-- @@ L15-15 verbatim
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ] {Jo:ℕ}

-- @@ L16-17 verbatim
variable (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})


-- @@ L19-42 verbatim
theorem whole_assigned_source_original
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (cube:CubeCoordinates ι) (C E:Finset ι) (old:Fin Jo→SmoothMobiusCorrection.PrimeIdeal)
    (selector:Finset ι→ℂ) (negative:Bool) (Ψ:Eis→*ℂ) (m:Eis)
    (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (H:SecondParentSource ι Jo→ℂ):
    (∑y∈activeParents p extra pool cube C E old selector negative assigned lists,
      coefficient p assigned a (fun x=>(priorityOuter p hg cube negative Ψ m selector ray core x.quotientSupport:ℂ)) y *
        H (forgetAppended y))=
    ∑D∈pool.powerset,(priorityOuter p hg cube negative Ψ m selector ray core D:ℂ)*
      (‖primeMark assigned lists a ((extra cube∪((if negative then cube.rightDivisor else cube.leftDivisor)∪C))∪D)‖^2:ℝ)*
      H (parent p (fixedPoint cube C E old D)) := by
  rw [activeParents,←wholePaired_parent_sq_sum p (fun x=>extra x.cube) hinj,
    sum_activeFixedSource]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro D hD
  by_cases hs:selector D≠0
  · rw [ite_eq_left hs]
    simp only [fixedPoint,wholeExtractedSupport,extractedSupport,Finset.union_assoc]
  · rw [ite_eq_right hs,priorityOuter_zero p hg cube negative Ψ m selector ray core D (not_ne_iff.mp hs)]
    simp


-- @@ L44-63 verbatim
theorem whole_assigned_source_norm
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (cube:CubeCoordinates ι) (C E:Finset ι) (old:Fin Jo→SmoothMobiusCorrection.PrimeIdeal)
    (selector:Finset ι→ℂ) (negative:Bool) (Ψ:Eis→*ℂ) (m:Eis)
    (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (H:SecondParentSource ι Jo→ℂ):
    ‖∑y∈activeParents p extra pool cube C E old selector negative assigned lists,
      coefficient p assigned a (fun x=>(priorityOuter p hg cube negative Ψ m selector ray core x.quotientSupport:ℂ)) y *
        H (forgetAppended y)‖≤
    ∑D∈pool.powerset,priorityOuter p hg cube negative Ψ m selector ray core D*
      ‖primeMark assigned lists a ((extra cube∪((if negative then cube.rightDivisor else cube.leftDivisor)∪C))∪D)‖^2*
      ‖H (parent p (fixedPoint cube C E old D))‖ := by
  rw [whole_assigned_source_original p hg hinj]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro D hD
  rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,
    Real.norm_of_nonneg (by unfold priorityOuter;positivity),Real.norm_of_nonneg (sq_nonneg _)]


-- @@ L65-65 verbatim
end SevenEighths.InverseMoment


-- @@ L67-67 verbatim
end


-- @@ L69-69 verbatim
end OAI
