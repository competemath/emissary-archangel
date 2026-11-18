import OAI.NumberTheory.DirichletL.PrimeRows.MarkedProduct
import OAI.NumberTheory.DirichletL.PrimeRows.FirstBoundary


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators

-- @@ L8-8 verbatim
namespace SevenEighths.ProbeHighRowFamily

-- @@ L9-9 verbatim
open HeckeFamily ProbePhysical

-- @@ L10-10 verbatim
local notation "O" => HeckeFamily.O


-- @@ L12-24 verbatim
theorem correctionTail_mono {S T : Finset (Ideal O)} (hS : CorrectionTail S) (hst : S⊆T) :
    CorrectionTail T := by
  let inc : {P : PrimeIdeal // P.val∉T}→{P : PrimeIdeal // P.val∉S} :=
    fun P=>⟨P.val,fun h=>P.property (hst h)⟩
  have hi : Function.Injective inc := by
    intro P Q h
    exact Subtype.ext (congrArg (fun R : {P : PrimeIdeal // P.val∉S}=>R.val) h)
  constructor
  · intro P hP
    exact hS.norm_four P (fun h=>hP (hst h))
  · apply le_trans _ hS.small
    exact Summable.tsum_le_tsum_of_inj inc hi (fun P _=>globalPrimeDefectBound_nonneg P.val)
      (fun _=>le_rfl) (globalPrimeDefectBound_summable.subtype _) hS.summable


-- @@ L26-38 verbatim
theorem firstTail_mono {eps : ℝ} {S T : Finset (Ideal O)} (hS : FirstTail eps S) (hst : S⊆T) :
    FirstTail eps T := by
  let inc : {P : PrimeIdeal // P.val∉T}→{P : PrimeIdeal // P.val∉S} :=
    fun P=>⟨P.val,fun h=>P.property (hst h)⟩
  have hi : Function.Injective inc := by
    intro P Q h
    exact Subtype.ext (congrArg (fun R : {P : PrimeIdeal // P.val∉S}=>R.val) h)
  refine ⟨hS.positive,?_,?_⟩
  · intro P hP
    exact hS.norm_four P (fun h=>hP (hst h))
  · apply le_trans _ hS.small
    exact Summable.tsum_le_tsum_of_inj inc hi (fun P _=>firstPrimeDefectBound_nonneg eps P.val)
      (fun _=>le_rfl) ((firstPrimeDefectBound_summable eps hS.positive).subtype _) hS.summable


-- @@ L40-44 verbatim
theorem markedSourceExclusions (S : Finset (Ideal O)) (hS : SourceExclusions S) (T : Finset PrimeIdeal) :
    SourceExclusions (markExclusions S T) := {
  prime := markExclusions_prime S hS.prime T
  bad := hS.bad.trans Finset.subset_union_left
  tail := correctionTail_mono hS.tail Finset.subset_union_left }


-- @@ L46-47 verbatim
theorem marked_firstTail (eps : ℝ) (S : Finset (Ideal O)) (hS : FirstTail eps S) (T : Finset PrimeIdeal) :
    FirstTail eps (markExclusions S T) := firstTail_mono hS Finset.subset_union_left


-- @@ L49-49 verbatim
end SevenEighths.ProbeHighRowFamily


-- @@ L51-51 verbatim
end


-- @@ L53-53 verbatim
end OAI
