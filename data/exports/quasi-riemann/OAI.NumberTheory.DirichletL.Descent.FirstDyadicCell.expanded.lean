import OAI.NumberTheory.DirichletL.Descent.FirstDyadicRadius
import OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileLiveParents


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators


-- @@ L9-9 verbatim
namespace SevenEighths.InverseMoment

-- @@ L10-10 verbatim
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic

-- @@ L11-11 verbatim
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows

-- @@ L12-12 verbatim
open InverseMomentFirstOriginalProfile

-- @@ L13-13 verbatim
open ConcreteTraceCRT (eisEmbedding)

-- @@ L14-14 verbatim
local notation "O"=>ActualEisensteinCubic.O

-- @@ L15-15 verbatim
variable {ι:Type*}[DecidableEq ι]

-- @@ L16-16 verbatim
variable (p:ι→O)


-- @@ L18-20 verbatim
def firstCellRadius (Z M r ell V eta tau:ℝ)(k:SourceIndex)(j:ℕ):ℝ:=
  Z^(firstPhysicalHeight M r ell V (dyadicExponent Z (k 3))
    (dyadicExponent Z (k 2)) (dyadicExponent Z j)+12*eta+tau)


-- @@ L22-40 verbatim
theorem first_dyadic_radius_cell (pool:Finset ι)(Q:Finset (ι→₀ℕ))
    (k:SourceIndex)(j:ℕ)(x:FirstOriginalOuter ι)
    (hx:x∈refinedOuter p pool Q k (labelGate p j))
    (Z M r ell V eta tau:ℝ):
    firstDyadicRadius p x.1 x.2.1 x.2.2 Z M r ell V eta tau=
      firstCellRadius Z M r ell V eta tau k j:=by
  rw [refinedOuter_label] at hx
  obtain ⟨hx,hj⟩:=Finset.mem_filter.mp hx
  have hg:outerGate p k x:=(Finset.mem_filter.mp hx).2
  have hC:=hg 2
  have hD:=hg 3
  change dyadIndex (primeProductNorm p x.2.1)=k 2 at hC
  change dyadIndex (‖eisEmbedding (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.2.2)‖^2)=k 3 at hD
  rw [primeSubsetGenerator_norm_eq_productNorm] at hD
  unfold firstDyadicRadius firstCellRadius firstDyadicExponent
  rw [hD,hC]
  change dyadIndex (‖eisEmbedding (jLabel p x.1.support
    (fun i=>x.1.leftExponent i+x.1.rightExponent i) x.1.leftBit x.1.rightBit)‖^2)=j at hj
  rw [hj]


-- @@ L42-48 verbatim
theorem first_dyadic_refined_cutoff (pool:Finset ι)(Q:Finset (ι→₀ℕ))
    (k:SourceIndex)(j:ℕ)(Z M r ell V eta tau:ℝ):
    ∀x∈refinedOuter p pool Q k (labelGate p j),∀_I:Ideal O,
      firstDyadicRadius p x.1 x.2.1 x.2.2 Z M r ell V eta tau≤
        firstCellRadius Z M r ell V eta tau k j:=by
  intro x hx I
  exact (first_dyadic_radius_cell p pool Q k j x hx Z M r ell V eta tau).le


-- @@ L50-50 verbatim
end SevenEighths.InverseMoment


-- @@ L52-52 verbatim
end


-- @@ L54-54 verbatim
end OAI
