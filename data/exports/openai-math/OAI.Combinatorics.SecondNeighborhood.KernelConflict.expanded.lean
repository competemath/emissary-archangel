import OAI.Combinatorics.SecondNeighborhood.KernelRestriction
import OAI.Combinatorics.SecondNeighborhood.MaxSupportKernel


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
namespace SeymourSecondNeighborhood.Pruning


-- @@ L8-8 verbatim
open Matrix

-- @@ L9-9 verbatim
open SeymourSecondNeighborhood.LinearAlgebra.MaxSupportKernel


-- @@ L11-11 verbatim
variable {X : Type*} [Fintype X] [DecidableEq X]


-- @@ L13-18 verbatim
omit [Fintype X] [DecidableEq X] in
theorem matrixD_supported (r : X → X → Prop) (R C : Finset (X × X))
    (b : X → X → ℝ) (hb : SupportedCoefficients r b) (p i : X) :
    SupportedOn (localSupport r R C p i) (matrixD R C b p i) := by
  intro s j h
  exact hb s.1 j.1 h


-- @@ L20-23 verbatim
def LocalMaximalRanks (r : X → X → Prop) (R C : Finset (X × X))
    (b : X → X → ℝ) : Prop :=
  ∀ p i, r p i → ∀ D : Matrix (PairFiber C i) (PairFiber R p) ℝ,
    SupportedOn (localSupport r R C p i) D → D.rank ≤ (matrixD R C b p i).rank


-- @@ L25-40 verbatim
theorem conflict_kernel_product_eq_zero (r : X → X → Prop)
    (R C : Finset (X × X)) (b : X → X → ℝ) (hb : SupportedCoefficients r b)
    (hmax : LocalMaximalRanks r R C b)
    (u : ↥R → ℝ) (hu : matrixB r R C b *ᵥ u = 0)
    (v : ↥C → ℝ) (hv : (matrixN r R C b)ᵀ *ᵥ v = 0)
    (left : ↥R) (right : ↥C) (hc : Conflict r left.1 right.1) :
    u left * v right = 0 := by
  let j : PairFiber R left.1.1 := ⟨left.1.2, left.2⟩
  let s : PairFiber C right.1.1 := ⟨right.1.2, right.2⟩
  have hx := restrictFiber_mem_kernelD r R C b hb left.1.1 right.1.1 hc.1 u hu
  have hy := restrictFiber_mem_kernelD_transpose r R C b hb
    left.1.1 right.1.1 hc.1 v hv
  have h := kernel_support_of_max_rank
    (matrixD_supported r R C b hb left.1.1 right.1.1)
    (hmax left.1.1 right.1.1 hc.1) hx hy (s := s) (j := j) hc.2
  simpa [restrictFiber, fiberIndex, j, s] using h


-- @@ L42-42 verbatim
end SeymourSecondNeighborhood.Pruning


-- @@ L44-44 verbatim
end OAI
