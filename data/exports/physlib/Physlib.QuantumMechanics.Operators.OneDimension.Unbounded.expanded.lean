/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QuantumMechanics.HilbertSpaces.OneDimension.Basic

-- @@ L9-18 verbatim
/-!

# Unbounded operators

## Note

It is likely one day the material in this file will be moved to or appear
in another form within Mathlib.

-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
namespace QuantumMechanics


-- @@ L24-24 verbatim
namespace OneDimension

-- @@ L25-25 verbatim
noncomputable section

-- @@ L26-26 verbatim
open _root_.QuantumMechanics.OneDimension.HilbertSpace


-- @@ L28-34 verbatim
/-- An unbounded operator on the one-dimensional Hilbert space,
  corresponds to a subobject `ι : S →L[ℂ] HilbertSpace` of the Hilbert
  space along with the operator `op : S →L[ℂ] HilbertSpace` -/
@[nolint unusedArguments]
def UnboundedOperator {S : Type} [AddCommGroup S] [Module ℂ S]
    [TopologicalSpace S] (ι : S →L[ℂ] HilbertSpace)
    (_ : Function.Injective ι) := S →L[ℂ] HilbertSpace


-- @@ L36-36 verbatim
namespace UnboundedOperator


-- @@ L38-40 verbatim
variable {S : Type} [AddCommGroup S] [Module ℂ S] [TopologicalSpace S]
  {ι : S →L[ℂ] HilbertSpace}
  {hι : Function.Injective ι} (U : UnboundedOperator ι hι)


-- @@ L42-43 verbatim
instance : CoeFun (UnboundedOperator ι hι) (fun _ => S → HilbertSpace) where
  coe := fun U => U.toFun


-- @@ L45-46 verbatim
/-- An unbounded operator created from a continuous linear map ` S →L[ℂ] S`. -/
def ofSelfCLM (Op : S →L[ℂ] S) : UnboundedOperator ι hι := ι ∘L Op


-- @@ L48-50 verbatim
@[simp]
lemma ofSelfCLM_apply (Op : S →L[ℂ] S) (ψ : S) :
    ofSelfCLM (hι := hι) Op ψ = ι (Op ψ) := rfl


-- @@ L52-55 verbatim
/-- A map `F : S →L[ℂ] ℂ` is a generalized eigenvector of an unbounded operator `U`
  on `S` if there is an eigenvalue `c` such that for all `ψ`, `F (U ψ) = c ⬝ F ψ` -/
def IsGeneralizedEigenvector (F : S →L[ℂ] ℂ) (c : ℂ) : Prop :=
  ∀ ψ : S, ∃ ψ' : S, ι ψ' = U ψ ∧ F ψ' = c • F ψ


-- @@ L57-61 verbatim
lemma isGeneralizedEigenvector_ofSelfCLM_iff {Op : S →L[ℂ] S}
    (F : S →L[ℂ] ℂ) (c : ℂ) :
    IsGeneralizedEigenvector (ofSelfCLM (hι := hι) Op) F c ↔
    ∀ ψ : S, F (Op ψ) = c • F ψ := by
  simp only [IsGeneralizedEigenvector, ofSelfCLM_apply, hι.eq_iff, exists_eq_left]


-- @@ L63-63 verbatim
open InnerProductSpace


-- @@ L65-71 verbatim
/-- The condition for an unbounded operator to be *symmetric* (equivalently, formally
self-adjoint): `⟪U ψ1, ι ψ2⟫ = ⟪ι ψ1, U ψ2⟫` for all `ψ1 ψ2`. This is the Hermitian
pairing on the underlying space `S`; on its own it does **not** imply genuine
self-adjointness (`A† = A`, including equality of domains), which for an unbounded
operator on a proper dense core is strictly stronger. -/
def IsSymmetric : Prop :=
  ∀ ψ1 ψ2 : S, ⟪U ψ1, ι ψ2⟫_ℂ = ⟪ι ψ1, U ψ2⟫_ℂ


-- @@ L73-73 verbatim
end UnboundedOperator


-- @@ L75-75 verbatim
end

-- @@ L76-76 verbatim
end OneDimension

-- @@ L77-77 verbatim
end QuantumMechanics
