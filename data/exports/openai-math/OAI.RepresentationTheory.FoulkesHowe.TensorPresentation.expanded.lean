import OAI.RepresentationTheory.FoulkesHowe.Model


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped BigOperators TensorProduct


-- @@ L8-8 verbatim
universe u


-- @@ L10-10 verbatim
namespace Problem346


-- @@ L12-12 verbatim
variable (n : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V]


-- @@ L14-18 verbatim
/-- Multiplication of degree-one generators as a multilinear map. -/
def symMonomialMultilinearRaw :
    MultilinearMap ℂ (fun _ : Fin n => V) (SymmetricAlgebra ℂ V) :=
  (MultilinearMap.mkPiAlgebra ℂ (Fin n) (SymmetricAlgebra ℂ V)).compLinearMap
    (fun _ => SymmetricAlgebra.ι ℂ V)


-- @@ L20-21 verbatim
@[simp] theorem symMonomialMultilinearRaw_apply (v : Fin n → V) :
    symMonomialMultilinearRaw n V v = symMonomialRaw n V v := rfl


-- @@ L23-26 verbatim
/-- The tensor-power presentation of the homogeneous symmetric power. -/
def tensorToSymPowRaw :
    (⨂[ℂ] _ : Fin n, V) →ₗ[ℂ] SymmetricAlgebra ℂ V :=
  PiTensorProduct.lift (symMonomialMultilinearRaw n V)


-- @@ L28-30 verbatim
@[simp] theorem tensorToSymPowRaw_tprod (v : Fin n → V) :
    tensorToSymPowRaw n V (PiTensorProduct.tprod ℂ v) = symMonomialRaw n V v :=
  PiTensorProduct.lift.tprod _


-- @@ L32-36 verbatim
theorem tensorToSymPowRaw_range :
    LinearMap.range (tensorToSymPowRaw n V) = symPowSubmodule n V := by
  rw [← Submodule.map_top, ← PiTensorProduct.span_tprod_eq_top,
    Submodule.map_span, ← Set.range_comp]
  simp only [Function.comp_def, tensorToSymPowRaw_tprod, symPowSubmodule]


-- @@ L38-42 verbatim
/-- Multiplication of tensors, with codomain restricted to degree `n`. -/
def tensorToSymPow : (⨂[ℂ] _ : Fin n, V) →ₗ[ℂ] SymPow n V :=
  (tensorToSymPowRaw n V).codRestrict (symPowSubmodule n V) (fun x => by
    rw [← tensorToSymPowRaw_range]
    exact LinearMap.mem_range_self _ x)


-- @@ L44-47 verbatim
@[simp] theorem tensorToSymPow_tprod (v : Fin n → V) :
    tensorToSymPow n V (PiTensorProduct.tprod ℂ v) = symMonomial n V v := by
  apply Subtype.ext
  exact tensorToSymPowRaw_tprod n V v


-- @@ L49-55 verbatim
theorem tensorToSymPow_surjective : Function.Surjective (tensorToSymPow n V) := by
  intro x
  have hx : x.val ∈ LinearMap.range (tensorToSymPowRaw n V) := by
    rw [tensorToSymPowRaw_range]
    exact x.property
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, Subtype.ext hy⟩


-- @@ L57-57 verbatim
end Problem346


-- @@ L59-59 verbatim
end


-- @@ L61-61 verbatim
end OAI
