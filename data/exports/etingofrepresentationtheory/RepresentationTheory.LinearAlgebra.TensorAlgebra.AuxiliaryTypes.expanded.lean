/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.LinearAlgebra.TensorAlgebra.Basis
import Mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower
import RepresentationTheory.Alignment.Attribute


-- @@ L11-11 verbatim
/-! # Auxiliary tensor-algebra types -/


-- @@ L13-13 verbatim
namespace RepresentationTheory.LinearAlgebra.TensorAlgebra.AuxiliaryTypes


-- @@ L15-15 verbatim
open scoped DirectSum TensorProduct


-- @@ L17-17 verbatim
universe u v w


-- @@ L19-19 verbatim
variable (k : Type u) [Field k]

-- @@ L20-20 verbatim
variable (V : Type v) [AddCommGroup V] [Module k V]


-- @@ L22-22 verbatim
namespace TensorAlgebra


-- @@ L24-25 verbatim
/-- An auxiliary type depending on a vector space over a field. -/
abbrev AuxiliaryType := _root_.TensorAlgebra k V


-- @@ L27-31 verbatim
/-- An algebra equivalence from the auxiliary type to the direct sum of tensor powers. -/
@[source_ref "Chapter2/Discussion_2.12_heading" (role := supporting)]
noncomputable def auxiliaryTypeEquivDirectSum :
    AuxiliaryType k V ≃ₐ[k] ⨁ n : ℕ, ⨂[k]^n V :=
  _root_.TensorAlgebra.equivDirectSum


-- @@ L33-38 verbatim
/-- The auxiliary-type equivalence sends a pure tensor product to its corresponding direct-sum
component. -/
theorem auxiliaryTypeEquivDirectSum_tprod {n : ℕ} (x : Fin n → V) :
    auxiliaryTypeEquivDirectSum k V (_root_.TensorAlgebra.tprod k V n x) =
      DirectSum.of (fun n : ℕ => ⨂[k]^n V) n (PiTensorProduct.tprod k x) :=
  _root_.TensorAlgebra.toDirectSum_tensorPower_tprod x


-- @@ L40-40 verbatim
end TensorAlgebra


-- @@ L42-42 verbatim
namespace TensorPower


-- @@ L44-52 verbatim
/-- Embedding tensor powers into the tensor algebra preserves multiplication of homogeneous
elements. -/
@[source_ref "Chapter2/Discussion_2.12_heading" (role := supporting)]
theorem toTensorAlgebra_mul_compatible {n m : ℕ} (a : ⨂[k]^n V) (b : ⨂[k]^m V) :
    _root_.TensorPower.toTensorAlgebra a * _root_.TensorPower.toTensorAlgebra b =
      _root_.TensorPower.toTensorAlgebra
        (@GradedMonoid.GMul.mul ℕ (fun d : ℕ => ⨂[k]^d V) _
          _root_.TensorPower.gMul n m a b) :=
  (_root_.TensorPower.toTensorAlgebra_gMul a b).symm


-- @@ L54-54 verbatim
end TensorPower


-- @@ L56-56 verbatim
namespace TensorAlgebra


-- @@ L58-62 verbatim
/-- A chosen basis gives an algebra equivalence from the auxiliary type to a free algebra. -/
@[source_ref "Chapter2/Discussion_2.12_heading" (role := supporting)]
noncomputable def basisAuxiliaryTypeEquivFreeAlgebra {ι : Type w} (b : Module.Basis ι k V) :
    AuxiliaryType k V ≃ₐ[k] FreeAlgebra k ι :=
  _root_.TensorAlgebra.equivFreeAlgebra b


-- @@ L64-70 verbatim
/-- Under the basis-induced equivalence from the auxiliary type, a tensor generator corresponding
to a basis element maps to the free generator. -/
@[simp] theorem basisAuxiliaryTypeEquivFreeAlgebra_generator
    {ι : Type w} (b : Module.Basis ι k V) (i : ι) :
    basisAuxiliaryTypeEquivFreeAlgebra k V b
        (_root_.TensorAlgebra.ι k (b i)) = FreeAlgebra.ι k i :=
  _root_.TensorAlgebra.equivFreeAlgebra_ι_apply b i


-- @@ L72-75 verbatim
/-- The canonical map from a module into its tensor algebra is injective. -/
theorem generator_injective :
    Function.Injective (_root_.TensorAlgebra.ι k : V → _root_.TensorAlgebra k V) :=
  _root_.TensorAlgebra.ι_leftInverse.injective


-- @@ L77-77 verbatim
end TensorAlgebra


-- @@ L79-79 verbatim
end RepresentationTheory.LinearAlgebra.TensorAlgebra.AuxiliaryTypes
