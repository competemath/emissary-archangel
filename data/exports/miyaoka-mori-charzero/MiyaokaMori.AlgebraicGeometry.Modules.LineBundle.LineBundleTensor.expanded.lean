import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafToModules
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleOfModules
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct


-- @@ L10-16 verbatim
/-! # Tensor product of bundled line bundles

The tensor product `L ⊗ M` of bundled line bundles: the underlying module is
`Scheme.Modules.tensor L.toModules M.toModules` (the tensor product of two line bundles is a line bundle,
Stacks 01CT), bundled into `LineBundle X` by `LineBundle.ofModules`. This is the `L.tensor M` used for
`L^{⊗q}` and `ρ^*A ⊗ L^{-q}`.
-/


-- @@ L18-18 verbatim
set_option autoImplicit false

-- @@ L19-19 verbatim
set_option maxHeartbeats 400000


-- @@ L21-21 verbatim
universe u v w u' v'


-- @@ L23-23 verbatim
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

-- @@ L24-24 verbatim
open scoped AlgebraicGeometry


-- @@ L26-26 verbatim
noncomputable section


-- @@ L28-30 verbatim
noncomputable def LineBundle.tensor {k : Type u} [Field k] {X : Variety k} (L M : LineBundle X) :
    LineBundle X :=
  LineBundle.ofModules (AlgebraicGeometry.Scheme.Modules.tensor L.toModules M.toModules)


-- @@ L32-34 verbatim
theorem LineBundle.tensor_toModules {k : Type u} [Field k] {X : Variety k} (L M : LineBundle X) :
    (L.tensor M).toModules = AlgebraicGeometry.Scheme.Modules.tensor L.toModules M.toModules :=
  rfl


-- @@ L36-36 verbatim
end
