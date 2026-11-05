import Mathlib
import Definitions.Def_ModularCurve_X0


-- @@ L4-4 verbatim
noncomputable section


-- @@ L6-6 verbatim
open IntermediateField


-- @@ L8-8 verbatim
namespace ModularCurve


-- @@ L10-10 verbatim
section Tower


-- @@ L12-12 verbatim
variable (N : ℕ) [NeZero N]


-- @@ L14-19 verbatim
def jAdjoinRingHom : ℚ⟮jq⟯ →+* modularFunctionField N where
  toFun x := ⟨(x : LaurentSeries ℚ), adjoin_jq_le N x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl


-- @@ L21-22 verbatim
@[reducible] def algebraIntPolyModularFunctionField : Algebra (Polynomial ℤ) (modularFunctionField N) :=
  ((jAdjoinRingHom N).comp evalAtJGen).toAlgebra


-- @@ L24-24 verbatim
attribute [local instance] algebraIntPolyModularFunctionField


-- @@ L26-27 verbatim
abbrev routeBCoordRing : Subalgebra (Polynomial ℤ) (modularFunctionField N) :=
  integralClosure (Polynomial ℤ) (modularFunctionField N)


-- @@ L29-30 verbatim
def routeBJValue {N : ℕ} [NeZero N] {L : Type*} [CommRing L] (φ : ↥(routeBCoordRing N) →+* L) : L :=
  φ ⟨algebraMap (Polynomial ℤ) ↥(modularFunctionField N) Polynomial.X, Subalgebra.algebraMap_mem _ _⟩


-- @@ L32-32 verbatim
end Tower


-- @@ L34-34 verbatim
end ModularCurve


-- @@ L36-36 verbatim
end
