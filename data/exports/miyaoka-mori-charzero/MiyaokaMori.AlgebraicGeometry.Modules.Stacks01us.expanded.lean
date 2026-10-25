import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.RelativeDifferentials
import MiyaokaMori.AlgebraicGeometry.Modules.OmegaOpenImmersionSquare


-- @@ L5-9 verbatim
/-! # Relative differentials and open subschemes (Stacks 01US)

Stacks 01US: `Ω` is compatible with open subschemes — for `f : X → S` and opens `U ⊆ X`, `V ⊆ S` with
`f(U) ⊆ V`, `Ω_{X/S}|_U ≅ Ω_{U/V}` (compatibly with `d`). Used for `E = s^*T_{Z/C}` which only sees `Z^×`.
-/


-- @@ L11-11 verbatim
set_option autoImplicit false

-- @@ L12-12 verbatim
set_option maxHeartbeats 400000


-- @@ L14-14 verbatim
universe u v w u' v'


-- @@ L16-16 verbatim
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

-- @@ L17-17 verbatim
open scoped AlgebraicGeometry


-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
open scoped AlgebraicGeometry


-- @@ L23-29 verbatim
theorem AlgebraicGeometry.Omega_restrict_open {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
    (U : X.Opens) (V : S.Opens) (e : U ≤ f ⁻¹ᵁ V) :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj (AlgebraicGeometry.Omega f) ≅
      AlgebraicGeometry.Omega (f.resLE V U e)) :=
  ⟨(AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app _ ≪≫
    AlgebraicGeometry.Omega.restrictIso f (f.resLE V U e) U.ι V.ι
      (AlgebraicGeometry.Scheme.Hom.resLE_comp_ι f e)⟩


-- @@ L31-31 verbatim
end
