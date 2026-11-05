import Mathlib
import Definitions.Def_ModularCurve_RouteBCoordRing
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Theorems.Thm_ModularCurve_transcendental_jq


-- @@ L7-7 verbatim
set_option autoImplicit false


-- @@ L9-9 verbatim
noncomputable section


-- @@ L11-11 verbatim
open IntermediateField AlgebraicCurve AlgebraicCurve.RationalFunctionField


-- @@ L13-13 verbatim
namespace ModularCurve


-- @@ L15-15 verbatim
section Tower


-- @@ L17-17 verbatim
variable (N : ℕ) [NeZero N]


-- @@ L19-20 verbatim
@[reducible] def jAdjoinAlgebra : Algebra ℚ⟮jq⟯ (modularFunctionField N) :=
  (jAdjoinRingHom N).toAlgebra


-- @@ L22-22 verbatim
attribute [local instance] jAdjoinAlgebra


-- @@ L24-27 verbatim
instance instIsScalarTowerJAdjoin :
    @IsScalarTower ℚ ℚ⟮jq⟯ (modularFunctionField N)
      Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  IsScalarTower.of_algebraMap_eq' (by apply RingHom.ext_rat)


-- @@ L29-30 verbatim
theorem algebraMap_jGen_val : (algebraMap ℚ⟮jq⟯ (modularFunctionField N) jGen : LaurentSeries ℚ) = jq :=
  rfl


-- @@ L32-32 verbatim
end Tower


-- @@ L34-34 verbatim
attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial


-- @@ L36-38 verbatim
def jLineRingEquiv : RatFunc ℚ ≃+* ℚ⟮jq⟯ :=
  RingEquiv.ofBijective (RatFunc.algEquivOfTranscendental jq transcendental_jq)
    (EquivLike.bijective _)


-- @@ L40-41 verbatim
theorem jLineRingEquiv_apply (f : RatFunc ℚ) :
    jLineRingEquiv f = RatFunc.algEquivOfTranscendental jq transcendental_jq f := rfl


-- @@ L43-44 verbatim
theorem jLineRingEquiv_X : jLineRingEquiv RatFunc.X = jGen :=
  Subtype.ext (RatFunc.algEquivOfTranscendental_X jq transcendental_jq)


-- @@ L46-46 verbatim
@[reducible] def instDecidableEqRatFuncRat : DecidableEq (RatFunc ℚ) := Classical.decEq _


-- @@ L48-48 verbatim
attribute [local instance] instDecidableEqRatFuncRat


-- @@ L50-52 verbatim
def jLinePlace1728 : Place ℚ ℚ⟮jq⟯ :=
  Place.congrRingEquiv jLineRingEquiv (RingHom.map_rat_algebraMap jLineRingEquiv.toRingHom)
    (placeOfPoint ℚ 1728)


-- @@ L54-56 verbatim
def jLinePlaceZero : Place ℚ ℚ⟮jq⟯ :=
  Place.congrRingEquiv jLineRingEquiv (RingHom.map_rat_algebraMap jLineRingEquiv.toRingHom)
    (placeOfPoint ℚ 0)


-- @@ L58-60 verbatim
def jLinePlaceInfty : Place ℚ ℚ⟮jq⟯ :=
  Place.congrRingEquiv jLineRingEquiv (RingHom.map_rat_algebraMap jLineRingEquiv.toRingHom)
    (placeInfty ℚ)


-- @@ L62-62 verbatim
end ModularCurve


-- @@ L64-64 verbatim
end
