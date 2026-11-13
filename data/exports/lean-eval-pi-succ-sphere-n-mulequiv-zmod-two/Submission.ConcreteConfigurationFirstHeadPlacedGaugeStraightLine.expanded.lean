import Mathlib
import Submission.ConcreteConfigurationFirstHeadPlacedGaugeEntry
import Submission.SameFiberStraightLineComparison


-- @@ L5-26 verbatim
/-!
# Straight-line closure of the placed first-head gauge entry

The finite discrepancy gauge and the canonical placement of the literal first
compact head already have the same zero fiber.  Equality of zero fibers alone
does not make the affine interpolation of their defining maps regular: it can
create new zeros away from the fiber, or its derivative can lose rank on the
fiber.

This file isolates exactly that remaining analytic check for these two
concrete endpoints.  `StraightLineAdmissibility` has one field: throughout the
closed interpolation interval, the affine family has the prescribed zero
fiber and is regular there.  Everything else (joint smoothness and both exact
endpoint equations) is automatic, so the field constructs the previously
abstract `PlacedGaugeHomotopy` directly.

For a more elementary sufficient criterion, `AlignedData` specializes the
existing `SameFiberStraightLineComparison`: nonnegative pointwise pairing
prevents new zeros, while equality of first jets on the common fiber preserves
surjectivity.  The common-fiber equality itself is discharged from the two
already-proved canonical-target-union theorems.
-/


-- @@ L28-28 verbatim
set_option autoImplicit false


-- @@ L30-30 verbatim
noncomputable section


-- @@ L32-32 verbatim
open Set Function

-- @@ L33-33 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L35-35 verbatim
namespace Submission

-- @@ L36-36 verbatim
namespace ConcreteConfigurationFirstHeadPlacedGaugeStraightLine


-- @@ L38-38 verbatim
open ConcreteConfigurationMorseReduction

-- @@ L39-39 verbatim
open ConcreteConfigurationBridgeExactReduction

-- @@ L40-40 verbatim
open ConcreteConfigurationSignedFramedActualGaugeBridgeEntry

-- @@ L41-41 verbatim
open ConcreteConfigurationFirstHeadPlacedGaugeEntry


-- @@ L43-43 verbatim
variable {m : ℕ} {z : StableSpherePi (m + 2)}

-- @@ L44-44 verbatim
variable {B : BridgeData (m + 2) z}

-- @@ L45-45 verbatim
variable {Z : ZeroPairSaddleModel m}

-- @@ L46-46 verbatim
variable {kind : CompactMoveKind}

-- @@ L47-47 verbatim
variable {tail : FlatSignedConfiguration (m + 2) (compactBackground m)}


-- @@ L49-49 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (m + 3))

-- @@ L50-50 verbatim
local notation "Fₙ" => EuclideanSpace ℝ (Fin (m + 2))


-- @@ L52-52 verbatim
variable {hm : 0 < m}

-- @@ L53-56 verbatim
variable {M : SignedFramedOrbitEquiv
  (ConcreteConfigurationConfigure.field m : TamedField B.fls)
  (firstSourceField Z kind tail)
  B.fiberSign (firstSourceFlat Z kind tail).sign}

-- @@ L57-57 verbatim
variable {F : M.ActualFrameLoopMatch}


-- @@ L59-68 verbatim
/-- Literal affine interpolation between the finite-gauge endpoint and the
placed literal first-head endpoint. -/
def straightMap (hm : 0 < m)
    (M : SignedFramedOrbitEquiv
      (ConcreteConfigurationConfigure.field m : TamedField B.fls)
      (firstSourceField Z kind tail)
      B.fiberSign (firstSourceFlat Z kind tail).sign)
    (F : M.ActualFrameLoopMatch) (s : ℝ) (x : E) : Fₙ :=
  (1 - s) • (discrepancyHomotopy hm M F).toCobordism.X₁.g x +
    s • (firstSourcePlacement hm Z kind tail).endpointX.g x


-- @@ L70-84 verbatim
/-- The exact remaining analytic assertion for the literal affine family.
It is deliberately one field: every non-analytic `DefiningMapHomotopy`
obligation is proved below from the endpoint definitions. -/
structure StraightLineAdmissibility
    (hm : 0 < m)
    (M : SignedFramedOrbitEquiv
      (ConcreteConfigurationConfigure.field m : TamedField B.fls)
      (firstSourceField Z kind tail)
      B.fiberSign (firstSourceFlat Z kind tail).sign)
    (F : M.ActualFrameLoopMatch) : Prop where
  zeroFiber_regular : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
    {x : E | straightMap hm M F s x = 0} =
        (discrepancyHomotopy hm M F).toCobordism.X₁.fiber ∧
      ∀ x ∈ (discrepancyHomotopy hm M F).toCobordism.X₁.fiber,
        Function.Surjective (fderiv ℝ (straightMap hm M F s) x)


-- @@ L86-86 verbatim
namespace StraightLineAdmissibility


-- @@ L88-88 verbatim
variable (D : StraightLineAdmissibility hm M F)


-- @@ L90-97 verbatim
theorem straightMap_smooth :
    ContDiff ℝ ∞ (fun p : ℝ × E => straightMap hm M F p.1 p.2) := by
  exact ((contDiff_const.sub contDiff_fst).smul
      ((discrepancyHomotopy hm M F).toCobordism.X₁.smooth.comp
        contDiff_snd)).add
    (contDiff_fst.smul
      ((firstSourcePlacement hm Z kind tail).endpointX.smooth.comp
        contDiff_snd))


-- @@ L99-102 verbatim
@[simp] theorem straightMap_zero : straightMap hm M F 0 =
    (discrepancyHomotopy hm M F).toCobordism.X₁.g := by
  funext x
  simp [straightMap]


-- @@ L104-107 verbatim
@[simp] theorem straightMap_one : straightMap hm M F 1 =
    (firstSourcePlacement hm Z kind tail).endpointX.g := by
  funext x
  simp [straightMap]


-- @@ L109-119 verbatim
/-- The one specialized analytic assertion produces the actual missing
common-fiber homotopy with both endpoints definitionally exact. -/
def homotopy : DefiningMapHomotopy
    (discrepancyHomotopy hm M F).toCobordism.X₁
    (firstSourcePlacement hm Z kind tail).endpointX where
  H := straightMap hm M F
  smooth := straightMap_smooth (hm := hm) (M := M) (F := F)
  H_zero := straightMap_zero (hm := hm) (M := M) (F := F)
  H_one := straightMap_one (hm := hm) (M := M) (F := F)
  fiber_eq := fun s hs0 hs1 => (D.zeroFiber_regular s hs0 hs1).1
  regular := fun s hs0 hs1 => (D.zeroFiber_regular s hs0 hs1).2


-- @@ L121-125 verbatim
/-- Directly fill the sole field of the first-head placed-gauge entry. -/
def toPlacedGaugeHomotopy :
    ConcreteConfigurationFirstHeadPlacedGaugeEntry.PlacedGaugeHomotopy
      hm M F :=
  ⟨D.homotopy⟩


-- @@ L127-127 verbatim
end StraightLineAdmissibility


-- @@ L129-129 verbatim
/-! ## Checkable sufficient conditions -/


-- @@ L131-149 verbatim
/-- A concrete sufficient certificate for the affine family.  The two fields
are precisely the nonautomatic hypotheses of
`SameFiberStraightLineComparison`; equality of the endpoint fibers is already
a theorem in this specialization. -/
structure AlignedData
    (hm : 0 < m)
    (M : SignedFramedOrbitEquiv
      (ConcreteConfigurationConfigure.field m : TamedField B.fls)
      (firstSourceField Z kind tail)
      B.fiberSign (firstSourceFlat Z kind tail).sign)
    (F : M.ActualFrameLoopMatch) : Prop where
  pairing_nonneg : ∀ x : E,
    0 ≤ inner ℝ
      ((discrepancyHomotopy hm M F).toCobordism.X₁.g x)
      ((firstSourcePlacement hm Z kind tail).endpointX.g x)
  firstJet_eq : ∀ x ∈
      (discrepancyHomotopy hm M F).toCobordism.X₁.fiber,
    fderiv ℝ (firstSourcePlacement hm Z kind tail).endpointX.g x =
      fderiv ℝ (discrepancyHomotopy hm M F).toCobordism.X₁.g x


-- @@ L151-151 verbatim
namespace AlignedData


-- @@ L153-153 verbatim
variable (D : AlignedData hm M F)


-- @@ L155-162 verbatim
/-- Both endpoint fibers are the same canonical target union; no new
geometric hypothesis is needed for this field. -/
theorem placed_fiber_eq_gauge_fiber :
    (firstSourcePlacement hm Z kind tail).endpointX.fiber =
      (discrepancyHomotopy hm M F).toCobordism.X₁.fiber := by
  rw [(firstSourcePlacement hm Z kind tail).endpoint_fiber,
    ConcreteConfigurationFirstHeadPlacedGaugeEntry.gaugeEndpoint_fiber
      hm M F]


-- @@ L164-172 verbatim
/-- Package the specialized endpoint facts for the generic straight-line
comparison theorem. -/
theorem toComparisonData (D : AlignedData hm M F) :
    SameFiberStraightLineComparison.Data
    (discrepancyHomotopy hm M F).toCobordism.X₁
    (firstSourcePlacement hm Z kind tail).endpointX where
  fiber_eq := placed_fiber_eq_gauge_fiber (hm := hm) (M := M) (F := F)
  pairing_nonneg := D.pairing_nonneg
  firstJet_eq := D.firstJet_eq


-- @@ L174-179 verbatim
/-- The elementary alignment certificate therefore constructs the missing
homotopy without restating interval-wise regularity. -/
def homotopy : DefiningMapHomotopy
    (discrepancyHomotopy hm M F).toCobordism.X₁
    (firstSourcePlacement hm Z kind tail).endpointX :=
  D.toComparisonData.homotopy


-- @@ L181-186 verbatim
/-- Fill the bridge-entry contract directly from value-direction and
first-jet alignment. -/
def toPlacedGaugeHomotopy :
    ConcreteConfigurationFirstHeadPlacedGaugeEntry.PlacedGaugeHomotopy
      hm M F :=
  ⟨D.homotopy⟩


-- @@ L188-188 verbatim
end AlignedData


-- @@ L190-190 verbatim
end ConcreteConfigurationFirstHeadPlacedGaugeStraightLine

-- @@ L191-191 verbatim
end Submission
