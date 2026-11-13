import Mathlib
import Submission.ConcreteZeroPairCassiniTwist
import Submission.PTSignedCobordismCollaredSphere


-- @@ L5-17 verbatim
/-!
# A concrete transverse PT middle for the twisted Cassini saddle

The twisted Cassini event already is a genuine framed cobordism.  Giving its
whole zero surface the constant positive label lets the signed PT collapse and
relative Sard theorem construct an actual transverse sphere middle.  All
choices below are made from proved nonempty types; no geometric witness is an
argument of the final definition.

This file deliberately stops short of claiming that the horizontal regular
value has no southern-sheet endpoint components.  That extra assertion is a
field of `CassiniPTEndpointStability`, not a consequence of relative Sard.
-/


-- @@ L19-19 verbatim
set_option autoImplicit false


-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
namespace Submission

-- @@ L24-24 verbatim
namespace ConcreteZeroPairCassiniPTMiddle


-- @@ L26-26 verbatim
open Set Function Metric

-- @@ L27-27 verbatim
open scoped Topology RealInnerProductSpace ContDiff unitInterval


-- @@ L29-29 verbatim
variable (m : ℕ) (hm : 0 < m)


-- @@ L31-31 verbatim
local notation "X₀" => ConcreteZeroPairCassiniTwist.sourceFLS m hm

-- @@ L32-32 verbatim
local notation "X₁" => ConcreteZeroPairCassiniTwist.targetFLS m hm


-- @@ L34-44 verbatim
/-- The twisted pair of pants with the constant-positive space-time label. -/
def signedCobordism : SignedFramedLevelCobordism
    (FiberSign.allPositive X₀) (FiberSign.allPositive X₁) where
  cobordism := ConcreteZeroPairCassiniTwist.cobordism m hm
  source_eq := rfl
  target_eq := rfl
  toFun := fun _ => 1
  continuous := continuous_const
  nonzero := by simp
  collar_zero := by simp [FiberSign.allPositive]
  collar_one := by simp [FiberSign.allPositive]


-- @@ L46-52 verbatim
/-- A proved-existing compactly supported selector for the positive Cassini
slab fiber. -/
def slabCutoff :
    SignedFramedLevelCobordism.SignedSlabCutoff (signedCobordism m hm) :=
  Classical.choice
    (SignedFramedLevelCobordism.SignedSlabCutoff.nonempty
      (signedCobordism m hm))


-- @@ L54-58 verbatim
/-- The unrestricted smooth collared sphere homotopy obtained from the actual
twisted Cassini cobordism. -/
def sphereHomotopy : CollaredSphereHomotopy (m + 2) :=
  SignedFramedLevelCobordism.SignedSlabCutoff.toCollaredSphereHomotopy
    (signedCobordism m hm) (slabCutoff m hm)


-- @@ L60-67 verbatim
/-- A nonzero small regular horizontal value for one collared sphere middle. -/
structure TransverseValue where
  target : EuclideanSpace ℝ (Fin (m + 2))
  target_ne_zero : target ≠ 0
  target_norm_lt_one : ‖target‖ < 1
  regular : IsRegularValue (sphereHomotopy m hm).horizontal target
  norm_pos : 0 < ‖target‖
  norm_lt_eighth : ‖target‖ < 1 / 8


-- @@ L69-81 verbatim
theorem transverseValue_nonempty : Nonempty (TransverseValue m hm) := by
  obtain ⟨y, hypos, hy8, -, hreg⟩ :=
    exists_small_regular_value (n := m + 2) (by omega)
      (sphereHomotopy m hm).contDiff_horizontal
  have hy0 : y ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hypos)
  exact ⟨{
    target := y
    target_ne_zero := hy0
    target_norm_lt_one := hy8.trans (by norm_num)
    regular := hreg
    norm_pos := hypos
    norm_lt_eighth := hy8
  }⟩


-- @@ L83-85 verbatim
/-- A fixed regular value selected from the proved Sard output. -/
def transverseValue : TransverseValue m hm :=
  Classical.choice (transverseValue_nonempty m hm)


-- @@ L87-92 verbatim
/-- The incoming presentation induced by the concrete Cassini PT middle. -/
def sourceFLS : FramedLevelSet (m + 2) :=
  (sphereHomotopy m hm).sourceLevelSet
    (transverseValue m hm).target
    (transverseValue m hm).target_ne_zero
    (transverseValue m hm).regular


-- @@ L94-99 verbatim
/-- The outgoing presentation induced by the same common regular value. -/
def targetFLS : FramedLevelSet (m + 2) :=
  (sphereHomotopy m hm).targetLevelSet
    (transverseValue m hm).target
    (transverseValue m hm).target_ne_zero
    (transverseValue m hm).regular


-- @@ L101-107 verbatim
/-- Incoming north/south label at the chosen regular horizontal value. -/
def sourceSign : FiberSign (sourceFLS m hm) :=
  (sphereHomotopy m hm).sourceSign
    (transverseValue m hm).target
    (transverseValue m hm).target_ne_zero
    (transverseValue m hm).regular
    (transverseValue m hm).target_norm_lt_one


-- @@ L109-115 verbatim
/-- Outgoing north/south label at the same value. -/
def targetSign : FiberSign (targetFLS m hm) :=
  (sphereHomotopy m hm).targetSign
    (transverseValue m hm).target
    (transverseValue m hm).target_ne_zero
    (transverseValue m hm).regular
    (transverseValue m hm).target_norm_lt_one


-- @@ L117-125 verbatim
/-- The requested actual transverse PT datum; the middle has no remaining
constructor argument. -/
def transverseData : PTTransverseHomotopyData
    (sourceSign m hm) (targetSign m hm) :=
  (sphereHomotopy m hm).toPTTransverseHomotopyData
    (transverseValue m hm).target
    (transverseValue m hm).target_ne_zero
    (transverseValue m hm).regular
    (transverseValue m hm).target_norm_lt_one


-- @@ L127-129 verbatim
theorem nonempty_transverseData : Nonempty
    (PTTransverseHomotopyData (sourceSign m hm) (targetSign m hm)) :=
  ⟨transverseData m hm⟩


-- @@ L131-131 verbatim
end ConcreteZeroPairCassiniPTMiddle

-- @@ L132-132 verbatim
end Submission
