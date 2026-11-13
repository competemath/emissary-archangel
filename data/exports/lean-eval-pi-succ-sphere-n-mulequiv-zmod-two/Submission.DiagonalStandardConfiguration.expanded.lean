import Mathlib
import Submission.CodomainEquivDelta
import Submission.FlatConfigurationAssembly


-- @@ L5-17 verbatim
/-!
# Concrete standards for the diagonal signed invariant

Bridge fibers carry the same positive and negative framed delta.  Consequently
the final bridge classification only needs two standard signed presentations:
one for `(0, 0)` and one for `(1, 1)`.

This file constructs both presentations with one literal common value at
spatial infinity.  The zero standard is the empty presentation.  The one
standard is the harmonized once-twisted tube bridge: its northern class-zero
circle and its compensating southern sheet both have delta one.  No
normalization or cobordism-existence hypothesis is introduced here.
-/


-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
namespace Submission

-- @@ L22-22 verbatim
namespace DiagonalStandardConfiguration


-- @@ L24-24 verbatim
variable (m : ℕ)


-- @@ L26-26 verbatim
local notation "c" => CompactBirth.background (m + 1)


-- @@ L28-30 verbatim
/-- The empty spatially flat standard for the invariant pair `(0, 0)`. -/
def zero : FlatSignedConfiguration (m + 2) c :=
  FlatSignedConfiguration.empty c (CompactBirth.background_ne_zero (m + 1))


-- @@ L32-40 verbatim
/-- The harmonized once-twisted bridge as a spatially flat standard for the
invariant pair `(1, 1)`. -/
def one : FlatSignedConfiguration (m + 2) c where
  X := ZeroFramedConfiguration.harmonizedX m
  sign := ZeroFramedConfiguration.harmonizedSign m
  center := 0
  radius := m + 4
  radius_nonneg := by positivity
  flatOutside := ZeroFramedConfiguration.harmonized_flatOutside m


-- @@ L42-45 verbatim
/-- Select the empty or once-twisted standard according to the mod-two
invariant. -/
def standard (d : ZMod 2) : FlatSignedConfiguration (m + 2) c :=
  if d = 0 then zero m else one m


-- @@ L47-54 verbatim
/-- The empty standard has no fiber points. -/
theorem zero_fiber_eq_empty : (zero m).X.fiber = ∅ := by
  change (FlatSignedConfiguration.backgroundFLS c
    (CompactBirth.background_ne_zero (m + 1))).fiber = ∅
  ext x
  simp only [FramedLevelSet.fiber, Set.mem_setOf_eq,
    Set.mem_empty_iff_false, iff_false]
  exact CompactBirth.background_ne_zero (m + 1)


-- @@ L56-57 verbatim
@[simp] theorem zero_positiveDelta : (zero m).sign.positiveDelta = 0 :=
  FiberSign.positiveDelta_eq_zero_of_fiber_eq_empty _ (zero_fiber_eq_empty m)


-- @@ L59-60 verbatim
@[simp] theorem zero_negativeDelta : (zero m).sign.negativeDelta = 0 :=
  FiberSign.negativeDelta_eq_zero_of_fiber_eq_empty _ (zero_fiber_eq_empty m)


-- @@ L62-67 verbatim
/-- The positive sheet of the nontrivial standard has delta one, by the
explicit once-twisted tube computation. -/
@[simp] theorem one_positiveDelta : (one m).sign.positiveDelta = 1 := by
  change (ZeroFramedConfiguration.harmonizedSign m).positiveDelta = 1
  rw [ZeroFramedConfiguration.harmonized_positiveDelta,
    ZeroFramedConfiguration.positiveDelta_eq_one]


-- @@ L69-76 verbatim
/-- Global signed-cobordism invariance identifies the compensating southern
sheet of the nontrivial standard with the northern delta. -/
@[simp] theorem one_negativeDelta
    (I : SignedCobordismDeltaInvariant (m + 2)) :
    (one m).sign.negativeDelta = 1 := by
  change (ZeroFramedConfiguration.harmonizedSign m).negativeDelta = 1
  rw [ZeroFramedConfiguration.harmonized_negativeDelta,
    ZeroFramedConfiguration.negativeDelta_eq_one m I]


-- @@ L78-83 verbatim
/-- The selected standard realizes its prescribed positive invariant. -/
@[simp] theorem standard_positiveDelta (d : ZMod 2) :
    (standard m d).sign.positiveDelta = d := by
  rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) d with rfl | rfl
  · simp [standard]
  · simp [standard]


-- @@ L85-92 verbatim
/-- The selected standard realizes the same prescribed invariant on its
negative sheet. -/
@[simp] theorem standard_negativeDelta
    (I : SignedCobordismDeltaInvariant (m + 2)) (d : ZMod 2) :
    (standard m d).sign.negativeDelta = d := by
  rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) d with rfl | rfl
  · simp [standard]
  · simp [standard, I]


-- @@ L94-100 verbatim
/-- Both signed sheets of every concrete bridge standard have the same
prescribed delta. -/
theorem standard_delta_pair
    (I : SignedCobordismDeltaInvariant (m + 2)) (d : ZMod 2) :
    (standard m d).sign.positiveDelta = d ∧
      (standard m d).sign.negativeDelta = d :=
  ⟨standard_positiveDelta m d, standard_negativeDelta m I d⟩


-- @@ L102-102 verbatim
end DiagonalStandardConfiguration

-- @@ L103-103 verbatim
end Submission
