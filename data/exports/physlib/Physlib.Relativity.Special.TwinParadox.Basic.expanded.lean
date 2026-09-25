/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Special.ProperTime

-- @@ L9-26 verbatim
/-!
# Twin Paradox

The twin paradox corresponds to the following scenario:

Two twins start at the same point `startPoint` in spacetime.
Twin A travels at constant speed to the spacetime point `endPoint`,
whilst twin B makes a detour through the spacetime `twinBMid` and then to `endPoint`.

In this file, we assume that both twins travel at constant speed,
and that the acceleration of Twin B is instantaneous.

The conclusion of this scenario is that Twin A will be older than Twin B when they meet at
`endPoint`. This is something we show here with an explicit example.

The origin of the twin paradox dates back to Paul Langevin in 1911.

-/


-- @@ L28-28 verbatim
@[expose] public section


-- @@ L30-30 verbatim
noncomputable section


-- @@ L32-32 verbatim
namespace SpecialRelativity


-- @@ L34-34 verbatim
open Matrix

-- @@ L35-35 verbatim
open Real

-- @@ L36-36 verbatim
open Lorentz

-- @@ L37-37 verbatim
open Vector


-- @@ L39-49 verbatim
/-- The twin paradox assuming instantaneous acceleration. -/
structure InstantaneousTwinParadox where
  /-- The starting point of both twins. -/
  startPoint : SpaceTime 3
  /-- The end point of both twins. -/
  endPoint : SpaceTime 3
  /-- The point twin B travels to between the start point and the end point. -/
  twinBMid : SpaceTime 3
  endPoint_causallyFollows_startPoint : causallyFollows startPoint endPoint
  twinBMid_causallyFollows_startPoint : causallyFollows startPoint twinBMid
  endPoint_causallyFollows_twinBMid : causallyFollows twinBMid endPoint


-- @@ L51-51 verbatim
namespace InstantaneousTwinParadox

-- @@ L52-52 verbatim
variable (T: InstantaneousTwinParadox)

-- @@ L53-53 verbatim
open SpaceTime


-- @@ L55-57 verbatim
/-- The proper time experienced by twin A travelling at constant speed
  from `T.startPoint` to `T.endPoint`. -/
def properTimeTwinA : ℝ := SpaceTime.properTime T.startPoint T.endPoint


-- @@ L59-63 verbatim
/-- The proper time experienced by twin B travelling at constant speed
  from `T.startPoint` to `T.twinBMid`, and then from `T.twinBMid`
  to `T.endPoint`. -/
def properTimeTwinB : ℝ := SpaceTime.properTime T.startPoint T.twinBMid +
  SpaceTime.properTime T.twinBMid T.endPoint


-- @@ L65-66 verbatim
/-- The proper time of twin A minus the proper time of twin B. -/
def ageGap : ℝ := T.properTimeTwinA - T.properTimeTwinB


-- @@ L68-68 verbatim
TODO "Find the conditions for which the age gap for the twin paradox is zero."


-- @@ L70-74 expanded
/-- In the twin paradox with instantaneous acceleration, Twin A is always older
  then Twin B. -/
def ageGap_nonneg : InformalLemma where
  deps := [``ageGap]
  tag := "7ROVE"


-- @@ L76-80 verbatim
/-!

## Example 1

-/


-- @@ L82-122 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The twin paradox in which:
- Twin A starts at `0` and travels at constant
  speed to `[15, 0, 0, 0]`.
- Twin B starts at `0` and travels at constant speed to
  `[7.5, 6, 0, 0]` and then at (different) constant speed to `[15, 0, 0, 0]`. -/
def example1 : InstantaneousTwinParadox where
  startPoint := 0
  endPoint := (fun
    | Sum.inl 0 => 15
    | Sum.inr i => 0)
  twinBMid := (fun
    | Sum.inl 0 => 7.5
    | Sum.inr 0 => 6
    | Sum.inr i => 0)
  endPoint_causallyFollows_startPoint := by
    simp [causallyFollows]
    left
    simp only [interiorFutureLightCone, sub_zero, Fin.isValue, Set.mem_ofPred_eq, Nat.ofNat_pos,
      and_true]
    refine (timeLike_iff_norm_sq_pos _).mpr ?_
    rw [minkowskiProduct_toCoord]
    simp
  twinBMid_causallyFollows_startPoint := by
    simp only [causallyFollows]
    left
    simp only [interiorFutureLightCone, sub_zero, Fin.isValue, Set.mem_ofPred_eq]
    norm_num
    refine (timeLike_iff_norm_sq_pos _).mpr ?_
    rw [minkowskiProduct_toCoord]
    simp [Fin.sum_univ_three]
    norm_num
  endPoint_causallyFollows_twinBMid := by
    simp [causallyFollows]
    left
    simp [interiorFutureLightCone]
    norm_num
    refine (timeLike_iff_norm_sq_pos _).mpr ?_
    rw [minkowskiProduct_toCoord]
    simp [Fin.sum_univ_three]
    norm_num


-- @@ L124-127 verbatim
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma example1_properTimeTwinA : example1.properTimeTwinA = 15 := by
  simp [properTimeTwinA, example1, properTime, minkowskiProduct_toCoord]


-- @@ L129-134 verbatim
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma example1_properTimeTwinB : example1.properTimeTwinB = 9 := by
  simp [properTimeTwinB, properTime, example1, minkowskiProduct_toCoord, Fin.sum_univ_three]
  norm_num [show √81 = 9 from sqrt_eq_cases.mpr (by norm_num),
    show √4 = 2 from sqrt_eq_cases.mpr (by norm_num)]


-- @@ L136-137 verbatim
lemma example1_ageGap : example1.ageGap = 6 := by
  norm_num [ageGap]


-- @@ L139-139 verbatim
end InstantaneousTwinParadox


-- @@ L141-142 verbatim
TODO "Do the twin paradox with a non-instantaneous acceleration. This should be done
  in a different module."


-- @@ L144-144 verbatim
end SpecialRelativity


-- @@ L146-146 verbatim
end
