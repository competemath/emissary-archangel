/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.AnomalyCancellation.Basic

-- @@ L9-15 verbatim
/-!
# Anomaly Cancellation in the Standard Model without Gravity

This file defines the system of anomaly equations for the SM without RHN, and
without the gravitational ACC.

-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
namespace SM

-- @@ L20-20 verbatim
open SMCharges

-- @@ L21-21 verbatim
open SMACCs

-- @@ L22-22 verbatim
open BigOperators


-- @@ L24-37 verbatim
/-- The ACC system for the standard model without RHN and without the gravitational ACC. -/
@[simps!]
def SMNoGrav (n : ℕ) : ACCSystem where
  toACCSystemCharges := SMCharges n
  numberLinear := 2
  linearACCs := fun i =>
    match i with
    | 0 => @accSU2 n
    | 1 => accSU3
  numberQuadratic := 0
  quadraticACCs := by
    intro i
    exact Fin.elim0 i
  cubicACC := accCube


-- @@ L39-39 verbatim
namespace SMNoGrav


-- @@ L41-41 verbatim
variable {n : ℕ}


-- @@ L43-48 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The charges in `(SMNoGrav n).LinSols` satisfy the `SU(2)` anomaly-equation. -/
lemma SU2Sol (S : (SMNoGrav n).LinSols) : accSU2 S.val = 0 := by
  have hS := S.linearSol
  simp only [SMNoGrav_linearACCs] at hS
  exact hS ⟨0, by simp⟩


-- @@ L50-55 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The charges in `(SMNoGrav n).LinSols` satisfy the `SU(3)` anomaly-equation. -/
lemma SU3Sol (S : (SMNoGrav n).LinSols) : accSU3 S.val = 0 := by
  have hS := S.linearSol
  simp only [SMNoGrav_linearACCs] at hS
  exact hS ⟨1, by simp⟩


-- @@ L57-58 verbatim
/-- The charges in `(SMNoGrav n).Sols` satisfy the cubic anomaly-equation. -/
lemma cubeSol (S : (SMNoGrav n).Sols) : accCube S.val = 0 := S.cubicSol


-- @@ L60-68 verbatim
/-- An element of `charges` which satisfies the linear ACCs
  gives us a element of `AnomalyFreeLinear`. -/
def chargeToLinear (S : (SMNoGrav n).Charges) (hSU2 : accSU2 S = 0) (hSU3 : accSU3 S = 0) :
    (SMNoGrav n).LinSols :=
  ⟨S, by
    intro i
    match i with
    | ⟨0, _⟩ => exact hSU2
    | ⟨1, _⟩ => exact hSU3⟩


-- @@ L70-75 verbatim
/-- An element of `AnomalyFreeLinear` which satisfies the quadratic ACCs
  gives us a element of `AnomalyFreeQuad`. -/
def linearToQuad (S : (SMNoGrav n).LinSols) : (SMNoGrav n).QuadSols :=
  ⟨S, by
    intro i
    exact Fin.elim0 i⟩


-- @@ L77-80 verbatim
/-- An element of `AnomalyFreeQuad` which satisfies the quadratic ACCs
  gives us a element of `AnomalyFree`. -/
def quadToAF (S : (SMNoGrav n).QuadSols) (hc : accCube S.val = 0) :
    (SMNoGrav n).Sols := ⟨S, hc⟩


-- @@ L82-86 verbatim
/-- An element of `charges` which satisfies the linear and quadratic ACCs
  gives us a element of `AnomalyFreeQuad`. -/
def chargeToQuad (S : (SMNoGrav n).Charges) (hSU2 : accSU2 S = 0) (hSU3 : accSU3 S = 0) :
    (SMNoGrav n).QuadSols :=
  linearToQuad $ chargeToLinear S hSU2 hSU3


-- @@ L88-92 verbatim
/-- An element of `charges` which satisfies the linear, quadratic and cubic ACCs
  gives us a element of `AnomalyFree`. -/
def chargeToAF (S : (SMNoGrav n).Charges) (hSU2 : accSU2 S = 0) (hSU3 : accSU3 S = 0)
    (hc : accCube S = 0) : (SMNoGrav n).Sols :=
  quadToAF (chargeToQuad S hSU2 hSU3) hc


-- @@ L94-98 verbatim
/-- An element of `AnomalyFreeLinear` which satisfies the quadratic and cubic ACCs
  gives us a element of `AnomalyFree`. -/
def linearToAF (S : (SMNoGrav n).LinSols)
    (hc : accCube S.val = 0) : (SMNoGrav n).Sols :=
  quadToAF (linearToQuad S) hc


-- @@ L100-100 verbatim
end SMNoGrav


-- @@ L102-102 verbatim
end SM
