/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.Permutations
public import Physlib.QFT.AnomalyCancellation.GroupActions

-- @@ L10-15 verbatim
/-!
# ACC system for SM with RHN and no gravitational anomaly.

We define the ACC system for the Standard Model with right-handed neutrinos and no gravitational
anomaly.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
namespace SMRHN

-- @@ L20-20 verbatim
open SMνCharges

-- @@ L21-21 verbatim
open SMνACCs

-- @@ L22-22 verbatim
open BigOperators


-- @@ L24-35 verbatim
/-- The ACC system for the SM plus RHN with no gravitational anomaly. -/
@[simps!]
def SMNoGrav (n : ℕ) : ACCSystem where
  toACCSystemCharges := SMνCharges n
  numberLinear := 2
  linearACCs := fun i =>
    match i with
    | 0 => @accSU2 n
    | 1 => accSU3
  numberQuadratic := 0
  quadraticACCs := fun i ↦ Fin.elim0 i
  cubicACC := accCube


-- @@ L37-37 verbatim
namespace SMNoGrav


-- @@ L39-39 verbatim
variable {n : ℕ}


-- @@ L41-41 verbatim
lemma SU2Sol (S : (SMNoGrav n).LinSols) : accSU2 S.val = 0 := S.linearSol ⟨0, by simp⟩


-- @@ L43-43 verbatim
lemma SU3Sol (S : (SMNoGrav n).LinSols) : accSU3 S.val = 0 := S.linearSol ⟨1, by simp⟩


-- @@ L45-45 verbatim
lemma cubeSol (S : (SMNoGrav n).Sols) : accCube S.val = 0 := S.cubicSol


-- @@ L47-55 verbatim
/-- An element of `charges` which satisfies the linear ACCs
  gives us a element of `LinSols`. -/
def chargeToLinear (S : (SMNoGrav n).Charges) (hSU2 : accSU2 S = 0) (hSU3 : accSU3 S = 0) :
    (SMNoGrav n).LinSols :=
  ⟨S, by
    intro i
    match i with
    | ⟨0, _⟩ => exact hSU2
    | ⟨1, _⟩ => exact hSU3⟩


-- @@ L57-59 verbatim
/-- An element of `LinSols` which satisfies the quadratic ACCs
  gives us a element of `QuadSols`. -/
def linearToQuad (S : (SMNoGrav n).LinSols) : (SMNoGrav n).QuadSols := ⟨S, fun i ↦ Fin.elim0 i⟩


-- @@ L61-64 verbatim
/-- An element of `QuadSols` which satisfies the quadratic ACCs
  gives us a element of `LinSols`. -/
def quadToAF (S : (SMNoGrav n).QuadSols) (hc : accCube S.val = 0) :
    (SMNoGrav n).Sols := ⟨S, hc⟩


-- @@ L66-70 verbatim
/-- An element of `charges` which satisfies the linear and quadratic ACCs
  gives us a element of `QuadSols`. -/
def chargeToQuad (S : (SMNoGrav n).Charges) (hSU2 : accSU2 S = 0) (hSU3 : accSU3 S = 0) :
    (SMNoGrav n).QuadSols :=
  linearToQuad $ chargeToLinear S hSU2 hSU3


-- @@ L72-76 verbatim
/-- An element of `charges` which satisfies the linear, quadratic and cubic ACCs
  gives us a element of `Sols`. -/
def chargeToAF (S : (SMNoGrav n).Charges) (hSU2 : accSU2 S = 0) (hSU3 : accSU3 S = 0)
    (hc : accCube S = 0) : (SMNoGrav n).Sols :=
  quadToAF (chargeToQuad S hSU2 hSU3) hc


-- @@ L78-82 verbatim
/-- An element of `LinSols` which satisfies the quadratic and cubic ACCs
  gives us a element of `Sols`. -/
def linearToAF (S : (SMNoGrav n).LinSols)
    (hc : accCube S.val = 0) : (SMNoGrav n).Sols :=
  quadToAF (linearToQuad S) hc


-- @@ L84-99 verbatim
/-- The permutations acting on the ACC system corresponding to the SM with RHN,
and no gravitational anomaly. -/
def perm (n : ℕ) : ACCSystemGroupAction (SMNoGrav n) where
  group := PermGroup n
  groupInst := inferInstance
  rep := repCharges
  linearInvariant := by
    intro i
    match i with
    | ⟨0, _⟩ => exact accSU2_invariant
    | ⟨1, _⟩ => exact accSU3_invariant
  quadInvariant := by
    intro i
    simp only [SMNoGrav_numberQuadratic] at i
    exact Fin.elim0 i
  cubicInvariant := accCube_invariant


-- @@ L101-101 verbatim
end SMNoGrav


-- @@ L103-103 verbatim
end SMRHN
