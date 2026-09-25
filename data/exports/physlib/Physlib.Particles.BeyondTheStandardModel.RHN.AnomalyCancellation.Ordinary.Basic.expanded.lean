/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.Permutations
public import Physlib.QFT.AnomalyCancellation.GroupActions

-- @@ L10-14 verbatim
/-!
# ACC system for SM with RHN (without hypercharge).

We define the ACC system for the Standard Model (without hypercharge) with right-handed neutrinos.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
namespace SMRHN

-- @@ L19-19 verbatim
open SMνCharges

-- @@ L20-20 verbatim
open SMνACCs

-- @@ L21-21 verbatim
open BigOperators


-- @@ L23-35 verbatim
/-- The ACC system for the SM plus RHN. -/
@[simps!]
def SM (n : ℕ) : ACCSystem where
  toACCSystemCharges := SMνCharges n
  numberLinear := 3
  linearACCs := fun i =>
    match i with
    | 0 => @accGrav n
    | 1 => accSU2
    | 2 => accSU3
  numberQuadratic := 0
  quadraticACCs := fun i ↦ Fin.elim0 i
  cubicACC := accCube


-- @@ L37-37 verbatim
namespace SM


-- @@ L39-39 verbatim
variable {n : ℕ}


-- @@ L41-41 verbatim
lemma gravSol (S : (SM n).LinSols) : accGrav S.val = 0 := S.linearSol ⟨0, by simp⟩


-- @@ L43-43 verbatim
lemma SU2Sol (S : (SM n).LinSols) : accSU2 S.val = 0 := S.linearSol ⟨1, by simp⟩


-- @@ L45-45 verbatim
lemma SU3Sol (S : (SM n).LinSols) : accSU3 S.val = 0 := S.linearSol ⟨2, by simp⟩


-- @@ L47-47 verbatim
lemma cubeSol (S : (SM n).Sols) : accCube S.val = 0 := S.cubicSol


-- @@ L49-58 verbatim
/-- An element of `charges` which satisfies the linear ACCs
  gives us a element of `LinSols`. -/
def chargeToLinear (S : (SM n).Charges) (hGrav : accGrav S = 0)
    (hSU2 : accSU2 S = 0) (hSU3 : accSU3 S = 0) : (SM n).LinSols :=
  ⟨S, by
    intro i
    match i with
    | ⟨0, _⟩ => exact hGrav
    | ⟨1, _⟩ => exact hSU2
    | ⟨2, _⟩ => exact hSU3⟩


-- @@ L60-63 verbatim
/-- An element of `LinSols` which satisfies the quadratic ACCs
  gives us a element of `QuadSols`. -/
def linearToQuad (S : (SM n).LinSols) : (SM n).QuadSols :=
  ⟨S, fun i ↦ Fin.elim0 i⟩


-- @@ L65-68 verbatim
/-- An element of `QuadSols` which satisfies the quadratic ACCs
  gives us a element of `Sols`. -/
def quadToAF (S : (SM n).QuadSols) (hc : accCube S.val = 0) :
    (SM n).Sols := ⟨S, hc⟩


-- @@ L70-75 verbatim
/-- An element of `charges` which satisfies the linear and quadratic ACCs
  gives us a element of `QuadSols`. -/
def chargeToQuad (S : (SM n).Charges) (hGrav : accGrav S = 0)
    (hSU2 : accSU2 S = 0) (hSU3 : accSU3 S = 0) :
    (SM n).QuadSols :=
  linearToQuad $ chargeToLinear S hGrav hSU2 hSU3


-- @@ L77-81 verbatim
/-- An element of `charges` which satisfies the linear, quadratic and cubic ACCs
  gives us a element of `Sols`. -/
def chargeToAF (S : (SM n).Charges) (hGrav : accGrav S = 0) (hSU2 : accSU2 S = 0)
    (hSU3 : accSU3 S = 0) (hc : accCube S = 0) : (SM n).Sols :=
  quadToAF (chargeToQuad S hGrav hSU2 hSU3) hc


-- @@ L83-87 verbatim
/-- An element of `LinSols` which satisfies the quadratic and cubic ACCs
  gives us a element of `Sols`. -/
def linearToAF (S : (SM n).LinSols)
    (hc : accCube S.val = 0) : (SM n).Sols :=
  quadToAF (linearToQuad S) hc


-- @@ L89-104 verbatim
/-- The permutations acting on the ACC system corresponding to the SM with RHN. -/
def perm (n : ℕ) : ACCSystemGroupAction (SM n) where
  group := PermGroup n
  groupInst := inferInstance
  rep := repCharges
  linearInvariant := by
    intro i
    match i with
    | ⟨0, _⟩ => exact accGrav_invariant
    | ⟨1, _⟩ => exact accSU2_invariant
    | ⟨2, _⟩ => exact accSU3_invariant
  quadInvariant := by
    intro i
    simp only [SM_numberQuadratic] at i
    exact Fin.elim0 i
  cubicInvariant := accCube_invariant


-- @@ L106-106 verbatim
end SM


-- @@ L108-108 verbatim
end SMRHN
