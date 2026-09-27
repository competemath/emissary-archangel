/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/
module

public import LeanPool.Wallace.RationalFusionRun
public import LeanPool.Wallace.FullTopology
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init


-- @@ L13-19 verbatim
/-!
# Global assembly for the rational vector group

The local fusion around each nonzero vector is extended by the rational transfinite recursion.
The resulting compatible characters separate points and realize the nonzero ultrafilter limit
attached to every injective rational sequence.
-/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
open Filter Set Topology


-- @@ L25-25 verbatim
namespace Wallace

-- @@ L26-26 verbatim
namespace RationalAssembly


-- @@ L28-28 verbatim
noncomputable section


-- @@ L30-30 verbatim
open RationalTriangularPreprocess

-- @@ L31-31 verbatim
open RationalData

-- @@ L32-32 verbatim
open BlockData

-- @@ L33-33 verbatim
open RationalClosure

-- @@ L34-34 verbatim
open RationalFusionRun

-- @@ L35-35 verbatim
open RationalTransfiniteExtension


-- @@ L37-38 verbatim
/-- The block-size schedule used by the assembled rational construction. -/
abbrev N : ℕ → ℕ := RationalFusionRun.blockSize

-- @@ L39-39 verbatim
theorem hN (l : ℕ) : 0 < N l := RationalFusionRun.blockSize_pos l

-- @@ L40-41 verbatim
/-- The bounded-independence schedule used by the assembled rational construction. -/
abbrev M : ℕ → ℕ := RationalFusionRun.independenceBound


-- @@ L43-46 verbatim
/-- The local limiting character supplied by the concrete fusion. -/
def localCharacter (x : {x : ContinuumRationalGroup // x ≠ 0}) :
    (closure N hN M x.1 →₀ ℚ) →+ UnitAddCircle :=
  (localRunCertificate x).run.limitCharacter


-- @@ L48-51 verbatim
theorem localCharacter_self_ne_zero
    (x : {x : ContinuumRationalGroup // x ≠ 0}) :
    localCharacter x (Finsupp.subtypeDomain (closure N hN M x.1) x.1) ≠ 0 :=
  (localRunCertificate x).self_ne_zero


-- @@ L53-57 verbatim
theorem localCharacter_admissible
    (x : {x : ContinuumRationalGroup // x ≠ 0}) :
    LocallyAdmissible (transfiniteData N hN M) (closure N hN M x.1)
      (localCharacter x) :=
  (localRunCertificate x).locallyAdmissible


-- @@ L59-63 verbatim
/-- Extend the local character to all continuum coordinates. -/
def globalCharacter (x : {x : ContinuumRationalGroup // x ≠ 0}) :
    ContinuumRationalGroup →+ UnitAddCircle :=
  RationalTransfiniteExtension.globalCharacter (transfiniteData N hN M)
    (closure N hN M x.1) (localCharacter x)


-- @@ L65-71 verbatim
theorem globalCharacter_self_ne_zero
    (x : {x : ContinuumRationalGroup // x ≠ 0}) :
    globalCharacter x x.1 ≠ 0 := by
  rw [globalCharacter,
    RationalTransfiniteExtension.globalCharacter_eq_local_restriction]
  · exact localCharacter_self_ne_zero x
  · exact support_subset_closure N hN M x.1


-- @@ L73-82 verbatim
theorem globalCharacter_admissible
    (x : {x : ContinuumRationalGroup // x ≠ 0}) (a : ContinuumIndex) :
    Tendsto
      (fun n ↦ globalCharacter x (prepared N hN M a n))
      (ultrafilter N hN a)
      (nhds (globalCharacter x (codeBasisVector a))) := by
  exact RationalTransfiniteExtension.globalCharacter_admissible
    (transfiniteData N hN M) (closure N hN M x.1) (localCharacter x)
    (closure_closedUnderPreparedSupports N hN M x.1)
    (localCharacter_admissible x) a


-- @@ L84-99 verbatim
/-- The complete character package for the rational direct sum of rank continuum. -/
def fullCharacterPackage : FullCharacterPackage ContinuumRationalGroup where
  Code := ContinuumIndex
  codeEquiv := rationalSequenceCodeEquiv
  subsequence := selector N hN M
  subsequence_strictMono := selector_strictMono N hN M
  ultrafilter := ultrafilter N hN
  ultrafilter_free := ultrafilter_free N hN
  limitPoint := codeBasisVector
  limitPoint_ne_zero := fun _ ↦ Finsupp.single_ne_zero.mpr one_ne_zero
  CharacterIndex := {x : ContinuumRationalGroup // x ≠ 0}
  character := globalCharacter
  character_detects x hx := ⟨⟨x, hx⟩, globalCharacter_self_ne_zero ⟨x, hx⟩⟩
  character_limit := by
    intro a x
    exact globalCharacter_admissible x a


-- @@ L101-105 verbatim
/-- The rational vector group of continuum rank has the full constructed topology: Hausdorff,
countably compact, totally bounded, and with only eventually constant convergent sequences. -/
theorem continuumRationalGroup_mainTheorem :
    RationalVectorGroupConclusion ContinuumIndex :=
  fullCharacterPackage.rationalVectorGroupConclusion


-- @@ L107-107 verbatim
end

-- @@ L108-108 verbatim
end RationalAssembly

-- @@ L109-109 verbatim
end Wallace
