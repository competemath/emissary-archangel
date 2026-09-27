/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/
module

public import LeanPool.Wallace.CoefficientTransfiniteExtension
public import LeanPool.Wallace.TriangularPreprocess
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Order


-- @@ L18-23 verbatim
/-!
# Transfinite extension of an integer-valued local character

This file specializes the coefficient-parametric Wallace recursion to the free Abelian group.
An integer coordinate character is uniquely determined by its value at one.
-/


-- @@ L25-25 verbatim
@[expose] public section


-- @@ L27-27 verbatim
open Filter Set Topology


-- @@ L29-29 verbatim
namespace Wallace

-- @@ L30-30 verbatim
namespace TransfiniteExtension


-- @@ L32-32 verbatim
noncomputable section


-- @@ L34-34 verbatim
universe u


-- @@ L36-36 verbatim
open CoefficientTransfiniteExtension


-- @@ L38-43 verbatim
/-- Extend a prescribed circle value to the corresponding integer character. -/
def integerCoordinateExtension : CoordinateExtension ℤ where
  ofValue := fun t ↦ (zmultiplesHom UnitAddCircle) t
  ofValue_one := by
    intro t
    simp


-- @@ L45-46 verbatim
/-- Triangular data for integer-valued prepared sequences. -/
abbrev Data (I : Type u) [LT I] := CoefficientTransfiniteExtension.Data ℤ I


-- @@ L48-51 verbatim
/-- Closure under the integer prepared supports associated to local code coordinates. -/
abbrev ClosedUnderPreparedSupports {I : Type u} [LT I]
    (E : Data I) (D : Set I) : Prop :=
  CoefficientTransfiniteExtension.ClosedUnderPreparedSupports E D


-- @@ L53-56 verbatim
/-- The local integer character realizes every limit whose code coordinate is local. -/
abbrev LocallyAdmissible {I : Type u} [LT I] (E : Data I) (D : Set I)
    (character : (D →₀ ℤ) →+ UnitAddCircle) : Prop :=
  CoefficientTransfiniteExtension.LocallyAdmissible E D character


-- @@ L58-62 verbatim
/-- The global integer character produced by the shared transfinite recursion. -/
abbrev globalCharacter {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (E : Data I) (D : Set I) (character : (D →₀ ℤ) →+ UnitAddCircle) :
    (I →₀ ℤ) →+ UnitAddCircle :=
  CoefficientTransfiniteExtension.globalCharacter integerCoordinateExtension E D character


-- @@ L64-69 verbatim
theorem globalCharacter_eq_local_restriction {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (E : Data I) (D : Set I) (character : (D →₀ ℤ) →+ UnitAddCircle)
    (x : I →₀ ℤ) (hx : ∀ i ∈ x.support, i ∈ D) :
    globalCharacter E D character x = character (Finsupp.subtypeDomain D x) :=
  CoefficientTransfiniteExtension.globalCharacter_eq_local_restriction
    integerCoordinateExtension E D character x hx


-- @@ L71-79 verbatim
theorem globalCharacter_admissible {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (E : Data I) (D : Set I) (character : (D →₀ ℤ) →+ UnitAddCircle)
    (hclosed : ClosedUnderPreparedSupports E D)
    (hlocal : LocallyAdmissible E D character) :
    ∀ c : E.Code,
      Tendsto (fun n ↦ globalCharacter E D character (E.prepared c n)) (E.p c)
        (nhds (globalCharacter E D character (Finsupp.single (E.codeIndex c) 1))) :=
  CoefficientTransfiniteExtension.globalCharacter_admissible
    integerCoordinateExtension E D character hclosed hlocal


-- @@ L81-82 verbatim
/-- Integer transfinite-extension data over the canonical continuum index. -/
abbrev ContinuumData := Data TriangularPreprocess.ContinuumIndex


-- @@ L84-84 verbatim
end

-- @@ L85-85 verbatim
end TransfiniteExtension

-- @@ L86-86 verbatim
end Wallace
