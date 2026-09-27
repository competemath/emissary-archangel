/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/
module

public import LeanPool.Wallace.CoefficientTransfiniteExtension
public import LeanPool.Wallace.RationalTriangularPreprocess
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Order


-- @@ L19-25 verbatim
/-!
# Transfinite extension for the rational direct sum

This file supplies the coefficient-specific input to the shared transfinite recursion. Baer's
extension theorem extends the integer character with prescribed value at one to a character on
each rational coordinate.
-/


-- @@ L27-27 verbatim
@[expose] public section


-- @@ L29-29 verbatim
open Filter Set Topology


-- @@ L31-31 verbatim
namespace Wallace

-- @@ L32-32 verbatim
namespace RationalTransfiniteExtension


-- @@ L34-34 verbatim
noncomputable section


-- @@ L36-36 verbatim
universe u


-- @@ L38-38 verbatim
open CoefficientTransfiniteExtension


-- @@ L40-42 verbatim
/-- The integer character with prescribed value at one. -/
def integerCircleHom (t : UnitAddCircle) : ℤ →+ UnitAddCircle :=
  (zmultiplesHom UnitAddCircle) t


-- @@ L44-47 verbatim
private theorem intCastAddHom_rational_injective :
    Function.Injective (Int.castAddHom ℚ) := by
  intro m n h
  exact Rat.intCast_injective h


-- @@ L49-53 verbatim
/-- An additive homomorphism on `ℚ` extending the integer character with value `t` at one. -/
def extendRationalCoordinate (t : UnitAddCircle) : ℚ →+ UnitAddCircle :=
  Classical.choose <| private_decl%
    ((Module.Baer.of_divisible UnitAddCircle).extension_property_addMonoidHom
      (Int.castAddHom ℚ) intCastAddHom_rational_injective (integerCircleHom t))


-- @@ L55-59 verbatim
private theorem extendRationalCoordinate_comp_intCast (t : UnitAddCircle) :
    (extendRationalCoordinate t).comp (Int.castAddHom ℚ) = integerCircleHom t :=
  Classical.choose_spec <|
    (Module.Baer.of_divisible UnitAddCircle).extension_property_addMonoidHom
      (Int.castAddHom ℚ) intCastAddHom_rational_injective (integerCircleHom t)


-- @@ L61-65 verbatim
@[simp]
private theorem extendRationalCoordinate_one (t : UnitAddCircle) :
    extendRationalCoordinate t 1 = t := by
  have h := DFunLike.congr_fun (extendRationalCoordinate_comp_intCast t) 1
  simpa [integerCircleHom] using h


-- @@ L67-70 verbatim
/-- Baer's extension supplies the coordinate extension used by the generic recursion. -/
def rationalCoordinateExtension : CoordinateExtension ℚ where
  ofValue := extendRationalCoordinate
  ofValue_one := by exact extendRationalCoordinate_one


-- @@ L72-73 verbatim
/-- Triangular data for rational-valued prepared sequences. -/
abbrev Data (I : Type u) [LT I] := CoefficientTransfiniteExtension.Data ℚ I


-- @@ L75-78 verbatim
/-- Closure under the rational prepared supports associated to local code coordinates. -/
abbrev ClosedUnderPreparedSupports {I : Type u} [LT I]
    (E : Data I) (D : Set I) : Prop :=
  CoefficientTransfiniteExtension.ClosedUnderPreparedSupports E D


-- @@ L80-83 verbatim
/-- The local rational character realizes every limit whose code coordinate is local. -/
abbrev LocallyAdmissible {I : Type u} [LT I] (E : Data I) (D : Set I)
    (character : (D →₀ ℚ) →+ UnitAddCircle) : Prop :=
  CoefficientTransfiniteExtension.LocallyAdmissible E D character


-- @@ L85-89 verbatim
/-- The global rational character produced by the shared transfinite recursion. -/
abbrev globalCharacter {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (E : Data I) (D : Set I) (character : (D →₀ ℚ) →+ UnitAddCircle) :
    (I →₀ ℚ) →+ UnitAddCircle :=
  CoefficientTransfiniteExtension.globalCharacter rationalCoordinateExtension E D character


-- @@ L91-96 verbatim
theorem globalCharacter_eq_local_restriction {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (E : Data I) (D : Set I) (character : (D →₀ ℚ) →+ UnitAddCircle)
    (x : I →₀ ℚ) (hx : ∀ i ∈ x.support, i ∈ D) :
    globalCharacter E D character x = character (Finsupp.subtypeDomain D x) :=
  CoefficientTransfiniteExtension.globalCharacter_eq_local_restriction
    rationalCoordinateExtension E D character x hx


-- @@ L98-106 verbatim
theorem globalCharacter_admissible {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (E : Data I) (D : Set I) (character : (D →₀ ℚ) →+ UnitAddCircle)
    (hclosed : ClosedUnderPreparedSupports E D)
    (hlocal : LocallyAdmissible E D character) :
    ∀ c : E.Code,
      Tendsto (fun n ↦ globalCharacter E D character (E.prepared c n)) (E.p c)
        (nhds (globalCharacter E D character (Finsupp.single (E.codeIndex c) 1))) :=
  CoefficientTransfiniteExtension.globalCharacter_admissible
    rationalCoordinateExtension E D character hclosed hlocal


-- @@ L108-109 verbatim
/-- Rational transfinite-extension data over the canonical continuum index. -/
abbrev ContinuumData := Data RationalTriangularPreprocess.ContinuumIndex


-- @@ L111-111 verbatim
end

-- @@ L112-112 verbatim
end RationalTransfiniteExtension

-- @@ L113-113 verbatim
end Wallace
