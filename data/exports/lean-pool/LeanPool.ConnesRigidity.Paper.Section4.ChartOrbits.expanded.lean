/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-

Concrete SL₃ orbit witnesses for the finite polynomial charts. Paper: §4.
-/
module

public import LeanPool.ConnesRigidity.Paper.Section4.FiniteCharts
public import LeanPool.ConnesRigidity.Construction.PaperActions
import LeanPool.ConnesRigidity.Construction.PaperActionInstances


-- @@ L16-18 verbatim
/-!
The chart orbits component of the Connes rigidity formalization.
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
namespace Connes

-- @@ L23-23 verbatim
namespace PaperChartOrbits


-- @@ L25-25 verbatim
open Construction

-- @@ L26-26 verbatim
open Construction.PaperKernel

-- @@ L27-27 verbatim
open PaperFiniteCharts


-- @@ L29-29 verbatim
noncomputable section


-- @@ L31-34 verbatim
/--
The `F` construction used in the Connes rigidity formalization.
-/
abbrev F := Construction.k

-- @@ L35-38 verbatim
/--
The `R` construction used in the Connes rigidity formalization.
-/
abbrev R := Construction.R

-- @@ L39-45 verbatim
/--
The `A` construction used in the Connes rigidity formalization.
-/
abbrev A := Construction.A

/- The three basis points are connected by elementary determinant-one moves.
Paper: §4. -/

-- @@ L46-46 verbatim
theorem h10 : (1 : Fin 3) ≠ 0 := by decide

-- @@ L47-47 verbatim
theorem h01 : (0 : Fin 3) ≠ 1 := by decide

-- @@ L48-48 verbatim
theorem h20 : (2 : Fin 3) ≠ 0 := by decide

-- @@ L49-49 verbatim
theorem h02 : (0 : Fin 3) ≠ 2 := by decide


-- @@ L51-55 verbatim
/--
The `t10` construction used in the Connes rigidity formalization.
-/
def t10 : SpecialLinear.SL3 :=
  Matrix.SpecialLinearGroup.transvection h10 1

-- @@ L56-60 verbatim
/--
The `t01` construction used in the Connes rigidity formalization.
-/
def t01 : SpecialLinear.SL3 :=
  Matrix.SpecialLinearGroup.transvection h01 1

-- @@ L61-65 verbatim
/--
The `t20` construction used in the Connes rigidity formalization.
-/
def t20 : SpecialLinear.SL3 :=
  Matrix.SpecialLinearGroup.transvection h20 1

-- @@ L66-70 verbatim
/--
The `t02` construction used in the Connes rigidity formalization.
-/
def t02 : SpecialLinear.SL3 :=
  Matrix.SpecialLinearGroup.transvection h02 1


-- @@ L72-75 verbatim
/--
The `moveOne` construction used in the Connes rigidity formalization.
-/
def moveOne : SpecialLinear.SL3 := t10 * (t01 * t10)

-- @@ L76-79 verbatim
/--
The `moveTwo` construction used in the Connes rigidity formalization.
-/
def moveTwo : SpecialLinear.SL3 := t20 * (t02 * t20)


-- @@ L81-85 verbatim
/--
The `basisMove` construction used in the Connes rigidity formalization.
-/
def basisMove (s : Fin 3) : SpecialLinear.SL3 :=
  if s = 0 then 1 else if s = 1 then moveOne else moveTwo


-- @@ L87-97 verbatim
theorem transvection_action_vector {i j : Fin 3} (hij : i ≠ j)
    (a : R) (x : A) :
    sl3AAction (Matrix.SpecialLinearGroup.transvection hij a) x =
      fun r => if r = i then x r + a * x j else x r := by
  funext r
  by_cases hri : r = i
  · subst r
    rw [transvection_action_apply_target hij a x]
    simp
  · rw [transvection_action_apply_of_ne_target hij hri a x]
    simp [hri]


-- @@ L99-107 verbatim
theorem moveOne_apply :
    sl3AAction moveOne (basisVector 0) = basisVector 1 := by
  simp only [moveOne, t10, t01, map_mul, LinearEquiv.mul_apply]
  rw [transvection_action_vector h10 1,
    transvection_action_vector h01 1,
    transvection_action_vector h10 1]
  funext i
  fin_cases i <;> simp [basisVector,
    CharTwo.add_self_eq_zero]


-- @@ L109-117 verbatim
theorem moveTwo_apply :
    sl3AAction moveTwo (basisVector 0) = basisVector 2 := by
  simp only [moveTwo, t20, t02, map_mul, LinearEquiv.mul_apply]
  rw [transvection_action_vector h20 1,
    transvection_action_vector h02 1,
    transvection_action_vector h20 1]
  funext i
  fin_cases i <;> simp [basisVector,
    CharTwo.add_self_eq_zero]


-- @@ L119-128 verbatim
theorem basisMove_apply (s : Fin 3) :
    sl3AAction (basisMove s) (basisVector 0) = basisVector s := by
  fin_cases s
  · simp [basisMove, basisVector, sl3AAction]
  · simpa [basisMove] using moveOne_apply
  · simpa [basisMove] using moveTwo_apply

/- Shears add the two polynomial coefficients while fixing the distinguished
coordinate. Paper: §4.
-/

-- @@ L129-136 verbatim
/--
The `chartOrbitWitness` construction used in the Connes rigidity formalization.
-/
def chartOrbitWitness (s : Fin 3) (f h : R) : SpecialLinear.SL3 :=
  Matrix.SpecialLinearGroup.transvection
      (i := nextNext s) (j := s) (nextNext_ne s) h *
    (Matrix.SpecialLinearGroup.transvection
        (i := next s) (j := s) (next_ne s) f * basisMove s)


-- @@ L138-150 verbatim
theorem chartOrbitWitness_apply (s : Fin 3) (f h : R) :
    sl3AAction (chartOrbitWitness s f h) (basisVector 0) =
      chartVector s f h := by
  simp only [chartOrbitWitness, map_mul, LinearEquiv.mul_apply]
  rw [transvection_action_vector (nextNext_ne s) h,
    transvection_action_vector (next_ne s) f,
    basisMove_apply]
  funext i
  fin_cases s <;> fin_cases i <;>
    simp [chartVector, basisVector, next, nextNext]

/- Every finite chart point belongs to the SL₃ orbit of the base point.
Paper: Lemma 4.2. -/

-- @@ L151-160 verbatim
theorem chartPoint_in_orbit (N : ℕ) (s : Fin 3)
    (f h : Fin N → F) :
    ∃ g : SpecialLinear.SL3,
      sl3AAction g (basisVector 0) = chartPoint N (s, f, h) := by
  refine ⟨chartOrbitWitness s (Polynomial.ofFn N f) (Polynomial.ofFn N h), ?_⟩
  rw [chartOrbitWitness_apply]
  rfl

/- Squaring transports the chart orbit statement to the symmetric tensor
carrier. Paper: Lemma 4.2. -/

-- @@ L161-169 verbatim
theorem chartSquare_in_orbit (N : ℕ) (s : Fin 3)
    (f h : Fin N → F) :
    ∃ g : SpecialLinear.SL3,
      sl3CAction g (PaperKernel.diagonal (basisVector 0)) =
        chartSquare N (s, f, h) := by
  obtain ⟨g, hg⟩ := chartPoint_in_orbit N s f h
  refine ⟨g, ?_⟩
  rw [sl3CAction_diagonal, hg]
  rfl


-- @@ L171-171 verbatim
end

-- @@ L172-172 verbatim
end PaperChartOrbits

-- @@ L173-173 verbatim
end Connes
