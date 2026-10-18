import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Derivation.Basic


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-13 verbatim
/-!
# Exact rings in the noncoordinate obstruction

These transparent definitions fix the independent variables and relations in
Sections 2–5 of the paper. The relations define the quadric and determinant
rings used to obstruct polynomial coordinateness.
-/


-- @@ L15-15 verbatim
namespace StableCoordinate.Obstruction


-- @@ L17-17 verbatim
open MvPolynomial


-- @@ L19-19 verbatim
abbrev P (k : Type*) [CommRing k] (n : ℕ) := MvPolynomial (Fin n) k


-- @@ L21-21 verbatim
variable (k : Type*) [CommRing k]


-- @@ L23-24 verbatim
/-- The source's determinant invariant in `k[p,s,u,F,J]`. -/
noncomputable def xP : P k 5 := X 1 ^ 2 - X 2 ^ 2 + X 0 * X 3


-- @@ L26-28 verbatim
/-- Highest weighted part of the source hypersurface equation. -/
noncomputable def Hstar : P k 5 :=
  xP k ^ 2 * X 3 - (1 + 2 * X 1 * xP k) * X 4 - X 0 * X 4 ^ 2


-- @@ L30-30 verbatim
noncomputable def H : P k 5 := Hstar k - X 2

-- @@ L31-31 verbatim
noncomputable def idealA : Ideal (P k 5) := Ideal.span {H k}

-- @@ L32-32 verbatim
noncomputable def idealG : Ideal (P k 5) := Ideal.span {Hstar k}

-- @@ L33-33 verbatim
abbrev A := P k 5 ⧸ idealA k

-- @@ L34-34 verbatim
abbrev G := P k 5 ⧸ idealG k


-- @@ L36-37 verbatim
/-- Generator images of the original polynomial presentation. -/
noncomputable def aX (i : Fin 5) : A k := Ideal.Quotient.mk (idealA k) (X i)

-- @@ L38-39 verbatim
/-- Generator images of the weighted degeneration presentation. -/
noncomputable def gX (i : Fin 5) : G k := Ideal.Quotient.mk (idealG k) (X i)


-- @@ L41-41 verbatim
noncomputable def quadricRelation : P k 4 := X 0 * X 1 - X 2 * (X 2 + 1)

-- @@ L42-42 verbatim
noncomputable def idealB : Ideal (P k 4) := Ideal.span {quadricRelation k}

-- @@ L43-43 verbatim
abbrev B := P k 4 ⧸ idealB k

-- @@ L44-45 verbatim
/-- Quadric variables `x,y,z,u`, in this order. -/
noncomputable def bX (i : Fin 4) : B k := Ideal.Quotient.mk (idealB k) (X i)


-- @@ L47-47 verbatim
noncomputable def determinantRelation : P k 5 := X 0 * X 3 - X 2 * X 1 - 1

-- @@ L48-48 verbatim
noncomputable def idealC : Ideal (P k 5) := Ideal.span {determinantRelation k}

-- @@ L49-49 verbatim
abbrev C := P k 5 ⧸ idealC k

-- @@ L50-51 verbatim
/-- Determinant-ring variables `a,d,b,c,u`, in this order. -/
noncomputable def cX (i : Fin 5) : C k := Ideal.Quotient.mk (idealC k) (X i)


-- @@ L53-53 verbatim
noncomputable def sB : B k := bX k 1 - bX k 0 * (bX k 0 + bX k 3 ^ 2)

-- @@ L54-54 verbatim
noncomputable def f0 : B k := bX k 0 - sB k ^ 2 + bX k 3 ^ 2

-- @@ L55-55 verbatim
noncomputable def g0 : B k := bX k 2 - sB k * bX k 0

-- @@ L56-56 verbatim
noncomputable def I : Ideal (B k) := Ideal.span {f0 k, g0 k}

-- @@ L57-57 verbatim
noncomputable def v : C k := cX k 0 ^ 3 * cX k 2 + cX k 0 ^ 2 * cX k 4 ^ 2 - cX k 1 ^ 2


-- @@ L59-60 verbatim
/-- The exact negative integer weights on the presentation variables. -/
def presentationWeight : Fin 5 → ℤ := ![-1, 0, 0, 1, 1]

-- @@ L61-62 verbatim
/-- Fiber weights on `a,d,b,c,u`; these encode fiber scaling. -/
def fiberWeight : Fin 5 → ℤ := ![1, 1, -1, -1, 0]

-- @@ L63-64 verbatim
/-- The second, auxiliary grading used only in the rigidity argument. -/
def auxiliaryWeight : Fin 5 → ℤ := ![0, 1, -1, 0, 1]


-- @@ L66-68 verbatim
@[simp] theorem mk_H : Ideal.Quotient.mk (idealA k) (H k) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (Set.mem_singleton (H k))


-- @@ L70-72 verbatim
@[simp] theorem mk_Hstar : Ideal.Quotient.mk (idealG k) (Hstar k) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (Set.mem_singleton (Hstar k))


-- @@ L74-78 verbatim
theorem b_relation : bX k 0 * bX k 1 - bX k 2 * (bX k 2 + 1) = 0 := by
  have h : Ideal.Quotient.mk (idealB k) (quadricRelation k) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (Set.mem_singleton (quadricRelation k))
  simpa [quadricRelation, bX] using h


-- @@ L80-84 verbatim
theorem c_relation : cX k 0 * cX k 3 - cX k 2 * cX k 1 - 1 = 0 := by
  have h : Ideal.Quotient.mk (idealC k) (determinantRelation k) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (Set.mem_singleton (determinantRelation k))
  simpa [determinantRelation, cX] using h


-- @@ L86-86 verbatim
end StableCoordinate.Obstruction


-- @@ L88-88 verbatim
end OAI
