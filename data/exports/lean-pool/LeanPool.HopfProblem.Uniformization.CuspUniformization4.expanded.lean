/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Threefold.SpecialPeriods9
public import LeanPool.HopfProblem.Toric.DiagonalQuotient2
import all LeanPool.HopfProblem.Foundations.Core1
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.Toric.ToricSpace1
import all LeanPool.HopfProblem.Uniformization.CuspUniformization1
import all LeanPool.HopfProblem.Threefold.SpecialPeriods1
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods2
import all LeanPool.HopfProblem.Threefold.SpecialPeriods9
import all LeanPool.HopfProblem.Toric.DiagonalQuotient2


-- @@ L21-25 verbatim
/-!
# Hopf problem: uniformization · cusp uniformization 4

Supporting definitions and proofs for this stage of the six-sphere construction.
-/



-- @@ L28-28 verbatim
open Set Function Filter Manifold Topology


-- @@ L30-33 verbatim
open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane


-- @@ L35-35 verbatim
universe u v


-- @@ L37-37 verbatim
noncomputable section


-- @@ L39-39 verbatim
namespace Mathoverflow1973


-- @@ L41-41 verbatim
local infixr:80 " ≫ₚ " => Path.trans


-- @@ L43-43 verbatim
local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f


-- @@ L45-57 verbatim
@[simp]
private theorem CuspUniformization.exponentialPoint_zero (t : ℂ) :
    exponentialPoint t 0 =
      ToricSpace.inclusion ToricSpace.referenceTriangle (CuspQuotient.sectionCoordinates t) := by
  change
    ToricSpace.inclusion ToricSpace.referenceTriangle
        (ToricCharts.monomial ToricSpace.referenceTriangle.dual (exponentialCoordinates t 0)) =
      _
  apply congrArg (ToricSpace.inclusion ToricSpace.referenceTriangle)
  ext i
  fin_cases i <;>
    simp [ToricCharts.monomial, ToricSpace.referenceTriangle, ToricFan.Triangle.dual,
      exponentialCoordinates, CuspQuotient.sectionCoordinates, Fin.prod_univ_succ]


-- @@ L59-67 verbatim
private theorem
    CuspUniformization.totalExponentialLift_eq_sectionLift_of_zero (r : ℝ) (x : LogCover r)
    (hx : x.1.2 = 0) (t : CuspQuotient.disc r) (ht : (t : ℂ) = exponential x.1.1) :
    totalExponentialLift r x = CuspQuotient.sectionLift r t := by
  apply Subtype.ext
  change
    exponentialPoint (exponential x.1.1) x.1.2 =
      ToricSpace.inclusion ToricSpace.referenceTriangle (CuspQuotient.sectionCoordinates t)
  rw [hx, exponentialPoint_zero, ← ht]


-- @@ L69-74 verbatim
private theorem CuspUniformization.totalCuspCover_eq_zeroSection_of_zero
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (x : LogCover r) (hx : x.1.2 = 0)
    (t : CuspQuotient.disc r) (ht : (t : ℂ) = exponential x.1.1) :
    totalCuspCover C r x = CuspQuotient.zeroSection C r t :=
  congrArg (CuspQuotient.quotientMap C r)
    (totalExponentialLift_eq_sectionLift_of_zero r x hx t ht)


-- @@ L76-81 verbatim
private theorem CuspUniformization.puncturedCuspCover_eq_zeroSection_of_zero
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (x : LogCover r) (hx : x.1.2 = 0)
    (t : CuspQuotient.disc r) (ht : (t : ℂ) = exponential x.1.1) :
    (puncturedCuspCover C r x : CuspQuotient.QuotientSpace C r) =
      CuspQuotient.zeroSection C r t :=
  totalCuspCover_eq_zeroSection_of_zero C r x hx t ht


-- @@ L83-89 verbatim
private theorem
    CuspUniformization.puncturedCuspCover_zero (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (s : SpecialPeriods.CuspFamily.LogBase r) (t : CuspQuotient.disc r)
    (ht : (t : ℂ) = exponential s) :
    (puncturedCuspCover C r ⟨((s : ℂ), 0), s.property⟩ : CuspQuotient.QuotientSpace C r) =
      CuspQuotient.zeroSection C r t :=
  puncturedCuspCover_eq_zeroSection_of_zero C r _ rfl t ht


-- @@ L91-116 verbatim
/-- The triangle-group action by multiplicative automorphisms of the lattice. -/
@[expose]
public
def SpecialPeriods.triangleLatticeMulAutHom : TriangleGroup →* MulAut (Multiplicative Lattice)
    where
  toFun
    g :=
    (Matrix.SpecialLinearGroup.toLin' (triangleDualRepresentation g)).toAddEquiv.toMultiplicative
  map_one' := by
    apply MulEquiv.ext
    intro n
    apply Multiplicative.toAdd.injective
    change Matrix.SpecialLinearGroup.toLin' (triangleDualRepresentation 1) n.toAdd = n.toAdd
    rw [map_one, map_one]
    rfl
  map_mul' g
    h := by
    apply MulEquiv.ext
    intro n
    apply Multiplicative.toAdd.injective
    change
      Matrix.SpecialLinearGroup.toLin' (triangleDualRepresentation (g * h)) n.toAdd =
        Matrix.SpecialLinearGroup.toLin' (triangleDualRepresentation g)
          (Matrix.SpecialLinearGroup.toLin' (triangleDualRepresentation h) n.toAdd)
    rw [map_mul, map_mul]
    rfl


-- @@ L118-124 verbatim
@[simp]
public
theorem SpecialPeriods.triangleLatticeMulAutHom_toAdd (g : TriangleGroup)
    (n : Multiplicative Lattice) :
    (triangleLatticeMulAutHom g n).toAdd =
      (triangleDualRepresentation g : LatticeMatrix) *ᵥ n.toAdd :=
  rfl


-- @@ L126-126 verbatim
end Mathoverflow1973


-- @@ L128-128 verbatim
end
