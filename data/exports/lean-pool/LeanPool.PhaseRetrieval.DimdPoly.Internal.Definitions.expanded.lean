/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Factorial.DoubleFactorial


-- @@ L15-15 verbatim
/-! # Definitions -/


-- @@ L17-17 verbatim
@[expose] public section



-- @@ L20-20 verbatim
open scoped BigOperators


-- @@ L22-22 verbatim
noncomputable section


-- @@ L24-24 verbatim
namespace DimdPolyLEAN


-- @@ L26-27 verbatim
/-- `Cd d`: the complex coordinate space `Fin d → ℂ` (`d`-dimensional). -/
abbrev Cd (d : Nat) := Fin d -> ℂ

-- @@ L28-29 verbatim
/-- `MultiIndex d`: a `d`-tuple of natural-number indices, `Fin d → ℕ`. -/
abbrev MultiIndex (d : Nat) := Fin d -> Nat

-- @@ L30-31 verbatim
/-- `Idx d`: the index set for Hermite-Fock coefficient arrays, equal to `MultiIndex d`. -/
abbrev Idx (d : Nat) := MultiIndex d


-- @@ L33-34 verbatim
/-- `CircleFreq`: an integer Fourier frequency on the circle. -/
abbrev CircleFreq := Int

-- @@ L35-37 verbatim
/-- `CircleTrigPoly`: a finite complex trigonometric polynomial on the circle, as a
finitely supported map from frequencies to coefficients. -/
abbrev CircleTrigPoly := Finsupp CircleFreq ℂ


-- @@ L39-42 verbatim
/-- `Pkappa d kappa`: the space of finite Hermite-Fock coefficient arrays at level
`kappa`, namely finitely supported maps `Idx d → ℂ`. -/
abbrev Pkappa (d : Nat) (kappa : MultiIndex d) : Type :=
  (fun _ : MultiIndex d => Finsupp (Idx d) ℂ) kappa


-- @@ L44-44 verbatim
namespace Pkappa


-- @@ L46-48 verbatim
/-- Two `Pkappa d kappa` coefficient arrays agreeing pointwise are equal. -/
@[ext] theorem ext {d : Nat} {kappa : MultiIndex d} {F G : Pkappa d kappa}
    (h : ∀ a, F a = G a) : F = G := Finsupp.ext h


-- @@ L50-50 verbatim
end Pkappa


-- @@ L52-58 verbatim
/-- `Skappa d kappa`: a square-summable Hermite-Fock coefficient array at level
`kappa` (the `ℓ²` completion datum behind the Gaussian `L²` closure). -/
structure Skappa (d : Nat) (kappa : MultiIndex d) where
  /-- The coefficient of each multi-index. -/
  coeff : Idx d -> ℂ
  /-- The coefficients are square-summable. -/
  summable_norm_sq : Summable (fun alpha : Idx d => ‖coeff alpha‖ ^ 2)


-- @@ L60-60 verbatim
instance : Fact (0 < (2 * Real.pi : ℝ)) := ⟨by positivity⟩


-- @@ L62-64 verbatim
/-- `gaussianDensity`: gaussian Density. -/
def gaussianDensity (d : Nat) (z : Cd d) : ℝ :=
  (1 / Real.pi ^ d) * Real.exp (-Finset.sum Finset.univ (fun q : Fin d => ‖z q‖ ^ 2))


-- @@ L66-68 verbatim
/-- `gammaD`: gamma d. -/
def gammaD (d : Nat) : MeasureTheory.Measure (Cd d) :=
  MeasureTheory.volume.withDensity fun z => ENNReal.ofReal (gaussianDensity d z)


-- @@ L70-71 verbatim
/-- `L2Tensor`: L2 Tensor. -/
abbrev L2Tensor (d : Nat) := MeasureTheory.Lp ℂ 2 (gammaD d)


-- @@ L73-78 verbatim
/-- `complexHermite`: complex Hermite. -/
def complexHermite (m n : Nat) (z : ℂ) : ℂ :=
  Finset.sum (Finset.range (min m n + 1)) fun j =>
    ((-1 : ℂ) ^ j) * (Nat.factorial j : ℂ) *
      (Nat.choose m j : ℂ) * (Nat.choose n j : ℂ) *
      z ^ (m - j) * (star z) ^ (n - j)


-- @@ L80-83 verbatim
/-- `phi1D`: phi1 D. -/
def phi1D (k n : Nat) (z : ℂ) : ℂ :=
  (((Real.sqrt ((Nat.factorial n : ℝ) * (Nat.factorial k : ℝ))) : ℂ)⁻¹) *
    complexHermite n k z


-- @@ L85-87 verbatim
/-- `Phi`: Phi. -/
def Phi {d : Nat} (kappa : MultiIndex d) (alpha : Idx d) (z : Cd d) : ℂ :=
  Finset.prod Finset.univ fun q : Fin d => phi1D (kappa q) (alpha q) (z q)


-- @@ L89-91 verbatim
/-- `box`: box. -/
def box {d : Nat} (J : MultiIndex d) : Finset (Idx d) :=
  Fintype.piFinset fun q : Fin d => Finset.range (J q + 1)


-- @@ L93-94 verbatim
noncomputable instance instNormCircleTrigPoly : Norm CircleTrigPoly :=
  ⟨fun p => Real.sqrt (Finset.sum p.support fun n => ‖p n‖ ^ 2)⟩


-- @@ L96-97 verbatim
noncomputable instance instNormPkappa {d : Nat} {kappa : MultiIndex d} : Norm (Pkappa d kappa) :=
  ⟨fun F => Real.sqrt (Finset.sum F.support fun alpha => ‖F alpha‖ ^ 2)⟩


-- @@ L99-101 verbatim
instance {d : Nat} {kappa : MultiIndex d} : Zero (Skappa d kappa) :=
  ⟨{ coeff := fun _ => 0
     summable_norm_sq := by simp }⟩


-- @@ L103-113 verbatim
instance {d : Nat} {kappa : MultiIndex d} : SMul ℂ (Skappa d kappa) where
  smul c u :=
    { coeff := fun alpha => c * u.coeff alpha
      summable_norm_sq := by
        have hEq :
            (fun alpha : Idx d => ‖c * u.coeff alpha‖ ^ 2) =
              fun alpha => (‖c‖ ^ 2) * (‖u.coeff alpha‖ ^ 2) := by
          funext alpha
          rw [norm_mul, mul_pow]
        rw [hEq]
        exact u.summable_norm_sq.mul_left (‖c‖ ^ 2) }


-- @@ L115-116 verbatim
/-- `coeffPkappa`: coeff Pkappa. -/
def coeffPkappa {d : Nat} {kappa : MultiIndex d} (F : Pkappa d kappa) (alpha : Idx d) : ℂ := F alpha


-- @@ L118-120 verbatim
/-- `coeffSkappa`: coeff Skappa. -/
def coeffSkappa {d : Nat} {kappa : MultiIndex d} (F : Skappa d kappa) (alpha : Idx d) : ℂ :=
  F.coeff alpha


-- @@ L122-124 verbatim
/-- `evalPkappa`: eval Pkappa. -/
def evalPkappa {d : Nat} (kappa : MultiIndex d) (F : Pkappa d kappa) : Cd d -> ℂ :=
  fun z => F.sum fun alpha c => c * Phi kappa alpha z


-- @@ L126-128 verbatim
/-- `toFun`: to Fun. -/
def toFun {d : Nat} (kappa : MultiIndex d) (F : Skappa d kappa) : Cd d -> ℂ :=
  fun z => ∑' alpha : Idx d, coeffSkappa F alpha * Phi kappa alpha z


-- @@ L130-133 verbatim
/-- `toL2`: to L2. -/
noncomputable def toL2 {d : Nat} (kappa : MultiIndex d) (F : Skappa d kappa) : L2Tensor d := by
  classical
  exact if h : MeasureTheory.MemLp (toFun kappa F) 2 (gammaD d) then h.toLp (toFun kappa F) else 0


-- @@ L135-142 verbatim
/-- `ofPkappa`: of Pkappa. -/
def ofPkappa {d : Nat} (kappa : MultiIndex d) (F : Pkappa d kappa) : Skappa d kappa :=
  { coeff := fun alpha => F alpha
    summable_norm_sq := by
      classical
      refine summable_of_hasFiniteSupport ?_
      refine Set.Finite.subset F.support.finite_toSet ?_
      simp_all }


-- @@ L144-147 verbatim
/-- `projFinset`: proj Finset. -/
def projFinset {d : Nat} {kappa : MultiIndex d} (E : Finset (Idx d)) (F : Pkappa d kappa) :
    Pkappa d kappa :=
  F.filter fun alpha => alpha ∈ E


-- @@ L149-152 verbatim
/-- `truncateFinset`: truncate Finset. -/
def truncateFinset {d : Nat} {kappa : MultiIndex d} (E : Finset (Idx d)) (F : Skappa d kappa) :
    Pkappa d kappa :=
  Finset.sum E fun alpha => Finsupp.single alpha (coeffSkappa F alpha)


-- @@ L154-156 verbatim
/-- `rotateCoord`: rotate Coord. -/
def rotateCoord {d : Nat} (q : Fin d) (t : ℝ) (z : Cd d) : Cd d :=
  Function.update z q (Complex.exp (t * Complex.I) * z q)


-- @@ L158-160 verbatim
/-- `pkappaInner`: pkappa Inner. -/
def pkappaInner {d : Nat} {kappa : MultiIndex d} (F G : Pkappa d kappa) : ℂ :=
  F.sum fun alpha c => c * star (G alpha)


-- @@ L162-164 verbatim
/-- `basePointNormalized`: base Point Normalized. -/
def basePointNormalized {d : Nat} {kappa : MultiIndex d} (F : Pkappa d kappa) : Prop :=
  F ≠ 0 ∧ ‖F‖ = 1


-- @@ L166-168 verbatim
/-- `orthogonalToPk`: orthogonal To Pk. -/
def orthogonalToPk {d : Nat} {kappa : MultiIndex d} (F G : Pkappa d kappa) : Prop :=
  pkappaInner G F = 0


-- @@ L170-179 verbatim
/--
The positive phase gauge for a fixed base point `F`.

The coefficient of `Q` in the `F` direction is required to be a nonnegative
real number.  This is the global gauge needed for a no-`δ`, `lambda = 1`
stability statement: the weaker local real gauge would still allow `Q = -F`.
-/
def positivePhaseGauge {d : Nat} {kappa : MultiIndex d}
    (F Q : Pkappa d kappa) : Prop :=
  (pkappaInner Q F).im = 0 ∧ 0 ≤ (pkappaInner Q F).re


-- @@ L181-183 verbatim
/-- `defect`: defect. -/
def defect {d : Nat} {kappa : MultiIndex d} (F G : Pkappa d kappa) : ℝ :=
  Real.sqrt <| ∫ z, (‖evalPkappa kappa (F + G) z‖ - ‖evalPkappa kappa F z‖) ^ 2 ∂ gammaD d


-- @@ L185-187 verbatim
/-- `productAnnulus`: product Annulus. -/
def productAnnulus {d : Nat} (j : Idx d) : Set (Cd d) :=
  { z | ∀ q : Fin d, (j q : ℝ) ≤ ‖z q‖ ∧ ‖z q‖ < (j q : ℝ) + 1 }


-- @@ L189-191 verbatim
/-- `annulusMass`: annulus Mass. -/
def annulusMass {d : Nat} {kappa : MultiIndex d} (j : Idx d) (F : Skappa d kappa) : ℝ :=
  ∫ z, Set.indicator (productAnnulus j) (fun w => ‖toFun kappa F w‖ ^ 2) z ∂ gammaD d


-- @@ L193-195 verbatim
/-- `lowAnnuli`: low Annuli. -/
def lowAnnuli (d J : Nat) : Finset (Idx d) :=
  Fintype.piFinset fun _ : Fin d => Finset.range J


-- @@ L197-199 verbatim
/-- `lowAnnulusMass`: low Annulus Mass. -/
def lowAnnulusMass {d : Nat} {kappa : MultiIndex d} (J : Nat) (F : Skappa d kappa) : ℝ :=
  Finset.sum (lowAnnuli d J) fun j => annulusMass j F


-- @@ L201-203 verbatim
/-- `highAnnulusMass`: high Annulus Mass. -/
def highAnnulusMass {d : Nat} {kappa : MultiIndex d} (J : Nat) (F : Skappa d kappa) : ℝ :=
  (∫ z, ‖toFun kappa F z‖ ^ 2 ∂ gammaD d) - lowAnnulusMass J F


-- @@ L205-207 verbatim
/-- `coefficientRadius`: coefficient Radius. -/
def coefficientRadius {d : Nat} (alpha : Idx d) : Nat :=
  Finset.sup Finset.univ alpha


-- @@ L209-211 verbatim
/-- `highAnnulusEnergy`: high Annulus Energy. -/
def highAnnulusEnergy {d : Nat} {kappa : MultiIndex d} (J : Nat) (F : Pkappa d kappa) : ℝ :=
  highAnnulusMass J (ofPkappa kappa F)


-- @@ L213-215 verbatim
/-- `lowBlockLeakage`: low Block Leakage. -/
def lowBlockLeakage {d : Nat} {kappa : MultiIndex d} (J : Nat) (F : Pkappa d kappa) : ℝ :=
  lowAnnulusMass J (ofPkappa kappa F)


-- @@ L217-219 verbatim
/-- `supportRadius`: support Radius. -/
def supportRadius {d : Nat} {kappa : MultiIndex d} (F : Pkappa d kappa) : Nat :=
  Finset.sup F.support coefficientRadius


-- @@ L221-223 verbatim
/-- `Jann`: Jann. -/
def Jann {d : Nat} {kappa : MultiIndex d} (F : Pkappa d kappa) : Nat :=
  supportRadius F + 1


-- @@ L225-227 verbatim
/-- `Cann`: Cann. -/
def Cann {d : Nat} {kappa : MultiIndex d} (F : Pkappa d kappa) : ℝ :=
  ‖F‖ ^ 2 + (Jann F : ℝ) + 1


-- @@ L229-231 verbatim
/-- `Cleak`: Cleak. -/
def Cleak {d : Nat} {kappa : MultiIndex d} (F : Pkappa d kappa) : ℝ :=
  ‖F‖ + (F.support.card : ℝ) + 1


-- @@ L233-236 verbatim
/-- `deltaRig`: delta Rig. -/
def deltaRig {d : Nat} {kappa : MultiIndex d}
    (F : Pkappa d kappa) (E : Finset (Idx d)) (rho : ℝ) : ℝ :=
  rho / ((Jann F + E.card + 1 : Nat) : ℝ)


-- @@ L238-240 verbatim
/-- `Cperp`: Cperp. -/
def Cperp {d : Nat} {kappa : MultiIndex d} (F : Pkappa d kappa) : ℝ :=
  Cann F + Cleak F


-- @@ L242-244 verbatim
/-- `evalCircle`: eval Circle. -/
noncomputable def evalCircle (p : CircleTrigPoly) : AddCircle (2 * Real.pi) -> ℂ :=
  fun t => Finset.sum p.support fun n => p n * (AddCircle.toCircle (n • t) : ℂ)


-- @@ L246-248 verbatim
/-- `oneSidedLowFreq`: one Sided Low Freq. -/
def oneSidedLowFreq (p : CircleTrigPoly) (D : Nat) : Prop :=
  ∀ n ∈ p.support, 0 ≤ n ∧ n ≤ D


-- @@ L250-252 verbatim
/-- `highBandSupport`: high Band Support. -/
def highBandSupport (q : CircleTrigPoly) (N B : Nat) : Prop :=
  ∀ n ∈ q.support, (N : Int) ≤ n ∧ n < ((N + B) : Int)


-- @@ L254-255 verbatim
/-- `gapCircle`: gap Circle. -/
def gapCircle (D : Nat) : Nat := D + 1


-- @@ L257-259 verbatim
/-- `defectCircle`: defect Circle. -/
def defectCircle (p q : CircleTrigPoly) : ℝ :=
  Real.sqrt <| ∫ t, (‖evalCircle (p + q) t‖ - ‖evalCircle p t‖) ^ 2 ∂ AddCircle.haarAddCircle


-- @@ L261-263 verbatim
/-- `Ccircle`: Ccircle. -/
def Ccircle (p : CircleTrigPoly) (D N B : Nat) : ℝ :=
  ‖p‖ + ((D + N + B + 1 : Nat) : ℝ)


-- @@ L265-265 verbatim
end DimdPolyLEAN
