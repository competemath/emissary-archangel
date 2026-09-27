/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.MeanIncrementBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.HarmonicFields
public import LeanPool.NavierStokesAndEuler.NavierStokes.TemporalMeanUpdate
public import LeanPool.NavierStokesAndEuler.NavierStokes.MeanRankUpdate


-- @@ L14-21 verbatim
/-!
# Concrete fields and residuals for the correction construction

The state stores fields, rather than a residual-solving operator.  Covariances
are actual angular integrals, and the mean residuals are the differential
expressions in `MeanIncrementBounds`.  The three sorts of excluded additive
errors are retained as fields on the same space as the oscillations.
-/


-- @@ L23-23 verbatim
@[expose] public section



-- @@ L26-26 verbatim
noncomputable section


-- @@ L28-28 verbatim
namespace NavierStokes.CorrectionState


-- @@ L30-30 verbatim
open Set MeasureTheory MeanIncrementBounds WeightedClasses

-- @@ L31-31 verbatim
open scoped BigOperators ContDiff


-- @@ L33-33 verbatim
variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]


-- @@ L35-36 verbatim
/-- Scalar field: an abbreviation for `MeanIncrementBounds.Field D`. -/
abbrev ScalarField (D : Type) := MeanIncrementBounds.Field D


-- @@ L38-39 verbatim
/-- Oscillation: an abbreviation for `ℕ → (D × ℝ) → Fin 3 → ℝ`. -/
abbrev Oscillation (D : Type) := ℕ → (D × ℝ) → Fin 3 → ℝ

-- @@ L40-41 verbatim
/-- Oscillatory scalar: an abbreviation for `ℕ → (D × ℝ) → ℝ`. -/
abbrev OscillatoryScalar (D : Type) := ℕ → (D × ℝ) → ℝ

-- @@ L42-43 verbatim
/-- Mean vector: an abbreviation for `ℕ → D → Fin 3 → ℝ`. -/
abbrev MeanVector (D : Type) := ℕ → D → Fin 3 → ℝ


-- @@ L45-54 verbatim
/-- Fixed data used by every correction stage. -/
structure Context (D : Type) where
  /-- Operators of `Context`, of type `Operators D`. -/
  operators : Operators D
  /-- Base of `Context`, of type `Triple D`. -/
  base : Triple D
  /-- Virtual theta of `Context`, of type `ScalarField D`. -/
  virtualTheta : ScalarField D
  /-- Virtual axial of `Context`, of type `ScalarField D`. -/
  virtualAxial : ScalarField D


-- @@ L56-63 verbatim
/-- Additive errors are fields, not an exemption from the residual identity. -/
structure ExcludedErrors (D : Type) where
  /-- Base of `ExcludedErrors`, of type `Oscillation D`. -/
  base : Oscillation D
  /-- Gaussian of `ExcludedErrors`, of type `Oscillation D`. -/
  gaussian : Oscillation D
  /-- Alias error of `ExcludedErrors`, of type `Oscillation D`. -/
  aliasError : Oscillation D


-- @@ L65-65 verbatim
namespace ExcludedErrors


-- @@ L67-68 verbatim
/-- Zero, given by `⟨0, 0, 0⟩`. -/
noncomputable def zero : ExcludedErrors D := ⟨0, 0, 0⟩


-- @@ L70-72 verbatim
/-- Total, given by `e.base + e.gaussian + e.aliasError`. -/
noncomputable def total (e : ExcludedErrors D) : Oscillation D :=
  e.base + e.gaussian + e.aliasError


-- @@ L74-76 verbatim
/-- Add, given by `⟨e.base + f.base, e.gaussian + f.gaussian, e.aliasError + f.aliasError⟩`. -/
noncomputable def add (e f : ExcludedErrors D) : ExcludedErrors D :=
  ⟨e.base + f.base, e.gaussian + f.gaussian, e.aliasError + f.aliasError⟩


-- @@ L78-80 verbatim
omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
@[simp] theorem total_zero : (zero : ExcludedErrors D).total = 0 := by
  simp [total, zero]


-- @@ L82-85 verbatim
omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem total_add (e f : ExcludedErrors D) : (e.add f).total = e.total + f.total := by
  simp only [total, add]
  abel


-- @@ L87-87 verbatim
end ExcludedErrors


-- @@ L89-100 verbatim
/-- An actual velocity/pressure state on a lifted chart and angular circle. -/
structure State (D : Type) where
  /-- Mean field of `State`, of type `Triple D`. -/
  mean : Triple D
  /-- Pressure field of `State`, of type `ScalarField D`. -/
  pressure : ScalarField D
  /-- Oscillation of `State`, of type `Oscillation D`. -/
  oscillation : Oscillation D
  /-- Oscillatory pressure of `State`, of type `OscillatoryScalar D`. -/
  oscillatoryPressure : OscillatoryScalar D
  /-- Errors of `State`, of type `ExcludedErrors D`. -/
  errors : ExcludedErrors D


-- @@ L102-104 verbatim
/-- The angular normalization agrees with the physical mean over one period. -/
noncomputable def angularAverage (f : OscillatoryScalar D) : ScalarField D :=
  fun n x => (∫ θ in (0 : ℝ)..2 * Real.pi, f n (x, θ)) / (2 * Real.pi)


-- @@ L106-108 verbatim
/-- Bilinear covariance, given by `angularAverage (fun n p => u n p i * v n p j)`. -/
noncomputable def bilinearCovariance (u v : Oscillation D) (i j : Fin 3) : ScalarField D :=
  angularAverage (fun n p => u n p i * v n p j)


-- @@ L110-115 verbatim
omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem angularAverage_axisymmetric (f : ScalarField D) :
    angularAverage (fun n p => f n p.1) = f := by
  funext n x
  simp only [angularAverage, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  field_simp [Real.pi_ne_zero]


-- @@ L117-120 verbatim
omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
@[simp] theorem angularAverage_zero : angularAverage (0 : OscillatoryScalar D) = 0 := by
  funext n x
  simp [angularAverage]


-- @@ L122-125 verbatim
omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem bilinearCovariance_comm (u v : Oscillation D) (i j : Fin 3) :
    bilinearCovariance u v i j = bilinearCovariance v u j i := by
  simp only [bilinearCovariance, mul_comm]


-- @@ L127-127 verbatim
namespace State


-- @@ L129-131 verbatim
/-- Covariance, given by `bilinearCovariance s.oscillation s.oscillation i j`. -/
noncomputable def covariance (s : State D) (i j : Fin 3) : ScalarField D :=
  bilinearCovariance s.oscillation s.oscillation i j


-- @@ L133-137 verbatim
/-- Total velocity as an element of `Oscillation D`. -/
noncomputable def totalVelocity (s : State D) (c : Context D) : Oscillation D :=
  fun n p => ![c.base.radial n p.1 + s.mean.radial n p.1 + s.oscillation n p 0,
    c.base.angular n p.1 + s.mean.angular n p.1 + s.oscillation n p 1,
    c.base.axial n p.1 + s.mean.axial n p.1 + s.oscillation n p 2]


-- @@ L139-141 verbatim
/-- This is the pressure increment; the fixed base pressure is not part of a stage. -/
noncomputable def totalPressureIncrement (s : State D) : OscillatoryScalar D :=
  fun n p => s.pressure n p.1 + s.oscillatoryPressure n p


-- @@ L143-146 verbatim
/-- Theta residual, given by `MeanIncrementBounds.thetaResidual c.operators c.base s.mean
s.covariance c.virtualTheta`. -/
noncomputable def thetaResidual (s : State D) (c : Context D) : ScalarField D :=
  MeanIncrementBounds.thetaResidual c.operators c.base s.mean s.covariance c.virtualTheta


-- @@ L148-152 verbatim
/-- Axial residual, given by `MeanIncrementBounds.axialResidual c.operators c.base s.mean
s.covariance s.pressure c.virtualAxial`. -/
noncomputable def axialResidual (s : State D) (c : Context D) : ScalarField D :=
  MeanIncrementBounds.axialResidual c.operators c.base s.mean s.covariance
    s.pressure c.virtualAxial


-- @@ L154-156 verbatim
/-- Gr, given by `MeanIncrementBounds.gr c.operators c.base s.mean s.covariance`. -/
noncomputable def gr (s : State D) (c : Context D) : ScalarField D :=
  MeanIncrementBounds.gr c.operators c.base s.mean s.covariance


-- @@ L158-160 verbatim
/-- Radial residual, given by `c.operators.dr s.pressure - s.gr c`. -/
noncomputable def radialResidual (s : State D) (c : Context D) : ScalarField D :=
  c.operators.dr s.pressure - s.gr c


-- @@ L162-165 verbatim
/-- Reduced mean residual, defined pointwise by `![s.radialResidual c n x, s.thetaResidual c n
x, s.axialResidual c n x]`. -/
noncomputable def reducedMeanResidual (s : State D) (c : Context D) : MeanVector D :=
  fun n x => ![s.radialResidual c n x, s.thetaResidual c n x, s.axialResidual c n x]


-- @@ L167-169 verbatim
/-- Mean base error, defined pointwise by `angularAverage (fun k p => s.errors.base k p i) n x`. -/
noncomputable def meanBaseError (s : State D) : MeanVector D :=
  fun n x i => angularAverage (fun k p => s.errors.base k p i) n x


-- @@ L171-173 verbatim
/-- Equation (32) omits the fixed base-flat error from (24); it is restored here. -/
noncomputable def meanResidual (s : State D) (c : Context D) : MeanVector D :=
  s.reducedMeanResidual c + s.meanBaseError


-- @@ L175-177 verbatim
/-- Mean excluded, defined pointwise by `angularAverage (fun k p => s.errors.total k p i) n x`. -/
noncomputable def meanExcluded (s : State D) : MeanVector D :=
  fun n x i => angularAverage (fun k p => s.errors.total k p i) n x


-- @@ L179-181 verbatim
/-- Only the actual mean of the explicitly stored errors is removed here. -/
noncomputable def meanGoodResidual (s : State D) (c : Context D) : MeanVector D :=
  s.meanResidual c - s.meanExcluded


-- @@ L183-185 verbatim
theorem meanResidual_eq_good_add_excluded (s : State D) (c : Context D) :
    s.meanResidual c = s.meanGoodResidual c + s.meanExcluded := by
  simp [meanGoodResidual]


-- @@ L187-190 verbatim
omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem covariance_symm (s : State D) (i j : Fin 3) :
    s.covariance i j = s.covariance j i :=
  bilinearCovariance_comm _ _ _ _


-- @@ L192-199 verbatim
/-- Addition of actual fields.  No estimate or cancellation is part of this definition. -/
noncomputable def addIncrement (s : State D) (m : Triple D) (p : ScalarField D)
    (u : Oscillation D) (q : OscillatoryScalar D) (e : ExcludedErrors D) : State D where
  mean := updated s.mean m
  pressure := s.pressure + p
  oscillation := s.oscillation + u
  oscillatoryPressure := s.oscillatoryPressure + q
  errors := s.errors.add e


-- @@ L201-208 verbatim
omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem totalVelocity_addIncrement (s : State D) (c : Context D) (m : Triple D)
    (p : ScalarField D) (u : Oscillation D) (q : OscillatoryScalar D) (e : ExcludedErrors D) :
    (s.addIncrement m p u q e).totalVelocity c =
      fun n x => s.totalVelocity c n x +
        ![m.radial n x.1, m.angular n x.1, m.axial n x.1] + u n x := by
  funext n x i
  fin_cases i <;> simp [totalVelocity, addIncrement, updated] <;> ring


-- @@ L210-210 verbatim
end State


-- @@ L212-223 verbatim
/-- A single grouped label.  The finite group algebra records actual harmonics. -/
structure HarmonicBlock (D : Type) where
  /-- Velocity field of `HarmonicBlock`, of type `ℕ → Fin 3 → HarmonicFields.Coefficients D`. -/
  velocity : ℕ → Fin 3 → HarmonicFields.Coefficients D
  /-- Pressure field of `HarmonicBlock`, of type `ℕ → HarmonicFields.Coefficients D`. -/
  pressure : ℕ → HarmonicFields.Coefficients D
  /-- Frequency of `HarmonicBlock`, of type `ℕ → ℝ`. -/
  frequency : ℕ → ℝ
  /-- Phase of `HarmonicBlock`, of type `ℕ → D → ℝ`. -/
  phase : ℕ → D → ℝ
  /-- Angular frequency of `HarmonicBlock`, of type `ℕ → ℤ`. -/
  angularFrequency : ℕ → ℤ


-- @@ L225-225 verbatim
namespace HarmonicBlock


-- @@ L227-231 verbatim
/-- Oscillation, defined pointwise by `(HarmonicFields.field (b.velocity n i) (b.frequency n)
(b.phase n) (b.angularFrequency n) p).re`. -/
noncomputable def oscillation (b : HarmonicBlock D) : Oscillation D :=
  fun n p i => (HarmonicFields.field (b.velocity n i) (b.frequency n)
    (b.phase n) (b.angularFrequency n) p).re


-- @@ L233-237 verbatim
/-- Oscillatory pressure, defined pointwise by `(HarmonicFields.field (b.pressure n)
(b.frequency n) (b.phase n) (b.angularFrequency n) p).re`. -/
noncomputable def oscillatoryPressure (b : HarmonicBlock D) : OscillatoryScalar D :=
  fun n p => (HarmonicFields.field (b.pressure n) (b.frequency n)
    (b.phase n) (b.angularFrequency n) p).re


-- @@ L239-243 verbatim
/-- Band limited, given by `(∀ n i, HarmonicFields.BandLimited (b.velocity n i) N) ∧ ∀ n,
HarmonicFields.BandLimited (b.pressure n) N`. -/
def BandLimited (b : HarmonicBlock D) (N : ℕ) : Prop :=
  (∀ n i, HarmonicFields.BandLimited (b.velocity n i) N) ∧
    ∀ n, HarmonicFields.BandLimited (b.pressure n) N


-- @@ L245-249 verbatim
/-- Bounds are on stripped, grouped, nonzero harmonic coefficients. -/
def WaveBounds (s : StripData D) (P : ℕ → D → ℝ) (α : ℝ)
    (b : HarmonicBlock D) : Prop :=
  ∀ (i : Fin 3) (j : ℤ), j ≠ 0 →
    WaveClass s P α (fun n x => b.velocity n i j x)


-- @@ L251-254 verbatim
/-- Pressure bounds, given by `∀ j : ℤ, j ≠ 0 → WaveClass s P α (fun n x => b.pressure n j x)`. -/
def PressureBounds (s : StripData D) (P : ℕ → D → ℝ) (α : ℝ)
    (b : HarmonicBlock D) : Prop :=
  ∀ j : ℤ, j ≠ 0 → WaveClass s P α (fun n x => b.pressure n j x)


-- @@ L256-256 verbatim
end HarmonicBlock


-- @@ L258-263 verbatim
/-- A representation on a finite set of labels active in a fixed chart.
Global local-finiteness is a separate property of the physical label assembly. -/
def Represents {ι : Type} (labels : Finset ι) (blocks : ι → HarmonicBlock D)
    (s : State D) : Prop :=
  s.oscillation = ∑ l ∈ labels, (blocks l).oscillation ∧
    s.oscillatoryPressure = ∑ l ∈ labels, (blocks l).oscillatoryPressure


-- @@ L265-268 verbatim
/-- The mean portion of the cumulative bounds after initialization. -/
structure CumulativeBounds (s : StripData D) (u : State D) : Prop where
  velocity : MeanIncrementBounds.CumulativeBounds s u.mean
  pressure : MeanClass s (9 / 10) u.pressure


-- @@ L270-274 verbatim
/-- The mean residual portion of (36), computed from the state fields. -/
structure MeanResidualBounds (s : StripData D) (σ : ℝ) (c : Context D)
    (u : State D) : Prop where
  angular : MeanClass s (1 + σ) (fun n x => u.meanGoodResidual c n x 1)
  axial : MeanClass s (1 + σ) (fun n x => u.meanGoodResidual c n x 2)


-- @@ L276-276 verbatim
section Moments


-- @@ L278-278 verbatim
variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]


-- @@ L280-282 verbatim
/-- Actual radial moment of the full auxiliary torus mean. -/
noncomputable def radialMoment (k : ℕ) (f : ScalarField (PressureStream.Lift S)) : ScalarField S :=
  fun n p => PressureStream.pressureMass (fun x => x.1 ^ k * f n x) p


-- @@ L284-286 verbatim
/-- Pressure defect, given by `radialMoment 0 (u.gr c)`. -/
noncomputable def pressureDefect (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) : ScalarField S := radialMoment 0 (u.gr c)


-- @@ L288-291 verbatim
/-- Theta defect, given by `radialMoment 2 (thetaAxial c.base u.mean + u.covariance 2 1)`. -/
noncomputable def thetaDefect (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) : ScalarField S :=
  radialMoment 2 (thetaAxial c.base u.mean + u.covariance 2 1)


-- @@ L293-298 verbatim
/-- Axial defect, given by `radialMoment 1 (axialAxial c.base u.mean + u.covariance 2 2) - (1 /
2 : ℝ) • radialMoment 2 (u.gr c)`. -/
noncomputable def axialDefect (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) : ScalarField S :=
  radialMoment 1 (axialAxial c.base u.mean + u.covariance 2 2) -
    (1 / 2 : ℝ) • radialMoment 2 (u.gr c)


-- @@ L300-303 verbatim
/-- The row order is exactly `(P, Jθ, Jz)`, as in `MeanRankUpdate`. -/
noncomputable def debt (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) : ℕ → S → Fin 3 → ℝ :=
  fun n x => ![pressureDefect c u n x, thetaDefect c u n x, axialDefect c u n x]


-- @@ L305-309 verbatim
/-- Defect bounds, given by `∀ i : Fin 3, UnweightedClass s (1 + σ) (fun n x => debt c u n x
i)`. -/
def DefectBounds (s : StripData S) (σ : ℝ) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) : Prop :=
  ∀ i : Fin 3, UnweightedClass s (1 + σ) (fun n x => debt c u n x i)


-- @@ L311-313 verbatim
/-- Zero masses, given by `radialMoment 2 u.mean.angular = 0 ∧ radialMoment 1 u.mean.axial = 0`. -/
def ZeroMasses (u : State (PressureStream.Lift S)) : Prop :=
  radialMoment 2 u.mean.angular = 0 ∧ radialMoment 1 u.mean.axial = 0


-- @@ L315-315 verbatim
end Moments


-- @@ L317-329 verbatim
/-- Geometry of the genuine compact shifted pressure/stream primitive. -/
structure ReconstructionData where
  /-- Exponent of `ReconstructionData`, of type `ℝ`. -/
  exponent : ℝ
  /-- Inner of `ReconstructionData`, of type `ℝ`. -/
  inner : ℝ
  /-- Outer of `ReconstructionData`, of type `ℝ`. -/
  outer : ℝ
  inner_lt_outer : inner < outer
  /-- Frequency of `ReconstructionData`, of type `ℕ → ℝ`. -/
  frequency : ℕ → ℝ
  /-- Radial direction of `ReconstructionData`, of type `PressureStream.Plane`. -/
  radialDirection : PressureStream.Plane


-- @@ L331-331 verbatim
section Fields


-- @@ L333-333 verbatim
variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]


-- @@ L335-336 verbatim
/-- Lift: an abbreviation for `PressureStream.Lift S`. -/
abbrev Lift (S : Type) := PressureStream.Lift S


-- @@ L338-342 verbatim
/-- Recompute (33) from the current actual radial source. -/
noncomputable def reconstructPressure (r : ReconstructionData) (c : Context (Lift S))
    (u : State (Lift S)) : State (Lift S) :=
  { u with pressure := (fun n => PressureStream.meanPressure r.exponent r.inner r.outer
      (r.frequency n) r.inner_lt_outer r.radialDirection (u.gr c n)) }


-- @@ L344-348 verbatim
/-- The pressure alias has the sign with which it occurs in the radial residual. -/
noncomputable def pressureAlias (r : ReconstructionData) (c : Context (Lift S))
    (u : State (Lift S)) : Oscillation (Lift S) :=
  fun n p => ![-PressureStream.pressureAlias r.exponent r.inner r.outer (r.frequency n)
    r.inner_lt_outer r.radialDirection (u.gr c n) p.1, 0, 0]


-- @@ L350-351 verbatim
@[simp] theorem reconstructPressure_gr (r : ReconstructionData) (c : Context (Lift S))
    (u : State (Lift S)) : (reconstructPressure r c u).gr c = u.gr c := rfl


-- @@ L353-355 verbatim
@[simp] theorem reconstructPressure_covariance (r : ReconstructionData)
    (c : Context (Lift S)) (u : State (Lift S)) :
    (reconstructPressure r c u).covariance = u.covariance := rfl


-- @@ L357-370 verbatim
/-- Explicit graph operators with the pressure primitive's radial direction. -/
noncomputable def graphOperators (r : ReconstructionData) (epsilon fast : ℕ → ℝ)
    (axial slowTime : S × PressureStream.Plane) (temporal : PressureStream.Plane) :
    MeanIncrementBounds.Operators (Lift S) where
  epsilon := epsilon
  radialFrequency := r.frequency
  fastCoefficient := fast
  radius := Prod.fst
  radialProfile := fun x => RadialPullback.radialJacobian r.exponent x.1
  eR := (1, (0, 0))
  eZ := (0, axial)
  eT := (0, slowTime)
  vR := (0, (0, r.radialDirection))
  vT := (0, (0, temporal))


-- @@ L372-386 verbatim
theorem graphOperators_dr (r : ReconstructionData) (epsilon fast : ℕ → ℝ)
    (axial slowTime : S × PressureStream.Plane) (temporal : PressureStream.Plane)
    (f : ScalarField (Lift S)) (n : ℕ) (x : Lift S) :
    (graphOperators r epsilon fast axial slowTime temporal).dr f n x =
      PressureStream.graphDr (PressureStream.physicalSpeed r.exponent (r.frequency n))
        (0, r.radialDirection) (f n) x := by
  have he : ((1 : ℝ), ((0 : S), (0 : PressureStream.Plane))) +
      (r.frequency n * RadialPullback.radialJacobian r.exponent x.1) •
        ((0 : ℝ), ((0 : S), r.radialDirection)) =
      PressureStream.radialVector (PressureStream.physicalSpeed r.exponent (r.frequency n))
        ((0 : S), r.radialDirection) x := by
    simp [PressureStream.radialVector, PressureStream.physicalSpeed, mul_comm]
  rw [PressureStream.graphDr, ← he, map_add, map_smul]
  simp [graphOperators, MeanIncrementBounds.Operators.dr, WeightedClasses.graphDerivative,
    smul_eq_mul, mul_assoc]


-- @@ L388-397 verbatim
theorem graphOperators_dz (r : ReconstructionData) (epsilon fast : ℕ → ℝ)
    (axial slowTime : S × PressureStream.Plane) (temporal : PressureStream.Plane)
    (f : ScalarField (Lift S)) (n : ℕ) (x : Lift S) :
    (graphOperators r epsilon fast axial slowTime temporal).dz f n x =
      PressureStream.graphDz (epsilon n • axial) (f n) x := by
  have he : ((0 : ℝ), epsilon n • axial) = epsilon n • ((0 : ℝ), axial) := by simp
  change epsilon n * fderiv ℝ (f n) x (0, axial) =
    fderiv ℝ (f n) x (0, epsilon n • axial)
  rw [he, map_smul]
  rfl


-- @@ L399-404 verbatim
theorem graphOperators_fastTime (r : ReconstructionData) (epsilon : ℕ → ℝ) (h : ℝ)
    (axial slowTime : S × PressureStream.Plane) (f : ScalarField (Lift S))
    (n : ℕ) (x : Lift S) :
    (graphOperators r epsilon (ChartScales.timeCoefficient h) axial slowTime
      (TorusInverse.vector .temporal)).fastTime f n x =
      TemporalMeanUpdate.fastDerivative h n (f n) x := rfl


-- @@ L406-423 verbatim
theorem reconstructed_radial_residual (r : ReconstructionData)
    (ha : 0 < r.inner) (hd : 0 < r.exponent) (c : Context (Lift S))
    (u : State (Lift S))
    (hoperator : ∀ f : ScalarField (Lift S), ∀ n x, c.operators.dr f n x =
      PressureStream.graphDr (PressureStream.physicalSpeed r.exponent (r.frequency n))
        (0, r.radialDirection) (f n) x)
    (hsmooth : ∀ n, ContDiff ℝ ∞ (u.gr c n))
    (hsupport : ∀ n, RadialAlias.RadiallySupported r.inner r.outer (u.gr c n))
    (n : ℕ) (x : Lift S) :
    (reconstructPressure r c u).radialResidual c n x =
      -PressureStream.rho r.inner r.outer r.inner_lt_outer x.1 * pressureDefect c u n x.2.1 +
        pressureAlias r c u n (x, 0) 0 := by
  rw [State.radialResidual, Pi.sub_apply, Pi.sub_apply, hoperator]
  change PressureStream.graphDr _ _
      (PressureStream.meanPressure _ _ _ _ _ _ (u.gr c n)) x - u.gr c n x = _
  rw [PressureStream.meanPressure_radial_residual_global ha r.inner_lt_outer hd
    r.radialDirection (hsmooth n) (hsupport n)]
  simp [pressureDefect, radialMoment, pressureAlias, sub_eq_add_neg]


-- @@ L425-425 verbatim
end Fields


-- @@ L427-427 verbatim
section Temporal


-- @@ L429-429 verbatim
variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]


-- @@ L431-439 verbatim
/-- The actual temporal increment, including the compactified axial stream. -/
noncomputable def temporalIncrement (r : ReconstructionData) (h : ℝ)
    (axial : S × PressureStream.Plane) (c : Context (Lift S)) (u : State (Lift S)) :
    MeanIncrementBounds.Triple (Lift S) where
  radial := fun n => TemporalMeanUpdate.radialUpdate r.exponent r.inner r.outer
    (r.frequency n) r.radialDirection (c.operators.epsilon n • axial) h n (u.axialResidual c n)
  angular := fun n => TemporalMeanUpdate.desiredIncrement h n (u.thetaResidual c n)
  axial := fun n => TemporalMeanUpdate.axialUpdate r.exponent r.inner r.outer
    (r.frequency n) r.radialDirection h n (u.axialResidual c n)


-- @@ L441-446 verbatim
/-- The exact remaining axial fast-time error, not its asymptotic estimate. -/
noncomputable def temporalAlias (r : ReconstructionData) (h : ℝ)
    (c : Context (Lift S)) (u : State (Lift S)) : Oscillation (Lift S) :=
  fun n p => ![0, 0, -TemporalMeanUpdate.fastDerivative h n
    (TemporalMeanUpdate.axialAlias r.exponent r.inner r.outer (r.frequency n)
      r.radialDirection h n (u.axialResidual c n)) p.1]


-- @@ L448-454 verbatim
/-- Temporal stage, given by `reconstructPressure r c (u.addIncrement (temporalIncrement r h
axial c u) 0 0 0 ⟨0, 0, temporalAlias r h c u⟩)`. -/
noncomputable def temporalStage (r : ReconstructionData) (h : ℝ)
    (axial : S × PressureStream.Plane) (c : Context (Lift S)) (u : State (Lift S)) :
    State (Lift S) :=
  reconstructPressure r c (u.addIncrement (temporalIncrement r h axial c u) 0 0 0
    ⟨0, 0, temporalAlias r h c u⟩)


-- @@ L456-472 verbatim
theorem temporal_fast_cancellation (r : ReconstructionData) (h : ℝ)
    (axial : S × PressureStream.Plane) (c : Context (Lift S)) (u : State (Lift S))
    (ha : 0 < r.inner) (hd : 0 < r.exponent)
    (hθ : ∀ n, ContDiff ℝ ∞ (u.thetaResidual c n))
    (hz : ∀ n, ContDiff ℝ ∞ (u.axialResidual c n))
    (hpθ : ∀ n, PressureStream.TorusPeriodicLift (u.thetaResidual c n))
    (hpz : ∀ n, PressureStream.TorusPeriodicLift (u.axialResidual c n))
    (hsz : ∀ n, RadialAlias.RadiallySupported r.inner r.outer (u.axialResidual c n))
    (n : ℕ) (x : Lift S) :
    TemporalMeanUpdate.fastDerivative h n ((temporalIncrement r h axial c u).angular n) x +
        TemporalMeanUpdate.centered (u.thetaResidual c n) x = 0 ∧
    TemporalMeanUpdate.fastDerivative h n ((temporalIncrement r h axial c u).axial n) x +
        TemporalMeanUpdate.centered (u.axialResidual c n) x = temporalAlias r h c u n (x, 0) 2 := by
  have hv := TemporalMeanUpdate.temporal_mean_update (M := r.frequency n) ha r.inner_lt_outer hd
      r.radialDirection
    (c.operators.epsilon n • axial) h n (hθ n) (hz n) (hpθ n) (hpz n) (hsz n) x
  exact ⟨hv.1, hv.2.1⟩


-- @@ L474-474 verbatim
end Temporal


-- @@ L476-490 verbatim
/-- The physical length, velocity, and background amplitude used by the
five-row inverse.  These may depend on the band and slow variables. -/
structure RankData (S : Type) where
  /-- Lambda of `RankData`, of type `ℝ`. -/
  lambda : ℝ
  /-- Inner of `RankData`, of type `ℝ`. -/
  inner : ℝ
  /-- Outer of `RankData`, of type `ℝ`. -/
  outer : ℝ
  /-- Length of `RankData`, of type `ℕ → S → ℝ`. -/
  length : ℕ → S → ℝ
  /-- Velocity field of `RankData`, of type `ℕ → S → ℝ`. -/
  velocity : ℕ → S → ℝ
  /-- Coefficient of `RankData`, of type `ℕ → S → ℝ`. -/
  coefficient : ℕ → S → ℝ


-- @@ L492-492 verbatim
section Rank


-- @@ L494-494 verbatim
variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]


-- @@ L496-501 verbatim
/-- Rank angular, given by `MeanRankUpdate.angularFamily r.lambda r.inner r.outer (r.length n)
(r.velocity n) (r.coefficient n) (debt c u n)`. -/
noncomputable def rankAngular (r : RankData S) (c : Context (Lift S))
    (u : State (Lift S)) (n : ℕ) : ℝ × S → ℝ :=
  MeanRankUpdate.angularFamily r.lambda r.inner r.outer (r.length n) (r.velocity n)
    (r.coefficient n) (debt c u n)


-- @@ L503-508 verbatim
/-- Rank desired axial, given by `MeanRankUpdate.desiredAxialFamily r.lambda r.inner r.outer
(r.length n) (r.velocity n) (r.coefficient n) (debt c u n)`. -/
noncomputable def rankDesiredAxial (r : RankData S) (c : Context (Lift S))
    (u : State (Lift S)) (n : ℕ) : ℝ × S → ℝ :=
  MeanRankUpdate.desiredAxialFamily r.lambda r.inner r.outer (r.length n) (r.velocity n)
    (r.coefficient n) (debt c u n)


-- @@ L510-514 verbatim
/-- Rank potential, constructed using `PressureStream.streamPotential`. -/
noncomputable def rankPotential (p : ReconstructionData) (r : RankData S)
    (c : Context (Lift S)) (u : State (Lift S)) (n : ℕ) : Lift S → ℝ :=
  PressureStream.streamPotential p.exponent p.inner p.outer (p.frequency n)
    ((0 : S), p.radialDirection) (MeanRankUpdate.slowLift (rankDesiredAxial r c u n))


-- @@ L516-525 verbatim
/-- Rank increment, bundling `radial`, `angular`, `axial`. -/
noncomputable def rankIncrement (p : ReconstructionData) (r : RankData S)
    (axial : S × PressureStream.Plane) (c : Context (Lift S)) (u : State (Lift S)) :
    MeanIncrementBounds.Triple (Lift S) where
  radial := fun n => PressureStream.streamBeta (c.operators.epsilon n • axial)
    (rankPotential p r c u n)
  angular := fun n => MeanRankUpdate.slowLift (rankAngular r c u n)
  axial := fun n => PressureStream.streamGamma
    (PressureStream.physicalSpeed p.exponent (p.frequency n)) ((0 : S), p.radialDirection)
    (rankPotential p r c u n)


-- @@ L527-532 verbatim
/-- Rank stage, given by `reconstructPressure p c (u.addIncrement (rankIncrement p r axial c u)
0 0 0 ExcludedErrors.zero)`. -/
noncomputable def rankStage (p : ReconstructionData) (r : RankData S)
    (axial : S × PressureStream.Plane) (c : Context (Lift S)) (u : State (Lift S)) :
    State (Lift S) :=
  reconstructPressure p c (u.addIncrement (rankIncrement p r axial c u) 0 0 0 ExcludedErrors.zero)


-- @@ L534-543 verbatim
theorem rank_model_rows (r : RankData S) (c : Context (Lift S)) (u : State (Lift S))
    (n : ℕ) (x : S) (hlam : 0 < r.lambda) (hC : r.coefficient n x ≠ 0)
    (ha : 0 < r.inner) (hab : r.inner < r.outer) (hell : 0 < r.length n x)
    (hU : r.velocity n x ≠ 0) :
    FiveRowRank.FiveRows
      (MeanRankUpdate.background r.lambda (r.coefficient n x) (r.length n x) (r.velocity n x))
      (fun _ => 0) (debt c u n x)
      (fun R => rankAngular r c u n (R, x))
      (fun R => rankDesiredAxial r c u n (R, x)) :=
  MeanRankUpdate.physical_five_rows hlam hC ha hab hell hU (debt c u n x)


-- @@ L545-561 verbatim
/-- The linear rows hold for the actual base whenever it agrees with the
prescribed background on the support of the constructed bumps. -/
theorem rank_rows_on_patch (r : RankData S) (c : Context (Lift S)) (u : State (Lift S))
    (n : ℕ) (x : S) (Y : PressureStream.Plane)
    (hlam : 0 < r.lambda) (hC : r.coefficient n x ≠ 0)
    (ha : 0 < r.inner) (hab : r.inner < r.outer) (hell : 0 < r.length n x)
    (hU : r.velocity n x ≠ 0)
    (hV : ∀ R ∈ Ioo (r.length n x * r.inner) (r.length n x * r.outer),
      c.base.angular n (R, (x, Y)) =
        MeanRankUpdate.background r.lambda (r.coefficient n x) (r.length n x) (r.velocity n x) R)
    (hG : ∀ R ∈ Ioo (r.length n x * r.inner) (r.length n x * r.outer),
      c.base.axial n (R, (x, Y)) = 0) :
    FiveRowRank.FiveRows (fun R => c.base.angular n (R, (x, Y)))
      (fun R => c.base.axial n (R, (x, Y))) (debt c u n x)
      (fun R => rankAngular r c u n (R, x))
      (fun R => rankDesiredAxial r c u n (R, x)) :=
  MeanRankUpdate.physical_rows_on_patch hlam hC ha hab hell hU (debt c u n x) _ _ hV hG


-- @@ L563-575 verbatim
theorem rank_axial_eq_desired (p : ReconstructionData) (r : RankData S)
    (axial : S × PressureStream.Plane) (c : Context (Lift S)) (u : State (Lift S))
    (ha : 0 < p.inner) (hd : 0 < p.exponent) (n : ℕ)
    (hlam : 0 < r.lambda) (hC : ∀ x, r.coefficient n x ≠ 0)
    (hra : 0 < r.inner) (hrab : r.inner < r.outer)
    (hell : ∀ x, 0 < r.length n x) (hU : ∀ x, r.velocity n x ≠ 0)
    (hf : ContDiff ℝ ∞ (rankDesiredAxial r c u n))
    (hs : RadialAlias.RadiallySupported p.inner p.outer (rankDesiredAxial r c u n))
    (x : Lift S) :
    (rankIncrement p r axial c u).axial n x = rankDesiredAxial r c u n (x.1, x.2.1) := by
  apply MeanRankUpdate.slow_streamGamma_eq_desired ha p.inner_lt_outer hd p.radialDirection hf hs
  intro z
  exact (rank_model_rows r c u n z hlam (hC z) hra hrab (hell z) (hU z)).2.1


-- @@ L577-587 verbatim
theorem rank_divergence_zero (p : ReconstructionData) (r : RankData S)
    (axial : S × PressureStream.Plane) (c : Context (Lift S)) (u : State (Lift S))
    (ha : 0 < p.inner) (hd : 0 < p.exponent) (n : ℕ)
    (hf : ContDiff ℝ ∞ (rankDesiredAxial r c u n))
    (hs : RadialAlias.RadiallySupported p.inner p.outer (rankDesiredAxial r c u n))
    (x : Lift S) :
    PressureStream.graphDivergence (PressureStream.physicalSpeed p.exponent (p.frequency n))
      ((0 : S), p.radialDirection) (c.operators.epsilon n • axial)
      ((rankIncrement p r axial c u).radial n) ((rankIncrement p r axial c u).axial n) x = 0 :=
  MeanRankUpdate.slow_stream_divergence_zero ha p.inner_lt_outer hd p.radialDirection
    (c.operators.epsilon n • axial) hf hs x


-- @@ L589-589 verbatim
end Rank


-- @@ L591-591 verbatim
end NavierStokes.CorrectionState
