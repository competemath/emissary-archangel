import Singularity.RealHittingMartinDensity
import Singularity.MobiusOrbitDensity
import Singularity.GeometricHittingErgodicity


-- @@ L5-11 verbatim
/-!
# Logarithmic analysis columns for actual hitting measures

A visual upper bound constructs the bounded analysis family. Its cyclic rows
are the logarithmic densities q(u) K(a^n b_j,u), simultaneously almost
everywhere. The base density may be any measurable nonnegative representative.
-/


-- @@ L13-13 verbatim
noncomputable section

-- @@ L14-14 verbatim
open MeasureTheory Filter Set OnePoint

-- @@ L15-15 verbatim
open scoped Classical Topology MatrixGroups UpperHalfPlane ENNReal

-- @@ L16-16 verbatim
namespace Singularity


-- @@ L18-22 verbatim
variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (z : ℍ)


-- @@ L24-24 verbatim
local notation "ν" => geometricHittingMeasure Γ s μ hpos hmass hgen hgap z


-- @@ L26-28 verbatim
local instance : IsProbabilityMeasure (finiteBoundaryMeasure ν) := by
  let := geometricHittingMeasure_probability Γ s μ hpos hmass hgen hgap z
  exact finiteBoundaryMeasure_probability ν


-- @@ L30-32 verbatim
variable {J : Type*} [Fintype J] (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
  {τ : ℝ} (hτ : 0 < τ) (B : ℝ) (hB : 0 ≤ B)
  (hbound : geometricHittingMeasure Γ s μ hpos hmass hgen hgap z ≤ ENNReal.ofReal B • compactPoissonMeasure UpperHalfPlane.I) (b : J → Γ)


-- @@ L34-37 verbatim
/-- The bounded lattice density family of the actual hitting law. -/
def geometricHittingDensityFamily : DensityFamily ℝ (ℤ × J) volume :=
  mobiusBoundaryDensityFamily ε hε hτ (finiteBoundaryMeasure ν) UpperHalfPlane.I B hB
    (finiteBoundaryMeasure_poisson_bound ν UpperHalfPlane.I B hbound) (fun j => (b j : SL(2, ℝ)))


-- @@ L39-44 verbatim
/-- Finite lattice translation gives a nonzero kernel for this actual analysis operator. -/
theorem geometricHittingDensityFamily_has_kernel :
    ∃ v : RealLineL2, v ≠ 0 ∧
      (geometricHittingDensityFamily Γ s μ hpos hmass hgen hgap z ε hε hτ B hB hbound b).analysis v = 0 :=
  mobiusBoundary_analysis_has_kernel ε hε hτ (finiteBoundaryMeasure ν) UpperHalfPlane.I B hB
    (finiteBoundaryMeasure_poisson_bound ν UpperHalfPlane.I B hbound) (fun j => (b j : SL(2, ℝ)))


-- @@ L46-48 verbatim
variable [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  (horbit : (MulAction.orbit Γ (∞ : OnePoint ℝ)).Infinite)
  (a : Γ) (ha : (a : SL(2, ℝ)) = dilationMatrix τ)


-- @@ L50-78 verbatim
include horbit ha in
/-- On one common full-measure set, all actual density-column coordinates
are the base density times the actual Martin coordinates and the Jacobian. -/
theorem geometricHittingDensityFamily_column_ae
    (q : ℝ → ℝ) (hq : Measurable q) (hpq : ∀ u, 0 ≤ q u)
    (hmeasure : volume.withDensity (fun u => ENNReal.ofReal (q u)) = finiteBoundaryMeasure ν) :
    ∀ᵐ t : ℝ ∂volume, ∀ p : ℤ × J,
      (geometricHittingDensityFamily Γ s μ hpos hmass hgen hgap z ε hε hτ B hB hbound b).column t p =
        ((Real.exp t * q (ε * Real.exp t) *
          (rayMartinPoint Γ s μ hpos hgen hgap (ε * Real.exp t)).val (a ^ p.1 * b p.2) : ℝ) : ℂ) := by
  have hac : ν ≪ compactPoissonMeasure z :=
    (Measure.absolutelyContinuous_of_le_smul hbound).trans (compactPoissonMeasure_absolutelyContinuous _ _)
  have hq' (n : ℤ) (j : J) : Measurable (fun u => q u *
      (rayMartinPoint Γ s μ hpos hgen hgap u).val (a ^ n * b j)) :=
    hq.mul (continuous_rayMartinPoint_eval Γ s μ hpos hmass hgen hgap _).measurable
  have hpq' (n : ℤ) (j : J) (u : ℝ) : 0 ≤ q u *
      (rayMartinPoint Γ s μ hpos hgen hgap u).val (a ^ n * b j) :=
    mul_nonneg (hpq u) (martinBoundaryKernel_pos s μ hpos hgen hgap 1 _ _).le
  have hm (n : ℤ) (j : J) :
      volume.withDensity (fun u => ENNReal.ofReal (q u *
        (rayMartinPoint Γ s μ hpos hgen hgap u).val (a ^ n * b j))) =
        Measure.map (realBoundaryMobius (dilationMatrix τ ^ n * (b j : SL(2, ℝ)))) (finiteBoundaryMeasure ν) := by
    have h := geometricHittingMeasure_real_translate_ray_density Γ s μ hpos hmass hgen hgap
      horbit z hac q hq hpq hmeasure (a ^ n * b j)
    simpa only [Subgroup.coe_mul, Subgroup.coe_zpow, ha] using h
  have h := mobiusOrbit_column_all_ae ε hε hτ (finiteBoundaryMeasure ν) UpperHalfPlane.I B hB
    (finiteBoundaryMeasure_poisson_bound ν UpperHalfPlane.I B hbound) (fun j => (b j : SL(2, ℝ)))
    (fun n j u => q u * (rayMartinPoint Γ s μ hpos hgen hgap u).val (a ^ n * b j)) hq' hpq' hm
  simpa only [geometricHittingDensityFamily, logBoundaryDensity, mul_assoc] using h


-- @@ L80-80 verbatim
end Singularity
