import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L6-6 verbatim
open scoped ENNReal NNReal RealInnerProductSpace Topology

-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
namespace CurrentProjection


-- @@ L10-10 verbatim
abbrev Vector (d : ℕ) := EuclideanSpace ℝ (Fin d)

-- @@ L11-11 verbatim
abbrev Sphere (d : ℕ) := Metric.sphere (0 : Vector d) 1

-- @@ L12-12 verbatim
abbrev Rows (k d : ℕ) := Fin k → Vector d



-- @@ L15-17 verbatim
def uniformSphere (d : ℕ) : Measure (Sphere d) :=
  let σ := (volume : Measure (Vector d)).toSphere
  (σ Set.univ)⁻¹ • σ



-- @@ L20-21 verbatim
def gaussianRows (k d : ℕ) : Measure (Rows k d) :=
  Measure.pi fun _ => stdGaussian (Vector d)


-- @@ L23-24 verbatim
def label {k d : ℕ} (g : Rows k d) (s : Vector d) : Fin k → ℝ :=
  fun i => ⟪s, g i⟫



-- @@ L27-29 verbatim
def LocalGrowth {d : ℕ} (ρ : Measure (Sphere d)) (a : ℕ) (B : ℝ) : Prop :=
  ∀ z : Vector d, ∀ t : ℝ, 0 < t →
    ρ {u | dist (u : Vector d) z ≤ t} ≤ ENNReal.ofReal (B * t ^ a)



-- @@ L32-35 verbatim
def cubeAverage {k d : ℕ} (ρ : Measure (Sphere d)) (g : Rows k d)
    (y : Fin k → ℝ) (δ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 * δ)⁻¹ ^ k) *
    ρ {u | ∀ i, |label g (u : Vector d) i - y i| ≤ δ}



-- @@ L38-42 verbatim
def exactDensity {k d : ℕ} (ρ : Measure (Sphere d)) (g : Rows k d)
    (y : Fin k → ℝ) : ℝ≥0∞ := by
  classical
  let f := fun j : ℕ => (cubeAverage ρ g y (1 / (j : ℝ))).toReal
  exact if h : ∃ L : ℝ, Tendsto f atTop (𝓝 L) then ENNReal.ofReal h.choose else 0



-- @@ L45-46 verbatim
def AdmissibleDimensions (d m r q : ℕ) : Prop :=
  1 ≤ m ∧ 1 ≤ r ∧ 1 ≤ q ∧ m + r < d - 1 ∧ m + r - m - (q - 1) ≥ 1


-- @@ L48-49 verbatim
def momentConstant (C : ℝ) (d : ℕ) (B D : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (C * d) * B * (1 + max (Real.log (D / B)) 0))




-- @@ L53-71 verbatim
def MixedMomentMain : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (d m r q : ℕ), AdmissibleDimensions d m r q →
    ∀ (ρ : Measure (Sphere d)), IsFiniteMeasure ρ →
    ∀ (B D : ℝ), 0 < B → 0 < D → LocalGrowth ρ (m+r) B → LocalGrowth ρ (d-1) D →
    (∀ (s : Sphere d) (δ : ℝ), 0 < δ →
      (∫⁻ X, (∫⁻ Z, cubeAverage ρ (Fin.append X Z)
        (label (Fin.append X Z) (s : Vector d)) δ ∂gaussianRows r d)^q
          ∂gaussianRows m d) ≤ (momentConstant C d B D)^q) ∧
    (ρ ≪ uniformSphere d → ∃ E : Set (Sphere d), MeasurableSet E ∧ ρ E = 0 ∧
      ∀ s ∉ E,
        (∀ᵐ G ∂gaussianRows (m+r) d,
          Tendsto (fun δ : ℝ => cubeAverage ρ G (label G (s : Vector d)) δ)
            (𝓝[>] 0) (𝓝 (exactDensity ρ G (label G (s : Vector d))))) ∧
        ((∫⁻ X, (∫⁻ Z, exactDensity ρ (Fin.append X Z)
          (label (Fin.append X Z) (s : Vector d)) ∂gaussianRows r d)^q
            ∂gaussianRows m d) ≤ (momentConstant C d B D)^q) ∧
        (ρ ≠ 0 → ∀ᵐ G ∂gaussianRows (m+r) d,
          0 < exactDensity ρ G (label G (s : Vector d)) ∧
          exactDensity ρ G (label G (s : Vector d)) < ∞))





-- @@ L76-76 verbatim
end CurrentProjection


-- @@ L78-78 verbatim
end


-- @@ L80-80 verbatim
end OAI
