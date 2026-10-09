import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
/-! Nondegenerate spectral calculus, the closed Tomita graph, and bounded recovery. -/


-- @@ L7-7 verbatim
universe u


-- @@ L9-9 verbatim
noncomputable section


-- @@ L11-11 verbatim
open Filter MeasureTheory Set

-- @@ L12-12 verbatim
open scoped Topology ComplexConjugate


-- @@ L14-14 verbatim
namespace BoundedRecovery


-- @@ L16-16 verbatim
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


-- @@ L18-21 verbatim
def spectralCharacter (t : ℝ) : BoundedContinuousFunction ℝ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun u : ℝ => Complex.exp (((t * u : ℝ) : ℂ) * Complex.I))
    (by fun_prop) 1 (by intro u; simp [Complex.norm_exp])


-- @@ L23-29 verbatim
def halfExponentialCutoff (n : ℕ) : BoundedContinuousFunction ℝ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun u : ℝ => (Real.exp (min (n : ℝ) u / 2) : ℂ))
    (by fun_prop) (Real.exp ((n : ℝ) / 2)) (by
      intro u
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)))


-- @@ L31-35 verbatim
structure RealSpectralCalculus (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  calculus : (BoundedContinuousFunction ℝ ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)
  nondegenerate : Dense {h : H | ∃ f : BoundedContinuousFunction ℝ ℂ,
    HasCompactSupport (f : ℝ → ℂ) ∧ ∃ k : H, calculus f k = h}


-- @@ L37-37 verbatim
namespace RealSpectralCalculus


-- @@ L39-40 verbatim
def unitary (D : RealSpectralCalculus H) (t : ℝ) : H →L[ℂ] H :=
  D.calculus (spectralCharacter t)


-- @@ L42-43 verbatim
def halfGraph (D : RealSpectralCalculus H) : Set (H × H) :=
  {p | Tendsto (fun n : ℕ => D.calculus (halfExponentialCutoff n) p.1) atTop (𝓝 p.2)}


-- @@ L45-46 verbatim
def HasSpectralSupport (D : RealSpectralCalculus H) (I : Set ℝ) (h : H) : Prop :=
  ∀ f : BoundedContinuousFunction ℝ ℂ, (∀ u ∈ I, f u = 0) → D.calculus f h = 0


-- @@ L48-48 verbatim
end RealSpectralCalculus


-- @@ L50-62 verbatim
structure StandardModularData (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  M : VonNeumannAlgebra H
  xi : H
  norm_xi : ‖xi‖ = 1
  cyclic : Dense {h : H | ∃ a : H →L[ℂ] H, a ∈ M ∧ a xi = h}
  separating : ∀ a : H →L[ℂ] H, a ∈ M → a xi = 0 → a = 0
  D : RealSpectralCalculus H
  J : H ≃ₗᵢ⋆[ℂ] H
  conjugation : Function.Involutive J
  tomita_graph : closure {p : H × H | ∃ a : H →L[ℂ] H,
      a ∈ M ∧ p = (a xi, (star a) xi)} =
    {p | ∃ q : H, (p.1, q) ∈ D.halfGraph ∧ p.2 = J q}


-- @@ L64-64 verbatim
namespace StandardModularData


-- @@ L66-67 verbatim
def sigma (S : StandardModularData H) (t : ℝ) (a : H →L[ℂ] H) : H →L[ℂ] H :=
  S.D.unitary t * a * S.D.unitary (-t)


-- @@ L69-71 verbatim
def ScalarCentralizer (S : StandardModularData H) : Prop :=
  ∀ a : H →L[ℂ] H, a ∈ S.M → (∀ t : ℝ, S.sigma t a = a) →
    ∃ c : ℂ, a = c • (1 : H →L[ℂ] H)


-- @@ L73-73 verbatim
end StandardModularData


-- @@ L75-76 verbatim
def symmetricAverage (f : ℝ → ℝ) (k : ℕ) : ℝ :=
  (2 * (k : ℝ))⁻¹ * ∫ t in -(k : ℝ)..(k : ℝ), f t


-- @@ L78-79 verbatim
def fixedMean (omega : Ultrafilter ℕ) (f : ℝ → ℝ) : ℝ :=
  Filter.limUnder (omega : Filter ℕ) (symmetricAverage f)


-- @@ L81-86 verbatim
def RecoveryConclusion (S : StandardModularData H) (T : H →L[ℂ] H)
    (s : ℝ) (delta : ℕ → ℝ) : Prop :=
  ∃ (nj : ℕ → ℕ) (_ : StrictMono nj) (v : ℕ → (H →L[ℂ] H)) (C eta : ℝ),
    0 < eta ∧ ∀ j : ℕ, v j ∈ S.M ∧ ‖v j‖ ≤ C ∧ eta ≤ ‖T (v j S.xi)‖ ∧
      S.D.HasSpectralSupport (Icc (s - 4 * delta (nj j)) (s + 4 * delta (nj j)))
        (v j S.xi)


-- @@ L88-88 verbatim
namespace StandardModularData


-- @@ L90-91 verbatim
def state (S : StandardModularData H) (a : H →L[ℂ] H) : ℂ :=
  inner ℂ S.xi (a S.xi)


-- @@ L93-93 verbatim
end StandardModularData


-- @@ L95-95 verbatim
end BoundedRecovery


-- @@ L97-97 verbatim
end


-- @@ L99-99 verbatim
end OAI
