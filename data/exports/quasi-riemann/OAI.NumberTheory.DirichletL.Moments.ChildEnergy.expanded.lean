import OAI.NumberTheory.DirichletL.Moments.GaussEnergy
import OAI.NumberTheory.DirichletL.Moments.Cauchy


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped BigOperators Classical SchwartzMap

-- @@ L8-8 verbatim
namespace SevenEighths.CenteredMomentChildEnergy

-- @@ L9-9 verbatim
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentCauchy

-- @@ L10-10 verbatim
open CenteredMomentSmooth

-- @@ L11-11 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L13-21 verbatim
theorem leftColumn_eq_gaussPolynomial {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (V : ℝ → ℂ) (u : α → ℝ) (z : O) (t : ℝ) :
    leftColumn S (fun i => c i * gaussRow (a i) (ha i) z) V u t =
      gaussPolynomial S a ha (fun i => c i * columnPhase V (u i) t) z := by
  unfold leftColumn gaussPolynomial
  apply Finset.sum_congr rfl
  intro i hi
  ring


-- @@ L23-31 verbatim
theorem rightColumn_eq_star_gaussPolynomial {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (V : ℝ → ℂ) (u : α → ℝ) (z : O) (t : ℝ) :
    rightColumn S (fun i => c i * gaussRow (a i) (ha i) z) V u t =
      star (gaussPolynomial S a ha (fun i => c i * star (columnPhase V (u i) t)) z) := by
  simp only [rightColumn, gaussPolynomial, star_sum, star_mul, star_star]
  apply Finset.sum_congr rfl
  intro i hi
  ring


-- @@ L33-80 verbatim
theorem whole_kernel_gauss_child_bound (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J₁ J₂ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
        (a : α → O) (b : β → O)
        (ha : ∀ i, Supported (Ideal.span {a i}))
        (hb : ∀ j, Supported (Ideal.span {b j}))
        (c : α → ℂ) (d : β → ℂ) (u : α → ℝ) (v : β → ℝ)
        (ρ x : O → ℝ) (η : O → ℂ),
      (∀ z ∈ rows, ‖η z‖ ≤ 1) →
      (∀ z ∈ rows, ‖V 0 (ρ z)‖ ≤ 1) → (∀ z ∈ rows, ‖V 1 (x z)‖ ≤ 1) →
      ∀ (U : 𝓢(ℝ, ℂ)) (K : ℝ), 0 < K →
      (∀ z : O, 0 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / K)).re) →
      (∀ z ∈ rows, 1 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / K)).re) →
      ∀ E₁ E₂ : ℝ, 0 ≤ E₁ → 0 ≤ E₂ →
      (∀ t : ℝ, (gaussEnergy S a ha (fun i => c i * columnPhase (V 2) (u i) t) U K).re ≤
        (E₁ * (1 + ‖t‖) ^ J₁) ^ 2) →
      (∀ t : ℝ, (gaussEnergy T b hb (fun j => d j * star (columnPhase (V 3) (v j) t)) U K).re ≤
        (E₂ * (1 + ‖t‖) ^ J₂) ^ 2) →
      (1 + R) ^ A * ‖∑ z ∈ rows, η z *
        (∑ i ∈ S, ∑ j ∈ T,
          ((c i * gaussRow (a i) (ha i) z) * star (d j * gaussRow (b j) (hb j) z)) *
            wholeKernel W V R (ρ z) (x z) (u i) (v j))‖ ≤ C * (E₁ * E₂) := by
  obtain ⟨C, hC, hbound⟩ := whole_kernel_row_estimate W V M hM hV A (J₁ + J₂)
  refine ⟨C, hC, ?_⟩
  intro R hR α β rows S T a b ha hb c d u v ρ x η hη hV₀ hV₁ U K hK hU hmajor
    E₁ E₂ hE₁ hE₂ hleft hright
  apply hbound R hR rows S T
    (fun z i => c i * gaussRow (a i) (ha i) z)
    (fun z j => d j * gaussRow (b j) (hb j) z) u v ρ x η hη hV₀ hV₁
    (E₁ * E₂) (mul_nonneg hE₁ hE₂)
  intro t
  have hL := (finite_energy_le_gaussEnergy S a ha
    (fun i => c i * columnPhase (V 2) (u i) t) U K hK rows hU hmajor).trans (hleft t)
  have hR' := (finite_energy_le_gaussEnergy T b hb
    (fun j => d j * star (columnPhase (V 3) (v j) t)) U K hK rows hU hmajor).trans (hright t)
  have hl : Real.sqrt (∑ z ∈ rows,
      ‖gaussPolynomial S a ha (fun i => c i * columnPhase (V 2) (u i) t) z‖ ^ 2) ≤
      E₁ * (1 + ‖t‖) ^ J₁ := (Real.sqrt_le_iff).mpr ⟨by positivity, hL⟩
  have hr : Real.sqrt (∑ z ∈ rows,
      ‖gaussPolynomial T b hb (fun j => d j * star (columnPhase (V 3) (v j) t)) z‖ ^ 2) ≤
      E₂ * (1 + ‖t‖) ^ J₂ := (Real.sqrt_le_iff).mpr ⟨by positivity, hR'⟩
  simp only [leftColumn_eq_gaussPolynomial, rightColumn_eq_star_gaussPolynomial, norm_star]
  calc
    _ ≤ (E₁ * (1 + ‖t‖) ^ J₁) * (E₂ * (1 + ‖t‖) ^ J₂) :=
      mul_le_mul hl hr (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; ring


-- @@ L82-82 verbatim
end SevenEighths.CenteredMomentChildEnergy


-- @@ L84-84 verbatim
end


-- @@ L86-86 verbatim
end OAI
