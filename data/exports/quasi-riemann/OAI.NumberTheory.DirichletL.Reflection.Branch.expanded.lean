import OAI.NumberTheory.DirichletL.Reflection.Brackets


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace SevenEighths.InverseReflectedPhase

-- @@ L6-6 verbatim
open scoped Classical BigOperators

-- @@ L7-7 verbatim
open ActualEisensteinCubic CubicEisenstein CompletedGauss LocalReflectionBrackets

-- @@ L8-8 verbatim
open CanonicalQuadraticSieve

-- @@ L9-9 verbatim
noncomputable section

-- @@ L10-10 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L11-11 verbatim
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

-- @@ L12-12 verbatim
noncomputable local instance branchFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _


-- @@ L14-23 verbatim
theorem residual_branch_zero (K : Ideal Eis) (hK : Admissible K) (n b : Ideal Eis) :
    reflectedBranch (fun P : PrimeIndex K => P.val) (admissiblePrimeGood K hK)
      (fun _ => 1) (fun _ => 0) (primaryGenerator n) (primaryGenerator b) =
      quadraticRow K (primaryGenerator (n*b)) := by
  simp only [reflectedBranch,reflectedLocalPiece,show (1:ℕ) ≠ 4 by decide,↓reduceIte]
  have hh := residual_bracket_product (fun P : PrimeIndex K => P.val)
    (admissiblePrimeGood K hK) 1 (primaryGenerator n) (primaryGenerator b)
  simp only [one_mul] at hh
  rw [hh,← quadraticRow_eq_primeIndex K hK,← quadraticRow_eq_primeIndex K hK,
    canonical_quadraticRow_one K hK,one_mul,primaryGenerator_mul]


-- @@ L25-33 verbatim
theorem marked_branch_zero {ι : Type*} [Fintype ι]
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, λ₀ ∉ P i) (n b : Ideal Eis) (hb : primaryGenerator b ≠ 0) :
    reflectedBranch P hg (fun _ => 0) (fun _ => 0) (primaryGenerator n) (primaryGenerator b) =
      (Real.sqrt (Ideal.absNorm (∏ i, P i) : ℝ) : ℂ)⁻¹ *
      InverseMoment.inverseCubicKernel (∏ i, P i) n *
      (if IsCoprime (∏ i, P i) b then 1 else 0) := by
  simpa only [reflectedBranch,reflectedLocalPiece,show (0:ℕ) ≠ 4 by decide,↓reduceIte]
    using marked_bracket_hybrid P hg n b hb


-- @@ L35-49 verbatim
theorem moving_branches_hybrid {ι : Type*} [Fintype ι]
    (K : Ideal Eis) (hK : Admissible K)
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal] (hg : ∀ i, λ₀ ∉ P i)
    (n b : Ideal Eis) (hb : primaryGenerator b ≠ 0) :
    reflectedBranch (fun R : PrimeIndex K => R.val) (admissiblePrimeGood K hK)
      (fun _ => 1) (fun _ => 0) (primaryGenerator n) (primaryGenerator b) *
    reflectedBranch P hg (fun _ => 0) (fun _ => 0) (primaryGenerator n) (primaryGenerator b) *
      (if IsCoprime K (∏ i, P i) then 1 else 0) =
    (Real.sqrt (Ideal.absNorm (∏ i, P i) : ℝ) : ℂ)⁻¹ *
      quadraticRow K (primaryGenerator (n*b)) *
      InverseMoment.inverseCubicKernel (∏ i, P i) n *
      (if IsCoprime (∏ i, P i) b then 1 else 0) *
      (if IsCoprime K (∏ i, P i) then 1 else 0) := by
  rw [residual_branch_zero K hK n b,marked_branch_zero P hg n b hb]
  ring


-- @@ L51-69 verbatim
theorem frozen_moving_branches_hybrid {ι κ : Type*} [Fintype ι] [Fintype κ]
    (K : Ideal Eis) (hK : Admissible K)
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal] (hg : ∀ i, λ₀ ∉ P i)
    (F : κ → Ideal Eis) [∀ i, (F i).IsMaximal] (hf : ∀ i, λ₀ ∉ F i)
    (j : κ → ℕ) (e : κ → Fin 3) (β : Ideal Eis → Ideal Eis → ℂ)
    (n b : Ideal Eis) (hb : primaryGenerator b ≠ 0) :
    β n b * reflectedBranch F hf j e (primaryGenerator n) (primaryGenerator b) *
      (reflectedBranch (fun R : PrimeIndex K => R.val) (admissiblePrimeGood K hK)
        (fun _ => 1) (fun _ => 0) (primaryGenerator n) (primaryGenerator b) *
      reflectedBranch P hg (fun _ => 0) (fun _ => 0) (primaryGenerator n) (primaryGenerator b) *
        (if IsCoprime K (∏ i, P i) then 1 else 0)) =
    (Real.sqrt (Ideal.absNorm (∏ i, P i) : ℝ) : ℂ)⁻¹ *
      (β n b * reflectedBranch F hf j e (primaryGenerator n) (primaryGenerator b)) *
      quadraticRow K (primaryGenerator (n*b)) *
      InverseMoment.inverseCubicKernel (∏ i, P i) n *
      (if IsCoprime (∏ i, P i) b then 1 else 0) *
      (if IsCoprime K (∏ i, P i) then 1 else 0) := by
  rw [moving_branches_hybrid K hK P hg n b hb]
  ring


-- @@ L71-71 verbatim
end

-- @@ L72-72 verbatim
end SevenEighths.InverseReflectedPhase


-- @@ L74-74 verbatim
end OAI
