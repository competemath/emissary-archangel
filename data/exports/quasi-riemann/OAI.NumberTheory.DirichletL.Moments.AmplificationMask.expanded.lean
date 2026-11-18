import OAI.NumberTheory.DirichletL.Moments.AmplificationRectangle


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped BigOperators Classical

-- @@ L7-7 verbatim
namespace SevenEighths.CenteredMomentAmplificationMask

-- @@ L8-8 verbatim
open CenteredMomentRectangle CenteredMomentAmplificationRectangle CenteredMomentAmplificationShortening

-- @@ L9-9 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L11-20 verbatim
theorem whole_product_divisibility (p : O) (s Q I J : Ideal O)
    (hcop : IsCoprime s (Ideal.span {p})) (k j : ℕ) (hj : j ≤ k) :
    s∣Q*((Ideal.span {p})^j*I)*((Ideal.span {p})^(k-j)*J) ↔ s∣Q*I*J := by
  have he : Q*((Ideal.span {p})^j*I)*((Ideal.span {p})^(k-j)*J) =
      (Ideal.span {p})^k*(Q*I*J) := by
    calc
      _ = ((Ideal.span {p})^j*(Ideal.span {p})^(k-j))*(Q*I*J) := by ring
      _ = _ := by rw [← pow_add,Nat.add_sub_of_le hj]
  rw [he]
  exact (hcop.pow_right (n := k)).dvd_mul_left_iff


-- @@ L22-43 verbatim
theorem masked_centered_coefficient_prime_extract (p : O) (hp : p ≠ 0)
    (s : Ideal O) (hcop : IsCoprime s (Ideal.span {p}))
    (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ T : ℝ) (hT : 0 < T)
    (Q I J : Ideal O) (k j : ℕ) (hj : j ≤ k) :
    (Real.sqrt T:ℂ)⁻¹ *
      (idealWeight c χ R t (Q*((Ideal.span {p})^j*I)*((Ideal.span {p})^(k-j)*J))*
        CenteredMomentRectangle.idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂
          ((Ideal.span {p})^j*I) ((Ideal.span {p})^(k-j)*J)) *
      (if s∣Q*((Ideal.span {p})^j*I)*((Ideal.span {p})^(k-j)*J) then (1:ℂ) else 0) =
      (idealWeight c χ R t ((Ideal.span {p})^k)/primeRoot p k)*
        ((Real.sqrt (T/(Ideal.absNorm (Ideal.span {p}):ℝ)^k):ℂ)⁻¹ *
          (idealWeight c χ R t (Q*I*J)*
            CenteredMomentRectangle.idealRectangle W₁ W₂
              (X₁/(Ideal.absNorm (Ideal.span {p}):ℝ)^j)
              (X₂/(Ideal.absNorm (Ideal.span {p}):ℝ)^(k-j))
              (Y₁/(Ideal.absNorm (Ideal.span {p}):ℝ)^j)
              (Y₂/(Ideal.absNorm (Ideal.span {p}):ℝ)^(k-j)) I J)*
          (if s∣Q*I*J then (1:ℂ) else 0)) := by
  simp only [whole_product_divisibility p s Q I J hcop k j hj]
  rw [centered_coefficient_prime_extract p hp c χ R t W₁ W₂ X₁ X₂ Y₁ Y₂ T hT Q I J k j hj]
  ring


-- @@ L45-45 verbatim
end SevenEighths.CenteredMomentAmplificationMask


-- @@ L47-47 verbatim
end


-- @@ L49-49 verbatim
end OAI
