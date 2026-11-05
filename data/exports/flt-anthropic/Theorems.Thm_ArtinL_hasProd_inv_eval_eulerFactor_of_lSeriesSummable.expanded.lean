import Mathlib
import Definitions.Def_ArtinL_EulerFactor
import P2M.Util
import P2M.Sol.S_ArtinL_hasProd_inv_eval_eulerFactor_of_lSeriesSummable


-- @@ L6-6 verbatim
set_option autoImplicit false


-- @@ L8-8 verbatim
open scoped MatrixGroups


-- @@ L10-10 verbatim
local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)


-- @@ L12-19 expanded
theorem ArtinL.hasProd_inv_eval_eulerFactor_of_lSeriesSummable {n : ℕ}
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin n) ℂ) {s : ℂ}
    (hsum : LSeriesSummable (ArtinL.coeff ρ) s) :
    (∀ p : ℕ,
        p.Prime →
          HasSum (fun k : ℕ => ArtinL.coeffPrimePow ρ p k * ((p : ℂ) ^ (-s)) ^ k)
              (((ArtinL.eulerFactor ρ p).eval ((p : ℂ) ^ (-s)))⁻¹) ∧
            (ArtinL.eulerFactor ρ p).eval ((p : ℂ) ^ (-s)) ≠ 0) ∧
      HasProd (fun p : Nat.Primes => ((ArtinL.eulerFactor ρ p).eval ((p : ℂ) ^ (-s)))⁻¹)
        (ArtinL.LSeries ρ s) :=
  by
  p2m_exact_reverting @_root_.P2MW.S_ArtinL_hasProd_inv_eval_eulerFactor_of_lSeriesSummable.solution

