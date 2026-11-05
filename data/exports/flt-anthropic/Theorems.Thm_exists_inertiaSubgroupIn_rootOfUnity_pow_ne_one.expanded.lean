import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_exists_inertiaSubgroupIn_rootOfUnity_pow_ne_one


-- @@ L5-5 verbatim
set_option autoImplicit false


-- @@ L7-7 verbatim
local notation "Qbar" => AlgebraicClosure ℚ


-- @@ L9-13 expanded
theorem exists_inertiaSubgroupIn_rootOfUnity_pow_ne_one (ℓ : ℕ) (hℓ : ℓ.Prime)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ) :
    ∃ σ ∈ A.inertiaSubgroupIn ℚ,
      ∃ n a : ℕ, (∀ μ : AlgebraicClosure ℚ, μ ^ ℓ ^ n = 1 → σ μ = μ ^ a) ∧ ¬a ≡ 1 [MOD ℓ ^ n] :=
  by p2m_exact_reverting @_root_.P2MW.S_exists_inertiaSubgroupIn_rootOfUnity_pow_ne_one.solution

