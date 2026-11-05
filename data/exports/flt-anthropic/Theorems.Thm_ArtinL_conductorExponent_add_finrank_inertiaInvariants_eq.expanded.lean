import Mathlib
import Definitions.Def_ArtinL_Conductor
import Definitions.Def_GaloisRep_Residual
import P2M.Util
import P2M.Sol.S_ArtinL_conductorExponent_add_finrank_inertiaInvariants_eq


-- @@ L7-7 verbatim
set_option autoImplicit false


-- @@ L9-9 verbatim
open scoped MatrixGroups


-- @@ L11-11 verbatim
local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)


-- @@ L13-17 expanded
theorem ArtinL.conductorExponent_add_finrank_inertiaInvariants_eq {n : ℕ}
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin n) ℂ)
    (hρ : GaloisFactorsThroughFiniteLevel ρ) {p : ℕ} (hp : p.Prime)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (htame : (Nat.card ((A.inertiaSubgroupIn ℚ).map ρ)).Coprime p) :
    ArtinL.conductorExponent ρ p + Module.finrank ℂ (ArtinL.inertiaInvariants ρ A) = n := by
  p2m_exact_reverting
    @_root_.P2MW.S_ArtinL_conductorExponent_add_finrank_inertiaInvariants_eq.solution

