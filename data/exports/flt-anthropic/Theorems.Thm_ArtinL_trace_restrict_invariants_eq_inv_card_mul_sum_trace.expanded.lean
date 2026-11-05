import Mathlib
import Definitions.Def_ArtinL_EulerFactor
import Definitions.Def_ArtinL_Abelian
import P2M.Util
import P2M.Sol.S_ArtinL_trace_restrict_invariants_eq_inv_card_mul_sum_trace


-- @@ L7-7 verbatim
set_option autoImplicit false


-- @@ L9-9 verbatim
open scoped MatrixGroups

-- @@ L10-10 verbatim
open NumberField


-- @@ L12-12 verbatim
local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)


-- @@ L14-22 verbatim
theorem ArtinL.trace_restrict_invariants_eq_inv_card_mul_sum_trace
    {K : Type*} [Field K] [CharZero K] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V) (I : Subgroup G) [Fintype ↥I]
    (g : G)
    (h : ∀ v ∈ Representation.invariants (ρ.comp I.subtype),
      ρ g v ∈ Representation.invariants (ρ.comp I.subtype)) :
    LinearMap.trace K _ ((ρ g).restrict h) =
      (Fintype.card ↥I : K)⁻¹ * ∑ τ : ↥I, LinearMap.trace K V (ρ (g * τ)) := by p2m_exact_reverting @_root_.P2MW.S_ArtinL_trace_restrict_invariants_eq_inv_card_mul_sum_trace.solution
