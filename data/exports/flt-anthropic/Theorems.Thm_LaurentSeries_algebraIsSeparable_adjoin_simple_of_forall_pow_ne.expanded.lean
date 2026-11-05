import Mathlib
import P2M.Util
import P2M.Sol.S_LaurentSeries_algebraIsSeparable_adjoin_simple_of_forall_pow_ne


-- @@ L5-5 verbatim
set_option autoImplicit false


-- @@ L7-7 verbatim
open scoped IntermediateField


-- @@ L9-14 verbatim
theorem LaurentSeries.algebraIsSeparable_adjoin_simple_of_forall_pow_ne
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p]
    (F : IntermediateField k (LaurentSeries k)) (t : ↥F)
    (htr : Transcendental k t) (hp : ∀ v : LaurentSeries k, v ^ p ≠ (t : LaurentSeries k))
    [FiniteDimensional ↥k⟮t⟯ ↥F] :
    Algebra.IsSeparable ↥k⟮t⟯ ↥F := by p2m_exact_reverting @_root_.P2MW.S_LaurentSeries_algebraIsSeparable_adjoin_simple_of_forall_pow_ne.solution
