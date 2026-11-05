import Definitions.Def_GaloisRep_CompletionBridge
import P2M.Util
import P2M.Sol.S_PadicAlgCl_exists_mem_adjoin_padicEmbedding


-- @@ L5-5 verbatim
set_option autoImplicit false

-- @@ L6-6 verbatim
open scoped IntermediateField

-- @@ L7-9 verbatim
theorem PadicAlgCl.exists_mem_adjoin_padicEmbedding
    (q : ℕ) [Fact q.Prime] (α : PadicAlgCl q) :
    ∃ b : AlgebraicClosure ℚ, α ∈ ℚ_[q]⟮padicEmbedding q b⟯ := by p2m_exact_reverting @_root_.P2MW.S_PadicAlgCl_exists_mem_adjoin_padicEmbedding.solution
