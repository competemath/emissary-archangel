/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.IntProp.Hilbert.Basic


-- @@ L10-10 verbatim
/-! # Int -/


-- @@ L12-12 verbatim
@[expose] public section



-- @@ L15-15 verbatim
namespace LO

-- @@ L16-16 verbatim
namespace IntProp

-- @@ L17-17 verbatim
namespace Hilbert


-- @@ L19-19 verbatim
variable {H : Hilbert α}


-- @@ L21-21 verbatim
open Deduction


-- @@ L23-23 verbatim
section «lp_section_1»


-- @@ L25-29 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class HasEFQ (H : Hilbert α) where
  /-- Imported declaration from the Incompleteness formalization. -/
  p : α
  mem_efq : (Arrow.arrow ⊥ (.atom p)) ∈ H.axioms := by tauto;


-- @@ L31-34 verbatim
instance [DecidableEq α] [hEfq : H.HasEFQ] : Entailment.HasAxiomEFQ H where
  efq φ :=
    maxm ⟨Axioms.EFQ (Formula.atom hEfq.p), hEfq.mem_efq,
      fun b => if hEfq.p = b then φ else (.atom b), by simp⟩

-- @@ L35-35 verbatim
instance [DecidableEq α] [H.HasEFQ] : Entailment.Intuitionistic H where


-- @@ L37-37 verbatim
end «lp_section_1»



-- @@ L40-40 verbatim
section «lp_section_2»


-- @@ L42-43 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Int : Hilbert ℕ := ⟨{Axioms.EFQ (.atom 0)}⟩

-- @@ L44-44 verbatim
instance : Hilbert.Int.FiniteAxiomatizable where

-- @@ L45-45 verbatim
instance : Hilbert.Int.HasEFQ where p := 0;


-- @@ L47-47 verbatim
end «lp_section_2»


-- @@ L49-49 verbatim
end Hilbert

-- @@ L50-50 verbatim
end IntProp

-- @@ L51-51 verbatim
end LO
