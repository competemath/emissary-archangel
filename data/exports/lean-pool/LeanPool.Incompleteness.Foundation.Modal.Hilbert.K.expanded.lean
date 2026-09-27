/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.Hilbert.Basic


-- @@ L10-10 verbatim
/-! # K -/


-- @@ L12-12 verbatim
@[expose] public section



-- @@ L15-15 verbatim
namespace LO

-- @@ L16-16 verbatim
namespace Modal

-- @@ L17-17 verbatim
namespace Hilbert


-- @@ L19-19 verbatim
variable {H : Hilbert α}


-- @@ L21-21 verbatim
open Deduction


-- @@ L23-23 verbatim
section «lp_section_1»


-- @@ L25-32 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class HasK (H : Hilbert α) where
  /-- Imported declaration from the Incompleteness formalization. -/
  p : α
  /-- Imported declaration from the Incompleteness formalization. -/
  q : α
  ne_pq : p ≠ q := by trivial;
  mem_K : Axioms.K (.atom p) (.atom q) ∈ H.axioms := by tauto;


-- @@ L34-37 verbatim
instance [DecidableEq α] [hK : H.HasK] : Entailment.HasAxiomK H where
  K φ ψ :=
    maxm ⟨Axioms.K (.atom hK.p) (.atom hK.q), hK.mem_K,
      (fun b => if hK.p = b then φ else if hK.q = b then ψ else (.atom b)), by simp [hK.ne_pq]⟩


-- @@ L39-39 verbatim
end «lp_section_1»



-- @@ L42-42 verbatim
section «lp_section_2»


-- @@ L44-45 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev K : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1)}⟩

-- @@ L46-46 verbatim
instance : Hilbert.K.FiniteAxiomatizable where

-- @@ L47-47 verbatim
instance : Hilbert.K.HasK where p := 0; q := 1

-- @@ L48-48 verbatim
instance : Entailment.K (Hilbert.K) where


-- @@ L50-50 verbatim
end «lp_section_2»


-- @@ L52-52 verbatim
end Hilbert

-- @@ L53-53 verbatim
end Modal

-- @@ L54-54 verbatim
end LO
