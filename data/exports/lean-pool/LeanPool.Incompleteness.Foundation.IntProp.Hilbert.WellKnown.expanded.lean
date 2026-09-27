/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.IntProp.Hilbert.Int
public import LeanPool.Incompleteness.Foundation.Logic.HilbertStyle.Supplemental


-- @@ L11-11 verbatim
/-! # WellKnown -/


-- @@ L13-13 verbatim
@[expose] public section



-- @@ L16-16 verbatim
namespace LO

-- @@ L17-17 verbatim
namespace IntProp

-- @@ L18-18 verbatim
namespace Hilbert


-- @@ L20-20 verbatim
variable {H : Hilbert α}


-- @@ L22-22 verbatim
open Deduction


-- @@ L24-24 verbatim
section «lp_section_1»


-- @@ L26-30 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class HasLEM (H : Hilbert α) where
  /-- Imported declaration from the Incompleteness formalization. -/
  p : α
  mem_lem : (Vee.vee (.atom p) (Tilde.tilde (.atom p))) ∈ H.axioms := by tauto;


-- @@ L32-35 verbatim
instance [DecidableEq α] [hLEM : H.HasLEM] : Entailment.HasAxiomLEM H where
  lem φ :=
    maxm ⟨Axioms.LEM (.atom hLEM.p), hLEM.mem_lem,
      fun b => if hLEM.p = b then φ else (.atom b), by simp⟩



-- @@ L38-42 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class HasDNE (H : Hilbert α) where
  /-- Imported declaration from the Incompleteness formalization. -/
  p : α
  mem_dne : (Arrow.arrow (Tilde.tilde (Tilde.tilde (.atom p))) (.atom p)) ∈ H.axioms := by tauto;


-- @@ L44-47 verbatim
instance [DecidableEq α] [hDNE : H.HasDNE] : Entailment.HasAxiomDNE H where
  dne φ :=
    maxm ⟨Axioms.DNE (.atom hDNE.p), hDNE.mem_dne,
      fun b => if hDNE.p = b then φ else (.atom b), by simp⟩



-- @@ L50-54 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class HasWeakLEM (H : Hilbert α) where
  /-- Imported declaration from the Incompleteness formalization. -/
  p : α
  mem_wlem :
    (Vee.vee (Tilde.tilde (.atom p)) (Tilde.tilde (Tilde.tilde (.atom p)))) ∈ H.axioms := by tauto;


-- @@ L56-59 verbatim
instance [DecidableEq α] [hWLEM : H.HasWeakLEM] : Entailment.HasAxiomWeakLEM H where
  wlem φ :=
    maxm ⟨Axioms.WeakLEM (.atom hWLEM.p), hWLEM.mem_wlem,
      fun b => if hWLEM.p = b then φ else (.atom b), by simp⟩



-- @@ L62-69 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class HasDummett (H : Hilbert α) where
  /-- Imported declaration from the Incompleteness formalization. -/
  p : α
  /-- Imported declaration from the Incompleteness formalization. -/
  q : α
  ne_pq : p ≠ q := by tauto;
  mem_dummet :
    Vee.vee (Arrow.arrow (.atom p) (.atom q)) (Arrow.arrow (.atom q) (.atom p)) ∈ H.axioms := by
    tauto;


-- @@ L71-75 verbatim
instance [DecidableEq α] [hDummett : H.HasDummett] : Entailment.HasAxiomDummett H where
  dummett φ ψ :=
    maxm ⟨Axioms.Dummett (.atom hDummett.p) (.atom hDummett.q), hDummett.mem_dummet,
      fun b => if hDummett.p = b then φ else if hDummett.q = b then ψ else (.atom b),
      by simp [hDummett.ne_pq]⟩


-- @@ L77-77 verbatim
end «lp_section_1»



-- @@ L80-80 verbatim
section «lp_section_2»



-- @@ L83-84 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Cl : Hilbert ℕ := ⟨{Axioms.EFQ (.atom 0), Axioms.LEM (.atom 0)}⟩

-- @@ L85-85 verbatim
instance : Hilbert.Cl.FiniteAxiomatizable where

-- @@ L86-86 verbatim
instance : Hilbert.Cl.HasEFQ where p := 0;

-- @@ L87-87 verbatim
instance : Hilbert.Cl.HasLEM where p := 0;

-- @@ L88-88 verbatim
instance : Entailment.Classical (Hilbert.Cl) where


-- @@ L90-92 expanded
lemma Int_weakerThan_Cl : WeakerThan (Hilbert.Int) (Hilbert.Cl) := by
  apply weakerThan_of_subset_axioms; tauto;


-- @@ L95-96 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KC : Hilbert ℕ := ⟨{Axioms.EFQ (.atom 0), Axioms.WeakLEM (.atom 0)}⟩

-- @@ L97-97 verbatim
instance : Hilbert.KC.FiniteAxiomatizable where

-- @@ L98-98 verbatim
instance : Hilbert.KC.HasEFQ where p := 0;

-- @@ L99-99 verbatim
instance : Hilbert.KC.HasWeakLEM where p := 0;

-- @@ L100-100 verbatim
instance : Entailment.Intuitionistic (Hilbert.KC) where



-- @@ L103-104 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev LC : Hilbert ℕ := ⟨{Axioms.EFQ (.atom 0), Axioms.Dummett (.atom 0) (.atom 1)}⟩

-- @@ L105-105 verbatim
instance : Hilbert.LC.FiniteAxiomatizable where

-- @@ L106-106 verbatim
instance : Hilbert.LC.HasEFQ where p := 0;

-- @@ L107-107 verbatim
instance : Hilbert.LC.HasDummett where p := 0; q := 1;

-- @@ L108-108 verbatim
instance : Entailment.Intuitionistic (Hilbert.LC) where


-- @@ L110-110 verbatim
end «lp_section_2»


-- @@ L112-112 verbatim
end Hilbert

-- @@ L113-113 verbatim
end IntProp

-- @@ L114-114 verbatim
end LO
