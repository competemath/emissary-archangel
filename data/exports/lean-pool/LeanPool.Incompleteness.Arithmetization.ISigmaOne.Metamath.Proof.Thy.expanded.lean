/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Arithmetization.ISigmaOne.Metamath.Language
import LeanPool.Incompleteness.Arithmetization.Definability.Init


-- @@ L11-11 verbatim
/-! # Thy -/


-- @@ L13-13 verbatim
@[expose] public section



-- @@ L16-16 verbatim
noncomputable section «lp_nc_section_1»


-- @@ L18-18 verbatim
namespace LO

-- @@ L19-19 verbatim
namespace Arith


-- @@ L21-21 verbatim
open FirstOrder FirstOrder.Arith


-- @@ L23-23 verbatim
variable {V : Type*} [ORingStruc V]


-- @@ L25-25 verbatim
variable {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL]


-- @@ L27-27 verbatim
section «lp_section_1»


-- @@ L29-29 verbatim
variable (L)


-- @@ L31-34 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
structure _root_.LO.FirstOrder.Arith.LDef.TDef (pL : LDef) where
  /-- Imported declaration from the Incompleteness formalization. -/
  ch : Dlt1.Semisentence 1


-- @@ L36-40 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected structure _root_.LO.Arith.Language.Theory (L : Arith.Language V) {pL :
    LDef} [Arith.Language.Defined L pL] where
  /-- Imported declaration from the Incompleteness formalization. -/
  set : Set V


-- @@ L42-42 verbatim
instance : Membership V L.Theory := ⟨fun T x ↦ x ∈ T.set⟩


-- @@ L44-44 verbatim
instance : HasSubset L.Theory := ⟨fun T U ↦ T.set ⊆ U.set⟩


-- @@ L46-46 verbatim
lemma _root_.LO.Arith.Language.Theory.mem_def {T : L.Theory} {p} : p ∈ T ↔ p ∈ T.set := by rfl


-- @@ L48-48 verbatim
variable {L}


-- @@ L50-50 verbatim
namespace Language

-- @@ L51-51 verbatim
namespace Theory


-- @@ L53-55 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected class Defined (T : L.Theory) (pT : outParam pL.TDef) where
  defined : DefinedPred Dlt1 (· ∈ T.set) pT.ch


-- @@ L57-57 verbatim
variable (T : L.Theory) {pT : pL.TDef} [T.Defined pT]


-- @@ L59-60 expanded
/-- Imported declaration from the Incompleteness formalization. -/
lemma mem_defined : DefinedPred Dlt1 (· ∈ T) pT.ch :=
  Defined.defined


-- @@ L62-62 expanded
instance mem_definable : BoldfacePred Dlt1 (· ∈ T) :=
  (mem_defined T).to_definable


-- @@ L64-64 verbatim
end Theory

-- @@ L65-65 verbatim
end Language


-- @@ L67-67 verbatim
end «lp_section_1»

-- @@ L68-68 verbatim
end Arith

-- @@ L69-69 verbatim
end LO
