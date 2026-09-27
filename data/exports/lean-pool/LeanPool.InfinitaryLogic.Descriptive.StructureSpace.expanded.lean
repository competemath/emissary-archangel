/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.ModelTheory.Basic
import Mathlib.Basic.Countable.Basic

-- @@ L10-33 verbatim
/-!
# Coding Space for Countable Structures

This file defines the space of countable relational L-structures coded as
functions from relation queries to Bool. The carrier-parametric versions
`RelQueryOn L α` and `StructureSpaceOn L α` generalize over the carrier type,
while `RelQuery L` and `StructureSpace L` specialize to carrier ℕ.

## Main Definitions

- `RelQueryOn L α`: Carrier-parametric relation query index type.
- `StructureSpaceOn L α`: Carrier-parametric coding space `RelQueryOn L α → Bool`.
- `RelQuery L`: Relation queries for carrier ℕ (= `RelQueryOn L ℕ`).
- `StructureSpace L`: The coding space for ℕ-structures (= `StructureSpaceOn L ℕ`).
- `StructureSpaceOn.toStructure`: Decode a code into an L-structure on carrier α.
- `StructureSpaceOn.ofStructure`: Encode a structure into a code.

## Main Results

- `StructureSpaceOn.relMap_toStructure`: Relation holding in the decoded structure
  corresponds to the code returning `true`.
- `StructureSpaceOn.toStructure_ofStructure`: Round-trip from structure to code to structure
  preserves relation satisfaction.
-/


-- @@ L35-35 verbatim
@[expose] public section


-- @@ L37-37 verbatim
universe u v


-- @@ L39-39 verbatim
namespace FirstOrder


-- @@ L41-41 verbatim
namespace Language


-- @@ L43-43 verbatim
open Structure


-- @@ L45-45 verbatim
variable (L : Language.{u, v})


-- @@ L47-49 verbatim
/-- A carrier-parametric relation query: a choice of relation symbol and a tuple
of elements from the carrier type α. -/
def RelQueryOn (α : Type*) := Σ (R : Σ l, L.Relations l), (Fin R.1 → α)


-- @@ L51-52 verbatim
/-- A relation query for carrier ℕ. -/
def RelQuery := RelQueryOn L ℕ


-- @@ L54-54 verbatim
variable {L}


-- @@ L56-58 verbatim
instance [Countable (Σ l, L.Relations l)] [Countable α] : Countable (RelQueryOn L α) := by
  unfold RelQueryOn
  infer_instance


-- @@ L60-62 verbatim
instance [Countable (Σ l, L.Relations l)] : Countable (RelQuery L) := by
  unfold RelQuery
  infer_instance


-- @@ L64-67 verbatim
/-- The carrier-parametric coding space for L-structures on α: for each relation
query, does the relation hold on that tuple? This is an `abbrev` so type class
resolution can see through it. -/
abbrev StructureSpaceOn (L : Language.{u, v}) (α : Type*) := RelQueryOn L α → Bool


-- @@ L69-71 verbatim
/-- The coding space for countable L-structures on ℕ: for each relation query,
does the relation hold on that tuple? -/
def StructureSpace (L : Language.{u, v}) := StructureSpaceOn L ℕ


-- @@ L73-73 verbatim
namespace StructureSpaceOn


-- @@ L75-75 verbatim
variable {α : Type*}


-- @@ L77-82 verbatim
/-- Decode a code into an L-structure on carrier α.
Relations are determined by the code; functions are eliminated by `IsRelational`. -/
@[reducible] noncomputable def toStructure [L.IsRelational]
    (c : StructureSpaceOn L α) : L.Structure α where
  funMap := fun f => isEmptyElim f
  RelMap := fun {_} R v => c ⟨⟨_, R⟩, v⟩ = true


-- @@ L84-89 verbatim
/-- The relation holding in the decoded structure corresponds to the code value. -/
@[simp]
theorem relMap_toStructure [L.IsRelational] (c : StructureSpaceOn L α)
    {l : ℕ} (R : L.Relations l) (v : Fin l → α) :
    @Structure.RelMap _ _ c.toStructure _ R v ↔ c ⟨⟨l, R⟩, v⟩ = true :=
  Iff.rfl


-- @@ L91-95 verbatim
/-- Encode an L-structure on carrier α into a code.
Takes an explicit structure instance rather than using the typeclass. -/
noncomputable def ofStructure [_isRelational : L.IsRelational]
    (inst : L.Structure α) : StructureSpaceOn L α :=
  fun ⟨⟨_, R⟩, v⟩ => @decide _ (Classical.dec (@Structure.RelMap _ _ inst _ R v))


-- @@ L97-102 verbatim
/-- Round-trip: decoding the code of a structure preserves relation satisfaction. -/
theorem toStructure_ofStructure [L.IsRelational]
    (inst : L.Structure α) {l : ℕ} (R : L.Relations l) (v : Fin l → α) :
    @Structure.RelMap _ _ (ofStructure inst).toStructure _ R v ↔
    @Structure.RelMap _ _ inst _ R v := by
  simp only [relMap_toStructure, ofStructure, decide_eq_true_eq]


-- @@ L104-106 verbatim
end StructureSpaceOn

-- ℕ-specialized wrappers for dot-notation on `StructureSpace`.

-- @@ L107-107 verbatim
namespace StructureSpace


-- @@ L109-112 verbatim
/-- Decode a code into an L-structure on ℕ. -/
@[reducible] noncomputable def toStructure [L.IsRelational]
    (c : StructureSpace L) : L.Structure ℕ :=
  StructureSpaceOn.toStructure c


-- @@ L114-119 verbatim
/-- The relation holding in the decoded structure corresponds to the code value. -/
@[simp]
theorem relMap_toStructure [L.IsRelational] (c : StructureSpace L)
    {l : ℕ} (R : L.Relations l) (v : Fin l → ℕ) :
    @Structure.RelMap _ _ c.toStructure _ R v ↔ c ⟨⟨l, R⟩, v⟩ = true :=
  Iff.rfl


-- @@ L121-124 verbatim
/-- Encode an L-structure on ℕ into a code. -/
noncomputable def ofStructure [L.IsRelational]
    (inst : L.Structure ℕ) : StructureSpace L :=
  StructureSpaceOn.ofStructure inst


-- @@ L126-131 verbatim
/-- Round-trip: decoding the code of a structure preserves relation satisfaction. -/
theorem toStructure_ofStructure [L.IsRelational]
    (inst : L.Structure ℕ) {l : ℕ} (R : L.Relations l) (v : Fin l → ℕ) :
    @Structure.RelMap _ _ (ofStructure inst).toStructure _ R v ↔
    @Structure.RelMap _ _ inst _ R v := by
  simp only [relMap_toStructure, ofStructure, StructureSpaceOn.ofStructure, decide_eq_true_eq]


-- @@ L133-133 verbatim
end StructureSpace


-- @@ L135-135 verbatim
end Language


-- @@ L137-137 verbatim
end FirstOrder
