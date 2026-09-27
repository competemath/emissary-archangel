/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import LeanPool.InfinitaryLogic.Scott.Height.Defs

-- @@ L9-27 verbatim
/-!
# Canonical Scott Sentence

The canonical Scott sentence of a structure M is the Scott formula at Scott
height level for the empty tuple. It is the "optimal" Scott sentence whose
quantifier rank is minimized among Scott formulas.

## Main Definitions

- `canonicalScottSentence`: The Scott formula at Scott height for the empty tuple.

## Main Results

- `canonicalScottSentence_iff_potentialIso`: Characterizes potential isomorphism.
- `canonicalScottSentence_characterizes`: For countable structures, characterizes isomorphism.
- `canonicalScottSentence_equiv_scottSentence`: Semantically equivalent to the standard
Scott sentence.
- `canonicalScottSentence_qrank`: Quantifier rank bounded by scottHeight + ω.
-/


-- @@ L29-29 verbatim
@[expose] public section


-- @@ L31-31 verbatim
universe u v w w'


-- @@ L33-33 verbatim
namespace FirstOrder


-- @@ L35-35 verbatim
namespace Language


-- @@ L37-37 verbatim
variable {L : Language.{u, v}} [L.IsRelational]

-- @@ L38-38 verbatim
variable [Countable (Σ l, L.Relations l)]


-- @@ L40-40 verbatim
open FirstOrder Structure Ordinal


-- @@ L42-50 verbatim
/-- The canonical Scott sentence of a structure M, defined as the Scott formula at Scott
height level for the empty tuple.

This is the "optimal" Scott sentence in the sense that its quantifier rank is minimized
(among Scott formulas). It characterizes the structure up to potential isomorphism,
and for countable structures, up to isomorphism. -/
noncomputable def canonicalScottSentence (M : Type w) [L.Structure M] [Countable M] :
    L.Formulaω (Fin 0) :=
  scottFormula (L := L) (M := M) Fin.elim0 (scottHeight (L := L) M)


-- @@ L52-52 verbatim
end Language


-- @@ L54-54 verbatim
end FirstOrder
