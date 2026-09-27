/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import LeanPool.InfinitaryLogic.Lomega1omega.Semantics
public import LeanPool.InfinitaryLogic.Mathlib.ModelTheory.Infinitary.Reindex

-- @@ L10-31 verbatim
/-!
# Countable connectives over arbitrary countable index types

`BoundedFormulaω`'s `iInf`/`iSup` branch over the fixed carrier `ℕ`. Constructions like the
Hanf beth ladder (clause families over pairs of countable ordinals) and countable fragments
quantify over countable-but-not-`ℕ` index types. This file provides the conjunction and
disjunction over any such index, as thin wrappers around the carrier-transport
primitives `BoundedFormulaInf.iInfAlong`/`iSupAlong`.

**The index may live in any universe**, since `ι` is encoded into `ℕ` rather than enumerated
from it. This is what lets a consumer such as `ModelTheory/TypeIsolation.lean` — whose index
is a subtype of realized types, landing in `Type (max u v)` — be universe-polymorphic.

Both definitions are noncomputable: `Encodable.ofCountable` upgrades `[Countable ι]` to an
encoding by choice. Padding handles the empty index uniformly, an empty `ι` padding every
branch, so no case split is needed and each realization lemma is the upstream one applied
directly.

Only the realization lemmas are provided. No syntactic naturality API is built here: the
encoding is noncanonical, so definitional commutation statements would be unpleasant —
consumers should work through `realize_ciInf`/`realize_ciSup`.
-/


-- @@ L33-33 verbatim
@[expose] public section


-- @@ L35-35 verbatim
namespace FirstOrder


-- @@ L37-37 verbatim
namespace Language


-- @@ L39-39 verbatim
namespace BoundedFormulaω


-- @@ L41-41 verbatim
universe uι


-- @@ L43-43 verbatim
variable {L : Language.{u, v}} {γ : Type u'} {n : ℕ}


-- @@ L45-52 verbatim
/-- **Countable conjunction over a countable index type**, at any index universe.

The index is encoded into the fixed `ℕ` carrier by an `IndexCoding`, and branches outside the
image are padded with `⊤`. Padding is what makes the empty carrier need no special handling:
an empty `ι` pads every branch, and the conjunction is vacuously true. -/
noncomputable def ciInf {ι : Type uι} [Countable ι] (φs : ι → L.BoundedFormulaω γ n) :
    L.BoundedFormulaω γ n :=
  BoundedFormulaInf.iInfAlong (.ofEncodableWith (Encodable.ofCountable ι)) φs


-- @@ L54-58 verbatim
/-- **Countable disjunction over a countable index type**, at any index universe. Dual to
`ciInf`; undecodable branches are padded with `⊥`, so an empty `ι` is vacuously false. -/
noncomputable def ciSup {ι : Type uι} [Countable ι] (φs : ι → L.BoundedFormulaω γ n) :
    L.BoundedFormulaω γ n :=
  BoundedFormulaInf.iSupAlong (.ofEncodableWith (Encodable.ofCountable ι)) φs


-- @@ L60-60 verbatim
variable {M : Type w} [L.Structure M]


-- @@ L62-65 verbatim
theorem realize_ciInf {ι : Type uι} [Countable ι] (φs : ι → L.BoundedFormulaω γ n)
    (v : γ → M) (xs : Fin n → M) :
    (ciInf φs).Realize v xs ↔ ∀ i, (φs i).Realize v xs :=
  BoundedFormulaInf.realize_iInfAlong


-- @@ L67-70 verbatim
theorem realize_ciSup {ι : Type uι} [Countable ι] (φs : ι → L.BoundedFormulaω γ n)
    (v : γ → M) (xs : Fin n → M) :
    (ciSup φs).Realize v xs ↔ ∃ i, (φs i).Realize v xs :=
  BoundedFormulaInf.realize_iSupAlong


-- @@ L72-72 verbatim
end BoundedFormulaω


-- @@ L74-74 verbatim
end Language


-- @@ L76-76 verbatim
end FirstOrder
