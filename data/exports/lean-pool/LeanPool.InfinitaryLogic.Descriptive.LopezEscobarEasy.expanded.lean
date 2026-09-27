/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import LeanPool.InfinitaryLogic.Descriptive.SatisfactionBorel
import LeanPool.InfinitaryLogic.Lomega1omega.Theory
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.EReal.Inv
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

-- @@ L14-31 verbatim
/-!
# López-Escobar, the easy direction

For arbitrary relational vocabularies the model class of an `L_ω₁ω`-sentence is
PRODUCT-MEASURABLE and ISOMORPHISM-INVARIANT (`modelsOf_measurable_invariant`); for countable
relational vocabularies — where the repository's `BorelSpace`/`StandardBorelSpace
(StructureSpace L)` instances apply — this is an invariant BOREL subset of the standard Borel
structure space (`lopezEscobar_easy`, the literature statement).

Invariance is the named isomorphism-closed predicate `IsomorphismInvariant` (an
`L`-isomorphism of the decoded structures transports membership) — equivalent to invariance
under the logic action (`actionInvariant_iff_isomorphismInvariant`, `Descriptive/LogicAction.lean`).

The hard converse — every isomorphism-invariant Borel class is `L_ω₁ω`-definable, by Marker's
route through Craig interpolation and PC-separation — is **proved**: `lopez_escobar`
(`Methods/LopezEscobar/Separation.lean`), packaged with this direction as `lopezEscobar_iff`
in `Descriptive/LopezEscobar.lean`.
-/


-- @@ L33-33 verbatim
@[expose] public section


-- @@ L35-35 verbatim
namespace FirstOrder


-- @@ L37-37 verbatim
namespace Language


-- @@ L39-39 verbatim
variable {L : Language.{u, v}} [L.IsRelational]


-- @@ L41-45 verbatim
/-- **Isomorphism invariance** of a class of coded structures, in isomorphism-closed form: an
`L`-isomorphism of the decoded structures transports membership. -/
def IsomorphismInvariant (B : Set (StructureSpace L)) : Prop :=
  ∀ c d : StructureSpace L,
    Nonempty (@Language.Equiv L ℕ ℕ c.toStructure d.toStructure) → (c ∈ B ↔ d ∈ B)


-- @@ L47-58 verbatim
/-- Membership in a sentence's model class is isomorphism-invariant: an `L`-isomorphism of the
decoded structures transports satisfaction. -/
private theorem modelsOf_mem_iff_of_equiv (φ : L.Sentenceω) {c d : StructureSpace L}
    (e : @Language.Equiv L ℕ ℕ c.toStructure d.toStructure) :
    c ∈ ModelsOf φ ↔ d ∈ ModelsOf φ := by
  let : L.Structure ℕ := c.toStructure
  change @BoundedFormulaω.Realize L ℕ c.toStructure Empty 0 φ Empty.elim Fin.elim0
    ↔ @BoundedFormulaω.Realize L ℕ d.toStructure Empty 0 φ Empty.elim Fin.elim0
  have h := @BoundedFormulaω.realize_equiv L ℕ ℕ c.toStructure d.toStructure e Empty 0 φ
    Empty.elim Fin.elim0
  rwa [show (⇑e ∘ Empty.elim : Empty → ℕ) = Empty.elim from funext fun x => x.elim,
    show (⇑e ∘ Fin.elim0 : Fin 0 → ℕ) = Fin.elim0 from funext fun i => i.elim0] at h


-- @@ L60-62 verbatim
private theorem isomorphismInvariant_modelsOf (φ : L.Sentenceω) :
    IsomorphismInvariant (ModelsOf φ) :=
  fun _ _ ⟨e⟩ => modelsOf_mem_iff_of_equiv φ e


-- @@ L64-68 verbatim
/-- **The general form** (arbitrary relational vocabularies): the model class of a sentence is
product-measurable and isomorphism-invariant. -/
private theorem modelsOf_measurable_invariant (φ : L.Sentenceω) :
    MeasurableSet (ModelsOf φ) ∧ IsomorphismInvariant (ModelsOf φ) :=
  ⟨modelsOf_measurableSet φ, isomorphismInvariant_modelsOf φ⟩


-- @@ L70-76 verbatim
/-- **López-Escobar, easy direction**: every `L_ω₁ω`-sentence defines a product-measurable,
isomorphism-invariant class of coded countable structures. For countable relational vocabularies,
this is a Borel class for the Polish topology. The converse is `lopez_escobar`; the two directions
are packaged as `lopezEscobar_iff`. -/
theorem lopezEscobar_easy (φ : L.Sentenceω) :
    MeasurableSet (ModelsOf φ) ∧ IsomorphismInvariant (ModelsOf φ) :=
  modelsOf_measurable_invariant φ


-- @@ L78-78 verbatim
end Language


-- @@ L80-80 verbatim
end FirstOrder
