/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.FirstOrder.Basic.Eq
import LeanPool.Incompleteness.Foundation.FirstOrder.Basic.Model
import LeanPool.Incompleteness.Foundation.FirstOrder.Basic.Soundness
import LeanPool.Incompleteness.Foundation.FirstOrder.Completeness.Completeness


-- @@ L13-13 verbatim
/-! # Corollaries -/


-- @@ L15-15 verbatim
@[expose] public section



-- @@ L18-18 verbatim
namespace LO

-- @@ L19-19 verbatim
namespace FirstOrder


-- @@ L21-21 verbatim
namespace ModelsTheory


-- @@ L23-23 verbatim
variable {L : Language.{u}} (M : Type w) [Nonempty M] [Structure L M] (T U V : Theory L)


-- @@ L25-28 expanded
lemma of_provably_subtheory [WeakerThan T U] (h : ModelsTheory M U) : ModelsTheory M T :=
  ⟨by
    intro φ hp
    have : Provable U φ := (inferInstance : WeakerThan T U).pbl (Entailment.by_axm _ hp)
    exact consequence_iff'.{u, w}.mp (sound! this) M⟩


-- @@ L30-31 expanded
lemma of_provably_subtheory' [WeakerThan T U] [ModelsTheory M U] : ModelsTheory M T :=
  of_provably_subtheory M T U inferInstance


-- @@ L33-34 expanded
lemma of_add_left [ModelsTheory M (T + U)] : ModelsTheory M T :=
  of_ss inferInstance (show T ⊆ T + U from by simp [Theory.add_def])


-- @@ L36-37 expanded
lemma of_add_right [ModelsTheory M (T + U)] : ModelsTheory M U :=
  of_ss inferInstance (show U ⊆ T + U from by simp [Theory.add_def])


-- @@ L39-40 expanded
lemma of_add_left_left [ModelsTheory M (T + U + V)] : ModelsTheory M T :=
  @of_add_left _ M _ _ T U (of_add_left M (T + U) V)


-- @@ L42-43 expanded
lemma of_add_left_right [ModelsTheory M (T + U + V)] : ModelsTheory M U :=
  @of_add_right _ M _ _ T U (of_add_left M (T + U) V)


-- @@ L45-45 verbatim
end ModelsTheory


-- @@ L47-47 expanded
variable {L : Language.{u}} [L.Eq] {T : Theory L} [WeakerThan eqAxiom T]


-- @@ L49-59 expanded
lemma _root_.LO.FirstOrder.EQ.provOf (φ : SyntacticFormula L)
    (H :
      ∀ (M : Type (max u w)) [Nonempty M] [Structure L M] [Structure.Eq L M] [ModelsTheory M T],
        Models M φ) :
    Consequence T φ :=
  consequence_iff_consequence.{u, w}.mp <|
    consequence_iff_eq.mpr fun M _ _ _ hT =>
      letI : ModelsTheory (Structure.Model L M) T :=
        ((Structure.ElementaryEquiv.modelsTheory (Structure.Model.elementaryEquiv L M)).mp hT)
      (Structure.ElementaryEquiv.models (Structure.Model.elementaryEquiv L M)).mpr
        (H (Structure.Model L M))


-- @@ L61-61 verbatim
end FirstOrder

-- @@ L62-62 verbatim
end LO
