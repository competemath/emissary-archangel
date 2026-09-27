/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.FirstOrder.Basic.Eq
import LeanPool.Incompleteness.Foundation.FirstOrder.Basic.Model
import LeanPool.Incompleteness.Foundation.FirstOrder.Completeness.Completeness


-- @@ L12-12 verbatim
/-! # Le -/


-- @@ L14-14 verbatim
@[expose] public section



-- @@ L17-17 verbatim
namespace LO


-- @@ L19-19 verbatim
namespace FirstOrder


-- @@ L21-21 verbatim
variable {L : Language.{u}} [Semiformula.Operator.Eq L] [Semiformula.Operator.LT L]


-- @@ L23-23 verbatim
open Semiformula


-- @@ L25-27 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.LT.le :
    Operator L 2 := Semiformula.Operator.Eq.eq.or Semiformula.Operator.LT.lt


-- @@ L29-30 expanded
lemma le_eq (t₁ t₂ : Semiterm L μ n) :
    LT.le.operator ![t₁, t₂] =
      Vee.vee (Semiformula.Operator.operator Operator.Eq.eq ![t₁, t₂])
        (Semiformula.Operator.operator Operator.LT.lt ![t₁, t₂]) :=
  by simp [Operator.operator, Operator.or, LT.le, ← TransitiveRewriting.comp_app]


-- @@ L32-32 verbatim
namespace Order

-- @@ L33-33 expanded
variable {T : Theory L} [WeakerThan eqAxiom T]


-- @@ L35-39 expanded
omit [WeakerThan eqAxiom T] in
/-- Imported declaration from the Incompleteness formalization. -/
lemma leIffEqOrLt :
    Provable T
      (UnivQuantifier.univ
        (UnivQuantifier.univ
          (LogicalConnective.iff (Semiformula.Operator.operator Operator.LE.le ![#1, #0])
            (Vee.vee (Semiformula.Operator.operator Operator.Eq.eq ![#1, #0])
              (Semiformula.Operator.operator Operator.LT.lt ![#1, #0]))))) :=
  complete
    (consequence_iff.mpr <| fun _ _ _ _ => by
      simp [models_def, Semiformula.Operator.LE.def_of_Eq_of_LT])


-- @@ L41-51 expanded
lemma provOf (φ : SyntacticFormula L)
    (H :
      ∀ (M : Type (max u w)) [Nonempty M] [LT M] [Structure L M] [Structure.Eq L M]
        [Structure.LT L M] [ModelsTheory M T], Models M φ) :
    Consequence T φ :=
  consequence_iff_consequence.{u, w}.mp <|
    consequence_iff_eq.mpr fun M _ _ _ hT =>
      letI : ModelsTheory (Structure.Model L M) T :=
        ((Structure.ElementaryEquiv.modelsTheory (Structure.Model.elementaryEquiv L M)).mp hT)
      (Structure.ElementaryEquiv.models (Structure.Model.elementaryEquiv L M)).mpr
        (H (Structure.Model L M))


-- @@ L53-53 verbatim
end Order


-- @@ L55-55 verbatim
end FirstOrder


-- @@ L57-57 verbatim
end LO
