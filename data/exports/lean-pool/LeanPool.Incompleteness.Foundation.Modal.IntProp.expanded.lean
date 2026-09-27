/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.IntProp.Formula
public import LeanPool.Incompleteness.Foundation.Modal.Formula


-- @@ L11-11 verbatim
/-! # IntProp -/


-- @@ L13-13 verbatim
@[expose] public section



-- @@ L16-16 verbatim
namespace LO

-- @@ L17-17 verbatim
namespace IntProp


-- @@ L19-25 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.IntProp.Formula.toModalFormula : Formula α → Modal.Formula α
  | .atom a => Modal.Formula.atom a
  | ⊥ => ⊥
  | Arrow.arrow φ ψ => Arrow.arrow (toModalFormula φ) (toModalFormula ψ)
  | Wedge.wedge φ ψ => Wedge.wedge (toModalFormula φ) (toModalFormula ψ)
  | Vee.vee φ ψ => Vee.vee (toModalFormula φ) (toModalFormula ψ)


-- @@ L26-27 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
postfix:75 "ᴹ" => Formula.toModalFormula


-- @@ L29-29 verbatim
namespace Formula

-- @@ L30-30 verbatim
namespace toModalFormula


-- @@ L32-32 expanded
@[simp]
lemma def_top : Formula.toModalFormula (⊤ : Formula α) = ⊤ := by rfl


-- @@ L34-34 expanded
@[simp]
lemma def_bot : Formula.toModalFormula (⊥ : Formula α) = ⊥ := by rfl


-- @@ L36-36 expanded
@[simp]
lemma def_atom (a : α) : Formula.toModalFormula (atom a) = .atom a := by rfl


-- @@ L38-38 expanded
@[simp]
lemma def_not (φ : Formula α) :
    Formula.toModalFormula (Tilde.tilde φ) = Tilde.tilde (Formula.toModalFormula φ) := by rfl


-- @@ L40-40 expanded
@[simp]
lemma def_imp (φ ψ : Formula α) :
    Formula.toModalFormula (Arrow.arrow φ ψ) =
      Arrow.arrow (Formula.toModalFormula φ) (Formula.toModalFormula ψ) :=
  by rfl


-- @@ L42-42 expanded
@[simp]
lemma def_and (φ ψ : Formula α) :
    Formula.toModalFormula (Wedge.wedge φ ψ) =
      Wedge.wedge (Formula.toModalFormula φ) (Formula.toModalFormula ψ) :=
  by rfl


-- @@ L44-44 expanded
@[simp]
lemma def_or (φ ψ : Formula α) :
    Formula.toModalFormula (Vee.vee φ ψ) =
      Vee.vee (Formula.toModalFormula φ) (Formula.toModalFormula ψ) :=
  by rfl


-- @@ L46-46 verbatim
end toModalFormula

-- @@ L47-47 verbatim
end Formula


-- @@ L49-49 verbatim
end IntProp

-- @@ L50-50 verbatim
end LO



-- @@ L53-53 verbatim
namespace LO

-- @@ L54-54 verbatim
namespace Modal


-- @@ L56-63 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Modal.Formula.toPropFormula (φ : Formula α)
    (_ : φ.degree = 0 := by simp_all [Formula.degree, Formula.degree_neg, Formula.degree_imp]) :
    IntProp.Formula α :=
  match φ with
  | .atom a => IntProp.Formula.atom a
  | ⊥ => ⊥
  | Arrow.arrow φ ψ => Arrow.arrow φ.toPropFormula ψ.toPropFormula


-- @@ L64-65 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
postfix:75 "ᴾ" => Formula.toPropFormula


-- @@ L67-67 verbatim
end Modal

-- @@ L68-68 verbatim
end LO
