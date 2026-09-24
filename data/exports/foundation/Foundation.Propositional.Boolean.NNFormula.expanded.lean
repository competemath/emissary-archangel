module

public import Foundation.Propositional.Boolean.Basic
public import Foundation.Propositional.Formula.NNFormula


-- @@ L6-6 verbatim
@[expose] public section


-- @@ L8-8 verbatim
namespace FFL.Propositional


-- @@ L10-10 verbatim
variable {α : Type*}


-- @@ L12-12 verbatim
open Boolean (Valuation)



-- @@ L15-15 verbatim
namespace NNFormula


-- @@ L17-17 verbatim
section val


-- @@ L19-20 verbatim
variable {F : Type*} [LogicalConnective F] [LogicalNeutral F]
  [TildeInvolutive F] [LogicalNeutral.DeMorgan F] [LogicalConnective.DeMorgan F] (v : α → F)


-- @@ L22-32 verbatim
def valAux : NNFormula α → F
  | .atom a  => v a
  | .natom a => ∼v a
  | ⊤       => ⊤
  | ⊥       => ⊥
  | φ ⋏ ψ   => φ.valAux ⋏ ψ.valAux
  | φ ⋎ ψ   => φ.valAux ⋎ ψ.valAux

lemma valAux_neg (φ : NNFormula α) :
    valAux v (∼φ) = ∼(valAux v φ) :=
  by induction φ using rec' <;> simp [*, valAux]


-- @@ L34-41 verbatim
def val : NNFormula α →ˡᶜ F where
  toTr := valAux v
  map_top' := rfl
  map_bot' := rfl
  map_and' := fun _ _ => rfl
  map_or' := fun _ _ => rfl
  map_imply' := fun _ _ => by simp [LogicalConnective.DeMorgan.imply, valAux, ←neg_eq, valAux_neg]
  map_neg' := fun _ => by simp [valAux_neg]


-- @@ L43-43 verbatim
@[simp] lemma val_atom : val v (atom a) = v a := rfl


-- @@ L45-45 verbatim
@[simp] lemma val_natom : val v (natom a) = ∼v a := rfl


-- @@ L47-47 verbatim
end val



-- @@ L50-50 verbatim
section semantics


-- @@ L52-56 verbatim
variable {v : Valuation α}

-- `Valuation α` is also the model type of `Formula.Boolean.semantics` and the formula parameter of
-- `Semantics` is an `outParam`, so an explicit priority is needed to pin down which of the two
-- instances a valuation resolves to.

-- @@ L57-59 verbatim
instance (priority := high) semantics : Semantics (Valuation α) (NNFormula α) := ⟨fun v ↦ NNFormula.val v⟩

lemma models_iff_val {v : Valuation α} {f : NNFormula α} : v ⊧ f ↔ NNFormula.val v f := iff_of_eq rfl


-- @@ L61-67 verbatim
instance : Semantics.Tarski (Valuation α) where
  models_verum := by simp [models_iff_val]
  models_falsum := by simp [models_iff_val]
  models_and := by simp [models_iff_val]
  models_or := by simp [models_iff_val]
  models_not := by simp [models_iff_val]
  models_imply := by simp [models_iff_val]


-- @@ L69-69 verbatim
@[simp] protected lemma models_atom : v ⊧ .atom a ↔ v a := iff_of_eq rfl


-- @@ L71-71 verbatim
@[simp] protected lemma models_natom : v ⊧ .natom a ↔ ¬v a := iff_of_eq rfl


-- @@ L73-73 verbatim
end semantics


-- @@ L75-75 verbatim
end NNFormula



-- @@ L78-78 verbatim
end FFL.Propositional

-- @@ L79-79 verbatim
end
