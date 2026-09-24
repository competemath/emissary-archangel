import Clean.Circuit.Provable
import Clean.Circuit.Subcircuit
import Clean.Gadgets.Boolean
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving


-- @@ L7-7 verbatim
namespace Gadgets.Conditional


-- @@ L9-9 verbatim
section

-- @@ L10-10 verbatim
variable {F : Type} [FiniteField F]

-- @@ L11-11 verbatim
variable {M : TypeMap} [ProvableType M]


-- @@ L13-21 verbatim
/--
Inputs for conditional selection between two ProvableTypes.
Contains a selector bit and two data values.
-/
structure Inputs (M : TypeMap) (F : Type) where
  selector : F
  ifTrue : M F
  ifFalse : M F
deriving ProvableStruct


-- @@ L23-31 verbatim
def main [DecidableEq F] (input : Var (Inputs M) F) : Circuit F (Var M F) := do
  let { selector, ifTrue, ifFalse } := input

  -- Inline element-wise scalar multiplication / addition
  let trueVars := toElements ifTrue
  let falseVars := toElements ifFalse
  let resultVars := Vector.ofFn fun i => selector * (trueVars[i] - falseVars[i]) + falseVars[i]

  return fromElements (M:=M) resultVars


-- @@ L33-38 verbatim
def output (selector: Expression F) (ifTrue ifFalse : Var M F) : Var M F :=
  -- Inline element-wise scalar multiplication / addition
  let trueVars := toElements (M:=M) ifTrue
  let falseVars := toElements (M:=M) ifFalse
  let resultVars := Vector.ofFn fun i => selector * (trueVars[i] - falseVars[i]) + falseVars[i]
  fromElements (M:=M) resultVars


-- @@ L40-45 verbatim
def outputValue (selector: F) (ifTrue ifFalse : M F) : M F :=
  -- Inline element-wise scalar multiplication / addition
  let trueElems := toElements ifTrue
  let falseElems := toElements ifFalse
  let resultElems := Vector.ofFn fun i => selector * (trueElems[i] - falseElems[i]) + falseElems[i]
  fromElements resultElems


-- @@ L47-49 verbatim
@[circuit_norm]
def Assumptions (input : Inputs M F) : Prop :=
  IsBool input.selector


-- @@ L51-56 verbatim
/--
Specification: Output is selected based on selector value using if-then-else.
-/
@[circuit_norm]
def Spec [DecidableEq F] (input : Inputs M F) (output : M F) : Prop :=
  output = if input.selector = 1 then input.ifTrue else input.ifFalse


-- @@ L58-59 verbatim
instance elaborated [DecidableEq F] : ElaboratedCircuit F (Inputs M) M main := by
  elaborate_circuit


-- @@ L61-83 verbatim
theorem soundness [DecidableEq F] : Soundness F (Input := Inputs M) main Assumptions Spec := by
  circuit_proof_start
  rcases h_input with ⟨h_selector, h_ifTrue, h_ifFalse⟩

  -- Show that the result equals the conditional expression
  rw [ProvableType.ext_iff]
  intro i hi
  rw [ProvableType.eval_fromElements]
  rw [ProvableType.toElements_fromElements, Vector.getElem_map, Vector.getElem_ofFn]
  simp only [circuit_norm, ProvableType.getElem_eval_toElements, h_selector, h_ifTrue, h_ifFalse]

  -- Case split on the selector value
  cases h_assumptions with
  | inl h_zero =>
    simp only [h_zero]
    have : (0 : F) = 1 ↔ False := by simp
    simp only [this, if_false]
    ring_nf
  | inr h_one =>
    simp only [h_one]
    have : (1 : F) = 1 ↔ True := by simp
    simp only [if_true]
    ring_nf


-- @@ L85-86 verbatim
theorem completeness [DecidableEq F] : Completeness F (Input := Inputs M) main Assumptions := by
  circuit_proof_start


-- @@ L88-98 verbatim
/--
Conditional selection. Computes: selector * ifTrue + (1 - selector) * ifFalse
-/
@[circuit_norm]
def circuit [DecidableEq F] : FormalCircuit F (Inputs M) M where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness


-- @@ L100-106 verbatim
/--
Conditional selection.
-/
@[circuit_norm]
def ifElse [DecidableEq F] {M : TypeMap} [ProvableType M]
  (selector : Expression F) (ifTrue ifFalse : M (Expression F)) : Circuit F (M (Expression F)) :=
  circuit { selector, ifTrue, ifFalse }


-- @@ L108-122 verbatim
/--
  Lemma to simplify the evaluated output
-/
@[circuit_norm]
theorem eval_ifElse_output {M : TypeMap} [ProvableType M] {env}
  (selector : Expression F) (ifTrue ifFalse : M (Expression F)) :
  eval env (output selector ifTrue ifFalse) =
    outputValue (selector.eval env) (eval env ifTrue) (eval env ifFalse) := by
  simp only [output, outputValue, circuit_norm]

  -- Show that the result equals the conditional expression
  rw [ProvableType.ext_iff]
  intro i hi
  rw [ProvableType.eval_fromElements]
  simp only [circuit_norm, Vector.getElem_map, Vector.getElem_ofFn, ProvableType.getElem_eval_toElements]

-- @@ L123-123 verbatim
end


-- @@ L125-125 verbatim
end Gadgets.Conditional


-- @@ L127-127 verbatim
export Gadgets.Conditional (ifElse)
