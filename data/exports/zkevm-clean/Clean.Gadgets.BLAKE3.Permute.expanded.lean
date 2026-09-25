import Clean.Gadgets.BLAKE3.BLAKE3State
import Clean.Circuit


-- @@ L4-4 verbatim
namespace Gadgets.BLAKE3.Permute

-- @@ L5-5 verbatim
variable {p : ℕ} [Fact p.Prime]


-- @@ L7-7 verbatim
open Specs.BLAKE3 (msgPermutation permute)


-- @@ L9-10 verbatim
def main (state : Var BLAKE3State (F p)) : Circuit (F p) (Var BLAKE3State (F p)) := do
  return Vector.ofFn (fun i => state[msgPermutation[i]])


-- @@ L12-13 verbatim
@[reducible] instance elaborated: ElaboratedCircuit (F p) BLAKE3State BLAKE3State main := by
  elaborate_circuit


-- @@ L15-15 verbatim
def Assumptions (state : BLAKE3State (F p)) := state.Normalized


-- @@ L17-18 verbatim
def Spec (state : BLAKE3State (F p)) (out : BLAKE3State (F p)) :=
  out.value = permute state.value ∧ out.Normalized


-- @@ L20-34 verbatim
theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start
  simp only [BLAKE3State.value, Vector.map, ↓Fin.getElem_fin,
    eval_vector, Vector.toArray_ofFn, Array.map_map, permute, Vector.getElem_mk, Array.getElem_map,
    ↓Vector.getElem_toArray, Vector.mk_eq]
  constructor
  · ext i hi
    · simp only [Array.size_map, Array.size_ofFn]
    simp only [Array.getElem_map, Array.getElem_ofFn]
    rw [Function.comp_apply, getElem_eval_vector, h_input]
  · simp [BLAKE3State.Normalized]
    intro i
    rw [getElem_eval_vector, h_input]
    simp only [BLAKE3State.Normalized] at h_assumptions
    fin_cases i <;> simp only [msgPermutation, h_assumptions]


-- @@ L36-37 verbatim
theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_all


-- @@ L39-40 verbatim
def circuit : FormalCircuit (F p) BLAKE3State BLAKE3State :=
  { main, elaborated, Assumptions, Spec, soundness, completeness }


-- @@ L42-42 verbatim
end Gadgets.BLAKE3.Permute
