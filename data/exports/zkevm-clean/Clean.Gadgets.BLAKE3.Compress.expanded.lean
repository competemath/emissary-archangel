import Clean.Gadgets.BLAKE3.ApplyRounds
import Clean.Gadgets.BLAKE3.FinalStateUpdate
import Clean.Specs.BLAKE3
import Clean.Circuit.Provable
import Clean.Utils.Tactics


-- @@ L7-7 verbatim
namespace Gadgets.BLAKE3.Compress

-- @@ L8-8 verbatim
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 2^16 + 2^8)]

-- @@ L9-9 verbatim
instance : Fact (p > 512) := .mk (by linarith [p_large_enough.elim])


-- @@ L11-11 verbatim
open Specs.BLAKE3 (compress)


-- @@ L13-20 verbatim
/--
Main circuit that chains ApplyRounds and FinalStateUpdate.
-/
def main (input : Var ApplyRounds.Inputs (F p)) : Circuit (F p) (Var BLAKE3State (F p)) := do
  -- First apply the 7 rounds
  let state ← ApplyRounds.circuit input
  -- Then apply final state update
  FinalStateUpdate.circuit ⟨state, input.chaining_value⟩


-- @@ L22-23 verbatim
instance elaborated : ElaboratedCircuit (F p) ApplyRounds.Inputs BLAKE3State main := by
  elaborate_circuit


-- @@ L25-26 verbatim
def Assumptions (input : ApplyRounds.Inputs (F p)) : Prop :=
  ApplyRounds.Assumptions input


-- @@ L28-36 verbatim
def Spec (input : ApplyRounds.Inputs (F p)) (output : BLAKE3State (F p)) : Prop :=
  let { chaining_value, block_words, counter_high, counter_low, block_len, flags } := input
  output.value = compress
    (chaining_value.map U32.value)
    (block_words.map U32.value)
    (counter_low.value + 2^32 * counter_high.value)
    block_len.value
    flags.value ∧
  output.Normalized


-- @@ L38-41 verbatim
theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_all [circuit_norm, ApplyRounds.circuit,
    ApplyRounds.Spec, FinalStateUpdate.circuit, FinalStateUpdate.Assumptions, compress,
    ApplyRounds.Assumptions, FinalStateUpdate.Spec]


-- @@ L43-46 verbatim
theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_all [ApplyRounds.circuit,
    ApplyRounds.Spec, FinalStateUpdate.circuit, FinalStateUpdate.Assumptions,
    ApplyRounds.Assumptions, FinalStateUpdate.Spec]


-- @@ L48-50 verbatim
def circuit : FormalCircuit (F p) ApplyRounds.Inputs BLAKE3State := {
  main, Assumptions, Spec, soundness, completeness
}


-- @@ L52-52 verbatim
end Gadgets.BLAKE3.Compress
