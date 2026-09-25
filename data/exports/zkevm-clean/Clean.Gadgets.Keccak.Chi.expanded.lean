import Clean.Types.U64
import Clean.Circuit.Loops
import Clean.Gadgets.Xor.Xor64
import Clean.Gadgets.And.And64
import Clean.Gadgets.Not.Not64
import Clean.Gadgets.Keccak.KeccakState
import Clean.Specs.Keccak256


-- @@ L9-9 verbatim
namespace Gadgets.Keccak256.Chi

-- @@ L10-10 verbatim
variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

-- @@ L11-11 verbatim
open Gadgets.Not (not64_bytewise not64_bytewise_value)


-- @@ L13-17 verbatim
def main (state : Var KeccakState (F p)) : Circuit (F p) (Var KeccakState (F p)) :=
  .mapFinRange 25 fun i => do
    let state_not ← Not.circuit (state[i + 5])
    let state_and ← And.And64.circuit ⟨state_not, state[i + 10]⟩
    Xor64.circuit ⟨state[i], state_and⟩


-- @@ L19-19 verbatim
def Assumptions := KeccakState.Normalized (p:=p)


-- @@ L21-23 verbatim
def Spec (state : KeccakState (F p)) (out_state : KeccakState (F p)) :=
  out_state.Normalized
  ∧ out_state.value = Specs.Keccak256.chi state.value


-- @@ L25-28 verbatim
@[reducible] instance elaborated : ElaboratedCircuit (F p) KeccakState KeccakState main := by
  elaborate_circuit

-- rewrite the chi spec as a loop

-- @@ L29-32 verbatim
lemma chi_loop (state : Vector ℕ 25) :
    Specs.Keccak256.chi state = .mapFinRange 25 fun i => state[i] ^^^ ((not64 state[i + 5]) &&& state[i + 10]) := by
  rw [Specs.Keccak256.chi, Vector.mapFinRange, Vector.finRange, Vector.map_mk, Vector.eq_mk, List.map_toArray]
  rfl


-- @@ L34-46 verbatim
theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [ Xor64.circuit, And.And64.circuit, And.And8.circuit, Not.circuit,
    Xor64.Assumptions, Xor64.Spec, And.And64.Assumptions, And.And64.Spec]

  -- simplify goal
  apply KeccakState.normalized_value_ext
  simp only [circuit_norm, chi_loop, eval_vector, KeccakState.value]

  -- simplify constraints
  simp only [circuit_norm, eval_vector, Vector.ext_iff] at h_input
  simp only [KeccakState.Normalized] at h_assumptions

  simp_all


-- @@ L48-53 verbatim
theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [Xor64.circuit, And.And64.circuit, And.And8.circuit, Not.circuit,
    Xor64.Assumptions, Xor64.Spec, And.And64.Assumptions, And.And64.Spec,
    KeccakState.Normalized]
  simp only [circuit_norm, eval_vector, Vector.ext_iff] at h_input
  simp_all


-- @@ L55-61 verbatim
def circuit : FormalCircuit (F p) KeccakState KeccakState where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness

-- @@ L62-62 verbatim
end Gadgets.Keccak256.Chi
