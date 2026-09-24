import Clean.Circuit.Loops
import Clean.Gadgets.Xor.Xor64
import Clean.Gadgets.Keccak.KeccakState
import Clean.Specs.Keccak256


-- @@ L6-6 verbatim
namespace Gadgets.Keccak256.ThetaXor

-- @@ L7-7 verbatim
variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]


-- @@ L9-12 verbatim
structure Inputs (F : Type) where
  state : KeccakState F
  d : KeccakRow F
deriving ProvableStruct


-- @@ L14-16 verbatim
def main (inputs : Var Inputs (F p)) : Circuit (F p) (Var KeccakState (F p)) :=
  .mapFinRange 25 fun i =>
    Xor64.circuit ⟨inputs.state[i.val], inputs.d[i.val / 5]⟩


-- @@ L18-19 verbatim
@[reducible] instance elaborated : ElaboratedCircuit (F p) Inputs KeccakState main := by
  elaborate_circuit


-- @@ L21-23 verbatim
def Assumptions (inputs : Inputs (F p)) : Prop :=
  let ⟨state, d⟩ := inputs
  state.Normalized ∧ d.Normalized


-- @@ L25-33 verbatim
def Spec (inputs : Inputs (F p)) (out : KeccakState (F p)) : Prop :=
  let ⟨state, d⟩ := inputs
  out.Normalized
  ∧ out.value = Specs.Keccak256.thetaXor state.value d.value

-- rewrite thetaXor as a loop
lemma thetaXor_loop (state : Vector ℕ 25) (d : Vector ℕ 5) :
    Specs.Keccak256.thetaXor state d = .mapFinRange 25 fun i => state[i.val] ^^^ d[i.val / 5] := by
  simp [Specs.Keccak256.thetaXor, circuit_norm, Vector.mapFinRange_succ, Vector.mapFinRange_zero]


-- @@ L35-50 verbatim
theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [Xor64.circuit, Xor64.Assumptions, Xor64.Spec]
  obtain ⟨state_norm, d_norm⟩ := h_assumptions

  -- rewrite goal
  apply KeccakState.normalized_value_ext
  simp only [circuit_norm, thetaXor_loop, eval_vector, KeccakState.value, KeccakRow.value]

  -- simplify constraints
  simp only [circuit_norm, eval_vector, Vector.ext_iff] at h_input
  simp only [circuit_norm, h_input] at h_holds

  -- use assumptions, prove goal
  intro i
  specialize h_holds i ⟨ state_norm i, d_norm ⟨i.val / 5, by omega⟩ ⟩
  exact ⟨ h_holds.right, h_holds.left ⟩


-- @@ L52-57 verbatim
theorem completeness : Completeness (F p) main Assumptions := by
  intro i0 env ⟨state_var, d_var⟩ h_env ⟨state, d⟩ h_input ⟨state_norm, d_norm⟩
  simp only [circuit_norm, eval_vector, Inputs.mk.injEq, Vector.ext_iff] at h_input
  simp only [h_input, main, circuit_norm, Xor64.circuit, Xor64.Assumptions]
  intro i
  exact ⟨ state_norm i, d_norm ⟨i.val / 5, by omega⟩ ⟩


-- @@ L59-65 verbatim
def circuit : FormalCircuit (F p) Inputs KeccakState where
  main := main
  elaborated := elaborated
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness


-- @@ L67-67 verbatim
end Gadgets.Keccak256.ThetaXor
