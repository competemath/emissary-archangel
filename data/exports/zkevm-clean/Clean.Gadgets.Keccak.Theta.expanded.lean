import Clean.Specs.Keccak256
import Clean.Gadgets.Keccak.ThetaC
import Clean.Gadgets.Keccak.ThetaD
import Clean.Gadgets.Keccak.ThetaXor


-- @@ L6-6 verbatim
namespace Gadgets.Keccak256.Theta

-- @@ L7-7 verbatim
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 2^16 + 2^8)]


-- @@ L9-9 verbatim
instance : Fact (p > 512) := .mk (by linarith [p_large_enough.elim])


-- @@ L11-14 verbatim
def main (state : Var KeccakState (F p)) : Circuit (F p) (Var KeccakState (F p)) := do
  let c ← ThetaC.circuit state
  let d ← ThetaD.circuit c
  ThetaXor.circuit ⟨state, d⟩


-- @@ L16-17 verbatim
@[reducible] instance elaborated : ElaboratedCircuit (F p) KeccakState KeccakState main := by
  elaborate_circuit


-- @@ L19-19 verbatim
def Assumptions (state : KeccakState (F p)) := state.Normalized


-- @@ L21-23 verbatim
def Spec (state : KeccakState (F p)) (out_state : KeccakState (F p)) : Prop :=
  out_state.Normalized
  ∧ out_state.value = Specs.Keccak256.theta state.value


-- @@ L25-28 verbatim
theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_all [ThetaC.circuit, ThetaC.Assumptions, ThetaC.Spec,
    ThetaD.circuit, ThetaD.Assumptions, ThetaD.Spec,
    ThetaXor.circuit, ThetaXor.Assumptions, ThetaXor.Spec, Specs.Keccak256.theta]


-- @@ L30-33 verbatim
theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_all [ThetaC.circuit, ThetaC.Assumptions, ThetaC.Spec,
    ThetaD.circuit, ThetaD.Assumptions, ThetaD.Spec,
    ThetaXor.circuit, ThetaXor.Assumptions, ThetaXor.Spec]


-- @@ L35-37 verbatim
def circuit : FormalCircuit (F p) KeccakState KeccakState := {
  main, Assumptions, Spec, soundness, completeness
}

-- @@ L38-38 verbatim
end Gadgets.Keccak256.Theta
