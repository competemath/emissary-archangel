import Clean.Circuit.Loops
import Clean.Gadgets.Rotation64.Rotation64
import Clean.Gadgets.Keccak.KeccakState
import Clean.Specs.Keccak256


-- @@ L6-6 verbatim
namespace Gadgets.Keccak256.RhoPi

-- @@ L7-7 verbatim
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^16 + 2^8)]

-- @@ L8-8 verbatim
instance : Fact (p > 512) := .mk (by linarith [‹Fact (p > _)›.elim])


-- @@ L10-12 verbatim
def rhoPiIndices : Vector (Fin 25) 25 := #v[
  0, 15, 5, 20, 10, 6, 21, 11, 1, 16, 12, 2, 17, 7, 22, 18, 8, 23, 13, 3, 24, 14, 4, 19, 9
]

-- @@ L13-15 verbatim
def rhoPiShifts : Vector (Fin 64) 25 := #v[
  0, 28, 1, 27, 62, 44, 20, 6, 36, 55, 43, 3, 25, 10, 39, 21, 45, 8, 15, 41, 14, 61, 18, 56, 2
]

-- @@ L16-16 verbatim
def rhoPiConstants := rhoPiIndices.zip rhoPiShifts


-- @@ L18-20 verbatim
def main (state : Var KeccakState (F p)) : Circuit (F p) (Var KeccakState (F p)) :=
  .map rhoPiConstants fun (i, s) =>
    Rotation64.circuit (-s) state[i.val]


-- @@ L22-22 verbatim
def Assumptions := KeccakState.Normalized (p:=p)


-- @@ L24-26 verbatim
def Spec (state : KeccakState (F p)) (out_state : KeccakState (F p)) :=
  out_state.Normalized
  ∧ out_state.value = Specs.Keccak256.rhoPi state.value


-- @@ L28-31 verbatim
@[reducible] instance elaborated : ElaboratedCircuit (F p) KeccakState KeccakState main := by
  elaborate_circuit

-- recharacterize rhoPi as a loop

-- @@ L32-34 verbatim
lemma rhoPi_loop (state : Vector ℕ 25) :
    Specs.Keccak256.rhoPi state = rhoPiConstants.map fun (i, s) => rotLeft64 state[i.val] s := by
  simp [Specs.Keccak256.rhoPi, rhoPiConstants, rhoPiIndices, rhoPiShifts]


-- @@ L36-49 verbatim
theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [Rotation64.circuit, Rotation64.elaborated]

  -- simplify goal
  apply KeccakState.normalized_value_ext
  simp only [eval_vector, Vector.getElem_map, KeccakState.value, rhoPi_loop]

  -- simplify constraints
  simp only [circuit_norm, eval_vector, Vector.ext_iff] at h_input
  simp only [KeccakState.Normalized] at h_assumptions
  simp only [h_input, h_assumptions, circuit_norm,
    Rotation64.Assumptions, Rotation64.Spec] at h_holds

  simp_all [rhoPiConstants, rotLeft64_eq_rotRight64]


-- @@ L51-59 verbatim
theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start

  -- simplify assumptions
  simp only [circuit_norm, eval_vector, Vector.ext_iff] at h_input
  simp only [KeccakState.Normalized] at h_assumptions

  -- simplify constraints (goal + environment) and apply assumptions
  simp_all [circuit_norm, Rotation64.circuit, Rotation64.Assumptions, Rotation64.Spec]


-- @@ L61-67 verbatim
def circuit : FormalCircuit (F p) KeccakState KeccakState where
  main := main
  elaborated := elaborated
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

-- @@ L68-68 verbatim
end Gadgets.Keccak256.RhoPi
