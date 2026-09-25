import Batteries.Data.Fin.Fold
import Clean.Gadgets.Keccak.KeccakRound
import Clean.Specs.Keccak256


-- @@ L5-5 verbatim
namespace Gadgets.Keccak256.Permutation

-- @@ L6-6 verbatim
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^16 + 2^8)]

-- @@ L7-7 verbatim
open Specs.Keccak256


-- @@ L9-11 verbatim
def main (state : Var KeccakState (F p)) : Circuit (F p) (Var KeccakState (F p)) :=
  .foldl roundConstants state
    fun state rc => KeccakRound.circuit rc state


-- @@ L13-13 verbatim
def Assumptions (state : KeccakState (F p)) := state.Normalized


-- @@ L15-17 verbatim
def Spec (state : KeccakState (F p)) (out_state : KeccakState (F p)) :=
  out_state.Normalized
  ∧ out_state.value = keccakPermutation state.value


-- @@ L19-22 verbatim
/-- state in the ith round, starting from offset n -/
def stateVar (n : ℕ) (i : ℕ) : Var KeccakState (F p) :=
  Vector.mapRange 25 (fun j => varFromOffset U64 (n + i * 1288 + j * 16 + 888))
  |>.set 0 (varFromOffset U64 (n + i * 1288 + 1280))


-- @@ L24-29 verbatim
instance elaborated : ElaboratedCircuit (F p) KeccakState KeccakState main := by
  elaborate_circuit_with {
    output _ i0 := stateVar i0 23
  }

-- `Fin.foldl` relates to `Vector.foldl` via this lemma

-- @@ L30-35 verbatim
lemma fin_foldl_eq_vector_foldl (state : Vector ℕ 25) :
  Fin.foldl 24 (fun state j => keccakRound state roundConstants[j]) state
  = roundConstants.foldl keccakRound state := by
  simp only [Vector.foldl, roundConstants, Fin.foldl_eq_foldl_finRange]
  rw [← Array.foldl_toList, ← List.foldl_map]
  simp [List.finRange]


-- @@ L37-70 verbatim
theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [KeccakRound.circuit, KeccakRound.Spec, KeccakRound.Assumptions]

  -- simplify
  obtain ⟨ h_init, h_succ ⟩ := h_holds
  specialize h_init h_assumptions

  -- clean up formulation
  let state (i : ℕ) : KeccakState (F p) := eval env (stateVar (p:=p) i₀ i)

  change (state 0).Normalized ∧
    (state 0).value = keccakRound input.value roundConstants[0]
  at h_init

  change ∀ (i : ℕ) (hi : i + 1 < 24), (state i).Normalized → (state (i + 1)).Normalized ∧
    (state (i + 1)).value = keccakRound (state i).value roundConstants[i + 1]
  at h_succ

  -- inductive proof
  have h_inductive (i : ℕ) (hi : i < 24) :
    (state i).Normalized ∧ (state i).value =
      Fin.foldl (i + 1) (fun state j => keccakRound state roundConstants[j.val]) input.value := by
    induction i with
    | zero => simp [Fin.foldl_succ, h_init]
    | succ i ih =>
      have hi' : i < 24 := Nat.lt_of_succ_lt hi
      specialize ih hi'
      specialize h_succ i hi ih.left
      use h_succ.left
      rw [h_succ.right, Fin.foldl_succ_last, ih.right]
      simp
  have h := h_inductive 23 (by norm_num)
  simp only [keccakPermutation, ← fin_foldl_eq_vector_foldl] at h ⊢
  exact h


-- @@ L72-103 verbatim
theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [KeccakRound.circuit, KeccakRound.Spec, KeccakRound.Assumptions]

  -- simplify
  simp only [h_assumptions, circuit_norm] at h_env ⊢

  obtain ⟨ h_init, h_succ ⟩ := h_env
  replace h_init := h_init.left
  replace h_succ := fun i hi ih => (h_succ i hi ih).left

  intro i hi

  -- clean up formulation
  let state (i : ℕ) : KeccakState (F p) := eval env.toEnvironment (stateVar (p:=p) i₀ i)

  change (state 0).Normalized at h_init

  change ∀ (i : ℕ) (hi : i + 1 < 24),
    (state i).Normalized → (state (i + 1)).Normalized
  at h_succ

  change (state i).Normalized

  -- inductive proof
  have h_norm (i : ℕ) (hi : i < 24) : (state i).Normalized := by
    induction i with
    | zero => exact h_init
    | succ i ih =>
      have hi' : i < 24 := Nat.lt_of_succ_lt hi
      specialize ih hi'
      exact h_succ i hi ih
  exact h_norm i (Nat.lt_of_succ_lt hi)


-- @@ L105-113 verbatim
def circuit : FormalCircuit (F p) KeccakState KeccakState where
  main := main
  elaborated := elaborated
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  -- TODO why does this time out??
  -- completeness
  completeness := by simp only [completeness]


-- @@ L115-115 verbatim
end Gadgets.Keccak256.Permutation
