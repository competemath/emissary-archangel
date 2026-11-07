/-
  EvmAsm.Evm64.PrecompileResult

  Pure precompile result framing for GH #116.
-/

module

public import EvmAsm.Evm64.Precompile


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
namespace EvmAsm.Evm64


-- @@ L15-19 verbatim
/-- Coarse status returned by a precompile dispatch. -/
inductive PrecompileStatus where
  | success
  | failure
  deriving DecidableEq, Repr


-- @@ L21-26 verbatim
/-- Pure input surface for a precompile invocation. -/
structure PrecompileInput where
  target : Precompile
  caller : Address
  input : List (BitVec 8)
  gas : Nat


-- @@ L28-32 verbatim
/-- Pure output surface for a precompile invocation. -/
structure PrecompileResult where
  status : PrecompileStatus
  output : List (BitVec 8)
  gasRemaining : Nat


-- @@ L34-34 verbatim
namespace PrecompileResult


-- @@ L36-39 verbatim
def ok (out : List (BitVec 8)) (gasRemaining : Nat) : PrecompileResult :=
  { status := .success
    output := out
    gasRemaining := gasRemaining }


-- @@ L41-44 verbatim
def fail (gasRemaining : Nat) : PrecompileResult :=
  { status := .failure
    output := ([] : List (BitVec 8))
    gasRemaining := gasRemaining }


-- @@ L46-47 verbatim
def succeeded (result : PrecompileResult) : Prop :=
  result.status = .success


-- @@ L49-50 verbatim
def failed (result : PrecompileResult) : Prop :=
  result.status = .failure


-- @@ L52-53 verbatim
def preservesGasBound (input : PrecompileInput) (result : PrecompileResult) : Prop :=
  result.gasRemaining ≤ input.gas


-- @@ L55-56 verbatim
def outputMatches (result : PrecompileResult) (out : List (BitVec 8)) : Prop :=
  result.status = .success ∧ result.output = out


-- @@ L58-59 verbatim
@[simp] theorem ok_status (out : List (BitVec 8)) (gasRemaining : Nat) :
    (ok out gasRemaining).status = .success := rfl


-- @@ L61-62 verbatim
@[simp] theorem ok_output (out : List (BitVec 8)) (gasRemaining : Nat) :
    (ok out gasRemaining).output = out := rfl


-- @@ L64-65 verbatim
@[simp] theorem ok_gasRemaining (out : List (BitVec 8)) (gasRemaining : Nat) :
    (ok out gasRemaining).gasRemaining = gasRemaining := rfl


-- @@ L67-68 verbatim
@[simp] theorem fail_status (gasRemaining : Nat) :
    (fail gasRemaining).status = .failure := rfl


-- @@ L70-71 verbatim
@[simp] theorem fail_output (gasRemaining : Nat) :
    (fail gasRemaining).output = ([] : List (BitVec 8)) := rfl


-- @@ L73-74 verbatim
@[simp] theorem fail_gasRemaining (gasRemaining : Nat) :
    (fail gasRemaining).gasRemaining = gasRemaining := rfl


-- @@ L76-77 verbatim
theorem succeeded_ok (out : List (BitVec 8)) (gasRemaining : Nat) :
    succeeded (ok out gasRemaining) := rfl


-- @@ L79-80 verbatim
theorem failed_fail (gasRemaining : Nat) :
    failed (fail gasRemaining) := rfl


-- @@ L82-83 verbatim
@[simp] theorem output_fail (gasRemaining : Nat) :
    (fail gasRemaining).output = ([] : List (BitVec 8)) := rfl


-- @@ L85-87 verbatim
theorem outputMatches_ok (out : List (BitVec 8)) (gasRemaining : Nat) :
    outputMatches (ok out gasRemaining) out := by
  exact ⟨rfl, rfl⟩


-- @@ L89-91 verbatim
theorem not_failed_ok (out : List (BitVec 8)) (gasRemaining : Nat) :
    ¬ failed (ok out gasRemaining) := by
  simp [failed]


-- @@ L93-95 verbatim
theorem not_succeeded_fail (gasRemaining : Nat) :
    ¬ succeeded (fail gasRemaining) := by
  simp [succeeded, fail]


-- @@ L97-99 verbatim
theorem not_outputMatches_fail (out : List (BitVec 8)) (gasRemaining : Nat) :
    ¬ outputMatches (fail gasRemaining) out := by
  simp [outputMatches]


-- @@ L101-104 verbatim
theorem preservesGasBound_ok_iff
    (input : PrecompileInput) (out : List (BitVec 8)) (gasRemaining : Nat) :
    preservesGasBound input (ok out gasRemaining) ↔ gasRemaining ≤ input.gas := by
  simp [preservesGasBound]


-- @@ L106-109 verbatim
theorem preservesGasBound_fail_iff
    (input : PrecompileInput) (gasRemaining : Nat) :
    preservesGasBound input (fail gasRemaining) ↔ gasRemaining ≤ input.gas := by
  simp [preservesGasBound]


-- @@ L111-113 verbatim
theorem preservesGasBound_same (input : PrecompileInput) :
    preservesGasBound input (ok ([] : List (BitVec 8)) input.gas) := by
  simp [preservesGasBound, ok]


-- @@ L115-115 verbatim
end PrecompileResult


-- @@ L117-117 verbatim
end EvmAsm.Evm64
