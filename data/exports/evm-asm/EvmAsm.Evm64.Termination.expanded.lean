/-
  EvmAsm.Evm64.Termination

  Pure terminating-status helpers for GH #113.
-/

module

public import EvmAsm.Evm64.EvmState


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
namespace EvmAsm.Evm64

-- @@ L14-14 verbatim
namespace EvmState


-- @@ L16-18 verbatim
/-- STOP terminates without returndata. -/
def stop (state : EvmState) : EvmState :=
  state.withStatus .stopped


-- @@ L20-22 verbatim
/-- RETURN terminates successfully with returndata bytes. -/
def returnWith (state : EvmState) (data : List (BitVec 8)) : EvmState :=
  state.withStatus (.returned data)


-- @@ L24-26 verbatim
/-- REVERT terminates with revert data. -/
def revertWith (state : EvmState) (data : List (BitVec 8)) : EvmState :=
  state.withStatus (.reverted data)


-- @@ L28-30 verbatim
/-- INVALID terminates with an error status. -/
def invalid (state : EvmState) : EvmState :=
  state.withStatus .error


-- @@ L32-33 verbatim
@[simp] theorem stop_status (state : EvmState) :
    state.stop.status = .stopped := rfl


-- @@ L35-36 verbatim
@[simp] theorem returnWith_status (state : EvmState) (data : List (BitVec 8)) :
    (state.returnWith data).status = .returned data := rfl


-- @@ L38-39 verbatim
@[simp] theorem revertWith_status (state : EvmState) (data : List (BitVec 8)) :
    (state.revertWith data).status = .reverted data := rfl


-- @@ L41-42 verbatim
@[simp] theorem invalid_status (state : EvmState) :
    state.invalid.status = .error := rfl


-- @@ L44-45 verbatim
theorem stop_status_tag (state : EvmState) :
    state.stop.status.tag = 1 := rfl


-- @@ L47-48 verbatim
theorem returnWith_status_tag (state : EvmState) (data : List (BitVec 8)) :
    (state.returnWith data).status.tag = 2 := rfl


-- @@ L50-51 verbatim
theorem revertWith_status_tag (state : EvmState) (data : List (BitVec 8)) :
    (state.revertWith data).status.tag = 3 := rfl


-- @@ L53-54 verbatim
theorem invalid_status_tag (state : EvmState) :
    state.invalid.status.tag = 4 := rfl


-- @@ L56-57 verbatim
@[simp] theorem stop_pc (state : EvmState) :
    state.stop.pc = state.pc := rfl


-- @@ L59-60 verbatim
@[simp] theorem returnWith_pc (state : EvmState) (data : List (BitVec 8)) :
    (state.returnWith data).pc = state.pc := rfl


-- @@ L62-63 verbatim
@[simp] theorem revertWith_pc (state : EvmState) (data : List (BitVec 8)) :
    (state.revertWith data).pc = state.pc := rfl


-- @@ L65-66 verbatim
@[simp] theorem invalid_pc (state : EvmState) :
    state.invalid.pc = state.pc := rfl


-- @@ L68-69 verbatim
@[simp] theorem stop_stack (state : EvmState) :
    state.stop.stack = state.stack := rfl


-- @@ L71-72 verbatim
@[simp] theorem returnWith_stack (state : EvmState) (data : List (BitVec 8)) :
    (state.returnWith data).stack = state.stack := rfl


-- @@ L74-75 verbatim
@[simp] theorem revertWith_stack (state : EvmState) (data : List (BitVec 8)) :
    (state.revertWith data).stack = state.stack := rfl


-- @@ L77-78 verbatim
@[simp] theorem invalid_stack (state : EvmState) :
    (state.invalid).stack = state.stack := rfl


-- @@ L80-85 verbatim
/-! ### Structural preservation lemmas

The terminating helpers only update the `status` field; gas, memory, code, and
environment fields are preserved untouched. Frame-side reasoning for the
upcoming RETURN/REVERT/STOP/INVALID handler specs and the interpreter-loop
termination proofs needs each preservation fact as a `simp` lemma. -/


-- @@ L87-88 verbatim
@[simp] theorem stop_gas (state : EvmState) :
    state.stop.gas = state.gas := rfl


-- @@ L90-91 verbatim
@[simp] theorem stop_memoryCells (state : EvmState) :
    state.stop.memoryCells = state.memoryCells := rfl


-- @@ L93-94 verbatim
@[simp] theorem stop_memory (state : EvmState) :
    state.stop.memory = state.memory := rfl


-- @@ L96-97 verbatim
@[simp] theorem stop_memSize (state : EvmState) :
    state.stop.memSize = state.memSize := rfl


-- @@ L99-100 verbatim
@[simp] theorem stop_code (state : EvmState) :
    state.stop.code = state.code := rfl


-- @@ L102-103 verbatim
@[simp] theorem stop_codeLen (state : EvmState) :
    state.stop.codeLen = state.codeLen := rfl


-- @@ L105-106 verbatim
@[simp] theorem stop_env (state : EvmState) :
    state.stop.env = state.env := rfl


-- @@ L108-112 verbatim
theorem stop_codeLenMatches
    (state : EvmState) (h_codeLen : state.codeLenMatches) :
    state.stop.codeLenMatches := by
  unfold EvmState.codeLenMatches at h_codeLen ⊢
  simp [h_codeLen]


-- @@ L114-115 verbatim
@[simp] theorem returnWith_gas (state : EvmState) (data : List (BitVec 8)) :
    (state.returnWith data).gas = state.gas := rfl


-- @@ L117-118 verbatim
@[simp] theorem returnWith_memoryCells (state : EvmState) (data : List (BitVec 8)) :
    (state.returnWith data).memoryCells = state.memoryCells := rfl


-- @@ L120-121 verbatim
@[simp] theorem returnWith_memory (state : EvmState) (data : List (BitVec 8)) :
    (state.returnWith data).memory = state.memory := rfl


-- @@ L123-124 verbatim
@[simp] theorem returnWith_memSize (state : EvmState) (data : List (BitVec 8)) :
    (state.returnWith data).memSize = state.memSize := rfl


-- @@ L126-127 verbatim
@[simp] theorem returnWith_code (state : EvmState) (data : List (BitVec 8)) :
    (state.returnWith data).code = state.code := rfl


-- @@ L129-130 verbatim
@[simp] theorem returnWith_codeLen (state : EvmState) (data : List (BitVec 8)) :
    (state.returnWith data).codeLen = state.codeLen := rfl


-- @@ L132-133 verbatim
@[simp] theorem returnWith_env (state : EvmState) (data : List (BitVec 8)) :
    (state.returnWith data).env = state.env := rfl


-- @@ L135-136 verbatim
@[simp] theorem revertWith_gas (state : EvmState) (data : List (BitVec 8)) :
    (state.revertWith data).gas = state.gas := rfl


-- @@ L138-139 verbatim
@[simp] theorem revertWith_memoryCells (state : EvmState) (data : List (BitVec 8)) :
    (state.revertWith data).memoryCells = state.memoryCells := rfl


-- @@ L141-142 verbatim
@[simp] theorem revertWith_memory (state : EvmState) (data : List (BitVec 8)) :
    (state.revertWith data).memory = state.memory := rfl


-- @@ L144-145 verbatim
@[simp] theorem revertWith_memSize (state : EvmState) (data : List (BitVec 8)) :
    (state.revertWith data).memSize = state.memSize := rfl


-- @@ L147-148 verbatim
@[simp] theorem revertWith_code (state : EvmState) (data : List (BitVec 8)) :
    (state.revertWith data).code = state.code := rfl


-- @@ L150-151 verbatim
@[simp] theorem revertWith_codeLen (state : EvmState) (data : List (BitVec 8)) :
    (state.revertWith data).codeLen = state.codeLen := rfl


-- @@ L153-154 verbatim
@[simp] theorem revertWith_env (state : EvmState) (data : List (BitVec 8)) :
    (state.revertWith data).env = state.env := rfl


-- @@ L156-157 verbatim
@[simp] theorem invalid_gas (state : EvmState) :
    state.invalid.gas = state.gas := rfl


-- @@ L159-160 verbatim
@[simp] theorem invalid_memoryCells (state : EvmState) :
    state.invalid.memoryCells = state.memoryCells := rfl


-- @@ L162-163 verbatim
@[simp] theorem invalid_memory (state : EvmState) :
    state.invalid.memory = state.memory := rfl


-- @@ L165-166 verbatim
@[simp] theorem invalid_memSize (state : EvmState) :
    state.invalid.memSize = state.memSize := rfl


-- @@ L168-169 verbatim
@[simp] theorem invalid_code (state : EvmState) :
    state.invalid.code = state.code := rfl


-- @@ L171-172 verbatim
@[simp] theorem invalid_codeLen (state : EvmState) :
    state.invalid.codeLen = state.codeLen := rfl


-- @@ L174-175 verbatim
@[simp] theorem invalid_env (state : EvmState) :
    state.invalid.env = state.env := rfl


-- @@ L177-181 verbatim
theorem invalid_codeLenMatches
    (state : EvmState) (h_codeLen : state.codeLenMatches) :
    state.invalid.codeLenMatches := by
  unfold EvmState.codeLenMatches at h_codeLen ⊢
  simp [h_codeLen]


-- @@ L183-183 verbatim
end EvmState

-- @@ L184-184 verbatim
end EvmAsm.Evm64
