/-
  EvmAsm.Stateless.SpecRef.Vm

  Port of the EVM machine layer of
  `execution-specs/src/ethereum/forks/amsterdam/` (`@tests-zkevm@v0.5.0`,
  `bd8c673`) — bead `evm-asm-s1d19.5`, Stack C stage 3:

  * `vm/__init__.py`: `BlockEnvironment`, `BlockOutput`,
    `TransactionEnvironment`, `Message`, `Evm` (classes of the same
    names), `credit_state_gas_refund` (function
    `credit_state_gas_refund`), `TRANSFER_TOPIC` / `SYSTEM_ADDRESS` /
    `CALL_SUCCESS` and the `blocks.py` `Log` (class `Log`)
  * `vm/exceptions.py`: the `ExceptionalHalt` / `Revert` hierarchy
    (class `ExceptionalHalt` and friends) as `EvmError`
  * `vm/stack.py`: `pop`, `push`, `decode_single`, `decode_pair`
    (functions of the same names)
  * `vm/memory.py`: `memory_write`, `memory_read_bytes`, `buffer_read`
    (functions of the same names)
  * `vm/gas.py`: `check_gas`, `charge_gas`, `charge_state_gas`
    (functions of the same names) — the `Evm`-mutating half deferred
    from the stage-2 `Gas.lean`

  ## The machine monad

  Python instruction implementations mutate an `Evm` object (which
  aliases the `TransactionState`/`BlockState` trackers through
  `message.tx_env.state`) and raise two kinds of exceptions:

  * `ExceptionalHalt` / `Revert` — caught at frame boundaries
    (`execute_code`); the `Evm`'s mutations up to the raise are KEPT
    (state-tracker rollback is a separate, explicit
    `restore_tx_state`).
  * everything else (witness-authentication failures, spec asserts) —
    propagates uncaught to `verify_stateless_new_payload` → rejection.

  The monad mirrors exactly that:
  `EvmM α := ExceptT EvmError (StateT Machine (Except SpecError)) α`
  — a thrown `EvmError` carries the mutated `Machine` with it, while a
  `SpecError` aborts the whole computation.  `Machine` is the current
  frame's `Evm` plus the shared world (the transaction tracker; the
  Python aliasing `evm.message.tx_env.state.parent == block_env.state`
  becomes a single copy living in `Machine.txState`).  Frame nesting
  (`parent_evm`) is realized by RUNNING the child's `EvmM` on a child
  `Machine` and merging (the interpreter stage); `parent_evm` itself is
  only read by tracing hooks, which are not modeled.

  Python `bytearray` memory is `Bytes` here; `Set`s are dedup lists
  (`StateTracker.lean` conventions).
-/

module

public import EvmAsm.Stateless.SpecRef.BlockAccessLists
public import EvmAsm.Stateless.SpecRef.Transactions
meta import EvmAsm.Stateless.SpecRef.BlockAccessLists
meta import EvmAsm.Stateless.SpecRef.Transactions


-- @@ L58-58 verbatim
@[expose] public section


-- @@ L60-60 verbatim
namespace EvmAsm.Stateless.SpecRef


-- @@ L62-62 verbatim
/-! ## `vm/exceptions.py` — `EvmError` -/


-- @@ L64-80 verbatim
/-- The `ExceptionalHalt`/`Revert` hierarchy (`vm/exceptions.py`).
    `revert` is the only non-halt: it preserves unspent gas. -/
inductive EvmError where
  | revert
  | stackUnderflow
  | stackOverflow
  | outOfGas
  | invalidOpcode (op : Nat)
  | invalidJumpDest
  | stackDepthLimit
  | writeInStaticContext
  | outOfBoundsRead
  | invalidParameter (why : String)
  | invalidContractPrefix
  | addressCollision
  | kzgProofError
  deriving Repr, BEq


-- @@ L82-85 verbatim
/-- Is this an `ExceptionalHalt` (consumes all frame gas)? -/
def EvmError.isHalt : EvmError → Bool
  | .revert => false
  | _ => true


-- @@ L87-87 verbatim
/-! ## `blocks.py` `Log` (class `Log`) -/


-- @@ L89-94 verbatim
/-- `Log` (`blocks.py`, class `Log`). -/
structure Log where
  address : Address
  topics : List Hash32
  data : Bytes
  deriving Repr, BEq


-- @@ L96-96 verbatim
/-! ## `vm/__init__.py` dataclasses -/


-- @@ L98-101 verbatim
/-- `TRANSFER_TOPIC = keccak256(b"Transfer(address,address,uint256)")`. -/
def TRANSFER_TOPIC : Hash32 :=
  keccak256 ("Transfer(address,address,uint256)".toUTF8.toList.map
    (fun b => BitVec.ofNat 8 b.toNat))


-- @@ L103-105 verbatim
/-- `SYSTEM_ADDRESS` (`vm/__init__.py`). -/
def VM_SYSTEM_ADDRESS : Address :=
  natToBytesBE 20 0xfffffffffffffffffffffffffffffffffffffffe


-- @@ L107-108 verbatim
/-- `CALL_SUCCESS` (`vm/__init__.py`). -/
def CALL_SUCCESS : U256 := 1


-- @@ L110-126 verbatim
/-- `BlockEnvironment` (class `BlockEnvironment`), minus the mutable
    `state`/`block_access_list_builder` — those live in `Machine`
    (see the header note on aliasing). -/
structure BlockEnvironment where
  chainId : U64
  blockGasLimit : Uint
  blockHashes : List Hash32
  coinbase : Address
  number : Uint
  baseFeePerGas : Uint
  time : U256
  prevRandao : Bytes32
  excessBlobGas : U64
  parentBeaconBlockRoot : Hash32
  slotNumber : U64
  transactionPublicKeys : Option (List Bytes) := none
  deriving Repr


-- @@ L128-142 verbatim
/-- `BlockOutput` (class `BlockOutput`); the three `Trie`s are their
    key→value assoc data (roots are computed at the end via
    `build_mpt`/`mpt_root`, exactly the Python `root(trie)`). -/
structure BlockOutput where
  blockGasUsed : Uint := 0
  blockStateGasUsed : Uint := 0
  cumulativeGasUsed : Uint := 0
  transactionsTrie : List (Bytes × Bytes) := []
  receiptsTrie : List (Bytes × Bytes) := []
  receiptKeys : List Bytes := []
  blockLogs : List Log := []
  withdrawalsTrie : List (Bytes × Bytes) := []
  blobGasUsed : U64 := 0
  requests : List Bytes := []
  blockAccessList : BlockAccessList := []
  
-- @@ L143-147 verbatim
/-- Modeling-only: the decoded logs of each receipt in order, kept so
      `parse_deposit_requests` need not re-decode the trie values (the
      Python stores `Bytes | Receipt` objects and decodes on read —
      observationally equal). -/
  decodedReceiptLogs : List (List Log) := []
  
-- @@ L148-148 verbatim
deriving Repr


-- @@ L150-167 verbatim
/-- `TransactionEnvironment` (class `TransactionEnvironment`), minus
    the mutable `state` tracker (lives in `Machine`). -/
structure TransactionEnvironment where
  origin : Address
  /-- `Bytes0 | Address`: `none` = creation. -/
  recipient : Option Address
  value : U256
  gasPrice : Uint
  gas : Uint
  stateGasReservoir : Uint
  accessListAddresses : List Address
  accessListStorageKeys : List (Address × Bytes32)
  blobVersionedHashes : List VersionedHash
  authorizations : List Authorization
  indexInBlock : Option Uint
  txHash : Option Hash32
  intrinsicRegularGas : Uint
  intrinsicStateGas : Uint
  
-- @@ L168-168 verbatim
deriving Repr


-- @@ L170-189 verbatim
/-- `Message` (class `Message`), minus `parent_evm` (tracing only). -/
structure Message where
  blockEnv : BlockEnvironment
  txEnv : TransactionEnvironment
  caller : Address
  /-- `Bytes0 | Address`: `none` = creation. -/
  target : Option Address
  currentTarget : Address
  gas : Uint
  stateGasReservoir : Uint
  value : U256
  data : Bytes
  codeAddress : Option Address
  code : Bytes
  depth : Uint
  shouldTransferValue : Bool
  isStatic : Bool
  accessedAddresses : List Address
  accessedStorageKeys : List (Address × Bytes32)
  disablePrecompiles : Bool
  
-- @@ L190-190 verbatim
deriving Repr


-- @@ L192-212 verbatim
/-- `Evm` (class `Evm`) — the per-frame machine registers. -/
structure Evm where
  pc : Uint := 0
  stack : List U256 := []
  memory : Bytes := []
  code : Bytes
  gasLeft : Uint
  stateGasLeft : Uint
  validJumpDestinations : List Uint
  logs : List Log := []
  refundCounter : Int := 0
  running : Bool := true
  message : Message
  output : Bytes := []
  accountsToDelete : List Address := []
  returnData : Bytes := []
  error : Option EvmError := none
  accessedAddresses : List Address
  accessedStorageKeys : List (Address × Bytes32)
  regularGasUsed : Uint := 0
  stateGasSpilled : Uint := 0
  
-- @@ L213-217 verbatim
/-- v0.6.0: state gas consumed by `set_delegation` at the top frame,
      folded out of the frame baseline by `process_message` (the running
      `state_gas_used` counter is deleted; net frame use is computed by
      `frame_state_gas_used` from the reservoir delta). -/
  authStateGasUsed : Int := 0
  
-- @@ L218-218 verbatim
deriving Repr


-- @@ L220-225 verbatim
/-- The machine: the current frame plus the shared mutable world (the
    transaction tracker — whose `parent` is the block tracker — and
    the BAL builder). -/
structure Machine where
  evm : Evm
  txState : TransactionState


-- @@ L227-229 verbatim
/-- The machine monad (see the header): `EvmError` throws carry the
    mutated state; `SpecError`s abort everything. -/
abbrev EvmM (α : Type) := ExceptT EvmError (StateT Machine (Except SpecError)) α


-- @@ L231-231 verbatim
namespace EvmM


-- @@ L233-237 verbatim
/-- Run a `TxM` (state-tracker) action against the machine's tracker. -/
def liftTx (m : TxM α) : EvmM α := fun s =>
  match m.run s.txState with
  | .error e => .error e
  | .ok (a, ts) => .ok (.ok a, { s with txState := ts })


-- @@ L239-243 verbatim
/-- Abort with a spec-level rejection (never caught by frames). -/
def liftSpec (m : Except SpecError α) : EvmM α := fun s =>
  match m with
  | .error e => .error e
  | .ok a => .ok (.ok a, s)


-- @@ L245-245 verbatim
def getEvm : EvmM Evm := fun s => .ok (.ok s.evm, s)


-- @@ L247-247 verbatim
def getBlockState : EvmM BlockState := fun s => .ok (.ok s.txState.parent, s)


-- @@ L249-250 verbatim
def modifyEvm (f : Evm → Evm) : EvmM Unit := fun s =>
  .ok (.ok (), { s with evm := f s.evm })


-- @@ L252-252 verbatim
end EvmM


-- @@ L254-254 verbatim
/-! ## `vm/stack.py` -/


-- @@ L256-262 verbatim
/-- `pop(stack)` (`vm/stack.py`, function `pop`). -/
def stackPop : EvmM U256 := do
  match (← EvmM.getEvm).stack with
  | [] => throw .stackUnderflow
  | top :: rest =>
      EvmM.modifyEvm (fun e => { e with stack := rest })
      pure top


-- @@ L264-266 verbatim
/-- Pop `n` items (top first). -/
def stackPopN (n : Nat) : EvmM (List U256) :=
  (List.range n).mapM (fun _ => stackPop)


-- @@ L268-271 verbatim
/-- `push(stack, value)` (`vm/stack.py`, function `push`). -/
def stackPush (value : U256) : EvmM Unit := do
  if (← EvmM.getEvm).stack.length == 1024 then throw .stackOverflow
  EvmM.modifyEvm (fun e => { e with stack := value :: e.stack })


-- @@ L273-277 verbatim
/-- `decode_single(x)` (`vm/stack.py`, function `decode_single`):
    DUPN/SWAPN immediate → stack index `17 ≤ n ≤ 235`. -/
def decode_single (x : Nat) : Except EvmError Nat :=
  if x ≤ 90 || (128 ≤ x && x ≤ 255) then pure ((x + 145) % 256)
  else throw (.invalidParameter "DUPN/SWAPN immediate out of range")


-- @@ L279-288 verbatim
/-- `decode_pair(x)` (`vm/stack.py`, function `decode_pair`):
    EXCHANGE immediate → `(n, m)`, `1 ≤ n ≤ 14`, `n < m ≤ 30 − n`. -/
def decode_pair (x : Nat) : Except EvmError (Nat × Nat) :=
  if x ≤ 81 || (128 ≤ x && x ≤ 255) then
    let k := x ^^^ 143
    let q := k / 16
    let r := k % 16
    if q < r then pure (q + 1, r + 1)
    else pure (r + 1, 29 - q)
  else throw (.invalidParameter "EXCHANGE immediate in forbidden range")


-- @@ L290-294 verbatim
/-! ## `vm/memory.py`

Memory is `Bytes`; expansion happens explicitly (`extend_memory` at the
instruction sites appends zeros), matching the Python bytearray whose
size only grows via the gas-metered extension. -/


-- @@ L296-298 verbatim
/-- `memory_write(memory, start_position, value)`. -/
def memory_write (memory : Bytes) (start_position : U256) (value : Bytes) : Bytes :=
  memory.take start_position ++ value ++ memory.drop (start_position + value.length)


-- @@ L300-302 verbatim
/-- `memory_read_bytes(memory, start_position, size)`. -/
def memory_read_bytes (memory : Bytes) (start_position size : U256) : Bytes :=
  (memory.drop start_position).take size


-- @@ L304-307 verbatim
/-- `buffer_read(buffer, start_position, size)`: zero-padded read. -/
def buffer_read (buffer : Bytes) (start_position size : U256) : Bytes :=
  let s := (buffer.drop start_position).take size
  s ++ List.replicate (size - s.length) 0x00


-- @@ L309-312 verbatim
/-- Grow the frame memory by `expand_by` zero bytes (the instruction
    sites' `evm.memory += b"\x00" * extend_memory.expand_by`). -/
def extendMemory (expand_by : Uint) : EvmM Unit :=
  EvmM.modifyEvm (fun e => { e with memory := e.memory ++ List.replicate expand_by 0x00 })


-- @@ L314-316 verbatim
/-! ## `vm/gas.py` — the `Evm`-mutating half
(`check_gas` / `charge_gas` / `charge_state_gas`, and
`vm/__init__.py` `credit_state_gas_refund`) -/


-- @@ L318-320 verbatim
/-- `check_gas(evm, amount)`. -/
def check_gas (amount : Uint) : EvmM Unit := do
  if (← EvmM.getEvm).gasLeft < amount then throw .outOfGas


-- @@ L322-327 verbatim
/-- `charge_gas(evm, amount)`. -/
def charge_gas (amount : Uint) : EvmM Unit := do
  if (← EvmM.getEvm).gasLeft < amount then throw .outOfGas
  EvmM.modifyEvm (fun e =>
    { e with gasLeft := e.gasLeft - amount
             regularGasUsed := e.regularGasUsed + amount })


-- @@ L329-342 verbatim
/-- `charge_state_gas(evm, amount)`: reservoir first, spill into
    `gas_left`. -/
def charge_state_gas (amount : Uint) : EvmM Unit := do
  let e ← EvmM.getEvm
  if e.stateGasLeft ≥ amount then
    EvmM.modifyEvm (fun e => { e with stateGasLeft := e.stateGasLeft - amount })
  else if e.stateGasLeft + e.gasLeft ≥ amount then
    let remainder := amount - e.stateGasLeft
    EvmM.modifyEvm (fun e =>
      { e with stateGasLeft := 0
               gasLeft := e.gasLeft - remainder
               stateGasSpilled := e.stateGasSpilled + remainder })
  else
    throw .outOfGas


-- @@ L344-352 verbatim
/-- `credit_state_gas_refund(evm, amount)` (`vm/__init__.py`): LIFO —
    `gas_left` up to `state_gas_spilled`, then the reservoir. -/
def credit_state_gas_refund (amount : Uint) : EvmM Unit := do
  let e ← EvmM.getEvm
  let from_gas_left := min amount e.stateGasSpilled
  EvmM.modifyEvm (fun e =>
    { e with gasLeft := e.gasLeft + from_gas_left
             stateGasSpilled := e.stateGasSpilled - from_gas_left
             stateGasLeft := e.stateGasLeft + (amount - from_gas_left) })


-- @@ L354-359 verbatim
/-- `frame_state_gas_used(evm)` (`vm/__init__.py:259`, v0.6.0): net
    state gas consumed by a finished frame — the reservoir drawn down
    plus the spill. May be negative when refunds exceed charges. -/
def frame_state_gas_used (e : Evm) : Int :=
  (e.message.stateGasReservoir : Int) - (e.stateGasLeft : Int)
    + (e.stateGasSpilled : Int)


-- @@ L361-361 verbatim
/-! ## Sanity checks -/


-- @@ L363-386 verbatim
private def testMachine : Machine :=
  let blockEnv : BlockEnvironment :=
    { chainId := 1, blockGasLimit := 30000000, blockHashes := [],
      coinbase := List.replicate 20 0, number := 1, baseFeePerGas := 7,
      time := 0, prevRandao := List.replicate 32 0, excessBlobGas := 0,
      parentBeaconBlockRoot := List.replicate 32 0, slotNumber := 1 }
  let txEnv : TransactionEnvironment :=
    { origin := List.replicate 20 0xAA, recipient := none, value := 0,
      gasPrice := 10, gas := 100000, stateGasReservoir := 0,
      accessListAddresses := [], accessListStorageKeys := [],
      blobVersionedHashes := [], authorizations := [], indexInBlock := none,
      txHash := none, intrinsicRegularGas := 21000, intrinsicStateGas := 0 }
  let msg : Message :=
    { blockEnv, txEnv, caller := List.replicate 20 0xAA, target := none,
      currentTarget := List.replicate 20 0xBB, gas := 79000,
      stateGasReservoir := 50, value := 0, data := [], codeAddress := none,
      code := [], depth := 0, shouldTransferValue := true, isStatic := false,
      accessedAddresses := [], accessedStorageKeys := [],
      disablePrecompiles := false }
  { evm := { code := [], gasLeft := 1000, stateGasLeft := 50,
             validJumpDestinations := [], message := msg,
             accessedAddresses := [], accessedStorageKeys := [] }
    txState := { parent := { preState := { nodeDb := [], stateRoot := EMPTY_TRIE_ROOT,
                                           codeDb := [] } } } }


-- @@ L388-435 verbatim
private def runVm (m : EvmM α) : Except SpecError (Except EvmError α × Machine) :=
  (m.run.run testMachine)

-- push/pop round trip; underflow and overflow throw.
#guard match runVm (do stackPush 5; stackPush 7; stackPop) with
  | .ok (.ok 7, s) => s.evm.stack == [5] | _ => false
#guard match runVm stackPop with
  | .ok (.error .stackUnderflow, _) => true | _ => false
#guard match runVm (do
    for _ in [0:1024] do stackPush 1
    stackPush 1) with
  | .ok (.error .stackOverflow, s) => s.evm.stack.length == 1024 | _ => false

-- decode_single/decode_pair vectors (Python: decode_single(0)=145,
-- decode_single(90)=235, decode_single(128)=17, decode_single(255)=144;
-- decode_pair(0)=(1,16)… k=143→q=8,r=15,q<r→(9,16); forbidden ranges).
#guard (decode_single 0).toOption == some 145
#guard (decode_single 90).toOption == some 235
#guard (decode_single 128).toOption == some 17
#guard (decode_single 255).toOption == some 144
#guard match decode_single 100 with | .error (.invalidParameter _) => true | _ => false
#guard (decode_pair 0).toOption == some (9, 16)
#guard (decode_pair 81).toOption == some (14, 15)
#guard (decode_pair 128).toOption == some (1, 16)
#guard (decode_pair 255).toOption == some (1, 22)
#guard match decode_pair 100 with | .error (.invalidParameter _) => true | _ => false

-- memory: write/read round trip, zero-padded buffer read.
#guard memory_write [0, 0, 0, 0] 1 [0xAA, 0xBB] == [0, 0xAA, 0xBB, 0]
#guard memory_read_bytes [1, 2, 3, 4] 1 2 == [2, 3]
#guard buffer_read [1, 2, 3] 2 4 == [3, 0, 0, 0]

-- charge_gas debits and records; OOG preserves the machine state.
#guard match runVm (do charge_gas 300; charge_gas 800) with
  | .ok (.error .outOfGas, s) => s.evm.gasLeft == 700 && s.evm.regularGasUsed == 300
  | _ => false

-- charge_state_gas: reservoir first, then spill; refund restores LIFO.
#guard match runVm (do
    charge_state_gas 30   -- reservoir 50 → 20
    charge_state_gas 120  -- reservoir → 0, spill 100 from gas_left
    credit_state_gas_refund 110) with
  | .ok (.ok _, s) =>
      s.evm.stateGasLeft == 10 && s.evm.gasLeft == 1000
      && s.evm.stateGasSpilled == 0
      -- v0.6.0: net frame use from the reservoir delta (50 − 10 + 0).
      && frame_state_gas_used s.evm == 40
  | _ => false


-- @@ L437-437 verbatim
end EvmAsm.Stateless.SpecRef
