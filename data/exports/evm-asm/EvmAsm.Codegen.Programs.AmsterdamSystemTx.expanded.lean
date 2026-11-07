/-
  EvmAsm.Codegen.Programs.AmsterdamSystemTx

  Shared constants for Amsterdam system transactions.  These mirror
  execution-specs `src/ethereum/forks/amsterdam/fork.py` and `vm/gas.py`:
  `process_unchecked_system_transaction` constructs a SYSTEM-address call with
  a fixed 30M regular gas budget and a bounded state-gas reservoir sized for
  16 storage-set writes.  The concrete system-contract children (EIP-4788,
  EIP-2935, EIP-7002, EIP-7251) should import this module instead of
  open-coding these numbers.

  `COST_PER_STATE_BYTE` itself moved **down** to the import-free
  `EvmAsm.Codegen.GasConstants` (GH #10980) so the two code-deposit sites, which need
  the multiplier as a runtime operand rather than a folded product, can name it without
  importing this module.  Every user of `amsterdamCostPerStateByte` still resolves it
  through the import below.
-/

module

public import EvmAsm.Codegen.GasConstants
meta import EvmAsm.Codegen.GasConstants


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-26 verbatim
namespace EvmAsm.Codegen


-- @@ L28-32 verbatim
/-- execution-specs Amsterdam `SYSTEM_TRANSACTION_GAS`. -/
def amsterdamSystemTransactionGas : Nat := 30000000

/- `amsterdamCostPerStateByte` now lives in `EvmAsm.Codegen.GasConstants` (imported above);
   it is unchanged at 1530 and is still referenced by name throughout this module. -/


-- @@ L34-35 verbatim
/-- `STATE_BYTES_PER_NEW_ACCOUNT` for the v0.4.0 conformance target = 120 (vm/gas.py:31). -/
def amsterdamStateBytesPerNewAccountV2 : Nat := 120


-- @@ L37-37 verbatim
#guard amsterdamStateBytesPerNewAccountV2 * amsterdamCostPerStateByte = 183600   -- new-account state gas (v0.4.0)

-- @@ L38-38 verbatim
#guard (120 + 64) * amsterdamCostPerStateByte = 281520  -- new-account + one SSTORE = create_state_gas header.gas_used


-- @@ L40-41 verbatim
/-- execution-specs Amsterdam `STATE_BYTES_PER_STORAGE_SET`. -/
def amsterdamStateBytesPerStorageSet : Nat := 64


-- @@ L43-44 verbatim
/-- execution-specs Amsterdam `STATE_BYTES_PER_NEW_ACCOUNT`. -/
def amsterdamStateBytesPerNewAccount : Nat := 120


-- @@ L46-47 verbatim
/-- execution-specs Amsterdam `STATE_BYTES_PER_AUTH_BASE`. -/
def amsterdamStateBytesPerAuthBase : Nat := 23


-- @@ L49-50 verbatim
/-- execution-specs Amsterdam `SYSTEM_MAX_SSTORES_PER_CALL`. -/
def amsterdamSystemMaxSstoresPerCall : Nat := 16


-- @@ L52-54 verbatim
/-- State gas charged for one zero-to-nonzero storage set. -/
def amsterdamStorageSetStateGas : Nat :=
  amsterdamStateBytesPerStorageSet * amsterdamCostPerStateByte


-- @@ L56-58 verbatim
/-- State gas precharged for one new-account creation. -/
def amsterdamNewAccountStateGas : Nat :=
  amsterdamStateBytesPerNewAccount * amsterdamCostPerStateByte


-- @@ L60-62 verbatim
/-- State gas precharged for one EIP-7702 authorization. -/
def amsterdamAuthStateGas : Nat :=
  (amsterdamStateBytesPerNewAccount + amsterdamStateBytesPerAuthBase) * amsterdamCostPerStateByte


-- @@ L64-67 verbatim
/-- Intrinsic state gas charged per EIP-7702 authorization. -/
def amsterdamAuthStateGasPerAuth : Nat :=
  (amsterdamStateBytesPerNewAccount + amsterdamStateBytesPerAuthBase)
    * amsterdamCostPerStateByte


-- @@ L69-71 verbatim
/-- State-gas reservoir passed to each Amsterdam system transaction. -/
def amsterdamSystemStateGasReservoir : Nat :=
  amsterdamStorageSetStateGas * amsterdamSystemMaxSstoresPerCall


-- @@ L73-80 verbatim
/-- Emit `li reg, bytes * COST_PER_STATE_BYTE` (the v0.4.0 state-gas charge). The conformance target
    (execution-specs tag `tests-zkevm@v0.4.0`) hardcodes `COST_PER_STATE_BYTE = 1530` (a CONSTANT — the
    scaling `state_gas_per_byte(gas_limit)` formula is a LATER eip-8037 draft and does NOT match the v0.4.0
    fixtures, whose header.gas_used = block_state = 184*1530 = 281520 is independent of the block gas limit).
    A previous refactor (drj99.1.2) made this a runtime `evm_state_gas_per_byte` load + multiply; that
    regressed every state-gas charge for v0.4.0, so it is reverted to the constant. -/
def liStateGasRuntime (reg : String) (bytes : Nat) : String :=
  "  li " ++ reg ++ ", " ++ toString (bytes * amsterdamCostPerStateByte) ++ "\n"


-- @@ L82-83 verbatim
def liAmsterdamStorageSetStateGas (reg : String) : String :=
  liStateGasRuntime reg amsterdamStateBytesPerStorageSet               -- 64 * cost


-- @@ L85-96 verbatim
/-- Assembly helper for the new-account state gas: `amsterdamStateBytesPerNewAccountV2` (**120**) bytes times
    `amsterdamCostPerStateByte` (1530) = **183600**, pinned by the `#guard` above.

    ⚠️ GH #10980: this docstring previously read *"112 bytes \* runtime cost"* with a trailing
    *"(was 120\*1530)"*, i.e. it named the WRONG count **and** presented the correct one as superseded. That is
    worse than a bare wrong number, because it pre-answers the question a reader would otherwise ask: taking it at
    face value gives `112 * 1530 = 171360`, which against the bare `183600` literals still emitted on the refund
    paths (`Dispatch.lean`, `ChildFrameCreateTail.lean`, `ChildFrameHandlers.lean`, `NoopHalt.lean`) assembles
    into a plausible "every charge-then-refund cycle leaks 12240 gas" — a gas defect that does not exist. Do not
    reintroduce a byte count here; cite the constant. -/
def liAmsterdamNewAccountStateGas (reg : String) : String :=
  liStateGasRuntime reg amsterdamStateBytesPerNewAccountV2             -- 120 * 1530 = 183600


-- @@ L98-100 verbatim
/-- Assembly helper for the per-authorization state gas ((112+23) bytes * runtime cost). -/
def liAmsterdamAuthStateGas (reg : String) : String :=
  liStateGasRuntime reg (amsterdamStateBytesPerNewAccountV2 + amsterdamStateBytesPerAuthBase)  -- 135 * cost


-- @@ L102-104 verbatim
/-- Assembly helper for the per-authorization state gas ((112+23) bytes * runtime cost). -/
def liAmsterdamAuthStateGasPerAuth (reg : String) : String :=
  liStateGasRuntime reg (amsterdamStateBytesPerNewAccountV2 + amsterdamStateBytesPerAuthBase)  -- 135 * cost


-- @@ L106-108 verbatim
/-- Assembly `li` helper for the system transaction regular gas budget. -/
def liAmsterdamSystemTransactionGas (reg : String) : String :=
  "  li " ++ reg ++ ", " ++ toString amsterdamSystemTransactionGas ++ "\n"


-- @@ L110-112 verbatim
/-- Assembly helper for the system transaction state-gas reservoir = (64 bytes/set * 16 sets) * runtime cost. -/
def liAmsterdamSystemStateGasReservoir (reg : String) : String :=
  liStateGasRuntime reg (amsterdamStateBytesPerStorageSet * amsterdamSystemMaxSstoresPerCall)  -- 1024 * cost


-- @@ L114-114 verbatim
#guard amsterdamStorageSetStateGas = 97920

-- @@ L115-115 verbatim
#guard amsterdamNewAccountStateGas = 183600

-- @@ L116-116 verbatim
#guard amsterdamAuthStateGas = 218790

-- @@ L117-117 verbatim
#guard amsterdamAuthStateGasPerAuth = 218790

-- @@ L118-118 verbatim
#guard amsterdamSystemStateGasReservoir = 1566720


-- @@ L120-120 verbatim
end EvmAsm.Codegen
