/-
  EvmAsm.Stateless.SpecRef.Gas

  Port of the blob-gas / gas-limit slice of
  `execution-specs/src/ethereum/forks/amsterdam/vm/gas.py`
  (`@tests-zkevm@v0.5.0`, `bd8c673`) needed by the seam shell's
  `validate_header` (bead `evm-asm-s1d19.3`):

  * the `GasCosts` / `StateGasCosts` constants (classes `GasCosts` and
    `StateGasCosts`) — the seam-shell subset plus the transaction-level
    EIP-8037 constants (Stack C stage 2); the per-opcode `OPCODE_*`
    table lands with the interpreter stage
  * `calculate_blob_gas_price` (function `calculate_blob_gas_price`)
  * `calculate_excess_blob_gas` (function `calculate_excess_blob_gas`)
  * `calculate_total_blob_gas` / `calculate_data_fee` (functions of the
    same names)
  * `calculate_memory_gas_cost`, `calculate_gas_extend_memory`,
    `calculate_message_call_gas`, `max_message_call_gas`,
    `init_code_cost` (functions of the same names)

  plus `taylor_exponential` and `ceil32` from `ethereum/utils/numeric.py`
  (`execution-specs/src/ethereum/utils/numeric.py`, function
  `taylor_exponential` and function `ceil32`).  `check_gas` /
  `charge_gas` / `charge_state_gas` mutate the `Evm` object and land
  with the interpreter stage.

  ## Modeling note: `taylor_exponential` fuel

  The Python loop runs until the accumulated term underflows to zero
  under integer division.  The term after step `i` is bounded by
  `factor·denominator·(numerator/denominator)^i / i!`, so its peak is
  ≤ `factor·denominator·e^(numerator/denominator)` and once
  `i ≥ 2·numerator/denominator` each step at least halves it; the loop
  therefore takes at most `4·(numerator/denominator) +
  log₂(factor·denominator) + O(1)` iterations, which the fuel strictly
  over-approximates.  The factor = 1 instance used by
  `calculate_blob_gas_price` is proved in `TaylorExponentialFuel`; that is the
  only in-repository call site.  Exhaustion is unreachable there; it rejects
  rather than returning a wrong value.
-/

module

public import EvmAsm.Stateless.SpecRef.Types
meta import EvmAsm.Stateless.SpecRef.Types


-- @@ L47-47 verbatim
@[expose] public section


-- @@ L49-49 verbatim
namespace EvmAsm.Stateless.SpecRef


-- @@ L51-52 verbatim
/-! ## `StateGasCosts` (`vm/gas.py`, class `StateGasCosts`) — EIP-8037
state-byte counts converted to gas via `COST_PER_STATE_BYTE`. -/


-- @@ L54-54 verbatim
namespace StateGasCosts


-- @@ L56-56 verbatim
def COST_PER_STATE_BYTE : Uint := 1530

-- @@ L57-57 verbatim
def STATE_BYTES_PER_NEW_ACCOUNT : Uint := 120

-- @@ L58-58 verbatim
def STATE_BYTES_PER_STORAGE_SET : Uint := 64

-- @@ L59-59 verbatim
def STATE_BYTES_PER_AUTH_BASE : Uint := 23

-- @@ L60-60 verbatim
def STORAGE_SET : Uint := STATE_BYTES_PER_STORAGE_SET * COST_PER_STATE_BYTE

-- @@ L61-61 verbatim
def NEW_ACCOUNT : Uint := STATE_BYTES_PER_NEW_ACCOUNT * COST_PER_STATE_BYTE

-- @@ L62-62 verbatim
def AUTH_BASE : Uint := STATE_BYTES_PER_AUTH_BASE * COST_PER_STATE_BYTE


-- @@ L64-64 verbatim
end StateGasCosts


-- @@ L66-66 verbatim
/-! ## `GasCosts` constants (`vm/gas.py`, class `GasCosts`) -/


-- @@ L68-68 verbatim
namespace GasCosts


-- @@ L70-70 verbatim
def BASE : Uint := 2

-- @@ L71-71 verbatim
def VERY_LOW : Uint := 3

-- @@ L72-72 verbatim
def LOW : Uint := 5

-- @@ L73-73 verbatim
def MID : Uint := 8

-- @@ L74-74 verbatim
def HIGH : Uint := 10

-- @@ L75-75 verbatim
def WARM_ACCESS : Uint := 100

-- @@ L76-76 verbatim
def COLD_ACCOUNT_ACCESS : Uint := 3000

-- @@ L77-77 verbatim
def COLD_STORAGE_ACCESS : Uint := 3000

-- @@ L78-78 verbatim
def STORAGE_WRITE : Uint := 10000

-- @@ L79-79 verbatim
def CALL_VALUE : Uint := 10300  -- ACCOUNT_WRITE + CALL_STIPEND

-- @@ L80-80 verbatim
def CALL_STIPEND : Uint := 2300

-- @@ L81-81 verbatim
def ACCOUNT_WRITE : Uint := 8000

-- @@ L82-82 verbatim
def CODE_DEPOSIT_PER_BYTE : Uint := 200

-- @@ L83-83 verbatim
def CODE_INIT_PER_WORD : Uint := 2

-- @@ L84-84 verbatim
def CREATE_ACCESS : Uint := ACCOUNT_WRITE + COLD_STORAGE_ACCESS

-- @@ L85-85 verbatim
def ZERO : Uint := 0

-- @@ L86-86 verbatim
def MEMORY_PER_WORD : Uint := 3

-- @@ L87-87 verbatim
def FAST_STEP : Uint := 5

-- @@ L88-89 verbatim
def REFUND_STORAGE_CLEAR : Nat :=
  (STORAGE_WRITE + COLD_STORAGE_ACCESS) * 4800 / 5000

-- @@ L90-90 verbatim
def PER_BLOB : U64 := 2^17

-- @@ L91-91 verbatim
def BLOB_SCHEDULE_TARGET : U64 := 14

-- @@ L92-92 verbatim
def BLOB_TARGET_GAS_PER_BLOCK : U64 := PER_BLOB * BLOB_SCHEDULE_TARGET

-- @@ L93-93 verbatim
def BLOB_BASE_COST : Uint := 2^13

-- @@ L94-94 verbatim
def BLOB_SCHEDULE_MAX : U64 := 21

-- @@ L95-95 verbatim
def BLOB_MIN_GASPRICE : Uint := 1

-- @@ L96-96 verbatim
def BLOB_BASE_FEE_UPDATE_FRACTION : Uint := 11684671

-- @@ L97-97 verbatim
def TX_BASE : Uint := 12000

-- @@ L98-98 verbatim
def TX_CREATE : Uint := 32000

-- @@ L99-99 verbatim
def TX_VALUE_COST : Uint := 4244

-- @@ L100-100 verbatim
def TRANSFER_LOG_COST : Uint := 1756

-- @@ L101-101 verbatim
def TX_DATA_TOKEN_STANDARD : Uint := 4

-- @@ L102-102 verbatim
def TX_DATA_TOKEN_FLOOR : Uint := 16

-- @@ L103-103 verbatim
def TX_ACCESS_LIST_ADDRESS : Uint := COLD_ACCOUNT_ACCESS

-- @@ L104-104 verbatim
def TX_ACCESS_LIST_STORAGE_KEY : Uint := COLD_STORAGE_ACCESS

-- @@ L105-105 verbatim
def PRECOMPILE_ECRECOVER : Uint := 3000

-- @@ L106-106 verbatim
def AUTH_TUPLE_BYTES : Uint := 101

-- @@ L107-109 verbatim
def REGULAR_PER_AUTH_BASE_COST : Uint :=
  AUTH_TUPLE_BYTES * TX_DATA_TOKEN_FLOOR + PRECOMPILE_ECRECOVER
    + COLD_ACCOUNT_ACCESS + 2 * WARM_ACCESS

-- @@ L110-110 verbatim
def LIMIT_ADJUSTMENT_FACTOR : Uint := 1024

-- @@ L111-111 verbatim
def LIMIT_MINIMUM : Uint := 5000


-- @@ L113-113 verbatim
end GasCosts


-- @@ L115-115 verbatim
/-! ## `ceil32` (`ethereum/utils/numeric.py`, function `ceil32`) -/


-- @@ L117-119 verbatim
/-- The smallest multiple of 32 that is ≥ `value`. -/
def ceil32 (value : Uint) : Uint :=
  if value % 32 == 0 then value else value + 32 - value % 32


-- @@ L121-121 verbatim
/-! ## `taylor_exponential` (`ethereum/utils/numeric.py`, function `taylor_exponential`) -/


-- @@ L123-129 verbatim
def taylorAux (numerator denominator : Nat) :
    Nat → Nat → Nat → Nat → Except SpecError Nat
  | _, _, 0, output => pure output
  | 0, _, _, _ => throw (.mptWriteError "taylor_exponential: fuel exhausted")
  | fuel + 1, i, acc, output =>
      taylorAux numerator denominator fuel (i + 1)
        (acc * numerator / (denominator * i)) (output + acc)


-- @@ L131-138 verbatim
/-- `factor · e^(numerator/denominator)`, Taylor-approximated in integer
    arithmetic (see the fuel note in the header). -/
def taylor_exponential (factor numerator denominator : Uint) :
    Except SpecError Uint := do
  let output ← taylorAux numerator denominator
    (4 * (numerator / denominator) + Nat.log2 (factor * denominator + 2) + 8)
    1 (factor * denominator) 0
  pure (output / denominator)


-- @@ L140-140 verbatim
/-! ## `calculate_blob_gas_price` (function `calculate_blob_gas_price`) -/


-- @@ L142-145 verbatim
/-- The blob gas price for a block. -/
def calculate_blob_gas_price (excess_blob_gas : U64) : Except SpecError Uint :=
  taylor_exponential GasCosts.BLOB_MIN_GASPRICE excess_blob_gas
    GasCosts.BLOB_BASE_FEE_UPDATE_FRACTION


-- @@ L147-147 verbatim
/-! ## `calculate_excess_blob_gas` (function `calculate_excess_blob_gas`) -/


-- @@ L149-170 verbatim
/-- The excess blob gas for the current block from the parent header
    (the parent is always a decoded `Header | PreviousForkHeader` on
    this path, so the Python at-fork zero defaults never apply). -/
def calculate_excess_blob_gas (parent_header : Header) :
    Except SpecError U64 := do
  let excess_blob_gas := parent_header.excessBlobGas
  let blob_gas_used := parent_header.blobGasUsed
  let base_fee_per_gas := parent_header.baseFeePerGas
  let parent_blob_gas := excess_blob_gas + blob_gas_used
  if parent_blob_gas < GasCosts.BLOB_TARGET_GAS_PER_BLOCK then
    pure 0
  else
    let target_blob_gas_price := GasCosts.PER_BLOB *
      (← calculate_blob_gas_price excess_blob_gas)
    let base_blob_tx_price := GasCosts.BLOB_BASE_COST * base_fee_per_gas
    if base_blob_tx_price > target_blob_gas_price then
      let blob_schedule_delta :=
        GasCosts.BLOB_SCHEDULE_MAX - GasCosts.BLOB_SCHEDULE_TARGET
      pure (excess_blob_gas
        + blob_gas_used * blob_schedule_delta / GasCosts.BLOB_SCHEDULE_MAX)
    else
      pure (parent_blob_gas - GasCosts.BLOB_TARGET_GAS_PER_BLOCK)


-- @@ L172-172 verbatim
/-! ## Memory / call gas (`vm/gas.py`) -/


-- @@ L174-178 verbatim
/-- `ExtendMemory` (class `ExtendMemory`). -/
structure ExtendMemory where
  cost : Uint
  expandBy : Uint
  deriving Repr, BEq


-- @@ L180-184 verbatim
/-- `MessageCallGas` (class `MessageCallGas`). -/
structure MessageCallGas where
  cost : Uint
  subCall : Uint
  deriving Repr, BEq


-- @@ L186-189 verbatim
/-- `calculate_memory_gas_cost(size_in_bytes)`. -/
def calculate_memory_gas_cost (size_in_bytes : Uint) : Uint :=
  let size_in_words := ceil32 size_in_bytes / 32
  size_in_words * GasCosts.MEMORY_PER_WORD + size_in_words ^ 2 / 512


-- @@ L191-208 verbatim
/-- `calculate_gas_extend_memory(memory, extensions)` — over the current
    memory SIZE (the Python takes the bytearray; only its length is
    read). -/
def calculate_gas_extend_memory (memory_size : Uint)
    (extensions : List (U256 × U256)) : ExtendMemory := Id.run do
  let mut size_to_extend : Uint := 0
  let mut to_be_paid : Uint := 0
  let mut current_size := memory_size
  for (start_position, size) in extensions do
    if size == 0 then continue
    let before_size := ceil32 current_size
    let after_size := ceil32 (start_position + size)
    if after_size ≤ before_size then continue
    size_to_extend := size_to_extend + (after_size - before_size)
    to_be_paid := to_be_paid +
      (calculate_memory_gas_cost after_size - calculate_memory_gas_cost before_size)
    current_size := after_size
  pure { cost := to_be_paid, expandBy := size_to_extend }


-- @@ L210-211 verbatim
/-- `max_message_call_gas(gas)`: the 63/64 rule. -/
def max_message_call_gas (gas : Uint) : Uint := gas - gas / 64


-- @@ L213-223 verbatim
/-- `calculate_message_call_gas(value, gas, gas_left, memory_cost,
    extra_gas, call_stipend)`. -/
def calculate_message_call_gas (value : U256) (gas gas_left memory_cost
    extra_gas : Uint) (call_stipend : Uint := GasCosts.CALL_STIPEND) :
    MessageCallGas :=
  let call_stipend := if value == 0 then 0 else call_stipend
  if gas_left < extra_gas + memory_cost then
    { cost := gas + extra_gas, subCall := gas + call_stipend }
  else
    let gas := min gas (max_message_call_gas (gas_left - memory_cost - extra_gas))
    { cost := gas + extra_gas, subCall := gas + call_stipend }


-- @@ L225-227 verbatim
/-- `init_code_cost(init_code_length)`. -/
def init_code_cost (init_code_length : Uint) : Uint :=
  GasCosts.CODE_INIT_PER_WORD * ceil32 init_code_length / 32


-- @@ L229-259 verbatim
/-! ## Sanity checks (cross-checked against the Python spec at `bd8c673`) -/

#guard ceil32 0 == 0
#guard ceil32 1 == 32
#guard ceil32 32 == 32
#guard ceil32 33 == 64
#guard GasCosts.REGULAR_PER_AUTH_BASE_COST == 7816
#guard GasCosts.REFUND_STORAGE_CLEAR == 12480
#guard StateGasCosts.STORAGE_SET == 97920
#guard StateGasCosts.NEW_ACCOUNT == 183600
#guard StateGasCosts.AUTH_BASE == 35190

-- memory gas: one word = 3; 32 KiB = 3072 + 1048576/512·… (Python:
-- calculate_memory_gas_cost(32768) = 5120).
#guard calculate_memory_gas_cost 32 == 3
#guard calculate_memory_gas_cost 32768 == 5120
#guard (calculate_gas_extend_memory 0 [(0, 64)])
  == { cost := 6, expandBy := 64 }
#guard (calculate_gas_extend_memory 64 [(0, 32), (32, 64), (0, 0)])
  == { cost := 3, expandBy := 32 }
#guard max_message_call_gas 6400 == 6300

-- calculate_blob_gas_price: zero excess → min price; two Python-checked
-- points on the exponential.
#guard (calculate_blob_gas_price 0).toOption == some 1
#guard (calculate_blob_gas_price 10000000).toOption == some 2
#guard (calculate_blob_gas_price 100000000).toOption == some 5209

-- calculate_excess_blob_gas on synthetic parent headers (Python-checked):
-- below target → 0; above target with cheap base fee → linear branch;
-- expensive base fee → schedule-delta branch.

-- @@ L260-277 verbatim
private def gasTestHeader (ebg bgu bf : Nat) : Header :=
  { isCurrentFork := true, parentHash := List.replicate 32 0,
    ommersHash := List.replicate 32 0, coinbase := List.replicate 20 0,
    stateRoot := List.replicate 32 0, transactionsRoot := List.replicate 32 0,
    receiptRoot := List.replicate 32 0, bloom := List.replicate 256 0,
    difficulty := 0, number := 1, gasLimit := 30000000, gasUsed := 0,
    timestamp := 0, extraData := [], prevRandao := List.replicate 32 0,
    nonce := List.replicate 8 0, baseFeePerGas := bf,
    withdrawalsRoot := List.replicate 32 0, blobGasUsed := bgu,
    excessBlobGas := ebg, parentBeaconBlockRoot := List.replicate 32 0,
    requestsHash := List.replicate 32 0,
    blockAccessListHash := List.replicate 32 0, slotNumber := 1 }

#guard (calculate_excess_blob_gas (gasTestHeader 0 0 7)).toOption == some 0
#guard (calculate_excess_blob_gas (gasTestHeader 2000000 500000 7)).toOption
  == some 664992
#guard (calculate_excess_blob_gas (gasTestHeader 0 2621440 1000000000)).toOption
  == some 873813


-- @@ L279-279 verbatim
end EvmAsm.Stateless.SpecRef
