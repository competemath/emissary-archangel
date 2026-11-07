/-
  EvmAsm.Stateless.SpecRef.InstructionsCore

  Port of the non-system instruction families of
  `execution-specs/src/ethereum/forks/amsterdam/vm/instructions/`
  (`@tests-zkevm@v0.5.0`, `bd8c673`) — bead `evm-asm-s1d19.5`, Stack C
  stage 4:

  * `arithmetic.py` — `add`, `sub`, `mul`, `div`, `sdiv`, `mod`,
    `smod`, `addmod`, `mulmod`, `exp`, `signextend` (functions of the
    same names)
  * `comparison.py` — `less_than`, `signed_less_than`, `greater_than`,
    `signed_greater_than`, `equal`, `is_zero`
  * `bitwise.py` — `bitwise_and`, `bitwise_or`, `bitwise_xor`,
    `bitwise_not`, `get_byte`, `bitwise_shl`, `bitwise_shr`,
    `bitwise_sar`, `count_leading_zeros`
  * `keccak.py` — `keccak` (function `keccak`)
  * `control_flow.py` — `stop`, `jump`, `jumpi`, `pc`, `gas_left`,
    `jumpdest`
  * `memory.py` — `mstore`, `mstore8`, `mload`, `msize`, `mcopy`
  * `stack.py` (instructions) — `pop`, `push_n`, `dup_n`, `swap_n`,
    `dupn`, `swapn`, `exchange` (functions of the same names)
  * `log.py` — `log_n` (function `log_n`)
  * `storage.py` — `sload`, `sstore`, `tload`, `tstore`

  plus the per-opcode `OPCODE_*` gas constants (`vm/gas.py`, class
  `GasCosts`), added here into the open `GasCosts` namespace.

  Values are unbounded `Nat` capped explicitly at 2²⁵⁶ (`wrap256` at
  every arithmetic site, mirroring the Python `U256` wrapping ops);
  the stack holds its TOP at the list HEAD (Python appends at the end),
  so Python's `stack[-1 - n]` is index `n` here.
-/

module

public import EvmAsm.Stateless.SpecRef.Vm


-- @@ L39-39 verbatim
@[expose] public section


-- @@ L41-41 verbatim
namespace EvmAsm.Stateless.SpecRef


-- @@ L43-43 verbatim
namespace GasCosts


-- @@ L45-45 verbatim
def OPCODE_ADD : Uint := 3

-- @@ L46-46 verbatim
def OPCODE_ADDMOD : Uint := 8

-- @@ L47-47 verbatim
def OPCODE_AND : Uint := 3

-- @@ L48-48 verbatim
def OPCODE_BYTE : Uint := 3

-- @@ L49-49 verbatim
def OPCODE_CALLDATALOAD : Uint := 3

-- @@ L50-50 verbatim
def OPCODE_CLZ : Uint := 5

-- @@ L51-51 verbatim
def OPCODE_COPY_PER_WORD : Uint := 3

-- @@ L52-52 verbatim
def OPCODE_DIV : Uint := 5

-- @@ L53-53 verbatim
def OPCODE_DUP : Uint := 3

-- @@ L54-54 verbatim
def OPCODE_DUPN : Uint := 3

-- @@ L55-55 verbatim
def OPCODE_EQ : Uint := 3

-- @@ L56-56 verbatim
def OPCODE_EXCHANGE : Uint := 3

-- @@ L57-57 verbatim
def OPCODE_EXP_BASE : Uint := 10

-- @@ L58-58 verbatim
def OPCODE_EXP_PER_BYTE : Uint := 50

-- @@ L59-59 verbatim
def OPCODE_GAS : Uint := 2

-- @@ L60-60 verbatim
def OPCODE_GT : Uint := 3

-- @@ L61-61 verbatim
def OPCODE_ISZERO : Uint := 3

-- @@ L62-62 verbatim
def OPCODE_JUMP : Uint := 8

-- @@ L63-63 verbatim
def OPCODE_JUMPDEST : Uint := 1

-- @@ L64-64 verbatim
def OPCODE_JUMPI : Uint := 10

-- @@ L65-65 verbatim
def OPCODE_KECCAK256_BASE : Uint := 30

-- @@ L66-66 verbatim
def OPCODE_KECCAK256_PER_WORD : Uint := 6

-- @@ L67-67 verbatim
def OPCODE_LOG_BASE : Uint := 375

-- @@ L68-68 verbatim
def OPCODE_LOG_DATA_PER_BYTE : Uint := 8

-- @@ L69-69 verbatim
def OPCODE_LOG_TOPIC : Uint := 375

-- @@ L70-70 verbatim
def OPCODE_LT : Uint := 3

-- @@ L71-71 verbatim
def OPCODE_MCOPY_BASE : Uint := 3

-- @@ L72-72 verbatim
def OPCODE_MLOAD_BASE : Uint := 3

-- @@ L73-73 verbatim
def OPCODE_MOD : Uint := 5

-- @@ L74-74 verbatim
def OPCODE_MSIZE : Uint := 2

-- @@ L75-75 verbatim
def OPCODE_MSTORE8_BASE : Uint := 3

-- @@ L76-76 verbatim
def OPCODE_MSTORE_BASE : Uint := 3

-- @@ L77-77 verbatim
def OPCODE_MUL : Uint := 5

-- @@ L78-78 verbatim
def OPCODE_MULMOD : Uint := 8

-- @@ L79-79 verbatim
def OPCODE_NOT : Uint := 3

-- @@ L80-80 verbatim
def OPCODE_OR : Uint := 3

-- @@ L81-81 verbatim
def OPCODE_PC : Uint := 2

-- @@ L82-82 verbatim
def OPCODE_POP : Uint := 2

-- @@ L83-83 verbatim
def OPCODE_PUSH : Uint := 3

-- @@ L84-84 verbatim
def OPCODE_PUSH0 : Uint := 2

-- @@ L85-85 verbatim
def OPCODE_SAR : Uint := 3

-- @@ L86-86 verbatim
def OPCODE_SDIV : Uint := 5

-- @@ L87-87 verbatim
def OPCODE_SGT : Uint := 3

-- @@ L88-88 verbatim
def OPCODE_SHL : Uint := 3

-- @@ L89-89 verbatim
def OPCODE_SHR : Uint := 3

-- @@ L90-90 verbatim
def OPCODE_SIGNEXTEND : Uint := 5

-- @@ L91-91 verbatim
def OPCODE_SLT : Uint := 3

-- @@ L92-92 verbatim
def OPCODE_SMOD : Uint := 5

-- @@ L93-93 verbatim
def OPCODE_SUB : Uint := 3

-- @@ L94-94 verbatim
def OPCODE_SWAP : Uint := 3

-- @@ L95-95 verbatim
def OPCODE_SWAPN : Uint := 3

-- @@ L96-96 verbatim
def OPCODE_TLOAD : Uint := 100

-- @@ L97-97 verbatim
def OPCODE_TSTORE : Uint := 100

-- @@ L98-98 verbatim
def OPCODE_XOR : Uint := 3


-- @@ L100-100 verbatim
end GasCosts


-- @@ L102-102 verbatim
/-! ## U256 helpers (`ethereum_types.numeric.U256`) -/


-- @@ L104-104 verbatim
def U256_MOD : Nat := 2^256

-- @@ L105-105 verbatim
def U256_MAX : Nat := 2^256 - 1


-- @@ L107-108 verbatim
/-- Wrap into the U256 range (`wrapping_add`/`sub`/`mul` etc.). -/
def wrap256 (n : Nat) : U256 := n % U256_MOD


-- @@ L110-112 verbatim
/-- `U256.to_signed()`: two's-complement read. -/
def toSigned (x : U256) : Int :=
  if x < 2^255 then (x : Int) else (x : Int) - (U256_MOD : Int)


-- @@ L114-116 verbatim
/-- `U256.from_signed(v)`: two's-complement write. -/
def fromSigned (v : Int) : U256 :=
  (v % (U256_MOD : Int)).toNat


-- @@ L118-119 verbatim
/-- `x.to_be_bytes32()`. -/
def toBeBytes32 (x : U256) : Bytes := natToBytesBE 32 x


-- @@ L121-123 verbatim
/-- Advance the program counter. -/
def pcAdd (n : Nat) : EvmM Unit :=
  EvmM.modifyEvm (fun e => { e with pc := e.pc + n })


-- @@ L125-131 verbatim
/-- The shared shape of a binary op: pop 2, charge, push, `pc += 1`. -/
def binOp (gas : Uint) (f : U256 → U256 → U256) : EvmM Unit := do
  let x ← stackPop
  let y ← stackPop
  charge_gas gas
  stackPush (f x y)
  pcAdd 1


-- @@ L133-137 verbatim
def unOp (gas : Uint) (f : U256 → U256) : EvmM Unit := do
  let x ← stackPop
  charge_gas gas
  stackPush (f x)
  pcAdd 1


-- @@ L139-139 verbatim
/-! ## `arithmetic.py` -/


-- @@ L141-141 verbatim
def iAdd : EvmM Unit := binOp GasCosts.OPCODE_ADD (fun x y => wrap256 (x + y))

-- @@ L142-142 verbatim
def iSub : EvmM Unit := binOp GasCosts.OPCODE_SUB (fun x y => wrap256 (U256_MOD + x - y))

-- @@ L143-143 verbatim
def iMul : EvmM Unit := binOp GasCosts.OPCODE_MUL (fun x y => wrap256 (x * y))

-- @@ L144-144 verbatim
def iDiv : EvmM Unit := binOp GasCosts.OPCODE_DIV (fun x y => if y == 0 then 0 else x / y)


-- @@ L146-155 verbatim
/-- `sdiv`: truncated signed division with the `-2²⁵⁵ / -1` special
    case. -/
def iSdiv : EvmM Unit := binOp GasCosts.OPCODE_SDIV (fun x y =>
  let a := toSigned x
  let b := toSigned y
  if b == 0 then 0
  else if a == -(2^255 : Int) && b == -1 then fromSigned (-(2^255 : Int))
  else
    let q : Int := (if a * b < 0 then -1 else 1) * ((a.natAbs / b.natAbs : Nat) : Int)
    fromSigned q)


-- @@ L157-157 verbatim
def iMod : EvmM Unit := binOp GasCosts.OPCODE_MOD (fun x y => if y == 0 then 0 else x % y)


-- @@ L159-164 verbatim
/-- `smod`: sign follows the dividend. -/
def iSmod : EvmM Unit := binOp GasCosts.OPCODE_SMOD (fun x y =>
  let a := toSigned x
  let b := toSigned y
  if b == 0 then 0
  else fromSigned ((if a < 0 then -1 else 1) * ((a.natAbs % b.natAbs : Nat) : Int)))


-- @@ L166-172 verbatim
def iAddmod : EvmM Unit := do
  let x ← stackPop
  let y ← stackPop
  let z ← stackPop
  charge_gas GasCosts.OPCODE_ADDMOD
  stackPush (if z == 0 then 0 else (x + y) % z)
  pcAdd 1


-- @@ L174-180 verbatim
def iMulmod : EvmM Unit := do
  let x ← stackPop
  let y ← stackPop
  let z ← stackPop
  charge_gas GasCosts.OPCODE_MULMOD
  stackPush (if z == 0 then 0 else (x * y) % z)
  pcAdd 1


-- @@ L182-189 verbatim
def iExp : EvmM Unit := do
  let base ← stackPop
  let exponent ← stackPop
  let exponent_bytes := (Nat.log2 (max exponent 1) + 1 + 7) / 8
  let exponent_bytes := if exponent == 0 then 0 else exponent_bytes
  charge_gas (GasCosts.OPCODE_EXP_BASE + GasCosts.OPCODE_EXP_PER_BYTE * exponent_bytes)
  stackPush (EvmAsm.Rv64.Accel.powMod base exponent U256_MOD)
  pcAdd 1


-- @@ L191-197 verbatim
def iSignextend : EvmM Unit := binOp GasCosts.OPCODE_SIGNEXTEND (fun byte_num value =>
  if byte_num > 31 then value
  else
    let bits := (byte_num + 1) * 8
    let low := value % 2^bits
    if low < 2^(bits - 1) then low
    else low + (U256_MOD - 2^bits))


-- @@ L199-199 verbatim
/-! ## `comparison.py` -/


-- @@ L201-201 verbatim
def boolPush (b : Bool) : U256 := if b then 1 else 0


-- @@ L203-203 verbatim
def iLt : EvmM Unit := binOp GasCosts.OPCODE_LT (fun x y => boolPush (x < y))

-- @@ L204-204 verbatim
def iGt : EvmM Unit := binOp GasCosts.OPCODE_GT (fun x y => boolPush (x > y))

-- @@ L205-205 verbatim
def iSlt : EvmM Unit := binOp GasCosts.OPCODE_SLT (fun x y => boolPush (toSigned x < toSigned y))

-- @@ L206-206 verbatim
def iSgt : EvmM Unit := binOp GasCosts.OPCODE_SGT (fun x y => boolPush (toSigned x > toSigned y))

-- @@ L207-207 verbatim
def iEq : EvmM Unit := binOp GasCosts.OPCODE_EQ (fun x y => boolPush (x == y))

-- @@ L208-208 verbatim
def iIszero : EvmM Unit := unOp GasCosts.OPCODE_ISZERO (fun x => boolPush (x == 0))


-- @@ L210-210 verbatim
/-! ## `bitwise.py` -/


-- @@ L212-212 verbatim
def iAnd : EvmM Unit := binOp GasCosts.OPCODE_AND (fun x y => x &&& y)

-- @@ L213-213 verbatim
def iOr : EvmM Unit := binOp GasCosts.OPCODE_OR (fun x y => x ||| y)

-- @@ L214-214 verbatim
def iXor : EvmM Unit := binOp GasCosts.OPCODE_XOR (fun x y => x ^^^ y)

-- @@ L215-215 verbatim
def iNot : EvmM Unit := unOp GasCosts.OPCODE_NOT (fun x => U256_MAX - x)


-- @@ L217-219 verbatim
def iByte : EvmM Unit := binOp GasCosts.OPCODE_BYTE (fun byte_index word =>
  if byte_index ≥ 32 then 0
  else (word >>> ((31 - byte_index) * 8)) &&& 0xFF)


-- @@ L221-222 verbatim
def iShl : EvmM Unit := binOp GasCosts.OPCODE_SHL (fun shift value =>
  if shift < 256 then wrap256 (value <<< shift) else 0)


-- @@ L224-225 verbatim
def iShr : EvmM Unit := binOp GasCosts.OPCODE_SHR (fun shift value =>
  if shift < 256 then value >>> shift else 0)


-- @@ L227-231 verbatim
def iSar : EvmM Unit := binOp GasCosts.OPCODE_SAR (fun shift value =>
  let sv := toSigned value
  -- Python `>>` on int is an arithmetic shift = floor division.
  if shift < 256 then fromSigned (Int.fdiv sv (2^shift))
  else if sv ≥ 0 then 0 else U256_MAX)


-- @@ L233-236 verbatim
/-- `count_leading_zeros` (EIP-7939). -/
def iClz : EvmM Unit := unOp GasCosts.OPCODE_CLZ (fun x =>
  let bit_length := if x == 0 then 0 else Nat.log2 x + 1
  256 - bit_length)


-- @@ L238-238 verbatim
/-! ## `keccak.py` -/


-- @@ L240-251 verbatim
def iKeccak : EvmM Unit := do
  let memory_start_index ← stackPop
  let size ← stackPop
  let words := ceil32 size / 32
  let extend ← (fun e => calculate_gas_extend_memory e.memory.length
    [(memory_start_index, size)]) <$> EvmM.getEvm
  charge_gas (GasCosts.OPCODE_KECCAK256_BASE
    + GasCosts.OPCODE_KECCAK256_PER_WORD * words + extend.cost)
  extendMemory extend.expandBy
  let data := memory_read_bytes (← EvmM.getEvm).memory memory_start_index size
  stackPush (bytesBEtoNat (keccak256 data))
  pcAdd 1


-- @@ L253-253 verbatim
/-! ## `control_flow.py` -/


-- @@ L255-257 verbatim
def iStop : EvmM Unit := do
  EvmM.modifyEvm (fun e => { e with running := false })
  pcAdd 1


-- @@ L259-264 verbatim
def iJump : EvmM Unit := do
  let jump_dest ← stackPop
  charge_gas GasCosts.OPCODE_JUMP
  if !(← EvmM.getEvm).validJumpDestinations.contains jump_dest then
    throw .invalidJumpDest
  EvmM.modifyEvm (fun e => { e with pc := jump_dest })


-- @@ L266-275 verbatim
def iJumpi : EvmM Unit := do
  let jump_dest ← stackPop
  let conditional_value ← stackPop
  charge_gas GasCosts.OPCODE_JUMPI
  if conditional_value == 0 then
    pcAdd 1
  else if !(← EvmM.getEvm).validJumpDestinations.contains jump_dest then
    throw .invalidJumpDest
  else
    EvmM.modifyEvm (fun e => { e with pc := jump_dest })


-- @@ L277-280 verbatim
def iPc : EvmM Unit := do
  charge_gas GasCosts.OPCODE_PC
  stackPush (← EvmM.getEvm).pc
  pcAdd 1


-- @@ L282-285 verbatim
def iGas : EvmM Unit := do
  charge_gas GasCosts.OPCODE_GAS
  stackPush (← EvmM.getEvm).gasLeft
  pcAdd 1


-- @@ L287-289 verbatim
def iJumpdest : EvmM Unit := do
  charge_gas GasCosts.OPCODE_JUMPDEST
  pcAdd 1


-- @@ L291-291 verbatim
/-! ## `memory.py` (instructions) -/


-- @@ L293-298 verbatim
def chargeWithMemory (base : Uint) (extensions : List (U256 × U256)) :
    EvmM Unit := do
  let extend ← (fun e => calculate_gas_extend_memory e.memory.length extensions)
    <$> EvmM.getEvm
  charge_gas (base + extend.cost)
  extendMemory extend.expandBy


-- @@ L300-306 verbatim
def iMstore : EvmM Unit := do
  let start_position ← stackPop
  let value ← stackPop
  chargeWithMemory GasCosts.OPCODE_MSTORE_BASE [(start_position, 32)]
  EvmM.modifyEvm (fun e =>
    { e with memory := memory_write e.memory start_position (toBeBytes32 value) })
  pcAdd 1


-- @@ L308-315 verbatim
def iMstore8 : EvmM Unit := do
  let start_position ← stackPop
  let value ← stackPop
  chargeWithMemory GasCosts.OPCODE_MSTORE8_BASE [(start_position, 1)]
  EvmM.modifyEvm (fun e =>
    let m := memory_write e.memory start_position [BitVec.ofNat 8 (value &&& 0xFF)]
    { e with memory := m })
  pcAdd 1


-- @@ L317-323 verbatim
def iMload : EvmM Unit := do
  let start_position ← stackPop
  chargeWithMemory GasCosts.OPCODE_MLOAD_BASE [(start_position, 32)]
  let value := bytesBEtoNat
    (memory_read_bytes (← EvmM.getEvm).memory start_position 32)
  stackPush value
  pcAdd 1


-- @@ L325-328 verbatim
def iMsize : EvmM Unit := do
  charge_gas GasCosts.OPCODE_MSIZE
  stackPush (← EvmM.getEvm).memory.length
  pcAdd 1


-- @@ L330-340 verbatim
def iMcopy : EvmM Unit := do
  let destination ← stackPop
  let source ← stackPop
  let length ← stackPop
  let words := ceil32 length / 32
  chargeWithMemory (GasCosts.OPCODE_MCOPY_BASE + GasCosts.OPCODE_COPY_PER_WORD * words)
    [(source, length), (destination, length)]
  EvmM.modifyEvm (fun e =>
    let m := memory_write e.memory destination (memory_read_bytes e.memory source length)
    { e with memory := m })
  pcAdd 1


-- @@ L342-342 verbatim
/-! ## `stack.py` (instructions) -/


-- @@ L344-347 verbatim
def iPop : EvmM Unit := do
  let _ ← stackPop
  charge_gas GasCosts.OPCODE_POP
  pcAdd 1


-- @@ L349-354 verbatim
/-- `push_n(evm, num_bytes)` — PUSH0 (2 gas) through PUSH32. -/
def iPushN (num_bytes : Nat) : EvmM Unit := do
  charge_gas (if num_bytes == 0 then GasCosts.OPCODE_PUSH0 else GasCosts.OPCODE_PUSH)
  let e ← EvmM.getEvm
  stackPush (bytesBEtoNat (buffer_read e.code (e.pc + 1) num_bytes))
  pcAdd (1 + num_bytes)


-- @@ L356-362 verbatim
/-- `dup_n(evm, item_number)` — `item_number` 0-indexed from the top. -/
def iDupN (item_number : Nat) : EvmM Unit := do
  charge_gas GasCosts.OPCODE_DUP
  let e ← EvmM.getEvm
  if item_number ≥ e.stack.length then throw .stackUnderflow
  stackPush (e.stack.getD item_number 0)
  pcAdd 1


-- @@ L364-367 verbatim
def listSwap (l : List U256) (i j : Nat) : List U256 :=
  let a := l.getD i 0
  let b := l.getD j 0
  (l.set i b).set j a


-- @@ L369-376 verbatim
/-- `swap_n(evm, item_number)` — swap top with position `item_number`
    from the top (1-indexed distance). -/
def iSwapN (item_number : Nat) : EvmM Unit := do
  charge_gas GasCosts.OPCODE_SWAP
  let e ← EvmM.getEvm
  if item_number ≥ e.stack.length then throw .stackUnderflow
  EvmM.modifyEvm (fun e => { e with stack := listSwap e.stack 0 item_number })
  pcAdd 1


-- @@ L378-389 verbatim
/-- `dupn(evm)` (EIP-663 DUPN): decoded immediate `n`, duplicates
    position `n` from the top (1-indexed). -/
def iDupn : EvmM Unit := do
  charge_gas GasCosts.OPCODE_DUPN
  let e ← EvmM.getEvm
  let imm := ((buffer_read e.code (e.pc + 1) 1).headD 0).toNat
  let item_number ← match decode_single imm with
    | .ok n => pure n
    | .error err => throw err
  if item_number > e.stack.length then throw .stackUnderflow
  stackPush (e.stack.getD (item_number - 1) 0)
  pcAdd 2


-- @@ L391-401 verbatim
/-- `swapn(evm)`: swap top with position `n+1`. -/
def iSwapn : EvmM Unit := do
  charge_gas GasCosts.OPCODE_SWAPN
  let e ← EvmM.getEvm
  let imm := ((buffer_read e.code (e.pc + 1) 1).headD 0).toNat
  let item_number ← match decode_single imm with
    | .ok n => pure n
    | .error err => throw err
  if item_number + 1 > e.stack.length then throw .stackUnderflow
  EvmM.modifyEvm (fun e => { e with stack := listSwap e.stack 0 item_number })
  pcAdd 2


-- @@ L403-413 verbatim
/-- `exchange(evm)`: swap positions `n+1` and `m+1`. -/
def iExchange : EvmM Unit := do
  charge_gas GasCosts.OPCODE_EXCHANGE
  let e ← EvmM.getEvm
  let imm := ((buffer_read e.code (e.pc + 1) 1).headD 0).toNat
  let (n, m) ← match decode_pair imm with
    | .ok nm => pure nm
    | .error err => throw err
  if max n m + 1 > e.stack.length then throw .stackUnderflow
  EvmM.modifyEvm (fun e => { e with stack := listSwap e.stack n m })
  pcAdd 2


-- @@ L415-415 verbatim
/-! ## `log.py` -/


-- @@ L417-436 verbatim
/-- `log_n(evm, num_topics)`. -/
def iLogN (num_topics : Nat) : EvmM Unit := do
  let memory_start_index ← stackPop
  let size ← stackPop
  let topics ← (List.range num_topics).mapM (fun _ => do
    pure (toBeBytes32 (← stackPop)))
  let extend ← (fun e => calculate_gas_extend_memory e.memory.length
    [(memory_start_index, size)]) <$> EvmM.getEvm
  charge_gas (GasCosts.OPCODE_LOG_BASE
    + GasCosts.OPCODE_LOG_DATA_PER_BYTE * size
    + GasCosts.OPCODE_LOG_TOPIC * num_topics + extend.cost)
  extendMemory extend.expandBy
  let e ← EvmM.getEvm
  if e.message.isStatic then throw .writeInStaticContext
  let log : Log :=
    { address := e.message.currentTarget
      topics := topics
      data := memory_read_bytes e.memory memory_start_index size }
  EvmM.modifyEvm (fun e => { e with logs := e.logs ++ [log] })
  pcAdd 1


-- @@ L438-438 verbatim
/-! ## `storage.py` -/


-- @@ L440-442 verbatim
/-- Warm/cold storage-key accounting shared by `sload`/`sstore`. -/
def isWarmStorageKey (key : Address × Bytes32) : EvmM Bool := do
  pure ((← EvmM.getEvm).accessedStorageKeys.contains key)


-- @@ L444-446 verbatim
def warmStorageKey (key : Address × Bytes32) : EvmM Unit :=
  EvmM.modifyEvm (fun e =>
    { e with accessedStorageKeys := setAdd e.accessedStorageKeys key })


-- @@ L448-457 verbatim
def iSload : EvmM Unit := do
  let key := toBeBytes32 (← stackPop)
  let target := (← EvmM.getEvm).message.currentTarget
  if ← isWarmStorageKey (target, key) then
    charge_gas GasCosts.WARM_ACCESS
  else
    warmStorageKey (target, key)
    charge_gas GasCosts.COLD_STORAGE_ACCESS
  stackPush (← EvmM.liftTx (getStorage target key))
  pcAdd 1


-- @@ L459-498 verbatim
def iSstore : EvmM Unit := do
  if (← EvmM.getEvm).message.isStatic then throw .writeInStaticContext
  let key := toBeBytes32 (← stackPop)
  let new_value ← stackPop
  let target := (← EvmM.getEvm).message.currentTarget
  -- v0.6.0: the access cost is computed and checked BEFORE the state
  -- reads record the slot in the Block Access List — post-repricing the
  -- cold access cost can exceed the EIP-2200 stipend, so the stipend
  -- sentry alone is no longer sufficient.
  let cold := !(← isWarmStorageKey (target, key))
  let access_cost := if cold then GasCosts.COLD_STORAGE_ACCESS else GasCosts.WARM_ACCESS
  check_gas (max access_cost (GasCosts.CALL_STIPEND + 1))
  if cold then warmStorageKey (target, key)
  let original_value ← EvmM.liftTx (getStorageOriginal target key)
  let current_value ← EvmM.liftTx (getStorage target key)
  let gas_cost := access_cost
    + (if original_value == current_value && current_value != new_value then
         GasCosts.STORAGE_WRITE else 0)
  if current_value != new_value then
    if original_value != 0 && current_value != 0 && new_value == 0 then
      EvmM.modifyEvm (fun e =>
        { e with refundCounter := e.refundCounter + GasCosts.REFUND_STORAGE_CLEAR })
    if original_value != 0 && current_value == 0 then
      EvmM.modifyEvm (fun e =>
        { e with refundCounter := e.refundCounter - GasCosts.REFUND_STORAGE_CLEAR })
    if original_value == new_value then
      EvmM.modifyEvm (fun e =>
        { e with refundCounter := e.refundCounter + GasCosts.STORAGE_WRITE })
  let state_gas :=
    if original_value == current_value && current_value != new_value
        && original_value == 0 then
      StateGasCosts.STORAGE_SET
    else 0
  if current_value != new_value && original_value == new_value
      && original_value == 0 then
    credit_state_gas_refund StateGasCosts.STORAGE_SET
  charge_gas gas_cost
  charge_state_gas state_gas
  EvmM.liftTx (setStorage target key new_value)
  pcAdd 1


-- @@ L500-505 verbatim
def iTload : EvmM Unit := do
  let key := toBeBytes32 (← stackPop)
  charge_gas GasCosts.OPCODE_TLOAD
  let target := (← EvmM.getEvm).message.currentTarget
  stackPush (← EvmM.liftTx (getTransientStorage target key))
  pcAdd 1


-- @@ L507-514 verbatim
def iTstore : EvmM Unit := do
  if (← EvmM.getEvm).message.isStatic then throw .writeInStaticContext
  let key := toBeBytes32 (← stackPop)
  let new_value ← stackPop
  charge_gas GasCosts.OPCODE_TSTORE
  let target := (← EvmM.getEvm).message.currentTarget
  EvmM.liftTx (setTransientStorage target key new_value)
  pcAdd 1


-- @@ L516-516 verbatim
end EvmAsm.Stateless.SpecRef
