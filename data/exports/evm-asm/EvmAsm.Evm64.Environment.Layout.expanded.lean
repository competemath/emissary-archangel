/-
  EvmAsm.Evm64.Environment.Layout

  Slice 2 of #100 (EVM environment context layout).

  Concrete byte-offset table for every `EvmEnv` field, materialized as
  named `Nat` constants relative to a base address.  The layout follows
  two simple rules:

  - Fields whose runtime representation is 256-bit (`EvmWord`) or
    20-byte Ethereum addresses (zero-extended to 256 bits in memory)
    occupy a 32-byte slot, 32-byte aligned.
  - Fields whose runtime representation is 64-bit (`Word` — pointers
    and lengths under LP64) occupy an 8-byte slot, 8-byte aligned.

  All 32-byte fields are placed first so their alignment is automatic;
  the 8-byte fields tail the block.  `envSize` is the total footprint.

  This slice introduces only the offset constants and a small set of
  trivially decidable arithmetic facts about them; the `envIs`
  separation-logic assertion that decomposes a heap range into per-field
  cells is the next slice (#100 slice 3 / `evm-asm-3fr7`).

  Layout table (all values in bytes, relative to `base`):

  ```text
  offset  size  field
  ------  ----  ---------------------------
       0    32  address          (Address, zero-extended)
      32    32  selfBalance      (EvmWord)
      64    32  caller           (Address, zero-extended)
      96    32  callValue        (EvmWord)
     128    32  txOrigin         (Address, zero-extended)
     160    32  gasPrice         (EvmWord)
     192    32  blockCoinbase    (Address, zero-extended)
     224    32  blockTimestamp   (EvmWord)
     256    32  blockNumber      (EvmWord)
     288    32  blockPrevrandao  (EvmWord)
     320    32  blockGasLimit    (EvmWord)
     352    32  blockBaseFee     (EvmWord)
     384    32  chainId          (EvmWord)
     416     8  callDataPtr      (Word)
     424     8  callDataLen      (Word)
     432     8  returnDataPtr    (Word)
     440     8  returnDataSize   (Word)
     448        envSize          (total)
  ```
-/

module


-- @@ L52-52 verbatim
@[expose] public section

-- @@ L53-53 verbatim
namespace EvmAsm.Evm64

-- @@ L54-54 verbatim
namespace EvmEnv


-- @@ L56-56 verbatim
/-! ## 32-byte slot offsets (EvmWord / Address) -/


-- @@ L58-59 verbatim
/-- Byte offset of `address` within the env block. -/
def addressOff : Nat := 0

-- @@ L60-61 verbatim
/-- Byte offset of `selfBalance` within the env block. -/
def selfBalanceOff : Nat := 32

-- @@ L62-63 verbatim
/-- Byte offset of `caller` within the env block. -/
def callerOff : Nat := 64

-- @@ L64-65 verbatim
/-- Byte offset of `callValue` within the env block. -/
def callValueOff : Nat := 96

-- @@ L66-67 verbatim
/-- Byte offset of `txOrigin` within the env block. -/
def txOriginOff : Nat := 128

-- @@ L68-69 verbatim
/-- Byte offset of `gasPrice` within the env block. -/
def gasPriceOff : Nat := 160

-- @@ L70-71 verbatim
/-- Byte offset of `blockCoinbase` within the env block. -/
def blockCoinbaseOff : Nat := 192

-- @@ L72-73 verbatim
/-- Byte offset of `blockTimestamp` within the env block. -/
def blockTimestampOff : Nat := 224

-- @@ L74-75 verbatim
/-- Byte offset of `blockNumber` within the env block. -/
def blockNumberOff : Nat := 256

-- @@ L76-77 verbatim
/-- Byte offset of `blockPrevrandao` within the env block. -/
def blockPrevrandaoOff : Nat := 288

-- @@ L78-79 verbatim
/-- Byte offset of `blockGasLimit` within the env block. -/
def blockGasLimitOff : Nat := 320

-- @@ L80-81 verbatim
/-- Byte offset of `blockBaseFee` within the env block. -/
def blockBaseFeeOff : Nat := 352

-- @@ L82-83 verbatim
/-- Byte offset of `chainId` within the env block. -/
def chainIdOff : Nat := 384


-- @@ L85-85 verbatim
/-! ## 8-byte slot offsets (Word — pointers / lengths) -/


-- @@ L87-88 verbatim
/-- Byte offset of `callDataPtr` within the env block. -/
def callDataPtrOff : Nat := 416

-- @@ L89-90 verbatim
/-- Byte offset of `callDataLen` within the env block. -/
def callDataLenOff : Nat := 424

-- @@ L91-92 verbatim
/-- Byte offset of `returnDataPtr` within the env block. -/
def returnDataPtrOff : Nat := 432

-- @@ L93-94 verbatim
/-- Byte offset of `returnDataSize` within the env block. -/
def returnDataSizeOff : Nat := 440

-- @@ L95-101 verbatim
/-- M24 — byte offset of the retired `persistentLogLength` (u64) within the
    env block. The emitted guest keeps this cell at zero for env-layout
    compatibility; the legacy Option-A model uses it as the count of 128-B
    `(addrHash:32, slotKey:32, original:32, current:32)` rows at
    `STATE_TRACKER_AREA = 0xa0630000`. Renamed from M22's `slotTableCountOff`
    (which counted 64-B `(key, value)` entries in the dispatcher `.data`). -/
def persistentLogLengthOff : Nat := 448

-- @@ L102-105 verbatim
/-- M24 legacy Option-A byte offset of `persistentLogCheckpoint` (u64). The
    emitted guest no longer captures or restores a persistent-log checkpoint;
    the cell remains reserved because env layout is shared with legacy proofs. -/
def persistentLogCheckpointOff : Nat := 456

-- @@ L106-111 verbatim
/-- M24 — byte offset of `transientLogLength` (u64). Live counter of
    entries in the transient storage log at `0xa0830000` (EIP-1153
    TLOAD/TSTORE backing store). REVERT resets this to 0 (transient
    storage starts empty at tx start; we have no preload mechanism
    for it). -/
def transientLogLengthOff : Nat := 464


-- @@ L113-117 verbatim
/-- Total byte size of an EVM environment context block.

    `envSize = 13 * 32 + 7 * 8 = 416 + 56 = 472` (M24 added
    `persistentLogCheckpoint` and `transientLogLength`). -/
def envSize : Nat := 472


-- @@ L119-124 verbatim
/-! ## Layout sanity facts

These are all concrete `Nat`-literal facts; they exist so downstream
slices (and tests) can `rfl`/`decide` against the named layout without
re-deriving each offset.  Bumping the layout in a future slice forces
exactly one consistent rewrite in this file. -/


-- @@ L126-127 verbatim
/-- `addressOff` is 32-byte aligned. -/
theorem addressOff_align : addressOff % 32 = 0 := by decide

-- @@ L128-129 verbatim
/-- `selfBalanceOff` is 32-byte aligned. -/
theorem selfBalanceOff_align : selfBalanceOff % 32 = 0 := by decide

-- @@ L130-131 verbatim
/-- `callerOff` is 32-byte aligned. -/
theorem callerOff_align : callerOff % 32 = 0 := by decide

-- @@ L132-133 verbatim
/-- `callValueOff` is 32-byte aligned. -/
theorem callValueOff_align : callValueOff % 32 = 0 := by decide

-- @@ L134-135 verbatim
/-- `txOriginOff` is 32-byte aligned. -/
theorem txOriginOff_align : txOriginOff % 32 = 0 := by decide

-- @@ L136-137 verbatim
/-- `gasPriceOff` is 32-byte aligned. -/
theorem gasPriceOff_align : gasPriceOff % 32 = 0 := by decide

-- @@ L138-139 verbatim
/-- `blockCoinbaseOff` is 32-byte aligned. -/
theorem blockCoinbaseOff_align : blockCoinbaseOff % 32 = 0 := by decide

-- @@ L140-141 verbatim
/-- `blockTimestampOff` is 32-byte aligned. -/
theorem blockTimestampOff_align : blockTimestampOff % 32 = 0 := by decide

-- @@ L142-143 verbatim
/-- `blockNumberOff` is 32-byte aligned. -/
theorem blockNumberOff_align : blockNumberOff % 32 = 0 := by decide

-- @@ L144-145 verbatim
/-- `blockPrevrandaoOff` is 32-byte aligned. -/
theorem blockPrevrandaoOff_align : blockPrevrandaoOff % 32 = 0 := by decide

-- @@ L146-147 verbatim
/-- `blockGasLimitOff` is 32-byte aligned. -/
theorem blockGasLimitOff_align : blockGasLimitOff % 32 = 0 := by decide

-- @@ L148-149 verbatim
/-- `blockBaseFeeOff` is 32-byte aligned. -/
theorem blockBaseFeeOff_align : blockBaseFeeOff % 32 = 0 := by decide

-- @@ L150-151 verbatim
/-- `chainIdOff` is 32-byte aligned. -/
theorem chainIdOff_align : chainIdOff % 32 = 0 := by decide


-- @@ L153-154 verbatim
/-- `callDataPtrOff` is 8-byte aligned. -/
theorem callDataPtrOff_align : callDataPtrOff % 8 = 0 := by decide

-- @@ L155-156 verbatim
/-- `callDataLenOff` is 8-byte aligned. -/
theorem callDataLenOff_align : callDataLenOff % 8 = 0 := by decide

-- @@ L157-158 verbatim
/-- `returnDataPtrOff` is 8-byte aligned. -/
theorem returnDataPtrOff_align : returnDataPtrOff % 8 = 0 := by decide

-- @@ L159-160 verbatim
/-- `returnDataSizeOff` is 8-byte aligned. -/
theorem returnDataSizeOff_align : returnDataSizeOff % 8 = 0 := by decide

-- @@ L161-162 verbatim
/-- `persistentLogLengthOff` is 8-byte aligned. -/
theorem persistentLogLengthOff_align : persistentLogLengthOff % 8 = 0 := by decide

-- @@ L163-164 verbatim
/-- `persistentLogCheckpointOff` is 8-byte aligned. -/
theorem persistentLogCheckpointOff_align : persistentLogCheckpointOff % 8 = 0 := by decide

-- @@ L165-166 verbatim
/-- `transientLogLengthOff` is 8-byte aligned. -/
theorem transientLogLengthOff_align : transientLogLengthOff % 8 = 0 := by decide


-- @@ L168-169 verbatim
/-- `envSize` matches `13 * 32 + 7 * 8` (M24 added 2 more 8-byte cells). -/
theorem envSize_eq : envSize = 13 * 32 + 7 * 8 := by decide


-- @@ L171-195 verbatim
/-- Every 32-byte field's slot ends at the next 32-byte field's start;
    all 8-byte fields then tail without gap up to `envSize`.  This is
    proved as a single concrete decidable fact: the disjoint union of
    every named slot exactly fills `[0, envSize)`. -/
theorem envSize_covers :
    addressOff + 32 = selfBalanceOff ∧
    selfBalanceOff + 32 = callerOff ∧
    callerOff + 32 = callValueOff ∧
    callValueOff + 32 = txOriginOff ∧
    txOriginOff + 32 = gasPriceOff ∧
    gasPriceOff + 32 = blockCoinbaseOff ∧
    blockCoinbaseOff + 32 = blockTimestampOff ∧
    blockTimestampOff + 32 = blockNumberOff ∧
    blockNumberOff + 32 = blockPrevrandaoOff ∧
    blockPrevrandaoOff + 32 = blockGasLimitOff ∧
    blockGasLimitOff + 32 = blockBaseFeeOff ∧
    blockBaseFeeOff + 32 = chainIdOff ∧
    chainIdOff + 32 = callDataPtrOff ∧
    callDataPtrOff + 8 = callDataLenOff ∧
    callDataLenOff + 8 = returnDataPtrOff ∧
    returnDataPtrOff + 8 = returnDataSizeOff ∧
    returnDataSizeOff + 8 = persistentLogLengthOff ∧
    persistentLogLengthOff + 8 = persistentLogCheckpointOff ∧
    persistentLogCheckpointOff + 8 = transientLogLengthOff ∧
    transientLogLengthOff + 8 = envSize := by decide


-- @@ L197-197 verbatim
end EvmEnv

-- @@ L198-198 verbatim
end EvmAsm.Evm64
