/-
  EvmAsm.Codegen.Programs.BlockVerdictParams

  Shared numeric parameters for the block-state-root / stateless-verdict-v2
  programs: static arena capacities and layout byte-widths.
  Extracted from BlockVerdict.lean so BlockVerdictDataSection.lean can share
  them without a circular import.
-/

module

public import EvmAsm.Codegen.Programs.EvmAccessGas
public import EvmAsm.Codegen.Programs.EvmStorageAccessGas
public import EvmAsm.Codegen.RegionMapLinkPins
public import EvmAsm.Stateless.Constants
public import EvmAsm.Stateless.MemoryLayout
meta import EvmAsm.Codegen.Programs.EvmAccessGas
meta import EvmAsm.Codegen.Programs.EvmStorageAccessGas
meta import EvmAsm.Codegen.RegionMapLinkPins
meta import EvmAsm.Stateless.Constants
meta import EvmAsm.Stateless.MemoryLayout


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-25 verbatim
namespace EvmAsm.Codegen


-- @@ L27-34 verbatim
/-- Amsterdam's EIP-7928 `GasCosts.BLOCK_ACCESS_LIST_ITEM`.  This is the
    proven lower-bound divisor for an input-originated *distinct final state
    change*: `validate_block_access_list_gas_limit` charges one 2,000-gas BAL
    item per account and one per distinct storage slot (storage changes and
    reads are de-duplicated by slot).  It is deliberately not inferred from an
    EVM `SSTORE` price: BAL is the consensus-level accounting rule that bounds
    the final state-change input set. -/
def bsrBalGasCost : Nat := 2000


-- @@ L36-39 verbatim
/-- Current Amsterdam resource target.  Keep capacities as functions of this
    value: changing the supported block gas limit must resize every fixed
    state-root builder arena rather than silently preserving a stale literal. -/
def bsrStateRootBlockGasLimit : Nat := 200000000


-- @@ L41-46 verbatim
/-- Static BAL/state replay arena capacity.  EIP-7928 enforces
    `bal_items <= block_gas_limit / BLOCK_ACCESS_LIST_ITEM`, so a 200M block
    has at most 100,000 BAL items.  The later bounded builder accepts only the
    normalized distinct final changes plus the explicitly bounded auxiliary
    system/withdrawal changes below. -/
def bsrMaxBalItems : Nat := bsrStateRootBlockGasLimit / bsrBalGasCost

-- @@ L47-47 verbatim
def bsrModeledSystemChanges : Nat := 2

-- @@ L48-48 verbatim
def bsrMaxWithdrawalChanges : Nat := 16

-- @@ L49-49 verbatim
def bsrMaxAuxChanges : Nat := bsrModeledSystemChanges + bsrMaxWithdrawalChanges

-- @@ L50-51 verbatim
def bsrMaxStateChanges : Nat :=
  bsrMaxBalItems + bsrModeledSystemChanges + bsrMaxWithdrawalChanges


-- @@ L53-57 verbatim
/-- State-trie keys are 32-byte hashes represented as 64 nibbles.  The sorted
    builder uses an in-place MSD partitioner: its only sort workspace is a
    bounded pending-range stack (one range per nibble fanout at each depth),
    never attacker-sized bucket arrays. -/
def bsrMptKeyNibbles : Nat := 64

-- @@ L58-58 verbatim
def bsrMptRadixFanout : Nat := 16

-- @@ L59-59 verbatim
def bsrMptSortRangeStackCapacity : Nat := bsrMptKeyNibbles * bsrMptRadixFanout

-- @@ L60-60 verbatim
def bsrMptSortRangeFrameBytes : Nat := 32


-- @@ L62-64 verbatim
/-- A Patricia trie has at most one active construction frame per consumed key
    nibble plus its root frame.  This is depth-derived, not input-count-derived. -/
def bsrMptBuilderFrameCapacity : Nat := bsrMptKeyNibbles + 1

-- @@ L65-71 verbatim
/-- A builder frame records one Patricia depth, its input range, and all 17
    canonical child references (16 branch children plus the value slot).  Each
    reference may be an inline RLP item or a 33-byte hash reference, so this
    deliberately reserves a full 1 KiB frame rather than pretending that a
    handful of scalar words is enough.  The 65-frame array remains bounded by
    key depth only; it is never indexed by the number of untrusted changes. -/
def bsrMptBuilderFrameBytes : Nat := 1024

-- @@ L72-75 verbatim
/-- The SSZ `ByteList[1024]` envelope caps every pre-state witness node.  The
    bounded builder also uses this as its maximum one-node re-encoding buffer;
    larger reconstructed nodes are rejected before they can reach a frame. -/
def bsrMptNodeMaxBytes : Nat := bsrMptBuilderFrameBytes

-- @@ L76-82 verbatim
/-- Canonical pre-state branch-child references are at most 32 raw bytes:
    either an inline RLP encoding (<32) or a 32-byte hash.  A frontier frame
    stores the raw reference length followed by the bytes, rounded to 40 B;
    all sixteen branch children therefore consume 640 B of its 1 KiB budget.
    The remaining 384 B is reserved for the range/depth bookkeeping and the
    branch value/reference produced while unwinding. -/
def bsrMptFrameChildRefBytes : Nat := 32

-- @@ L83-83 verbatim
def bsrMptFrameChildRefStride : Nat := 40

-- @@ L84-84 verbatim
def bsrMptFrameBranchChildrenBytes : Nat := bsrMptRadixFanout * bsrMptFrameChildRefStride

-- @@ L85-86 verbatim
/-- Frame metadata immediately follows the sixteen retained child references. -/
def bsrMptFrameNodePtrOffset : Nat := bsrMptFrameBranchChildrenBytes

-- @@ L87-87 verbatim
def bsrMptFrameNodeLenOffset : Nat := bsrMptFrameNodePtrOffset + 8

-- @@ L88-88 verbatim
def bsrMptFrameNodeKindOffset : Nat := bsrMptFrameNodeLenOffset + 8

-- @@ L89-92 verbatim
/-- Sixteen `{start,end}` ranges for the current nibble partition live after
    root metadata.  They are frame-local, so their capacity is depth-derived
    rather than proportional to untrusted change count. -/
def bsrMptFrameRangeTableOffset : Nat := bsrMptFrameNodeKindOffset + 8

-- @@ L93-93 verbatim
def bsrMptFrameRangeStride : Nat := 16

-- @@ L94-94 verbatim
def bsrMptFrameRangeTableBytes : Nat := bsrMptRadixFanout * bsrMptFrameRangeStride

-- @@ L95-98 verbatim
/-- Extension metadata occupies the frame tail after the branch-range table.
    The decoded path is at most the remaining 64 state-key nibbles; it is
    deliberately not the SSZ node's potentially 2047-nibble compact path. -/
def bsrMptFrameExtensionPathLenOffset : Nat := bsrMptFrameRangeTableOffset + bsrMptFrameRangeTableBytes

-- @@ L99-99 verbatim
def bsrMptFrameExtensionChildPtrOffset : Nat := bsrMptFrameExtensionPathLenOffset + 8

-- @@ L100-100 verbatim
def bsrMptFrameExtensionChildLenOffset : Nat := bsrMptFrameExtensionChildPtrOffset + 8

-- @@ L101-101 verbatim
def bsrMptFrameExtensionPathOffset : Nat := bsrMptFrameExtensionChildLenOffset + 8

-- @@ L102-102 verbatim
def bsrMptFrameExtensionPathBytes : Nat := bsrMptKeyNibbles

-- @@ L103-103 verbatim
def bsrMptFrameUsedBytes : Nat := bsrMptFrameExtensionPathOffset + bsrMptFrameExtensionPathBytes

-- @@ L104-107 verbatim
/-- One shared node buffer is enough for depth-first construction: every
    completed child is reduced to its raw reference before its next sibling is
    built. This is independent of the gas-derived descriptor count. -/
def bsrMptBuilderNodeScratchBytes : Nat := bsrMptNodeMaxBytes


-- @@ L109-112 verbatim
/-- Constructed nodes retained for a possible one-child branch collapse are
    indexed only by Patricia depth.  This is deliberately not a NodeDb: the
    fixed `65 = 64 + 1` slots cannot grow with the number of changes. -/
def bsrMptConstructedCacheSlots : Nat := bsrMptBuilderFrameCapacity

-- @@ L113-113 verbatim
def bsrMptConstructedCacheNodeBytes : Nat := bsrMptNodeMaxBytes

-- @@ L114-114 verbatim
def bsrMptConstructedCacheBytes : Nat := bsrMptConstructedCacheSlots * bsrMptConstructedCacheNodeBytes

-- @@ L115-115 verbatim
def bsrMptConstructedCacheRefBytes : Nat := bsrMptConstructedCacheSlots * bsrMptFrameChildRefBytes

-- @@ L116-116 verbatim
def bsrMptConstructedCacheWordBytes : Nat := bsrMptConstructedCacheSlots * 8


-- @@ L118-118 verbatim
#guard bsrMptConstructedCacheSlots = bsrMptKeyNibbles + 1


-- @@ L120-120 verbatim
#guard bsrMptFrameUsedBytes <= bsrMptBuilderFrameBytes

-- @@ L121-121 verbatim
def bsrMaxAccessAccounts : Nat := runtimeAccessAccountOutcomeCapacity


-- @@ L123-132 verbatim
/-- Per-account storage-slot staging capacity for the BAL key helpers
    (`bal_recipient_storage_keys`, `bal_recipient_storage_reads_keys` and their
    consumer buffers `sps_keys` / `bvcd_keys` / `csce_keys`). One account's changes+reads can
    absorb the entire gas-derived BAL budget (storage reads are the cheapest
    BAL item), so the only bound that avoids conservative rejects of legitimate
    200M blocks is `bsrMaxBalItems` itself. Counts above this make the helpers
    write nothing and return the true count; callers bail conservatively
    (fhsxz.2.4.2.66.1.2 — the former 512 cap false-rejected queue-heavy
    blocks far below 200M). -/
def bsrAccountSlotCap : Nat := bsrMaxBalItems


-- @@ L134-142 verbatim
/-- Conservative upper bound on `witness.state` byte length accepted by
    `block_state_root`. Beyond this the post-state recompute bails conservatively
    (bsr_fail=111). This is a coarse size guard, NOT a fixed-buffer limit: the
    witness is read in place and the real structural bound is the sorted witness
    index node cap (8192, `MptWitnessIndex`). The earlier 262144 value
    false-rejected legitimately large state-creation blocks (EIP-8037 state-gas
    reservoir fixtures push >256 KiB witnesses, e.g. evm-asm-zbvak's 336 KB row);
    512 KiB keeps a guard while accepting those blocks. -/
def bsrMaxWitnessBytes : Nat := 524288


-- @@ L144-148 verbatim
/-- The cheapest Amsterdam transaction pays `GasCosts.TX_BASE = 12,000`.
    EIP-2780 deliberately decomposes the old 21,000 floor: recipient, value,
    calldata and access-list costs are conditional, so this base is the only
    unconditional divisor for the full block transaction-count bound. -/
def bvMtxIntrinsicGasFloor : Nat := 12000


-- @@ L150-156 verbatim
/-- Amsterdam's `COLD_STORAGE_ACCESS` gas cost (execution-specs
    `amsterdam/vm/gas.py:68-74`).  The block-lifetime storage-write map can
    hold at most one distinct cold slot per 3,000 gas at the supported
    200,000,000-gas block limit, so its capacity is the floor of that quotient.
    Warm repeats stay in the transaction map and do not consume new block rows.
-/
def coldStorageAccessGas : Nat := 3000


-- @@ L158-161 verbatim
/-- Block-lifetime storage-map rows: `200,000,000 / 3,000 = 66,666`.
    This is the bound for `BlockState.storage_writes`, not the per-transaction
    distinct-slot bound below. -/
def blockStorageWritesCapacity : Nat := bsrStateRootBlockGasLimit / coldStorageAccessGas


-- @@ L163-167 verbatim
/-- Per-transaction storage-map rows: `(16,777,216 - 12,000) / 3,000 = 5,588`.
    `TX_MAX_GAS_LIMIT` is pinned by execution-specs
    `amsterdam/transactions.py:63`; subtracting `TX_BASE` leaves the regular
    gas available for distinct cold storage accesses. -/
def txStorageWritesCapacity : Nat := (16777216 - bvMtxIntrinsicGasFloor) / coldStorageAccessGas


-- @@ L169-171 verbatim
/-! The storage arenas are absolute-address Scheme-A regions.  The enlarged
    block map keeps its low anchor, the smaller tx map moves after it, and the
    independent undo journal follows the link-derived `.state_gas_diag` end. -/

-- @@ L172-172 verbatim
def storageWritesBlockBase : Nat := EvmAsm.Stateless.STORAGE_WRITES_AREA.toNat

-- @@ L173-173 verbatim
def storageWritesTxBase : Nat := EvmAsm.Stateless.TX_STORAGE_WRITES_AREA.toNat

-- @@ L174-175 verbatim
def storageWritesStateGasDiagEnd : Nat :=
  0xa0b70000 + RegionMapLinkPins.bssSizeBytes + RegionMapLinkPins.stateGasDiagSizeBytes

-- @@ L176-177 verbatim
def storageWritesUndoBase : Nat :=
  ((storageWritesStateGasDiagEnd + 0xfff) / 0x1000) * 0x1000


-- @@ L179-181 verbatim
/-- Full Amsterdam transaction capacity target derived from the supported block
    gas limit and `GasCosts.TX_BASE` (gas.py:131). -/
def bvMtxFullTxCap : Nat := bsrStateRootBlockGasLimit / bvMtxIntrinsicGasFloor

-- @@ L182-182 verbatim
#guard bvMtxFullTxCap = 16666


-- @@ L184-188 verbatim
/-- Amsterdam `REGULAR_PER_AUTH_BASE_COST`: 101 calldata-floor bytes, one
    ecrecover precompile, one cold account access, and two warm accesses.  Every
    authorization tuple pays this regular-gas cost before execution, so it gives
    a protocol-derived bound on all type-4 authorization records in a block. -/
def bvEip7702AuthRegularGas : Nat := 7816


-- @@ L190-195 verbatim
/-- Maximum authorization tuples in any block under the supported gas limit.
    This is a gas bound, not a fixture-derived admission cap.  Use floor
    division: a capacity may be conservative, but it must not claim one more
    tuple than the gas limit can pay for. -/
def bvEip7702AuthEntryCapacity : Nat :=
  bsrStateRootBlockGasLimit / bvEip7702AuthRegularGas

-- @@ L196-196 verbatim
#guard bvEip7702AuthEntryCapacity = 25588


-- @@ L198-203 verbatim
/-- The ordered EIP-7702 authority simulation materializes the union of all
    transaction senders and recovered authorization authorities.  The additive
    bound is conservative (the two maxima cannot both be attained in one valid
    block) but keeps the static table's fail-closed contract simple. -/
def bvEip7702AuthorityEventCapacity : Nat :=
  bvMtxFullTxCap + bvEip7702AuthEntryCapacity

-- @@ L204-204 verbatim
#guard bvEip7702AuthorityEventCapacity = 42254


-- @@ L206-208 verbatim
/-- One authority-state row is a padded address, running nonce delta, and the
    current delegation-marker bit. -/
def bvEip7702AuthorityRowBytes : Nat := 48

-- @@ L209-210 verbatim
def bvEip7702AuthorityTableBytes : Nat :=
  bvEip7702AuthorityEventCapacity * bvEip7702AuthorityRowBytes

-- @@ L211-211 verbatim
#guard bvEip7702AuthorityTableBytes = 2028192


-- @@ L213-217 verbatim
/-- Active multi-transaction execution-loop capacity. Every live per-transaction
    arena and aggregation table is statically sized to the protocol-derived
    `bvMtxFullTxCap`, so the loop must use the same bound rather than preserve a
    fixture-era 1024-transaction false-reject gate. -/
def bvMtxActiveTxCap : Nat := bvMtxFullTxCap


-- @@ L219-223 verbatim
/-- An RLP transaction/receipt index below `bvMtxFullTxCap` has at most three
    key bytes, hence at most six nibbles.  The indexed-root replacement keeps
    its sort stack and construction frames depth-derived; only the descriptor
    and permutation arrays are gas-derived. -/
def itrIndexedKeyMaxNibbles : Nat := 6

-- @@ L224-224 verbatim
def itrIndexedRadixFanout : Nat := 16

-- @@ L225-225 verbatim
def itrIndexedSortRangeStackCapacity : Nat := itrIndexedKeyMaxNibbles * itrIndexedRadixFanout

-- @@ L226-226 verbatim
def itrIndexedBuilderFrameCapacity : Nat := itrIndexedKeyMaxNibbles + 1

-- @@ L227-227 verbatim
def itrIndexedEntryCapacity : Nat := bvMtxFullTxCap


-- @@ L229-231 verbatim
/-- Compatibility alias for existing active-loop call sites. New code should
    choose `bvMtxActiveTxCap` or `bvMtxFullTxCap` explicitly. -/
def bvMtxArenaTxCap : Nat := bvMtxActiveTxCap


-- @@ L233-236 verbatim
/-- Cheap per-transaction result arenas use the full tx-capacity target. They
    are indexed only by tx number and are small enough to make static sizing
    preferable to preserving the old 1024 fixture cap. -/
def bvMtxU64ArenaBytes : Nat := bvMtxFullTxCap * 8

-- @@ L237-237 verbatim
def bvMtxLogWindowBytes : Nat := bvMtxFullTxCap * 16


-- @@ L239-244 verbatim
/-- System addresses in the MtxTail skip-list. **Empty (0).** GH #10684 / #11210 /
    #11218 union: every whole-account system skip (EIP-2935, EIP-4788, EIP-7002,
    EIP-7251, EIP-6110, SYSTEM_ADDRESS) is a false-accept surface with no
    execution-specs counterpart. Gas/value-coupled {sender, recipient, coinbase}
    remain. -/
def bvMtxSystemSkipEntries : Nat := 0

-- @@ L245-249 verbatim
/-- The multi-tx skip-list stores `{sender_i, recipient_i}` for every
    transaction plus the shared coinbase account. No system addresses
    (`bvMtxSystemSkipEntries = 0`). Sized to the full 200M tx-count target so the
    post-loop BAL comparators do not inherit the active execution-loop cap. -/
def bvMtxSkipListEntries : Nat := bvMtxFullTxCap * 2 + 1 + bvMtxSystemSkipEntries

-- @@ L250-251 verbatim
/-- Two 32-byte addresses per transaction plus the shared coinbase entry. -/
def bvMtxSkipListBytes : Nat := bvMtxSkipListEntries * 32

-- @@ L252-254 verbatim
/-- Sender-balance aggregation shares the full sender table capacity so the
    B2 running-balance check does not inherit the active execution-loop cap. -/
def bvMtxSenderBalanceEntries : Nat := bvMtxFullTxCap

-- @@ L255-256 verbatim
/-- One 64-byte sender-balance row for every transaction-capacity slot. -/
def bvMtxSenderBalanceTableBytes : Nat := bvMtxSenderBalanceEntries * 64

-- @@ L257-258 verbatim
/-- One 32-byte created-recipient address slot for every transaction. -/
def bvMtxCreatedRecipientBytes : Nat := bvMtxFullTxCap * 32

-- @@ L259-262 verbatim
/-- Sender-count aggregation is a post-loop, keyed-by-sender table. It is sized
    to the full tx-count target so the B1 final-nonce check does not inherit the
    active execution-loop cap. -/
def bvMtxSenderCountEntries : Nat := bvMtxFullTxCap

-- @@ L263-264 verbatim
/-- One 40-byte sender-count row for every transaction-capacity slot. -/
def bvMtxSenderCountTableBytes : Nat := bvMtxSenderCountEntries * 40

-- @@ L265-266 verbatim
/-- One 32-byte sort key per sender-count row. -/
def bvMtxSenderCountSortBytes : Nat := bvMtxSenderCountEntries * 32

-- @@ L267-268 verbatim
/-- One 64-byte skip row per sender-count row. -/
def bvMtxSenderCountSkipBytes : Nat := bvMtxSenderCountEntries * 64


-- @@ L270-274 verbatim
/-- Execution-specs runs each EIP-7002/EIP-7251 system transaction with
    `SYSTEM_TRANSACTION_GAS = 30,000,000`. The stateless verdict derives both
    withdrawal and consolidation requests, so side capture must be sized for two
    such calls. -/
def bvSystemTransactionGas : Nat := 30000000

-- @@ L275-275 verbatim
def bvSystemRequestCallCount : Nat := 2


-- @@ L277-277 verbatim
def bvSystemStorageMinSstoreGas : Nat := 100


-- @@ L279-283 verbatim
/-- Receipt/log arena capacities are deliberately separated by resource type.
    Receipt records are per transaction and therefore use the full Amsterdam
    200M intrinsic-floor transaction count target; log/RLP byte arenas remain
    independent capacity slices tracked under `evm-asm-vv4hr.3`. -/
def bvReceiptRecordCapacity : Nat := bvMtxFullTxCap

-- @@ L284-284 verbatim
def bvReceiptRecordBytes : Nat := 64

-- @@ L285-286 verbatim
/-- One 64-byte receipt record for every full-capacity transaction. -/
def bvReceiptRecordsBytes : Nat := bvReceiptRecordCapacity * bvReceiptRecordBytes


-- @@ L288-290 verbatim
/-- Current EEST resource target for Amsterdam/Prague/Osaka stateless blocks. -/
def bvResourceBlockGasLimit : Nat :=
  EvmAsm.Stateless.Constants.resourceBlockGasLimit


-- @@ L292-294 verbatim
/-- EVM LOG base gas. A zero-topic, zero-data LOG0 is the cheapest way to
    increase the number of execution-derived receipt log descriptors. -/
def bvBlockLogMinGas : Nat := 375


-- @@ L296-298 verbatim
/-- EVM LOG data gas per byte. Topic/base gas can only reduce the number of
    data bytes that fit inside the same block gas target. -/
def bvBlockLogDataByteGas : Nat := 8


-- @@ L300-304 verbatim
/-- Worst-case execution-derived log COUNT in a 200M block. Each LOG opcode
    costs at least `bvBlockLogMinGas` (the zero-topic, zero-data LOG0 base), so
    the block holds at most `gas_limit / 375 = 533,333` log records. -/
def bvBlockLogFullDescTarget : Nat :=
  bvResourceBlockGasLimit / bvBlockLogMinGas


-- @@ L306-314 verbatim
/-- FIXED-STRIDE descriptor byte target (the verbatim 256 B copy that
    `block_log_window_snapshot` performs today, one slot per log). NOTE: this is
    the INFEASIBLE upper bound -- 533,333 * 256 = ~136.5 MiB of descriptors
    alone. Combined with `bvBlockLogFullMetaBytes` + `bvBlockLogFullDataBytes`
    the fixed-stride arena is ~162 MiB, which is 2.76x the measured ~58.7 MiB of
    `.data` headroom before `.sszscratch` (0xbf800000). Kept only to document why
    the verbatim-copy layout cannot reach the 200M target; the actual
    implementation target is `bvBlockLogPackedDescBytes` below. -/
def bvBlockLogFullDescBytes : Nat := bvBlockLogFullDescTarget * 256

-- @@ L315-315 verbatim
def bvBlockLogFullMetaBytes : Nat := bvBlockLogFullDescTarget * 16


-- @@ L317-321 verbatim
/-- Full copied-log-data byte target for the 200M resource work. It deliberately
    uses a simple upper bound (`gas_limit / LOGDATA_GAS`) so the implementation
    target covers every execution-specs-valid mix of LOG base/topic/data gas. -/
def bvBlockLogFullDataBytes : Nat :=
  bvResourceBlockGasLimit / bvBlockLogDataByteGas


-- @@ L323-353 verbatim
/-- vv4hr.3.4.1 capacity DERIVATION -- the FEASIBLE 200M log-arena target.

    The fixed-256 B stride (`bvBlockLogFullDescBytes`) over-allocates because it
    reserves room for four 32 B topics in EVERY descriptor even though most logs
    carry none. The gas schedule charges 375 per log base AND 375 per topic, so

        #logs + #topics  <=  gas_limit / 375  =  533,333   (one "gas unit" each)

    bounds the SUM of records and topics. A packed descriptor needs at most one
    gas unit's worth of bytes per unit: a log header (address 20 + data
    offset/len 8 + topic_count/flags) fits in 32 B, and each topic is 32 B. So a
    packed descriptor arena charged at 32 B per gas unit is a sound upper bound
    over every LOG0..LOG4 / data mix:

        packed desc <=  32 * (gas_limit / 375)  =  ~16.3 MiB

    With the count-scaled meta table (16 B/log -> ~8.1 MiB) and the gas/8 data
    bound (~23.8 MiB), the packed arena totals ~48.3 MiB, which DOES fit the
    ~58.7 MiB `.data` headroom (10+ MiB margin).

    Implementation (vv4hr.3.4.2): `block_log_window_snapshot` must REPACK on copy
    -- emit a variable-length packed record per log instead of the current
    verbatim 256 B `slli ..,8` memcpy -- and the descriptor readers
    (`block_receipt_logs_materialize`, `materialize_log_records`,
    `parse_deposit_requests`) must walk the packed stride. The runtime
    dispatcher's `evm_event_logs` 256 B source format is unchanged. Closing this
    keeps `bv_block_log_overflow` unreachable under 200M. If it is reached anyway,
    BlockVerdictReceiptsTail now fails visibly instead of accepting through a
    capacity skip, so class-D receipt enforcement and class-E deposit derivation do
    not normalize incomplete log materialization into success. -/
def bvBlockLogPackedUnitBytes : Nat := 32

-- @@ L354-374 verbatim
def bvBlockLogPackedDescBytes : Nat :=
  bvBlockLogPackedUnitBytes * bvBlockLogFullDescTarget

-- vv4hr.3.4.2 PACK (2026-06-20): the active block-log DESCRIPTOR arena is the
-- PACKED layout (32 B per gas unit), not the fixed 256 B/log stride. The gas
-- schedule charges 375 per log base AND 375 per topic, so `#logs + #topics <=
-- gas/375 = 533,333`; a packed descriptor is a 32 B header (topic_count @+0,
-- canonical-BE address 20 B @+8) plus 32 B per ACTUAL topic, so a 32 B/gas-unit
-- arena (`bvBlockLogPackedDescBytes` = 32*533,333 = ~16.3 MiB) is a sound upper
-- bound over every LOG0..LOG4/data mix -- vs ~136.5 MiB for the old 256 B stride.
-- The descriptor records are VARIABLE length, so `block_log_window_snapshot`
-- repacks on copy and records each log's packed byte-offset in
-- `bv_block_log_meta[idx].desc_off` (+16; meta widened 16 -> 24 B). The lone
-- random-access reader (`block_receipt_logs_materialize`) jumps via that desc_off;
-- the sequential readers (`materialize_log_records`, `log_records_encode_rlp`)
-- walk `reclen = 32 + 32*topic_count`. The runtime dispatcher's `evm_event_logs`
-- 256 B SOURCE format is UNCHANGED. The data byte arena (gas/8 = 25,000,000) and
-- the count cap (533,333) are unchanged, so `bv_block_log_overflow` stays
-- UNREACHABLE under 200M -- preserving the #9043 class-D (receipts) / class-E
-- (deposit-derivation) no-skip property -- while reclaiming ~113 MiB of the
-- .data -> .sszscratch link-time window.

-- @@ L375-375 verbatim
def bvBlockLogDescCapacity : Nat := bvBlockLogFullDescTarget

-- @@ L376-376 verbatim
def bvBlockLogDescBytes : Nat := bvBlockLogPackedDescBytes

-- @@ L377-377 verbatim
def bvBlockLogMetaBytes : Nat := bvBlockLogDescCapacity * 24

-- @@ L378-378 verbatim
def bvBlockLogDataBytes : Nat := bvBlockLogFullDataBytes

-- @@ L379-379 verbatim
def bvLogsRlpArenaBytes : Nat := 1048576

-- @@ L380-380 verbatim
def bvRecordBloomBytes : Nat := 256

-- @@ L381-382 verbatim
/-- One 256-byte receipt bloom for every full-capacity transaction. -/
def bvRecordBloomsBytes : Nat := bvReceiptRecordCapacity * bvRecordBloomBytes

-- @@ L383-384 verbatim
/-- One 32-byte log descriptor for every full-capacity transaction. -/
def bvRecordLogsDescBytes : Nat := bvReceiptRecordCapacity * 32

-- @@ L385-385 verbatim
def bvReceiptsRlpBytes : Nat := 1048576

-- @@ L386-386 verbatim
def bvReceiptEncodePayloadBytes : Nat := 1048576

-- @@ L387-387 verbatim
def bvReceiptListPayloadBytes : Nat := 1048576

-- @@ L388-395 verbatim
/-- One `{ptr,len}` descriptor per logical receipt for
    `block_validate_receipts_consensus_list` → `block_validate_receipts_root_indexed`.
    Must cover the full MTx receipt list, not a fixed 128: exact-intrinsic multi-tx
    blocks with >128 receipts (GH #11542 03361 tx_count=1020, 23017 tx_count=200)
    hit `.Lbrcl_root_fail` → validator status 1 → bv_fail=56 while state root matched.

    Bound is `bvMtxFullTxCap`, derived from the Amsterdam `TX_BASE` floor. -/
def bvReceiptConsensusDescCapacity : Nat := bvMtxFullTxCap

-- @@ L396-397 verbatim
/-- One 16-byte consensus-list descriptor for every full-capacity receipt. -/
def bvReceiptConsensusDescBytes : Nat := bvReceiptConsensusDescCapacity * 16


-- @@ L399-402 verbatim
/-- Amsterdam SSZ execution-request capacity:
    deposits 8192*192, withdrawals 16*76, consolidations 2*116, plus the
    3-entry offset table used by the guest's flattened request-section body. -/
def bvMaxDepositRequestBodyBytes : Nat := 8192 * 192

-- @@ L403-404 verbatim
def bvMaxExecutionRequestSectionBytes : Nat :=
  12 + bvMaxDepositRequestBodyBytes + 16 * 76 + 2 * 116


-- @@ L406-408 verbatim
/-- One canonicalized EIP-6110 deposit log record has the common 80-byte
    log-record header plus the 576-byte DepositEvent ABI payload. -/
def bvDepositLogRecordBytes : Nat := 80 + 576


-- @@ L410-413 verbatim
/-- Protocol target for execution-derived EIP-6110 deposit log-record staging
    before `parse_deposit_requests`. Upstream block-log descriptor/data capture
    has independent capacity work under `evm-asm-vv4hr.3`. -/
def bvMaxDepositLogRecordBytes : Nat := 8192 * bvDepositLogRecordBytes


-- @@ L415-422 verbatim
/-- `c1_staging` (system-call payload buffer) byte size: must hold
    round8(predeploy codelen) + preload_count*64 + m29_count*32 + 584.
    Predeploy code comes from the witness and is NOT EIP-170-bounded, but the
    whole witness is <= `bsrMaxWitnessBytes`; preloads <= `bsrAccountSlotCap`;
    m29 <= 256 hashes (8 KiB) + 584 header fit in the 16 KiB slack. The
    `stage_system_call_payload` size guard uses this same constant (it bails
    soundly on anything larger instead of corrupting `.data`). -/
def c1StagingBytes : Nat := bsrMaxWitnessBytes + bsrAccountSlotCap * 64 + 16384

-- @@ L423-423 verbatim
def bsrAccountRecordBytes : Nat := 24

-- @@ L424-424 verbatim
def bsrPathBytes : Nat := 64

-- @@ L425-425 verbatim
def bsrEncodedAccountBytes : Nat := 256

-- @@ L426-429 verbatim
/-- A storage leaf contains the RLP encoding of a minimal unsigned 256-bit
    integer: at most 32 payload bytes plus its one-byte string prefix.  Zero
    is represented by a deletion descriptor and is never stored as a leaf. -/
def bsrEncodedStorageValueBytes : Nat := 33

-- @@ L430-430 verbatim
def bsrSystemAccountBytes : Nat := 128

-- @@ L431-431 verbatim
def bsrStateChangeBytes : Nat := 40

-- @@ L432-432 verbatim
def baapStorageDescBytes : Nat := 40


-- @@ L434-437 verbatim
/-- Current static multi-transaction fixture arena capacity. The verdict guest's
    active per-tx u64/log-window buffers are still sized to this bound while the
    full-capacity migration lands in smaller slices. -/
def bmvFixtureTxCapacity : Nat := 16


-- @@ L439-439 verbatim
def bmvFullTxCapacity : Nat := bvMtxFullTxCap


-- @@ L441-441 verbatim
def bmvU64PerTxArenaBytes (txCapacity : Nat) : Nat := txCapacity * 8

-- @@ L442-442 verbatim
def bmvLogWindowPerTxArenaBytes (txCapacity : Nat) : Nat := txCapacity * 16


-- @@ L444-445 verbatim
def bmvFixtureU64PerTxArenaBytes : Nat :=
  bmvU64PerTxArenaBytes bmvFixtureTxCapacity


-- @@ L447-448 verbatim
def bmvFixtureLogWindowArenaBytes : Nat :=
  bmvLogWindowPerTxArenaBytes bmvFixtureTxCapacity


-- @@ L450-451 verbatim
def bmvFullU64PerTxArenaBytes : Nat :=
  bmvU64PerTxArenaBytes bmvFullTxCapacity


-- @@ L453-454 verbatim
def bmvFullLogWindowArenaBytes : Nat :=
  bmvLogWindowPerTxArenaBytes bmvFullTxCapacity


-- @@ L456-456 verbatim
#guard bvMtxSenderBalanceEntries = bvMtxFullTxCap

-- @@ L457-457 verbatim
#guard bvMtxSenderBalanceTableBytes = bvMtxFullTxCap * 64

-- @@ L458-458 verbatim
#guard bvMtxCreatedRecipientBytes = 533312

-- @@ L459-459 verbatim
#guard bvMtxSkipListEntries = 33333

-- @@ L460-460 verbatim
#guard bvMtxSkipListBytes = 1066656

-- @@ L461-461 verbatim
#guard bvMtxSenderCountEntries = 16666

-- @@ L462-462 verbatim
#guard bvMtxSenderCountTableBytes = 666640

-- @@ L463-463 verbatim
#guard bvMtxSenderCountSortBytes = 533312

-- @@ L464-464 verbatim
#guard bvMtxSenderCountSkipBytes = 1066624

-- @@ L465-465 verbatim
#guard bvMtxActiveTxCap = bvMtxFullTxCap

-- @@ L466-466 verbatim
#guard bvMtxFullTxCap = 16666

-- @@ L467-467 verbatim
#guard bvMtxArenaTxCap = bvMtxActiveTxCap

-- @@ L468-468 verbatim
#guard bvMtxU64ArenaBytes = 133328

-- @@ L469-469 verbatim
#guard bvMtxLogWindowBytes = 266656

-- @@ L470-470 verbatim
#guard bmvFullTxCapacity = 16666

-- @@ L471-471 verbatim
#guard bmvFullU64PerTxArenaBytes = 133328

-- @@ L472-472 verbatim
#guard bmvFullLogWindowArenaBytes = 266656

-- @@ L473-473 verbatim
#guard bvReceiptRecordsBytes = 1066624

-- @@ L474-474 verbatim
#guard bvResourceBlockGasLimit = 200000000

-- @@ L475-475 verbatim
#guard bsrBalGasCost = 2000

-- @@ L476-476 verbatim
#guard bsrMaxBalItems = bsrStateRootBlockGasLimit / bsrBalGasCost

-- @@ L477-477 verbatim
#guard bsrMaxBalItems = 100000

-- @@ L478-478 verbatim
#guard bsrMaxStateChanges = 100018

-- @@ L479-479 verbatim
#guard bsrMptBuilderFrameCapacity = 65

-- @@ L480-480 verbatim
#guard bvBlockLogFullDescTarget = 533333

-- @@ L481-481 verbatim
#guard bvBlockLogFullDescBytes = 136533248

-- @@ L482-482 verbatim
#guard bvBlockLogFullMetaBytes = 8533328

-- @@ L483-485 verbatim
#guard bvBlockLogFullDataBytes = 25000000
-- vv4hr.3.4.2 PACK: active descriptor arena = packed 32 B/gas-unit (~16.3 MiB)
-- and the meta table widened to 24 B/log (adds the packed desc byte-offset).

-- @@ L486-486 verbatim
#guard bvBlockLogPackedDescBytes = 17066656

-- @@ L487-487 verbatim
#guard bvBlockLogDescBytes = 17066656

-- @@ L488-488 verbatim
#guard bvBlockLogMetaBytes = 12799992

-- @@ L489-489 verbatim
#guard bvBlockLogDataBytes = 25000000

-- @@ L490-490 verbatim
#guard bvRecordBloomsBytes = 4266496

-- @@ L491-491 verbatim
#guard bvRecordLogsDescBytes = 533312

-- @@ L492-492 verbatim
#guard bvReceiptConsensusDescBytes = 266656

-- @@ L493-493 verbatim
#guard bvMaxDepositRequestBodyBytes = 1572864

-- @@ L494-494 verbatim
#guard bvMaxExecutionRequestSectionBytes = 1574324

-- @@ L495-495 verbatim
#guard bvDepositLogRecordBytes = 656

-- @@ L496-496 verbatim
#guard bvMaxDepositLogRecordBytes = 5373952


-- @@ L498-498 verbatim
end EvmAsm.Codegen
