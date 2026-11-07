/-
  EvmAsm.Rv64.RLP.UnifiedHeteroFieldWalk

  EL.3 / Phase 5 — the first HETEROGENEOUS multi-field walk: a scalar field followed by a
  byte-array field, both decoded into ONE shared whole-struct output `bytesRegion`. This is
  the keystone that ties the two field-type decoders together — real STF schemas (legacy
  tx, block header) interleave u64 scalars (`nonce`, `gas`) with fixed byte arrays
  (20-byte `address`, 32-byte hash).

  Field A (scalar, `1 ≤ len ≤ 8`) is decoded by `unified_scalar_field_decode_and_store_region`
  (concrete scratch pre), which spills its u64 value little-endian into the output region at
  byte offset `diA` and advances `x13` to the next field. Field B (byte array, `1 ≤ len ≤ 55`)
  is decoded by `unified_bytes_field_decode_and_copy_at_regOwn` (the `regOwn`-pre variant,
  callable after A clobbered the scratch), which copies its payload into the output region at
  byte offset `diB`. A's `x13` feeds B's payload pointer with no glue; the output region is
  threaded directly (A's `spillRange` is B's input `bytesRegion`), so the final region holds
  both fields. Coincides with the scalar peel for A and the item-decode peel for B.

  Layout (program base `base`; aligned `regionBase`/`bs`, output `outBase`/`outBytes`):
      base       < scalar field A : decode + spill into region >   (base .. base+280)
      base+280   < byte field  B : decode + copy  into region >    (base+280 .. base+432+20·|dataB|)
-/

import EvmAsm.Rv64.RLP.UnifiedScalarFieldRegion
import EvmAsm.Rv64.RLP.UnifiedBytesFieldRegOwn


-- @@ L27-27 verbatim
namespace EvmAsm.Rv64.RLP


-- @@ L29-29 verbatim
open EvmAsm.Rv64

-- @@ L30-30 verbatim
open EvmAsm.EL.RLP

-- @@ L31-31 verbatim
open EvmAsm.Rv64.Tactics


-- @@ L33-38 verbatim
/-- Spilling preserves the destination list's length (it is a sequence of `List.set`s). -/
theorem spillRange_length (dst : List Byte) (v : Word) (di0 N : Nat) :
    (spillRange dst v di0 N).length = dst.length := by
  induction N generalizing dst v di0 with
  | zero => rfl
  | succ n ih => rw [spillRange, ih, List.length_set]


-- @@ L40-40 verbatim
end EvmAsm.Rv64.RLP
