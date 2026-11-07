/-
  Concrete construction glue for the bare-mode Sail memory reductions.

  The memory reduction theorems are intentionally stated against a `BareModeInv`
  plus access-local PMA/MMIO facts.  This file discharges those facts for the
  concrete platform shape installed by `sail_model_init`: the initializer's three
  PMA regions are reproduced verbatim (`sailInitPmaRegions`), a representative
  main-memory address (`sailRamWitnessAddr`) is proved aligned, PMA-matched to
  the main-memory region, readable, and writable; zeroed PMP configs decode to
  `OFF` (`zeroPmpcfgs_off`); and `bareModeWitnessState_inv` exhibits a concrete
  Sail state satisfying `BareModeInv`.
-/

import EvmAsm.Rv64.SailEquiv.VmemReductionStores
import Mathlib.Data.Vector.Basic


-- @@ L17-17 verbatim
open RiscvZkvm.Sail.Functions

-- @@ L18-18 verbatim
open Sail


-- @@ L20-20 verbatim
namespace EvmAsm.Rv64.SailEquiv


-- @@ L22-46 verbatim
/-- First PMA region installed by `sail_model_init`: small read-only I/O. -/
def sailInitReadOnlyIoRegion : PMA_Region :=
  { base := 4096#64
    size := 4096#64
    attributes :=
      { mem_type := MemoryRegionType.IOMemory
        cacheable := true
        coherent := false
        executable := false
        readable := true
        writable := false
        read_idempotent := true
        write_idempotent := true
        misaligned_exceptions :=
          { load_store := none
            vector := none
            amo := misaligned_exception.AccessFault }
        atomic_support := AtomicSupport.AMONone
        reservability := Reservability.RsrvNone
        supports_cbo_zero := false
        supports_pte_read := false
        supports_pte_write := false
        misaligned_atomicity_granule_size_exp := 0
        vector_misaligned_atomicity_granule_size_exp := 0 }
    include_in_device_tree := false }


-- @@ L48-72 verbatim
/-- Second PMA region installed by `sail_model_init`: CLINT/signature I/O window. -/
def sailInitIoRegion : PMA_Region :=
  { base := 33554432#64
    size := 268435456#64
    attributes :=
      { mem_type := MemoryRegionType.IOMemory
        cacheable := false
        coherent := true
        executable := false
        readable := true
        writable := true
        read_idempotent := false
        write_idempotent := false
        misaligned_exceptions :=
          { load_store := none
            vector := none
            amo := misaligned_exception.AccessFault }
        atomic_support := AtomicSupport.AMONone
        reservability := Reservability.RsrvNone
        supports_cbo_zero := false
        supports_pte_read := false
        supports_pte_write := false
        misaligned_atomicity_granule_size_exp := 0
        vector_misaligned_atomicity_granule_size_exp := 0 }
    include_in_device_tree := false }


-- @@ L74-98 verbatim
/-- Main-memory PMA region installed by `sail_model_init`. -/
def sailInitMainMemoryRegion : PMA_Region :=
  { base := 2147483648#64
    size := 2147483648#64
    attributes :=
      { mem_type := MemoryRegionType.MainMemory
        cacheable := true
        coherent := true
        executable := true
        readable := true
        writable := true
        read_idempotent := true
        write_idempotent := true
        misaligned_exceptions :=
          { load_store := none
            vector := none
            amo := misaligned_exception.AccessFault }
        atomic_support := AtomicSupport.AMOCASQ
        reservability := Reservability.RsrvEventual
        supports_cbo_zero := true
        supports_pte_read := true
        supports_pte_write := true
        misaligned_atomicity_granule_size_exp := 4
        vector_misaligned_atomicity_granule_size_exp := 4 }
    include_in_device_tree := true }


-- @@ L100-102 verbatim
/-- The concrete PMA region list written by `sail_model_init`. -/
def sailInitPmaRegions : List PMA_Region :=
  [sailInitReadOnlyIoRegion, sailInitIoRegion, sailInitMainMemoryRegion]


-- @@ L104-105 verbatim
/-- A concrete dword-aligned zkVM RAM address inside the initializer's main-memory PMA. -/
def sailRamWitnessAddr : BitVec 64 := 0xa0000000#64


-- @@ L107-109 verbatim
theorem sailRamWitness_vaddr_aligned :
    is_aligned_vaddr (virtaddr.Virtaddr sailRamWitnessAddr) 8 = true := by
  simp [sailRamWitnessAddr, is_aligned_vaddr, BitVec.toNatInt]


-- @@ L111-113 verbatim
theorem sailRamWitness_paddr_aligned :
    is_aligned_paddr (physaddr.Physaddr sailRamWitnessAddr) 8 = true := by
  simp [sailRamWitnessAddr, is_aligned_paddr, BitVec.toNatInt]


-- @@ L115-121 verbatim
theorem sailRamWitness_matching_pma :
    matching_pma_region sailInitPmaRegions (physaddr.Physaddr sailRamWitnessAddr) 8 =
      some sailInitMainMemoryRegion := by
  simp [sailInitPmaRegions, sailInitReadOnlyIoRegion, sailInitIoRegion,
    sailInitMainMemoryRegion, sailRamWitnessAddr, matching_pma_region,
    matching_pma_region_bits_range, range_subset, zero_extend, Sail.BitVec.zeroExtend,
    to_bits, get_slice_int, BitVec.toNatInt, zopz0zIzJ_u, bits_of_physaddr]


-- @@ L123-125 verbatim
theorem sailInitMainMemoryRegion_readable :
    sailInitMainMemoryRegion.attributes.readable = true := by
  rfl


-- @@ L127-129 verbatim
theorem sailInitMainMemoryRegion_writable :
    sailInitMainMemoryRegion.attributes.writable = true := by
  rfl


-- @@ L131-132 verbatim
/-- Zeroed PMP config vector: every entry decodes as `OFF`. -/
def zeroPmpcfgs : Vector (BitVec 8) 64 := Vector.replicate 64 0#8


-- @@ L134-135 verbatim
/-- Zeroed PMP address vector. -/
def zeroPmpaddrs : Vector (BitVec 64) 64 := Vector.replicate 64 0#64


-- @@ L137-147 verbatim
theorem zeroPmpcfgs_off (i : Nat) :
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (zeroPmpcfgs[i]!)) =
      PmpAddrMatchType.OFF := by
  by_cases h_i : i < 64
  · rw [getElem!_pos zeroPmpcfgs i h_i]
    simp [zeroPmpcfgs, Vector.getElem_replicate, pmpAddrMatchType_encdec_backwards,
      _get_Pmpcfg_ent_A, Sail.BitVec.extractLsb]
  · rw [getElem!_neg zeroPmpcfgs i h_i]
    change pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (0#8)) =
      PmpAddrMatchType.OFF
    simp [pmpAddrMatchType_encdec_backwards, _get_Pmpcfg_ent_A, Sail.BitVec.extractLsb]


-- @@ L149-156 verbatim
/-- A concrete bare-mode Sail state with the initializer PMA table installed. -/
def bareModeWitnessState : SailState :=
  { (default : SailState) with
    regs :=
      ((((((default : SailState).regs.insert Register.cur_privilege Privilege.Machine).insert
        Register.mstatus 0#64).insert Register.mseccfg 0#64).insert
        Register.pmpcfg_n zeroPmpcfgs).insert Register.pmpaddr_n zeroPmpaddrs).insert
        Register.pma_regions sailInitPmaRegions }


-- @@ L158-181 verbatim
def bareModeWitnessState_inv : BareModeInv bareModeWitnessState := by
  refine
    { mst := 0#64
      msec := 0#64
      cfgs := zeroPmpcfgs
      pmpaddrs := zeroPmpaddrs
      regions := sailInitPmaRegions
      h_priv := ?_
      h_mst := ?_
      h_mprv := ?_
      h_sec := ?_
      h_pmm := ?_
      h_cfg := ?_
      h_pmpaddr := ?_
      h_off := zeroPmpcfgs_off
      h_reg := ?_ }
  · simp [bareModeWitnessState, Std.ExtDHashMap.get?_insert]
  · simp [bareModeWitnessState, Std.ExtDHashMap.get?_insert]
  · simp [_get_Mstatus_MPRV, Sail.BitVec.extractLsb]
  · simp [bareModeWitnessState, Std.ExtDHashMap.get?_insert]
  · simp [_get_Seccfg_PMM, Sail.BitVec.extractLsb]
  · simp [bareModeWitnessState, zeroPmpcfgs, Std.ExtDHashMap.get?_insert]
  · simp [bareModeWitnessState, zeroPmpaddrs, Std.ExtDHashMap.get?_insert]
  · simp [bareModeWitnessState]


-- @@ L183-183 verbatim
end EvmAsm.Rv64.SailEquiv
