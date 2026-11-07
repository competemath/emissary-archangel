/-
  EvmAsm.Codegen.RegionMapLinkPins

  GENERATED — do not edit by hand.
  `python3 scripts/gen-region-map-link-pins.py` regenerates this from the
  linked stateless_guest ELF (issue #11230).

  Link-layout-dependent pins only (class A): section sizes and two
  BSS bases, which move when the guest image moves. Class B stable
  bases stay hand-typed in RegionMap.lean; `.state_gas_diag`'s base is
  neither — RegionMap DERIVES it from `bssSizeBytes` (GH #11186).

  Regenerated from: gen-out/regionmap/stateless_guest.elf
  Guard contract (check-region-map.sh): pins are this file (regen-time
  ELF reading); expectation is readelf/nm of the ELF built at *check*
  time. Two independent readings of two artefacts. Catches: image moved
  and nobody regenerated.
-/

module


-- @@ L22-22 verbatim
@[expose] public section

-- @@ L23-23 verbatim
namespace EvmAsm.Codegen.RegionMapLinkPins


-- @@ L25-25 verbatim
abbrev textSizeBytes : Nat := 0x543e8

-- @@ L26-26 verbatim
abbrev dataSizeBytes : Nat := 0x5310

-- @@ L27-27 verbatim
abbrev bssSizeBytes : Nat := 0x1affaf00


-- @@ L29-29 verbatim
abbrev stateGasDiagSizeBytes : Nat := 0x61a78


-- @@ L31-31 verbatim
abbrev callFrameArenaBase : Nat := 0xabf6dc00

-- @@ L32-32 verbatim
abbrev evmMemoryPoolBase : Nat := 0xb2386c00


-- @@ L34-34 verbatim
end EvmAsm.Codegen.RegionMapLinkPins
