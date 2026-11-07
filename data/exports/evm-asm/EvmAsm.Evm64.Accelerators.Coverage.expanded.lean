/-
  EvmAsm.Evm64.Accelerators.Coverage

  Checked coverage table for the 19 functions declared by
  `zkvm_accelerators.h`. This mirrors the human-facing audit table in
  `docs/zkvm-accelerators-interface.md` while keeping the selector count,
  selector uniqueness, and accelerator range checked by Lean.
-/

module

public import EvmAsm.Evm64.Accelerators.Dispatch


-- @@ L14-14 verbatim
@[expose] public section


-- @@ L16-16 verbatim
namespace EvmAsm

-- @@ L17-17 verbatim
namespace Accelerators


-- @@ L19-19 verbatim
open SyscallId


-- @@ L21-26 verbatim
/-- EVM-facing surface that uses a zkVM accelerator. -/
inductive AcceleratorSurface where
  | opcode (name : String)
  | precompile (address : Nat) (name : String)
  | nonPrecompile (name : String)
  deriving DecidableEq, Repr


-- @@ L28-33 verbatim
/-- One row of the zkVM accelerator coverage table. -/
structure AcceleratorCoverage where
  cSymbol : String
  selector : Nat
  surface : AcceleratorSurface
  deriving DecidableEq, Repr


-- @@ L35-93 verbatim
/-- The 19 `zkvm_accelerators.h` functions and the selector assigned to each. -/
def acceleratorCoverageTable : List AcceleratorCoverage :=
  [{ cSymbol := "zkvm_keccak256",
     selector := keccak256,
     surface := .opcode "KECCAK256" },
   { cSymbol := "zkvm_secp256k1_verify",
     selector := secp256k1_verify,
     surface := .nonPrecompile "secp256k1 signature verify" },
   { cSymbol := "zkvm_secp256k1_ecrecover",
     selector := secp256k1_ecrecover,
     surface := .precompile 0x01 "ECRECOVER" },
   { cSymbol := "zkvm_sha256",
     selector := sha256,
     surface := .precompile 0x02 "SHA256" },
   { cSymbol := "zkvm_ripemd160",
     selector := ripemd160,
     surface := .precompile 0x03 "RIPEMD160" },
   { cSymbol := "zkvm_modexp",
     selector := modexp,
     surface := .precompile 0x05 "MODEXP" },
   { cSymbol := "zkvm_bn254_g1_add",
     selector := bn254_g1_add,
     surface := .precompile 0x06 "BN254 G1 ADD" },
   { cSymbol := "zkvm_bn254_g1_mul",
     selector := bn254_g1_mul,
     surface := .precompile 0x07 "BN254 G1 MUL" },
   { cSymbol := "zkvm_bn254_pairing",
     selector := bn254_pairing,
     surface := .precompile 0x08 "BN254 PAIRING" },
   { cSymbol := "zkvm_blake2f",
     selector := blake2f,
     surface := .precompile 0x09 "BLAKE2F" },
   { cSymbol := "zkvm_kzg_point_eval",
     selector := kzg_point_eval,
     surface := .precompile 0x0a "KZG POINT EVAL" },
   { cSymbol := "zkvm_bls12_g1_add",
     selector := bls12_g1_add,
     surface := .precompile 0x0b "BLS12 G1 ADD" },
   { cSymbol := "zkvm_bls12_g1_msm",
     selector := bls12_g1_msm,
     surface := .precompile 0x0c "BLS12 G1 MSM" },
   { cSymbol := "zkvm_bls12_g2_add",
     selector := bls12_g2_add,
     surface := .precompile 0x0d "BLS12 G2 ADD" },
   { cSymbol := "zkvm_bls12_g2_msm",
     selector := bls12_g2_msm,
     surface := .precompile 0x0e "BLS12 G2 MSM" },
   { cSymbol := "zkvm_bls12_pairing",
     selector := bls12_pairing,
     surface := .precompile 0x0f "BLS12 PAIRING" },
   { cSymbol := "zkvm_bls12_map_fp_to_g1",
     selector := bls12_map_fp_to_g1,
     surface := .precompile 0x10 "BLS12 MAP FP TO G1" },
   { cSymbol := "zkvm_bls12_map_fp2_to_g2",
     selector := bls12_map_fp2_to_g2,
     surface := .precompile 0x11 "BLS12 MAP FP2 TO G2" },
   { cSymbol := "zkvm_secp256r1_verify",
     selector := secp256r1_verify,
     surface := .precompile 0x100 "secp256r1 verify" }]


-- @@ L95-98 verbatim
/-- The checked coverage table has one row per accelerator C function. -/
theorem acceleratorCoverageTable_length :
    acceleratorCoverageTable.length = 19 := by
  decide


-- @@ L100-102 verbatim
/-- Selectors projected from the coverage table. -/
def acceleratorCoverageSelectors : List Nat :=
  acceleratorCoverageTable.map (fun row => row.selector)


-- @@ L104-114 verbatim
/-- The coverage-table selectors match the canonical selector list. -/
theorem acceleratorCoverageSelectors_eq :
    acceleratorCoverageSelectors =
      [keccak256, secp256k1_verify,
       secp256k1_ecrecover, sha256, ripemd160, modexp,
       bn254_g1_add, bn254_g1_mul, bn254_pairing,
       blake2f, kzg_point_eval,
       bls12_g1_add, bls12_g1_msm, bls12_g2_add, bls12_g2_msm,
       bls12_pairing, bls12_map_fp_to_g1, bls12_map_fp2_to_g2,
       secp256r1_verify] := by
  decide


-- @@ L116-120 verbatim
/-- The coverage table and dispatch module use the same canonical selectors. -/
theorem acceleratorCoverageSelectors_eq_dispatch :
    acceleratorCoverageSelectors = acceleratorSelectors := by
  rw [acceleratorCoverageSelectors_eq]
  rfl


-- @@ L122-127 verbatim
/-- Every selector row in the coverage table is routed by accelerator dispatch. -/
theorem acceleratorCoverageSelectors_are_accelerators :
    ∀ id ∈ acceleratorCoverageSelectors, isAccelerator id := by
  intro id h_id
  rw [acceleratorCoverageSelectors_eq_dispatch] at h_id
  exact h_id


-- @@ L129-132 verbatim
/-- Every coverage-table row has a selector recognised by accelerator dispatch. -/
theorem acceleratorCoverageTable_selectors_are_accelerators :
    ∀ row ∈ acceleratorCoverageTable, isAccelerator row.selector := by
  decide


-- @@ L134-138 verbatim
/-- The coverage table does not assign the same selector twice. -/
theorem acceleratorCoverageSelectors_nodup :
    acceleratorCoverageSelectors.Nodup := by
  rw [acceleratorCoverageSelectors_eq]
  decide


-- @@ L140-144 verbatim
/-- Every selector in the coverage table is in the reserved accelerator range. -/
theorem acceleratorCoverageSelectors_in_range :
    ∀ id ∈ acceleratorCoverageSelectors, 0x100 ≤ id ∧ id < 0x113 := by
  rw [acceleratorCoverageSelectors_eq]
  decide


-- @@ L146-148 verbatim
/-- C symbols projected from the coverage table. -/
def acceleratorCoverageSymbols : List String :=
  acceleratorCoverageTable.map (fun row => row.cSymbol)


-- @@ L150-172 verbatim
/-- Exact `zkvm_accelerators.h` C-symbol order represented by the table. -/
theorem acceleratorCoverageSymbols_eq :
    acceleratorCoverageSymbols =
      ["zkvm_keccak256",
       "zkvm_secp256k1_verify",
       "zkvm_secp256k1_ecrecover",
       "zkvm_sha256",
       "zkvm_ripemd160",
       "zkvm_modexp",
       "zkvm_bn254_g1_add",
       "zkvm_bn254_g1_mul",
       "zkvm_bn254_pairing",
       "zkvm_blake2f",
       "zkvm_kzg_point_eval",
       "zkvm_bls12_g1_add",
       "zkvm_bls12_g1_msm",
       "zkvm_bls12_g2_add",
       "zkvm_bls12_g2_msm",
       "zkvm_bls12_pairing",
       "zkvm_bls12_map_fp_to_g1",
       "zkvm_bls12_map_fp2_to_g2",
       "zkvm_secp256r1_verify"] := by
  decide


-- @@ L174-178 verbatim
/-- The coverage table has one C symbol for each accelerator entry point. -/
theorem acceleratorCoverageSymbols_length :
    acceleratorCoverageSymbols.length = 19 := by
  rw [acceleratorCoverageSymbols_eq]
  decide


-- @@ L180-184 verbatim
/-- The coverage table lists each `zkvm_accelerators.h` C symbol once. -/
theorem acceleratorCoverageSymbols_nodup :
    acceleratorCoverageSymbols.Nodup := by
  rw [acceleratorCoverageSymbols_eq]
  decide


-- @@ L186-195 verbatim
/-- Ethereum precompile addresses covered by accelerator-backed rows.

This excludes the non-precompile KECCAK256 and secp256k1 verification
accelerators and also excludes IDENTITY (`0x04`), which is pure memory copy
and has no accelerator C symbol. -/
def acceleratorPrecompileAddresses : List Nat :=
  acceleratorCoverageTable.filterMap fun row =>
    match row.surface with
    | .precompile address _ => some address
    | _ => none


-- @@ L197-204 verbatim
/-- The accelerator-backed precompile address set mirrors `zkvm_accelerators.h`.

Address `0x04` is intentionally absent because IDENTITY has no accelerator. -/
theorem acceleratorPrecompileAddresses_eq :
    acceleratorPrecompileAddresses =
      [0x01, 0x02, 0x03, 0x05, 0x06, 0x07, 0x08, 0x09,
       0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x100] := by
  decide


-- @@ L206-210 verbatim
/-- No precompile address is assigned to more than one accelerator row. -/
theorem acceleratorPrecompileAddresses_nodup :
    acceleratorPrecompileAddresses.Nodup := by
  rw [acceleratorPrecompileAddresses_eq]
  decide


-- @@ L212-216 verbatim
/-- IDENTITY (`0x04`) is not accelerator-backed. -/
theorem identity_not_mem_acceleratorPrecompileAddresses :
    0x04 ∉ acceleratorPrecompileAddresses := by
  rw [acceleratorPrecompileAddresses_eq]
  decide


-- @@ L218-220 verbatim
/-- EVM-facing surfaces projected from the coverage table. -/
def acceleratorCoverageSurfaces : List AcceleratorSurface :=
  acceleratorCoverageTable.map (fun row => row.surface)


-- @@ L222-244 verbatim
/-- Exact EVM-facing surface order represented by the coverage table. -/
theorem acceleratorCoverageSurfaces_eq :
    acceleratorCoverageSurfaces =
      [.opcode "KECCAK256",
       .nonPrecompile "secp256k1 signature verify",
       .precompile 0x01 "ECRECOVER",
       .precompile 0x02 "SHA256",
       .precompile 0x03 "RIPEMD160",
       .precompile 0x05 "MODEXP",
       .precompile 0x06 "BN254 G1 ADD",
       .precompile 0x07 "BN254 G1 MUL",
       .precompile 0x08 "BN254 PAIRING",
       .precompile 0x09 "BLAKE2F",
       .precompile 0x0a "KZG POINT EVAL",
       .precompile 0x0b "BLS12 G1 ADD",
       .precompile 0x0c "BLS12 G1 MSM",
       .precompile 0x0d "BLS12 G2 ADD",
       .precompile 0x0e "BLS12 G2 MSM",
       .precompile 0x0f "BLS12 PAIRING",
       .precompile 0x10 "BLS12 MAP FP TO G1",
       .precompile 0x11 "BLS12 MAP FP2 TO G2",
       .precompile 0x100 "secp256r1 verify"] := by
  decide


-- @@ L246-250 verbatim
/-- Every row has a unique EVM-facing surface. -/
theorem acceleratorCoverageSurfaces_nodup :
    acceleratorCoverageSurfaces.Nodup := by
  rw [acceleratorCoverageSurfaces_eq]
  decide


-- @@ L252-257 verbatim
/-- Accelerator C symbols used by EVM opcodes rather than precompile surfaces. -/
def acceleratorOpcodeSymbols : List String :=
  acceleratorCoverageTable.filterMap fun row =>
    match row.surface with
    | .opcode _ => some row.cSymbol
    | _ => none


-- @@ L259-264 verbatim
/-- Accelerator C symbols used outside the precompile table. -/
def acceleratorNonPrecompileSymbols : List String :=
  acceleratorCoverageTable.filterMap fun row =>
    match row.surface with
    | .nonPrecompile _ => some row.cSymbol
    | _ => none


-- @@ L266-271 verbatim
/-- Accelerator C symbols used by Ethereum precompile entry points. -/
def acceleratorPrecompileSymbols : List String :=
  acceleratorCoverageTable.filterMap fun row =>
    match row.surface with
    | .precompile _ _ => some row.cSymbol
    | _ => none


-- @@ L273-275 verbatim
theorem acceleratorOpcodeSymbols_eq :
    acceleratorOpcodeSymbols = ["zkvm_keccak256"] := by
  decide


-- @@ L277-279 verbatim
theorem acceleratorNonPrecompileSymbols_eq :
    acceleratorNonPrecompileSymbols = ["zkvm_secp256k1_verify"] := by
  decide


-- @@ L281-300 verbatim
theorem acceleratorPrecompileSymbols_eq :
    acceleratorPrecompileSymbols =
      ["zkvm_secp256k1_ecrecover",
       "zkvm_sha256",
       "zkvm_ripemd160",
       "zkvm_modexp",
       "zkvm_bn254_g1_add",
       "zkvm_bn254_g1_mul",
       "zkvm_bn254_pairing",
       "zkvm_blake2f",
       "zkvm_kzg_point_eval",
       "zkvm_bls12_g1_add",
       "zkvm_bls12_g1_msm",
       "zkvm_bls12_g2_add",
       "zkvm_bls12_g2_msm",
       "zkvm_bls12_pairing",
       "zkvm_bls12_map_fp_to_g1",
       "zkvm_bls12_map_fp2_to_g2",
       "zkvm_secp256r1_verify"] := by
  decide


-- @@ L302-305 verbatim
theorem acceleratorOpcodeSymbols_length :
    acceleratorOpcodeSymbols.length = 1 := by
  rw [acceleratorOpcodeSymbols_eq]
  decide


-- @@ L307-310 verbatim
theorem acceleratorNonPrecompileSymbols_length :
    acceleratorNonPrecompileSymbols.length = 1 := by
  rw [acceleratorNonPrecompileSymbols_eq]
  decide


-- @@ L312-315 verbatim
theorem acceleratorPrecompileSymbols_length :
    acceleratorPrecompileSymbols.length = 17 := by
  rw [acceleratorPrecompileSymbols_eq]
  decide


-- @@ L317-320 verbatim
theorem acceleratorPrecompileSymbols_nodup :
    acceleratorPrecompileSymbols.Nodup := by
  rw [acceleratorPrecompileSymbols_eq]
  decide


-- @@ L322-326 verbatim
theorem acceleratorPrecompileSymbols_subset_coverage :
    ∀ symbol ∈ acceleratorPrecompileSymbols,
      symbol ∈ acceleratorCoverageSymbols := by
  rw [acceleratorPrecompileSymbols_eq, acceleratorCoverageSymbols_eq]
  decide


-- @@ L328-328 verbatim
/-! ### Hash precompile slice -/


-- @@ L330-332 verbatim
/-- Hash-family precompile accelerator C symbols tracked by `evm-asm-yvfgi`. -/
def hashPrecompileSymbols : List String :=
  ["zkvm_sha256", "zkvm_ripemd160", "zkvm_blake2f"]


-- @@ L334-337 verbatim
theorem hashPrecompileSymbols_subset_precompiles :
    ∀ symbol ∈ hashPrecompileSymbols, symbol ∈ acceleratorPrecompileSymbols := by
  rw [hashPrecompileSymbols, acceleratorPrecompileSymbols_eq]
  decide


-- @@ L339-342 verbatim
theorem hashPrecompileSymbols_nodup :
    hashPrecompileSymbols.Nodup := by
  rw [hashPrecompileSymbols]
  decide


-- @@ L344-346 verbatim
/-- EVM precompile addresses covered by the hash-family accelerator slice. -/
def hashPrecompileAddresses : List Nat :=
  [0x02, 0x03, 0x09]


-- @@ L348-352 verbatim
theorem hashPrecompileAddresses_subset_acceleratorPrecompileAddresses :
    ∀ address ∈ hashPrecompileAddresses,
      address ∈ acceleratorPrecompileAddresses := by
  rw [hashPrecompileAddresses, acceleratorPrecompileAddresses_eq]
  decide


-- @@ L354-357 verbatim
theorem hashPrecompileAddresses_nodup :
    hashPrecompileAddresses.Nodup := by
  rw [hashPrecompileAddresses]
  decide


-- @@ L359-359 verbatim
/-! ### secp256k1 accelerator slice -/


-- @@ L361-363 verbatim
/-- secp256k1-family accelerator C symbols tracked by `evm-asm-g8tgi`. -/
def secp256k1AcceleratorSymbols : List String :=
  ["zkvm_secp256k1_verify", "zkvm_secp256k1_ecrecover"]


-- @@ L365-369 verbatim
theorem secp256k1AcceleratorSymbols_subset_coverage :
    ∀ symbol ∈ secp256k1AcceleratorSymbols,
      symbol ∈ acceleratorCoverageSymbols := by
  rw [secp256k1AcceleratorSymbols, acceleratorCoverageSymbols_eq]
  decide


-- @@ L371-374 verbatim
theorem secp256k1AcceleratorSymbols_nodup :
    secp256k1AcceleratorSymbols.Nodup := by
  rw [secp256k1AcceleratorSymbols]
  decide


-- @@ L376-378 verbatim
/-- EVM precompile addresses covered by the secp256k1 accelerator slice. -/
def secp256k1PrecompileAddresses : List Nat :=
  [0x01]


-- @@ L380-384 verbatim
theorem secp256k1PrecompileAddresses_subset_acceleratorPrecompileAddresses :
    ∀ address ∈ secp256k1PrecompileAddresses,
      address ∈ acceleratorPrecompileAddresses := by
  rw [secp256k1PrecompileAddresses, acceleratorPrecompileAddresses_eq]
  decide


-- @@ L386-389 verbatim
theorem secp256k1PrecompileAddresses_nodup :
    secp256k1PrecompileAddresses.Nodup := by
  rw [secp256k1PrecompileAddresses]
  decide


-- @@ L391-391 verbatim
/-! ### Curve, pairing, KZG, and MODEXP precompile slice -/


-- @@ L393-407 verbatim
/-- Curve-arithmetic, pairing, KZG, and MODEXP accelerator C symbols tracked by
`evm-asm-bc3sd`. -/
def curvePrecompileSymbols : List String :=
  ["zkvm_modexp",
   "zkvm_bn254_g1_add",
   "zkvm_bn254_g1_mul",
   "zkvm_bn254_pairing",
   "zkvm_kzg_point_eval",
   "zkvm_bls12_g1_add",
   "zkvm_bls12_g1_msm",
   "zkvm_bls12_g2_add",
   "zkvm_bls12_g2_msm",
   "zkvm_bls12_pairing",
   "zkvm_bls12_map_fp_to_g1",
   "zkvm_bls12_map_fp2_to_g2"]


-- @@ L409-413 verbatim
theorem curvePrecompileSymbols_subset_precompiles :
    ∀ symbol ∈ curvePrecompileSymbols,
      symbol ∈ acceleratorPrecompileSymbols := by
  rw [curvePrecompileSymbols, acceleratorPrecompileSymbols_eq]
  decide


-- @@ L415-418 verbatim
theorem curvePrecompileSymbols_nodup :
    curvePrecompileSymbols.Nodup := by
  rw [curvePrecompileSymbols]
  decide


-- @@ L420-422 verbatim
/-- EVM precompile addresses covered by the curve/pairing/KZG/MODEXP slice. -/
def curvePrecompileAddresses : List Nat :=
  [0x05, 0x06, 0x07, 0x08, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11]


-- @@ L424-428 verbatim
theorem curvePrecompileAddresses_subset_acceleratorPrecompileAddresses :
    ∀ address ∈ curvePrecompileAddresses,
      address ∈ acceleratorPrecompileAddresses := by
  rw [curvePrecompileAddresses, acceleratorPrecompileAddresses_eq]
  decide


-- @@ L430-433 verbatim
theorem curvePrecompileAddresses_nodup :
    curvePrecompileAddresses.Nodup := by
  rw [curvePrecompileAddresses]
  decide


-- @@ L435-437 verbatim
def acceleratorClassifiedSymbols : List String :=
  acceleratorOpcodeSymbols ++ acceleratorNonPrecompileSymbols ++
    acceleratorPrecompileSymbols


-- @@ L439-444 verbatim
theorem acceleratorClassifiedSymbols_eq_coverage :
    acceleratorClassifiedSymbols = acceleratorCoverageSymbols := by
  rw [acceleratorClassifiedSymbols, acceleratorOpcodeSymbols_eq,
    acceleratorNonPrecompileSymbols_eq, acceleratorPrecompileSymbols_eq,
    acceleratorCoverageSymbols_eq]
  decide


-- @@ L446-448 verbatim
def acceleratorClassifiedSymbolCount : Nat :=
  acceleratorOpcodeSymbols.length + acceleratorNonPrecompileSymbols.length +
    acceleratorPrecompileSymbols.length


-- @@ L450-453 verbatim
theorem acceleratorClassifiedSymbolCount_eq :
    acceleratorClassifiedSymbolCount = 19 := by
  rw [acceleratorClassifiedSymbolCount, acceleratorOpcodeSymbols_length,
    acceleratorNonPrecompileSymbols_length, acceleratorPrecompileSymbols_length]


-- @@ L455-457 verbatim
theorem acceleratorClassifiedSymbols_length :
    acceleratorClassifiedSymbols.length = acceleratorCoverageSymbols.length := by
  rw [acceleratorClassifiedSymbols_eq_coverage]


-- @@ L459-462 verbatim
theorem acceleratorClassifiedSymbols_nodup :
    acceleratorClassifiedSymbols.Nodup := by
  rw [acceleratorClassifiedSymbols_eq_coverage]
  exact acceleratorCoverageSymbols_nodup


-- @@ L464-469 verbatim
/-- Accelerator selectors used by EVM opcodes rather than precompile surfaces. -/
def acceleratorOpcodeSelectors : List Nat :=
  acceleratorCoverageTable.filterMap fun row =>
    match row.surface with
    | .opcode _ => some row.selector
    | _ => none


-- @@ L471-476 verbatim
/-- Accelerator selectors used outside the precompile table. -/
def acceleratorNonPrecompileSelectors : List Nat :=
  acceleratorCoverageTable.filterMap fun row =>
    match row.surface with
    | .nonPrecompile _ => some row.selector
    | _ => none


-- @@ L478-483 verbatim
/-- Accelerator selectors used by Ethereum precompile entry points. -/
def acceleratorPrecompileSelectors : List Nat :=
  acceleratorCoverageTable.filterMap fun row =>
    match row.surface with
    | .precompile _ _ => some row.selector
    | _ => none


-- @@ L485-487 verbatim
theorem acceleratorOpcodeSelectors_eq :
    acceleratorOpcodeSelectors = [keccak256] := by
  decide


-- @@ L489-491 verbatim
theorem acceleratorNonPrecompileSelectors_eq :
    acceleratorNonPrecompileSelectors = [secp256k1_verify] := by
  decide


-- @@ L493-501 verbatim
theorem acceleratorPrecompileSelectors_eq :
    acceleratorPrecompileSelectors =
      [secp256k1_ecrecover, sha256, ripemd160, modexp,
       bn254_g1_add, bn254_g1_mul, bn254_pairing,
       blake2f, kzg_point_eval,
       bls12_g1_add, bls12_g1_msm, bls12_g2_add, bls12_g2_msm,
       bls12_pairing, bls12_map_fp_to_g1, bls12_map_fp2_to_g2,
       secp256r1_verify] := by
  decide


-- @@ L503-506 verbatim
theorem acceleratorPrecompileSelectors_length :
    acceleratorPrecompileSelectors.length = 17 := by
  rw [acceleratorPrecompileSelectors_eq]
  decide


-- @@ L508-511 verbatim
theorem acceleratorPrecompileSelectors_nodup :
    acceleratorPrecompileSelectors.Nodup := by
  rw [acceleratorPrecompileSelectors_eq]
  decide


-- @@ L513-516 verbatim
theorem acceleratorPrecompileSelectors_are_accelerators :
    ∀ id ∈ acceleratorPrecompileSelectors, isAccelerator id := by
  rw [acceleratorPrecompileSelectors_eq]
  decide


-- @@ L518-520 verbatim
/-- Accelerator selectors covered by the hash-family precompile slice. -/
def hashPrecompileSelectors : List Nat :=
  [sha256, ripemd160, blake2f]


-- @@ L522-525 verbatim
theorem hashPrecompileSelectors_subset_precompiles :
    ∀ id ∈ hashPrecompileSelectors, id ∈ acceleratorPrecompileSelectors := by
  rw [hashPrecompileSelectors, acceleratorPrecompileSelectors_eq]
  decide


-- @@ L527-530 verbatim
theorem hashPrecompileSelectors_are_accelerators :
    ∀ id ∈ hashPrecompileSelectors, isAccelerator id := by
  rw [hashPrecompileSelectors]
  decide


-- @@ L532-535 verbatim
theorem hashPrecompileSelectors_nodup :
    hashPrecompileSelectors.Nodup := by
  rw [hashPrecompileSelectors]
  decide


-- @@ L537-539 verbatim
/-- Accelerator selectors covered by the secp256k1 slice. -/
def secp256k1AcceleratorSelectors : List Nat :=
  [secp256k1_verify, secp256k1_ecrecover]


-- @@ L541-544 verbatim
theorem secp256k1AcceleratorSelectors_are_accelerators :
    ∀ id ∈ secp256k1AcceleratorSelectors, isAccelerator id := by
  rw [secp256k1AcceleratorSelectors]
  decide


-- @@ L546-549 verbatim
theorem secp256k1AcceleratorSelectors_nodup :
    secp256k1AcceleratorSelectors.Nodup := by
  rw [secp256k1AcceleratorSelectors]
  decide


-- @@ L551-554 verbatim
theorem secp256k1_verify_mem_nonPrecompileSelectors :
    secp256k1_verify ∈ acceleratorNonPrecompileSelectors := by
  rw [acceleratorNonPrecompileSelectors_eq]
  decide


-- @@ L556-559 verbatim
theorem secp256k1_ecrecover_mem_precompileSelectors :
    secp256k1_ecrecover ∈ acceleratorPrecompileSelectors := by
  rw [acceleratorPrecompileSelectors_eq]
  decide


-- @@ L561-574 verbatim
/-- Accelerator selectors covered by the curve/pairing/KZG/MODEXP slice. -/
def curvePrecompileSelectors : List Nat :=
  [modexp,
   bn254_g1_add,
   bn254_g1_mul,
   bn254_pairing,
   kzg_point_eval,
   bls12_g1_add,
   bls12_g1_msm,
   bls12_g2_add,
   bls12_g2_msm,
   bls12_pairing,
   bls12_map_fp_to_g1,
   bls12_map_fp2_to_g2]


-- @@ L576-579 verbatim
theorem curvePrecompileSelectors_subset_precompiles :
    ∀ id ∈ curvePrecompileSelectors, id ∈ acceleratorPrecompileSelectors := by
  rw [curvePrecompileSelectors, acceleratorPrecompileSelectors_eq]
  decide


-- @@ L581-584 verbatim
theorem curvePrecompileSelectors_are_accelerators :
    ∀ id ∈ curvePrecompileSelectors, isAccelerator id := by
  rw [curvePrecompileSelectors]
  decide


-- @@ L586-589 verbatim
theorem curvePrecompileSelectors_nodup :
    curvePrecompileSelectors.Nodup := by
  rw [curvePrecompileSelectors]
  decide


-- @@ L591-593 verbatim
def acceleratorClassifiedSelectors : List Nat :=
  acceleratorOpcodeSelectors ++ acceleratorNonPrecompileSelectors ++
    acceleratorPrecompileSelectors


-- @@ L595-600 verbatim
theorem acceleratorClassifiedSelectors_eq_coverage :
    acceleratorClassifiedSelectors = acceleratorCoverageSelectors := by
  rw [acceleratorClassifiedSelectors, acceleratorOpcodeSelectors_eq,
    acceleratorNonPrecompileSelectors_eq, acceleratorPrecompileSelectors_eq,
    acceleratorCoverageSelectors_eq]
  decide


-- @@ L602-604 verbatim
def acceleratorClassifiedSelectorCount : Nat :=
  acceleratorOpcodeSelectors.length + acceleratorNonPrecompileSelectors.length +
    acceleratorPrecompileSelectors.length


-- @@ L606-610 verbatim
theorem acceleratorClassifiedSelectorCount_eq :
    acceleratorClassifiedSelectorCount = 19 := by
  rw [acceleratorClassifiedSelectorCount, acceleratorOpcodeSelectors_eq,
    acceleratorNonPrecompileSelectors_eq, acceleratorPrecompileSelectors_length]
  decide


-- @@ L612-615 verbatim
theorem acceleratorClassifiedSelectors_nodup :
    acceleratorClassifiedSelectors.Nodup := by
  rw [acceleratorClassifiedSelectors_eq_coverage]
  exact acceleratorCoverageSelectors_nodup


-- @@ L617-620 verbatim
theorem acceleratorClassifiedSelectors_are_accelerators :
    ∀ id ∈ acceleratorClassifiedSelectors, isAccelerator id := by
  rw [acceleratorClassifiedSelectors_eq_coverage]
  exact acceleratorCoverageSelectors_are_accelerators


-- @@ L622-622 verbatim
end Accelerators

-- @@ L623-623 verbatim
end EvmAsm
