/-
  EvmAsm.Evm64.Env.Wrappers

  Per-opcode wrappers for the 13 simple environment opcodes (slice 6 of
  GH #103, beads `evm-asm-bqc2`). Each wrapper is a thin abbreviation
  over `evm_env_load envBaseReg tmpReg <field>` together with a per-opcode
  `_stack_spec_within` theorem that follows from the parameterized
  `evm_env_load_stack_spec_within` (see `EvmAsm.Evm64.Env.StackSpec`) by
  instantiating the `SimpleEnvField` argument.

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
-/

module

public import EvmAsm.Evm64.Env.StackSpec


-- @@ L18-18 verbatim
public section


-- @@ L20-20 verbatim
namespace EvmAsm.Evm64

-- @@ L21-21 verbatim
namespace Env


-- @@ L23-23 verbatim
open EvmAsm.Rv64

-- @@ L24-24 verbatim
open SimpleEnvField


-- @@ L26-26 verbatim
/-! ## Per-opcode program wrappers -/


-- @@ L28-30 verbatim
/-- `ADDRESS` opcode (0x30): push `addrAsWord env.address`. -/
abbrev evm_address (envBaseReg tmpReg : Reg) : Program :=
  evm_env_load envBaseReg tmpReg .address


-- @@ L32-34 verbatim
/-- `CALLER` opcode (0x33): push `addrAsWord env.caller`. -/
abbrev evm_caller (envBaseReg tmpReg : Reg) : Program :=
  evm_env_load envBaseReg tmpReg .caller


-- @@ L36-38 verbatim
/-- `CALLVALUE` opcode (0x34): push `env.callValue`. -/
abbrev evm_callvalue (envBaseReg tmpReg : Reg) : Program :=
  evm_env_load envBaseReg tmpReg .callValue


-- @@ L40-42 verbatim
/-- `ORIGIN` opcode (0x32): push `addrAsWord env.txOrigin`. -/
abbrev evm_origin (envBaseReg tmpReg : Reg) : Program :=
  evm_env_load envBaseReg tmpReg .origin


-- @@ L44-46 verbatim
/-- `GASPRICE` opcode (0x3a): push `env.gasPrice`. -/
abbrev evm_gasprice (envBaseReg tmpReg : Reg) : Program :=
  evm_env_load envBaseReg tmpReg .gasPrice


-- @@ L48-50 verbatim
/-- `COINBASE` opcode (0x41): push `addrAsWord env.blockCoinbase`. -/
abbrev evm_coinbase (envBaseReg tmpReg : Reg) : Program :=
  evm_env_load envBaseReg tmpReg .coinbase


-- @@ L52-54 verbatim
/-- `TIMESTAMP` opcode (0x42): push `env.blockTimestamp`. -/
abbrev evm_timestamp (envBaseReg tmpReg : Reg) : Program :=
  evm_env_load envBaseReg tmpReg .timestamp


-- @@ L56-58 verbatim
/-- `NUMBER` opcode (0x43): push `env.blockNumber`. -/
abbrev evm_number (envBaseReg tmpReg : Reg) : Program :=
  evm_env_load envBaseReg tmpReg .number


-- @@ L60-62 verbatim
/-- `PREVRANDAO` opcode (0x44): push `env.blockPrevrandao`. -/
abbrev evm_prevrandao (envBaseReg tmpReg : Reg) : Program :=
  evm_env_load envBaseReg tmpReg .prevrandao


-- @@ L64-66 verbatim
/-- `GASLIMIT` opcode (0x45): push `env.blockGasLimit`. -/
abbrev evm_gaslimit (envBaseReg tmpReg : Reg) : Program :=
  evm_env_load envBaseReg tmpReg .gasLimit


-- @@ L68-70 verbatim
/-- `CHAINID` opcode (0x46): push `env.chainId`. -/
abbrev evm_chainid (envBaseReg tmpReg : Reg) : Program :=
  evm_env_load envBaseReg tmpReg .chainId


-- @@ L72-74 verbatim
/-- `BASEFEE` opcode (0x48): push `env.blockBaseFee`. -/
abbrev evm_basefee (envBaseReg tmpReg : Reg) : Program :=
  evm_env_load envBaseReg tmpReg .baseFee


-- @@ L76-78 verbatim
/-- `SELFBALANCE` opcode (0x47): push `env.selfBalance`. -/
abbrev evm_selfbalance (envBaseReg tmpReg : Reg) : Program :=
  evm_env_load envBaseReg tmpReg .selfBalance


-- @@ L80-87 verbatim
/-! ## Per-opcode stack specs

  Each wrapper spec is the parameterized
  `evm_env_load_stack_spec_within` instantiated at the corresponding
  `SimpleEnvField`, with the `field.value env` post-state simplified
  via the per-field `value_*` rfl lemma in
  `EvmAsm.Evm64.Env.Field`.
-/


-- @@ L89-107 verbatim
theorem evm_address_stack_spec_within
    (envBaseReg tmpReg : Reg) (htmp_ne_x0 : tmpReg ≠ .x0)
    (nsp base envAddr tempOld : Word) (env : EvmEnv)
    (d0 d1 d2 d3 : Word) (rest : List EvmWord) :
    let code := evm_env_load_code envBaseReg tmpReg .address base
    cpsTripleWithin 9 base (base + 36) code
      ((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ tempOld) **
       (.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) **
       ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3) **
       EvmEnv.envIs envAddr env **
       evmStackIs (nsp + 32) rest)
      ((envBaseReg ↦ᵣ envAddr) **
       (tmpReg ↦ᵣ (EvmEnv.addrAsWord env.address).getLimbN 3) **
       (.x12 ↦ᵣ nsp) **
       evmStackIs nsp (EvmEnv.addrAsWord env.address :: rest) **
       EvmEnv.envIs envAddr env) :=
  evm_env_load_stack_spec_within envBaseReg tmpReg htmp_ne_x0
    nsp base envAddr tempOld .address env d0 d1 d2 d3 rest


-- @@ L109-127 verbatim
theorem evm_caller_stack_spec_within
    (envBaseReg tmpReg : Reg) (htmp_ne_x0 : tmpReg ≠ .x0)
    (nsp base envAddr tempOld : Word) (env : EvmEnv)
    (d0 d1 d2 d3 : Word) (rest : List EvmWord) :
    let code := evm_env_load_code envBaseReg tmpReg .caller base
    cpsTripleWithin 9 base (base + 36) code
      ((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ tempOld) **
       (.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) **
       ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3) **
       EvmEnv.envIs envAddr env **
       evmStackIs (nsp + 32) rest)
      ((envBaseReg ↦ᵣ envAddr) **
       (tmpReg ↦ᵣ (EvmEnv.addrAsWord env.caller).getLimbN 3) **
       (.x12 ↦ᵣ nsp) **
       evmStackIs nsp (EvmEnv.addrAsWord env.caller :: rest) **
       EvmEnv.envIs envAddr env) :=
  evm_env_load_stack_spec_within envBaseReg tmpReg htmp_ne_x0
    nsp base envAddr tempOld .caller env d0 d1 d2 d3 rest


-- @@ L129-147 verbatim
theorem evm_callvalue_stack_spec_within
    (envBaseReg tmpReg : Reg) (htmp_ne_x0 : tmpReg ≠ .x0)
    (nsp base envAddr tempOld : Word) (env : EvmEnv)
    (d0 d1 d2 d3 : Word) (rest : List EvmWord) :
    let code := evm_env_load_code envBaseReg tmpReg .callValue base
    cpsTripleWithin 9 base (base + 36) code
      ((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ tempOld) **
       (.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) **
       ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3) **
       EvmEnv.envIs envAddr env **
       evmStackIs (nsp + 32) rest)
      ((envBaseReg ↦ᵣ envAddr) **
       (tmpReg ↦ᵣ env.callValue.getLimbN 3) **
       (.x12 ↦ᵣ nsp) **
       evmStackIs nsp (env.callValue :: rest) **
       EvmEnv.envIs envAddr env) :=
  evm_env_load_stack_spec_within envBaseReg tmpReg htmp_ne_x0
    nsp base envAddr tempOld .callValue env d0 d1 d2 d3 rest


-- @@ L149-167 verbatim
theorem evm_origin_stack_spec_within
    (envBaseReg tmpReg : Reg) (htmp_ne_x0 : tmpReg ≠ .x0)
    (nsp base envAddr tempOld : Word) (env : EvmEnv)
    (d0 d1 d2 d3 : Word) (rest : List EvmWord) :
    let code := evm_env_load_code envBaseReg tmpReg .origin base
    cpsTripleWithin 9 base (base + 36) code
      ((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ tempOld) **
       (.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) **
       ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3) **
       EvmEnv.envIs envAddr env **
       evmStackIs (nsp + 32) rest)
      ((envBaseReg ↦ᵣ envAddr) **
       (tmpReg ↦ᵣ (EvmEnv.addrAsWord env.txOrigin).getLimbN 3) **
       (.x12 ↦ᵣ nsp) **
       evmStackIs nsp (EvmEnv.addrAsWord env.txOrigin :: rest) **
       EvmEnv.envIs envAddr env) :=
  evm_env_load_stack_spec_within envBaseReg tmpReg htmp_ne_x0
    nsp base envAddr tempOld .origin env d0 d1 d2 d3 rest


-- @@ L169-187 verbatim
theorem evm_gasprice_stack_spec_within
    (envBaseReg tmpReg : Reg) (htmp_ne_x0 : tmpReg ≠ .x0)
    (nsp base envAddr tempOld : Word) (env : EvmEnv)
    (d0 d1 d2 d3 : Word) (rest : List EvmWord) :
    let code := evm_env_load_code envBaseReg tmpReg .gasPrice base
    cpsTripleWithin 9 base (base + 36) code
      ((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ tempOld) **
       (.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) **
       ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3) **
       EvmEnv.envIs envAddr env **
       evmStackIs (nsp + 32) rest)
      ((envBaseReg ↦ᵣ envAddr) **
       (tmpReg ↦ᵣ env.gasPrice.getLimbN 3) **
       (.x12 ↦ᵣ nsp) **
       evmStackIs nsp (env.gasPrice :: rest) **
       EvmEnv.envIs envAddr env) :=
  evm_env_load_stack_spec_within envBaseReg tmpReg htmp_ne_x0
    nsp base envAddr tempOld .gasPrice env d0 d1 d2 d3 rest


-- @@ L189-207 verbatim
theorem evm_coinbase_stack_spec_within
    (envBaseReg tmpReg : Reg) (htmp_ne_x0 : tmpReg ≠ .x0)
    (nsp base envAddr tempOld : Word) (env : EvmEnv)
    (d0 d1 d2 d3 : Word) (rest : List EvmWord) :
    let code := evm_env_load_code envBaseReg tmpReg .coinbase base
    cpsTripleWithin 9 base (base + 36) code
      ((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ tempOld) **
       (.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) **
       ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3) **
       EvmEnv.envIs envAddr env **
       evmStackIs (nsp + 32) rest)
      ((envBaseReg ↦ᵣ envAddr) **
       (tmpReg ↦ᵣ (EvmEnv.addrAsWord env.blockCoinbase).getLimbN 3) **
       (.x12 ↦ᵣ nsp) **
       evmStackIs nsp (EvmEnv.addrAsWord env.blockCoinbase :: rest) **
       EvmEnv.envIs envAddr env) :=
  evm_env_load_stack_spec_within envBaseReg tmpReg htmp_ne_x0
    nsp base envAddr tempOld .coinbase env d0 d1 d2 d3 rest


-- @@ L209-227 verbatim
theorem evm_timestamp_stack_spec_within
    (envBaseReg tmpReg : Reg) (htmp_ne_x0 : tmpReg ≠ .x0)
    (nsp base envAddr tempOld : Word) (env : EvmEnv)
    (d0 d1 d2 d3 : Word) (rest : List EvmWord) :
    let code := evm_env_load_code envBaseReg tmpReg .timestamp base
    cpsTripleWithin 9 base (base + 36) code
      ((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ tempOld) **
       (.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) **
       ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3) **
       EvmEnv.envIs envAddr env **
       evmStackIs (nsp + 32) rest)
      ((envBaseReg ↦ᵣ envAddr) **
       (tmpReg ↦ᵣ env.blockTimestamp.getLimbN 3) **
       (.x12 ↦ᵣ nsp) **
       evmStackIs nsp (env.blockTimestamp :: rest) **
       EvmEnv.envIs envAddr env) :=
  evm_env_load_stack_spec_within envBaseReg tmpReg htmp_ne_x0
    nsp base envAddr tempOld .timestamp env d0 d1 d2 d3 rest


-- @@ L229-247 verbatim
theorem evm_number_stack_spec_within
    (envBaseReg tmpReg : Reg) (htmp_ne_x0 : tmpReg ≠ .x0)
    (nsp base envAddr tempOld : Word) (env : EvmEnv)
    (d0 d1 d2 d3 : Word) (rest : List EvmWord) :
    let code := evm_env_load_code envBaseReg tmpReg .number base
    cpsTripleWithin 9 base (base + 36) code
      ((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ tempOld) **
       (.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) **
       ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3) **
       EvmEnv.envIs envAddr env **
       evmStackIs (nsp + 32) rest)
      ((envBaseReg ↦ᵣ envAddr) **
       (tmpReg ↦ᵣ env.blockNumber.getLimbN 3) **
       (.x12 ↦ᵣ nsp) **
       evmStackIs nsp (env.blockNumber :: rest) **
       EvmEnv.envIs envAddr env) :=
  evm_env_load_stack_spec_within envBaseReg tmpReg htmp_ne_x0
    nsp base envAddr tempOld .number env d0 d1 d2 d3 rest


-- @@ L249-267 verbatim
theorem evm_prevrandao_stack_spec_within
    (envBaseReg tmpReg : Reg) (htmp_ne_x0 : tmpReg ≠ .x0)
    (nsp base envAddr tempOld : Word) (env : EvmEnv)
    (d0 d1 d2 d3 : Word) (rest : List EvmWord) :
    let code := evm_env_load_code envBaseReg tmpReg .prevrandao base
    cpsTripleWithin 9 base (base + 36) code
      ((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ tempOld) **
       (.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) **
       ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3) **
       EvmEnv.envIs envAddr env **
       evmStackIs (nsp + 32) rest)
      ((envBaseReg ↦ᵣ envAddr) **
       (tmpReg ↦ᵣ env.blockPrevrandao.getLimbN 3) **
       (.x12 ↦ᵣ nsp) **
       evmStackIs nsp (env.blockPrevrandao :: rest) **
       EvmEnv.envIs envAddr env) :=
  evm_env_load_stack_spec_within envBaseReg tmpReg htmp_ne_x0
    nsp base envAddr tempOld .prevrandao env d0 d1 d2 d3 rest


-- @@ L269-287 verbatim
theorem evm_gaslimit_stack_spec_within
    (envBaseReg tmpReg : Reg) (htmp_ne_x0 : tmpReg ≠ .x0)
    (nsp base envAddr tempOld : Word) (env : EvmEnv)
    (d0 d1 d2 d3 : Word) (rest : List EvmWord) :
    let code := evm_env_load_code envBaseReg tmpReg .gasLimit base
    cpsTripleWithin 9 base (base + 36) code
      ((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ tempOld) **
       (.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) **
       ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3) **
       EvmEnv.envIs envAddr env **
       evmStackIs (nsp + 32) rest)
      ((envBaseReg ↦ᵣ envAddr) **
       (tmpReg ↦ᵣ env.blockGasLimit.getLimbN 3) **
       (.x12 ↦ᵣ nsp) **
       evmStackIs nsp (env.blockGasLimit :: rest) **
       EvmEnv.envIs envAddr env) :=
  evm_env_load_stack_spec_within envBaseReg tmpReg htmp_ne_x0
    nsp base envAddr tempOld .gasLimit env d0 d1 d2 d3 rest


-- @@ L289-307 verbatim
theorem evm_chainid_stack_spec_within
    (envBaseReg tmpReg : Reg) (htmp_ne_x0 : tmpReg ≠ .x0)
    (nsp base envAddr tempOld : Word) (env : EvmEnv)
    (d0 d1 d2 d3 : Word) (rest : List EvmWord) :
    let code := evm_env_load_code envBaseReg tmpReg .chainId base
    cpsTripleWithin 9 base (base + 36) code
      ((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ tempOld) **
       (.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) **
       ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3) **
       EvmEnv.envIs envAddr env **
       evmStackIs (nsp + 32) rest)
      ((envBaseReg ↦ᵣ envAddr) **
       (tmpReg ↦ᵣ env.chainId.getLimbN 3) **
       (.x12 ↦ᵣ nsp) **
       evmStackIs nsp (env.chainId :: rest) **
       EvmEnv.envIs envAddr env) :=
  evm_env_load_stack_spec_within envBaseReg tmpReg htmp_ne_x0
    nsp base envAddr tempOld .chainId env d0 d1 d2 d3 rest


-- @@ L309-327 verbatim
theorem evm_basefee_stack_spec_within
    (envBaseReg tmpReg : Reg) (htmp_ne_x0 : tmpReg ≠ .x0)
    (nsp base envAddr tempOld : Word) (env : EvmEnv)
    (d0 d1 d2 d3 : Word) (rest : List EvmWord) :
    let code := evm_env_load_code envBaseReg tmpReg .baseFee base
    cpsTripleWithin 9 base (base + 36) code
      ((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ tempOld) **
       (.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) **
       ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3) **
       EvmEnv.envIs envAddr env **
       evmStackIs (nsp + 32) rest)
      ((envBaseReg ↦ᵣ envAddr) **
       (tmpReg ↦ᵣ env.blockBaseFee.getLimbN 3) **
       (.x12 ↦ᵣ nsp) **
       evmStackIs nsp (env.blockBaseFee :: rest) **
       EvmEnv.envIs envAddr env) :=
  evm_env_load_stack_spec_within envBaseReg tmpReg htmp_ne_x0
    nsp base envAddr tempOld .baseFee env d0 d1 d2 d3 rest


-- @@ L329-347 verbatim
theorem evm_selfbalance_stack_spec_within
    (envBaseReg tmpReg : Reg) (htmp_ne_x0 : tmpReg ≠ .x0)
    (nsp base envAddr tempOld : Word) (env : EvmEnv)
    (d0 d1 d2 d3 : Word) (rest : List EvmWord) :
    let code := evm_env_load_code envBaseReg tmpReg .selfBalance base
    cpsTripleWithin 9 base (base + 36) code
      ((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ tempOld) **
       (.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) **
       ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3) **
       EvmEnv.envIs envAddr env **
       evmStackIs (nsp + 32) rest)
      ((envBaseReg ↦ᵣ envAddr) **
       (tmpReg ↦ᵣ env.selfBalance.getLimbN 3) **
       (.x12 ↦ᵣ nsp) **
       evmStackIs nsp (env.selfBalance :: rest) **
       EvmEnv.envIs envAddr env) :=
  evm_env_load_stack_spec_within envBaseReg tmpReg htmp_ne_x0
    nsp base envAddr tempOld .selfBalance env d0 d1 d2 d3 rest


-- @@ L349-349 verbatim
end Env

-- @@ L350-350 verbatim
end EvmAsm.Evm64
