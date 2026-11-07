/-
  EvmAsm.Evm64.LogGas

  Pure dynamic gas helpers for LOG0 through LOG4 (GH #112 / #118).
-/

module

public import EvmAsm.Evm64.LogArgs
public import EvmAsm.Evm64.MemoryGas


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace EvmAsm.Evm64

-- @@ L15-15 verbatim
namespace LogGas


-- @@ L17-18 verbatim
/-- Dynamic gas charged per LOG topic. -/
def logGasPerTopic : Nat := 375


-- @@ L20-21 verbatim
/-- Dynamic gas charged per byte of LOG data. -/
def logGasPerDataByte : Nat := 8


-- @@ L23-25 verbatim
/-- Topic-dependent dynamic gas for LOG0 through LOG4. -/
def logTopicDynamicCost (kind : LogArgs.Kind) : Nat :=
  logGasPerTopic * LogArgs.topicCount kind


-- @@ L27-29 verbatim
/-- Data-byte dynamic gas for LOG input data. -/
def logDataDynamicCost (length : Nat) : Nat :=
  logGasPerDataByte * length


-- @@ L31-39 verbatim
/--
  LOG dynamic gas: topic charge, data-byte charge, and memory expansion for
  the logged byte range. The opcode base cost is tracked separately by the
  static gas table.
-/
def logDynamicCost
    (kind : LogArgs.Kind) (sizeBytes offset length : Nat) : Nat :=
  logTopicDynamicCost kind + logDataDynamicCost length +
    MemoryGas.memoryAccessExpansionCost sizeBytes offset length


-- @@ L41-42 verbatim
@[simp] theorem logTopicDynamicCost_log0 :
    logTopicDynamicCost .log0 = 0 := rfl


-- @@ L44-46 verbatim
@[simp] theorem logDataDynamicCost_zero :
    logDataDynamicCost 0 = 0 := by
  simp [logDataDynamicCost, logGasPerDataByte]


-- @@ L48-54 verbatim
theorem logDynamicCost_eq_charges_of_no_growth
    {kind : LogArgs.Kind} {sizeBytes offset length : Nat}
    (h_no_growth : evmMemExpand sizeBytes offset length = sizeBytes) :
    logDynamicCost kind sizeBytes offset length =
      logTopicDynamicCost kind + logDataDynamicCost length := by
  simp [logDynamicCost,
    MemoryGas.memoryAccessExpansionCost_eq_zero_of_no_growth h_no_growth]


-- @@ L56-62 verbatim
theorem logDynamicCost_eq_charges_of_access_le
    {kind : LogArgs.Kind} {sizeBytes offset length : Nat}
    (h_access : roundUpTo32 (offset + length) ≤ sizeBytes) :
    logDynamicCost kind sizeBytes offset length =
      logTopicDynamicCost kind + logDataDynamicCost length := by
  exact logDynamicCost_eq_charges_of_no_growth
    (evmMemExpand_eq_old_of_access_le sizeBytes offset length h_access)


-- @@ L64-66 verbatim
@[simp] theorem logDynamicCost_log0_zero_length (sizeBytes offset : Nat) :
    logDynamicCost .log0 sizeBytes offset 0 = 0 := by
  simp [logDynamicCost]


-- @@ L68-68 verbatim
end LogGas

-- @@ L69-69 verbatim
end EvmAsm.Evm64
