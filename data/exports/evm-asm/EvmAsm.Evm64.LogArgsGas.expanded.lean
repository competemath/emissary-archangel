/-
  EvmAsm.Evm64.LogArgsGas

  Bridge from LOG stack arguments to dynamic gas helpers (GH #112).
-/

module

public import EvmAsm.Evm64.LogGas


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
namespace EvmAsm.Evm64

-- @@ L14-14 verbatim
namespace LogArgsGas


-- @@ L16-18 verbatim
/-- LOG data offset converted to host `Nat` for executable memory/gas helpers. -/
def dataOffsetNat (args : LogArgs.Args) : Nat :=
  args.data.offset.toNat


-- @@ L20-22 verbatim
/-- LOG data size converted to host `Nat` for executable memory/gas helpers. -/
def dataSizeNat (args : LogArgs.Args) : Nat :=
  args.data.size.toNat


-- @@ L24-28 verbatim
/-- LOG dynamic gas computed directly from decoded stack arguments.
    Distinctive token: LogArgsGas.logDynamicCostFromArgs. -/
def logDynamicCostFromArgs
    (kind : LogArgs.Kind) (sizeBytes : Nat) (args : LogArgs.Args) : Nat :=
  LogGas.logDynamicCost kind sizeBytes (dataOffsetNat args) (dataSizeNat args)


-- @@ L30-31 verbatim
theorem dataOffsetNat_eq (args : LogArgs.Args) :
    dataOffsetNat args = args.data.offset.toNat := rfl


-- @@ L33-34 verbatim
theorem dataSizeNat_eq (args : LogArgs.Args) :
    dataSizeNat args = args.data.size.toNat := rfl


-- @@ L36-39 verbatim
theorem logDynamicCostFromArgs_eq
    (kind : LogArgs.Kind) (sizeBytes : Nat) (args : LogArgs.Args) :
    logDynamicCostFromArgs kind sizeBytes args =
      LogGas.logDynamicCost kind sizeBytes args.data.offset.toNat args.data.size.toNat := rfl


-- @@ L41-45 verbatim
@[simp] theorem logDynamicCostFromArgs_log0_zero_size
    (sizeBytes : Nat) (offset : EvmWord) :
    logDynamicCostFromArgs .log0 sizeBytes
      { data := { offset := offset, size := 0 }, topics := [] } = 0 := by
  simp [logDynamicCostFromArgs, dataOffsetNat, dataSizeNat]


-- @@ L47-53 verbatim
theorem logDynamicCostFromArgs_eq_charges_of_no_growth
    {kind : LogArgs.Kind} {sizeBytes : Nat} {args : LogArgs.Args}
    (h_no_growth :
      evmMemExpand sizeBytes args.data.offset.toNat args.data.size.toNat = sizeBytes) :
    logDynamicCostFromArgs kind sizeBytes args =
      LogGas.logTopicDynamicCost kind + LogGas.logDataDynamicCost args.data.size.toNat := by
  exact LogGas.logDynamicCost_eq_charges_of_no_growth h_no_growth


-- @@ L55-61 verbatim
theorem logDynamicCostFromArgs_eq_charges_of_access_le
    {kind : LogArgs.Kind} {sizeBytes : Nat} {args : LogArgs.Args}
    (h_access :
      roundUpTo32 (args.data.offset.toNat + args.data.size.toNat) ≤ sizeBytes) :
    logDynamicCostFromArgs kind sizeBytes args =
      LogGas.logTopicDynamicCost kind + LogGas.logDataDynamicCost args.data.size.toNat := by
  exact LogGas.logDynamicCost_eq_charges_of_access_le h_access


-- @@ L63-71 verbatim
theorem logDynamicCostFromArgs_log0_eq_data_cost_of_no_growth
    {sizeBytes : Nat} {args : LogArgs.Args}
    (h_no_growth :
      evmMemExpand sizeBytes args.data.offset.toNat args.data.size.toNat = sizeBytes) :
    logDynamicCostFromArgs .log0 sizeBytes args =
      LogGas.logDataDynamicCost args.data.size.toNat := by
  simpa using
    logDynamicCostFromArgs_eq_charges_of_no_growth
      (kind := .log0) (sizeBytes := sizeBytes) (args := args) h_no_growth


-- @@ L73-73 verbatim
end LogArgsGas

-- @@ L74-74 verbatim
end EvmAsm.Evm64
