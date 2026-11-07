/-
  EvmAsm.EL.LogExecutionBridge

  End-to-end pure bridge from LOG memory data to call side effects.
-/

module

public import EvmAsm.EL.LogCallEffects
public import EvmAsm.EL.LogDataBridge


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace EvmAsm.EL


-- @@ L16-16 verbatim
namespace LogExecutionBridge


-- @@ L18-18 verbatim
abbrev CallSideEffects := LogCallEffects.CallSideEffects

-- @@ L19-19 verbatim
abbrev LogArgs := LogDataBridge.LogArgs

-- @@ L20-20 verbatim
abbrev LogKind := LogArgsBridge.LogKind

-- @@ L21-21 verbatim
abbrev MemoryReader := LogDataBridge.MemoryReader


-- @@ L23-28 verbatim
/-- Distinctive token: LogExecutionBridge.appendLogFromMemory #112. -/
def appendLogFromMemory
    (effects : CallSideEffects) (emitter : Address)
    (readByte : MemoryReader) (args : LogArgs) : CallSideEffects :=
  LogCallEffects.appendLogSideEffect effects emitter
    (LogDataBridge.logDataFromMemory readByte args) args


-- @@ L30-34 verbatim
@[simp] theorem appendLogFromMemory_refundCounter
    (effects : CallSideEffects) (emitter : Address)
    (readByte : MemoryReader) (args : LogArgs) :
    (appendLogFromMemory effects emitter readByte args).refundCounter =
      effects.refundCounter := rfl


-- @@ L36-40 verbatim
@[simp] theorem appendLogFromMemory_accountsToDelete
    (effects : CallSideEffects) (emitter : Address)
    (readByte : MemoryReader) (args : LogArgs) :
    (appendLogFromMemory effects emitter readByte args).accountsToDelete =
      effects.accountsToDelete := rfl


-- @@ L42-46 verbatim
@[simp] theorem appendLogFromMemory_touchedAccounts
    (effects : CallSideEffects) (emitter : Address)
    (readByte : MemoryReader) (args : LogArgs) :
    (appendLogFromMemory effects emitter readByte args).touchedAccounts =
      effects.touchedAccounts := rfl


-- @@ L48-53 verbatim
@[simp] theorem appendLogFromMemory_logs
    (effects : CallSideEffects) (emitter : Address)
    (readByte : MemoryReader) (args : LogArgs) :
    (appendLogFromMemory effects emitter readByte args).logs =
      LogArgsBridge.appendLogFromArgs effects.logs emitter
        (LogDataBridge.logDataFromMemory readByte args) args := rfl


-- @@ L55-60 verbatim
theorem appendLogFromMemory_log_entries
    (effects : CallSideEffects) (emitter : Address)
    (readByte : MemoryReader) (args : LogArgs) :
    (appendLogFromMemory effects emitter readByte args).logs.entries =
      effects.logs.entries ++
        [LogDataBridge.mkLogEntryFromMemory emitter readByte args] := rfl


-- @@ L62-68 verbatim
theorem appendLogFromMemory_log_length
    (effects : CallSideEffects) (emitter : Address)
    (readByte : MemoryReader) (args : LogArgs) :
    (appendLogFromMemory effects emitter readByte args).logs.entries.length =
      effects.logs.entries.length + 1 := by
  simp [appendLogFromMemory, LogCallEffects.appendLogSideEffect,
    LogArgsBridge.appendLogFromArgs]


-- @@ L70-80 verbatim
theorem appendLogFromMemory_last_topicCountOk
    (effects : CallSideEffects) (kind : LogKind) (emitter : Address)
    (readByte : MemoryReader) (args : LogArgs)
    (h_topics : EvmAsm.Evm64.LogArgs.topicCountOk kind args) :
    ((appendLogFromMemory effects emitter readByte args).logs.entries.getLast
        (by simp [appendLogFromMemory, LogCallEffects.appendLogSideEffect,
          LogArgsBridge.appendLogFromArgs, LogState.appendLog])).topicCountOk := by
  simpa [appendLogFromMemory, LogCallEffects.appendLogSideEffect,
    LogDataBridge.mkLogEntryFromMemory_eq] using
    LogDataBridge.mkLogEntryFromMemoryTopicCountOk
      kind emitter readByte args h_topics


-- @@ L82-82 verbatim
end LogExecutionBridge


-- @@ L84-84 verbatim
end EvmAsm.EL
