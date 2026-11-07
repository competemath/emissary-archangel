/-
  EvmAsm.EL.LogCallEffects

  Bridge from LOG entries to message-call side effects (GH #112 / #121).
-/

module

public import EvmAsm.EL.LogArgsBridge
public import EvmAsm.EL.MessageCallExecution


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace EvmAsm.EL


-- @@ L16-16 verbatim
namespace LogCallEffects


-- @@ L18-18 verbatim
abbrev CallSideEffects := MessageCallExecution.CallSideEffects

-- @@ L19-19 verbatim
abbrev LogArgs := LogArgsBridge.LogArgs

-- @@ L20-20 verbatim
abbrev LogKind := LogArgsBridge.LogKind


-- @@ L22-30 verbatim
/-- Append a LOG entry into the message-call side-effect bundle, preserving
    every non-log side-effect field. Distinctive token: appendLogSideEffect. -/
def appendLogSideEffect
    (effects : CallSideEffects) (emitter : Address) (data : List Byte) (args : LogArgs) :
    CallSideEffects :=
  { refundCounter := effects.refundCounter
    logs := LogArgsBridge.appendLogFromArgs effects.logs emitter data args
    accountsToDelete := effects.accountsToDelete
    touchedAccounts := effects.touchedAccounts }


-- @@ L32-35 verbatim
@[simp] theorem appendLogSideEffect_refundCounter
    (effects : CallSideEffects) (emitter : Address) (data : List Byte) (args : LogArgs) :
    (appendLogSideEffect effects emitter data args).refundCounter =
      effects.refundCounter := rfl


-- @@ L37-40 verbatim
@[simp] theorem appendLogSideEffect_accountsToDelete
    (effects : CallSideEffects) (emitter : Address) (data : List Byte) (args : LogArgs) :
    (appendLogSideEffect effects emitter data args).accountsToDelete =
      effects.accountsToDelete := rfl


-- @@ L42-45 verbatim
@[simp] theorem appendLogSideEffect_touchedAccounts
    (effects : CallSideEffects) (emitter : Address) (data : List Byte) (args : LogArgs) :
    (appendLogSideEffect effects emitter data args).touchedAccounts =
      effects.touchedAccounts := rfl


-- @@ L47-50 verbatim
@[simp] theorem appendLogSideEffect_logs
    (effects : CallSideEffects) (emitter : Address) (data : List Byte) (args : LogArgs) :
    (appendLogSideEffect effects emitter data args).logs =
      LogArgsBridge.appendLogFromArgs effects.logs emitter data args := rfl


-- @@ L52-55 verbatim
theorem appendLogSideEffect_log_entries
    (effects : CallSideEffects) (emitter : Address) (data : List Byte) (args : LogArgs) :
    (appendLogSideEffect effects emitter data args).logs.entries =
      effects.logs.entries ++ [LogArgsBridge.mkLogEntry emitter data args] := rfl


-- @@ L57-61 verbatim
theorem appendLogSideEffect_log_length
    (effects : CallSideEffects) (emitter : Address) (data : List Byte) (args : LogArgs) :
    (appendLogSideEffect effects emitter data args).logs.entries.length =
      effects.logs.entries.length + 1 := by
  simp [appendLogSideEffect, LogArgsBridge.appendLogFromArgs]


-- @@ L63-70 verbatim
theorem appendLogSideEffect_last_topicCountOk
    (effects : CallSideEffects) (kind : LogKind) (emitter : Address) (data : List Byte)
    (args : LogArgs) (h_topics : EvmAsm.Evm64.LogArgs.topicCountOk kind args) :
    ((appendLogSideEffect effects emitter data args).logs.entries.getLast
        (by simp [appendLogSideEffect, LogArgsBridge.appendLogFromArgs,
          LogState.appendLog])).topicCountOk := by
  simpa [appendLogSideEffect] using
    LogArgsBridge.topicCountOk_appended effects.logs kind emitter data args h_topics


-- @@ L72-72 verbatim
end LogCallEffects


-- @@ L74-74 verbatim
end EvmAsm.EL
