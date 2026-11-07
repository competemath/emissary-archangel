/-
  EvmAsm.EL.LogDataBridge

  Bridge from LOG stack arguments to event data bytes (GH #112).
-/

module

public import EvmAsm.EL.LogArgsBridge


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
namespace EvmAsm.EL


-- @@ L15-15 verbatim
namespace LogDataBridge


-- @@ L17-17 verbatim
abbrev LogArgs := EvmAsm.Evm64.LogArgs.Args

-- @@ L18-18 verbatim
abbrev MemoryReader := Nat → Byte


-- @@ L20-22 verbatim
/-- First memory byte consumed as LOG event data. -/
def dataStart (args : LogArgs) : Nat :=
  args.data.offset.toNat


-- @@ L24-26 verbatim
/-- Number of memory bytes consumed as LOG event data. -/
def dataSize (args : LogArgs) : Nat :=
  args.data.size.toNat


-- @@ L28-30 verbatim
/-- LOG event data bytes loaded from a pure memory-reader function. -/
def logDataFromMemory (readByte : MemoryReader) (args : LogArgs) : List Byte :=
  (List.range (dataSize args)).map (fun i => readByte (dataStart args + i))


-- @@ L32-36 verbatim
/-- Build a LOG entry directly from stack args and a pure memory reader.
    Distinctive token: LogDataBridge.mkLogEntryFromMemory #112. -/
def mkLogEntryFromMemory (emitter : Address) (readByte : MemoryReader) (args : LogArgs) :
    LogEntry :=
  LogArgsBridge.mkLogEntry emitter (logDataFromMemory readByte args) args


-- @@ L38-39 verbatim
theorem dataStart_eq (args : LogArgs) :
    dataStart args = args.data.offset.toNat := rfl


-- @@ L41-42 verbatim
theorem dataSize_eq (args : LogArgs) :
    dataSize args = args.data.size.toNat := rfl


-- @@ L44-46 verbatim
@[simp] theorem logDataFromMemory_length (readByte : MemoryReader) (args : LogArgs) :
    (logDataFromMemory readByte args).length = dataSize args := by
  simp [logDataFromMemory]


-- @@ L48-54 verbatim
theorem logDataFromMemory_get
    {readByte : MemoryReader} {args : LogArgs} {i : Nat}
    (h : i < dataSize args) :
    (logDataFromMemory readByte args)[i]'(by
      simpa [logDataFromMemory_length] using h) =
      readByte (dataStart args + i) := by
  simp [logDataFromMemory, List.getElem_map, List.getElem_range]


-- @@ L56-61 verbatim
theorem logDataFromMemory_get?
    (readByte : MemoryReader) (args : LogArgs) (i : Nat)
    (h : i < dataSize args) :
    (logDataFromMemory readByte args)[i]? =
      some (readByte (dataStart args + i)) := by
  simp [logDataFromMemory, h]


-- @@ L63-68 verbatim
@[simp] theorem logDataFromMemory_zero_size
    (readByte : MemoryReader) (rangeOffset : EvmAsm.Evm64.EvmWord)
    (topics : List EvmAsm.Evm64.EvmWord) :
    logDataFromMemory readByte
        { data := { offset := rangeOffset, size := 0 }, topics := topics } =
      [] := rfl


-- @@ L70-73 verbatim
theorem mkLogEntryFromMemory_eq
    (emitter : Address) (readByte : MemoryReader) (args : LogArgs) :
    mkLogEntryFromMemory emitter readByte args =
      LogArgsBridge.mkLogEntry emitter (logDataFromMemory readByte args) args := rfl


-- @@ L75-77 verbatim
theorem mkLogEntryFromMemoryEmitter
    (emitter : Address) (readByte : MemoryReader) (args : LogArgs) :
    (mkLogEntryFromMemory emitter readByte args).emitter = emitter := rfl


-- @@ L79-82 verbatim
theorem mkLogEntryFromMemoryData
    (emitter : Address) (readByte : MemoryReader) (args : LogArgs) :
    (mkLogEntryFromMemory emitter readByte args).data =
      logDataFromMemory readByte args := rfl


-- @@ L84-87 verbatim
theorem mkLogEntryFromMemoryTopics
    (emitter : Address) (readByte : MemoryReader) (args : LogArgs) :
    (mkLogEntryFromMemory emitter readByte args).topics =
      LogArgsBridge.topics args := rfl


-- @@ L89-95 verbatim
theorem mkLogEntryFromMemoryTopicCountOk
    (kind : LogArgsBridge.LogKind) (emitter : Address) (readByte : MemoryReader)
    (args : LogArgs)
    (h_topics : EvmAsm.Evm64.LogArgs.topicCountOk kind args) :
    (mkLogEntryFromMemory emitter readByte args).topicCountOk := by
  exact LogArgsBridge.topicCountOk_of_logArgs
    kind emitter (logDataFromMemory readByte args) args h_topics


-- @@ L97-102 verbatim
/-- Append a LOG entry directly from stack args and a pure memory reader.
    Distinctive token: LogDataBridge.appendLogFromMemory #112. -/
def appendLogFromMemory
    (logs : LogState) (emitter : Address) (readByte : MemoryReader) (args : LogArgs) :
    LogState :=
  LogArgsBridge.appendLogFromArgs logs emitter (logDataFromMemory readByte args) args


-- @@ L104-107 verbatim
theorem appendLogFromMemory_entries
    (logs : LogState) (emitter : Address) (readByte : MemoryReader) (args : LogArgs) :
    (appendLogFromMemory logs emitter readByte args).entries =
      logs.entries ++ [mkLogEntryFromMemory emitter readByte args] := rfl


-- @@ L109-113 verbatim
theorem appendLogFromMemory_length
    (logs : LogState) (emitter : Address) (readByte : MemoryReader) (args : LogArgs) :
    (appendLogFromMemory logs emitter readByte args).entries.length =
      logs.entries.length + 1 := by
  simp [appendLogFromMemory, LogArgsBridge.appendLogFromArgs]


-- @@ L115-121 verbatim
theorem appendLogFromMemory_lastData
    (logs : LogState) (emitter : Address) (readByte : MemoryReader) (args : LogArgs) :
    ((appendLogFromMemory logs emitter readByte args).entries.getLast
        (by simp [appendLogFromMemory, LogArgsBridge.appendLogFromArgs])).data =
      logDataFromMemory readByte args := by
  simp [appendLogFromMemory, LogArgsBridge.appendLogFromArgs,
    LogArgsBridge.mkLogEntry, LogEntry.mkChecked]


-- @@ L123-130 verbatim
theorem appendLogFromMemory_lastTopicCountOk
    (logs : LogState) (kind : LogArgsBridge.LogKind) (emitter : Address)
    (readByte : MemoryReader) (args : LogArgs)
    (h_topics : EvmAsm.Evm64.LogArgs.topicCountOk kind args) :
    ((appendLogFromMemory logs emitter readByte args).entries.getLast
        (by simp [appendLogFromMemory, LogArgsBridge.appendLogFromArgs])).topicCountOk := by
  simpa [appendLogFromMemory, LogArgsBridge.appendLogFromArgs, mkLogEntryFromMemory]
    using mkLogEntryFromMemoryTopicCountOk kind emitter readByte args h_topics


-- @@ L132-132 verbatim
end LogDataBridge


-- @@ L134-134 verbatim
end EvmAsm.EL
