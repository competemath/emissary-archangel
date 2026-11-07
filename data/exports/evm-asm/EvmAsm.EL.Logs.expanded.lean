/-
  EvmAsm.EL.Logs

  Pure LOG0-LOG4 event surface for GH #112.
-/

module

public import EvmAsm.EL.WorldState


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
namespace EvmAsm.EL


-- @@ L15-16 verbatim
/-- A LOG topic is a full 256-bit EVM word. -/
abbrev LogTopic := Word256


-- @@ L18-23 verbatim
/-- One EVM log entry emitted by LOG0 through LOG4. -/
structure LogEntry where
  emitter : Address
  topics : List LogTopic
  data : List Byte
  deriving Repr


-- @@ L25-25 verbatim
namespace LogEntry


-- @@ L27-29 verbatim
/-- Topic-count validity for LOG0 through LOG4. -/
def topicCountOk (entry : LogEntry) : Prop :=
  entry.topics.length ≤ 4


-- @@ L31-33 verbatim
/-- Construct a log entry when the caller already has the concrete topics/data. -/
def mkChecked (emitter : Address) (topics : List LogTopic) (data : List Byte) : LogEntry :=
  { emitter := emitter, topics := topics, data := data }


-- @@ L35-36 verbatim
theorem topicCountOk_iff (entry : LogEntry) :
    entry.topicCountOk ↔ entry.topics.length ≤ 4 := Iff.rfl


-- @@ L38-40 verbatim
theorem topicCountOk_nil (emitter : Address) (data : List Byte) :
    (mkChecked emitter [] data).topicCountOk := by
  simp [topicCountOk, mkChecked]


-- @@ L42-44 verbatim
theorem topicCountOk_single (emitter : Address) (topic : LogTopic) (data : List Byte) :
    (mkChecked emitter [topic] data).topicCountOk := by
  simp [topicCountOk, mkChecked]


-- @@ L46-49 verbatim
theorem topicCountOk_two
    (emitter : Address) (topic0 topic1 : LogTopic) (data : List Byte) :
    (mkChecked emitter [topic0, topic1] data).topicCountOk := by
  simp [topicCountOk, mkChecked]


-- @@ L51-54 verbatim
theorem topicCountOk_three
    (emitter : Address) (topic0 topic1 topic2 : LogTopic) (data : List Byte) :
    (mkChecked emitter [topic0, topic1, topic2] data).topicCountOk := by
  simp [topicCountOk, mkChecked]


-- @@ L56-59 verbatim
theorem topicCountOk_four
    (emitter : Address) (topic0 topic1 topic2 topic3 : LogTopic) (data : List Byte) :
    (mkChecked emitter [topic0, topic1, topic2, topic3] data).topicCountOk := by
  simp [topicCountOk, mkChecked]


-- @@ L61-61 verbatim
end LogEntry


-- @@ L63-66 verbatim
/-- Append-only sequence of EVM log entries accumulated during execution. -/
structure LogState where
  entries : List LogEntry
  deriving Repr


-- @@ L68-68 verbatim
namespace LogState


-- @@ L70-71 verbatim
def empty : LogState :=
  { entries := [] }


-- @@ L73-75 verbatim
/-- Append one log entry to the end of the execution log. -/
def appendLog (logs : LogState) (entry : LogEntry) : LogState :=
  { entries := logs.entries ++ [entry] }


-- @@ L77-77 verbatim
@[simp] theorem entries_empty : empty.entries = [] := rfl


-- @@ L79-80 verbatim
@[simp] theorem entries_appendLog (logs : LogState) (entry : LogEntry) :
    (appendLog logs entry).entries = logs.entries ++ [entry] := rfl


-- @@ L82-84 verbatim
theorem length_appendLog (logs : LogState) (entry : LogEntry) :
    (appendLog logs entry).entries.length = logs.entries.length + 1 := by
  simp [appendLog]


-- @@ L86-87 verbatim
theorem appendLog_empty_entries (entry : LogEntry) :
    (appendLog empty entry).entries = [entry] := rfl


-- @@ L89-92 verbatim
theorem appended_log_topicCountOk
    (logs : LogState) {entry : LogEntry} (h_topics : entry.topicCountOk) :
    (appendLog logs entry).entries.getLast (by simp [appendLog]) |>.topicCountOk := by
  simpa [appendLog] using h_topics


-- @@ L94-94 verbatim
end LogState


-- @@ L96-96 verbatim
end EvmAsm.EL
