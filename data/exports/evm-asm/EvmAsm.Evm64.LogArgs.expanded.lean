/-
  EvmAsm.Evm64.LogArgs

  Pure stack-argument records for LOG0 through LOG4 (GH #112).
-/

module

public import EvmAsm.Evm64.EvmWord


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
namespace EvmAsm.Evm64


-- @@ L15-15 verbatim
namespace LogArgs


-- @@ L17-21 verbatim
/-- Memory slice described by an EVM offset and byte size. -/
structure MemoryRange where
  offset : EvmWord
  size : EvmWord
  deriving Repr


-- @@ L23-30 verbatim
/-- LOG opcode arity classifier. -/
inductive Kind where
  | log0
  | log1
  | log2
  | log3
  | log4
  deriving DecidableEq, Repr


-- @@ L32-36 verbatim
/-- Stack arguments shared by LOG0 through LOG4: a data range plus topics. -/
structure Args where
  data : MemoryRange
  topics : List EvmWord
  deriving Repr


-- @@ L38-43 verbatim
def topicCount : Kind → Nat
  | .log0 => 0
  | .log1 => 1
  | .log2 => 2
  | .log3 => 3
  | .log4 => 4


-- @@ L45-46 verbatim
def stackArgumentCount (kind : Kind) : Nat :=
  2 + topicCount kind


-- @@ L48-49 verbatim
def topicCountOk (kind : Kind) (args : Args) : Prop :=
  args.topics.length = topicCount kind


-- @@ L51-52 verbatim
def dataRange (args : Args) : MemoryRange :=
  args.data


-- @@ L54-54 verbatim
theorem topicCountLog0 : topicCount .log0 = 0 := rfl

-- @@ L55-55 verbatim
theorem topicCountLog1 : topicCount .log1 = 1 := rfl

-- @@ L56-56 verbatim
theorem topicCountLog2 : topicCount .log2 = 2 := rfl

-- @@ L57-57 verbatim
theorem topicCountLog3 : topicCount .log3 = 3 := rfl

-- @@ L58-58 verbatim
theorem topicCountLog4 : topicCount .log4 = 4 := rfl


-- @@ L60-60 verbatim
theorem stackArgumentCountLog0 : stackArgumentCount .log0 = 2 := rfl

-- @@ L61-61 verbatim
theorem stackArgumentCountLog1 : stackArgumentCount .log1 = 3 := rfl

-- @@ L62-62 verbatim
theorem stackArgumentCountLog2 : stackArgumentCount .log2 = 4 := rfl

-- @@ L63-63 verbatim
theorem stackArgumentCountLog3 : stackArgumentCount .log3 = 5 := rfl

-- @@ L64-64 verbatim
theorem stackArgumentCountLog4 : stackArgumentCount .log4 = 6 := rfl


-- @@ L66-67 verbatim
theorem topicCountOk_iff (kind : Kind) (args : Args) :
    topicCountOk kind args ↔ args.topics.length = topicCount kind := Iff.rfl


-- @@ L69-70 verbatim
theorem topicCountOk_log0 (data : MemoryRange) :
    topicCountOk .log0 { data := data, topics := [] } := rfl


-- @@ L72-73 verbatim
theorem topicCountOk_log1 (data : MemoryRange) (topic : EvmWord) :
    topicCountOk .log1 { data := data, topics := [topic] } := rfl


-- @@ L75-77 verbatim
theorem topicCountOk_log4
    (data : MemoryRange) (topic0 topic1 topic2 topic3 : EvmWord) :
    topicCountOk .log4 { data := data, topics := [topic0, topic1, topic2, topic3] } := rfl


-- @@ L79-79 verbatim
end LogArgs


-- @@ L81-81 verbatim
end EvmAsm.Evm64
