/-
  EvmAsm.EL.CreateInitcodeBridge

  Bridge from CREATE/CREATE2 initcode stack ranges to memory bytes (GH #115).
-/

module

public import EvmAsm.EL.CreateArgsBridge


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
namespace EvmAsm.EL


-- @@ L15-15 verbatim
namespace CreateInitcodeBridge


-- @@ L17-17 verbatim
abbrev InitcodeRange := EvmAsm.Evm64.CreateArgs.InitcodeRange

-- @@ L18-18 verbatim
abbrev CreateArgs := EvmAsm.Evm64.CreateArgs.Create

-- @@ L19-19 verbatim
abbrev Create2Args := EvmAsm.Evm64.CreateArgs.Create2

-- @@ L20-20 verbatim
abbrev MemoryReader := Nat → Byte


-- @@ L22-24 verbatim
/-- First memory byte consumed as CREATE/CREATE2 initcode. -/
def initcodeStart (range : InitcodeRange) : Nat :=
  range.offset.toNat


-- @@ L26-28 verbatim
/-- Number of memory bytes consumed as CREATE/CREATE2 initcode. -/
def initcodeSize (range : InitcodeRange) : Nat :=
  range.size.toNat


-- @@ L30-33 verbatim
/-- CREATE/CREATE2 initcode bytes loaded from a pure memory-reader function.
    Distinctive token: CreateInitcodeBridge.initcodeFromMemory #115. -/
def initcodeFromMemory (readByte : MemoryReader) (range : InitcodeRange) : List Byte :=
  (List.range (initcodeSize range)).map (fun i => readByte (initcodeStart range + i))


-- @@ L35-36 verbatim
def createInitcodeFromMemory (readByte : MemoryReader) (args : CreateArgs) : List Byte :=
  initcodeFromMemory readByte (CreateArgsBridge.createInitcodeRange args)


-- @@ L38-39 verbatim
def create2InitcodeFromMemory (readByte : MemoryReader) (args : Create2Args) : List Byte :=
  initcodeFromMemory readByte (CreateArgsBridge.create2InitcodeRange args)


-- @@ L41-45 verbatim
/-- Build the EL CREATE request directly from stack args and a pure memory reader. -/
def createRequestFromMemory
    (creator : Address) (readByte : MemoryReader) (gas : EvmAsm.Evm64.EvmWord)
    (args : CreateArgs) : CreateRequest :=
  CreateArgsBridge.createRequest creator (createInitcodeFromMemory readByte args) gas args


-- @@ L47-51 verbatim
/-- Build the EL CREATE2 request directly from stack args and a pure memory reader. -/
def create2RequestFromMemory
    (creator : Address) (readByte : MemoryReader) (gas : EvmAsm.Evm64.EvmWord)
    (args : Create2Args) : CreateRequest :=
  CreateArgsBridge.create2Request creator (create2InitcodeFromMemory readByte args) gas args


-- @@ L53-54 verbatim
theorem initcodeStart_eq (range : InitcodeRange) :
    initcodeStart range = range.offset.toNat := rfl


-- @@ L56-57 verbatim
theorem initcodeSize_eq (range : InitcodeRange) :
    initcodeSize range = range.size.toNat := rfl


-- @@ L59-61 verbatim
@[simp] theorem initcodeFromMemory_length (readByte : MemoryReader) (range : InitcodeRange) :
    (initcodeFromMemory readByte range).length = initcodeSize range := by
  simp [initcodeFromMemory]


-- @@ L63-69 verbatim
theorem initcodeFromMemory_get
    {readByte : MemoryReader} {range : InitcodeRange} {i : Nat}
    (h : i < initcodeSize range) :
    (initcodeFromMemory readByte range)[i]'(by
      simpa [initcodeFromMemory_length] using h) =
      readByte (initcodeStart range + i) := by
  simp [initcodeFromMemory, List.getElem_map, List.getElem_range]


-- @@ L71-73 verbatim
@[simp] theorem initcodeFromMemory_zero_size
    (readByte : MemoryReader) (rangeOffset : EvmAsm.Evm64.EvmWord) :
    initcodeFromMemory readByte { offset := rangeOffset, size := 0 } = [] := rfl


-- @@ L75-78 verbatim
theorem createInitcodeFromMemory_eq
    (readByte : MemoryReader) (args : CreateArgs) :
    createInitcodeFromMemory readByte args =
      initcodeFromMemory readByte args.initcode := rfl


-- @@ L80-83 verbatim
theorem create2InitcodeFromMemory_eq
    (readByte : MemoryReader) (args : Create2Args) :
    create2InitcodeFromMemory readByte args =
      initcodeFromMemory readByte args.initcode := rfl


-- @@ L85-90 verbatim
theorem createRequestFromMemory_eq
    (creator : Address) (readByte : MemoryReader) (gas : EvmAsm.Evm64.EvmWord)
    (args : CreateArgs) :
    createRequestFromMemory creator readByte gas args =
      CreateArgsBridge.createRequest creator (createInitcodeFromMemory readByte args) gas args :=
  rfl


-- @@ L92-97 verbatim
theorem create2RequestFromMemory_eq
    (creator : Address) (readByte : MemoryReader) (gas : EvmAsm.Evm64.EvmWord)
    (args : Create2Args) :
    create2RequestFromMemory creator readByte gas args =
      CreateArgsBridge.create2Request creator (create2InitcodeFromMemory readByte args) gas args :=
  rfl


-- @@ L99-103 verbatim
theorem createRequestFromMemoryInitcode
    (creator : Address) (readByte : MemoryReader) (gas : EvmAsm.Evm64.EvmWord)
    (args : CreateArgs) :
    (createRequestFromMemory creator readByte gas args).initcode =
      createInitcodeFromMemory readByte args := rfl


-- @@ L105-109 verbatim
theorem create2RequestFromMemoryInitcode
    (creator : Address) (readByte : MemoryReader) (gas : EvmAsm.Evm64.EvmWord)
    (args : Create2Args) :
    (create2RequestFromMemory creator readByte gas args).initcode =
      create2InitcodeFromMemory readByte args := rfl


-- @@ L111-114 verbatim
theorem createRequestFromMemoryKind
    (creator : Address) (readByte : MemoryReader) (gas : EvmAsm.Evm64.EvmWord)
    (args : CreateArgs) :
    (createRequestFromMemory creator readByte gas args).kind = .create := rfl


-- @@ L116-119 verbatim
theorem create2RequestFromMemoryKind
    (creator : Address) (readByte : MemoryReader) (gas : EvmAsm.Evm64.EvmWord)
    (args : Create2Args) :
    (create2RequestFromMemory creator readByte gas args).kind = .create2 := rfl


-- @@ L121-124 verbatim
theorem createRequestFromMemoryValue
    (creator : Address) (readByte : MemoryReader) (gas : EvmAsm.Evm64.EvmWord)
    (args : CreateArgs) :
    (createRequestFromMemory creator readByte gas args).value = args.value := rfl


-- @@ L126-129 verbatim
theorem create2RequestFromMemorySalt?
    (creator : Address) (readByte : MemoryReader) (gas : EvmAsm.Evm64.EvmWord)
    (args : Create2Args) :
    (create2RequestFromMemory creator readByte gas args).salt? = some args.salt := rfl


-- @@ L131-131 verbatim
end CreateInitcodeBridge


-- @@ L133-133 verbatim
end EvmAsm.EL
