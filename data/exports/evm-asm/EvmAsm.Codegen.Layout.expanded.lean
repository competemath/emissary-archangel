/-
  EvmAsm.Codegen.Layout

  Asm program layout: the `_start` text-unit wrapper, halt stubs, and the
  `BuildUnit` glue that lets a verified `Program` body sit alongside raw
  asm text (prologue, epilogue, `.data` seeding) needed to run on
  `ziskemu`.

  Halt convention is parametric (see CODEGEN.md §"Locked decisions"):
    `.sp1`     — `ECALL` with `t0 = 0`, matches the verified
                 `step_ecall_halt` (`EvmAsm/Rv64/Execution.lean:611-615`).
                 `ziskemu` does NOT honor this (resolved 2026-05-18 — see
                 CODEGEN.md §Tricky bits #5).
    `.linux93` — `ECALL` with `a7 = 93`, matches Zisk's `simple_add`.
                 `ziskemu` halts cleanly. Default for codegen output.

  The halt stubs and any prologue/epilogue/.data are emitted as raw
  GNU-as text rather than as `Instr` values because they sit outside the
  verified body. This keeps `emitInstr` total over `Instr` without
  forcing M2+ wiring (write_output, data sections, `la` pseudo) into
  the verified core.
-/

module

public import EvmAsm.Codegen.Emit
meta import EvmAsm.Codegen.Emit


-- @@ L29-29 verbatim
@[expose] public section


-- @@ L31-31 verbatim
namespace EvmAsm.Codegen


-- @@ L33-33 verbatim
open EvmAsm.Rv64


-- @@ L35-39 verbatim
/-- Halt convention selected at codegen time. -/
inductive HaltConv where
  | sp1
  | linux93
  deriving DecidableEq, Repr


-- @@ L41-41 verbatim
namespace HaltConv


-- @@ L43-46 verbatim
def ofString? : String → Option HaltConv
  | "sp1"     => some .sp1
  | "linux93" => some .linux93
  | _         => none


-- @@ L48-50 verbatim
def toString : HaltConv → String
  | .sp1     => "sp1"
  | .linux93 => "linux93"


-- @@ L52-52 verbatim
instance : ToString HaltConv := ⟨HaltConv.toString⟩


-- @@ L54-54 verbatim
end HaltConv


-- @@ L56-61 verbatim
/-! ## Verified memory zones (mirror of `EvmAsm/Rv64/Basic.lean`)

    Post-#5164 the verified model recognises three disjoint zones;
    the codegen side carries the same constants so any address-bounds
    introspection downstream sees the same numeric values.
-/


-- @@ L63-65 verbatim
/-- Inclusive lower bound of the legacy valid memory zone.
    Mirrors `MEM_START` at `EvmAsm/Rv64/Basic.lean`. -/
def MEM_START : Nat := 0x20


-- @@ L67-68 verbatim
/-- Inclusive upper bound of the legacy valid memory zone. -/
def MEM_END : Nat := 0x78000000


-- @@ L70-71 verbatim
/-- Lower bound of the input-buffer zone (matches `INPUT_ADDR`). -/
def INPUT_MEM_START : Nat := 0x40000000


-- @@ L73-74 verbatim
/-- Upper bound of the input-buffer zone. -/
def INPUT_MEM_END : Nat := 0x40002000


-- @@ L76-78 verbatim
/-- Lower bound of the writable-RAM zone (covers `.data`
    and `OUTPUT_ADDR`). -/
def RAM_MEM_START : Nat := 0xa0000000


-- @@ L80-81 verbatim
/-- Upper bound of the writable-RAM zone. -/
def RAM_MEM_END : Nat := 0xc0000000


-- @@ L83-89 verbatim
/-! ## Recursive RLP decoder reservation

    The decoder's recursion policy and the adapter's private frame reservation
    are kept here, alongside the other codegen layout constants, so the
    emitted section and the RegionMap consume one source of truth.  The
    adapter has one root frame in addition to one 40-byte frame per bounded
    recursive level. -/


-- @@ L91-97 verbatim
/-- Machine recursion threshold used by the linked Amsterdam guest.
    The externally observed nesting count includes two wrapper levels above the
    machine counter: with cap `C`, the walk accepts through observed depth
    `C + 1` and first rejects at observed depth `C + 2`.  This offset describes
    how to interpret depth measurements; it does not make an observed reference
    threshold a specification-mandated value for this machine cap. -/
def rlpRecursiveDecodeDepthCap : Nat := 1024


-- @@ L99-101 verbatim
/-- Bytes reserved by the adapter's frame arena for a given depth cap. -/
def rlpRecursiveDecodeFrameBytes (depthCap : Nat) : Nat :=
  40 * depthCap + 40


-- @@ L103-118 verbatim
/-- A program-plus-wrapping that codegen knows how to turn into a single
    `.s` file: the verified RV64 body, optional raw-asm prologue and
    epilogue (e.g. data-pointer setup and `write_output`), and an
    optional `.data` section. -/
structure BuildUnit where
  /-- The verified body, rendered via `emitProgram`. -/
  body         : Program
  /-- Raw asm emitted after `_start:` and before `body` (e.g.
      `la x12, operands`). Empty string means "omit". -/
  prologueAsm  : String := ""
  /-- Raw asm emitted after `body` and before the halt stub (e.g.
      a `write_output` ecall sequence). Empty string means "omit". -/
  epilogueAsm  : String := ""
  /-- Raw asm for a `.data` section, including the `.section .data`
      header. Emitted after the halt stub. Empty string means "omit". -/
  dataAsm      : String := ""


-- @@ L120-128 verbatim
/-- Halt stub emitted after the body + epilogue. -/
def emitHaltStub : HaltConv → String
  | .sp1 =>
      "  li x5, 0\n" ++
      "  ecall"
  | .linux93 =>
      "  li x17, 93\n" ++
      "  li x10, 0\n" ++
      "  ecall"


-- @@ L130-141 verbatim
/-- Header preamble: disable RVC so every encoding is a 4-byte instruction
    (predictable PC arithmetic; required for the future binary encoder). -/
def textPreamble : String :=
  ".option norvc\n" ++
  ".section .text\n" ++
  ".globl _start\n" ++
  "_start:"

-- `private` dropped: `emitSource`/`emitSourceR` are exposed public bodies that
-- reference this, and a public body may not mention a private declaration
-- (MODULES.md §5a). Checked first, per §5b: the name is unique in the tree
-- and no `open private` site names it.

-- @@ L142-143 verbatim
def joinNonEmpty (xs : List String) : String :=
  String.intercalate "\n" (xs.filter (fun s => ¬ s.isEmpty))


-- @@ L145-158 verbatim
/-! ## Zero-initialized data

    GNU `as` emits `.zero` inside a normal `.data` section as PROGBITS, which
    makes the file contain every byte of the guest's large scratch arenas.  The
    source generators intentionally keep labels, alignment, and nonzero tables
    interleaved, so the final data string is split here at the common
    `BuildUnit` boundary, GROUP-wise: a group is an alignment/label prefix plus
    the payload lines that follow it, and it moves to `.bss` only when every
    payload line is a zero directive.  A group with any nonzero payload stays
    whole in `.data` — splitting mid-group tears the nonzero tail away from its
    label (e.g. `blsg_b_be: .zero 47 / .byte 0x04`, the BLS12-381 curve
    constant, would read as b = 0 and break every finite-G1 on-curve check).
    This preserves every symbol's relative order within its new section while
    leaving the emitted instruction text untouched. -/


-- @@ L160-165 verbatim
/-! ⚠️ The `private` on the helpers below was dropped, not worked around.
    `emitSource`/`emitSourceR` are exposed public bodies, and a public body may
    not mention a private declaration (MODULES.md §5a) — which cascades through
    `moveZeroDataToBss` to everything it calls. Checked first, per §5a hazard 2
    and §5b: every name here is unique tree-wide and none is reached by an
    `open private` site, so widening cannot collide or break a consumer. -/


-- @@ L167-167 verbatim
def trimmed (line : String) : String := line.trimAscii.toString


-- @@ L169-170 verbatim
def isSection (name line : String) : Bool :=
  (trimmed line).startsWith (".section " ++ name)


-- @@ L172-176 verbatim
def isZeroDirective (line : String) : Bool :=
  let t := trimmed line
  t == ".zero" || t.startsWith ".zero " || t.startsWith ".zero\t" ||
    t.startsWith ".skip " || t.startsWith ".skip\t" ||
    t.startsWith ".space " || t.startsWith ".space\t"


-- @@ L178-181 verbatim
def isZeroPrefix (line : String) : Bool :=
  let t := trimmed line
  t.isEmpty || t.startsWith "#" || t.startsWith ".balign " ||
    (t.endsWith ":" && !t.startsWith ".")


-- @@ L183-184 verbatim
def isSectionDirective (line : String) : Bool :=
  (trimmed line).startsWith ".section "


-- @@ L186-187 verbatim
def isPushDataSection (line : String) : Bool :=
  (trimmed line).startsWith ".pushsection .data"


-- @@ L189-190 verbatim
def isPopSection (line : String) : Bool :=
  trimmed line == ".popsection"


-- @@ L192-193 verbatim
def flushPending (pending : List String) (outRev : List String) : List String :=
  pending.reverse.foldl (fun acc line => line :: acc) outRev


-- @@ L195-209 verbatim
/-- Emit one buffered group (prefix + payload, both reversed) into `.bss` when
    the payload is nonempty and all-zero, else into `.data`, inserting a section
    switch when the target differs from the currently open one.  Returns the
    section left open. -/
def flushGroup (curIsBss : Bool)
    (prefixRev payloadRev : List String) (outRev : List String) :
    Bool × List String :=
  if prefixRev.isEmpty && payloadRev.isEmpty then (curIsBss, outRev)
  else
    let toBss := !payloadRev.isEmpty && payloadRev.all isZeroDirective
    let outRev :=
      if curIsBss == toBss then outRev
      else (if toBss then ".section .bss,\"aw\",@nobits"
            else ".section .data") :: outRev
    (toBss, flushPending payloadRev (flushPending prefixRev outRev))


-- @@ L211-238 verbatim
def moveZeroDataLines
    (lines : List String) (inData curIsBss : Bool)
    (prefixRev payloadRev : List String) (outRev : List String) : List String :=
  match lines with
  | [] => (flushGroup curIsBss prefixRev payloadRev outRev).2
  | line :: rest =>
      if isSectionDirective line || isPushDataSection line || isPopSection line then
        let (curIsBss, outRev) := flushGroup curIsBss prefixRev payloadRev outRev
        -- a `.popsection` restores the pushed section, so close any `.bss`
        -- we opened inside the pushed `.data` region first
        let outRev :=
          if isPopSection line && curIsBss then ".section .data" :: outRev else outRev
        let inData' :=
          if isPushDataSection line then true
          else if isPopSection line then false
          else isSection ".data" line
        moveZeroDataLines rest inData' false [] [] (line :: outRev)
      else if inData then
        if isZeroPrefix line then
          if payloadRev.isEmpty then
            moveZeroDataLines rest inData curIsBss (line :: prefixRev) [] outRev
          else
            let (curIsBss, outRev) := flushGroup curIsBss prefixRev payloadRev outRev
            moveZeroDataLines rest inData curIsBss [line] [] outRev
        else
          moveZeroDataLines rest inData curIsBss prefixRev (line :: payloadRev) outRev
      else
        moveZeroDataLines rest inData curIsBss [] [] (line :: outRev)


-- @@ L240-259 verbatim
def moveZeroDataToBss (asm : String) : String :=
  String.intercalate "\n"
    ((moveZeroDataLines (asm.splitOn "\n") false false [] [] []).reverse)

-- A mixed group (zero run + nonzero tail under one label) must stay WHOLE in
-- `.data`; only the following all-zero group moves.  Splitting the mixed group
-- was the b = 4 → 0 curve-constant regression (bead evm-asm-rowr9).
#guard moveZeroDataToBss
    ".section .data\nblsg_b_be:\n  .zero 47\n  .byte 0x04\nnext:\n  .zero 8" =
  ".section .data\nblsg_b_be:\n  .zero 47\n  .byte 0x04\n" ++
    ".section .bss,\"aw\",@nobits\nnext:\n  .zero 8"

-- All-zero groups move to `.bss` with their alignment/label prefix; a
-- following nonzero group switches back to `.data`.
#guard moveZeroDataToBss
    (".section .data\nfoo:\n  .byte 0x01\n.balign 8\nbar:\n  .zero 48\n" ++
      "baz:\n  .byte 0x02") =
  ".section .data\nfoo:\n  .byte 0x01\n" ++
    ".section .bss,\"aw\",@nobits\n.balign 8\nbar:\n  .zero 48\n" ++
    ".section .data\nbaz:\n  .byte 0x02"


-- @@ L261-271 verbatim
/-- Render a full `.s` file from a `BuildUnit` and halt convention. -/
def emitBuildUnit (hc : HaltConv) (u : BuildUnit) : String :=
  joinNonEmpty
    [ textPreamble
    , u.prologueAsm
    , emitProgram u.body
    , moveZeroDataToBss u.epilogueAsm
    , emitHaltStub hc
    , moveZeroDataToBss u.dataAsm
    , ""  -- trailing newline
    ]


-- @@ L273-275 verbatim
/-- A `.dword 0x…` line for a 64-bit value. Two-space indent, lowercase hex. -/
def emitDword (n : UInt64) : String :=
  s!"  .dword 0x{natToHex n.toNat}"


-- @@ L277-284 verbatim
/-- Build a `.data` section with a label and a list of 64-bit values
    (little-endian on disk because `.dword` emits LE on RV64). -/
def emitDataLabel (sectionName label : String) (values : List UInt64) : String :=
  joinNonEmpty
    ([ s!".section {sectionName}"
     , ".balign 8"
     , s!"{label}:" ]
     ++ values.map emitDword)


-- @@ L286-286 verbatim
end EvmAsm.Codegen
