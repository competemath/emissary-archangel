/-
  EvmAsm.Evm64.DivMod.Compose.OffsetsV6

  Named byte offsets and code bundles for the n=1 fast-path programs
  `evm_div_v6` / `evm_mod_v6` (issue #9303), mirroring `Compose.Offsets` for
  the base v5 layout. The `drift_check_*` examples below fail to compile if a
  block length changes without the matching offset being bumped.

  Layout of `evm_div_v6` (bytes from program base; instruction count in parens):
    [dispatchN1Off  =   0] divK_dispatchN1 796 788     (8)
    [v6ClzOff       =  32] divK_clz                    (24)
    [v6SetupOff     = 128] divK_fastSetup 88           (7)
    [v6NormAOff     = 156] divK_normA 40               (21)
    [v6CopyAUOff    = 240] divK_copyAU                 (9)
    [v6Digit3Off    = 276] divK_fastDigit .. 188       (10)
    [v6Digit2Off    = 316] divK_fastDigit .. 148       (10)
    [v6Digit1Off    = 356] divK_fastDigit .. 108       (10)
    [v6Digit0Off    = 396] divK_fastDigit .. 68        (10)
    [v6EpilogueOff  = 436] divK_div_epilogue 1412      (10)
    [v6Div128Off    = 476] divK_div128_v5              (85)  ← fast path's own copy
    [v6V5Off        = 816] evm_div_v5                  (353)
    [v6ExitOff      =1884] embedded v5 NOP (= v6V5Off + nopOff)

  `evm_mod_v6` inserts `divK_fastDenorm` (7) at [modV6DenormOff = 436], pushing
  the MOD epilogue / div128 copy / v5 down by 7 instructions (28 bytes).
-/

module

public import EvmAsm.Evm64.DivMod.FastN1Program
public import EvmAsm.Evm64.DivMod.Compose.V5Code2


-- @@ L33-33 verbatim
public section


-- @@ L35-35 verbatim
namespace EvmAsm.Evm64


-- @@ L37-41 verbatim
open EvmAsm.Rv64

-- ============================================================================
-- evm_div_v6 block offsets
-- ============================================================================


-- @@ L43-43 verbatim
abbrev dispatchN1Off : Word :=    0

-- @@ L44-44 verbatim
abbrev v6ClzOff      : Word :=   32

-- @@ L45-45 verbatim
abbrev v6SetupOff    : Word :=  128

-- @@ L46-46 verbatim
abbrev v6NormAOff    : Word :=  156

-- @@ L47-47 verbatim
abbrev v6CopyAUOff   : Word :=  240

-- @@ L48-48 verbatim
abbrev v6Digit3Off   : Word :=  276

-- @@ L49-49 verbatim
abbrev v6Digit2Off   : Word :=  316

-- @@ L50-50 verbatim
abbrev v6Digit1Off   : Word :=  356

-- @@ L51-51 verbatim
abbrev v6Digit0Off   : Word :=  396

-- @@ L52-52 verbatim
abbrev v6EpilogueOff : Word :=  436

-- @@ L53-53 verbatim
abbrev v6Div128Off   : Word :=  476

-- @@ L54-54 verbatim
abbrev v6V5Off       : Word :=  816

-- @@ L55-58 verbatim
/-- v6 exit PC = embedded v5's NOP block (v6V5Off + nopOff = 816 + 1068). -/
abbrev v6ExitOff     : Word := 1884

-- evm_mod_v6: identical through the digits, then a denorm block is inserted.

-- @@ L59-59 verbatim
abbrev modV6DenormOff   : Word :=  436

-- @@ L60-60 verbatim
abbrev modV6EpilogueOff : Word :=  464

-- @@ L61-61 verbatim
abbrev modV6Div128Off   : Word :=  504

-- @@ L62-62 verbatim
abbrev modV6V5Off       : Word :=  844

-- @@ L63-67 verbatim
abbrev modV6ExitOff     : Word := 1912

-- ============================================================================
-- Code bundles
-- ============================================================================


-- @@ L69-86 verbatim
/-- Full `evm_div_v6` code as block-decomposed `CodeReq`. The last element is
    the reused v5 bundle at the shifted base, so `divCode_v5 (base + v6V5Off)`
    is a sub-bundle (for framing `evm_div_stack_spec_unconditional`). -/
abbrev divCodeV6 (base : Word) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg  base                   (divK_dispatchN1 796 788),
    CodeReq.ofProg (base + v6ClzOff)       divK_clz,
    CodeReq.ofProg (base + v6SetupOff)     (divK_fastSetup 88),
    CodeReq.ofProg (base + v6NormAOff)     (divK_normA 40),
    CodeReq.ofProg (base + v6CopyAUOff)    divK_copyAU,
    CodeReq.ofProg (base + v6Digit3Off)    (divK_fastDigit 4024 4032 4064 188),
    CodeReq.ofProg (base + v6Digit2Off)    (divK_fastDigit 4032 4040 4072 148),
    CodeReq.ofProg (base + v6Digit1Off)    (divK_fastDigit 4040 4048 4080 108),
    CodeReq.ofProg (base + v6Digit0Off)    (divK_fastDigit 4048 4056 4088 68),
    CodeReq.ofProg (base + v6EpilogueOff)  (divK_div_epilogue 1412),
    CodeReq.ofProg (base + v6Div128Off)    divK_div128_v5,
    divCode_v5 (base + v6V5Off)
  ]


-- @@ L88-108 verbatim
/-- Full `evm_mod_v6` code as block-decomposed `CodeReq`. -/
abbrev modCodeV6 (base : Word) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg  base                     (divK_dispatchN1 824 816),
    CodeReq.ofProg (base + v6ClzOff)         divK_clz,
    CodeReq.ofProg (base + v6SetupOff)       (divK_fastSetup 88),
    CodeReq.ofProg (base + v6NormAOff)       (divK_normA 40),
    CodeReq.ofProg (base + v6CopyAUOff)      divK_copyAU,
    CodeReq.ofProg (base + v6Digit3Off)      (divK_fastDigit 4024 4032 4064 216),
    CodeReq.ofProg (base + v6Digit2Off)      (divK_fastDigit 4032 4040 4072 176),
    CodeReq.ofProg (base + v6Digit1Off)      (divK_fastDigit 4040 4048 4080 136),
    CodeReq.ofProg (base + v6Digit0Off)      (divK_fastDigit 4048 4056 4088 96),
    CodeReq.ofProg (base + modV6DenormOff)   divK_fastDenorm,
    CodeReq.ofProg (base + modV6EpilogueOff) (divK_mod_epilogue 1412),
    CodeReq.ofProg (base + modV6Div128Off)   divK_div128_v5,
    modCode_v5 (base + modV6V5Off)
  ]

-- ============================================================================
-- Drift checks — each block's start = previous start + 4 * previous length.
-- ============================================================================


-- @@ L110-110 verbatim
example : v6ClzOff      = dispatchN1Off + 4 * (divK_dispatchN1 796 788).length := by decide

-- @@ L111-111 verbatim
example : v6SetupOff    = v6ClzOff      + 4 * divK_clz.length := by decide

-- @@ L112-112 verbatim
example : v6NormAOff    = v6SetupOff    + 4 * (divK_fastSetup 88).length := by decide

-- @@ L113-113 verbatim
example : v6CopyAUOff   = v6NormAOff    + 4 * (divK_normA 40).length := by decide

-- @@ L114-114 verbatim
example : v6Digit3Off   = v6CopyAUOff   + 4 * divK_copyAU.length := by decide

-- @@ L115-115 verbatim
example : v6Digit2Off   = v6Digit3Off   + 4 * (divK_fastDigit 4024 4032 4064 188).length := by decide

-- @@ L116-116 verbatim
example : v6Digit1Off   = v6Digit2Off   + 4 * (divK_fastDigit 4032 4040 4072 148).length := by decide

-- @@ L117-117 verbatim
example : v6Digit0Off   = v6Digit1Off   + 4 * (divK_fastDigit 4040 4048 4080 108).length := by decide

-- @@ L118-118 verbatim
example : v6EpilogueOff = v6Digit0Off   + 4 * (divK_fastDigit 4048 4056 4088 68).length := by decide

-- @@ L119-119 verbatim
example : v6Div128Off   = v6EpilogueOff + 4 * (divK_div_epilogue 1412).length := by decide

-- @@ L120-123 verbatim
example : v6V5Off       = v6Div128Off   + 4 * divK_div128_v5.length := by
  have : divK_div128_v5.length = 85 := by unfold divK_div128_v5; rfl
  rw [this]; decide
-- exit = v5 entry + v5's internal NOP offset (1068)

-- @@ L124-126 verbatim
example : v6ExitOff = v6V5Off + 1068 := by decide

-- MOD layout (denorm inserted after the digits)

-- @@ L127-127 verbatim
example : modV6DenormOff   = v6Digit0Off      + 4 * (divK_fastDigit 4048 4056 4088 96).length := by decide

-- @@ L128-128 verbatim
example : modV6EpilogueOff = modV6DenormOff   + 4 * divK_fastDenorm.length := by decide

-- @@ L129-129 verbatim
example : modV6Div128Off   = modV6EpilogueOff + 4 * (divK_mod_epilogue 1412).length := by decide

-- @@ L130-132 verbatim
example : modV6V5Off       = modV6Div128Off   + 4 * divK_div128_v5.length := by
  have : divK_div128_v5.length = 85 := by unfold divK_div128_v5; rfl
  rw [this]; decide

-- @@ L133-133 verbatim
example : modV6ExitOff = modV6V5Off + 1068 := by decide


-- @@ L135-135 verbatim
end EvmAsm.Evm64
