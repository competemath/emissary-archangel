/-
  EvmAsm.Evm64.CreateArgs

  Pure stack-argument records for CREATE-family opcodes (GH #115).
-/

module

public import EvmAsm.Evm64.EvmWord


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
namespace EvmAsm.Evm64


-- @@ L15-15 verbatim
namespace CreateArgs


-- @@ L17-21 verbatim
/-- Memory slice containing initcode, described by an EVM offset and byte size. -/
structure InitcodeRange where
  offset : EvmWord
  size : EvmWord
  deriving Repr


-- @@ L23-27 verbatim
/-- CREATE stack arguments: value plus initcode memory range. -/
structure Create where
  value : EvmWord
  initcode : InitcodeRange
  deriving Repr


-- @@ L29-34 verbatim
/-- CREATE2 stack arguments: value, initcode memory range, and salt. -/
structure Create2 where
  value : EvmWord
  initcode : InitcodeRange
  salt : EvmWord
  deriving Repr


-- @@ L36-40 verbatim
/-- Opcode family classifier for CREATE-family stack argument decoding. -/
inductive Kind where
  | create
  | create2
  deriving DecidableEq, Repr


-- @@ L42-44 verbatim
/-- The CREATE-family opcode kinds covered by GH #115. -/
def allKinds : List Kind :=
  [.create, .create2]


-- @@ L46-48 verbatim
def argumentCount : Kind → Nat
  | .create => 3
  | .create2 => 4


-- @@ L50-50 verbatim
def resultCount (_kind : Kind) : Nat := 1


-- @@ L52-52 verbatim
def initcodeRangeCount (_kind : Kind) : Nat := 1


-- @@ L54-56 verbatim
def usesSalt : Kind → Bool
  | .create => false
  | .create2 => true


-- @@ L58-58 verbatim
def hasInitcodeRange (_kind : Kind) : Bool := true


-- @@ L60-61 verbatim
theorem createArgumentCount :
    argumentCount .create = 3 := rfl


-- @@ L63-64 verbatim
theorem create2ArgumentCount :
    argumentCount .create2 = 4 := rfl


-- @@ L66-68 verbatim
theorem allKinds_nodup :
    allKinds.Nodup := by
  decide


-- @@ L70-72 verbatim
theorem mem_allKinds (kind : Kind) :
    kind ∈ allKinds := by
  cases kind <;> decide


-- @@ L74-75 verbatim
theorem allKinds_argumentCounts :
    allKinds.map argumentCount = [3, 4] := rfl


-- @@ L77-78 verbatim
theorem resultCount_eq_one (kind : Kind) :
    resultCount kind = 1 := rfl


-- @@ L80-81 verbatim
theorem initcodeRangeCount_eq_one (kind : Kind) :
    initcodeRangeCount kind = 1 := rfl


-- @@ L83-84 verbatim
theorem hasInitcodeRange_eq_true (kind : Kind) :
    hasInitcodeRange kind = true := rfl


-- @@ L86-88 verbatim
theorem argumentCount_eq_three_plus_salt (kind : Kind) :
    argumentCount kind = 3 + if usesSalt kind then 1 else 0 := by
  cases kind <;> rfl


-- @@ L90-91 verbatim
theorem createUsesNoSalt :
    usesSalt .create = false := rfl


-- @@ L93-94 verbatim
theorem create2UsesSalt :
    usesSalt .create2 = true := rfl


-- @@ L96-98 verbatim
theorem usesSalt_iff_create2 (kind : Kind) :
    usesSalt kind = true ↔ kind = .create2 := by
  cases kind <;> decide


-- @@ L100-102 verbatim
theorem not_usesSalt_iff_create (kind : Kind) :
    usesSalt kind = false ↔ kind = .create := by
  cases kind <;> decide


-- @@ L104-106 verbatim
theorem argumentCount_eq_three_iff_create (kind : Kind) :
    argumentCount kind = 3 ↔ kind = .create := by
  cases kind <;> decide


-- @@ L108-110 verbatim
theorem argumentCount_eq_four_iff_create2 (kind : Kind) :
    argumentCount kind = 4 ↔ kind = .create2 := by
  cases kind <;> decide


-- @@ L112-113 verbatim
theorem create2_argumentCount_eq_succ_create :
    argumentCount .create2 = argumentCount .create + 1 := rfl


-- @@ L115-118 verbatim
theorem create_initcode (args : Create) :
    args.initcode = { offset := args.initcode.offset, size := args.initcode.size } := by
  cases args.initcode
  rfl


-- @@ L120-123 verbatim
theorem create2_initcode (args : Create2) :
    args.initcode = { offset := args.initcode.offset, size := args.initcode.size } := by
  cases args.initcode
  rfl


-- @@ L125-125 verbatim
end CreateArgs


-- @@ L127-127 verbatim
end EvmAsm.Evm64
