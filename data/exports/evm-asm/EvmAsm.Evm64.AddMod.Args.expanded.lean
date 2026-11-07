/-
  EvmAsm.Evm64.AddMod.Args

  Pure stack-argument bridge for ADDMOD (GH #91).
-/

module

public import EvmAsm.Evm64.EvmWordArith.AddMod


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
namespace EvmAsm.Evm64

-- @@ L14-14 verbatim
namespace AddModArgs


-- @@ L16-21 verbatim
/-- ADDMOD stack arguments: first addend, second addend, and modulus. -/
structure Args where
  a : EvmWord
  b : EvmWord
  N : EvmWord
  deriving Repr


-- @@ L23-24 verbatim
/-- ADDMOD pops three stack words. -/
def stackArgumentCount : Nat := 3


-- @@ L26-27 verbatim
/-- ADDMOD pushes one result word. -/
def resultCount : Nat := 1


-- @@ L29-31 verbatim
/-- Convenience builder for ADDMOD stack arguments. -/
def addmodArgs (a b N : EvmWord) : Args :=
  { a := a, b := b, N := N }


-- @@ L33-35 verbatim
/-- ADDMOD result computed from decoded stack arguments. -/
def addmodResultFromArgs (args : Args) : EvmWord :=
  EvmWord.addmod args.a args.b args.N


-- @@ L37-39 verbatim
/-- Stack after the ADDMOD result replaces the three operands. -/
def stackAfterAddMod (args : Args) (rest : List EvmWord) : List EvmWord :=
  addmodResultFromArgs args :: rest


-- @@ L41-41 verbatim
theorem stackArgumentCount_eq_three : stackArgumentCount = 3 := rfl


-- @@ L43-43 verbatim
theorem resultCount_eq_one : resultCount = 1 := rfl


-- @@ L45-46 verbatim
theorem addmodArgs_a (a b N : EvmWord) :
    (addmodArgs a b N).a = a := rfl


-- @@ L48-49 verbatim
theorem addmodArgs_b (a b N : EvmWord) :
    (addmodArgs a b N).b = b := rfl


-- @@ L51-52 verbatim
theorem addmodArgs_N (a b N : EvmWord) :
    (addmodArgs a b N).N = N := rfl


-- @@ L54-55 verbatim
theorem addmodResultFromArgs_eq (args : Args) :
    addmodResultFromArgs args = EvmWord.addmod args.a args.b args.N := rfl


-- @@ L57-58 verbatim
theorem stackAfterAddMod_eq (args : Args) (rest : List EvmWord) :
    stackAfterAddMod args rest = addmodResultFromArgs args :: rest := rfl


-- @@ L60-62 verbatim
@[simp] theorem stackAfterAddMod_length (args : Args) (rest : List EvmWord) :
    (stackAfterAddMod args rest).length = rest.length + 1 := by
  simp [stackAfterAddMod]


-- @@ L64-66 verbatim
@[simp] theorem addmodResultFromArgs_zero_modulus (a b : EvmWord) :
    addmodResultFromArgs (addmodArgs a b 0) = 0 := by
  exact EvmWord.addmod_zero a b


-- @@ L68-68 verbatim
end AddModArgs

-- @@ L69-69 verbatim
end EvmAsm.Evm64
