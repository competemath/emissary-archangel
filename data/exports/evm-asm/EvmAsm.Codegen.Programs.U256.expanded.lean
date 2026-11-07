/-
  EvmAsm.Codegen.Programs.U256

  U256-BE arithmetic / comparison helpers lifted out
  of `EvmAsm.Codegen.Programs.Tx` per the file-size hard cap.

  Atomic primitives:
    K51 u256_add_be
    K52 u256_sub_be
    K53 u256_eq
    K54 u256_mul_u64_be
    K56 u256_from_u64_be
    K57 u256_to_u64_be
    K58 u256_is_zero
    K59 u256_min
    K60 u256_max
    K61 u256_div_u64_be
    K160 u256_lt_be

  Lives standalone so Tx / Header / Block / Mpt consumers can
  import the u256 arithmetic family without pulling the full Tx module.

  GH #10753: BRIDGE of the U256 module split.  The Programs live in the leaf
  `EvmAsm.Codegen.Programs.U256Prog` parameterised over `GuestLayout`; this
  module re-exposes the applied ones under their ORIGINAL names and types
  (`def u256Xxx_prog : Program := u256Xxx_prog_of guestLayout`) so every
  consumer compiles untouched — the bridge name is also REQUIRED by the
  concrete-render gate (key `emitProgram <camel(entry)>_prog`).
-/

module

public import EvmAsm.Codegen.Layout
public import EvmAsm.Codegen.Programs.U256Prog
public import EvmAsm.Codegen.GuestLayoutInstance


-- @@ L37-37 verbatim
@[expose] public section


-- @@ L39-39 verbatim
namespace EvmAsm.Codegen


-- @@ L41-41 verbatim
open EvmAsm.Rv64


-- @@ L43-43 verbatim
def u256AddBe_prog : Program := u256AddBe_prog_of guestLayout


-- @@ L45-45 verbatim
def u256LtBe_prog : Program := u256LtBe_prog_of guestLayout


-- @@ L47-47 verbatim
def u256SubBe_prog : Program := u256SubBe_prog_of guestLayout


-- @@ L49-49 verbatim
def u256FromU64Be_prog : Program := u256FromU64Be_prog_of guestLayout


-- @@ L51-51 verbatim
def u256IsZero_prog : Program := u256IsZero_prog_of guestLayout


-- @@ L53-53 verbatim
def u256Min_prog : Program := u256Min_prog_of guestLayout


-- @@ L55-55 verbatim
def u256DivU64Be_prog : Program := u256DivU64Be_prog_of guestLayout


-- @@ L57-57 verbatim
def u256Eq_prog : Program := u256Eq_prog_of guestLayout


-- @@ L59-59 verbatim
def u256MulU64Be_prog : Program := u256MulU64Be_prog_of guestLayout


-- @@ L61-61 verbatim
end EvmAsm.Codegen
