/-
  EvmAsm.Evm64.EvmWordArith.DivC3InvariantTrivials

  Trivial direct discharges of `MulsubMaxC3OneOfCarryZero` and
  `MulsubBltC3OneOfCarryZero` under the strong hypothesis that the mulsub
  carry `c3` equals 1.

  These are building blocks for the "selected reachable path with c3 = 1"
  case of the full discharge work; the harder case is when c3 = 0 with
  certain stack/value conditions.
-/

module

public import EvmAsm.Evm64.EvmWordArith.DivMaxC3Invariant
public import EvmAsm.Evm64.EvmWordArith.DivBltC3Invariant


-- @@ L18-18 verbatim
public section


-- @@ L20-20 verbatim
namespace EvmAsm.Evm64


-- @@ L22-22 verbatim
open EvmWord EvmAsm.Rv64


-- @@ L24-31 verbatim
/-- Trivial discharge of `MulsubMaxC3OneOfCarryZero` from `c3 = 1`. -/
theorem MulsubMaxC3OneOfCarryZero_of_c3_eq_one
    (v0 v1 v2 v3 u0 u1 u2 u3 : Word)
    (hc3 : (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 = 1) :
    MulsubMaxC3OneOfCarryZero v0 v1 v2 v3 u0 u1 u2 u3 := by
  unfold MulsubMaxC3OneOfCarryZero
  intro _
  exact hc3


-- @@ L33-42 verbatim
/-- Trivial discharge of `MulsubBltC3OneOfCarryZero` from `c3 = 1`. -/
theorem MulsubBltC3OneOfCarryZero_of_c3_eq_one
    (uHi uLo vTop : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 : Word)
    (hc3 : (mulsubN4 (divKTrialCallV4QHat uHi uLo vTop)
              v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 = 1) :
    MulsubBltC3OneOfCarryZero uHi uLo vTop v0 v1 v2 v3 u0 u1 u2 u3 := by
  show _ → _
  intro _
  exact hc3


-- @@ L44-44 verbatim
end EvmAsm.Evm64
