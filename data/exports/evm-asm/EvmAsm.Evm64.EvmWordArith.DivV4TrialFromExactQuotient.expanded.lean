/-
  EvmAsm.Evm64.EvmWordArith.DivV4TrialFromExactQuotient

  Trivial discharge of `DivKTrialCallV4QHatLeFloorPlusOne` under the
  "exact quotient" condition: when `divKTrialCallV4QHat uHi uLo vTop`
  equals the true 128/64 floor exactly, the `+1` bound holds with
  zero overshoot.

  This is the simplest case of the named Knuth-A v4 frontier from PR
  #7031.  Existing exactness lemmas in `CallSkipLowerBoundV4/ExactQuotient`
  produce this equality under specific runtime conditions (no-wrap,
  rhatdd high zero); discharging the frontier under just normalisation
  + call regime is the substantive bead `7.1.4.1` work.
-/

module

public import EvmAsm.Evm64.EvmWordArith.DivV4TrialOverestimate


-- @@ L20-20 verbatim
public section


-- @@ L22-22 verbatim
namespace EvmAsm.Evm64


-- @@ L24-24 verbatim
open EvmWord EvmAsm.Rv64


-- @@ L26-35 verbatim
/-- Discharge `DivKTrialCallV4QHatLeFloorPlusOne` from an exact-quotient
    equality.  Reduces directly to `≤ + 0 + 1`. -/
theorem DivKTrialCallV4QHatLeFloorPlusOne_of_exact
    (uHi uLo vTop : Word)
    (h_exact : (divKTrialCallV4QHat uHi uLo vTop).toNat =
      (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat) :
    DivKTrialCallV4QHatLeFloorPlusOne uHi uLo vTop := by
  unfold DivKTrialCallV4QHatLeFloorPlusOne
  rw [h_exact]
  omega


-- @@ L37-37 verbatim
end EvmAsm.Evm64
