/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/
module

public import LeanPool.Circuitlib.Circuit.Belnap.Basic
public import LeanPool.Circuitlib.Circuit.Gate


-- @@ L11-18 verbatim
/-! # Belnap gates

## References

* [N. D. Belnap, *A Useful Four-Valued Logic*][Belnap1977]
* [Ghica, Kaye, and Sprunger, *A Complete Theory of Sequential Digital Circuits*][Ghica2025]

-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
namespace Circuit


-- @@ L24-28 verbatim
/-- The gate set for Belnap circuits: the logical AND, OR and NOT gates. -/
inductive BelnapGate
  | and
  | or
  | not


-- @@ L30-30 verbatim
namespace BelnapGate


-- @@ L32-45 verbatim
instance : Gate BelnapLevel BelnapGate where
  inputs
  | .and => 2
  | .or => 2
  | .not => 1
  outputs _ := 1
  gate
  | .and => Belnap.and
  | .or => Belnap.or
  | .not => Belnap.not
  gate_monotone
  | .and => Belnap.and_monotonic
  | .or => Belnap.or_monotonic
  | .not => Belnap.not_monotonic


-- @@ L47-47 verbatim
end BelnapGate


-- @@ L49-49 verbatim
end Circuit
