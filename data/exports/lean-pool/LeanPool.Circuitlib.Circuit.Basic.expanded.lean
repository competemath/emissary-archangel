/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category

public import LeanPool.Circuitlib.Circuit.Category.Basic
public import LeanPool.Circuitlib.Circuit.Belnap.Gate


-- @@ L13-20 verbatim
/-! # Circuits

## References

* [N. D. Belnap, *A Useful Four-Valued Logic*][Belnap1977]
* [Ghica, Kaye, and Sprunger, *A Complete Theory of Sequential Digital Circuits*][Ghica2025]

-/


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
namespace Circuit


-- @@ L26-26 verbatim
open CategoryTheory

-- @@ L27-27 verbatim
open OfNat


-- @@ L29-29 verbatim
universe u


-- @@ L31-36 verbatim
variable
  {C : Type u}
  [∀ n, OfNat C n]
  [Category C]
  [MonoidalCategory C]
  [CircuitCategory BelnapLevel BelnapGate C]


-- @@ L38-39 verbatim
/-- The AND gate as a circuit morphism. -/
abbrev and : (ofNat 2 : C) ⟶ 1 := CircuitCategory.gate BelnapGate.and


-- @@ L41-42 verbatim
/-- The OR gate as a circuit morphism. -/
abbrev or : (ofNat 2 : C) ⟶ 1 := CircuitCategory.gate BelnapGate.or


-- @@ L44-45 verbatim
/-- The NOT gate as a circuit morphism. -/
abbrev not : (ofNat 1 : C) ⟶ 1 := CircuitCategory.gate BelnapGate.not


-- @@ L47-47 verbatim
open MonoidalCategory


-- @@ L49-50 verbatim
/-- The NAND gate, built as AND followed by NOT. -/
abbrev nand : (ofNat 2 : C) ⟶ 1 := and ≫ not


-- @@ L52-53 verbatim
/-- The NOR gate, built as OR followed by NOT. -/
abbrev nor : (ofNat 2 : C) ⟶ 1 := or ≫ not


-- @@ L55-55 verbatim
end Circuit
