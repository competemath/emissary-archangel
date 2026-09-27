/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/
module

public import LeanPool.Circuitlib.Circuit.Category.Combinational
public import LeanPool.Circuitlib.Circuit.Basic


-- @@ L11-18 verbatim
/-! # Combinational circuits

## References

* [N. D. Belnap, *A Useful Four-Valued Logic*][Belnap1977]
* [Ghica, Kaye, and Sprunger, *A Complete Theory of Sequential Digital Circuits*][Ghica2025]

-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
namespace Circuit


-- @@ L24-24 verbatim
open CategoryTheory

-- @@ L25-25 verbatim
open MonoidalCategory

-- @@ L26-26 verbatim
open OfNat


-- @@ L28-29 verbatim
/-- The combinational circuit category over Belnap levels and Belnap gates. -/
abbrev CombinationalCircuit := CombinationalCircuitCategory BelnapLevel BelnapGate


-- @@ L31-31 verbatim
namespace CombinationalCircuit


-- @@ L33-34 verbatim
/-- The AND gate as a combinational circuit. -/
abbrev and := Circuit.and (C:=CombinationalCircuit)


-- @@ L36-37 verbatim
@[simp]
lemma and_def (x y : Bool) : and.val #v[↑x, ↑y] = #v[↑(x && y)] := by cases x <;> cases y <;> rfl


-- @@ L39-40 verbatim
/-- The OR gate as a combinational circuit. -/
abbrev or := Circuit.or (C:=CombinationalCircuit)


-- @@ L42-43 verbatim
@[simp]
lemma or_def (x y : Bool) : or.val #v[↑x, ↑y] = #v[↑(x || y)] := by cases x <;> cases y <;> rfl


-- @@ L45-46 verbatim
/-- The NOT gate as a combinational circuit. -/
abbrev not := Circuit.not (C:=CombinationalCircuit)


-- @@ L48-49 verbatim
@[simp]
lemma not_def (x : Bool) : not.val #v[↑x] = #v[↑(!x)] := by cases x <;> rfl


-- @@ L51-52 verbatim
/-- The NAND gate as a combinational circuit. -/
abbrev nand := Circuit.nand (C:=CombinationalCircuit)


-- @@ L54-56 verbatim
@[simp]
lemma nand_def (x y : Bool) : nand.val #v[↑x, ↑y] = #v[↑!((x && y))] := by
  cases x <;> cases y <;> rfl


-- @@ L58-59 verbatim
/-- The NOR gate as a combinational circuit. -/
abbrev nor := Circuit.nor (C:=CombinationalCircuit)


-- @@ L61-62 verbatim
@[simp]
lemma nor_def (x y : Bool) : nor.val #v[↑x, ↑y] = #v[↑(!(x || y))] := by cases x <;> cases y <;> rfl


-- @@ L64-65 verbatim
/-- The fork (wire duplication) as a combinational circuit. -/
abbrev fork := CircuitCategory.fork (C:=CombinationalCircuit)


-- @@ L67-68 verbatim
@[simp]
lemma fork_def (x : Bool) : fork.val #v[↑x] = #v[↑x, ↑x] := by cases x <;> rfl


-- @@ L70-71 verbatim
/-- Two forks in parallel, duplicating each of two input wires. -/
def fork₂ := fork ⊗ₘ fork


-- @@ L73-75 verbatim
@[simp]
lemma fork₂_def (x y : Bool) : fork₂.val #v[↑x, ↑y] = #v[↑x, ↑x, ↑y, ↑y] :=
  by cases x <;> cases y <;> simp <;> rfl


-- @@ L77-78 verbatim
/-- Duplicate a pair of input wires, interleaving so the output is `[x, y, x, y]`. -/
def copy : (ofNat 2 : CombinationalCircuit) ⟶ 4 := fork₂ ≫ (1 ◁ ((β_ 1 1).hom ▷ 1))


-- @@ L80-82 verbatim
@[simp]
lemma copy_def (x y : Bool) : copy.val #v[↑x, ↑y] = #v[↑x, ↑y, ↑x, ↑y] := by
  cases x <;> cases y <;> rfl


-- @@ L84-85 verbatim
/-- The XOR gate as a combinational circuit. -/
def xor : (ofNat 2 : CombinationalCircuit) ⟶ 1 := copy ≫ (and ⊗ₘ or) ≫ (not ⊗ₘ 𝟙 1) ≫ and


-- @@ L87-89 verbatim
@[simp]
lemma xor_def (x y : Bool) : xor.val #v[↑x, ↑y] = #v[↑((x && !y) || (!x && y))] := by
  cases x <;> cases y <;> rfl


-- @@ L91-92 verbatim
/-- The XNOR gate as a combinational circuit. -/
def xnor : (ofNat 2 : CombinationalCircuit) ⟶ 1 := xor ≫ not


-- @@ L94-96 verbatim
@[simp]
lemma xnor_def (x y : Bool) : xnor.val #v[↑x, ↑y] = #v[↑((x && y) || (!x && !y))] := by
  cases x <;> cases y <;> rfl


-- @@ L98-99 verbatim
/-- A half adder, returning the sum and carry of two input bits. -/
def halfAdder : (ofNat 2 : CombinationalCircuit) ⟶ 2 := copy ≫ (xor ⊗ₘ and)


-- @@ L101-105 verbatim
@[simp]
lemma halfAdder_def
    (x y : Bool) :
    halfAdder.val #v[↑x, ↑y] = #v[↑((x && !y) || (!x && y)), ↑(x && y)] := by
  cases x <;> cases y <;> rfl


-- @@ L107-112 verbatim
/-- A full adder built from two half adders, returning the sum and carry of three input bits. -/
def adder : (ofNat 3 : CombinationalCircuit) ⟶ 2 :=
  (halfAdder ⊗ₘ 𝟙 1) ≫
  (1 ◁ (β_ 1 1).hom) ⊗≫
  (halfAdder ⊗ₘ 𝟙 1) ≫
  (𝟙 1 ⊗ₘ or)


-- @@ L114-119 verbatim
@[simp]
lemma adder_def (x y z : Bool) :
    adder.val #v[↑x, ↑y, ↑z] =
      #v[↑((((x && !y) || (!x && y)) && !z) || (!(((x && !y) || (!x && y))) && z)),
         ↑((x && y) || (((x && !y) || (!x && y)) && z))] := by
  cases x <;> cases y <;> cases z <;> rfl


-- @@ L121-121 verbatim
end CombinationalCircuit


-- @@ L123-123 verbatim
end Circuit
