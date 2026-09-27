/-
Copyright (c) 2026 Julius Marx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julius Marx
-/
module

public import LeanPool.MRiscX.AbstractSyntax.Map
public import LeanPool.MRiscX.AbstractSyntax.Instr


-- @@ L11-15 verbatim
/-!
# AbstractSyntax

This module provides core abstract-syntax types of the MRiscX assembly language.
-/


-- @@ L17-17 verbatim
@[expose] public section

-- @@ L18-18 verbatim
open Nat

-- @@ L19-19 verbatim
open Lean Lean.Elab

-- @@ L20-34 verbatim
/--
Purpose of this file:
This file establishes the syntax of the MRiscX assembly language, encompassing the definition
of instructions, labels, registers, memory and machine states. Given that the instructionsMap,
labels, registers, and memory are represented as maps, it may be beneficial to review the contents
of the file Maps.lean beforehand.


Next we define some Datatypes for the map keys.
This is because it makes it easier to understand which
map is being processed.
Firstly a register, which will hold a value
-/

abbrev Register := UInt64



-- @@ L37-38 verbatim
instance: Coe Register UInt64 where
 coe c := (c:UInt64)



-- @@ L41-45 verbatim
/--
Next, the memory address. This address will point to a certain
address in the memory which holds some value
-/
abbrev MemoryAddress := UInt64


-- @@ L47-51 verbatim
/--
The InstructionIndex is a serial number which points
to a instruction in the stack
-/
abbrev InstructionIndex := UInt64


-- @@ L53-54 verbatim
/-- The program counter: the index of the instruction currently being executed. -/
abbrev ProgramCounter := UInt64


-- @@ L56-65 verbatim
/--
A total map which holds the instructions of a program
tied to a unsigned 64-bit integers as InstructionIndex. The default value of this map
is the instruction Instr.Panic.

IM := {uint64_1 ↦ instr_1, uint64_2 ↦ instr_2, ..., uint64_n ↦ instr_n}
/ default:  Instr.IPanic
-/
def InstructionMap := TMap InstructionIndex Instr
deriving Repr, Inhabited


-- @@ L67-68 verbatim
instance : ToString InstructionMap where
  toString (instrMap : InstructionMap) := reprStr instrMap


-- @@ L70-73 verbatim
/--
Empty InstructionMap which serves as standard InstructionMap
-/
def EmptyInstructionMap : InstructionMap := TMap.empty Instr.Panic


-- @@ L75-82 verbatim
/--
A partial map LabelMap, which holds all the Labels as key and links these
to an unsigned 64-bit integers.

LM := {l_1 ↦ uint64_1, l_2 ↦ uint64_2, ..., l_n ↦ uint64_n}
-/
def LabelMap := PMap String UInt64
deriving Repr, Inhabited


-- @@ L84-85 verbatim
instance : ToString LabelMap where
  toString (labelMap : LabelMap) := reprStr labelMap



-- @@ L88-91 verbatim
/--
Empty LabelMap which serves as standard LabelMap
-/
def EmptyLabels : LabelMap := PMap.empty



-- @@ L94-102 verbatim
/--
The InstructionMap and the LabelMap are combined into a single structure,
which is refered as `Code`.
-/
structure Code where
  /-- The instruction map, associating each instruction index with an instruction. -/
  instructionMap: InstructionMap
  /-- The label map, associating each label name with its target index. -/
  labels: LabelMap



-- @@ L105-108 verbatim
/--
A default instance of Code, containing an empty `InstructionMap` and an empty `LabelMap`.
-/
def DefaultCode : Code := { instructionMap := EmptyInstructionMap, labels := EmptyLabels }




-- @@ L112-112 verbatim
namespace Code
  
-- @@ L113-115 verbatim
/-- Replace the instruction map of a `Code` with `c`. -/
  def setCMap (m : Code) (c : InstructionMap) : Code :=
    { m with instructionMap := c}

  
-- @@ L117-119 verbatim
/-- Replace the label map of a `Code` with `l`. -/
  def setLabels (m : Code) (l : LabelMap) : Code :=
    { m with labels := l}

  
-- @@ L121-125 expanded
/-- Add a list of `(name, index)` label bindings to a `Code`. -/
def addMultipleLabels (m : Code) (l : List (String × UInt64)) : Code :=
  match l with
  | [] => m
  | h :: t => addMultipleLabels { m with labels := PMap.put h.1 h.2 m.labels } t


-- @@ L127-129 expanded
/-- Insert an instruction `v` at index `id` into the instruction map of a `Code`. -/
def addCMap (m : Code) (id : InstructionIndex) (v : Instr) : Code :=
  { m with instructionMap := TMap.put id v m.instructionMap }


-- @@ L131-133 expanded
/-- Insert a label `id ↦ v` into the label map of a `Code`. -/
def addLabels (m : Code) (id : String) (v : UInt64) : Code :=
  { m with labels := PMap.put id v m.labels }


-- @@ L135-139 expanded
/-- Insert both an instruction and a label binding into a `Code`. -/
def addMaps (m : Code) (id_c : InstructionIndex) (v_c : Instr) (id_l : String) (v_l : UInt64) :
    Code :=
  { m with instructionMap := TMap.put id_c v_c m.instructionMap,
    labels := PMap.put id_l v_l m.labels }


-- @@ L141-143 verbatim
/-- Replace both the instruction map and the label map of a `Code`. -/
  def setMaps (m : Code) (c : InstructionMap) (l : LabelMap) : Code :=
    (m.setCMap c).setLabels l

  
-- @@ L145-146 verbatim
/-- Look up the target index of a label in a `Code`. -/
  def getLabel (m : Code) (l : String): Option UInt64 := m.labels.get l

  
-- @@ L148-149 verbatim
/-- Look up the instruction stored at index `l` in a `Code`. -/
  def getInstrAt (m : Code) (l : UInt64): Instr := m.instructionMap.get l

-- @@ L150-150 verbatim
end Code





-- @@ L155-160 verbatim
/--
Definiton of the registers
R := {r_1 ↦ w_1, … , r_k ↦ w_k}
-/
def Registers := TMap Register UInt64
  deriving Repr


-- @@ L162-167 verbatim
/--
RegisterMap with default value 0

R := {r_1 ↦ w_1, … , r_k ↦ w_k; 0}
-/
def EmptyRegisters : Registers := TMap.empty 0


-- @@ L169-174 verbatim
/--
Definiton of the memory
M := {m_1 ↦ w_1, … , m_k ↦ w_k}
-/
def Memory := TMap MemoryAddress UInt64
  deriving Repr



-- @@ L177-182 verbatim
/--
MemoryMap with default value 0

M := {m_1 ↦ w_1, … , m_k ↦ w_k; 0}
-/
def EmptyMemory : Memory := TMap.empty 0
