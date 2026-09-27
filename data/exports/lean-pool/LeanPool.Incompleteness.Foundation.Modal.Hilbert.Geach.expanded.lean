/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.Hilbert.WellKnown


-- @@ L10-10 verbatim
/-! # Geach -/


-- @@ L12-12 verbatim
@[expose] public section



-- @@ L15-15 verbatim
namespace LO

-- @@ L16-16 verbatim
namespace Modal


-- @@ L18-18 verbatim
namespace Hilbert


-- @@ L20-20 verbatim
variable (α) [DecidableEq α]


-- @@ L22-26 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Geach (G : Set (Geachean.Taple)) : Hilbert ℕ := ⟨
  {Axioms.K (.atom 0) (.atom 1)}
  ∪ G.image (fun t => Axioms.Geach t (.atom 0))
⟩


-- @@ L28-28 verbatim
instance : HasK (Hilbert.Geach G) where p := 0; q := 1

-- @@ L29-29 verbatim
instance : Entailment.K (Hilbert.Geach G) where


-- @@ L31-32 verbatim
lemma _root_.LO.Modal.Hilbert.K4.eq_Geach :
    Hilbert.K4   = Hilbert.Geach {⟨0, 2, 1, 0⟩} := by aesop;

-- @@ L33-34 verbatim
lemma _root_.LO.Modal.Hilbert.K45.eq_Geach :
    Hilbert.K45  = Hilbert.Geach {⟨0, 2, 1, 0⟩, ⟨1, 1, 0, 1⟩} := by aesop;

-- @@ L35-36 verbatim
lemma _root_.LO.Modal.Hilbert.K5.eq_Geach :
    Hilbert.K5   = Hilbert.Geach {⟨1, 1, 0, 1⟩} := by aesop;

-- @@ L37-38 verbatim
lemma _root_.LO.Modal.Hilbert.KB.eq_Geach :
    Hilbert.KB   = Hilbert.Geach {⟨0, 1, 0, 1⟩} := by aesop;

-- @@ L39-40 verbatim
lemma _root_.LO.Modal.Hilbert.KB4.eq_Geach :
    Hilbert.KB4  = Hilbert.Geach {⟨0, 1, 0, 1⟩, ⟨0, 2, 1, 0⟩} := by aesop;

-- @@ L41-42 verbatim
lemma _root_.LO.Modal.Hilbert.KB5.eq_Geach :
    Hilbert.KB5  = Hilbert.Geach {⟨0, 1, 0, 1⟩, ⟨1, 1, 0, 1⟩} := by aesop;

-- @@ L43-44 verbatim
lemma _root_.LO.Modal.Hilbert.KD.eq_Geach :
    Hilbert.KD   = Hilbert.Geach {⟨0, 0, 1, 1⟩} := by aesop;

-- @@ L45-46 verbatim
lemma _root_.LO.Modal.Hilbert.KD4.eq_Geach :
    Hilbert.KD4  = Hilbert.Geach {⟨0, 0, 1, 1⟩, ⟨0, 2, 1, 0⟩} := by aesop;

-- @@ L47-48 verbatim
lemma _root_.LO.Modal.Hilbert.KD45.eq_Geach :
    Hilbert.KD45 = Hilbert.Geach {⟨0, 0, 1, 1⟩, ⟨0, 2, 1, 0⟩, ⟨1, 1, 0, 1⟩} := by aesop;

-- @@ L49-50 verbatim
lemma _root_.LO.Modal.Hilbert.KD5.eq_Geach :
    Hilbert.KD5  = Hilbert.Geach {⟨0, 0, 1, 1⟩, ⟨1, 1, 0, 1⟩} := by aesop;

-- @@ L51-52 verbatim
lemma _root_.LO.Modal.Hilbert.KDB.eq_Geach :
    Hilbert.KDB  = Hilbert.Geach {⟨0, 0, 1, 1⟩, ⟨0, 1, 0, 1⟩} := by aesop;

-- @@ L53-54 verbatim
lemma _root_.LO.Modal.Hilbert.KT.eq_Geach :
    Hilbert.KT   = Hilbert.Geach {⟨0, 0, 1, 0⟩} := by aesop;

-- @@ L55-56 verbatim
lemma _root_.LO.Modal.Hilbert.KTB.eq_Geach :
    Hilbert.KTB  = Hilbert.Geach {⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 1⟩} := by aesop;

-- @@ L57-58 verbatim
lemma _root_.LO.Modal.Hilbert.S4.eq_Geach :
    Hilbert.S4   = Hilbert.Geach {⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩} := by aesop;

-- @@ L59-60 verbatim
lemma _root_.LO.Modal.Hilbert.S5.eq_Geach :
    Hilbert.S5   = Hilbert.Geach {⟨0, 0, 1, 0⟩, ⟨1, 1, 0, 1⟩} := by aesop;


-- @@ L62-63 verbatim
lemma _root_.LO.Modal.Hilbert.KT4B.eq_Geach :
    Hilbert.KT4B = Hilbert.Geach {⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨0, 1, 0, 1⟩} := by aesop;


-- @@ L65-66 verbatim
lemma _root_.LO.Modal.Hilbert.S4Dot2.eq_Geach :
    Hilbert.S4Dot2 = Hilbert.Geach {⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨1, 1, 1, 1⟩} := by aesop;

-- @@ L67-68 verbatim
lemma _root_.LO.Modal.Hilbert.Triv.eq_Geach :
    Hilbert.Triv = Hilbert.Geach {⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 0⟩} := by aesop;


-- @@ L70-78 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
@[reducible]
def HasTOfMem0010 (h : ⟨0, 0, 1, 0⟩ ∈ G) : HasT (Hilbert.Geach G) where
  p := 0
  mem_T := by
    simp only [Set.singleton_union, Set.mem_insert_iff, Formula.imp_inj, Box.box_injective',
      reduceCtorEq, and_self, Set.mem_image, false_or]
    use ⟨0, 0, 1, 0⟩;
    simpa;


-- @@ L80-88 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
@[reducible]
def HasB_of_mem_0_1_0_1 (h : ⟨0, 1, 0, 1⟩ ∈ G) : HasB (Hilbert.Geach G) where
  p := 0
  mem_B := by
    simp only [Set.singleton_union, Set.mem_insert_iff, Formula.imp_inj, reduceCtorEq, and_self,
      Set.mem_image, false_or]
    use ⟨0, 1, 0, 1⟩;
    simpa;


-- @@ L90-98 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
@[reducible]
def HasD_of_mem_0_0_1_1 (h : ⟨0, 0, 1, 1⟩ ∈ G) : HasD (Hilbert.Geach G) where
  p := 0
  mem_D := by
    simp only [Set.singleton_union, Set.mem_insert_iff, Formula.imp_inj, Box.box_injective',
      reduceCtorEq, false_and, Set.mem_image, false_or]
    use ⟨0, 0, 1, 1⟩;
    simpa;


-- @@ L100-108 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
@[reducible]
def HasFourOfMem0210 (h : ⟨0, 2, 1, 0⟩ ∈ G) : HasFour (Hilbert.Geach G) where
  p := 0
  mem_Four := by
    simp only [Set.singleton_union, Set.mem_insert_iff, Formula.imp_inj, Box.box_injective',
      reduceCtorEq, and_self, Set.mem_image, false_or]
    use ⟨0, 2, 1, 0⟩;
    simpa;


-- @@ L110-118 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
@[reducible]
def HasFive_of_mem_1_1_0_1 (h : ⟨1, 1, 0, 1⟩ ∈ G) : HasFive (Hilbert.Geach G) where
  p := 0
  mem_Five := by
    simp only [Set.singleton_union, Set.mem_insert_iff, Formula.imp_inj, reduceCtorEq, and_self,
      Set.mem_image, false_or]
    use ⟨1, 1, 0, 1⟩;
    simpa;


-- @@ L120-128 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
@[reducible]
def HasDot2_of_mem_1_1_1_1 (h : ⟨1, 1, 1, 1⟩ ∈ G) : HasDot2 (Hilbert.Geach G) where
  p := 0
  mem_Dot2 := by
    simp only [Set.singleton_union, Set.mem_insert_iff, Formula.imp_inj, reduceCtorEq, and_self,
      Set.mem_image, false_or]
    use ⟨1, 1, 1, 1⟩;
    simpa;


-- @@ L130-138 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
@[reducible]
def HasTcOfMem0100 (h : ⟨0, 1, 0, 0⟩ ∈ G) : HasTc (Hilbert.Geach G) where
  p := 0
  mem_Tc := by
    simp only [Set.singleton_union, Set.mem_insert_iff, Formula.imp_inj, reduceCtorEq, and_self,
      Set.mem_image, false_or]
    use ⟨0, 1, 0, 0⟩;
    simpa;


-- @@ L140-140 verbatim
end Hilbert


-- @@ L142-142 verbatim
end Modal

-- @@ L143-143 verbatim
end LO
