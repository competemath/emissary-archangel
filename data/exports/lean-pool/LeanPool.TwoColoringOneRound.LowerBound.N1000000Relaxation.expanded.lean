/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import LeanPool.TwoColoringOneRound.LowerBound.Correlation
public import LeanPool.TwoColoringOneRound.LowerBound.N1000000Witness
public import LeanPool.TwoColoringOneRound.LowerBound.N1000000WeakDuality
import Mathlib.Tactic.Positivity.Finset


-- @@ L13-15 verbatim
/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000Relaxation
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
namespace Distributed2Coloring.LowerBound


-- @@ L21-21 verbatim
namespace N1000000Relaxation


-- @@ L23-23 verbatim
open scoped BigOperators


-- @@ L25-25 verbatim
open Distributed2Coloring.LowerBound.Correlation

-- @@ L26-26 verbatim
open Distributed2Coloring.LowerBound.N1000000Data

-- @@ L27-27 verbatim
open Distributed2Coloring.LowerBound.N1000000Witness

-- @@ L28-28 verbatim
open Distributed2Coloring.LowerBound.N1000000WeakDuality


-- @@ L30-31 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev n : Nat := N1000000Data.n

-- @@ L32-33 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev SymN := Distributed2Coloring.LowerBound.Sym n

-- @@ L34-35 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev G := Correlation.G n

-- @@ L36-37 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Q := ℚ

-- @@ L38-39 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Var := N1000000WeakDuality.Var


-- @@ L41-41 verbatim
noncomputable instance : Fintype G := by infer_instance


-- @@ L43-44 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev LabelTriple := N1000000Witness.LabelTriple


-- @@ L46-48 verbatim
instance : NeZero n := ⟨by
  -- `n = 10^6`.
  decide⟩


-- @@ L50-52 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def symOfNat (k : Nat) : SymN :=
  Fin.ofNat n k


-- @@ L54-58 verbatim
lemma symOfNat_injective_of_lt {a b : Nat} (ha : a < n) (hb : b < n) :
    symOfNat a = symOfNat b → a = b := by
  intro hab
  have hval : a % n = b % n := by simpa [symOfNat] using congrArg Fin.val hab
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hval


-- @@ L60-65 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def labelGet (t : LabelTriple) (i : Fin 3) : SymN :=
  match i.1 with
  | 0 => symOfNat t.1
  | 1 => symOfNat t.2.1
  | _ => symOfNat t.2.2


-- @@ L67-69 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def tupleOfLabels (t : LabelTriple) : Tuple 3 n :=
  fun i => labelGet t i


-- @@ L71-76 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def labelGetNat (t : LabelTriple) (i : Fin 3) : Nat :=
  match i.1 with
  | 0 => t.1
  | 1 => t.2.1
  | _ => t.2.2


-- @@ L78-80 verbatim
lemma labelGet_eq_symOfNat_labelGetNat (t : LabelTriple) (i : Fin 3) :
    labelGet t i = symOfNat (labelGetNat t i) := by
  fin_cases i <;> rfl


-- @@ L82-84 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def LabelsDistinct (t : LabelTriple) : Prop :=
  t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2


-- @@ L86-88 verbatim
instance (t : LabelTriple) : Decidable (LabelsDistinct t) := by
  unfold LabelsDistinct
  infer_instance


-- @@ L90-92 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def LabelsInRange (t : LabelTriple) : Prop :=
  t.1 < n ∧ t.2.1 < n ∧ t.2.2 < n


-- @@ L94-96 verbatim
instance (t : LabelTriple) : Decidable (LabelsInRange t) := by
  unfold LabelsInRange
  infer_instance


-- @@ L98-103 verbatim
lemma labelGetNat_lt (t : LabelTriple) (hr : LabelsInRange (t := t)) (i : Fin 3) :
    labelGetNat t i < n := by
  fin_cases i
  · simpa [labelGetNat] using hr.1
  · simpa [labelGetNat] using hr.2.1
  · simpa [labelGetNat] using hr.2.2


-- @@ L105-110 verbatim
lemma labelGetNat_injective_of_labelsDistinct (t : LabelTriple) (h : LabelsDistinct t) :
    Function.Injective (labelGetNat t) := by
  intro i j hij
  obtain ⟨h1, h2, h3⟩ := h
  fin_cases i <;> fin_cases j <;>
    simp_all [labelGetNat, eq_comm]


-- @@ L112-119 verbatim
lemma tupleOfLabels_injective_of_labelsDistinct (t : LabelTriple) (h : LabelsDistinct t)
    (hr : LabelsInRange (t := t)) :
    Function.Injective (tupleOfLabels t) := by
  intro i j hij
  have hijSym : symOfNat (labelGetNat t i) = symOfNat (labelGetNat t j) := by
    simpa [tupleOfLabels, labelGet_eq_symOfNat_labelGetNat] using hij
  exact labelGetNat_injective_of_labelsDistinct (t := t) h
    (symOfNat_injective_of_lt (labelGetNat_lt (t := t) hr i) (labelGetNat_lt (t := t) hr j) hijSym)


-- @@ L121-123 verbatim
theorem varRepU_injective : ∀ i : Var, Function.Injective (tupleOfLabels (varRepU[i.1]!)) := by
  intro i
  fin_cases i <;> exact tupleOfLabels_injective_of_labelsDistinct _ (by decide) (by decide)


-- @@ L125-127 verbatim
theorem varRepV_injective : ∀ i : Var, Function.Injective (tupleOfLabels (varRepV[i.1]!)) := by
  intro i
  fin_cases i <;> exact tupleOfLabels_injective_of_labelsDistinct _ (by decide) (by decide)


-- @@ L129-131 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev varRepUAt (i : Var) : LabelTriple :=
  varRepU[i.1]!


-- @@ L133-135 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev varRepVAt (i : Var) : LabelTriple :=
  varRepV[i.1]!


-- @@ L137-138 verbatim
theorem varRepUAt_labelsDistinct (i : Var) : LabelsDistinct (varRepUAt i) := by
  fin_cases i <;> decide


-- @@ L140-141 verbatim
theorem varRepVAt_labelsDistinct (i : Var) : LabelsDistinct (varRepVAt i) := by
  fin_cases i <;> decide


-- @@ L143-143 verbatim
theorem varRepUAt_labelsInRange (i : Var) : LabelsInRange (varRepUAt i) := by fin_cases i <;> decide


-- @@ L145-145 verbatim
theorem varRepVAt_labelsInRange (i : Var) : LabelsInRange (varRepVAt i) := by fin_cases i <;> decide


-- @@ L147-149 verbatim
theorem varRepUAt_injective : ∀ i : Var, Function.Injective (tupleOfLabels (varRepUAt i)) := by
  intro i
  fin_cases i <;> exact tupleOfLabels_injective_of_labelsDistinct _ (by decide) (by decide)


-- @@ L151-153 verbatim
theorem varRepVAt_injective : ∀ i : Var, Function.Injective (tupleOfLabels (varRepVAt i)) := by
  intro i
  fin_cases i <;> exact tupleOfLabels_injective_of_labelsDistinct _ (by decide) (by decide)


-- @@ L155-157 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def varRepVertexU (i : Var) : Vertex n :=
  ⟨tupleOfLabels (varRepUAt i), varRepUAt_injective i⟩


-- @@ L159-161 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def varRepVertexV (i : Var) : Vertex n :=
  ⟨tupleOfLabels (varRepVAt i), varRepVAt_injective i⟩


-- @@ L163-165 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def xFromColoring (f : Coloring n) : Var → Q :=
  fun i => corrAvg (n := n) f (varRepVertexU i) (varRepVertexV i)


-- @@ L167-171 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def edgeVarVar : Var :=
  ⟨edgeVar, by decide⟩

-- A concrete representative edge `((3,0,1) -> (0,1,2))`, encoded as a 4-tuple `(3,0,1,2)`.

-- @@ L172-179 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def edgeRepTuple : Tuple 4 n :=
  fun i =>
    match i.1 with
    | 0 => symOfNat 3
    | 1 => symOfNat 0
    | 2 => symOfNat 1
    | _ => symOfNat 2


-- @@ L181-190 verbatim
lemma edgeRepTuple_injective : Function.Injective edgeRepTuple := by
  intro i j hij
  have hmod0 : (0 : Nat) % n = 0 := Nat.mod_eq_of_lt (by decide : (0 : Nat) < n)
  have hmod1 : (1 : Nat) % n = 1 := Nat.mod_eq_of_lt (by decide : (1 : Nat) < n)
  have hmod2 : (2 : Nat) % n = 2 := Nat.mod_eq_of_lt (by decide : (2 : Nat) < n)
  have hmod3 : (3 : Nat) % n = 3 := Nat.mod_eq_of_lt (by decide : (3 : Nat) < n)
  fin_cases i <;> fin_cases j <;> first
    | rfl
    | (exact absurd (congrArg Fin.val hij)
        (by simp [edgeRepTuple, symOfNat, hmod0, hmod1, hmod2, hmod3]))


-- @@ L192-194 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def edgeRep : Edge n :=
  ⟨edgeRepTuple, edgeRepTuple_injective⟩


-- @@ L196-203 verbatim
theorem edgeRep_src : Edge.src edgeRep = varRepVertexV edgeVarVar := by
  have hV : varRepVAt edgeVarVar = (3, 0, 1) := by decide
  apply Subtype.ext
  funext i
  fin_cases i <;>
    simp [Edge.src, Edge.srcIndex, edgeRep, edgeRepTuple, varRepVertexV, varRepVAt, tupleOfLabels,
      Distributed2Coloring.LowerBound.N1000000Relaxation.labelGet,
      Distributed2Coloring.LowerBound.N1000000Relaxation.symOfNat, hV]


-- @@ L205-212 verbatim
theorem edgeRep_dst : Edge.dst edgeRep = varRepVertexU edgeVarVar := by
  have hU : varRepUAt edgeVarVar = (0, 1, 2) := by decide
  apply Subtype.ext
  funext i
  fin_cases i <;>
    simp [Edge.dst, Edge.dstIndex, edgeRep, edgeRepTuple, varRepVertexU, varRepUAt, tupleOfLabels,
      Distributed2Coloring.LowerBound.N1000000Relaxation.labelGet,
      Distributed2Coloring.LowerBound.N1000000Relaxation.symOfNat, hU]


-- @@ L214-222 verbatim
/-!
This file currently defines the reduced orbit variables `xFromColoring` and the concrete edge
representative `edgeRep`.  The remaining objective link

`xEdge (xFromColoring f) = edgeCorrelation f`

is deferred to a separate module (it uses orbit-stabilizer / pretransitivity for the action of
`Sym(n)` on `Edge n`).
-/


-- @@ L224-224 verbatim
end N1000000Relaxation


-- @@ L226-226 verbatim
end Distributed2Coloring.LowerBound
