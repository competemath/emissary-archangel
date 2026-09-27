/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Rat.Init
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Finset

-- @@ L20-22 verbatim
/-!
# LeanPool.TwoColoringOneRound.LowerBound.Defs
-/


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-26 verbatim
namespace Distributed2Coloring.LowerBound


-- @@ L28-28 verbatim
open scoped BigOperators


-- @@ L30-31 verbatim
/-- Symbols. -/
abbrev Sym (n : Nat) := Fin n


-- @@ L33-34 verbatim
/-- Ordered `k`-tuples of symbols. -/
abbrev Tuple (k n : Nat) := Fin k → Sym n


-- @@ L36-37 verbatim
/-- Vertices are injective triples of symbols. -/
abbrev Vertex (n : Nat) := { v : Tuple 3 n // Function.Injective v }


-- @@ L39-40 verbatim
/-- Edges are injective quadruples of symbols, encoding `(a,b,c) → (b,c,d)`. -/
abbrev Edge (n : Nat) := { e : Tuple 4 n // Function.Injective e }


-- @@ L42-42 verbatim
namespace Vertex


-- @@ L44-45 verbatim
/-- First coordinate `a` of a vertex `(a,b,c)`. -/
def a {n : Nat} (v : Vertex n) : Sym n := v.1 ⟨0, by decide⟩

-- @@ L46-47 verbatim
/-- Second coordinate `b` of a vertex `(a,b,c)`. -/
def b {n : Nat} (v : Vertex n) : Sym n := v.1 ⟨1, by decide⟩

-- @@ L48-49 verbatim
/-- Third coordinate `c` of a vertex `(a,b,c)`. -/
def c {n : Nat} (v : Vertex n) : Sym n := v.1 ⟨2, by decide⟩


-- @@ L51-51 verbatim
end Vertex


-- @@ L53-53 verbatim
namespace Edge


-- @@ L55-57 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def srcIndex (i : Fin 3) : Fin 4 :=
  ⟨i.1, Nat.lt_trans i.2 (by decide)⟩


-- @@ L59-61 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def dstIndex (i : Fin 3) : Fin 4 :=
  ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩


-- @@ L63-65 verbatim
@[simp] lemma srcIndex_zero : srcIndex (0 : Fin 3) = (0 : Fin 4) := by
  ext
  rfl


-- @@ L67-69 verbatim
@[simp] lemma srcIndex_one : srcIndex (1 : Fin 3) = (1 : Fin 4) := by
  ext
  rfl


-- @@ L71-73 verbatim
@[simp] lemma srcIndex_two : srcIndex (2 : Fin 3) = (2 : Fin 4) := by
  ext
  rfl


-- @@ L75-77 verbatim
@[simp] lemma dstIndex_zero : dstIndex (0 : Fin 3) = (1 : Fin 4) := by
  ext
  rfl


-- @@ L79-81 verbatim
@[simp] lemma dstIndex_one : dstIndex (1 : Fin 3) = (2 : Fin 4) := by
  ext
  rfl


-- @@ L83-85 verbatim
@[simp] lemma dstIndex_two : dstIndex (2 : Fin 3) = (3 : Fin 4) := by
  ext
  rfl


-- @@ L87-93 verbatim
/-- Source vertex of an edge `(a,b,c,d)`, i.e. `(a,b,c)`. -/
def src {n : Nat} (e : Edge n) : Vertex n :=
  ⟨fun i => e.1 (srcIndex i), by
    intro i j hij
    have h4 : srcIndex i = srcIndex j := e.2 hij
    apply Fin.ext
    simpa [srcIndex] using congrArg Fin.val h4⟩


-- @@ L95-102 verbatim
/-- Target vertex of an edge `(a,b,c,d)`, i.e. `(b,c,d)`. -/
def dst {n : Nat} (e : Edge n) : Vertex n :=
  ⟨fun i => e.1 (dstIndex i), by
    intro i j hij
    have h4 : dstIndex i = dstIndex j := e.2 hij
    apply Fin.ext
    have hval : (i.1 + 1) = (j.1 + 1) := by simpa [dstIndex] using congrArg Fin.val h4
    exact Nat.succ.inj hval⟩


-- @@ L104-106 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def monochromatic {n : Nat} (f : Vertex n → Bool) (e : Edge n) : Prop :=
  f (src e) = f (dst e)


-- @@ L108-110 verbatim
instance {n : Nat} (f : Vertex n → Bool) (e : Edge n) : Decidable (monochromatic f e) := by
  dsimp [monochromatic]
  infer_instance


-- @@ L112-112 verbatim
end Edge


-- @@ L114-115 verbatim
/-- A `2`-coloring of the vertices. -/
abbrev Coloring (n : Nat) := Vertex n → Bool


-- @@ L117-118 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def edgeCount (n : Nat) : Nat := Fintype.card (Edge n)


-- @@ L120-122 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def monoEdges {n : Nat} (f : Coloring n) : Finset (Edge n) :=
  (Finset.univ : Finset (Edge n)).filter (Edge.monochromatic f)


-- @@ L124-126 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def monoCount {n : Nat} (f : Coloring n) : Nat :=
  (monoEdges f).card


-- @@ L128-130 verbatim
/-- Fraction of monochromatic directed edges under `f`. -/
def monoFraction {n : Nat} (f : Coloring n) : ℚ :=
  (monoCount f : ℚ) / (edgeCount n : ℚ)


-- @@ L132-134 verbatim
/-- Convert a coloring to a sign labeling `±1`. -/
def signOfColoring {n : Nat} (f : Coloring n) : Vertex n → Int :=
  fun v => if f v then (-1) else (1)


-- @@ L136-139 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def edgeCorrSum {n : Nat} (f : Coloring n) : Int :=
  (Finset.univ : Finset (Edge n)).sum fun e =>
    (signOfColoring f (Edge.src e)) * (signOfColoring f (Edge.dst e))


-- @@ L141-143 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def edgeCorrelation {n : Nat} (f : Coloring n) : ℚ :=
  (edgeCorrSum f : ℚ) / (edgeCount n : ℚ)


-- @@ L145-148 verbatim
lemma signOfColoring_sq {n : Nat} (f : Coloring n) (v : Vertex n) :
    (signOfColoring f v) * (signOfColoring f v) = 1 := by
  unfold signOfColoring
  by_cases h : f v <;> simp [h]


-- @@ L150-155 verbatim
/-- On an edge, being monochromatic is equivalent to having product `+1` in `±1`. -/
lemma mono_iff_sign_mul_eq_one {n : Nat} (f : Coloring n) (e : Edge n) :
    Edge.monochromatic f e ↔
      (signOfColoring f (Edge.src e)) * (signOfColoring f (Edge.dst e)) = 1 := by
  unfold Edge.monochromatic signOfColoring
  by_cases hs : f (Edge.src e) <;> by_cases ht : f (Edge.dst e) <;> simp [hs, ht]


-- @@ L157-161 verbatim
lemma monoIndicator_eq_one_add_sign_mul_div_two {n : Nat} (f : Coloring n) (e : Edge n) :
    (if Edge.monochromatic f e then (1 : ℚ) else 0)
      = ((1 : ℚ) + (signOfColoring f (Edge.src e) * signOfColoring f (Edge.dst e) : Int)) / 2 := by
  unfold Edge.monochromatic signOfColoring
  by_cases hs : f (Edge.src e) <;> by_cases ht : f (Edge.dst e) <;> simp [hs, ht]


-- @@ L163-206 verbatim
lemma monoFraction_eq_one_add_edgeCorrelation_div_two {n : Nat} (f : Coloring n)
    (hE : edgeCount n ≠ 0) :
    monoFraction f = ((1 : ℚ) + edgeCorrelation f) / 2 := by
  classical
  have hE' : (edgeCount n : ℚ) ≠ 0 := by exact_mod_cast hE
  let z : Edge n → ℚ := fun e =>
    ((signOfColoring f (Edge.src e) * signOfColoring f (Edge.dst e) : Int) : ℚ)
  -- Express `monoCount` as a sum of indicators using `Finset.sum_boole`.
  have hcount :
      (monoCount f : ℚ)
        = (Finset.univ : Finset (Edge n)).sum (fun e =>
            if Edge.monochromatic f e then (1 : ℚ) else 0) := by
    simp [monoCount, monoEdges]
  -- Rewrite each indicator as `(1 + sign_mul)/2` and sum.
  calc
    monoFraction f
        = (monoCount f : ℚ) / (edgeCount n : ℚ) := by rfl
    _ = ((Finset.univ : Finset (Edge n)).sum (fun e =>
          if Edge.monochromatic f e then (1 : ℚ) else 0)) / (edgeCount n : ℚ) := by
          simp [hcount]
    _ = ((Finset.univ : Finset (Edge n)).sum (fun e =>
          ((1 : ℚ) + z e) / 2))
          / (edgeCount n : ℚ) := by
          refine congrArg (fun z => z / (edgeCount n : ℚ)) ?_
          refine Finset.sum_congr rfl ?_
          intro e _
          simpa [z] using (monoIndicator_eq_one_add_sign_mul_div_two (n := n) f e)
    _ = ((((Finset.univ : Finset (Edge n)).sum (fun _e => (1 : ℚ))
            + (Finset.univ : Finset (Edge n)).sum z) / 2))
          / (edgeCount n : ℚ) := by
          -- Linearity: pull out the factor `1/2`, then distribute the sum across addition.
          have hlin :
              (Finset.univ : Finset (Edge n)).sum (fun e => ((1 : ℚ) + z e) / 2)
                = ((Finset.univ : Finset (Edge n)).sum (fun e => (1 : ℚ) + z e)) / 2 := by
            -- `x/2 = x * (2⁻¹)`, and `sum` commutes with right multiplication by a constant.
            simp [div_eq_mul_inv, Finset.sum_mul]
          -- Now distribute the sum across addition.
          simp [hlin, Finset.sum_add_distrib]
    _ = (((edgeCount n : ℚ) + (edgeCorrSum f : ℚ)) / 2) / (edgeCount n : ℚ) := by
          simp [edgeCount, edgeCorrSum, z]
    _ = ((1 : ℚ) + (edgeCorrSum f : ℚ) / (edgeCount n : ℚ)) / 2 := by
          -- algebra in a field; requires `edgeCount n ≠ 0`
          field_simp [hE', add_comm, add_left_comm, add_assoc, mul_add, add_mul]
    _ = ((1 : ℚ) + edgeCorrelation f) / 2 := by simp [edgeCorrelation]


-- @@ L208-208 verbatim
end Distributed2Coloring.LowerBound
