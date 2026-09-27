/-
Copyright (c) 2026 Elan Roth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elan Roth
-/
module

public import Mathlib.Algebra.Module.ZMod
public import LeanPool.UlmsTheorem.PGroups.UlmSubgroups


-- @@ L11-15 verbatim
/-!
# Socle-level constructions

This file contains the p-socle and its interaction with the Ulm filtration.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
namespace UlmsTheorem


-- @@ L21-21 verbatim
open Ordinal


-- @@ L23-23 verbatim
variable (p : ℕ)


-- @@ L25-36 verbatim
/-- The `p`-socle `P = {x | p • x = 0}`. -/
def pSocle {G : Type*} [AddCommGroup G] : AddSubgroup G where
  carrier   := {x | p • x = 0}
  zero_mem' := by simp
  add_mem'  := by
    rintro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [smul_add, ha, hb, add_zero]
  neg_mem'  := by
    rintro a ha
    simp only [Set.mem_ofPred_eq] at *
    rw [smul_neg, ha, neg_zero]


-- @@ L38-38 verbatim
section SocleLemmas


-- @@ L40-40 verbatim
variable {G : Type*} [AddCommGroup G]


-- @@ L42-42 verbatim
@[simp] lemma mem_pSocle (x : G) : x ∈ pSocle p (G := G) ↔ p • x = 0 := Iff.rfl


-- @@ L44-46 verbatim
/-- The filtered socle `P_α = P ∩ G_α`. -/
noncomputable def pSocleAt (α : Ordinal) : AddSubgroup G :=
  pSocle p ⊓ ulmSubgroup p α


-- @@ L48-49 verbatim
@[simp] lemma mem_pSocleAt (α : Ordinal) (x : G) :
    x ∈ pSocleAt p α (G := G) ↔ p • x = 0 ∧ x ∈ ulmSubgroup p α := Iff.rfl


-- @@ L51-52 verbatim
lemma pSocleAt_zero : pSocleAt p (0 : Ordinal) (G := G) = pSocle p := by
  simp [pSocleAt, ulmSubgroup_zero]


-- @@ L54-55 verbatim
lemma pSocleAt_antitone : Antitone (fun α ↦ pSocleAt p α (G := G)) := fun _ _ h ↦
  inf_le_inf_left _ (ulmSubgroup_antitone p h)


-- @@ L57-59 verbatim
lemma pSocleAt_succ_le (α : Ordinal) :
    pSocleAt p (Order.succ α) (G := G) ≤ pSocleAt p α :=
  pSocleAt_antitone p (Order.le_succ α)


-- @@ L61-63 verbatim
lemma pSocleAt_le_pSocle (α : Ordinal) :
    pSocleAt p α (G := G) ≤ pSocle p :=
  inf_le_left


-- @@ L65-71 verbatim
noncomputable instance pSocleZModModule :
    Module (ZMod p) (pSocle p (G := G)) := by
  classical
  refine AddCommGroup.zmodModule (n := p) (G := pSocle p (G := G)) ?_
  intro x
  apply Subtype.ext
  exact x.property


-- @@ L73-80 verbatim
noncomputable instance pSocleAtZModModule (α : Ordinal) :
    Module (ZMod p) (pSocleAt p α (G := G)) := by
  classical
  refine AddCommGroup.zmodModule (n := p) (G := pSocleAt p α (G := G)) ?_
  intro x
  have hx : p • (x : G) = 0 := (mem_pSocleAt p α (x : G)).1 x.property |>.1
  ext
  simp [hx]


-- @@ L82-86 verbatim
/-- `P_{α+1}` viewed as a subgroup of `P_α`. -/
noncomputable def pSocleAtSuccSubgroupOf (α : Ordinal) :
    AddSubgroup (pSocleAt p α (G := G)) :=
  (pSocleAt p (Order.succ α) (G := G)).comap
    (AddSubgroup.subtype (pSocleAt p α))


-- @@ L88-98 verbatim
noncomputable instance pSocleAtQuotModule (α : Ordinal) :
    Module (ZMod p) ((pSocleAt p α (G := G)) ⧸ pSocleAtSuccSubgroupOf p α) := by
  classical
  refine QuotientAddGroup.zmodModule (n := p)
    (G := pSocleAt p α (G := G)) (H := pSocleAtSuccSubgroupOf p α) ?_
  intro x
  have hx' : p • (x : G) = 0 := (mem_pSocleAt p α (x : G)).1 x.property |>.1
  have hx : p • x = 0 := by
    ext
    simp [hx']
  simp [hx]


-- @@ L100-100 verbatim
end SocleLemmas


-- @@ L102-102 verbatim
end UlmsTheorem
