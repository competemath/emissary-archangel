/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
Finite variable support and canonical fresh names for entry point (iii).

Unlike `FV`, `allVars` records bound names too.  Freshness from `allVars` is
the side condition needed when making the paper's implicit alpha-renaming
steps explicit over the raw named syntax of the verified base.
-/
module

public import LeanPool.MatchingLogic.Semantics
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Basic


-- @@ L21-23 verbatim
/-!
# MatchingLogic.EntryIII.Fresh
-/


-- @@ L25-25 verbatim
@[expose] public section


-- @@ L27-27 verbatim
namespace MatchingLogic


-- @@ L29-29 verbatim
variable {S : Signature} {Var : Type} [DecidableEq Var]


-- @@ L31-31 verbatim
namespace Pattern


-- @@ L33-39 verbatim
/-- The finite set of every free or bound variable name occurring in a pattern. -/
def allVars : Pattern S Var → Finset Var
  | .var x => {x}
  | .bot => ∅
  | .app _ args => Finset.univ.biUnion (fun i => (args i).allVars)
  | .imp phi psi => phi.allVars ∪ psi.allVars
  | .ex x phi => insert x phi.allVars


-- @@ L41-58 verbatim
/-- Every free variable occurs in the finite set of all variable names. -/
theorem FV_subset_allVars (p : Pattern S Var) : FV p ⊆ ↑p.allVars := by
  induction p with
  | var x => simp [allVars]
  | bot => simp [allVars]
  | app sigma args ih =>
      intro x hx
      simp only [FV_app, Set.mem_iUnion] at hx
      rcases hx with ⟨i, hi⟩
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, ih i hi⟩
  | imp phi psi ihphi ihpsi =>
      intro x hx
      rcases hx with hx | hx
      · exact Finset.mem_union_left _ (ihphi hx)
      · exact Finset.mem_union_right _ (ihpsi hx)
  | ex x phi ih =>
      intro y hy
      exact Finset.mem_insert_of_mem (ih hy.1)


-- @@ L60-62 verbatim
/-- A canonical natural-number variable not occurring anywhere in a pattern. -/
def fresh (p : Pattern S Nat) : Nat :=
  (insert 0 p.allVars).max' (Finset.insert_nonempty 0 p.allVars) + 1


-- @@ L64-70 verbatim
/-- The canonical fresh name does not occur free or bound. -/
theorem fresh_not_mem_allVars (p : Pattern S Nat) : p.fresh ∉ p.allVars := by
  intro hmem
  have hle := (insert 0 p.allVars).le_max' p.fresh
    (Finset.mem_insert_of_mem hmem)
  unfold fresh at hle
  omega


-- @@ L72-75 verbatim
/-- In particular, the canonical fresh name is not free. -/
theorem fresh_not_mem_FV (p : Pattern S Nat) : p.fresh ∉ FV p := by
  intro hmem
  exact p.fresh_not_mem_allVars (p.FV_subset_allVars hmem)


-- @@ L77-77 verbatim
end Pattern


-- @@ L79-79 verbatim
end MatchingLogic
