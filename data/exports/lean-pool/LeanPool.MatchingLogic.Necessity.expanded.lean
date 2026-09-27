/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
Written by the coordinating session: adversarial check on Lemma 9 (2026-08-25).

A mechanized lemma is worth only what it forbids.  `locality` carries a
backward-closure hypothesis; if the conclusion held without it, our encoding of
the pointwise extension would be too weak and the mechanization would be
vacuous where it matters.  This file exhibits a model, a set `C` that is NOT
backward closed, and two valuations satisfying `AgreeOn C` whose denotations
differ on `C`.  So the hypothesis is load-bearing.

The example is the smallest one that works: `M \ C` must have two points, since
`AgreeOn` forces the two valuations to agree whenever their common value lies
in `C`, and a one-point complement leaves them equal.
-/
module

public import LeanPool.MatchingLogic.Locality
import Mathlib.Data.Set.Insert


-- @@ L26-28 verbatim
/-!
# MatchingLogic.Necessity
-/


-- @@ L30-30 verbatim
@[expose] public section


-- @@ L32-32 verbatim
namespace MatchingLogic

-- @@ L33-33 verbatim
namespace Necessity


-- @@ L35-36 verbatim
/-- One unary symbol. -/
abbrev S : Signature := ⟨Unit, fun _ => 1⟩


-- @@ L38-44 verbatim
/-- Carrier `{0,1,2}`; the symbol sends `1` to `0` and everything else nowhere.
Since `0 ∈ σ_M(1)`, the backward step of Definition 2 runs from the output to the
argument: `0 ⇝ 1`.  So backward closure of `{0}` would force `1 ∈ {0}`. -/
abbrev M : Model S :=
  { carrier := Fin 3
    nonempty := ⟨0⟩
    interp := fun _ a => if a 0 = 1 then ({0} : Set (Fin 3)) else ∅ }


-- @@ L46-47 verbatim
/-- The set `{0}`, which is not backward closed. -/
abbrev C : Set (Fin 3) := {0}


-- @@ L49-52 verbatim
theorem C_not_backwardClosed : ¬ M.BackwardClosed C := by
  intro h
  have h1 : (1 : Fin 3) ∈ C := h (show (0 : Fin 3) ∈ C from rfl) ⟨(), fun _ => 1, 0, by simp, rfl⟩
  exact absurd h1 (by decide)


-- @@ L54-57 verbatim
/-! The countermodel is stated for an arbitrary variable type, then instantiated
both at `Unit` and at `ℕ`.  The `ℕ` instance is the paper's setting, where the
element variables are countably infinite, so this refutes the hypothesis-free
statement in the paper's own domain and not merely in a degenerate one. -/


-- @@ L59-59 verbatim
section Generic


-- @@ L61-61 verbatim
variable {Var : Type} [DecidableEq Var]


-- @@ L63-64 verbatim
/-- `σ(x)` for a chosen variable `x`. -/
def psi (x : Var) : Pattern S Var := .app () (fun _ => .var x)


-- @@ L66-67 verbatim
/-- Both valuations send every variable outside `C`, so they satisfy `AgreeOn`. -/
def rho : Var → Fin 3 := fun _ => 1

-- @@ L68-69 verbatim
/-- The second constant valuation used by the agreement counterexample. -/
def rho' : Var → Fin 3 := fun _ => 2


-- @@ L71-74 verbatim
omit [DecidableEq Var] in
theorem agree : AgreeOn (M := M) C (rho (Var := Var)) rho' := by
  intro _
  refine Or.inr ⟨?_, ?_⟩ <;> simp [rho, rho']


-- @@ L76-84 verbatim
theorem denote_rho (x : Var) : M.denote (rho (Var := Var)) (psi x) = {0} := by
  ext u
  simp only [psi, denote_app, Model.app, denote_var, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a, ha, hu⟩
    have h0 : a 0 = 1 := ha 0
    simpa [h0] using hu
  · intro hu
    exact ⟨fun _ => 1, fun _ => rfl, by simpa using hu⟩


-- @@ L86-92 verbatim
theorem denote_rho' (x : Var) : M.denote (rho' (Var := Var)) (psi x) = ∅ := by
  ext u
  simp only [psi, denote_app, Model.app, denote_var, Set.mem_ofPred_eq,
    Set.mem_empty_iff_false, iff_false]
  rintro ⟨a, ha, hu⟩
  have h0 : a 0 = 2 := ha 0
  simp [h0] at hu


-- @@ L94-105 verbatim
/-- **The hypothesis of Lemma 9 cannot be dropped**, for any variable type that
has at least one variable.  Without backward closure the conclusion fails, on a
three-element model. -/
theorem locality_needs_backwardClosed (x : Var) :
    ¬ (∀ (ψ : Pattern S Var) (ρ ρ' : Var → Fin 3),
        AgreeOn (M := M) C ρ ρ' → M.denote ρ ψ ∩ C = M.denote ρ' ψ ∩ C) := by
  intro h
  have hd := h (psi x) rho rho' agree
  rw [denote_rho, denote_rho'] at hd
  have h0 : (0 : Fin 3) ∈ ({0} : Set (Fin 3)) ∩ C := ⟨rfl, rfl⟩
  rw [hd] at h0
  exact h0.1


-- @@ L107-107 verbatim
end Generic


-- @@ L109-113 verbatim
/-- The paper's setting: countably infinite element variables. -/
theorem locality_needs_backwardClosed_nat :
    ¬ (∀ (ψ : Pattern S Nat) (ρ ρ' : Nat → Fin 3),
        AgreeOn (M := M) C ρ ρ' → M.denote ρ ψ ∩ C = M.denote ρ' ψ ∩ C) :=
  locality_needs_backwardClosed 0


-- @@ L115-115 verbatim
end Necessity

-- @@ L116-116 verbatim
end MatchingLogic
