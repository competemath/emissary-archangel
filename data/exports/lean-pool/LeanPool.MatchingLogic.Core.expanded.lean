/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
One-sorted basic matching logic — syntax, models, denotation, and backward
closure.

Source: Xiaohong Chen and Grigore Rosu, "Completeness and incompleteness of basic
matching logic", arXiv:2608.13306v1 (13 Aug 2026), Sections 2 and 3.

This file is the pinned interface the rest of the development is built against.
Its definitions were written first, then audited against the paper by independent
readers before any proof was commissioned on them, and their kernel-printed
bodies are pinned by `scripts/audit-pinned.sh`.

Representation rulings (fixed before any proof was written):
* Element variables are NAMED, and there is no syntactic substitution anywhere in
  this file or in the semantic development built on it.  The single exception is
  rule (3) of Figure 2, which needs variable-for-variable substitution;
  `ProofSystem.lean` defines `substVar` there and nowhere else. Lemmas 9 and 11
  are purely semantic: they speak only of valuation update `ρ[a/x]`, never of
  `φ[y/x]`. Capture-avoidance is therefore not needed and de Bruijn indices
  are forbidden -- they would add an entire
  layer of noise the paper's argument never touches.
* Symbol arguments are `Fin (arity σ) → Pattern`, not `List Pattern`.  This keeps
  the inductive non-nested from Lean's point of view and yields a usable
  structural recursor.
* Denotations are `Set M`, i.e. `M → Prop`, classically.
-/
module

public import Aesop.BuiltinRules
public import Mathlib.Order.SetNotation
public import Mathlib.Tactic.ToAdditive
import Mathlib.Data.Set.Lattice.Bounded
import Mathlib.Data.Set.Lattice.Disjoint
import Mathlib.Data.Set.Lattice.Image
import Mathlib.Data.Set.Lattice.Indexed
import Mathlib.Data.Set.Lattice.Order


-- @@ L44-46 verbatim
/-!
# MatchingLogic.Core
-/


-- @@ L48-48 verbatim
@[expose] public section


-- @@ L50-50 verbatim
namespace MatchingLogic


-- @@ L52-52 verbatim
universe u


-- @@ L54-67 verbatim
/-- A one-sorted finitary signature: a set of symbols, each with an arity.
Symbols of arity `0` are constants (paper, Section 2). -/
structure Signature where
  /-- The type of operation symbols. -/
  Sym : Type
  /-- The number of arguments of each operation symbol. -/
  arity : Sym → Nat

/- Note on `Var`.  The paper fixes a countably infinite set of element
variables.  Everything below is stated for an arbitrary `Var : Type` with
decidable equality, which is a generalization: instantiating at `Var := Nat`
gives the paper's setting, so a countermodel in the paper's setting would
refute the Lean statements too. `DecidableEq Var` is bookkeeping for
`Function.update`, not a semantic hypothesis. -/


-- @@ L69-69 verbatim
variable (S : Signature) (Var : Type)


-- @@ L71-78 verbatim
/-- Patterns of basic matching logic: no definedness, no set variables, no
fixpoints (paper, Section 2).  Primitives are implication and `⊥`. -/
inductive Pattern where
  | var : Var → Pattern
  | app : (σ : S.Sym) → (Fin (S.arity σ) → Pattern) → Pattern
  | imp : Pattern → Pattern → Pattern
  | bot : Pattern
  | ex : Var → Pattern → Pattern


-- @@ L80-80 verbatim
namespace Pattern


-- @@ L82-82 verbatim
variable {S Var}


-- @@ L84-85 verbatim
/-- `¬φ := φ → ⊥` -/
abbrev nt (φ : Pattern S Var) : Pattern S Var := imp φ bot

-- @@ L86-87 verbatim
/-- `⊤ := ⊥ → ⊥` -/
abbrev tp : Pattern S Var := imp bot bot

-- @@ L88-89 verbatim
/-- `φ ∨ ψ := ¬φ → ψ` -/
abbrev or (φ ψ : Pattern S Var) : Pattern S Var := imp (nt φ) ψ

-- @@ L90-91 verbatim
/-- `φ ∧ ψ := ¬(φ → ¬ψ)` -/
abbrev and (φ ψ : Pattern S Var) : Pattern S Var := nt (imp φ (nt ψ))

-- @@ L92-93 verbatim
/-- `∀x.φ := ¬∃x.¬φ` -/
abbrev al (x : Var) (φ : Pattern S Var) : Pattern S Var := nt (ex x (nt φ))


-- @@ L95-95 verbatim
end Pattern


-- @@ L97-114 verbatim
/-- A model: a nonempty carrier together with, for each symbol of arity `n`, a
map `Mⁿ → 𝒫(M)` (paper, Section 2). -/
/- NOTE FOR ANYONE BUILDING A CONCRETE MODEL. Declare it as an `abbrev`, not a
`def`. `Model.carrier` is a structure projection at semireducible
transparency, so with a `def` the carrier does not unfold at `instances`
transparency: `Membership` and `Function.update` instances then elaborate at the
underlying type while the ambient set keeps type `Set M.carrier`. The term
still typechecks, but later `rw`s fail with a misleading "did not find an
occurrence of the pattern". Two separate lanes lost time to this before it was
written down. The same applies to valuations: give them a named definition with
an explicit `: Var → M.carrier` ascription rather than writing `fun _ => a`
inline. -/
structure Model (S : Signature) where
  /-- The type of points in the model. -/
  carrier : Type
  nonempty : Nonempty carrier
  /-- The set-valued interpretation of each operation symbol. -/
  interp : (σ : S.Sym) → (Fin (S.arity σ) → carrier) → Set carrier


-- @@ L116-116 verbatim
attribute [instance] Model.nonempty


-- @@ L118-118 verbatim
namespace Model


-- @@ L120-120 verbatim
variable {S : Signature}


-- @@ L122-127 verbatim
/-- The pointwise extension of a symbol to sets:
`σ_M(A₁,…,Aₙ) = ⋃ {σ_M(a₁,…,aₙ) | aᵢ ∈ Aᵢ}`.
It is `∅` as soon as some `Aᵢ` is (paper, Section 2). -/
def app (M : Model S) (σ : S.Sym) (A : Fin (S.arity σ) → Set M.carrier) :
    Set M.carrier :=
  {u | ∃ a : Fin (S.arity σ) → M.carrier, (∀ i, a i ∈ A i) ∧ u ∈ M.interp σ a}


-- @@ L129-136 verbatim
/-- The denotation `ρ(φ) ⊆ M` (paper, Section 2). -/
def denote {Var : Type} [DecidableEq Var] (M : Model S) :
    (Var → M.carrier) → Pattern S Var → Set M.carrier
  | ρ, .var x => {ρ x}
  | _, .bot => ∅
  | ρ, .app σ f => M.app σ (fun i => M.denote ρ (f i))
  | ρ, .imp φ ψ => (M.denote ρ φ)ᶜ ∪ M.denote ρ ψ
  | ρ, .ex x φ => ⋃ a : M.carrier, M.denote (Function.update ρ x a) φ


-- @@ L138-138 verbatim
end Model


-- @@ L140-140 verbatim
section Denote


-- @@ L142-142 verbatim
variable {S : Signature} {Var : Type} [DecidableEq Var] (M : Model S)


-- @@ L144-145 verbatim
@[simp] theorem denote_var (ρ : Var → M.carrier) (x : Var) :
    M.denote ρ (.var x) = {ρ x} := rfl


-- @@ L147-148 verbatim
@[simp] theorem denote_bot (ρ : Var → M.carrier) :
    M.denote ρ (.bot : Pattern S Var) = ∅ := rfl


-- @@ L150-152 verbatim
@[simp] theorem denote_app (ρ : Var → M.carrier) (σ : S.Sym)
    (f : Fin (S.arity σ) → Pattern S Var) :
    M.denote ρ (.app σ f) = M.app σ (fun i => M.denote ρ (f i)) := rfl


-- @@ L154-155 verbatim
@[simp] theorem denote_imp (ρ : Var → M.carrier) (φ ψ : Pattern S Var) :
    M.denote ρ (.imp φ ψ) = (M.denote ρ φ)ᶜ ∪ M.denote ρ ψ := rfl


-- @@ L157-158 verbatim
@[simp] theorem denote_ex (ρ : Var → M.carrier) (x : Var) (φ : Pattern S Var) :
    M.denote ρ (.ex x φ) = ⋃ a : M.carrier, M.denote (Function.update ρ x a) φ := rfl


-- @@ L160-161 verbatim
/-! Derived clauses (paper, Section 2): these are the positive controls on the
definitions above -- if any of them failed, `denote` would be wrong. -/


-- @@ L163-165 verbatim
theorem denote_nt (ρ : Var → M.carrier) (φ : Pattern S Var) :
    M.denote ρ φ.nt = (M.denote ρ φ)ᶜ := by
  simp [Pattern.nt]


-- @@ L167-169 verbatim
theorem denote_tp (ρ : Var → M.carrier) :
    M.denote ρ (Pattern.tp : Pattern S Var) = Set.univ := by
  simp [Pattern.tp]


-- @@ L171-173 verbatim
theorem denote_al (ρ : Var → M.carrier) (x : Var) (φ : Pattern S Var) :
    M.denote ρ (Pattern.al x φ) = ⋂ a : M.carrier, M.denote (Function.update ρ x a) φ := by
  simp [Pattern.al, Set.compl_iUnion]


-- @@ L175-175 verbatim
end Denote


-- @@ L177-177 verbatim
namespace Model


-- @@ L179-179 verbatim
section Reach


-- @@ L181-181 verbatim
variable {S : Signature} (M : Model S)


-- @@ L183-188 verbatim
/-- One backward step: `u ⇝ v` when `u ∈ σ_M(a₁,…,aₙ)` for some tuple `a` with
`v = a i` (paper, Definition 2).  Constants contribute no steps, since
`Fin 0` is empty. -/
def Step (u v : M.carrier) : Prop :=
  ∃ (σ : S.Sym) (a : Fin (S.arity σ) → M.carrier) (i : Fin (S.arity σ)),
    u ∈ M.interp σ a ∧ v = a i


-- @@ L190-192 verbatim
/-- `C` is backward closed when `⇝[C] ⊆ C` (paper, Definition 2). -/
def BackwardClosed (C : Set M.carrier) : Prop :=
  ∀ ⦃u⦄, u ∈ C → ∀ ⦃v⦄, M.Step u v → v ∈ C


-- @@ L194-200 verbatim
/-- The concrete form used in the proofs: if a point of `C` is produced by a
tuple, every component of that tuple lies in `C` (paper, Definition 2, second
sentence). -/
theorem BackwardClosed.mem_of_interp {C : Set M.carrier} (hC : M.BackwardClosed C)
    {σ : S.Sym} {a : Fin (S.arity σ) → M.carrier} {u : M.carrier}
    (hu : u ∈ C) (ha : u ∈ M.interp σ a) (i : Fin (S.arity σ)) : a i ∈ C :=
  hC hu ⟨σ, a, i, ha, rfl⟩


-- @@ L202-202 verbatim
end Reach


-- @@ L204-204 verbatim
end Model


-- @@ L206-206 verbatim
end MatchingLogic
