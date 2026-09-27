/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import LeanPool.InfinitaryLogic.Lomega1omega.Semantics
import LeanPool.InfinitaryLogic.Util


-- @@ L11-36 verbatim
/-!
# Lω₁ω Theories and Semantic Entailment

This file defines theories, models, semantic entailment, and elementary equivalence
in Lω₁ω (countable infinitary logic with countable conjunctions/disjunctions).

## Main Definitions

- `Theoryω`: A theory in Lω₁ω is a set of sentences.
- `Theoryω.Model`: A structure M is a model of theory T if it satisfies all sentences in T.
- `Theoryω.IsSatisfiableIn`: T has a model in a selected carrier universe.
- `LomegaEquiv`: Lω₁ω-elementary equivalence between structures.

## Main Results

- `Theoryω.Model.empty`: The empty theory has every structure as a model.
- `Theoryω.Model.mono`: Models are monotone: if T ⊆ T' and M ⊨ T', then M ⊨ T.
- `LomegaEquiv.refl`, `LomegaEquiv.symm`, `LomegaEquiv.trans`: `LomegaEquiv` is an equivalence
  relation.
- `LomegaEquiv.of_equiv`: Isomorphic structures are Lω₁ω-equivalent.

## References

- [Mar16]
- [KK04]
-/


-- @@ L38-38 verbatim
@[expose] public section


-- @@ L40-40 verbatim
universe u v w w'


-- @@ L42-42 verbatim
namespace FirstOrder


-- @@ L44-44 verbatim
namespace Language


-- @@ L46-46 verbatim
variable {L : Language.{u, v}}


-- @@ L48-48 verbatim
open FirstOrder Structure


-- @@ L50-50 verbatim
/-! ### Theories -/


-- @@ L52-53 verbatim
/-- A theory in Lω₁ω is a set of Lω₁ω sentences. -/
abbrev Theoryω (L : Language.{u, v}) := Set L.Sentenceω


-- @@ L55-55 verbatim
namespace Theoryω


-- @@ L57-57 verbatim
variable {T T' : L.Theoryω} {φ : L.Sentenceω}


-- @@ L59-61 verbatim
/-- A structure M is a model of theory T if it satisfies all sentences in T. -/
def Model (T : L.Theoryω) (M : Type w) [L.Structure M] : Prop :=
  ∀ φ ∈ T, Sentenceω.Realize φ M


-- @@ L63-66 verbatim
/-- The empty theory has every structure as a model. -/
theorem Model.empty (M : Type w) [L.Structure M] : Model (∅ : L.Theoryω) M := by
  intro φ hφ
  exact False.elim (Set.notMem_empty φ hφ)


-- @@ L68-70 verbatim
/-- If T ⊆ T' and M ⊨ T', then M ⊨ T. -/
theorem Model.mono (h : T ⊆ T') {M : Type w} [L.Structure M] (hM : T'.Model M) : T.Model M :=
  fun φ hφ => hM φ (h hφ)


-- @@ L72-79 verbatim
/-- **Satisfiability in a selected carrier universe.**

The final universe parameter is part of the semantic specification:
`IsSatisfiableIn.{u, v, w} T` asks for a model whose carrier lies in `Type w`, independently of the
universes `u`, `v` of the language.  Use this form when a construction chooses the model universe;
the older `IsSatisfiable` below is its universe-zero specialization. -/
def IsSatisfiableIn (T : L.Theoryω) : Prop :=
  ∃ (M : Type w) (_ : L.Structure M) (_ : Nonempty M), T.Model M


-- @@ L81-84 verbatim
/-- **Finite satisfiability in a selected carrier universe** — every ordinarily finite subtheory
has a model in `Type w`. -/
def IsFinitelySatisfiableIn (T : L.Theoryω) : Prop :=
  ∀ T₀ ⊆ T, T₀.Finite → IsSatisfiableIn.{u, v, w} T₀


-- @@ L86-94 verbatim
/-- **Satisfiability**, named rather than written out.  The existential-model statement was
repeated at every compactness site; spelling it out invites confusing *ordinary* finite
satisfiability with the `A`-finite kind, which are different hypotheses.  Named after Mathlib's
`Theory.IsSatisfiable` for the finitary case.

This published predicate retains its original universe-zero meaning.  Constructions that select a
different model universe should use `IsSatisfiableIn`. -/
def IsSatisfiable (T : L.Theoryω) : Prop :=
  ∃ (M : Type) (_ : L.Structure M) (_ : Nonempty M), T.Model M


-- @@ L96-100 verbatim
/-- **Finite satisfiability** — every *ordinarily* finite subtheory has a model.  Contrast
`AFinitelySatisfiable`, the Barwise premise, which quantifies over `A`-finite subtheories
instead; at `A = HF` the two coincide, and nowhere else. -/
def IsFinitelySatisfiable (T : L.Theoryω) : Prop :=
  ∀ T₀ ⊆ T, T₀.Finite → T₀.IsSatisfiable


-- @@ L102-106 verbatim
/-- Satisfiability in a fixed carrier universe is monotone under shrinking the theory. -/
theorem IsSatisfiableIn.mono {T T' : L.Theoryω} (h : T ⊆ T')
    (hT' : IsSatisfiableIn.{u, v, w} T') : IsSatisfiableIn.{u, v, w} T := by
  obtain ⟨M, inst, ne, hM⟩ := hT'
  exact ⟨M, inst, ne, hM.mono h⟩


-- @@ L108-111 verbatim
theorem IsSatisfiable.mono {T T' : L.Theoryω} (h : T ⊆ T') (hT' : T'.IsSatisfiable) :
    T.IsSatisfiable := by
  obtain ⟨M, inst, ne, hM⟩ := hT'
  exact ⟨M, inst, ne, hM.mono h⟩


-- @@ L113-113 verbatim
end Theoryω


-- @@ L115-115 verbatim
/-! ### Isomorphism Invariance of Realization -/


-- @@ L117-155 verbatim
/-- Realization of Lω₁ω formulas is preserved by language isomorphisms.

Given an isomorphism `e : M ≃[L] N`, a formula realized in M with variable assignments
`v` and `xs` is also realized in N with the transported assignments `e ∘ v` and `e ∘ xs`. -/
theorem BoundedFormulaω.realize_equiv {M N : Type w} [L.Structure M] [L.Structure N]
    (e : M ≃[L] N) {α : Type*} {n : ℕ} (φ : L.BoundedFormulaω α n)
    (v : α → M) (xs : Fin n → M) :
    φ.Realize v xs ↔ φ.Realize (e ∘ v) (e ∘ xs) := by
  have h_elim : ∀ {m : ℕ} (v' : α → M) (xs' : Fin m → M),
      Sum.elim (⇑e ∘ v') (⇑e ∘ xs') = ⇑e ∘ Sum.elim v' xs' := by
    intro m v' xs'; funext x; cases x <;> rfl
  induction φ with
  | falsum => simp
  | equal t₁ t₂ =>
    simp only [BoundedFormulaInf.Realize, h_elim, HomClass.realize_term e]
    exact e.injective.eq_iff.symm
  | rel R ts =>
    simp only [BoundedFormulaInf.Realize]
    simp_rw [h_elim, HomClass.realize_term e]
    exact (StrongHomClass.map_rel e R _).symm
  | imp φ ψ ihφ ihψ =>
    simp only [BoundedFormulaInf.Realize]
    exact Iff.imp (ihφ xs) (ihψ xs)
  | all φ ih =>
    simp only [BoundedFormulaInf.Realize]
    constructor
    · intro h y
      have h1 := (ih (Fin.snoc xs (e.symm y))).mp (h (e.symm y))
      rwa [Fin.comp_snoc, e.apply_symm_apply] at h1
    · intro h x
      have h1 := h (e x)
      rw [← Fin.comp_snoc] at h1
      exact (ih (Fin.snoc xs x)).mpr h1
  | iSup φs ih =>
    simp only [BoundedFormulaInf.Realize]
    exact exists_congr fun i => ih i xs
  | iInf φs ih =>
    simp only [BoundedFormulaInf.Realize]
    exact forall_congr' fun i => ih i xs


-- @@ L157-157 verbatim
/-! ### Lω₁ω Elementary Equivalence -/


-- @@ L159-161 verbatim
/-- Two structures are Lω₁ω-elementarily equivalent if they satisfy the same Lω₁ω sentences. -/
def LomegaEquiv (L : Language) (M N : Type*) [L.Structure M] [L.Structure N] : Prop :=
  ∀ φ : L.Sentenceω, Sentenceω.Realize φ M ↔ Sentenceω.Realize φ N


-- @@ L163-163 verbatim
namespace LomegaEquiv


-- @@ L165-165 verbatim
variable {M : Type w} [L.Structure M]

-- @@ L166-166 verbatim
variable {N : Type w'} [L.Structure N]

-- @@ L167-167 verbatim
variable {P : Type*} [L.Structure P]


-- @@ L169-170 verbatim
/-- Lω₁ω-equivalence is reflexive. -/
theorem refl : LomegaEquiv L M M := fun _ => Iff.rfl


-- @@ L172-173 verbatim
/-- Lω₁ω-equivalence is symmetric. -/
theorem symm (h : LomegaEquiv L M N) : LomegaEquiv L N M := fun φ => (h φ).symm


-- @@ L175-177 verbatim
/-- Lω₁ω-equivalence is transitive. -/
theorem trans (h₁ : LomegaEquiv L M N) (h₂ : LomegaEquiv L N P) : LomegaEquiv L M P :=
  fun φ => (h₁ φ).trans (h₂ φ)


-- @@ L179-188 verbatim
/-- Isomorphic structures are Lω₁ω-equivalent.

The proof transports variable assignments along the isomorphism using
`BoundedFormulaω.realize_equiv`, then observes that `e ∘ Empty.elim = Empty.elim`
and `e ∘ Fin.elim0 = Fin.elim0` since both domains are empty. -/
theorem of_equiv {M N : Type w} [L.Structure M] [L.Structure N] (e : M ≃[L] N) :
    LomegaEquiv L M N := by
  intro φ
  have h := BoundedFormulaω.realize_equiv e φ (Empty.elim : Empty → M) (Fin.elim0 : Fin 0 → M)
  rwa [comp_empty_elim e, comp_fin_elim0 e] at h


-- @@ L190-190 verbatim
end LomegaEquiv


-- @@ L192-192 verbatim
/-! ### Invariance under Isomorphism -/


-- @@ L194-199 verbatim
/-- Models of a theory are preserved under isomorphism. -/
theorem Theoryω.Model.of_equiv {T : L.Theoryω} {M N : Type w} [L.Structure M]
    [L.Structure N] (hM : T.Model M) (e : M ≃[L] N) : T.Model N := by
  intro φ hφ
  have h := LomegaEquiv.of_equiv e φ
  exact h.mp (hM φ hφ)


-- @@ L201-201 verbatim
end Language


-- @@ L203-203 verbatim
end FirstOrder
