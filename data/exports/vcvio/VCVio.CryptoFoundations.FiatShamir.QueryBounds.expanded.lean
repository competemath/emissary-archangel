/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import VCVio.OracleComp.Coercions.Add
public import VCVio.OracleComp.QueryTracking.QueryBound


-- @@ L12-22 verbatim
/-!
# Query-count bounds for Fiat-Shamir adversaries

Structural `IsQueryBound` predicates used by both the Σ-protocol and
with-aborts instances of Fiat-Shamir, plus the reciprocal challenge-space size
that appears in the quantitative bounds.

The two non-aborting EUF-CMA variants use exactly the same predicates, so they
live here in the shared `FiatShamir` namespace. With-aborts call sites
reference them via their fully qualified name.
-/


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-26 verbatim
universe u v


-- @@ L28-28 verbatim
open OracleComp OracleSpec


-- @@ L30-30 verbatim
namespace FiatShamir


-- @@ L32-33 verbatim
variable {Stmt Wit Commit PrvState Chal Resp : Type}
    {rel : Stmt → Wit → Bool}


-- @@ L35-35 verbatim
section bounds


-- @@ L37-37 verbatim
variable (M : Type)


-- @@ L39-46 expanded
/-- Structural bound that counts only random-oracle queries in a Fiat-Shamir
EUF-CMA adversary. Uniform-sampling and signing-oracle queries are unrestricted.

Defined as the generic predicate-targeted query bound `IsQueryBoundP` with the predicate
selecting the nested `.inl (.inr _)` (random-oracle) component of the index sum. -/
def hashQueryBound {S' α : Type}
    (oa :
      OracleComp
        ((unifSpec + (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal))) +
          (OracleSpec.ofFn (ι := M) (fun _ => S')))
        α)
    (Q : ℕ) : Prop :=
  OracleComp.IsQueryBoundP oa (· matches .inl (.inr _)) Q


-- @@ L48-59 expanded
/-- Structural query bound for Fiat-Shamir EUF-CMA adversaries that tracks both
signing-oracle queries (`qS`) and random-oracle queries (`qH`).
Uniform-sampling queries are unrestricted.

Defined as the conjunction of two predicate-targeted query bounds `IsQueryBoundP`, one per
counted oracle. Because the two index predicates are disjoint, the conjunction is
equivalent to the prior single-vector `IsQueryBound` formulation. -/
def signHashQueryBound {S' α : Type}
    (oa :
      OracleComp
        ((unifSpec + (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal))) +
          (OracleSpec.ofFn (ι := M) (fun _ => S')))
        α)
    (qS qH : ℕ) : Prop :=
  oa.IsQueryBoundP (· matches .inr _) qS ∧ oa.IsQueryBoundP (· matches .inl (.inr _)) qH


-- @@ L61-68 expanded
/-- Structural bound on random-oracle queries for an NMA adversary (no signing oracle).
Uniform-sampling queries are unrestricted.

Defined as the generic predicate-targeted query bound `IsQueryBoundP` with the predicate
selecting the right (random-oracle) component of the index sum. -/
def nmaHashQueryBound {α : Type}
    (oa : OracleComp (unifSpec + (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal))) α) (Q : ℕ) :
    Prop :=
  OracleComp.IsQueryBoundP oa (· matches .inr _) Q


-- @@ L70-87 expanded
@[simp]
lemma nmaHashQueryBound_query_bind_iff {α : Type}
    (t : (unifSpec + (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal))).Domain)
    (oa :
      (unifSpec + (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal))).Range t →
        OracleComp (unifSpec + (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal))) α)
    (Q : ℕ) :
    nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal) (oa :=
        liftM ((unifSpec + (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal))).query t) >>= oa) Q ↔
      (match t with
        | .inl _ => True
        | .inr _ => 0 < Q) ∧
        ∀ u,
          nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal) (oa := oa u)
            (match t with
            | .inl _ => Q
            | .inr _ => Q - 1) :=
  by
  simp only [nmaHashQueryBound, OracleComp.isQueryBoundP_query_bind_iff]
  cases t <;> simp


-- @@ L89-98 expanded
@[simp]
lemma nmaHashQueryBound_query_iff
    (t : (unifSpec + (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal))).Domain) (Q : ℕ) :
    nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal) (oa :=
        liftM ((unifSpec + (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal))).query t)) Q ↔
      match t with
      | .inl _ => True
      | .inr _ => 0 < Q :=
  by
  simp only [nmaHashQueryBound, OracleComp.isQueryBoundP_query_iff]
  cases t <;> simp


-- @@ L100-105 expanded
lemma nmaHashQueryBound_mono {α : Type}
    {oa : OracleComp (unifSpec + (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal))) α} {Q₁ Q₂ : ℕ}
    (h : nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal) (oa := oa) Q₁)
    (hQ : Q₁ ≤ Q₂) : nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal) (oa := oa) Q₂ :=
  OracleComp.IsQueryBoundP.mono h hQ


-- @@ L107-114 expanded
lemma nmaHashQueryBound_bind {α β : Type}
    {oa : OracleComp (unifSpec + (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal))) α}
    {ob : α → OracleComp (unifSpec + (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal))) β}
    {Q₁ Q₂ : ℕ} (h1 : nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal) (oa := oa) Q₁)
    (h2 : ∀ x, nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal) (oa := ob x) Q₂) :
    nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal) (oa := oa >>= ob) (Q₁ + Q₂) :=
  OracleComp.isQueryBoundP_bind h1 (fun x _ => h2 x)


-- @@ L116-134 expanded
lemma nmaHashQueryBound_liftComp_zero [Inhabited Chal] [Finite Chal] {α : Type} (oa : ProbComp α) :
    nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal) (oa :=
      OracleComp.liftComp oa (unifSpec + (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)))) 0 :=
  by
  have : Fintype Chal := Fintype.ofFinite Chal
  let : IsUniformSpec ((OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) : OracleSpec _) :=
    IsUniformSpec.ofFintypeInhabited _
  rw [nmaHashQueryBound, OracleComp.liftComp_def]
  refine
    OracleComp.IsQueryBoundP.simulateQ_of_step (p := fun _ : ℕ => False) (impl := fun t =>
      (liftM (unifSpec.query t) :
        OracleComp (unifSpec + (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)))
          (unifSpec.Range t)))
      (OracleComp.isQueryBoundP_false oa 0) (fun _ h => h.elim) ?_
  intro t _
  change
    (liftM ((unifSpec + (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal))).query (Sum.inl t)) :
          OracleComp (unifSpec + (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)))
            _).IsQueryBoundP
      _ 0
  rw [OracleComp.isQueryBoundP_query_iff]
  simp


-- @@ L136-138 verbatim
/-- Reciprocal of the finite challenge-space size. -/
noncomputable def challengeSpaceInv (challenge : Type) [Fintype challenge] : ENNReal :=
  (Fintype.card challenge : ENNReal)⁻¹


-- @@ L140-140 verbatim
end bounds


-- @@ L142-142 verbatim
end FiatShamir
