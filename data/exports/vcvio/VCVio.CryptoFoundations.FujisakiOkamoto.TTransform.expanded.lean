/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.AsymmEncAlg.INDCPA.Oracle
public import VCVio.CryptoFoundations.FujisakiOkamoto.Defs
public import VCVio.OracleComp.Coercions.Add
public import VCVio.OracleComp.HasQuery.Morphism
public import VCVio.OracleComp.QueryTracking.QueryCost
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
public import VCVio.OracleComp.SimSemantics.StateT.BundledSemantics


-- @@ L16-23 verbatim
/-!
# Fujisaki-Okamoto T Transform

This file defines the derandomizing T transform:

- coins are derived from a random oracle on the plaintext
- decryption re-derives the coins and checks re-encryption
-/


-- @@ L25-25 verbatim
@[expose] public section



-- @@ L28-28 verbatim
open OracleComp OracleSpec ENNReal


-- @@ L30-30 verbatim
universe u v


-- @@ L32-32 verbatim
namespace TTransform


-- @@ L34-37 expanded
/-- The full oracle world for the T-transform: unrestricted public randomness plus a random oracle
mapping plaintexts to encryption coins. -/
abbrev oracleSpec (M R : Type) :=
  unifSpec + (OracleSpec.ofFn (ι := M) (fun _ => R))


-- @@ L39-41 expanded
/-- Cache state for the T-transform's lazy coins oracle. -/
abbrev QueryCache (M R : Type) :=
  (OracleSpec.ofFn (ι := M) (fun _ => R)).QueryCache


-- @@ L43-46 expanded
/-- Query implementation for the T-transform hash oracle. -/
def queryImpl {M R : Type} [DecidableEq M] [SampleableType R] :
    QueryImpl (OracleSpec.ofFn (ι := M) (fun _ => R)) (StateT (QueryCache M R) ProbComp) :=
  randomOracle


-- @@ L48-48 verbatim
end TTransform


-- @@ L50-50 verbatim
open TTransform


-- @@ L52-52 verbatim
variable {M PK SK R C : Type}


-- @@ L54-64 expanded
/-- Decryption for the T transform: decrypt deterministically, then re-query the coins oracle and
check that re-encryption reproduces the ciphertext. -/
def TTransform.decrypt {m : Type → Type v} [Monad m]
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C) [DecidableEq C]
    [HasQuery (OracleSpec.ofFn (ι := M) (fun _ => R)) m] (pk : PK) (sk : SK) (c : C) :
    m (Option M) := do
  match pke.decrypt sk c with
  | none =>
    return none
  | some msg =>
    let r ← HasQuery.query (spec := (OracleSpec.ofFn (ι := M) (fun _ => R))) msg
    return if pke.encrypt pk msg r = c then some msg else none


-- @@ L66-79 expanded
/-- The HHK17 T transform, realized as a monadic `AsymmEncAlg` in the random-oracle world
`unifSpec + (M →ₒ R)`. -/
def TTransform {m : Type → Type v} [Monad m] (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    [DecidableEq C] [MonadLiftT ProbComp m] [HasQuery (OracleSpec.ofFn (ι := M) (fun _ => R)) m] :
    AsymmEncAlg m M PK (PK × SK) C
    where
  keygen := do
    let (pk, sk) ← (monadLift pke.keygen : m (PK × SK))
    return (pk, (pk, sk))
  encrypt pk
    msg := do
    let r ← HasQuery.query (spec := (OracleSpec.ofFn (ι := M) (fun _ => R))) msg
    return pke.encrypt pk msg r
  decrypt
    | (pk, sk), c => TTransform.decrypt pke pk sk c


-- @@ L81-81 verbatim
section naturality


-- @@ L83-83 verbatim
variable [DecidableEq C]


-- @@ L85-88 expanded
variable {m : Type → Type u} [Monad m] {n : Type → Type v} [Monad n] [MonadLiftT ProbComp m]
  [MonadLiftT ProbComp n] [HasQuery (OracleSpec.ofFn (ι := M) (fun _ => R)) m]
  [HasQuery (OracleSpec.ofFn (ι := M) (fun _ => R)) n]


-- @@ L90-106 expanded
/-- The T-transform is natural in any oracle-semantics morphism that preserves both the
plaintext-to-coins query capability and the distinguished lift of `ProbComp`. -/
theorem map_construction (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    (F : HasQuery.QueryHom (OracleSpec.ofFn (ι := M) (fun _ => R)) m n)
    (hLift : HasQuery.PreservesProbCompLift (m := m) (n := n) F.toMonadHom) :
    (TTransform (m := m) pke).map F.toMonadHom = TTransform (m := n) pke := by
  cases pke with
  | mk keygen encrypt decrypt =>
    apply AsymmEncAlg.ext
    · simp [AsymmEncAlg.map, TTransform, hLift keygen]
    · funext pk msg
      simp [AsymmEncAlg.map, TTransform]
    · funext x c
      cases hdec : decrypt x.2 c <;> simp [AsymmEncAlg.map, TTransform, TTransform.decrypt, hdec]


-- @@ L108-108 verbatim
end naturality


-- @@ L110-110 verbatim
section costAccounting


-- @@ L112-112 verbatim
variable [DecidableEq C]


-- @@ L114-115 verbatim
variable {m : Type → Type u} [Monad m] [LawfulMonad m]
  [MonadLiftT ProbComp m]


-- @@ L117-124 expanded
/-- T-transform encryption incurs exactly the weighted cost assigned to the single coins-oracle
query on `msg`. -/
theorem encrypt_usesExactQueryCost {ω : Type} [AddMonoid ω]
    (runtime : QueryImpl (OracleSpec.ofFn (ι := M) (fun _ => R)) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C) (pk : PK) (msg : M) (costFn : M → ω) :
    HasQuery.UsesCostExactly
      (((fun [HasQuery _ _] => (TTransform pke).encrypt pk msg) :
        [HasQuery _ (AddWriterT _ _)] → AddWriterT _ _ _))
      runtime costFn (costFn msg) :=
  by simp [HasQuery.UsesCostExactly, HasQuery.Program.withAddCost, TTransform]


-- @@ L126-138 expanded
/-- T-transform encryption has expected weighted query cost equal to the weight of querying
`msg`. -/
theorem encrypt_expectedQueryCost_eq {ω : Type} [AddMonoid ω] [Preorder ω] [MonadLiftT m PMF]
    [LawfulMonadLiftT m PMF] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]
    (runtime : QueryImpl (OracleSpec.ofFn (ι := M) (fun _ => R)) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C) (pk : PK) (msg : M) (costFn : M → ω)
    (val : ω → ENNReal) (hval : Monotone val) :
    HasQuery.expectedQueryCost
        (((fun [HasQuery _ _] => (TTransform pke).encrypt pk msg) :
          [HasQuery _ (AddWriterT _ _)] → AddWriterT _ _ _))
        runtime costFn val =
      val (costFn msg) :=
  HasQuery.expectedQueryCost_eq_of_usesCostExactly
    (encrypt_usesExactQueryCost runtime pke pk msg costFn) hval


-- @@ L140-147 expanded
/-- T-transform encryption makes exactly one hash-oracle query under unit-cost instrumentation. -/
theorem encrypt_usesExactlyOneQuery (runtime : QueryImpl (OracleSpec.ofFn (ι := M) (fun _ => R)) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C) (pk : PK) (msg : M) :
    HasQuery.UsesExactlyQueries
      (((fun [HasQuery _ _] => (TTransform pke).encrypt pk msg) :
        [HasQuery _ (AddWriterT ℕ _)] → AddWriterT ℕ _ _))
      runtime 1 :=
  by
  simpa [HasQuery.UsesExactlyQueries] using
    encrypt_usesExactQueryCost (ω := ℕ) runtime pke pk msg fun _ => 1


-- @@ L149-158 expanded
/-- If deterministic decryption fails immediately, the T-transform incurs zero weighted
query cost. -/
theorem decrypt_usesZeroQueryCost_of_decrypt_eq_none {ω : Type} [AddMonoid ω]
    (runtime : QueryImpl (OracleSpec.ofFn (ι := M) (fun _ => R)) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C) (pk : PK) (sk : SK) (c : C)
    (costFn : M → ω) (hdec : pke.decrypt sk c = none) :
    HasQuery.UsesCostExactly
      (((fun [HasQuery _ _] => (TTransform pke).decrypt (pk, sk) c) :
        [HasQuery _ (AddWriterT _ _)] → AddWriterT _ _ _))
      runtime costFn 0 :=
  by
  simp [HasQuery.UsesCostExactly, HasQuery.Program.withAddCost, TTransform, TTransform.decrypt,
    hdec]


-- @@ L160-174 expanded
/-- If deterministic decryption fails immediately, the T-transform has expected weighted query
cost `0`. -/
theorem decrypt_expectedQueryCost_eq_zero_of_decrypt_eq_none {ω : Type} [AddMonoid ω] [Preorder ω]
    [MonadLiftT m PMF] [LawfulMonadLiftT m PMF] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    [EvalDistCompatible m] (runtime : QueryImpl (OracleSpec.ofFn (ι := M) (fun _ => R)) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C) (pk : PK) (sk : SK) (c : C)
    (costFn : M → ω) (val : ω → ENNReal) (hval : Monotone val) (hdec : pke.decrypt sk c = none) :
    HasQuery.expectedQueryCost
        (((fun [HasQuery _ _] => (TTransform pke).decrypt (pk, sk) c) :
          [HasQuery _ (AddWriterT _ _)] → AddWriterT _ _ _))
        runtime costFn val =
      val 0 :=
  HasQuery.expectedQueryCost_eq_of_usesCostExactly
    (decrypt_usesZeroQueryCost_of_decrypt_eq_none runtime pke pk sk c costFn hdec) hval


-- @@ L176-185 expanded
/-- If deterministic decryption returns a message, the T-transform incurs exactly the weighted
cost of querying that message to re-derive the coins. -/
theorem decrypt_usesExactQueryCost_of_decrypt_eq_some {ω : Type} [AddMonoid ω]
    (runtime : QueryImpl (OracleSpec.ofFn (ι := M) (fun _ => R)) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C) (pk : PK) (sk : SK) (c : C)
    (costFn : M → ω) {msg : M} (hdec : pke.decrypt sk c = some msg) :
    HasQuery.UsesCostExactly
      (((fun [HasQuery _ _] => (TTransform pke).decrypt (pk, sk) c) :
        [HasQuery _ (AddWriterT _ _)] → AddWriterT _ _ _))
      runtime costFn (costFn msg) :=
  by
  simp [HasQuery.UsesCostExactly, HasQuery.Program.withAddCost, TTransform, TTransform.decrypt,
    hdec]


-- @@ L187-201 expanded
/-- If deterministic decryption returns a message, the T-transform has expected weighted query
cost equal to the weight of querying that message. -/
theorem decrypt_expectedQueryCost_eq_of_decrypt_eq_some {ω : Type} [AddMonoid ω] [Preorder ω]
    [MonadLiftT m PMF] [LawfulMonadLiftT m PMF] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    [EvalDistCompatible m] (runtime : QueryImpl (OracleSpec.ofFn (ι := M) (fun _ => R)) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C) (pk : PK) (sk : SK) (c : C)
    (costFn : M → ω) (val : ω → ENNReal) (hval : Monotone val) {msg : M}
    (hdec : pke.decrypt sk c = some msg) :
    HasQuery.expectedQueryCost
        (((fun [HasQuery _ _] => (TTransform pke).decrypt (pk, sk) c) :
          [HasQuery _ (AddWriterT _ _)] → AddWriterT _ _ _))
        runtime costFn val =
      val (costFn msg) :=
  HasQuery.expectedQueryCost_eq_of_usesCostExactly
    (decrypt_usesExactQueryCost_of_decrypt_eq_some runtime pke pk sk c costFn hdec) hval


-- @@ L203-212 expanded
/-- If deterministic decryption fails immediately, the T-transform makes no hash-oracle
queries. -/
theorem decrypt_usesNoQueries_of_decrypt_eq_none
    (runtime : QueryImpl (OracleSpec.ofFn (ι := M) (fun _ => R)) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C) (pk : PK) (sk : SK) (c : C)
    (hdec : pke.decrypt sk c = none) :
    HasQuery.UsesExactlyQueries
      (((fun [HasQuery _ _] => (TTransform pke).decrypt (pk, sk) c) :
        [HasQuery _ (AddWriterT ℕ _)] → AddWriterT ℕ _ _))
      runtime 0 :=
  by
  simpa [HasQuery.UsesExactlyQueries] using
    decrypt_usesZeroQueryCost_of_decrypt_eq_none (ω := ℕ) runtime pke pk sk c (fun _ => 1) hdec


-- @@ L214-223 expanded
/-- If deterministic decryption returns a message, the T-transform makes exactly one
hash-oracle query to re-derive the coins. -/
theorem decrypt_usesExactlyOneQuery_of_decrypt_eq_some
    (runtime : QueryImpl (OracleSpec.ofFn (ι := M) (fun _ => R)) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C) (pk : PK) (sk : SK) (c : C) {msg : M}
    (hdec : pke.decrypt sk c = some msg) :
    HasQuery.UsesExactlyQueries
      (((fun [HasQuery _ _] => (TTransform pke).decrypt (pk, sk) c) :
        [HasQuery _ (AddWriterT ℕ _)] → AddWriterT ℕ _ _))
      runtime 1 :=
  by
  simpa [HasQuery.UsesExactlyQueries] using
    decrypt_usesExactQueryCost_of_decrypt_eq_some (ω := ℕ) runtime pke pk sk c (fun _ => 1) hdec


-- @@ L225-237 expanded
/-- T-transform decryption makes at most one hash-oracle query under unit-cost instrumentation. -/
theorem decrypt_usesAtMostOneQuery [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    (runtime : QueryImpl (OracleSpec.ofFn (ι := M) (fun _ => R)) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C) (pk : PK) (sk : SK) (c : C) :
    HasQuery.UsesAtMostQueries
      (((fun [HasQuery _ _] => (TTransform pke).decrypt (pk, sk) c) :
        [HasQuery _ (AddWriterT ℕ _)] → AddWriterT ℕ _ _))
      runtime 1 :=
  by
  cases hdec : pke.decrypt sk c with
  | none =>
    exact
      HasQuery.usesAtMostQueries_of_usesExactlyQueries
        (decrypt_usesNoQueries_of_decrypt_eq_none runtime pke pk sk c hdec) (Nat.zero_le 1)
  | some msg =>
    exact
      HasQuery.usesAtMostQueries_of_usesExactlyQueries
        (decrypt_usesExactlyOneQuery_of_decrypt_eq_some runtime pke pk sk c hdec) le_rfl


-- @@ L239-239 verbatim
end costAccounting


-- @@ L241-241 verbatim
namespace TTransform


-- @@ L243-248 verbatim
/-- Runtime bundle for the T-transform random-oracle world. -/
noncomputable def runtime
    [DecidableEq M] [SampleableType R] :
    ProbCompRuntime (OracleComp (TTransform.oracleSpec M R)) where
  toSPMFSemantics := SPMFSemantics.withStateOracle TTransform.queryImpl ∅
  toProbCompLift := ProbCompLift.ofMonadLift _


-- @@ L250-265 verbatim
/-- Structural query bound for T-transform OW-PCVA adversaries: uniform-sampling queries are
unrestricted, while `qH`, `qP`, and `qV` bound the hash, plaintext-checking, and validity
oracles respectively.

Defined as the conjunction of three predicate-targeted query bounds `IsQueryBoundP`, one per
counted oracle. Because the three index predicates are pairwise disjoint, this conjunction is
equivalent to a single-vector `IsQueryBound` over the combined per-oracle budget. -/
def OW_PCVA_Adversary.MakesAtMostQueries
    {M PK SK R C : Type} [DecidableEq M] [DecidableEq C] [SampleableType R]
    {pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C}
    (adversary : OW_PCVA_Adversary
      (TTransform (m := OracleComp (TTransform.oracleSpec M R)) pke)) (qH qP qV : ℕ) : Prop :=
  ∀ pk cStar,
    (adversary pk cStar).IsQueryBoundP (· matches .inl (.inr _)) qH ∧
    (adversary pk cStar).IsQueryBoundP (· matches .inr (.inl _)) qP ∧
    (adversary pk cStar).IsQueryBoundP (· matches .inr (.inr _)) qV


-- @@ L267-267 verbatim
end TTransform
