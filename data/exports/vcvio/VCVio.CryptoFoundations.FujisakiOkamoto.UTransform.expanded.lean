/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.FujisakiOkamoto.TTransform
public import VCVio.CryptoFoundations.KeyEncapMech
public import VCVio.CryptoFoundations.PRF
public import VCVio.OracleComp.Coercions.Add
public import VCVio.OracleComp.SimSemantics.StateT.BundledSemantics


-- @@ L14-18 verbatim
/-!
# Fujisaki-Okamoto U Transform

This file defines the U-transform family on top of the T-transform oracle world.
-/


-- @@ L20-20 verbatim
@[expose] public section



-- @@ L23-23 verbatim
universe u v


-- @@ L25-25 verbatim
open OracleComp OracleSpec ENNReal


-- @@ L27-27 verbatim
namespace FujisakiOkamoto


-- @@ L29-38 verbatim
/-- A reusable FO hash world packages the public hash-oracle interface together with the
variant-specific ways of deriving encryption coins and shared keys. -/
structure Variant {ι : Type} (hashOracleSpec : OracleSpec ι) (M PK C R K : Type) where
  QueryCache : Type
  initCache : QueryCache
  queryImpl : QueryImpl hashOracleSpec (StateT QueryCache ProbComp)
  deriveCoins : {m : Type → Type v} → [Monad m] → [MonadLiftT ProbComp m] →
    [HasQuery hashOracleSpec m] → PK → M → m R
  deriveKey : {m : Type → Type v} → [Monad m] → [MonadLiftT ProbComp m] →
    [HasQuery hashOracleSpec m] → PK → M → C → m K


-- @@ L40-45 verbatim
/-- Rejection behavior is factored out from the FO hash world so explicit and implicit rejection
share the same core construction. -/
structure RejectionPolicy (K C : Type) where
  FallbackState : Type
  keygen : ProbComp FallbackState
  onReject : FallbackState → C → Option K


-- @@ L47-51 verbatim
/-- Explicit rejection returns `none` and carries no extra secret state. -/
def explicitRejection {K C : Type} : RejectionPolicy K C where
  FallbackState := PUnit
  keygen := pure PUnit.unit
  onReject := fun _ _ => none


-- @@ L53-57 verbatim
/-- Implicit rejection stores a PRF key and derives a fallback shared key from the ciphertext. -/
def implicitRejection {K C KPRF : Type} (prf : PRFScheme KPRF C K) : RejectionPolicy K C where
  FallbackState := KPRF
  keygen := prf.keygen
  onReject := fun kPrf c => some (prf.eval kPrf c)


-- @@ L59-64 verbatim
/-- Bundled subprobabilistic semantics for an FO hash world, obtained by hiding the
variant-specific cache after running the public-randomness-plus-hash simulation. -/
noncomputable def spmfSemantics {ι : Type} {hashOracleSpec : OracleSpec ι}
    {M PK C R K : Type} (variant : Variant hashOracleSpec M PK C R K) :
    SPMFSemantics (OracleComp (unifSpec + hashOracleSpec)) :=
  SPMFSemantics.withStateOracle variant.queryImpl variant.initCache


-- @@ L66-71 verbatim
/-- Full public-randomness runtime for an FO hash world. -/
noncomputable def runtime {ι : Type} {hashOracleSpec : OracleSpec ι}
    {M PK C R K : Type} (variant : Variant hashOracleSpec M PK C R K) :
    ProbCompRuntime (OracleComp (unifSpec + hashOracleSpec)) where
  toSPMFSemantics := spmfSemantics variant
  toProbCompLift := ProbCompLift.ofMonadLift _


-- @@ L73-102 expanded
/-- Generic FO construction parameterized by a hash world and a rejection policy. -/
def scheme {ι : Type} {hashOracleSpec : OracleSpec ι} {M PK SK R C K : Type} {m : Type → Type v}
    [Monad m] [MonadLiftT ProbComp m] (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    (variant : Variant hashOracleSpec M PK C R K) (policy : RejectionPolicy K C) [SampleableType M]
    [DecidableEq C] [HasQuery hashOracleSpec m] :
    KEMScheme m K PK ((PK × SK) × policy.FallbackState) C
    where
  keygen := do
    let (pk, sk) ← monadLift pke.keygen
    let fb ← monadLift policy.keygen
    return (pk, ((pk, sk), fb))
  encaps := fun pk => do
    let msg ← monadLift (uniformSample M : ProbComp M)
    let r ← variant.deriveCoins pk msg
    let c := pke.encrypt pk msg r
    let k ← variant.deriveKey pk msg c
    return (c, k)
  decaps := fun ((pk, sk), fb) c => do
    match pke.decrypt sk c with
    | none =>
      return policy.onReject fb c
    | some msg =>
      let r ← variant.deriveCoins pk msg
      if pke.encrypt pk msg r = c then 
        let k ← variant.deriveKey pk msg c
        return some k
      else
        return policy.onReject fb c


-- @@ L104-104 verbatim
end FujisakiOkamoto


-- @@ L106-106 verbatim
namespace UTransform


-- @@ L108-110 expanded
/-- The public hash-oracle interface for the two-RO U-transform: one oracle derives encryption
coins from plaintexts and the other derives shared keys from the chosen derivation input. -/
abbrev hashOracleSpec (M R KD K : Type) :=
  (OracleSpec.ofFn (ι := M) (fun _ => R)) + (OracleSpec.ofFn (ι := KD) (fun _ => K))


-- @@ L112-114 verbatim
/-- The full oracle world for the U-transform, consisting of unrestricted public randomness plus
the two public hash oracles. -/
abbrev oracleSpec (M R KD K : Type) := unifSpec + hashOracleSpec M R KD K


-- @@ L116-117 expanded
/-- Cache state for the U-transform's two lazy random oracles. -/
abbrev QueryCache (M R KD K : Type) :=
  (OracleSpec.ofFn (ι := M) (fun _ => R)).QueryCache ×
    (OracleSpec.ofFn (ι := KD) (fun _ => K)).QueryCache


-- @@ L119-128 expanded
/-- Lazy random oracle for encryption coins, threaded through the combined U-transform state. -/
def coinOracleImpl {M R KD K : Type} [DecidableEq M] [SampleableType R] :
    QueryImpl (OracleSpec.ofFn (ι := M) (fun _ => R)) (StateT (QueryCache M R KD K) ProbComp) :=
  fun msg => do
  let st ← get
  match st.1 msg with
  | some r =>
    return r
  | none =>
    let r ← (uniformSample R : ProbComp R)
    set (st.1.cacheQuery msg r, st.2)
    return r


-- @@ L130-139 expanded
/-- Lazy random oracle for key derivation, threaded through the combined U-transform state. -/
def keyOracleImpl {M R KD K : Type} [DecidableEq KD] [SampleableType K] :
    QueryImpl (OracleSpec.ofFn (ι := KD) (fun _ => K)) (StateT (QueryCache M R KD K) ProbComp) :=
  fun kd => do
  let st ← get
  match st.2 kd with
  | some k =>
    return k
  | none =>
    let k ← (uniformSample K : ProbComp K)
    set (st.1, st.2.cacheQuery kd k)
    return k


-- @@ L141-146 verbatim
/-- Query implementation for the full two-RO FO hash world. -/
def queryImpl {M R KD K : Type}
    [DecidableEq M] [DecidableEq KD] [SampleableType R] [SampleableType K] :
    QueryImpl (hashOracleSpec M R KD K) (StateT (QueryCache M R KD K) ProbComp) :=
  coinOracleImpl (M := M) (R := R) (KD := KD) (K := K) +
    keyOracleImpl (M := M) (R := R) (KD := KD) (K := K)


-- @@ L148-163 verbatim
/-- Two-RO FO hash world: one oracle derives coins from the message, the other derives the shared
key from a variant-chosen encoding of `(m, c)`. -/
def variant
    {M PK C R KD K : Type}
    (kdInput : M → C → KD)
    [DecidableEq M] [DecidableEq KD] [SampleableType R] [SampleableType K] :
    FujisakiOkamoto.Variant (hashOracleSpec M R KD K) M PK C R K where
  QueryCache := QueryCache M R KD K
  initCache := (∅, ∅)
  queryImpl := queryImpl (M := M) (R := R) (KD := KD) (K := K)
  deriveCoins := fun {m} [Monad m] [MonadLiftT ProbComp m]
      [HasQuery (hashOracleSpec M R KD K) m] _pk msg =>
    HasQuery.query (spec := hashOracleSpec M R KD K) (m := m) (Sum.inl msg)
  deriveKey := fun {m} [Monad m] [MonadLiftT ProbComp m]
      [HasQuery (hashOracleSpec M R KD K) m] _pk msg c =>
    HasQuery.query (spec := hashOracleSpec M R KD K) (m := m) (Sum.inr (kdInput msg c))


-- @@ L165-165 verbatim
end UTransform


-- @@ L167-167 verbatim
open UTransform


-- @@ L169-169 verbatim
variable {M PK SK R C KD K KPRF : Type}


-- @@ L171-183 verbatim
/-- The generic two-RO U-transform family. The argument `kdInput` chooses whether the shared key
is derived from `m`, `(m, c)`, or some other encoding of the recovered plaintext and ciphertext. -/
def UTransform
    {m : Type → Type v} [Monad m] [MonadLiftT ProbComp m]
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    (kdInput : M → C → KD)
    (policy : FujisakiOkamoto.RejectionPolicy K C)
    [DecidableEq M] [DecidableEq C] [DecidableEq KD]
    [SampleableType M] [SampleableType R] [SampleableType K]
    [HasQuery (UTransform.hashOracleSpec M R KD K) m] :
    KEMScheme m
      K PK ((PK × SK) × policy.FallbackState) C :=
  FujisakiOkamoto.scheme pke (UTransform.variant kdInput) policy


-- @@ L185-185 verbatim
namespace UTransform


-- @@ L187-187 verbatim
section costAccounting


-- @@ L189-190 verbatim
variable [DecidableEq M] [DecidableEq C] [DecidableEq KD]
  [SampleableType M] [SampleableType R] [SampleableType K]


-- @@ L192-192 verbatim
variable {m : Type → Type v} [Monad m] [LawfulMonad m] [MonadLiftT ProbComp m]


-- @@ L194-218 expanded
/-- If each of the two U-transform oracle families is assigned a constant weight, encapsulation
incurs exactly the sum of those family weights. -/
theorem encaps_usesExactFamilyWeightedCost {ω : Type} [AddMonoid ω]
    (runtime : QueryImpl (UTransform.hashOracleSpec M R KD K) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C) (kdInput : M → C → KD)
    (policy : FujisakiOkamoto.RejectionPolicy K C) (pk : PK)
    (costFn : (UTransform.hashOracleSpec M R KD K).Domain → ω) (wCoins wKey : ω)
    (hCoins : ∀ msg, costFn (Sum.inl msg) = wCoins) (hKeys : ∀ kd, costFn (Sum.inr kd) = wKey) :
    HasQuery.UsesCostExactly
      (((fun [HasQuery _ _] => (UTransform pke kdInput policy).encaps pk) :
        [HasQuery _ (AddWriterT _ _)] → AddWriterT _ _ _))
      runtime costFn (wCoins + wKey) :=
  by
  rw [HasQuery.UsesCostExactly]
  change
    AddWriterT.HasCost
      ((monadLift ((monadLift (uniformSample M : ProbComp M) : m M)) : AddWriterT ω m M) >>=
        fun msg => do
        let r ← (runtime.withAddCost costFn) (Sum.inl msg)
        let c := pke.encrypt pk msg r
        let k ← (runtime.withAddCost costFn) (Sum.inr (kdInput msg c))
        pure (c, k))
      (wCoins + wKey)
  simp_rw [QueryImpl.withAddCost_apply_inl, QueryImpl.withAddCost_apply_inr]
  rw [AddWriterT.hasCost_iff]
  simp [AddWriterT.outputs, AddWriterT.costs, hCoins, hKeys]


-- @@ L220-255 expanded
/-- Under per-family upper bounds on the two U-transform oracle families, encapsulation incurs
weighted query cost at most the sum of those bounds. -/
theorem encaps_usesWeightedQueryCostAtMost {ω : Type} [AddCommMonoid ω] [PartialOrder ω]
    [IsOrderedAddMonoid ω] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    (runtime : QueryImpl (UTransform.hashOracleSpec M R KD K) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C) (kdInput : M → C → KD)
    (policy : FujisakiOkamoto.RejectionPolicy K C) (pk : PK)
    (costFn : (UTransform.hashOracleSpec M R KD K).Domain → ω) (wCoins wKey : ω)
    (hCoins : ∀ msg, costFn (Sum.inl msg) ≤ wCoins) (hKeys : ∀ kd, costFn (Sum.inr kd) ≤ wKey) :
    HasQuery.UsesCostAtMost
      (((fun [HasQuery _ _] => (UTransform pke kdInput policy).encaps pk) :
        [HasQuery _ (AddWriterT _ _)] → AddWriterT _ _ _))
      runtime costFn (wCoins + wKey) :=
  by
  rw [HasQuery.UsesCostAtMost]
  let f : M → AddWriterT ω m (C × K) := fun msg =>
    ((runtime.withAddCost costFn) (Sum.inl msg)) >>= fun r =>
      ((runtime.withAddCost costFn) (Sum.inr (kdInput msg (pke.encrypt pk msg r)))) >>= fun k =>
        pure (pke.encrypt pk msg r, k)
  change
    AddWriterT.PathwiseCostAtMost
      (((monadLift ((monadLift (uniformSample M : ProbComp M) : m M)) : AddWriterT ω m M) >>= f))
      (wCoins + wKey)
  rw [← zero_add (wCoins + wKey)]
  refine
    AddWriterT.pathwiseCostAtMost_bind
      (AddWriterT.pathwiseCostAtMost_monadLift (m := m)
        ((monadLift (uniformSample M : ProbComp M)) : m M))
      fun msg => ?_
  refine
    AddWriterT.pathwiseCostAtMost_bind (w₁ := wCoins) (w₂ := wKey)
      (HasQuery.usesCostAtMost_query_of_le (runtime := runtime) (costFn := costFn) (t :=
        Sum.inl msg) (b := wCoins) (hCoins msg))
      fun r => ?_
  rw [← add_zero wKey]
  refine
    AddWriterT.pathwiseCostAtMost_bind
      (HasQuery.usesCostAtMost_query_of_le (runtime := runtime) (costFn := costFn) (t :=
        Sum.inr (kdInput msg (pke.encrypt pk msg r))) (b := wKey)
        (hKeys (kdInput msg (pke.encrypt pk msg r))))
      fun k => ?_
  exact AddWriterT.pathwiseCostAtMost_pure (m := m) (pke.encrypt pk msg r, k)


-- @@ L257-270 expanded
/-- Unit-cost specialization: U-transform encapsulation always makes exactly two oracle queries,
one to derive coins and one to derive the shared key. -/
theorem encaps_usesExactlyTwoQueries (runtime : QueryImpl (UTransform.hashOracleSpec M R KD K) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C) (kdInput : M → C → KD)
    (policy : FujisakiOkamoto.RejectionPolicy K C) (pk : PK) :
    HasQuery.UsesExactlyQueries
      (((fun [HasQuery _ _] => (UTransform pke kdInput policy).encaps pk) :
        [HasQuery _ (AddWriterT ℕ _)] → AddWriterT ℕ _ _))
      runtime 2 :=
  by
  simpa [HasQuery.UsesExactlyQueries] using
    (encaps_usesExactFamilyWeightedCost (ω := ℕ) (runtime := runtime) (pke := pke) (kdInput :=
      kdInput) (policy := policy) (pk := pk) (costFn := fun _ ↦ 1) (wCoins := 1) (wKey := 1)
      (hCoins := fun _ ↦ rfl) (hKeys := fun _ ↦ rfl))


-- @@ L272-291 expanded
/-- Expected weighted query cost of U-transform encapsulation under constant per-family weights. -/
theorem encaps_expectedQueryCost_eq_of_constantOracleWeights {ω : Type} [AddMonoid ω] [Preorder ω]
    [MonadLiftT m PMF] [LawfulMonadLiftT m PMF] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    [EvalDistCompatible m] (runtime : QueryImpl (UTransform.hashOracleSpec M R KD K) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C) (kdInput : M → C → KD)
    (policy : FujisakiOkamoto.RejectionPolicy K C) (pk : PK)
    (costFn : (UTransform.hashOracleSpec M R KD K).Domain → ω) (wCoins wKey : ω) (val : ω → ENNReal)
    (hval : Monotone val) (hCoins : ∀ msg, costFn (Sum.inl msg) = wCoins)
    (hKeys : ∀ kd, costFn (Sum.inr kd) = wKey) :
    HasQuery.expectedQueryCost
        (((fun [HasQuery _ _] => (UTransform pke kdInput policy).encaps pk) :
          [HasQuery _ (AddWriterT _ _)] → AddWriterT _ _ _))
        runtime costFn val =
      val (wCoins + wKey) :=
  HasQuery.expectedQueryCost_eq_of_usesCostExactly
    (encaps_usesExactFamilyWeightedCost (runtime := runtime) (pke := pke) (kdInput := kdInput)
      (policy := policy) (pk := pk) (costFn := costFn) (wCoins := wCoins) (wKey := wKey) hCoins
      hKeys)
    hval


-- @@ L293-313 expanded
/-- Expected weighted query cost of U-transform encapsulation is bounded by the sum of the
per-family bounds. -/
theorem encaps_expectedQueryCost_le {ω : Type} [AddCommMonoid ω] [PartialOrder ω]
    [IsOrderedAddMonoid ω] [MonadLiftT m PMF] [LawfulMonadLiftT m PMF] [MonadLiftT m SetM]
    [LawfulMonadLiftT m SetM] [EvalDistCompatible m]
    (runtime : QueryImpl (UTransform.hashOracleSpec M R KD K) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C) (kdInput : M → C → KD)
    (policy : FujisakiOkamoto.RejectionPolicy K C) (pk : PK)
    (costFn : (UTransform.hashOracleSpec M R KD K).Domain → ω) (wCoins wKey : ω) (val : ω → ENNReal)
    (hval : Monotone val) (hCoins : ∀ msg, costFn (Sum.inl msg) ≤ wCoins)
    (hKeys : ∀ kd, costFn (Sum.inr kd) ≤ wKey) :
    HasQuery.expectedQueryCost
        (((fun [HasQuery _ _] => (UTransform pke kdInput policy).encaps pk) :
          [HasQuery _ (AddWriterT _ _)] → AddWriterT _ _ _))
        runtime costFn val ≤
      val (wCoins + wKey) :=
  HasQuery.expectedQueryCost_le_of_usesCostAtMost
    (encaps_usesWeightedQueryCostAtMost (runtime := runtime) (pke := pke) (kdInput := kdInput)
      (policy := policy) (pk := pk) (costFn := costFn) (wCoins := wCoins) (wKey := wKey) hCoins
      hKeys)
    hval


-- @@ L315-326 expanded
/-- Expected query count of U-transform encapsulation is exactly `2`. -/
theorem encaps_expectedQueries_eq_two [MonadLiftT m PMF] [LawfulMonadLiftT m PMF]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]
    (runtime : QueryImpl (UTransform.hashOracleSpec M R KD K) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C) (kdInput : M → C → KD)
    (policy : FujisakiOkamoto.RejectionPolicy K C) (pk : PK) :
    HasQuery.expectedQueries
        (((fun [HasQuery _ _] => (UTransform pke kdInput policy).encaps pk) :
          [HasQuery _ (AddWriterT ℕ _)] → AddWriterT ℕ _ _))
        runtime =
      2 :=
  HasQuery.expectedQueries_eq_of_usesExactlyQueries
    (encaps_usesExactlyTwoQueries (runtime := runtime) (pke := pke) (kdInput := kdInput) (policy :=
      policy) (pk := pk))


-- @@ L328-343 expanded
/-- If deterministic decryption fails immediately, U-transform decapsulation incurs zero weighted
query cost. -/
theorem decaps_usesZeroQueryCost_of_decrypt_eq_none {ω : Type} [AddMonoid ω]
    (runtime : QueryImpl (UTransform.hashOracleSpec M R KD K) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C) (kdInput : M → C → KD)
    (policy : FujisakiOkamoto.RejectionPolicy K C) (pk : PK) (sk : SK) (fb : policy.FallbackState)
    (c : C) (costFn : (UTransform.hashOracleSpec M R KD K).Domain → ω)
    (hdec : pke.decrypt sk c = none) :
    HasQuery.UsesCostExactly
      (((fun [HasQuery _ _] => (UTransform pke kdInput policy).decaps ((pk, sk), fb) c) :
        [HasQuery _ (AddWriterT _ _)] → AddWriterT _ _ _))
      runtime costFn 0 :=
  by
  rw [HasQuery.UsesCostExactly]
  simp [HasQuery.Program.withAddCost, UTransform, FujisakiOkamoto.scheme, hdec,
    AddWriterT.hasCost_iff, AddWriterT.outputs, AddWriterT.costs]


-- @@ L345-384 expanded
/-- Under per-family upper bounds on the two U-transform oracle families, decapsulation incurs
weighted query cost at most the sum of those bounds. -/
theorem decaps_usesWeightedQueryCostAtMost {ω : Type} [AddCommMonoid ω] [PartialOrder ω]
    [IsOrderedAddMonoid ω] [CanonicallyOrderedAdd ω] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    (runtime : QueryImpl (UTransform.hashOracleSpec M R KD K) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C) (kdInput : M → C → KD)
    (policy : FujisakiOkamoto.RejectionPolicy K C) (pk : PK) (sk : SK) (fb : policy.FallbackState)
    (c : C) (costFn : (UTransform.hashOracleSpec M R KD K).Domain → ω) (wCoins wKey : ω)
    (hCoins : ∀ msg, costFn (Sum.inl msg) ≤ wCoins) (hKeys : ∀ kd, costFn (Sum.inr kd) ≤ wKey) :
    HasQuery.UsesCostAtMost
      (((fun [HasQuery _ _] => (UTransform pke kdInput policy).decaps ((pk, sk), fb) c) :
        [HasQuery _ (AddWriterT _ _)] → AddWriterT _ _ _))
      runtime costFn (wCoins + wKey) :=
  by
  rw [HasQuery.UsesCostAtMost]
  cases hdec : pke.decrypt sk c with
  | none =>
    exact
      HasQuery.usesCostAtMost_of_usesCostExactly
        (decaps_usesZeroQueryCost_of_decrypt_eq_none (runtime := runtime) (pke := pke) (kdInput :=
          kdInput) (policy := policy) (pk := pk) (sk := sk) (fb := fb) (c := c) (costFn := costFn)
          hdec)
        zero_le
  | some msg =>
    let := (runtime.withAddCost costFn).toHasQuery
    simp only [HasQuery.Program.withAddCost, UTransform, FujisakiOkamoto.scheme, hdec]
    refine AddWriterT.pathwiseCostAtMost_bind (w₁ := wCoins) (w₂ := wKey) ?_ ?_
    ·
      exact
        HasQuery.usesCostAtMost_query_of_le (runtime := runtime) (costFn := costFn) (t :=
          Sum.inl msg) (b := wCoins) (hCoins msg)
    · intro r
      split
      · rw [bind_pure_comp]
        exact
          AddWriterT.pathwiseCostAtMost_map some
            (HasQuery.usesCostAtMost_query_of_le (runtime := runtime) (costFn := costFn) (t :=
              Sum.inr (kdInput msg c)) (b := wKey) (hKeys (kdInput msg c)))
      ·
        exact
          AddWriterT.pathwiseCostAtMost_mono
            (AddWriterT.pathwiseCostAtMost_pure (m := m) (policy.onReject fb c : Option K)) zero_le


-- @@ L386-406 expanded
/-- If deterministic decryption fails immediately, decapsulation has expected weighted query cost
`0`. -/
theorem decaps_expectedQueryCost_eq_zero_of_decrypt_eq_none {ω : Type} [AddMonoid ω] [Preorder ω]
    [MonadLiftT m PMF] [LawfulMonadLiftT m PMF] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    [EvalDistCompatible m] (runtime : QueryImpl (UTransform.hashOracleSpec M R KD K) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C) (kdInput : M → C → KD)
    (policy : FujisakiOkamoto.RejectionPolicy K C) (pk : PK) (sk : SK) (fb : policy.FallbackState)
    (c : C) (costFn : (UTransform.hashOracleSpec M R KD K).Domain → ω) (val : ω → ENNReal)
    (hval : Monotone val) (hdec : pke.decrypt sk c = none) :
    HasQuery.expectedQueryCost
        (((fun [HasQuery _ _] => (UTransform pke kdInput policy).decaps ((pk, sk), fb) c) :
          [HasQuery _ (AddWriterT _ _)] → AddWriterT _ _ _))
        runtime costFn val =
      val 0 :=
  HasQuery.expectedQueryCost_eq_of_usesCostExactly
    (decaps_usesZeroQueryCost_of_decrypt_eq_none (runtime := runtime) (pke := pke) (kdInput :=
      kdInput) (policy := policy) (pk := pk) (sk := sk) (fb := fb) (c := c) (costFn := costFn) hdec)
    hval


-- @@ L408-431 expanded
/-- Expected weighted query cost of U-transform decapsulation is bounded by the sum of the
per-family bounds. -/
theorem decaps_expectedQueryCost_le {ω : Type} [AddCommMonoid ω] [PartialOrder ω]
    [IsOrderedAddMonoid ω] [CanonicallyOrderedAdd ω] [MonadLiftT m PMF] [LawfulMonadLiftT m PMF]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]
    (runtime : QueryImpl (UTransform.hashOracleSpec M R KD K) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C) (kdInput : M → C → KD)
    (policy : FujisakiOkamoto.RejectionPolicy K C) (pk : PK) (sk : SK) (fb : policy.FallbackState)
    (c : C) (costFn : (UTransform.hashOracleSpec M R KD K).Domain → ω) (wCoins wKey : ω)
    (val : ω → ENNReal) (hval : Monotone val) (hCoins : ∀ msg, costFn (Sum.inl msg) ≤ wCoins)
    (hKeys : ∀ kd, costFn (Sum.inr kd) ≤ wKey) :
    HasQuery.expectedQueryCost
        (((fun [HasQuery _ _] => (UTransform pke kdInput policy).decaps ((pk, sk), fb) c) :
          [HasQuery _ (AddWriterT _ _)] → AddWriterT _ _ _))
        runtime costFn val ≤
      val (wCoins + wKey) :=
  HasQuery.expectedQueryCost_le_of_usesCostAtMost
    (decaps_usesWeightedQueryCostAtMost (runtime := runtime) (pke := pke) (kdInput := kdInput)
      (policy := policy) (pk := pk) (sk := sk) (fb := fb) (c := c) (costFn := costFn) (wCoins :=
      wCoins) (wKey := wKey) hCoins hKeys)
    hval


-- @@ L433-445 expanded
/-- Unit-cost specialization: U-transform decapsulation makes at most two oracle queries. -/
theorem decaps_usesAtMostTwoQueries [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    (runtime : QueryImpl (UTransform.hashOracleSpec M R KD K) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C) (kdInput : M → C → KD)
    (policy : FujisakiOkamoto.RejectionPolicy K C) (pk : PK) (sk : SK) (fb : policy.FallbackState)
    (c : C) :
    HasQuery.UsesAtMostQueries
      (((fun [HasQuery _ _] => (UTransform pke kdInput policy).decaps ((pk, sk), fb) c) :
        [HasQuery _ (AddWriterT ℕ _)] → AddWriterT ℕ _ _))
      runtime 2 :=
  by
  rw [HasQuery.UsesAtMostQueries, HasQuery.Program.withUnitCost_eq_withAddCost]
  exact
    decaps_usesWeightedQueryCostAtMost (ω := ℕ) (runtime := runtime) (pke := pke) (kdInput :=
      kdInput) (policy := policy) (pk := pk) (sk := sk) (fb := fb) (c := c) (costFn := fun _ ↦ 1)
      (wCoins := 1) (wKey := 1) (hCoins := fun _ ↦ le_rfl) (hKeys := fun _ ↦ le_rfl)


-- @@ L447-459 expanded
/-- Expected query count of U-transform decapsulation is at most `2`. -/
theorem decaps_expectedQueries_le_two [MonadLiftT m PMF] [LawfulMonadLiftT m PMF]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]
    (runtime : QueryImpl (UTransform.hashOracleSpec M R KD K) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C) (kdInput : M → C → KD)
    (policy : FujisakiOkamoto.RejectionPolicy K C) (pk : PK) (sk : SK) (fb : policy.FallbackState)
    (c : C) :
    HasQuery.expectedQueries
        (((fun [HasQuery _ _] => (UTransform pke kdInput policy).decaps ((pk, sk), fb) c) :
          [HasQuery _ (AddWriterT ℕ _)] → AddWriterT ℕ _ _))
        runtime ≤
      2 :=
  HasQuery.expectedQueries_le_of_usesAtMostQueries
    (decaps_usesAtMostTwoQueries (runtime := runtime) (pke := pke) (kdInput := kdInput) (policy :=
      policy) (pk := pk) (sk := sk) (fb := fb) (c := c))


-- @@ L461-461 verbatim
end costAccounting


-- @@ L463-471 verbatim
/-- Runtime bundle for the two-RO U-transform oracle world. -/
noncomputable def runtime
    {M R KD K : Type}
    [DecidableEq M] [DecidableEq KD] [SampleableType R] [SampleableType K] :
    ProbCompRuntime (OracleComp (oracleSpec M R KD K)) where
  toSPMFSemantics := SPMFSemantics.withStateOracle
    (hashImpl := queryImpl (M := M) (R := R) (KD := KD) (K := K))
    ((∅, ∅) : QueryCache M R KD K)
  toProbCompLift := ProbCompLift.ofMonadLift _


-- @@ L473-473 verbatim
end UTransform
