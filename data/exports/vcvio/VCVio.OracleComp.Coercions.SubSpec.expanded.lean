/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.OracleComp.EvalDist
public import VCVio.OracleComp.SimSemantics.SimulateQ
public import PolyFun.PFunctor.Lens.Cartesian


-- @@ L12-45 verbatim
/-!
# Coercions Between Computations With Additional Oracles

This file defines the `SubSpec` relation between pairs of `OracleSpec`s. An
instance `spec ⊂ₒ superSpec` packages the data of a polynomial-functor lens
`PFunctor.Lens spec.toPFunctor superSpec.toPFunctor` between the underlying
`PFunctor`s, given by

* `onQuery : spec.Domain → superSpec.Domain` --- forward translation on query
  inputs (oracle indices), and
* `onResponse : (t : spec.Domain) → superSpec.Range (onQuery t) → spec.Range t`
  --- fiberwise backward translation on query responses.

By the Yoneda lemma this lens data is in bijection with natural transformations
`OracleQuery spec → OracleQuery superSpec`. The class therefore `extends
MonadLift (OracleQuery spec) (OracleQuery superSpec)`. Concrete instances
spell `monadLift` out alongside the lens data and discharge the
propositional coherence `liftM_eq_lift` (typically `rfl`); see the class
docstring for why the `monadLift` field is not defaulted.

We use the notation `spec ⊂ₒ spec'` to represent this inclusion. The
non-inclusive subset symbol reflects that we avoid defining `SubSpec`
reflexively, since `MonadLiftT.refl` already handles the identity case.

`LawfulSubSpec` refines `SubSpec` with the requirement that `onResponse` is
bijective on every fiber, i.e. that the underlying lens is **cartesian** in
the sense of `PFunctor.Lens.IsCartesian`. This is *strictly weaker* than
`PFunctor.Lens.Equiv` (which would also require `onQuery` to be a bijection,
ruling out the basic case `spec ⊂ₒ (spec + spec')` where `onQuery = Sum.inl`).
Cartesianness is exactly the condition needed to preserve the uniform
distribution under lifting (`evalSPMF_liftComp`); see
`LawfulSubSpec.toLens_isCartesian` for the bridge to the lens-level
predicate.
-/


-- @@ L47-47 verbatim
@[expose] public section


-- @@ L49-49 verbatim
open OracleSpec OracleComp ENNReal


-- @@ L51-51 verbatim
universe u u' v v' w w'


-- @@ L53-53 verbatim
open scoped OracleSpec.PrimitiveQuery


-- @@ L55-56 verbatim
variable {ι : Type u} {τ : Type v}
  {spec : OracleSpec ι} {superSpec : OracleSpec τ} {α β γ : Type w}


-- @@ L58-58 verbatim
namespace OracleSpec


-- @@ L60-93 verbatim
/-- Inclusion of one set of oracles into another, packaged as a polynomial-functor
lens between the underlying `OracleSpec`s. Carries the forward translation
`onQuery` on query inputs and the fiberwise backward translation `onResponse`
on query responses, plus the resulting `MonadLift` action.

We `extends MonadLift (OracleQuery spec) (OracleQuery superSpec)` so that
typeclass synthesis can derive `MonadLift` (and therefore `MonadLiftT`)
through the structure projection `SubSpec.toMonadLift`. The `monadLift`
field is **not** defaulted: each concrete `SubSpec` instance must spell it
out, alongside `onQuery` / `onResponse`, and discharge the propositional
coherence `liftM_eq_lift` (typically by `rfl`).

Spelling `monadLift` out explicitly (rather than defaulting it from the
lens data) is what makes the lifted query fully reduce during `rw` / `simp`
pattern matching against lemmas like `probEvent_liftComp`. A defaulted
`monadLift` field becomes opaque to `isDefEq` once it travels through the
`MonadLiftT` instance chain, which silently breaks rewriting.

Informally, `spec ⊂ₒ superSpec` says that any query to an oracle of `spec`
can be perfectly simulated by a query to an oracle of `superSpec`. We avoid
the built-in `Subset` notation because we care about the actual data of the
mapping (it is needed when defining type coercions), not just its existence. -/
class SubSpec (spec : OracleSpec.{u, w} ι) (superSpec : OracleSpec.{v, w} τ)
    extends MonadLift (OracleQuery spec) (OracleQuery superSpec) where
  /-- Forward translation on query inputs (oracle indices). -/
  onQuery : spec.Domain → superSpec.Domain
  /-- Fiberwise backward translation on query responses. -/
  onResponse : (t : spec.Domain) → superSpec.Range (onQuery t) → spec.Range t
  /-- Coherence between the `MonadLift` action and the lens data: lifting a
  query is the lens applied to that query. Concrete instances supply
  `monadLift` directly in the lens form, making this `rfl`. -/
  liftM_eq_lift : ∀ {β : Type w} (q : OracleQuery spec β),
      monadLift q = ⟨onQuery q.input, q.cont ∘ onResponse q.input⟩ := by
    intros; rfl


-- @@ L95-95 verbatim
@[inherit_doc] infix : 50 " ⊂ₒ " => SubSpec


-- @@ L97-97 verbatim
namespace SubSpec


-- @@ L99-99 verbatim
variable {κ : Type w'} {spec₃ : OracleSpec κ}


-- @@ L101-106 verbatim
/-- The lens action on a single query: forward on the input, post-compose the
backward fiber on the continuation. Used as the canonical reduced form of
`liftM q` for proofs that need to inspect the resulting query. -/
@[reducible] def liftQuery [h : SubSpec spec superSpec] (q : OracleQuery spec α) :
    OracleQuery superSpec α :=
  ⟨h.onQuery q.input, q.cont ∘ h.onResponse q.input⟩


-- @@ L108-117 verbatim
/-- The polynomial-functor lens between the underlying `PFunctor`s carried by
a `SubSpec` instance. This is the lens-level view of the data; concrete
properties (like cartesianness via `LawfulSubSpec`) are stated on this lens.

The other half of the data, `monadLift`, is fixed by `liftM_eq_lift` to be
the standard action of this lens on `OracleQuery`. -/
def toLens (h : SubSpec spec superSpec) :
    PFunctor.Lens spec.toPFunctor superSpec.toPFunctor where
  toFunA := h.onQuery
  toFunB := h.onResponse


-- @@ L119-120 verbatim
@[simp] lemma toLens_toFunA (h : SubSpec spec superSpec) :
    h.toLens.toFunA = h.onQuery := rfl


-- @@ L122-123 verbatim
@[simp] lemma toLens_toFunB (h : SubSpec spec superSpec) :
    h.toLens.toFunB = h.onResponse := rfl


-- @@ L125-132 expanded
/-- Transitivity of `SubSpec`: lens composition. -/
@[reducible]
def trans (h₁ : SubSpec spec superSpec) (h₂ : SubSpec superSpec spec₃) : SubSpec spec spec₃
    where
  monadLift
    q :=
    ⟨h₂.onQuery (h₁.onQuery q.input),
      q.cont ∘ h₁.onResponse q.input ∘ h₂.onResponse (h₁.onQuery q.input)⟩
  onQuery t := h₂.onQuery (h₁.onQuery t)
  onResponse t r := h₁.onResponse t (h₂.onResponse (h₁.onQuery t) r)


-- @@ L134-135 expanded
@[simp]
lemma trans_toLens (h₁ : SubSpec spec superSpec) (h₂ : SubSpec superSpec spec₃) :
    (SubSpec.trans h₁ h₂).toLens = h₂.toLens ∘ₗ h₁.toLens :=
  rfl


-- @@ L137-137 verbatim
end SubSpec


-- @@ L139-158 verbatim
/-- `LawfulSubSpec` extends `SubSpec` with the requirement that the backward
translation `onResponse` is bijective on every fiber. Equivalently: the
underlying lens `SubSpec.toLens` is *cartesian* in the sense of
`PFunctor.Lens.IsCartesian`, i.e. it is a fiberwise isomorphism over an
arbitrary forward map on positions.

This is *strictly weaker* than `PFunctor.Lens.Equiv`, which would also force
`onQuery` to be a bijection. We intentionally only require fiberwise
bijectivity because the canonical `SubSpec` instances embed a small spec
into a larger one (e.g. `spec₁ ⊂ₒ (spec₁ + spec₂)` with `onQuery = Sum.inl`),
and these embeddings are essential to the API.

Cartesianness is exactly what is needed to preserve the uniform distribution
under the lift: see `evalSPMF_liftM_query` and the bridge
`LawfulSubSpec.toLens_isCartesian`. -/
class LawfulSubSpec (spec : OracleSpec.{u, w} ι) (superSpec : OracleSpec.{v, w} τ)
    [h : SubSpec spec superSpec] : Prop where
  /-- The backward translation is bijective on every fiber. -/
  onResponse_bijective (t : spec.Domain) :
    Function.Bijective (h.onResponse t)


-- @@ L160-162 verbatim
/-- Lawful oracle-spec inclusion: a `SubSpec` whose response translation is
bijective on every fiber. -/
macro:50 lhs:term " ˡ⊂ₒ " rhs:term : term => `(LawfulSubSpec $lhs $rhs)


-- @@ L164-164 verbatim
namespace LawfulSubSpec


-- @@ L166-167 expanded
variable {ι : Type u} {τ : Type v} {spec : OracleSpec ι} {superSpec : OracleSpec τ}
  [h : SubSpec spec superSpec] [LawfulSubSpec spec superSpec]


-- @@ L169-173 verbatim
/-- The lens-level statement of `LawfulSubSpec`: the underlying
`PFunctor.Lens` is cartesian. This makes the dictionary between the
oracle-spec layer and the polynomial-functor lens layer explicit. -/
lemma toLens_isCartesian : h.toLens.IsCartesian := fun t =>
  onResponse_bijective (h := h) t


-- @@ L175-186 verbatim
/-- Pushing the uniform distribution on `superSpec.Range` through the lens's
backward fiber recovers the uniform distribution on `spec.Range`. Load-bearing
for `evalSPMF_liftComp` below. -/
lemma evalSPMF_liftM_query [superSpec.Fintype] [superSpec.Inhabited]
    [spec.Fintype] [spec.Inhabited] (t : spec.Domain) :
    (PMF.uniformOfFintype (superSpec.Range
      ((liftM (n := OracleQuery superSpec) (spec.query t)).input))).map
      ((liftM (n := OracleQuery superSpec) (spec.query t)).cont) =
      PMF.uniformOfFintype (spec.Range t) := by
  rw [show (liftM (spec.query t) : OracleQuery superSpec (spec.Range t)) =
      ⟨h.onQuery t, h.onResponse t⟩ from h.liftM_eq_lift _]
  exact PMF.uniformOfFintype_map_of_bijective _ (onResponse_bijective t)


-- @@ L188-188 verbatim
end LawfulSubSpec


-- @@ L190-203 verbatim
/-- Two oracle-spec inclusions into the same ambient spec have disjoint query
images.

This is stronger than `LawfulSubSpec`: lawfulness preserves the distribution of
responses under lifting, while disjointness says the two lifted query namespaces
do not overlap inside the ambient interface. -/
class DisjointSubSpec
    {ι₁ : Type u} {ι₂ : Type v} {τ : Type w'}
    (spec₁ : OracleSpec.{u, w} ι₁) (spec₂ : OracleSpec.{v, w} ι₂)
    (superSpec : OracleSpec.{w', w} τ)
    [h₁ : SubSpec spec₁ superSpec] [h₂ : SubSpec spec₂ superSpec] : Prop where
  /-- The two forward query maps have disjoint images. -/
  disjoint_onQuery (t₁ : spec₁.Domain) (t₂ : spec₂.Domain) :
    h₁.onQuery t₁ ≠ h₂.onQuery t₂


-- @@ L205-207 verbatim
/-- Oracle-spec inclusions with disjoint query images in an ambient interface. -/
macro:50 lhs:term " ⊥ₒ[" ambient:term "] " rhs:term : term =>
  `(DisjointSubSpec $lhs $rhs $ambient)


-- @@ L209-209 verbatim
end OracleSpec



-- @@ L212-212 verbatim
namespace OracleComp


-- @@ L214-214 verbatim
section liftComp


-- @@ L216-221 verbatim
/-- Lift a computation from `spec` to `superSpec` using a `SubSpec` instance on queries.
Usually `liftM` should be preferred but this can allow more explicit annotation. -/
def liftComp (mx : OracleComp spec α) (superSpec : OracleSpec τ)
    [h : MonadLiftT (OracleQuery spec) (OracleQuery superSpec)] :
    OracleComp superSpec α :=
    simulateQ (fun t => liftM (spec.query t)) mx


-- @@ L223-224 verbatim
variable (superSpec : OracleSpec τ)
    [h : MonadLiftT (OracleQuery spec) (OracleQuery superSpec)]


-- @@ L226-228 verbatim
@[grind =, aesop unsafe norm]
lemma liftComp_def (mx : OracleComp spec α) : liftComp mx superSpec =
    simulateQ (fun t => liftM (spec.query t)) mx := rfl


-- @@ L230-231 verbatim
@[simp]
lemma liftComp_pure (x : α) : liftComp (pure x : OracleComp spec α) superSpec = pure x := rfl


-- @@ L233-237 verbatim
@[simp]
lemma liftComp_query (q : OracleQuery spec α) :
    liftComp (q : OracleComp spec _) superSpec =
      q.cont <$> (liftM (spec.query q.input) : OracleComp superSpec _) := by
  simp [liftComp]


-- @@ L239-243 verbatim
@[simp]
lemma liftComp_bind (mx : OracleComp spec α) (ob : α → OracleComp spec β) :
    liftComp (mx >>= ob) superSpec =
      liftComp mx superSpec >>= fun x ↦ liftComp (ob x) superSpec := by
  grind


-- @@ L245-250 verbatim
@[simp]
lemma liftComp_self (mx : OracleComp spec α) :
    liftComp mx spec = mx := by
  induction mx using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind t k ih => simp [liftComp_bind, liftComp_query, ih]


-- @@ L252-255 verbatim
@[simp]
lemma liftComp_map (mx : OracleComp spec α) (f : α → β) :
    liftComp (f <$> mx) superSpec = f <$> liftComp mx superSpec := by
  simp [liftComp]


-- @@ L257-263 verbatim
/-- `bind`-`pure` form of `liftComp_map`, matching the term shape produced by `do`-notation
(`do let a ← oa; pure (f a)`) before any `bind_pure_comp` normalization. -/
lemma liftComp_bind_pure (oa : OracleComp spec α) (f : α → β) :
    OracleComp.liftComp (do let a ← oa; pure (f a)) superSpec =
      f <$> OracleComp.liftComp oa superSpec := by
  rw [liftComp_bind, map_eq_bind_pure_comp]
  rfl


-- @@ L265-279 verbatim
/-- One-directional, assumption-light variant of `mem_support_liftComp_iff`: under just a
query-level lift (no `SubSpec` or lawfulness assumptions), the support of a lifted computation
is bounded by the support of the original. The reverse inclusion can fail without lawfulness,
since an arbitrary embedding need not reach all responses of the original oracles. -/
lemma mem_support_of_mem_support_liftComp (oa : OracleComp spec α) (x : α) :
    x ∈ support (oa.liftComp superSpec) → x ∈ support oa := by
  intro hx
  induction oa using OracleComp.inductionOn generalizing x with
  | pure y =>
      simpa using hx
  | query_bind q oa ih =>
      rw [OracleComp.liftComp_bind, mem_support_bind_iff] at hx
      rw [mem_support_bind_iff]
      obtain ⟨u, _hu, hx⟩ := hx
      exact ⟨u, OracleComp.mem_support_query q u, ih u x hx⟩


-- @@ L281-284 verbatim
@[simp]
lemma liftComp_seq (og : OracleComp spec (α → β)) (mx : OracleComp spec α) :
    liftComp (og <*> mx) superSpec = liftComp og superSpec <*> liftComp mx superSpec := by
  simp [liftComp, monad_norm]


-- @@ L286-289 verbatim
@[simp]
lemma liftComp_seqLeft (mx : OracleComp spec α) (my : OracleComp spec β) :
    liftComp (mx <* my) superSpec = liftComp mx superSpec <* liftComp my superSpec := by
  simp [seqLeft_eq]


-- @@ L291-299 verbatim
@[simp]
lemma liftComp_seqRight (mx : OracleComp spec α) (my : OracleComp spec β) :
    liftComp (mx *> my) superSpec = liftComp mx superSpec *> liftComp my superSpec := by
  simp [seqRight_eq]

-- NOTE: `liftComp_failure` cannot be stated for `OracleComp spec` because `failure` only exists
-- in `OptionT (OracleComp spec)`, not in `OracleComp spec` itself. `OracleComp` is
-- `PFunctor.FreeM` which has no `Alternative` instance. Use `liftM_failure` in the OptionT
-- section below for the analogous result.


-- @@ L301-301 verbatim
end liftComp


-- @@ L303-303 verbatim
section liftComp_evalSPMF


-- @@ L305-306 verbatim
variable {ι : Type u} {τ : Type v}
  {spec : OracleSpec ι} {superSpec : OracleSpec τ} {α : Type w}

-- @@ L307-308 expanded
variable [spec.IsUniformSpec] [superSpec.IsUniformSpec] [h : SubSpec spec superSpec]
  [LawfulSubSpec spec superSpec]


-- @@ L310-321 expanded
@[grind =]
lemma evalSPMF_liftComp (mx : OracleComp spec α) : evalSPMF (liftComp mx superSpec) = evalSPMF mx :=
  by
  induction mx using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t mx
    ih =>
    simp only [liftComp_bind, liftComp_query, OracleQuery.cont_query, id_map,
      OracleQuery.input_query, evalSPMF_bind, ih]
    congr 1
    rw [show
        (liftM (OracleSpec.query t) : OracleComp superSpec (spec.Range t)) =
          liftM (liftM (spec.query t) : OracleQuery superSpec _)
        from rfl,
      evalSPMF_liftM, evalSPMF_query]
    exact congrArg liftM (LawfulSubSpec.evalSPMF_liftM_query t)


-- @@ L323-325 expanded
@[grind =]
lemma probOutput_liftComp (mx : OracleComp spec α) (x : α) :
    probOutput (liftComp mx superSpec) x = probOutput mx x := by
  rw [probOutput_def, probOutput_def, evalSPMF_liftComp]


-- @@ L327-329 expanded
@[grind =]
lemma probEvent_liftComp (mx : OracleComp spec α) (p : α → Prop) :
    probEvent (liftComp mx superSpec) p = probEvent mx p := by
  simp only [probEvent_eq_tsum_indicator, probOutput_liftComp]


-- @@ L331-334 expanded
omit [LawfulSubSpec spec superSpec] in
lemma probFailure_liftComp (mx : OracleComp spec α) :
    probFailure (liftComp mx superSpec) = probFailure mx := by
  rw [probFailure_eq_zero, probFailure_eq_zero]


-- @@ L336-336 verbatim
end liftComp_evalSPMF


-- @@ L338-338 verbatim
section liftComp_support


-- @@ L340-342 expanded
variable {ι : Type u} {τ : Type v} {spec : OracleSpec ι} {superSpec : OracleSpec τ} {α : Type w}
  [h : SubSpec spec superSpec] [LawfulSubSpec spec superSpec]


-- @@ L344-361 verbatim
/-- Support is preserved by `liftComp`: lifting a computation to a larger oracle spec
does not change which outputs are reachable. This is the support analogue of
`evalSPMF_liftComp`. -/
lemma support_liftComp (mx : OracleComp spec α) :
    support (liftComp mx superSpec) = support mx := by
  simp only [liftComp]
  induction mx using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t oa ih =>
    simp only [simulateQ_query_bind, support_bind, OracleQuery.input_query, monadLift_self, ih]
    have hs : support (liftM (OracleSpec.query t) : OracleComp superSpec (spec.Range t)) =
        Set.univ := by
      change support ((liftM : OracleQuery superSpec _ → OracleComp superSpec _)
        ((monadLift : OracleQuery spec _ → OracleQuery superSpec _) (OracleSpec.query t))) = _
      rw [support_liftM, show (monadLift (OracleSpec.query t) : OracleQuery superSpec _) =
        ⟨h.onQuery t, h.onResponse t⟩ from h.liftM_eq_lift (OracleSpec.query t)]
      exact (LawfulSubSpec.onResponse_bijective (h := h) t).surjective.range_eq
    rw [hs]; simp


-- @@ L363-365 verbatim
@[grind =] lemma mem_support_liftComp_iff (mx : OracleComp spec α) (x : α) :
    x ∈ support (liftComp mx superSpec) ↔ x ∈ support mx := by
  simp [support_liftComp]


-- @@ L367-367 verbatim
end liftComp_support


-- @@ L369-392 verbatim
/-- Extend a lifting on `OracleQuery` to a lifting on `OracleComp`.

Registered as a low-priority `MonadLift` (not `MonadLiftT`) so that:

* For `spec = superSpec`, Lean's built-in `MonadLiftT.refl` (which is
  definitionally `id`) wins typeclass resolution. This is what
  `Std.Do.Spec.UnfoldLift.monadLift_refl` (a `rfl`-based lemma) needs in
  order to peel off spurious self-lifts inside `mvcgen`-elaborated terms.

* For `MonadLiftT (OracleQuery spec) (OracleComp superSpec)`, the built-in
  high-priority `MonadLift (OracleQuery superSpec) (OracleComp superSpec)` is
  tried first by `monadLiftTrans` and succeeds via the `SubSpec` chain on
  `OracleQuery`, never reaching this instance. Single-query lifts therefore
  go through the standard "lift query then embed" path with no spurious
  walk through `liftComp`.

* For `MonadLiftT (OracleComp spec) (OracleComp superSpec)` with
  `spec ≠ superSpec`, the high-priority built-in fails (no
  `MonadLiftT (OracleComp _) (OracleQuery _)`), Lean backtracks to this
  low-priority instance, and the recursive subgoal collapses via
  `MonadLiftT.refl`. The result is a single `liftComp mx superSpec`. -/
instance (priority := low) [MonadLift (OracleQuery spec) (OracleQuery superSpec)] :
    MonadLift (OracleComp spec) (OracleComp superSpec) where
  monadLift mx := liftComp mx superSpec


-- @@ L394-397 verbatim
/-- We choose to actively rewrite `liftComp` as `liftM` to enable `LawfulMonadLift` lemmas. -/
@[simp, aesop safe norm]
lemma liftComp_eq_liftM [MonadLift (OracleQuery spec) (OracleQuery superSpec)]
    (mx : OracleComp spec α) : liftComp mx superSpec = (liftM mx : OracleComp superSpec α) := rfl


-- @@ L399-417 verbatim
/-- Peel the outermost step off a *chained* `OracleComp`-level lift: a `liftM` whose
`MonadLiftT (OracleComp spec) (OracleComp spec₃)` instance is the transitive composition of
the query-keyed `MonadLift (OracleComp superSpec) (OracleComp spec₃)` step with a remaining
chain `MonadLiftT (OracleComp spec) (OracleComp superSpec)` is the `liftComp` of the
remaining lift. Typeclass resolution builds exactly this shape (via
`instMonadLiftTOfMonadLift`) when lifting across two or more `OracleSpec.add` layers, e.g.
`OracleComp spec₂ → OracleComp (spec + (spec₁ + spec₂))` through the intermediate
`spec + spec₂`. None of the single-step lemmas (`liftComp_eq_liftM`, `liftComp_query`, …)
can engage such a chain directly, since their statements bake in the one-step instance.

Not `@[simp]`: with `spec = superSpec` the remaining chain can be `MonadLiftT.refl`, and the
right-hand side would then re-match the left-hand side. Use via explicit `rw`, then rewrite
the inner lift with `← liftComp_eq_liftM` and proceed with the `liftComp` API. -/
lemma liftM_eq_liftComp_liftM {κ : Type*} {spec₃ : OracleSpec κ}
    [MonadLift (OracleQuery superSpec) (OracleQuery spec₃)]
    [MonadLiftT (OracleComp spec) (OracleComp superSpec)]
    (mx : OracleComp spec α) :
    (liftM mx : OracleComp spec₃ α) =
      liftComp (liftM mx : OracleComp superSpec α) spec₃ := rfl


-- @@ L419-422 verbatim
instance [MonadLift (OracleQuery spec) (OracleQuery superSpec)] :
    LawfulMonadLift (OracleComp spec) (OracleComp superSpec) where
  monadLift_pure x := liftComp_pure superSpec x
  monadLift_bind mx my := liftComp_bind superSpec mx my


-- @@ L424-430 verbatim
/-- Self-lift on `OracleComp` is definitionally `id`, supplied by Lean's
built-in `MonadLiftT.refl` thanks to the low-priority `MonadLift` instance
above (which causes the parametric path to lose typeclass resolution to
`MonadLiftT.refl` when `spec = superSpec`). -/
@[simp]
lemma monadLift_eq_self {α} (mx : OracleComp spec α) :
    (monadLift mx : OracleComp spec α) = mx := rfl


-- @@ L432-437 verbatim
/-! Regression smoke-tests for the instance-priority invariants above. The
`rfl` proofs are the load-bearing signal: if priority drifts so that the
parametric `MonadLift` beats `MonadLiftT.refl`, the self-lift stops being
definitionally `id` and the `rfl` below breaks. Similarly, the
`MonadLiftT` synthesis check guards against future refactors that would
remove the transitive lift chain. -/


-- @@ L439-440 verbatim
example (mx : OracleComp spec Nat) :
    (monadLift mx : OracleComp spec Nat) = mx := rfl


-- @@ L442-443 verbatim
example : MonadLiftT (OracleComp spec) (OracleComp spec) :=
  inferInstance


-- @@ L445-451 verbatim
example [MonadLift (OracleQuery spec) (OracleQuery superSpec)] :
    MonadLiftT (OracleComp spec) (OracleComp superSpec) :=
  inferInstance

-- NOTE: With constant universal levels it is fairly easy to abstract the below in a class
-- Getting a similar level of generality as the manual instances below would be useful,
--    might require some more general framework about monad transformers.


-- @@ L453-453 verbatim
section OptionT


-- @@ L455-457 expanded
instance [MonadLift (OracleQuery spec) (OracleQuery superSpec)] :
    MonadLift (OptionT (OracleComp spec)) (OptionT (OracleComp superSpec)) where
  monadLift mx := OptionT.mk (simulateQ (fun t => liftM (OracleSpec.query t)) (OptionT.run mx))


-- @@ L459-463 expanded
@[simp]
lemma liftM_OptionT_eq [MonadLift (OracleQuery spec) (OracleQuery superSpec)]
    (mx : OptionT (OracleComp spec) α) :
    (liftM mx : OptionT (OracleComp superSpec) α) =
      let impl : QueryImpl spec (OracleComp superSpec) := fun t => liftM (OracleSpec.query t)
      simulateQ impl mx :=
  rfl


-- @@ L465-467 verbatim
lemma liftM_failure [MonadLift (OracleQuery spec) (OracleQuery superSpec)] :
    (liftM (failure : OptionT (OracleComp spec) α) : OptionT (OracleComp superSpec) α) =
      failure := rfl


-- @@ L469-476 verbatim
instance [MonadLift (OracleQuery spec) (OracleQuery superSpec)] :
    LawfulMonadLift (OptionT (OracleComp spec)) (OptionT (OracleComp superSpec)) where
  monadLift_pure _ := rfl
  monadLift_bind mx my := by
    apply OptionT.ext
    simp only [MonadLift.monadLift, OptionT.run_bind, Option.elimM, simulateQ_bind, OptionT.mk_bind,
      OptionT.run_monadLift, monadLift_self, OptionT.run_mk, bind_map_left, Option.elim_some]
    exact bind_congr fun x => by cases x <;> simp


-- @@ L478-492 verbatim
/-- Coherence: lifting an `OracleComp` to a superspec and then into `OptionT` via the standard
  `MonadLift` equals lifting directly through the transitive `MonadLiftT` chain (which goes
  through the `simulateQ`-based `OptionT` MonadLift instance). -/
@[simp]
lemma monadLift_liftM_OptionT [MonadLift (OracleQuery spec) (OracleQuery superSpec)]
    (mx : OracleComp spec α) :
    (monadLift (liftM mx : OracleComp superSpec α) : OptionT (OracleComp superSpec) α) =
    (liftM mx : OptionT (OracleComp superSpec) α) := by
  apply OptionT.ext
  simp only [OptionT.run_monadLift, monadLift_eq_self]
  conv_rhs => dsimp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift]
  simp only [OptionT.run_mk, OptionT.lift]
  rw [simulateQ_bind]
  simp only [simulateQ_pure, ← map_eq_pure_bind]
  rfl


-- @@ L494-494 verbatim
end OptionT


-- @@ L496-496 verbatim
section StateT


-- @@ L498-500 verbatim
instance {σ : Type _} [MonadLift (OracleQuery spec) (OracleQuery superSpec)] :
    MonadLift (StateT σ (OracleComp spec)) (StateT σ (OracleComp superSpec)) where
  monadLift mx := StateT.mk fun s => liftComp (StateT.run mx s) superSpec


-- @@ L502-505 verbatim
@[simp]
lemma liftM_StateT_eq {σ : Type _} [MonadLift (OracleQuery spec) (OracleQuery superSpec)]
    (mx : StateT σ (OracleComp spec) α) : (liftM mx : StateT σ (OracleComp superSpec) α) =
      StateT.mk fun s => liftM (StateT.run mx s) := rfl


-- @@ L507-507 verbatim
end StateT


-- @@ L509-509 verbatim
end OracleComp
