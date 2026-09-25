/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import VCVio.OracleComp.OracleComp
public import PolyFun.PFunctor.Handler.Instrumentation


-- @@ L13-20 verbatim
/-!
# Implementing Oracle Queries in Other Monads

This file defines a type `QueryImpl spec m` to represent implementations
of queries to `spec` in terms of the monad `m`.
It also provides the bridge between explicit `QueryImpl`s and the lightweight
`HasQuery` capability from `VCVio.OracleComp.HasQuery.Basic`.
-/


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
open OracleSpec OracleComp


-- @@ L26-26 verbatim
universe u v w


-- @@ L28-28 verbatim
open scoped OracleSpec.PrimitiveQuery


-- @@ L30-37 verbatim
/-- A monadic handler for the polynomial interface induced by `spec`.

Concretely, this maps every oracle input `x` to a computation returning an
answer of type `spec.Range x`. It extends first to `OracleQuery spec` by
applying the continuation, then to `OracleComp spec` by preserving `pure` and
`bind`; see `QueryImpl.mapQuery` and `simulateQ`. -/
@[reducible] def QueryImpl {ι} (spec : OracleSpec ι) (m : Type u → Type v) :=
  (x : spec.Domain) → m (spec.Range x)


-- @@ L39-39 verbatim
namespace QueryImpl


-- @@ L41-41 verbatim
variable {ι} {spec : OracleSpec ι} {m : Type u → Type v} {n : Type u → Type w}


-- @@ L43-45 verbatim
/-- `QueryImpl` is definitionally PolyFun's generic monadic handler for the
polynomial interface induced by an oracle specification. -/
theorem eq_handler : QueryImpl spec m = PFunctor.Handler m spec.toPFunctor := rfl


-- @@ L47-48 verbatim
instance [spec.Inhabited] [Pure m] : Inhabited (QueryImpl spec m) where
  default _ := pure default


-- @@ L50-52 verbatim
/-- Two query implementations are the same if they are the same on all query inputs. -/
@[ext] lemma ext {so so' : QueryImpl spec m}
    (h : ∀ x : spec.Domain, so x = so' x) : so = so' := funext h


-- @@ L54-57 verbatim
/-- Restrict an implementation of a sum specification to its left component. -/
def restrictLeft {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    (impl : QueryImpl (spec₁ + spec₂) m) : QueryImpl spec₁ m :=
  fun t ↦ impl (Sum.inl t)


-- @@ L59-62 verbatim
/-- Restrict an implementation of a sum specification to its right component. -/
def restrictRight {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    (impl : QueryImpl (spec₁ + spec₂) m) : QueryImpl spec₂ m :=
  fun t ↦ impl (Sum.inr t)


-- @@ L64-67 verbatim
/-- Applying a left restriction is the original implementation on a left input. -/
lemma restrictLeft_apply {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    (impl : QueryImpl (spec₁ + spec₂) m) (t : spec₁.Domain) :
    impl.restrictLeft t = impl (Sum.inl t) := rfl


-- @@ L69-72 verbatim
/-- Applying a right restriction is the original implementation on a right input. -/
lemma restrictRight_apply {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    (impl : QueryImpl (spec₁ + spec₂) m) (t : spec₂.Domain) :
    impl.restrictRight t = impl (Sum.inr t) := rfl


-- @@ L74-78 verbatim
/-- View a concrete query implementation as query capability in the same monad. This is useful
when instantiating a generic `HasQuery` construction directly inside an analysis monad such as
`StateT σ ProbComp` or `WriterT ω (OracleComp spec)`. -/
abbrev toHasQuery (impl : QueryImpl spec m) : HasQuery spec m :=
  ⟨impl⟩


-- @@ L80-82 verbatim
@[simp]
lemma toHasQuery_query (impl : QueryImpl spec m) (t : spec.Domain) :
    HasQuery.query (spec := spec) (m := m) (self := toHasQuery impl) t = impl t := rfl


-- @@ L84-87 verbatim
/-- Embed an oracle query into a new functor by applying the implementation to the input value
before applying the continuation of the element. -/
def mapQuery {α} [Functor m] (impl : QueryImpl spec m)
    (q : OracleQuery spec α) : m α := q.cont <$> impl q.input


-- @@ L89-91 expanded
@[simp]
lemma mapQuery_query [Functor m] [LawfulFunctor m] (impl : QueryImpl spec m) (t : spec.Domain) :
    impl.mapQuery (OracleSpec.query t) = impl t := by simp [mapQuery]


-- @@ L93-98 verbatim
/-- Reduce `mapQuery` on an explicit constructor-form query. Companion to `mapQuery_query`
for queries that arise from `SubSpec`-lift normalization (which produces
`OracleQuery.mk`/anonymous-constructor forms rather than `OracleSpec.query`). -/
@[simp] lemma mapQuery_mk {α} [Functor m] (impl : QueryImpl spec m)
    (t : spec.Domain) (f : spec.Range t → α) :
    impl.mapQuery (OracleQuery.mk t f) = f <$> impl t := rfl


-- @@ L100-100 verbatim
section liftTarget


-- @@ L102-105 verbatim
/-- Compatibility alias for the generic polynomial-handler target lift. -/
abbrev liftTarget (n : Type u → Type*) [MonadLiftT m n]
    (impl : QueryImpl spec m) : QueryImpl spec n :=
  PFunctor.Handler.liftTarget (P := spec.toPFunctor) n impl


-- @@ L107-109 verbatim
lemma liftTarget_apply (n : Type u → Type*) [MonadLiftT m n]
    (impl : QueryImpl spec m) (t : spec.Domain) : impl.liftTarget n t = liftM (impl t) := by
  exact PFunctor.Handler.liftTarget_apply (P := spec.toPFunctor) n impl t


-- @@ L111-114 verbatim
/-- Lifting an implementation to the original monad has no effect. -/
lemma liftTarget_self (impl : QueryImpl spec m) :
    impl.liftTarget m = impl :=
  PFunctor.Handler.liftTarget_self (P := spec.toPFunctor) impl


-- @@ L116-120 verbatim
@[simp] lemma mapQuery_liftTarget {α} (n : Type u → Type w)
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [MonadLiftT m n]
    [LawfulMonadLiftT m n] (impl : QueryImpl spec m) (q : OracleQuery spec α) :
    (impl.liftTarget n).mapQuery q = liftM (impl.mapQuery q) := by
  simp [mapQuery]


-- @@ L122-122 verbatim
end liftTarget


-- @@ L124-124 verbatim
section id


-- @@ L126-128 expanded
/-- Identity implementation for queries, sending `q : OracleQuery spec α` to itself. -/
protected def id (spec : OracleSpec ι) : QueryImpl spec (OracleQuery spec) :=
  OracleSpec.query


-- @@ L130-131 expanded
@[simp]
lemma id_apply {spec : OracleSpec ι} (t : spec.Domain) : QueryImpl.id spec t = OracleSpec.query t :=
  rfl


-- @@ L133-134 verbatim
@[simp] lemma mapQuery_id {α} {spec : OracleSpec ι} (q : OracleQuery spec α) :
    (QueryImpl.id spec).mapQuery q = q := rfl


-- @@ L136-139 verbatim
/-- Version of `QueryImpl.id` that automatically lifts into `OracleComp spec` rather than
just implementing queries in the lower level `OracleQuery spec` monad -/
protected def id' {ι} (spec : OracleSpec ι) :
    QueryImpl spec (OracleComp spec) := QueryImpl.liftTarget _ (QueryImpl.id spec)


-- @@ L141-143 expanded
@[simp]
lemma id'_apply {spec : OracleSpec ι} (t : spec.Domain) :
    QueryImpl.id' spec t = liftM (OracleSpec.query t) := by simp [QueryImpl.id']


-- @@ L145-149 verbatim
@[simp] lemma mapQuery_id' {α} {spec : OracleSpec ι} (q : OracleQuery spec α) :
    (QueryImpl.id' spec).mapQuery q = q := by
  simp only [mapQuery, id'_apply]
  rw [← OracleComp.liftM_map]
  exact congrArg OracleComp.lift (mapQuery_id q)


-- @@ L151-151 verbatim
end id


-- @@ L153-153 verbatim
section ofLift


-- @@ L155-158 expanded
/-- Given that queries in `spec` lift to the monad `m` we get an implementation via lifting. -/
def ofLift (spec : OracleSpec ι) (m : Type u → Type v) [MonadLiftT (OracleQuery spec) m] :
    QueryImpl spec m := fun t : spec.Domain => liftM (OracleSpec.query t)


-- @@ L160-161 expanded
@[simp]
lemma ofLift_apply (spec : OracleSpec ι) (m : Type u → Type v) [MonadLiftT (OracleQuery spec) m]
    (t : spec.Domain) : ofLift spec m t = liftM (OracleSpec.query t) :=
  rfl


-- @@ L163-166 expanded
@[simp]
lemma mapQuery_ofLift {α} (spec : OracleSpec ι) (m : Type u → Type v) [Functor m]
    [MonadLiftT (OracleQuery spec) m] (q : OracleQuery spec α) :
    (ofLift spec m).mapQuery q = q.cont <$> liftM (OracleSpec.query q.input) := by simp [mapQuery]


-- @@ L168-168 verbatim
@[simp] lemma ofLift_eq_id : ofLift spec (OracleQuery spec) = QueryImpl.id spec := rfl


-- @@ L170-172 verbatim
@[simp] lemma ofLift_eq_id' : ofLift spec (OracleComp spec) = QueryImpl.id' spec := by
  funext t
  simp


-- @@ L174-174 verbatim
end ofLift


-- @@ L176-176 verbatim
section ofFn


-- @@ L178-181 verbatim
/-- View a function from oracle inputs to outputs as an implementation in the `Id` monad.
Can be used to run a computation to get a specific value. -/
def ofFn (f : (t : spec.Domain) → spec.Range t) :
    QueryImpl spec Id := f


-- @@ L183-184 verbatim
@[simp] lemma ofFn_apply (f : (t : spec.Domain) → spec.Range t)
    (t : spec.Domain) : ofFn f t = f t := rfl


-- @@ L186-187 verbatim
@[simp] lemma mapQuery_ofFn {α} (f : (t : spec.Domain) → spec.Range t)
    (q : OracleQuery spec α) : (ofFn f).mapQuery q = q.cont (f q.input) := rfl


-- @@ L189-189 verbatim
end ofFn


-- @@ L191-191 verbatim
section ofFn?


-- @@ L193-195 verbatim
/-- Version of `ofFn` that allows queries to fail to return a value. -/
def ofFn? (f : (t : spec.Domain) → Option (spec.Range t)) :
    QueryImpl spec Option := f


-- @@ L197-198 verbatim
@[simp] lemma ofFn?_apply (f : (t : spec.Domain) → Option (spec.Range t))
    (t : spec.Domain) : ofFn? f t = f t := rfl


-- @@ L200-201 verbatim
@[simp] lemma mapQuery_ofFn? {α} (f : (t : spec.Domain) → Option (spec.Range t))
    (q : OracleQuery spec α) : (ofFn? f).mapQuery q = (f q.input).map q.cont := rfl


-- @@ L203-203 verbatim
end ofFn?


-- @@ L205-208 expanded
/-- Implement a single oracle as evaluation of a `Polynomial`. -/
@[reducible]
def ofPolynomial {R} [Semiring R] (p : Polynomial R) :
    QueryImpl (OracleSpec.ofFn (ι := R) (fun _ => R)) Id :=
  .ofFn fun t : R => p.eval t


-- @@ L210-213 expanded
/-- Implement a single oracle as the evaluation of an `MvPolynomial. -/
@[reducible]
noncomputable def ofMvPolynomial {R σ} [CommSemiring R] (p : MvPolynomial σ R) :
    QueryImpl (OracleSpec.ofFn (ι := (σ → R)) (fun _ => R)) Id :=
  .ofFn fun t : σ → R => p.eval t


-- @@ L215-218 expanded
/-- Implement a single oracle as indexing into a `Vector`. -/
@[reducible]
def ofVector {α n} (v : Vector α n) : QueryImpl (OracleSpec.ofFn (ι := Fin n) (fun _ => α)) Id :=
  .ofFn fun t : Fin n => v[t]


-- @@ L220-223 expanded
/-- Oracle context for ability to query elements of a vector `v`. -/
@[reducible]
def ofListVector {α n} (v : List.Vector α n) :
    QueryImpl (OracleSpec.ofFn (ι := Fin n) (fun _ => α)) Id :=
  .ofFn fun t : Fin n => v[t]


-- @@ L225-225 verbatim
end QueryImpl


-- @@ L227-227 verbatim
namespace HasQuery


-- @@ L229-229 verbatim
variable {ι} {spec : OracleSpec ι} {m : Type u → Type v}


-- @@ L231-234 verbatim
/-- Repackage `HasQuery` as a `QueryImpl`, for APIs that still consume explicit oracle
implementations. -/
def toQueryImpl [HasQuery spec m] : QueryImpl spec m :=
  fun t => HasQuery.query t


-- @@ L236-238 verbatim
@[simp]
lemma toQueryImpl_apply [HasQuery spec m] (t : spec.Domain) :
    toQueryImpl (spec := spec) (m := m) t = HasQuery.query (spec := spec) (m := m) t := rfl


-- @@ L240-248 verbatim
/-- On `OracleComp spec`, `HasQuery.toQueryImpl` is the identity handler `QueryImpl.id'`.

Not `@[simp]`: in `unifFwdImpl`-style definitions where `toQueryImpl.liftTarget` appears
inside a `simp [unifFwdImpl]` call, the rewrite `toQueryImpl → id' = liftTarget _ (id _)`
nests `liftTarget`s and triggers unbounded depth. Use via explicit `rw` instead. -/
lemma toQueryImpl_eq_id' :
    (toQueryImpl : QueryImpl spec (OracleComp spec)) = QueryImpl.id' spec := by
  funext t
  simp


-- @@ L250-250 verbatim
end HasQuery
