/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.OracleSpec


-- @@ L10-14 verbatim
/-!
# Oracle Queries

This file defines `OracleQuery`, the single-query functor induced by an `OracleSpec`.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
universe u v w z


-- @@ L20-20 verbatim
open OracleSpec


-- @@ L22-30 verbatim
/-- Functor to represent queries to oracles specified by an `OracleSpec ι`,
defined to be the object type of the corresponding `PFunctor`.
In particular an element of `OracleQuery spec α` consists of an input value `t : spec.Domain`,
and a continuation `f : spec.Range t → α` specifying what to do with the result.
See `OracleSpec.query` for the case when the continuation `f` just returns the query result. -/
@[reducible]
def OracleQuery {ι : Type u} (spec : OracleSpec.{u, v} ι) :
    Type w → Type (max u v w) :=
  PFunctor.Obj spec.toPFunctor


-- @@ L32-33 verbatim
@[reducible] protected def OracleQuery.mk {ι α} {spec : OracleSpec ι}
    (t : spec.Domain) (f : spec.Range t → α) : OracleQuery spec α := ⟨t, f⟩


-- @@ L35-35 verbatim
namespace OracleSpec


-- @@ L37-37 verbatim
variable {ι : Type u} {spec : OracleSpec.{u, v} ι}


-- @@ L39-47 verbatim
/-- Query an oracle on in input `t` to get a result in the corresponding `range t`.

Marked `protected`: the bare identifier `query` resolves to `HasQuery.query`
(exported in `VCVio.OracleComp.HasQuery.Basic`), which yields a value in the
ambient monad and lets Lean recover `spec` from the expected type without an
ascription. Use `spec.query t` or `OracleSpec.query t` when you specifically
want the primitive single-query syntax `OracleQuery spec (spec.Range t)`. -/
protected def query (t : spec.Domain) : OracleQuery spec (spec.Range t) :=
  OracleQuery.mk t id


-- @@ L49-50 verbatim
protected lemma query_def (t : spec.Domain) :
    OracleSpec.query t = ⟨t, id⟩ := rfl


-- @@ L52-52 verbatim
end OracleSpec


-- @@ L54-68 verbatim
/-! ### Primitive `query` notation

`OracleSpec.query` is `protected` so the bare identifier `query` resolves to
`HasQuery.query` (exported in `VCVio.OracleComp.HasQuery.Basic`) for
ergonomic monadic use. Files that work *structurally* on the primitive
single-query syntax `OracleQuery spec _` (e.g. `liftM (query t)`,
`(query t).cont`, induction on `query_bind`) can opt back into the
primitive interpretation of bare `query` with a single line:

```
open scoped OracleSpec.PrimitiveQuery
```

The notation is `scoped` to this namespace, so it never leaks past a file
boundary; you must explicitly opt in. -/

-- @@ L69-69 verbatim
namespace OracleSpec.PrimitiveQuery


-- @@ L71-73 verbatim
/-- Inside `open scoped OracleSpec.PrimitiveQuery`, the bare identifier
`query` aliases the primitive single-query syntax `OracleSpec.query`. -/
scoped notation "query" => OracleSpec.query


-- @@ L75-75 verbatim
end OracleSpec.PrimitiveQuery


-- @@ L77-77 verbatim
namespace OracleQuery


-- @@ L79-79 verbatim
variable {ι : Type u} {spec : OracleSpec.{u, v} ι}


-- @@ L81-83 verbatim
/-- The oracle input used in an oracle query. -/
@[inline, reducible]
def input {α} (q : OracleQuery spec α) : spec.Domain := q.1


-- @@ L85-86 verbatim
@[simp] lemma input_apply {α} (t : spec.Domain) (f : spec.Range t → α) :
    input ⟨t, f⟩ = t := rfl


-- @@ L88-89 verbatim
@[simp] lemma input_map {α β} (q : OracleQuery spec α) (f : α → β) :
    (f <$> q).input = q.input := rfl


-- @@ L91-92 verbatim
@[simp] lemma input_map' {α β} (q : OracleQuery spec α) (f : α → β) :
    OracleQuery.input (PFunctor.map spec.toPFunctor f q) = q.input := rfl


-- @@ L94-96 verbatim
/-- The continuation used for the result of an oracle query. -/
@[inline, reducible]
def cont {α} (q : OracleQuery spec α) (f : spec.Range q.input) : α := q.2 f


-- @@ L98-99 verbatim
@[simp] lemma cont_apply {α} (t : spec.Domain) (f : spec.Range t → α) :
    cont ⟨t, f⟩ = f := rfl


-- @@ L101-102 verbatim
@[simp] lemma cont_map {α β} (q : OracleQuery spec α) (f : α → β) :
    (f <$> q).cont = f ∘ q.cont := rfl


-- @@ L104-105 verbatim
@[simp] lemma cont_map' {α β} (q : OracleQuery spec α) (f : α → β) :
    OracleQuery.cont (PFunctor.map spec.toPFunctor f q) = f ∘ q.cont := rfl


-- @@ L107-110 verbatim
/-- Two oracles queries are equal if they query for the same input and run
extensionally equal continuation on the results of the query. -/
@[ext] lemma ext {α} {q q' : OracleQuery spec α}
    (h : q.input = q'.input) (h' : q.cont ≍ q'.cont) : q = q' := Sigma.ext h h'


-- @@ L112-115 verbatim
/-- Version of `OracleQuery.ext` that avoids using `HEq` when the inputs are the same. -/
lemma ext' {α} (t : spec.Domain) {cont cont' : spec.Range t → α}
    (h : cont = cont') : (⟨t, cont⟩ : OracleQuery spec α) = ⟨t, cont'⟩ := by
  simpa [funext_iff] using h


-- @@ L117-119 verbatim
/-- If an oracle exists and the output type is non-empty then the type of queries is non-empty. -/
instance {α} [Inhabited ι] [Inhabited α] : Inhabited (OracleQuery spec α) :=
  inferInstanceAs (Inhabited ((t : spec.Domain) × (spec.Range t → α)))


-- @@ L121-123 verbatim
/-- If there are no oracles available then the type of queries is empty. -/
instance {α} [h : IsEmpty ι] : IsEmpty (OracleQuery spec α) :=
  inferInstanceAs (IsEmpty ((t : spec.Domain) × (spec.Range t → α)))


-- @@ L125-129 verbatim
/-- If there is at most one oracle and output, then there is at most one query. -/
instance {α} [h : Subsingleton ι] [h' : Subsingleton α] : Subsingleton (OracleQuery spec α) where
  allEq := fun ⟨t, cont⟩ ⟨t', cont'⟩ => by
    obtain rfl := h.allEq t t'
    exact OracleQuery.ext' t (Subsingleton.allEq cont cont')


-- @@ L131-131 verbatim
@[simp] lemma input_query (t : spec.Domain) : (OracleSpec.query t).input = t := rfl

-- @@ L132-132 verbatim
@[simp] lemma cont_query (t : spec.Domain) : (OracleSpec.query t).cont = id := rfl


-- @@ L134-134 verbatim
@[simp] lemma fst_query (t : spec.Domain) : (OracleSpec.query t).1 = t := rfl

-- @@ L135-135 verbatim
@[simp] lemma snd_query (t : spec.Domain) : (OracleSpec.query t).2 = id := rfl


-- @@ L137-138 verbatim
@[simp] lemma cont_map_query_input {α} (q : OracleQuery spec α) :
    q.cont <$> (OracleSpec.query q.input) = q := rfl


-- @@ L140-141 verbatim
@[simp] lemma cont_map_query_input' {α} (q : OracleQuery spec α) :
    PFunctor.map spec.toPFunctor q.cont (OracleSpec.query q.input) = q := rfl


-- @@ L143-145 verbatim
@[simp] lemma query_eq_mk_iff (t : spec.Domain) (cont : spec.Range t → spec.Range t) :
    OracleSpec.query t = OracleQuery.mk t cont ↔ cont = id := by
  simp [OracleQuery.ext_iff, eq_comm]


-- @@ L147-149 verbatim
@[simp] lemma mk_eq_query_iff (t : spec.Domain) (cont : spec.Range t → spec.Range t) :
    OracleQuery.mk t cont = OracleSpec.query t ↔ cont = id := by
  simp [OracleQuery.ext_iff, eq_comm]


-- @@ L151-151 verbatim
end OracleQuery
