/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.OracleComp.OracleQuery


-- @@ L11-22 verbatim
/-!
# Basic `HasQuery` Capability

This is the lightweight dependency boundary for the query capability.
It defines `HasQuery spec m`, exports the bare identifier `query`, and provides
only the foundational instances for primitive query syntax and monad lifts.

Core syntax modules, especially `VCVio.OracleComp.OracleComp`, should import
this file when they need the class or the bare `query` export.
Do not add `QueryImpl`, `ProbComp`, or monad-morphism APIs here; those live in
downstream modules with explicit imports.
-/


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-26 verbatim
universe u v w


-- @@ L28-36 verbatim
/-- Capability to issue queries to the oracle family `spec` inside the ambient monad `m`. -/
class HasQuery {ι : Type u} (spec : OracleSpec.{u, v} ι) (m : Type v → Type w) where
  /-- Issue a single oracle query. -/
  query : (t : spec.Domain) → m (spec.Range t)

-- Re-export `HasQuery.query` as the bare identifier `query`. With
-- `OracleSpec.query` marked `protected`, the bare `query` resolves to
-- `HasQuery.query`, which yields a value in the ambient monad `m` and lets
-- Lean recover `spec` from the expected return type.

-- @@ L37-37 verbatim
export HasQuery (query)


-- @@ L39-39 verbatim
namespace HasQuery


-- @@ L41-41 verbatim
variable {ι : Type u} {spec : OracleSpec.{u, v} ι} {m : Type v → Type w}


-- @@ L43-45 verbatim
/-- The primitive single-query syntax `OracleQuery spec` has the obvious query capability. -/
instance instOracleQuery : HasQuery spec (OracleQuery spec) where
  query := OracleSpec.query


-- @@ L47-51 verbatim
@[simp]
lemma instOracleQuery_query (t : spec.Domain) :
    HasQuery.query (spec := spec) (m := OracleQuery spec) t =
      OracleSpec.query t :=
  rfl


-- @@ L53-57 verbatim
/-- Any lawful lift of `OracleQuery spec` into `m` gives query capability in `m`. This is the
main bridge that makes `HasQuery` compose with `SubSpec` lifts and standard transformer lifts. -/
instance (priority := low) instOfMonadLift [MonadLiftT (OracleQuery spec) m] :
    HasQuery spec m where
  query t := liftM (OracleSpec.query t)


-- @@ L59-63 verbatim
@[simp]
lemma instOfMonadLift_query [MonadLiftT (OracleQuery spec) m] (t : spec.Domain) :
    HasQuery.query (spec := spec) (m := m) t =
      liftM (OracleSpec.query t) :=
  rfl


-- @@ L65-65 verbatim
end HasQuery
