/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.SimSemantics.Append


-- @@ L10-15 verbatim
/-!
# Bundled Oracle Specs and Implementations

This file defines a type `OracleContext ι m` that provides an ambient set of oracles,
along with an implementation of those oracles in the monad `m`.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
universe u v w


-- @@ L21-21 verbatim
open OracleSpec OracleComp


-- @@ L23-27 verbatim
/-- An `OracleContext ι m` bundles a specification `spec` of oracles with input set `ι`
and an implementation of the oracles in terms of the monad `m`. -/
structure OracleContext (ι : Type u) (m : Type v → Type w) : Type (max u v w + 1) where
  spec : OracleSpec.{u,v} ι
  impl : QueryImpl spec m


-- @@ L29-35 verbatim
/-- Convert an `OracleSpec` into an `OracleContext` with `OracleComp` as the implementation monad,
using the identity implementation for queries. -/
@[reducible]
def OracleSpec.defaultContext {ι : Type u} (spec : OracleSpec ι) :
    OracleContext spec.Domain (OracleComp spec) where
  spec := spec
  impl := QueryImpl.id' spec


-- @@ L37-37 verbatim
namespace OracleContext


-- @@ L39-40 expanded
instance {ι} {m : Type u → Type v} [Pure m] : Inhabited (OracleContext ι m) :=
  ⟨{ spec := OracleSpec.ofFn (ι := ι) (fun _ => PUnit), impl _ := pure PUnit.unit }⟩


-- @@ L42-42 verbatim
variable {ι ι'} {spec : OracleSpec ι} {m : Type u → Type v}


-- @@ L44-48 verbatim
/-- Convert a `QueryImpl` into an `OracleContext` by bundling the `OracleSpec` corresponding
to the particular implementation. -/
@[reducible] def ofImpl (impl : QueryImpl spec m) : OracleContext ι m where
  spec := spec
  impl := impl


-- @@ L50-55 verbatim
/-- Combine two oracle contexts with the same target monad, giving access to both ambient
oracles and implementing queries to each independently. -/
@[reducible] protected def add (O : OracleContext ι m) (O' : OracleContext ι' m) :
    OracleContext (ι ⊕ ι') m where
  spec := O.spec + O'.spec
  impl := O.impl + O'.impl


-- @@ L57-58 verbatim
instance : HAdd (OracleContext ι m) (OracleContext ι' m) (OracleContext (ι ⊕ ι') m) where
  hAdd := OracleContext.add


-- @@ L60-61 verbatim
@[simp] lemma add_def (O : OracleContext ι m) (O' : OracleContext ι' m) :
    O + O' = O.add O' := rfl


-- @@ L63-64 verbatim
lemma spec_add (O : OracleContext ι m) (O' : OracleContext ι' m) :
    (O + O').spec = O.spec + O'.spec := rfl


-- @@ L66-67 verbatim
lemma impl_add (O : OracleContext ι m) (O' : OracleContext ι' m) :
    (O + O').impl = O.impl + O'.impl := rfl


-- @@ L69-69 verbatim
end OracleContext
