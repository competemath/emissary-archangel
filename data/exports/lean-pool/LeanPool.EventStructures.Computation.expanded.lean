/-
Copyright (c) 2026 Vikraman Choudhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vikraman Choudhury
-/
module

public import LeanPool.EventStructures.Path
import Mathlib.Data.Finset.Attr


-- @@ L11-18 verbatim
/-!
# Computations

A computation to a configuration is an asynchronous path from the empty
configuration to it. This module defines computations, the type of reachable
configurations, and linearisations, and relates computations to the
configurations they reach.
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
namespace EventStructures


-- @@ L24-24 verbatim
variable (es : EventStructure)

-- @@ L25-25 verbatim
open EventStructure

-- @@ L26-26 verbatim
open Configuration

-- @@ L27-27 verbatim
open Path

-- @@ L28-28 verbatim
open Trace


-- @@ L30-31 verbatim
/-- Notation for trace equivalence. -/
local infixr:60 " ≈ₜ " => TraceEquiv es


-- @@ L33-37 verbatim
/-- The empty configuration is a valid configuration. -/
def emptyConf : Conf es :=
  ⟨(∅ : Set es.Event), by
    simp_all
  ⟩


-- @@ L39-44 verbatim
/-- A computation to a configuration `c` is an asynchronous path
  starting at the empty configuration and ending at `c`.
  Equivalently, a computation records a causal execution up to
  trace equivalence of the underlying path. -/
def Computation (c : Conf es) : Type _ :=
  Path.Async es (emptyConf es) c


-- @@ L46-47 verbatim
/-- The type of all computations, paired with their target configuration. -/
def Computations : Type _ := Σ c : Conf es, Computation es c


-- @@ L49-54 verbatim
/-- A list of events `t` is a linearisation of configuration `c`
  if it is trace-equivalent to the trace of some path from the
  empty configuration to `c`. Equivalently, `t` enumerates
  the events of `c` in some order compatible with causality. -/
def isLinearisation (c : Conf es) (t : List es.Event) : Prop :=
  ∃ p : Path es (emptyConf es) c, Path.trace es p ≈ₜ t


-- @@ L56-60 verbatim
/-- Every computation determines a linearisation of its target configuration. -/
lemma computation_is_linearisation {c : Conf es} (comp : Computation es c) :
    ∃ t : List es.Event, isLinearisation es c t := by
  obtain ⟨p, rfl⟩ := Quotient.exists_rep comp
  refine ⟨Path.trace es p, ⟨p, TraceEquiv.refl _⟩⟩


-- @@ L62-63 verbatim
/-- Configurations that are reachable by a computation. -/
def ReachableConf : Type _ := {c : Conf es // Nonempty (Computation es c)}


-- @@ L65-67 verbatim
/-- Every computation targets a reachable configuration. -/
def computationToReachable : Computations es → ReachableConf es :=
  fun p => ⟨p.1, ⟨p.2⟩⟩


-- @@ L69-72 verbatim
/-- The map from computations to reachable configurations is surjective. -/
lemma computation_to_reachable_surjective :
    Function.Surjective (computationToReachable es) :=
  fun ⟨c, ⟨comp⟩⟩ => ⟨⟨c, comp⟩, rfl⟩


-- @@ L74-74 verbatim
end EventStructures
