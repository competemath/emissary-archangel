/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Std.Tactic.Do
import VCVio.ProgramLogic.Unary.StdDoBridge


-- @@ L10-46 verbatim
/-!
# `RustOracleComp`: target monad for Rust verification frontends

A monad transformer stack that is the natural target for Lean code emitted
by Rust verification frontends (currently
[hax](https://github.com/cryspen/hax) and
[aeneas](https://github.com/AeneasVerif/aeneas)) once we want oracle access:

```
RustOracleComp spec α  :=  ExceptT Error (OptionT (OracleComp spec)) α
```

The `ExceptT Error` layer models Rust panics, the `OptionT` layer models
divergence, and the `OracleComp spec` layer models probabilistic / oracle
queries.

The `Error` enum in this file is a verbatim mirror of the shared
`Error` enum in `Hax.rust_primitives.RustM` and `Aeneas.Std.Primitives`.
We keep it local so this module compiles without requiring the hax / aeneas
Lake packages. The actual `MonadLift` instances from `Hax.RustM` and
`Aeneas.Std.Result` live in `Interop.Hax.Bridge` and `Interop.Aeneas.Bridge`,
both of which are gated on the corresponding `require` in `lakefile.lean`.

## Why a transformer stack?

`Hax.RustM` collapses panic + divergence into `ExceptT Error Option`:
the resulting WP shape is `.except Error (.except PUnit .pure)`. Replacing
the inner `Option` with `OptionT (OracleComp spec)` preserves the WP shape
exactly while threading oracles through the divergence layer; lifts from
`Hax.RustM` are then a definitional `pure`. Aeneas's `Result α` (an
inductive `ok | fail | div`) is isomorphic to `Hax.RustM α` and converts
into `RustOracleComp spec α` by case analysis.

This shape is intentional: it is the smallest extension of the hax /
aeneas target that admits oracle queries while keeping the boundary lemmas
trivial.
-/


-- @@ L48-48 verbatim
open Std.Do


-- @@ L50-50 verbatim
namespace Interop.Rust


-- @@ L52-64 verbatim
/-- Mirror of the `Error` enum used by both `Hax.rust_primitives.RustM`
and `Aeneas.Std.Primitives`. Mirrored locally so this module does not
depend on either upstream package; the bridges in `Interop.Hax` and
`Interop.Aeneas` translate at the boundary. -/
inductive Error where
  | assertionFailure : Error
  | integerOverflow : Error
  | divisionByZero : Error
  | arrayOutOfBounds : Error
  | maximumSizeExceeded : Error
  | panic : Error
  | undef : Error
  deriving Repr, BEq, DecidableEq, Inhabited


-- @@ L66-76 verbatim
/-- Oracle-aware version of `Hax.RustM` / `Aeneas.Std.Result`.

`ExceptT Error (OptionT (OracleComp spec)) α` is, layer by layer:
* `OracleComp spec` for oracle access and probabilistic semantics,
* `OptionT _` for divergence (`none` ≡ `div`),
* `ExceptT Error _` for Rust panics (`some (.error e)` ≡ `fail e`).

Once a computation panics it cannot diverge, and once it diverges it
cannot return — exactly the semantics of `Hax.RustM` and `Aeneas.Std.Result`. -/
abbrev RustOracleComp {ι : Type} (spec : OracleSpec ι) (α : Type) : Type :=
  ExceptT Error (OptionT (OracleComp spec)) α


-- @@ L78-78 verbatim
namespace RustOracleComp


-- @@ L80-80 verbatim
variable {ι : Type} {spec : OracleSpec ι} {α : Type}


-- @@ L82-84 verbatim
/-- A successful Rust computation. -/
@[reducible, match_pattern]
def ok (v : α) : RustOracleComp spec α := pure v


-- @@ L86-88 verbatim
/-- A panicking Rust computation. -/
@[reducible, match_pattern]
def fail (e : Error) : RustOracleComp spec α := throw e


-- @@ L90-93 verbatim
/-- A diverging Rust computation. -/
@[reducible, match_pattern]
def div : RustOracleComp spec α :=
  ExceptT.mk (OptionT.mk (pure none))


-- @@ L95-108 verbatim
/-- Lift an oracle computation into the Rust target by treating it as a
total, panic-free Rust value. This is the `pure`/`some` chain through both
transformers and is what every oracle query reduces to inside the Rust
target.

Defined as the two-step `ExceptT.lift ∘ OptionT.lift` so `mvcgen` can
peel the `MonadLiftT (OracleComp spec) (RustOracleComp spec)` chain via
the standard `@[spec]` rules `Spec.monadLift_OptionT` and
`Spec.monadLift_ExceptT`. A direct `MonadLift (OracleComp spec)
(RustOracleComp spec)` instance would short-circuit that chain and leave
mvcgen with no spec rule to apply. -/
@[reducible]
def liftOracleComp (oa : OracleComp spec α) : RustOracleComp spec α :=
  ExceptT.lift (OptionT.lift oa)


-- @@ L110-110 verbatim
end RustOracleComp


-- @@ L112-112 verbatim
end Interop.Rust
