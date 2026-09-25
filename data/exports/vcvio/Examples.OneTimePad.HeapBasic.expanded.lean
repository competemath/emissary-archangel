/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.StateSeparating.DistEquiv
public import VCVio.OracleComp.Constructions.BitVec
public import ToMathlib.Data.Heap


-- @@ L12-76 verbatim
/-!
# One-Time Pad as a state-separating handler

Pilot port of `Examples.OneTimePad.Basic` to the experimental `state-separating`
framework: the OTP perfect-secrecy story, rebuilt as a `state-separating.Handler`
"real vs ideal" pair, with the SSProve-style "single-call gate" idiom
applied so that distributional equivalence holds *unconditionally* at
the handler level.

## SSProve "single-call gate" idiom

OTP secrecy is structurally one-shot: encrypting two messages under the
same key reveals their XOR. To make `realImpl ≡ᵈ idealImpl` hold against
*every* adversary (rather than the "adversary issues at most one query"
fragment), both handlers bake the call-counting into their state. Each
handler carries a single `UsedFlag.used : Bool` cell, gated as follows:

* On the **first** `enc m` call (`h .used = false`), the handler does
  its real work (real: sample `k`, return `k ⊕ m`; ideal: sample a
  fresh `c`, return `c`) and flips `.used := true`.
* On **subsequent** calls (`h .used = true`), the handler short-circuits
  to a fixed dummy ciphertext (`0#sp`), with no further sampling.

Because the gate makes the second-and-later calls deterministic and
identical on both sides, and because the first call's outputs have the
same distribution (XOR with a uniform key is uniform), the two handlers
are distributionally equivalent against every adversary. This is the
standard SSProve playbook for bounded-query primitives: enforce the
bound *in the handler*, then quantify the equivalence over all
adversaries.

## Sampling deferred into the handler

A second SSProve-style choice: the real handler's key is **not** sampled
at `init` and stored in the heap. Instead, both `init`s are
`pure Heap.empty`, and the real handler samples its key locally on the
first call. This keeps the two `init`s `evalSPMF`-equal (so the simple
"per-handler" `DistEquiv.of_step` constructor applies) without any heap
bijection bookkeeping, and is observationally equivalent for OTP
because the key is single-use anyway.

## What this file builds

* `otpSpec sp` exposes a single export query `enc m` taking a plaintext
  `m : BitVec sp` and returning a ciphertext `BitVec sp`.
* `UsedFlag` is the single-cell identifier set carrying `.used : Bool`,
  shared by both handlers.
* `realImpl sp` and `idealImpl sp` are the gated real and ideal handlers
  on `UsedFlag`.
* `realImpl_distEquiv_idealImpl : realImpl sp ≡ᵈ idealImpl sp` is the
  unconditional `DistEquiv` headline, proved via
  `QueryImpl.Stateful.DistEquiv.of_step`.
* `encOnce sp m` is the canonical single-call adversary; the
  `evalSPMF_run_encOnce_eq` corollary on it is now a one-line
  consequence of the distributional equivalence.

## Comparison with `Examples.OneTimePad.Basic`

`Basic.lean` uses the `SymmEncAlg` abstraction layer (with
`PerfectSecrecyExp`, `Complete`, `perfectSecrecyAt`); it does not use
the SSP handler layer. This file uses the state-separating handler layer
directly, in the SSProve-style "handler as bounded-query gate" idiom.
The arithmetic core, "XOR with a uniform key is uniform", is shared
verbatim via `evalSPMF_map_bijective_uniform_cross` against the XOR
involution. -/


-- @@ L78-78 verbatim
@[expose] public section


-- @@ L80-80 verbatim
open OracleSpec OracleComp ENNReal

-- @@ L81-81 verbatim
open scoped QueryImpl.Stateful


-- @@ L83-83 verbatim
namespace VCVio.StateSeparating.OneTimePad


-- @@ L85-88 verbatim
/-! ## Export oracle interface

A single export query `enc m` with `m : BitVec sp` carrying the
plaintext, returning a ciphertext `BitVec sp`. -/


-- @@ L90-93 verbatim
/-- The OTP export query index: a single constructor `enc m` carrying
the plaintext. -/
inductive OTPOp (sp : ℕ)
  | enc (m : BitVec sp)


-- @@ L95-98 verbatim
/-- The OTP export interface: each `enc _` query returns a `BitVec sp`
ciphertext. -/
@[reducible] def otpSpec (sp : ℕ) : OracleSpec.{0, 0} (OTPOp sp)
  | .enc _ => BitVec sp


-- @@ L100-104 verbatim
/-! ## Single-call gate

Both `realImpl` and `idealImpl` use the same one-cell identifier set
`UsedFlag`. The lone cell `.used : Bool` records whether the (one)
encryption has already been issued. -/


-- @@ L106-109 verbatim
/-- Cell directory carrying the single-call gate flag. -/
inductive UsedFlag
  | used
  deriving DecidableEq


-- @@ L111-115 verbatim
/-- The cell `used` carries a `Bool`; the default value is `false`,
so a fresh `Heap.empty` represents "no encryption issued yet". -/
instance instCellSpecUsedFlag : CellSpec UsedFlag where
  type    | .used => Bool
  default | .used => false


-- @@ L117-117 verbatim
/-! ## Real and ideal handlers with the call gate -/


-- @@ L119-132 expanded
/-- The **real-world OTP handler** with single-call gating.

* **State.** A single `UsedFlag.used : Bool` cell.
* **Init.** Trivial (`pure Heap.empty`); the key is sampled on demand.
* **Handler.** On the first `enc m` call (`h .used = false`), sample a
  uniform key `k` *locally*, return `k ⊕ m`, and flip `.used := true`.
  On subsequent calls (`h .used = true`), short-circuit to `0#sp`. -/
def realImpl (sp : ℕ) : QueryImpl.Stateful unifSpec (otpSpec sp) (Heap UsedFlag)
  | .enc m =>
    StateT.mk fun (h : Heap UsedFlag) =>
      if h .used then pure (0#sp, h)
      else do
        let k ← (uniformSample (BitVec sp) : ProbComp (BitVec sp))
        pure (k ^^^ m, h.update .used true)


-- @@ L134-152 expanded
/-- The **ideal-world OTP handler** with single-call gating.

* **State.** A single `UsedFlag.used : Bool` cell.
* **Init.** Trivial (`pure Heap.empty`).
* **Handler.** On the first `enc _` call, sample a fresh uniform
  ciphertext, return it, and flip `.used := true`. On subsequent calls,
  short-circuit to `0#sp`.

The same identifier set as `realImpl` is shared on purpose: it lets the
proof `realImpl_distEquiv_idealImpl` use the simple
`QueryImpl.Stateful.DistEquiv.of_step` constructor (per-handler `evalSPMF`
equality), avoiding any heap bijection bookkeeping. -/
def idealImpl (sp : ℕ) : QueryImpl.Stateful unifSpec (otpSpec sp) (Heap UsedFlag)
  | .enc _ =>
    StateT.mk fun (h : Heap UsedFlag) =>
      if h .used then pure (0#sp, h)
      else do
        let c ← (uniformSample (BitVec sp) : ProbComp (BitVec sp))
        pure (c, h.update .used true)


-- @@ L154-154 verbatim
/-! ## XOR-by-`m` is a bijection on `BitVec sp` -/


-- @@ L156-165 verbatim
/-- Right XOR by a fixed mask is a bijection on `BitVec sp`: it is its
own inverse via `(a ^^^ m) ^^^ m = a`. The key arithmetic fact behind
OTP perfect secrecy. -/
private lemma bitVec_xor_right_bijective (sp : ℕ) (m : BitVec sp) :
    Function.Bijective ((· ^^^ m) : BitVec sp → BitVec sp) := by
  refine ⟨fun a b hab => ?_, fun y => ⟨y ^^^ m, ?_⟩⟩
  · have h : a ^^^ m ^^^ m = b ^^^ m ^^^ m := congrArg (· ^^^ m) hab
    simpa [BitVec.xor_assoc] using h
  · change y ^^^ m ^^^ m = y
    rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]


-- @@ L167-174 verbatim
/-! ## Per-(query, heap) handler equivalence

The arithmetic core of OTP perfect secrecy at the handler layer:
on every (query, heap) pair, `realImpl`'s and `idealImpl`'s handlers
have the same `evalSPMF`. Exposed as a stand-alone lemma so that
parallel-channel cutovers (e.g. `Examples.OneTimePad.HeapPar`) can
feed it to `QueryImpl.Stateful.DistEquiv.parSum_congr` without re-running the
case-split. -/


-- @@ L176-211 expanded
/-- **Per-handler `evalSPMF` equality** between `realImpl sp` and
`idealImpl sp`. On every input `(query, heap)`, the two handlers
produce the same output distribution.

Splits on `h .used`:

* `h .used = true` (gated): both handlers reduce to `pure (0#sp, h)`,
  with no sampling.
* `h .used = false` (live): both handlers sample a uniform value
  before tagging the heap; the inner `do`-blocks differ only by an
  XOR-with-`m` on the sampled value, which `(· ^^^ m)` being a
  bijection on `BitVec sp` makes distributionally invisible (via
  `probOutput_bind_bijective_uniform_cross`). -/
theorem realImpl_impl_evalSPMF_idealImpl (sp : ℕ) (q : (otpSpec sp).Domain) (h : Heap UsedFlag) :
    evalSPMF (((realImpl sp) q).run h) = evalSPMF (((idealImpl sp) q).run h) := by
  cases q with
  | enc
    m =>
    change
      evalSPMF
          (if h .used then (pure (0#sp, h) : OracleComp unifSpec _)
          else do
            let k ← (uniformSample (BitVec sp) : ProbComp (BitVec sp));
            pure (k ^^^ m, h.update .used true)) =
        evalSPMF
          (if h .used then (pure (0#sp, h) : OracleComp unifSpec _)
          else do
            let c ← (uniformSample (BitVec sp) : ProbComp (BitVec sp));
            pure (c, h.update .used true))
    by_cases hused : h .used
    · rw [if_pos hused, if_pos hused]
    · rw [if_neg hused, if_neg hused]
        -- `evalSPMF` of the two `do`-blocks coincide pointwise via the
              -- XOR-by-`m` bijection on the uniform sample.
        
      apply evalSPMF_ext
      intro z
      exact
        probOutput_bind_bijective_uniform_cross (α := BitVec sp) (β := BitVec sp) (· ^^^ m)
          (bitVec_xor_right_bijective sp m) (fun y => pure (y, h.update .used true)) z


-- @@ L213-217 verbatim
/-! ## Unconditional distributional equivalence

The headline statement: `realImpl sp ≡ᵈ idealImpl sp`. Once the
`UsedFlag` gate is in place, the equivalence holds against *every*
adversary, not just single-call ones. -/


-- @@ L219-229 expanded
/-- **OTP unconditional distributional equivalence.** With the
single-call gate baked into both handlers, the real and ideal OTP
handlers produce identical output distributions against every
adversary, on every output type.

Proof shape: `QueryImpl.Stateful.DistEquiv.of_step` from the default initial
heap state, using the per-(query, heap) handler equivalence
`realImpl_impl_evalSPMF_idealImpl`. -/
theorem realImpl_distEquiv_idealImpl (sp : ℕ) :
    QueryImpl.Stateful.DistEquiv₀ (realImpl sp) (idealImpl sp) :=
  QueryImpl.Stateful.DistEquiv.of_step (realImpl_impl_evalSPMF_idealImpl sp) Heap.empty


-- @@ L231-231 verbatim
/-! ## Single-call adversary and corollary -/


-- @@ L233-242 verbatim
/-- The single-call adversary that issues one `enc m` query and
returns the ciphertext verbatim.

The body `(otpSpec sp).query (.enc m)` is an `OracleQuery (otpSpec sp) _`;
the implicit `MonadLift (OracleQuery spec) (OracleComp spec)` lifts it
into `OracleComp (otpSpec sp) (BitVec sp)`, matching the declared
return type. Going through the named `(otpSpec sp).query` (rather than
the bare `query (.enc m)`) is what pins down the `spec` for elaboration. -/
def encOnce (sp : ℕ) (m : BitVec sp) : OracleComp (otpSpec sp) (BitVec sp) :=
  (otpSpec sp).query (.enc m)


-- @@ L244-258 expanded
/-- **OTP single-query indistinguishability**, recovered as a corollary
of `realImpl_distEquiv_idealImpl` by specialising the universal `≡ᵈ` to
the canonical single-call adversary `encOnce sp m`.

The same content, framed as `SymmEncAlg.PerfectSecrecyCipherGivenMsgExp`
equivalence, is proved as `cipherGivenMsg_equiv` in
`Examples.OneTimePad.Basic`. The state-separating framing replaces the
"reductive bijection" of that proof with the "per-call gate" idiom: a
direct existence statement at the handler level rather than a
per-message reduction. -/
theorem evalSPMF_run_encOnce_eq (sp : ℕ) (m : BitVec sp) :
    evalSPMF ((realImpl sp).runProb₀ (encOnce sp m)) =
      evalSPMF ((idealImpl sp).runProb₀ (encOnce sp m)) :=
  QueryImpl.Stateful.DistEquiv.runProb₀_evalSPMF_eq (realImpl_distEquiv_idealImpl sp) (encOnce sp m)


-- @@ L260-260 verbatim
end VCVio.StateSeparating.OneTimePad
