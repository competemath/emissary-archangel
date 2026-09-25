/-
Copyright (c) 2026 Quang Dao, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Alexander Hicks
-/

module
public import HashSig.SLHDSA.GeneralScheme
public import VCVio.OracleComp.Constructions.SampleableType


-- @@ L11-23 verbatim
/-!
# SLH-DSA external interfaces

The pure and pre-hash message encodings and the external key-generation, signing, and
verification interfaces from FIPS 205 Algorithms 21--25. The randomized definitions use the
repository's ideal, total `SampleableType` source. An implementation whose random-bit generator
can fail must translate that failure before calling the explicit-seed or explicit-randomizer
boundary exposed here.

## References

- NIST FIPS 205, Section 10, Algorithms 21--25
-/


-- @@ L25-25 verbatim
@[expose] public section


-- @@ L27-27 verbatim
namespace SLHDSA.External


-- @@ L29-29 verbatim
open OracleComp


-- @@ L31-39 verbatim
/-- Failures rejected at the FIPS external-message boundary. -/
inductive Error where
  /-- FIPS 205 limits the context string to at most 255 bytes. -/
  | contextTooLong (actual : ℕ)
  /-- FIPS 205 requires at least `2n` digest bytes for the claimed SLH-DSA security strength. -/
  | prehashTooWeak (n digestBytes : ℕ)
  /-- A built-in digest engine violated its advertised exact output width. -/
  | digestLengthMismatch (expected actual : ℕ)
deriving Repr, DecidableEq


-- @@ L41-50 verbatim
/-- Abstract pre-hash/OID binding used by the descriptor-parametric semantics. This descriptor
surface is an extension seam only: constructing a value is not by itself an assertion that the
OID/digest pair is FIPS approved. The closed `SLHDSA.Concrete.Prehash.Algorithm` enumeration is
the FIPS-approved registry; callers wanting FIPS conformance must use the enum entry points in
`SLHDSA.Concrete.Prehash` (which also enforce the §10.2 strength policy) rather than
instantiating descriptors directly. -/
structure PrehashDescriptor where
  oidDer : List Byte
  outputLength : ℕ
  digest : List Byte → Except Error (Bytes outputLength)


-- @@ L52-57 verbatim
/-- Enforce the Algorithm 22--25 context bound before evaluating the message body or pre-hash. -/
def requireContext (context : List Byte) : Except Error Unit :=
  if context.length ≤ 255 then
    .ok ()
  else
    .error (.contextTooLong context.length)


-- @@ L59-61 verbatim
/-- A context within the FIPS 205 255-byte bound passes the boundary check. -/
theorem requireContext_eq_ok (context : List Byte) (h : context.length ≤ 255) :
    requireContext context = .ok () := if_pos h


-- @@ L63-66 verbatim
/-- A context beyond the FIPS 205 255-byte bound is rejected with its observed length. -/
theorem requireContext_eq_error (context : List Byte) (h : 255 < context.length) :
    requireContext context = .error (.contextTooLong context.length) :=
  if_neg (Nat.not_le.mpr h)


-- @@ L68-72 verbatim
/-- Common FIPS external-message encoder. Domain `0` denotes pure signing and domain `1`
denotes pre-hash signing. -/
def encodeMessage (domain : Byte) (context body : List Byte) : Except Error (List Byte) := do
  requireContext context
  return [domain, UInt8.ofNat context.length] ++ context ++ body


-- @@ L74-76 verbatim
/-- Algorithm 22/24 message input: `0x00 || toByte(|ctx|, 1) || ctx || M`. -/
def encodePureMessage (context message : List Byte) : Except Error (List Byte) :=
  encodeMessage 0 context message


-- @@ L78-85 verbatim
/-- Under the context bound, the pure encoder is a deterministic total function of its inputs;
in particular signing and verification compute the same `M'`. -/
theorem encodePureMessage_eq_ok (context message : List Byte) (h : context.length ≤ 255) :
    encodePureMessage context message =
      .ok ([0, UInt8.ofNat context.length] ++ context ++ message) := by
  unfold encodePureMessage encodeMessage
  rw [requireContext_eq_ok context h]
  rfl


-- @@ L87-91 verbatim
/-- The empty-context external encoding is exactly the compatibility surface's
`emptyContextMessage`, so the two definitions of the FIPS `M'` for the empty context cannot
diverge. -/
@[simp] theorem encodePureMessage_nil (message : List Byte) :
    encodePureMessage [] message = .ok (emptyContextMessage message) := rfl


-- @@ L93-100 verbatim
/-- Descriptor-parametric Algorithm 23/25 message input:
`0x01 || toByte(|ctx|, 1) || ctx || OID || PH(M)`. FIPS-facing adapters must bind the descriptor
to an approved algorithm and enforce the security-strength requirement. -/
def encodePrehashMessageWithDescriptor (prehash : PrehashDescriptor)
    (context message : List Byte) : Except Error (List Byte) := do
  requireContext context
  let digest ← prehash.digest message
  encodeMessage 1 context (prehash.oidDer ++ digest.toList)


-- @@ L102-113 verbatim
/-- Under the context bound and a successful descriptor digest, the pre-hash encoder is a
deterministic total function of its inputs; in particular signing and verification compute the
same `M'`. -/
theorem encodePrehashMessageWithDescriptor_eq_ok (prehash : PrehashDescriptor)
    (context message : List Byte) (h : context.length ≤ 255)
    {digest : Bytes prehash.outputLength} (hdigest : prehash.digest message = .ok digest) :
    encodePrehashMessageWithDescriptor prehash context message =
      .ok ([1, UInt8.ofNat context.length] ++ context ++
        (prehash.oidDer ++ digest.toList)) := by
  unfold encodePrehashMessageWithDescriptor encodeMessage
  rw [requireContext_eq_ok context h, hdigest]
  rfl


-- @@ L115-121 verbatim
/-- Algorithm 21 after its approved random-bit generator has produced the three seeds. This
explicit boundary is the deterministic entry point used by ACVP key-generation vectors. -/
def keygenWithSeeds (vp : ValidatedParams) (prims : Primitives vp.params)
    (skSeed : prims.SkSeed) (skPrf : prims.SkPrf) (pkSeed : prims.PkSeed) :
    SecretKeyCore prims.core × PublicKeyCore prims.core :=
  let (pk, sk) := GeneralScheme.keygenInternal vp prims skSeed skPrf pkSeed
  (sk, pk)


-- @@ L123-131 expanded
/-- Algorithm 21 under the repository's ideal total random source. -/
noncomputable def keygen (vp : ValidatedParams) (prims : Primitives vp.params)
    [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.PkSeed] :
    ProbComp (SecretKeyCore prims.core × PublicKeyCore prims.core) := do
  let skSeed ← uniformSample prims.SkSeed
  let skPrf ← uniformSample prims.SkPrf
  let pkSeed ← uniformSample prims.PkSeed
  pure (keygenWithSeeds vp prims skSeed skPrf pkSeed)


-- @@ L133-138 verbatim
/-- Algorithm 22 with caller-supplied hedging randomness. -/
def signPureWithRandomizer (vp : ValidatedParams) (prims : Primitives vp.params)
    (message context : List Byte) (sk : SecretKeyCore prims.core) (addrnd : prims.Y) :
    Except Error (GeneralScheme.SignatureCore vp prims.core) := do
  let encoded ← encodePureMessage context message
  return GeneralScheme.signInternal vp prims encoded sk addrnd


-- @@ L140-150 verbatim
/-- Deterministic Algorithm 22. FIPS 205 Algorithm 19 line 2 normatively sets
`opt_rand = PK.seed`; the conversion is an explicit parameter only because the proof-level
primitive interface deliberately keeps `PkSeed` and `Y` independent. FIPS-conforming callers
must pass the canonical conversion for the selected approved family
(`SLHDSA.Concrete.approvedRandomizerOfPkSeed`), or use the pinned entry point
`SLHDSA.Concrete.signPureDeterministicApproved` which does so. -/
def signPureDeterministic (vp : ValidatedParams) (prims : Primitives vp.params)
    (pkSeedToRandomizer : prims.PkSeed → prims.Y) (message context : List Byte)
    (sk : SecretKeyCore prims.core) :
    Except Error (GeneralScheme.SignatureCore vp prims.core) :=
  signPureWithRandomizer vp prims message context sk (pkSeedToRandomizer sk.pkSeed)


-- @@ L152-160 expanded
/-- Default hedged Algorithm 22 under the repository's ideal total random source. -/
noncomputable def signPure (vp : ValidatedParams) (prims : Primitives vp.params)
    [SampleableType prims.Y] (message context : List Byte) (sk : SecretKeyCore prims.core) :
    ProbComp (Except Error (GeneralScheme.SignatureCore vp prims.core)) :=
  match encodePureMessage context message with
  | .error error => pure (.error error)
  | .ok encoded => do
    let addrnd ← uniformSample prims.Y
    pure (.ok (GeneralScheme.signInternal vp prims encoded sk addrnd))


-- @@ L162-168 verbatim
/-- Descriptor-parametric Algorithm 23 core with caller-supplied hedging randomness. -/
def signPrehashWithDescriptorAndRandomizer (vp : ValidatedParams)
    (prims : Primitives vp.params) (prehash : PrehashDescriptor) (message context : List Byte)
    (sk : SecretKeyCore prims.core) (addrnd : prims.Y) :
    Except Error (GeneralScheme.SignatureCore vp prims.core) := do
  let encoded ← encodePrehashMessageWithDescriptor prehash context message
  return GeneralScheme.signInternal vp prims encoded sk addrnd


-- @@ L170-180 verbatim
/-- Deterministic descriptor-parametric Algorithm 23 core. FIPS 205 Algorithm 19 line 2
normatively sets `opt_rand = PK.seed`; FIPS-conforming callers must pass the canonical
conversion (`SLHDSA.Concrete.approvedRandomizerOfPkSeed`), or use the pinned checked entry
point `SLHDSA.Concrete.Prehash.signDeterministicApproved` which does so. -/
def signPrehashWithDescriptorDeterministic (vp : ValidatedParams)
    (prims : Primitives vp.params) (pkSeedToRandomizer : prims.PkSeed → prims.Y)
    (prehash : PrehashDescriptor)
    (message context : List Byte) (sk : SecretKeyCore prims.core) :
    Except Error (GeneralScheme.SignatureCore vp prims.core) :=
  signPrehashWithDescriptorAndRandomizer vp prims prehash message context sk
    (pkSeedToRandomizer sk.pkSeed)


-- @@ L182-192 expanded
/-- Descriptor-parametric hedged Algorithm 23 core under the ideal total random source. -/
noncomputable def signPrehashWithDescriptor (vp : ValidatedParams) (prims : Primitives vp.params)
    [SampleableType prims.Y] (prehash : PrehashDescriptor) (message context : List Byte)
    (sk : SecretKeyCore prims.core) :
    ProbComp (Except Error (GeneralScheme.SignatureCore vp prims.core)) :=
  match encodePrehashMessageWithDescriptor prehash context message with
  | .error error => pure (.error error)
  | .ok encoded => do
    let addrnd ← uniformSample prims.Y
    pure (.ok (GeneralScheme.signInternal vp prims encoded sk addrnd))


-- @@ L194-201 verbatim
/-- Algorithm 24. An overlong context is rejected as `false`. -/
def verifyPure (vp : ValidatedParams) (prims : Primitives vp.params)
    [DecidableEq prims.Y] (message : List Byte)
    (signature : GeneralScheme.SignatureCore vp prims.core) (context : List Byte)
    (pk : PublicKeyCore prims.core) : Bool :=
  match encodePureMessage context message with
  | .error _ => false
  | .ok encoded => GeneralScheme.verifyInternal vp prims encoded signature pk


-- @@ L203-210 verbatim
/-- Descriptor-parametric Algorithm 25 core. An overlong context or digest failure is rejected. -/
def verifyPrehashWithDescriptor (vp : ValidatedParams) (prims : Primitives vp.params)
    [DecidableEq prims.Y] (prehash : PrehashDescriptor) (message : List Byte)
    (signature : GeneralScheme.SignatureCore vp prims.core) (context : List Byte)
    (pk : PublicKeyCore prims.core) : Bool :=
  match encodePrehashMessageWithDescriptor prehash context message with
  | .error _ => false
  | .ok encoded => GeneralScheme.verifyInternal vp prims encoded signature pk


-- @@ L212-218 verbatim
/-! ## External completeness and boundary rejection

Signing and verification encode `M'` with the same deterministic encoder, so the external
sign→verify round trips are corollaries of the internal completeness theorem
`GeneralScheme.verifyInternal_signInternal`.  Both statements quantify over an arbitrary
hedging randomizer, covering the hedged and the deterministic (`opt_rand = PK.seed`) variants
at once. -/


-- @@ L220-234 verbatim
/-- **External pure completeness** (Algorithms 21, 22, 24): under the FIPS 205 context bound,
pure-mode signing under an honestly generated key succeeds, and verifying the produced
signature for the same message and context with the matching public key accepts. -/
theorem verifyPure_signPureWithRandomizer (vp : ValidatedParams) (prims : Primitives vp.params)
    [DecidableEq prims.Y] (message context : List Byte)
    (skSeed : prims.SkSeed) (skPrf : prims.SkPrf) (pkSeed : prims.PkSeed) (addrnd : prims.Y)
    (hcontext : context.length ≤ 255) :
    (signPureWithRandomizer vp prims message context
        (keygenWithSeeds vp prims skSeed skPrf pkSeed).1 addrnd).map
      (fun signature => verifyPure vp prims message signature context
        (keygenWithSeeds vp prims skSeed skPrf pkSeed).2) = .ok true := by
  simp only [signPureWithRandomizer, verifyPure,
    encodePureMessage_eq_ok context message hcontext]
  exact congrArg Except.ok
    (GeneralScheme.verifyInternal_signInternal vp prims _ skSeed skPrf pkSeed addrnd)


-- @@ L236-253 verbatim
/-- **External pre-hash completeness** (Algorithms 21, 23, 25): under the FIPS 205 context
bound and a successful descriptor digest, pre-hash signing under an honestly generated key
succeeds, and verifying the produced signature for the same message and context with the
matching public key accepts. -/
theorem verifyPrehashWithDescriptor_signPrehashWithDescriptorAndRandomizer
    (vp : ValidatedParams) (prims : Primitives vp.params) [DecidableEq prims.Y]
    (prehash : PrehashDescriptor) (message context : List Byte)
    (skSeed : prims.SkSeed) (skPrf : prims.SkPrf) (pkSeed : prims.PkSeed) (addrnd : prims.Y)
    (hcontext : context.length ≤ 255)
    {digest : Bytes prehash.outputLength} (hdigest : prehash.digest message = .ok digest) :
    (signPrehashWithDescriptorAndRandomizer vp prims prehash message context
        (keygenWithSeeds vp prims skSeed skPrf pkSeed).1 addrnd).map
      (fun signature => verifyPrehashWithDescriptor vp prims prehash message signature context
        (keygenWithSeeds vp prims skSeed skPrf pkSeed).2) = .ok true := by
  simp only [signPrehashWithDescriptorAndRandomizer, verifyPrehashWithDescriptor,
    encodePrehashMessageWithDescriptor_eq_ok prehash context message hcontext hdigest]
  exact congrArg Except.ok
    (GeneralScheme.verifyInternal_signInternal vp prims _ skSeed skPrf pkSeed addrnd)


-- @@ L255-264 verbatim
/-- Algorithm 24 lines 1--2: pure verification rejects an overlong context as `false` for
every signature and public key, before any hashing. -/
theorem verifyPure_eq_false_of_contextTooLong (vp : ValidatedParams)
    (prims : Primitives vp.params) [DecidableEq prims.Y] (message : List Byte)
    (signature : GeneralScheme.SignatureCore vp prims.core) (context : List Byte)
    (pk : PublicKeyCore prims.core) (h : 255 < context.length) :
    verifyPure vp prims message signature context pk = false := by
  unfold verifyPure encodePureMessage encodeMessage
  rw [requireContext_eq_error context h]
  rfl


-- @@ L266-275 verbatim
/-- Algorithm 25 lines 1--2: pre-hash verification rejects an overlong context as `false` for
every signature and public key, before evaluating the pre-hash. -/
theorem verifyPrehashWithDescriptor_eq_false_of_contextTooLong (vp : ValidatedParams)
    (prims : Primitives vp.params) [DecidableEq prims.Y] (prehash : PrehashDescriptor)
    (message : List Byte) (signature : GeneralScheme.SignatureCore vp prims.core)
    (context : List Byte) (pk : PublicKeyCore prims.core) (h : 255 < context.length) :
    verifyPrehashWithDescriptor vp prims prehash message signature context pk = false := by
  unfold verifyPrehashWithDescriptor encodePrehashMessageWithDescriptor
  rw [requireContext_eq_error context h]
  rfl


-- @@ L277-277 verbatim
end SLHDSA.External
