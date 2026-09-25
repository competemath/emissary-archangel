/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module

public import VCVio.CryptoFoundations.PRF
public import VCVio.OracleComp.SimSemantics.StateT.PreservesInv
public import VCVio.OracleComp.QueryTracking.QueryBound


-- @@ L13-23 verbatim
/-!
# PRF Tag/Reader Protocol — Definitions

Core definitions for the RFID-style tag/reader protocol: transcripts, reader replies, session
patterns, the keyed-hash family packaging, game states, oracle specifications, adversary
abbreviations, the real and ideal authentication games, the random-function authentication game,
the unlinkability games, and the bad-event world.

The auth→PRF reduction and the security theorems built on these definitions live in the sibling
`Auth`, `Collision`, and `BadEvent` modules.
-/


-- @@ L25-25 verbatim
@[expose] public section


-- @@ L27-27 verbatim
open OracleComp OracleSpec ENNReal


-- @@ L29-29 verbatim
namespace PRFTagReader



-- @@ L32-36 verbatim
/-- Transcript emitted by a tag in one session: a fresh nonce together with its authenticator. -/
structure TagTranscript (Nonce Digest : Type) where
  nonce : Nonce
  auth : Digest
deriving DecidableEq, Repr


-- @@ L38-43 verbatim
/-- Reader's protocol response. `ok` means that the transcript was accepted, and `ko` means that
it was rejected. -/
inductive ReaderReply where
  | ok
  | ko
deriving DecidableEq, Repr, Inhabited


-- @@ L45-45 verbatim
namespace ReaderReply


-- @@ L47-50 verbatim
/-- Convert a boolean acceptance decision into the concrete protocol reply. -/
def ofBool : Bool → ReaderReply
  | true => .ok
  | false => .ko


-- @@ L52-55 verbatim
/-- Predicate exposing whether a reader reply is accepting. -/
def accepts : ReaderReply → Bool
  | .ok => true
  | .ko => false


-- @@ L57-57 verbatim
end ReaderReply


-- @@ L59-63 verbatim
/-- Session-slot assignment for a tag/reader world with `sessionsPerTag` many protocol sessions
available to each tag. Real unlinkability worlds reuse one slot per tag; ideal worlds may allocate
a fresh slot per session. -/
structure SessionPattern (TagId Slot : Type) (sessionsPerTag : ℕ) where
  slot : TagId → Fin sessionsPerTag → Slot


-- @@ L65-65 verbatim
section Pattern


-- @@ L67-67 verbatim
variable {TagId : Type} (sessionsPerTag : ℕ)


-- @@ L69-71 verbatim
/-- Real session pattern: every session of a given tag reuses the same slot. -/
def multiplePattern : SessionPattern TagId TagId sessionsPerTag where
  slot := fun tag _ => tag


-- @@ L73-75 verbatim
/-- Ideal unlinkability pattern: each session of each tag receives its own fresh slot. -/
def singlePattern : SessionPattern TagId (TagId × Fin sessionsPerTag) sessionsPerTag where
  slot := fun tag sid => (tag, sid)


-- @@ L77-77 verbatim
end Pattern


-- @@ L79-85 verbatim
/-- Packaging of the two keyed hash families used by the protocol. `evalMultiple` models secret
reuse across all sessions of a tag, while `evalSingle` models an independent secret for each
session of each tag. -/
structure TagReaderPRFs (K TagId Nonce Digest : Type) (sessionsPerTag : ℕ) where
  keygen : ProbComp K
  evalMultiple : K → TagId → Nonce → Digest
  evalSingle : K → TagId → Fin sessionsPerTag → Nonce → Digest


-- @@ L87-87 verbatim
namespace TagReaderPRFs


-- @@ L89-90 verbatim
variable {K TagId Nonce Digest : Type} {sessionsPerTag : ℕ}
  (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)


-- @@ L92-95 verbatim
/-- Derived PRF scheme for the multiple-session world. -/
def multiplePRFScheme : PRFScheme K (TagId × Nonce) Digest where
  keygen := prfs.keygen
  eval := fun k input => prfs.evalMultiple k input.1 input.2


-- @@ L97-100 verbatim
/-- Derived PRF scheme for the single-session world. -/
def singlePRFScheme : PRFScheme K ((TagId × Fin sessionsPerTag) × Nonce) Digest where
  keygen := prfs.keygen
  eval := fun k input => prfs.evalSingle k input.1.1 input.1.2 input.2


-- @@ L102-102 verbatim
end TagReaderPRFs


-- @@ L104-108 verbatim
/-- Authentication-game state: the honest tag transcripts emitted so far, together with all
reader acceptances that cannot be traced back to a prior honest tag output. -/
structure AuthState (TagId Nonce Digest : Type) where
  honestOutputs : Finset (TagId × TagTranscript Nonce Digest)
  readerForged : Finset (TagId × TagTranscript Nonce Digest)


-- @@ L110-115 expanded
/-- Ideal authentication-game state: the cached random-function table, together with the same
observable logs used in the real game. -/
structure AuthIdealState (TagId Nonce Digest : Type) where
  responses : (OracleSpec.ofFn (ι := (TagId × Nonce)) (fun _ => Digest)).QueryCache
  honestOutputs : Finset (TagId × TagTranscript Nonce Digest)
  readerForged : Finset (TagId × TagTranscript Nonce Digest)


-- @@ L117-117 verbatim
section AuthState


-- @@ L119-120 verbatim
variable {TagId Nonce Digest : Type}
  [DecidableEq TagId] [DecidableEq Nonce] [DecidableEq Digest]


-- @@ L122-125 verbatim
/-- Initial real authentication-game state. -/
def AuthState.init : AuthState TagId Nonce Digest where
  honestOutputs := ∅
  readerForged := ∅


-- @@ L127-131 verbatim
/-- Initial ideal authentication-game state. -/
def AuthIdealState.init : AuthIdealState TagId Nonce Digest where
  responses := ∅
  honestOutputs := ∅
  readerForged := ∅


-- @@ L133-133 verbatim
end AuthState


-- @@ L135-137 verbatim
/-- Unlinkability-game state: how many sessions of each tag have already been consumed. -/
structure UnlinkState (TagId : Type) where
  sessionsUsed : TagId → ℕ


-- @@ L139-149 expanded
/-- Bad-world state for the multiple-session unlinkability proof: session counters, the list of
random-function responses seen for each `(tag, nonce)` pair, the tag-side bad-event flag, and a
separate reader-side bad-event flag (`cacheBad`) used by the direct-coupling argument to absorb
slot-positive trace-union residue on the reader branch. The two flags are independent: tag steps
may flip `bad` but never touch `cacheBad`; reader steps may flip `cacheBad` but never touch `bad`.
-/
structure UnlinkBadState (TagId Nonce Digest : Type) where
  sessionsUsed : TagId → ℕ
  responses : (OracleSpec.ofFn (ι := (TagId × Nonce)) (fun _ => List Digest)).QueryCache
  bad : Bool
  cacheBad : Bool


-- @@ L151-151 verbatim
section UnlinkState


-- @@ L153-154 verbatim
variable {TagId Nonce Digest : Type}
  [DecidableEq TagId] [DecidableEq Nonce] [DecidableEq Digest]


-- @@ L156-158 verbatim
/-- Initial unlinkability-game state. -/
def UnlinkState.init : UnlinkState TagId where
  sessionsUsed := fun _ => 0


-- @@ L160-165 verbatim
/-- Initial unlinkability bad-event state. -/
def UnlinkBadState.init : UnlinkBadState TagId Nonce Digest where
  sessionsUsed := fun _ => 0
  responses := ∅
  bad := false
  cacheBad := false


-- @@ L167-167 verbatim
end UnlinkState


-- @@ L169-171 expanded
/-- Authentication-game oracle interface: a tag oracle and a reader oracle. -/
def AuthOracleSpec (TagId Nonce Digest : Type) :=
  (OracleSpec.ofFn (ι := TagId) (fun _ => TagTranscript Nonce Digest)) +
    (OracleSpec.ofFn (ι := (TagTranscript Nonce Digest)) (fun _ => ReaderReply))


-- @@ L173-176 expanded
/-- Unlinkability-game oracle interface: a session-bounded tag oracle and a reader oracle. -/
def UnlinkOracleSpec (TagId Nonce Digest : Type) :=
  (OracleSpec.ofFn (ι := TagId) (fun _ => Option (TagTranscript Nonce Digest))) +
    (OracleSpec.ofFn (ι := (TagTranscript Nonce Digest)) (fun _ => ReaderReply))


-- @@ L178-180 verbatim
/-- The tag side of the authentication interface returns a concrete transcript. -/
@[simp] lemma authOracleSpec_range_inl {TagId Nonce Digest : Type} (tag : TagId) :
    (AuthOracleSpec TagId Nonce Digest).Range (Sum.inl tag) = TagTranscript Nonce Digest := rfl


-- @@ L182-185 verbatim
/-- The reader side of the authentication interface returns a concrete reader reply. -/
@[simp] lemma authOracleSpec_range_inr {TagId Nonce Digest : Type}
    (transcript : TagTranscript Nonce Digest) :
    (AuthOracleSpec TagId Nonce Digest).Range (Sum.inr transcript) = ReaderReply := rfl


-- @@ L187-190 verbatim
/-- The tag side of the unlinkability interface returns an optional transcript. -/
@[simp] lemma unlinkOracleSpec_range_inl {TagId Nonce Digest : Type} (tag : TagId) :
    (UnlinkOracleSpec TagId Nonce Digest).Range (Sum.inl tag) =
      Option (TagTranscript Nonce Digest) := rfl


-- @@ L192-195 verbatim
/-- The reader side of the unlinkability interface returns a concrete reader reply. -/
@[simp] lemma unlinkOracleSpec_range_inr {TagId Nonce Digest : Type}
    (transcript : TagTranscript Nonce Digest) :
    (UnlinkOracleSpec TagId Nonce Digest).Range (Sum.inr transcript) = ReaderReply := rfl


-- @@ L197-199 verbatim
/-- Authentication adversaries are oracle computations over the tag and reader interfaces. -/
abbrev AuthAdversary (TagId Nonce Digest : Type) :=
  OracleComp (AuthOracleSpec TagId Nonce Digest) Unit


-- @@ L201-203 verbatim
/-- Unlinkability adversaries are oracle computations over the bounded-tag and reader interfaces. -/
abbrev UnlinkAdversary (TagId Nonce Digest : Type) :=
  OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool


-- @@ L205-205 verbatim
section AuthGame


-- @@ L207-210 verbatim
variable {TagId Nonce Digest : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest]


-- @@ L212-223 expanded
/-- Honest tag oracle for the real authentication game. -/
def authTagQueryImpl (hash : TagId → Nonce → Digest) :
    QueryImpl (OracleSpec.ofFn (ι := TagId) (fun _ => TagTranscript Nonce Digest))
      (StateT (AuthState TagId Nonce Digest) ProbComp) :=
  fun tag => do
  let st ← get
  let nonce ← (uniformSample Nonce : ProbComp Nonce)
  let auth := hash tag nonce
  let transcript : TagTranscript Nonce Digest := ⟨nonce, auth⟩
  set { st with honestOutputs := insert (tag, transcript) st.honestOutputs }
  return transcript


-- @@ L225-236 expanded
/-- Reader oracle for the real authentication game. It accepts any transcript that
matches some tag's hash image and logs acceptances that were never emitted by the honest tag
oracle. -/
def authReaderQueryImpl (hash : TagId → Nonce → Digest) :
    QueryImpl (OracleSpec.ofFn (ι := (TagTranscript Nonce Digest)) (fun _ => ReaderReply))
      (StateT (AuthState TagId Nonce Digest) ProbComp) :=
  fun transcript => do
  let st ← get
  let accepted := decide (∃ tag, hash tag transcript.nonce = transcript.auth)
  let newForged :=
    Finset.univ.filter fun tag =>
      hash tag transcript.nonce = transcript.auth ∧ (tag, transcript) ∉ st.honestOutputs
  set { st with readerForged := st.readerForged ∪ (newForged.image (·, transcript)) }
  return ReaderReply.ofBool accepted


-- @@ L238-243 verbatim
/-- Combined real-game oracle implementation for authentication. -/
def authRealQueryImpl (hash : TagId → Nonce → Digest) :
    QueryImpl (AuthOracleSpec TagId Nonce Digest)
      (StateT (AuthState TagId Nonce Digest) ProbComp) :=
  authTagQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) hash +
    authReaderQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) hash


-- @@ L245-254 verbatim
/-- Real active-authentication experiment. -/
def authExp {K : Type} {sessionsPerTag : ℕ}
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : AuthAdversary TagId Nonce Digest) : ProbComp Bool := do
  let k ← prfs.keygen
  let (_, st) ← (simulateQ
    (authRealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (fun tag nonce => prfs.evalMultiple k tag nonce))
    adversary).run AuthState.init
  return decide (st.readerForged ≠ ∅)


-- @@ L256-256 verbatim
end AuthGame


-- @@ L258-258 verbatim
section AuthIdealGame


-- @@ L260-263 verbatim
variable {TagId Nonce Digest : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]


-- @@ L265-284 expanded
/-- Honest tag oracle for the ideal authentication world. It queries a lazy random
function table and records the emitted transcript. -/
def authIdealTagQueryImpl :
    QueryImpl (OracleSpec.ofFn (ι := TagId) (fun _ => TagTranscript Nonce Digest))
      (StateT (AuthIdealState TagId Nonce Digest) ProbComp) :=
  fun tag => do
  let st ← get
  let nonce ← (uniformSample Nonce : ProbComp Nonce)
  let key := (tag, nonce)
  let (auth, responses) ←
    match st.responses key with
    | some out =>
      pure (out, st.responses)
    | none =>
      do
        let out ← (uniformSample Digest : ProbComp Digest)
        pure (out, st.responses.cacheQuery key out)
  let transcript : TagTranscript Nonce Digest := ⟨nonce, auth⟩
  set ({  responses := responses
          honestOutputs := insert (tag, transcript) st.honestOutputs
          readerForged := st.readerForged } : AuthIdealState TagId Nonce Digest)
  return transcript


-- @@ L286-301 expanded
/-- Reader oracle for the ideal authentication world. It only accepts transcripts that
were previously generated for the queried tag and nonce in the cached random-function table. -/
def authIdealReaderQueryImpl :
    QueryImpl (OracleSpec.ofFn (ι := (TagTranscript Nonce Digest)) (fun _ => ReaderReply))
      (StateT (AuthIdealState TagId Nonce Digest) ProbComp) :=
  fun transcript => do
  let st ← get
  let matching :=
    Finset.univ.filter fun tag => st.responses (tag, transcript.nonce) = some transcript.auth
  let newForged := matching.filter fun tag => (tag, transcript) ∉ st.honestOutputs
  set ({  responses := st.responses
          honestOutputs := st.honestOutputs
          readerForged := st.readerForged ∪ (newForged.image (·, transcript)) } :
        AuthIdealState TagId Nonce Digest)
  return ReaderReply.ofBool (decide (matching.Nonempty))


-- @@ L303-308 verbatim
/-- Combined ideal-game oracle implementation for authentication. -/
def authIdealQueryImpl :
    QueryImpl (AuthOracleSpec TagId Nonce Digest)
      (StateT (AuthIdealState TagId Nonce Digest) ProbComp) :=
  authIdealTagQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) +
    authIdealReaderQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)


-- @@ L310-317 verbatim
/-- Ideal active-authentication experiment. The keyed hash is replaced by a lazy random function on
`(tag, nonce)`, and the reader only accepts transcripts that match the cached table. -/
def authIdealExp
    (adversary : AuthAdversary TagId Nonce Digest) : ProbComp Bool := do
  let (_, st) ← (simulateQ
    (authIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
    adversary).run AuthIdealState.init
  return decide (st.readerForged ≠ ∅)


-- @@ L319-319 verbatim
end AuthIdealGame


-- @@ L321-321 verbatim
section AuthRFGame


-- @@ L323-326 verbatim
variable {TagId Nonce Digest : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]


-- @@ L328-340 expanded
/-- Lazy random-function lookup at `(tag, nonce)`: return the cached digest if present, otherwise
sample a fresh uniform digest and cache it. This is the `randomOracle` step expressed directly on
the `responses` table of `AuthIdealState`. -/
def authRFLookup (tag : TagId) (nonce : Nonce) :
    StateT (AuthIdealState TagId Nonce Digest) ProbComp Digest := do
  let st ← get
  match st.responses (tag, nonce) with
  | some d =>
    pure d
  | none =>
    let d ← (uniformSample Digest : ProbComp Digest)
    set
        ({ st with responses := st.responses.cacheQuery (tag, nonce) d } :
          AuthIdealState TagId Nonce Digest)
    return d


-- @@ L342-360 expanded
/-- Reader oracle for the random-function authentication world. Unlike the look-up-only
`authIdealReaderQueryImpl`, this reader queries the lazy random function for every tag at the
transcript's nonce, creating fresh cache entries for uncached pairs. It accepts when some digest
matches the submitted authenticator and records non-honest matches as forgeries. -/
noncomputable def authRFReaderQueryImpl :
    QueryImpl (OracleSpec.ofFn (ι := (TagTranscript Nonce Digest)) (fun _ => ReaderReply))
      (StateT (AuthIdealState TagId Nonce Digest) ProbComp) :=
  fun transcript => do
  let pairs ←
    (Finset.univ : Finset TagId).toList.mapM
        (fun tag => do
          let d ←
            authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest) tag transcript.nonce
          return (tag, d))
  let st ← get
  let accepted : Bool := decide (∃ p ∈ pairs, p.2 = transcript.auth)
  let newForged : Finset TagId :=
    ((pairs.filter fun p =>
            decide (p.2 = transcript.auth ∧ (p.1, transcript) ∉ st.honestOutputs)).map
        Prod.fst).toFinset
  set
      ({ st with readerForged := st.readerForged ∪ (newForged.image (·, transcript)) } :
        AuthIdealState TagId Nonce Digest)
  return ReaderReply.ofBool accepted


-- @@ L362-368 verbatim
/-- Combined oracle implementation for the random-function authentication world: the honest tag
oracle of the ideal world together with the fresh-drawing random-function reader. -/
noncomputable def authRFQueryImpl :
    QueryImpl (AuthOracleSpec TagId Nonce Digest)
      (StateT (AuthIdealState TagId Nonce Digest) ProbComp) :=
  authIdealTagQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) +
    authRFReaderQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)


-- @@ L370-377 verbatim
/-- Direct form of the random-function authentication experiment: run the adversary against
`authRFQueryImpl` and win when a forged reader acceptance is recorded. -/
noncomputable def authRFDirectExp
    (adversary : AuthAdversary TagId Nonce Digest) : ProbComp Bool := do
  let (_, st) ← (simulateQ
    (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
    adversary).run AuthIdealState.init
  return decide (st.readerForged ≠ ∅)


-- @@ L379-379 verbatim
end AuthRFGame

-- @@ L380-380 verbatim
section UnlinkGame


-- @@ L382-386 verbatim
variable {TagId Slot Nonce Digest : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]


-- @@ L388-393 verbatim
/-- Reader acceptance for a fixed tag in a given unlinkability session pattern. -/
def tagAccepts (hash : Slot → Nonce → Digest)
    (pattern : SessionPattern TagId Slot sessionsPerTag)
    (tag : TagId) (transcript : TagTranscript Nonce Digest) : Bool :=
  decide (∃ sid : Fin sessionsPerTag,
    hash (pattern.slot tag sid) transcript.nonce = transcript.auth)


-- @@ L395-401 verbatim
/-- Reader acceptance test for a fixed unlinkability session pattern. -/
def unlinkReaderAccepts (hash : Slot → Nonce → Digest)
    (pattern : SessionPattern TagId Slot sessionsPerTag)
    (transcript : TagTranscript Nonce Digest) : Bool :=
  decide (∃ tag,
    tagAccepts (TagId := TagId) (Slot := Slot) (Nonce := Nonce) (Digest := Digest)
      hash pattern tag transcript)


-- @@ L403-420 expanded
/-- Tag oracle for a fixed unlinkability session pattern. It returns `none` once the session cap
for the queried tag is exhausted. -/
def unlinkTagQueryImpl (hash : Slot → Nonce → Digest)
    (pattern : SessionPattern TagId Slot sessionsPerTag) :
    QueryImpl (OracleSpec.ofFn (ι := TagId) (fun _ => Option (TagTranscript Nonce Digest)))
      (StateT (UnlinkState TagId) ProbComp) :=
  fun tag => do
  let st ← get
  if h : st.sessionsUsed tag < sessionsPerTag then 
    let sid : Fin sessionsPerTag := ⟨st.sessionsUsed tag, h⟩
    let nonce ← (uniformSample Nonce : ProbComp Nonce)
    let auth := hash (pattern.slot tag sid) nonce
    let transcript : TagTranscript Nonce Digest := ⟨nonce, auth⟩
    set { st with sessionsUsed := Function.update st.sessionsUsed tag (st.sessionsUsed tag + 1) }
    return some transcript
  else
    return none


-- @@ L422-428 expanded
/-- Reader oracle for a fixed unlinkability session pattern. -/
def unlinkReaderQueryImpl (hash : Slot → Nonce → Digest)
    (pattern : SessionPattern TagId Slot sessionsPerTag) :
    QueryImpl (OracleSpec.ofFn (ι := (TagTranscript Nonce Digest)) (fun _ => ReaderReply))
      (StateT (UnlinkState TagId) ProbComp) :=
  fun transcript =>
  return
    ReaderReply.ofBool <|
      unlinkReaderAccepts (TagId := TagId) (Slot := Slot) (Nonce := Nonce) (Digest := Digest) hash
        pattern transcript


-- @@ L430-441 verbatim
/-- Combined multiple-session unlinkability oracle implementation. -/
def unlinkMultipleQueryImpl {K : Type}
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (k : K) :
    QueryImpl (UnlinkOracleSpec TagId Nonce Digest)
      (StateT (UnlinkState TagId) ProbComp) :=
  unlinkTagQueryImpl (TagId := TagId) (Slot := TagId) (Nonce := Nonce) (Digest := Digest)
    (fun tag nonce => prfs.evalMultiple k tag nonce)
    (multiplePattern (TagId := TagId) sessionsPerTag) +
    unlinkReaderQueryImpl (TagId := TagId) (Slot := TagId) (Nonce := Nonce) (Digest := Digest)
      (fun tag nonce => prfs.evalMultiple k tag nonce)
      (multiplePattern (TagId := TagId) sessionsPerTag)


-- @@ L443-456 verbatim
/-- Combined single-session unlinkability oracle implementation. -/
def unlinkSingleQueryImpl {K : Type}
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (k : K) :
    QueryImpl (UnlinkOracleSpec TagId Nonce Digest)
      (StateT (UnlinkState TagId) ProbComp) :=
  unlinkTagQueryImpl (TagId := TagId) (Slot := TagId × Fin sessionsPerTag)
    (Nonce := Nonce) (Digest := Digest)
    (fun slot nonce => prfs.evalSingle k slot.1 slot.2 nonce)
    (singlePattern (TagId := TagId) sessionsPerTag) +
    unlinkReaderQueryImpl (TagId := TagId) (Slot := TagId × Fin sessionsPerTag)
      (Nonce := Nonce) (Digest := Digest)
      (fun slot nonce => prfs.evalSingle k slot.1 slot.2 nonce)
      (singlePattern (TagId := TagId) sessionsPerTag)


-- @@ L458-464 verbatim
/-- Multiple-session unlinkability world: each tag reuses its own slot across all sessions. -/
def unlinkMultipleExp {K : Type}
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest) : ProbComp Bool := do
  let k ← prfs.keygen
  (simulateQ (unlinkMultipleQueryImpl (TagId := TagId) (Nonce := Nonce)
    (Digest := Digest) prfs k) adversary).run' UnlinkState.init


-- @@ L466-473 verbatim
/-- Single-session unlinkability world: each tag query consumes a fresh slot, while the reader
checks all session slots for that tag. -/
def unlinkSingleExp {K : Type}
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest) : ProbComp Bool := do
  let k ← prfs.keygen
  (simulateQ (unlinkSingleQueryImpl (TagId := TagId) (Nonce := Nonce)
    (Digest := Digest) prfs k) adversary).run' UnlinkState.init


-- @@ L475-483 expanded
/-- One-sided unlinkability gap `Pr[Multiple] - Pr[Single]` between the two session-allocation
worlds. -/
noncomputable def unlinkabilityAdvantage {K : Type}
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest) : ℝ :=
  (probOutput
        (unlinkMultipleExp (TagId := TagId) (Nonce := Nonce) (Digest := Digest) (sessionsPerTag :=
          sessionsPerTag) prfs adversary)
        true).toReal -
    (probOutput
        (unlinkSingleExp (TagId := TagId) (Nonce := Nonce) (Digest := Digest) (sessionsPerTag :=
          sessionsPerTag) prfs adversary)
        true).toReal


-- @@ L485-497 verbatim
/-! ## Failure-freeness of the unlinkability experiments

An `UnlinkAdversary` is an arbitrary `OracleComp (UnlinkOracleSpec …) Bool`, so it may itself
contain `failure`. Because `UnlinkOracleSpec` carries no probability semantics, `NeverFail
adversary` is not even a well-typed statement: failure-freeness of an experiment can only be
asserted *relative to* the adversary not forcing a failure when run in the corresponding world.

The two `…_run` lemmas below record that the handlers add no failure of their own: every oracle
step of `unlinkMultipleQueryImpl` / `unlinkSingleQueryImpl` is built from `$ᵗ`-sampling and pure
state updates, hence never fails. Consequently the experiment fails exactly when the simulated
adversary run does, and the `…_neverFail` lemmas conclude `NeverFail` of the whole experiment from
the honest hypothesis that the adversary run never fails (together with `[NeverFail prfs.keygen]`
for the key sampler). -/


-- @@ L499-514 verbatim
omit [Nonempty TagId] [DecidableEq Nonce] [NeZero sessionsPerTag] in
/-- Every oracle step of the multiple-session handler never fails: the tag step samples a nonce via
`$ᵗ` and performs pure state updates, and the reader step is a pure reply. -/
theorem neverFail_unlinkMultipleQueryImpl_run {K : Type}
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag) (k : K)
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain) (s : UnlinkState TagId) :
    NeverFail ((unlinkMultipleQueryImpl (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) prfs k t).run s) := by
  rcases t with tag | transcript
  · simp only [unlinkMultipleQueryImpl, QueryImpl.add_apply_inl]
    unfold unlinkTagQueryImpl
    refine NeverFail.of_probFailure_eq_zero _ ?_
    simp
  · simp only [unlinkMultipleQueryImpl, QueryImpl.add_apply_inr, unlinkReaderQueryImpl]
    refine NeverFail.of_probFailure_eq_zero _ ?_
    simp


-- @@ L516-531 verbatim
omit [Nonempty TagId] [DecidableEq Nonce] [NeZero sessionsPerTag] in
/-- Every oracle step of the single-session handler never fails: the tag step samples a nonce via
`$ᵗ` and performs pure state updates, and the reader step is a pure reply. -/
theorem neverFail_unlinkSingleQueryImpl_run {K : Type}
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag) (k : K)
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain) (s : UnlinkState TagId) :
    NeverFail ((unlinkSingleQueryImpl (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) prfs k t).run s) := by
  rcases t with tag | transcript
  · simp only [unlinkSingleQueryImpl, QueryImpl.add_apply_inl]
    unfold unlinkTagQueryImpl
    refine NeverFail.of_probFailure_eq_zero _ ?_
    simp
  · simp only [unlinkSingleQueryImpl, QueryImpl.add_apply_inr, unlinkReaderQueryImpl]
    refine NeverFail.of_probFailure_eq_zero _ ?_
    simp


-- @@ L533-548 verbatim
omit [Nonempty TagId] [DecidableEq Nonce] [NeZero sessionsPerTag] in
/-- The multiple-session unlinkability experiment never fails, provided the key sampler never fails
and the adversary, simulated in the multiple-session world, never forces a failure. -/
theorem unlinkMultipleExp_neverFail {K : Type}
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest) [NeverFail prfs.keygen]
    (hrun : ∀ k, NeverFail ((simulateQ (unlinkMultipleQueryImpl
      (TagId := TagId) (Nonce := Nonce) (Digest := Digest) prfs k) adversary).run
        UnlinkState.init)) :
    NeverFail (unlinkMultipleExp (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) prfs adversary) := by
  unfold unlinkMultipleExp
  refine NeverFail.bind_of_forall (hy := fun k => ?_)
  rw [StateT.run']
  have := hrun k
  exact NeverFail.instMap _


-- @@ L550-565 verbatim
omit [Nonempty TagId] [DecidableEq Nonce] [NeZero sessionsPerTag] in
/-- The single-session unlinkability experiment never fails, provided the key sampler never fails
and the adversary, simulated in the single-session world, never forces a failure. -/
theorem unlinkSingleExp_neverFail {K : Type}
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest) [NeverFail prfs.keygen]
    (hrun : ∀ k, NeverFail ((simulateQ (unlinkSingleQueryImpl
      (TagId := TagId) (Nonce := Nonce) (Digest := Digest) prfs k) adversary).run
        UnlinkState.init)) :
    NeverFail (unlinkSingleExp (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) prfs adversary) := by
  unfold unlinkSingleExp
  refine NeverFail.bind_of_forall (hy := fun k => ?_)
  rw [StateT.run']
  have := hrun k
  exact NeverFail.instMap _


-- @@ L567-578 expanded
omit [Nonempty TagId] [DecidableEq Nonce] [NeZero sessionsPerTag] in
/-- `probFailure` form of `unlinkMultipleExp_neverFail`: `Pr[⊥ | multiple experiment] = 0` under
the same hypotheses. -/
theorem probFailure_unlinkMultipleExp_eq_zero {K : Type}
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest) [NeverFail prfs.keygen]
    (hrun :
      ∀ k,
        NeverFail
          ((simulateQ
                (unlinkMultipleQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) prfs
                  k)
                adversary).run
            UnlinkState.init)) :
    probFailure
        (unlinkMultipleExp (TagId := TagId) (Nonce := Nonce) (Digest := Digest) prfs adversary) =
      0 :=
  (unlinkMultipleExp_neverFail prfs adversary hrun).probFailure_eq_zero


-- @@ L580-591 expanded
omit [Nonempty TagId] [DecidableEq Nonce] [NeZero sessionsPerTag] in
/-- `probFailure` form of `unlinkSingleExp_neverFail`: `Pr[⊥ | single experiment] = 0` under the
same hypotheses. -/
theorem probFailure_unlinkSingleExp_eq_zero {K : Type}
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest) [NeverFail prfs.keygen]
    (hrun :
      ∀ k,
        NeverFail
          ((simulateQ
                (unlinkSingleQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) prfs k)
                adversary).run
            UnlinkState.init)) :
    probFailure
        (unlinkSingleExp (TagId := TagId) (Nonce := Nonce) (Digest := Digest) prfs adversary) =
      0 :=
  (unlinkSingleExp_neverFail prfs adversary hrun).probFailure_eq_zero


-- @@ L593-593 verbatim
end UnlinkGame


-- @@ L595-595 verbatim
section BadEvent


-- @@ L597-601 verbatim
variable {TagId Nonce Digest : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]


-- @@ L603-623 expanded
/-- Tag oracle for the `RF_bad` multiple-session collision world. It
samples a fresh ideal hash output on every tag query, records all outputs associated with a given
`(tag, nonce)` pair, and sets `bad` once some pair is queried twice. -/
def unlinkBadTagQueryImpl :
    QueryImpl (OracleSpec.ofFn (ι := TagId) (fun _ => Option (TagTranscript Nonce Digest)))
      (StateT (UnlinkBadState TagId Nonce Digest) ProbComp) :=
  fun tag => do
  let st ← get
  if _h : st.sessionsUsed tag < sessionsPerTag then 
    let nonce ← (uniformSample Nonce : ProbComp Nonce)
    let auth ← (uniformSample Digest : ProbComp Digest)
    let outputs := auth :: Option.getD (st.responses (tag, nonce)) []
    let bad := st.bad || (st.responses (tag, nonce)).isSome
    let transcript : TagTranscript Nonce Digest := ⟨nonce, auth⟩
    set ({  sessionsUsed := Function.update st.sessionsUsed tag (st.sessionsUsed tag + 1)
            responses := st.responses.cacheQuery (tag, nonce) outputs
            bad := bad
            cacheBad := st.cacheBad } : UnlinkBadState TagId Nonce Digest)
    return some transcript
  else
    return none


-- @@ L625-633 expanded
/-- Reader oracle for the `RF_bad` multiple-session world. It accepts when the queried digest
appears among the cached random-function outputs for some tag at the given nonce. -/
def unlinkBadReaderQueryImpl :
    QueryImpl (OracleSpec.ofFn (ι := (TagTranscript Nonce Digest)) (fun _ => ReaderReply))
      (StateT (UnlinkBadState TagId Nonce Digest) ProbComp) :=
  fun transcript => do
  let st ← get
  let accepted :=
    decide
      (∃ tag ∈ (Finset.univ : Finset TagId),
        transcript.auth ∈ ((st.responses (tag, transcript.nonce)).getD []))
  return ReaderReply.ofBool accepted


-- @@ L635-642 verbatim
/-- Oracle implementation for the `RF_bad` multiple-session world. -/
def unlinkBadQueryImpl :
    QueryImpl (UnlinkOracleSpec TagId Nonce Digest)
      (StateT (UnlinkBadState TagId Nonce Digest) ProbComp) :=
  unlinkBadTagQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
    (sessionsPerTag := sessionsPerTag)
    +
    unlinkBadReaderQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)


-- @@ L644-651 verbatim
/-- Bad-event experiment from the `RF_bad` multiple-session collision world. -/
def unlinkBadExp
    (adversary : UnlinkAdversary TagId Nonce Digest) : ProbComp Bool := do
  let (_, st) ← (simulateQ
    (unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag))
    adversary).run UnlinkBadState.init
  return st.bad


-- @@ L653-653 verbatim
end BadEvent


-- @@ L655-655 verbatim
end PRFTagReader
