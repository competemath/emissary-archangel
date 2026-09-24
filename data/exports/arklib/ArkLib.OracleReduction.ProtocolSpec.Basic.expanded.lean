/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Fin.Tuple.Lemmas
public import ArkLib.OracleReduction.Prelude
public import ArkLib.OracleReduction.OracleInterface


-- @@ L12-17 verbatim
/-!
# Protocol Specifications for (Oracle) Reductions

This file defines the `ProtocolSpec` type, which is used to specify the protocol between the prover
and the verifier.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
universe u v


-- @@ L23-23 verbatim
open OracleComp OracleSpec


-- @@ L25-36 verbatim
/-- A protocol specification for an interactive protocol with `n` steps consists of:
- A vector of directions `dir` for each step, which is either `.P_to_V` (the prover sends a message
  to the verifier) or `.V_to_P` (the verifier sends a challenge to the prover).
- A vector of types `«Type»` for each step, which is the type of the message or challenge sent in
  that step. -/
@[ext]
structure ProtocolSpec (n : ℕ) where
  /-- The direction of each message in the protocol. -/
  dir : Fin n → Direction
  /-- The type of each message in the protocol. -/
  «Type» : Fin n → Type
deriving Inhabited


-- @@ L38-38 verbatim
variable {n : ℕ}


-- @@ L40-40 verbatim
namespace ProtocolSpec


-- @@ L42-42 verbatim
section Defs


-- @@ L44-46 verbatim
/-- The empty protocol specification, with no messages or challenges, written as `!p[]`. -/
@[reducible]
def empty : ProtocolSpec 0 := ⟨!v[], !v[]⟩


-- @@ L48-48 verbatim
@[inherit_doc] notation "!p[]" => empty


-- @@ L50-53 verbatim
/-- Subtype of `Fin n` for the indices corresponding to messages in a protocol specification -/
@[reducible, simp]
def MessageIdx (pSpec : ProtocolSpec n) :=
  {i : Fin n // pSpec.dir i = Direction.P_to_V}


-- @@ L55-58 verbatim
/-- Subtype of `Fin n` for the indices corresponding to challenges in a protocol specification -/
@[reducible, simp]
def ChallengeIdx (pSpec : ProtocolSpec n) :=
  {i : Fin n // pSpec.dir i = Direction.V_to_P}


-- @@ L60-61 verbatim
instance {pSpec : ProtocolSpec n} : CoeHead (MessageIdx pSpec) (Fin n) where
  coe := fun i => i.1

-- @@ L62-63 verbatim
instance {pSpec : ProtocolSpec n} : CoeHead (ChallengeIdx pSpec) (Fin n) where
  coe := fun i => i.1


-- @@ L65-69 verbatim
/-- The type of the `i`-th message in a protocol specification.

This does not distinguish between messages received in full or as an oracle. -/
@[reducible, inline, specialize, simp]
def Message (pSpec : ProtocolSpec n) (i : MessageIdx pSpec) := pSpec.«Type» i.val


-- @@ L71-73 verbatim
/-- Unbundled version of `Message`, which supplies the proof separately from the index. -/
@[reducible, inline, specialize, simp]
def Message' (pSpec : ProtocolSpec n) (i : Fin n) (_ : pSpec.dir i = .P_to_V) := pSpec.«Type» i


-- @@ L75-77 verbatim
/-- The type of the `i`-th challenge in a protocol specification -/
@[reducible, inline, specialize, simp]
def Challenge (pSpec : ProtocolSpec n) (i : ChallengeIdx pSpec) := pSpec.«Type» i.val


-- @@ L79-81 verbatim
/-- Unbundled version of `Challenge`, which supplies the proof separately from the index. -/
@[reducible, inline, specialize, simp]
def Challenge' (pSpec : ProtocolSpec n) (i : Fin n) (_ : pSpec.dir i = .V_to_P) := pSpec.«Type» i


-- @@ L83-85 verbatim
/-- The type of all messages in a protocol specification. Uncurried version of `Message`. -/
@[reducible, inline, specialize]
def Messages (pSpec : ProtocolSpec n) : Type := ∀ i, pSpec.Message i


-- @@ L87-90 verbatim
/-- Unbundled version of `Messages`, which supplies the proof separately from the index. -/
@[reducible, inline, specialize]
def Messages' (pSpec : ProtocolSpec n) : Type :=
  ∀ i, (hi : pSpec.dir i = .P_to_V) → pSpec.«Type» i


-- @@ L92-94 verbatim
/-- The type of all challenges in a protocol specification -/
@[reducible, inline, specialize]
def Challenges (pSpec : ProtocolSpec n) : Type := ∀ i, pSpec.Challenge i


-- @@ L96-99 verbatim
/-- Unbundled version of `Challenges`, which supplies the proof separately from the index. -/
@[reducible, inline, specialize]
def Challenges' (pSpec : ProtocolSpec n) : Type :=
  ∀ i, (hi : pSpec.dir i = .V_to_P) → pSpec.«Type» i


-- @@ L101-105 verbatim
/-- The (full)) transcript of an interactive protocol, which is a list of messages and challenges.

Note that this is definitionally equal to `Transcript (Fin.last n) pSpec`. -/
@[reducible, inline, specialize]
def FullTranscript (pSpec : ProtocolSpec n) := (i : Fin n) → pSpec.«Type» i


-- @@ L107-107 verbatim
section Restrict


-- @@ L109-109 verbatim
variable {n : ℕ}


-- @@ L111-114 verbatim
/-- Take the first `m ≤ n` rounds of a `ProtocolSpec n` -/
@[implicit_reducible]
def take (m : ℕ) (h : m ≤ n) (pSpec : ProtocolSpec n) : ProtocolSpec m :=
  {dir := Fin.take m h pSpec.dir, «Type» := Fin.take m h pSpec.«Type»}


-- @@ L116-118 verbatim
/-- Take the last `m ≤ n` rounds of a `ProtocolSpec n` -/
def rtake (m : ℕ) (h : m ≤ n) (pSpec : ProtocolSpec n) : ProtocolSpec m :=
  {dir := Fin.rtake m h pSpec.dir, «Type» := Fin.rtake m h pSpec.«Type»}


-- @@ L120-122 verbatim
/-- Drop the first `m ≤ n` rounds of a `ProtocolSpec n` -/
def drop (m : ℕ) (h : m ≤ n) (pSpec : ProtocolSpec n) : ProtocolSpec (n - m) :=
  {dir := Fin.drop m h pSpec.dir, «Type» := Fin.drop m h pSpec.«Type»}


-- @@ L124-126 verbatim
/-- Drop the last `m ≤ n` rounds of a `ProtocolSpec n` -/
def rdrop (m : ℕ) (h : m ≤ n) (pSpec : ProtocolSpec n) : ProtocolSpec (n - m) :=
  {dir := Fin.rdrop m h pSpec.dir, «Type» := Fin.rdrop m h pSpec.«Type»}


-- @@ L128-134 verbatim
/-- Extract the slice of the rounds of a `ProtocolSpec n` from `start` to `stop - 1`. -/
def extract (start stop : ℕ) (h1 : start ≤ stop) (h2 : stop ≤ n) (pSpec : ProtocolSpec n) :
    ProtocolSpec (stop - start) where
  dir := Fin.extract start stop h1 h2 pSpec.dir
  «Type» := Fin.extract start stop h1 h2 pSpec.«Type»

/- Instances for accessing slice notation -/


-- @@ L136-140 verbatim
instance : SliceLT (ProtocolSpec n) ℕ
    (fun _ stop => stop ≤ n)
    (fun _ stop _ => ProtocolSpec stop)
    where
  sliceLT := fun v stop h => take stop h v


-- @@ L142-146 verbatim
instance : SliceGE (ProtocolSpec n) ℕ
    (fun _ start => start ≤ n)
    (fun _ start _ => ProtocolSpec (n - start))
    where
  sliceGE := fun v start h => drop start h v


-- @@ L148-152 verbatim
instance : Slice (ProtocolSpec n) ℕ ℕ
    (fun _ start stop => start ≤ stop ∧ stop ≤ n)
    (fun _ start stop _ => ProtocolSpec (stop - start))
    where
  slice := fun v start stop h => extract start stop h.1 h.2 v


-- @@ L154-155 verbatim
variable {m start stop : ℕ} {h : m ≤ n} {h1 : start ≤ stop} {h2 : stop ≤ n}
  {pSpec : ProtocolSpec n}


-- @@ L157-157 verbatim
@[simp] lemma take_dir : pSpec⟦:m⟧.dir = pSpec.dir⟦:m⟧ := rfl

-- @@ L158-158 verbatim
@[simp] lemma take_Type : pSpec⟦:m⟧.«Type» = pSpec.«Type»⟦:m⟧ := rfl

-- @@ L159-159 verbatim
@[simp] lemma drop_dir : pSpec⟦m:⟧.dir = pSpec.dir⟦m:⟧ := rfl

-- @@ L160-160 verbatim
@[simp] lemma drop_Type : pSpec⟦m:⟧.«Type» = pSpec.«Type»⟦m:⟧ := rfl

-- @@ L161-161 verbatim
@[simp] lemma extract_dir : pSpec⟦start:stop⟧.dir = pSpec.dir⟦start:stop⟧ := rfl

-- @@ L162-162 verbatim
@[simp] lemma extract_Type : pSpec⟦start:stop⟧.«Type» = pSpec.«Type»⟦start:stop⟧ := rfl


-- @@ L164-164 verbatim
namespace FullTranscript


-- @@ L166-166 verbatim
variable {pSpec : ProtocolSpec n}


-- @@ L168-171 verbatim
/-- Take the first `m ≤ n` rounds of a (full) transcript for a protocol specification `pSpec` -/
abbrev take (m : ℕ) (h : m ≤ n)
    (transcript : FullTranscript pSpec) : FullTranscript (pSpec.take m h) :=
  Fin.take m h transcript


-- @@ L173-176 verbatim
/-- Take the last `m ≤ n` rounds of a (full) transcript for a protocol specification `pSpec` -/
abbrev rtake (m : ℕ) (h : m ≤ n)
    (transcript : FullTranscript pSpec) : FullTranscript (pSpec.rtake m h) :=
  Fin.rtake m h transcript


-- @@ L178-180 verbatim
abbrev drop (m : ℕ) (h : m ≤ n)
    (transcript : FullTranscript pSpec) : FullTranscript (pSpec.drop m h) :=
  Fin.drop m h transcript


-- @@ L182-184 verbatim
abbrev rdrop (m : ℕ) (h : m ≤ n)
    (transcript : FullTranscript pSpec) : FullTranscript (pSpec.rdrop m h) :=
  Fin.rdrop m h transcript


-- @@ L186-190 verbatim
abbrev extract (start stop : ℕ) (h1 : start ≤ stop) (h2 : stop ≤ n)
    (transcript : FullTranscript pSpec) : FullTranscript (pSpec.extract start stop h1 h2) :=
  Fin.extract start stop h1 h2 transcript

/- Instances for accessing slice notation -/


-- @@ L192-196 verbatim
instance : SliceLT (FullTranscript pSpec) ℕ
    (fun _ stop => stop ≤ n)
    (fun _ stop _ => FullTranscript (pSpec⟦:stop⟧))
    where
  sliceLT := fun v stop h => take stop h v


-- @@ L198-202 verbatim
instance : SliceGE (FullTranscript pSpec) ℕ
    (fun _ start => start ≤ n)
    (fun _ start _ => FullTranscript (pSpec⟦start:⟧))
    where
  sliceGE := fun v start h => drop start h v


-- @@ L204-208 verbatim
instance : Slice (FullTranscript pSpec) ℕ ℕ
    (fun _ start stop => start ≤ stop ∧ stop ≤ n)
    (fun _ start stop _ => FullTranscript (pSpec⟦start:stop⟧))
    where
  slice := fun v start stop h => extract start stop h.1 h.2 v


-- @@ L210-216 verbatim
variable {m start stop : ℕ} {h : m ≤ n} {h1 : start ≤ stop} {h2 : stop ≤ n}
  {pSpec : ProtocolSpec n} {transcript : FullTranscript pSpec}

lemma take_eq_take : transcript⟦:m⟧ = transcript.take m h := rfl
lemma rtake_eq_rtake : transcript⟦m:⟧ = transcript.drop m h := rfl
lemma extract_eq_extract : transcript⟦start:stop⟧ = transcript.extract start stop h1 h2 :=
  rfl


-- @@ L218-218 verbatim
end FullTranscript


-- @@ L220-220 verbatim
end Restrict


-- @@ L222-229 verbatim
/-- Subtype of `Fin k` for the indices corresponding to messages in a protocol specification up to
  round `k` -/
@[reducible, simp]
def MessageIdxUpTo (k : Fin (n + 1)) (pSpec : ProtocolSpec n) : Type :=
  (pSpec⟦:k.val⟧).MessageIdx

lemma MessageIdxUpTo.eq_MessageIdx {k : Fin (n + 1)} {pSpec : ProtocolSpec n} :
    pSpec.MessageIdxUpTo k = {i : Fin k // pSpec.dir (i.castLE (by omega)) = .P_to_V} := rfl


-- @@ L231-235 verbatim
/-- Subtype of `Fin k` for the indices corresponding to challenges in a protocol specification up to
  round `k` -/
@[reducible, simp]
def ChallengeIdxUpTo (k : Fin (n + 1)) (pSpec : ProtocolSpec n) : Type :=
  (pSpec⟦:k.val⟧).ChallengeIdx


-- @@ L237-240 verbatim
/-- The indexed family of messages from the prover up to round `k`. -/
@[reducible, inline, specialize]
def MessageUpTo (k : Fin (n + 1)) (pSpec : ProtocolSpec n) (i : pSpec.MessageIdxUpTo k) :=
  (pSpec⟦:k.val⟧).Message i


-- @@ L242-245 verbatim
/-- The indexed family of challenges from the verifier up to round `k`. -/
@[reducible, inline, specialize]
def ChallengeUpTo (k : Fin (n + 1)) (pSpec : ProtocolSpec n) (i : pSpec.ChallengeIdxUpTo k) :=
  (pSpec⟦:k.val⟧).Challenge i


-- @@ L247-250 verbatim
/-- The type of all messages from the prover up to round `k`. -/
@[reducible, inline, specialize]
def MessagesUpTo (k : Fin (n + 1)) (pSpec : ProtocolSpec n) : Type :=
  ∀ i, pSpec.MessageUpTo k i


-- @@ L252-255 verbatim
/-- The type of all challenges from the verifier up to round `k`. -/
@[reducible, inline, specialize]
def ChallengesUpTo (k : Fin (n + 1)) (pSpec : ProtocolSpec n) : Type :=
  ∀ i, (pSpec.take k k.is_le).Challenge i


-- @@ L257-263 verbatim
/-- A (partial) transcript of a protocol specification, indexed by some `k : Fin (n + 1)`, is a
list of messages from the protocol for all indices `i` less than `k`.

This is defined as the full transcript of the protocol specification up to round `k`. -/
@[reducible, inline, specialize]
def Transcript (k : Fin (n + 1)) (pSpec : ProtocolSpec n) : Type :=
  (pSpec⟦:k.val⟧).FullTranscript


-- @@ L265-269 verbatim
@[simp]
lemma Transcript.def_eq {k : Fin (n + 1)} {pSpec : ProtocolSpec n} :
    (pSpec.take k k.is_le).FullTranscript =
      ((i : Fin k) → pSpec.«Type» (Fin.castLE (by omega) i)) :=
  rfl


-- @@ L271-271 verbatim
end Defs


-- @@ L273-273 verbatim
section Instances


-- @@ L275-283 verbatim
/-- There is only one protocol specification with 0 messages (the empty one) -/
instance : Unique (ProtocolSpec 0) where
  default := empty
  uniq := fun ⟨_, _⟩ => by
    simp only [mk.injEq]
    constructor <;> (funext i; exact Fin.elim0 i)

-- Note these strange instance syntheses. This is necessary to avoid diamonds later on when
-- going to sequential composition.


-- @@ L285-287 verbatim
instance : ∀ i, VCVCompatible (Challenge !p[] i) :=
  fun ⟨i, h⟩ =>
    (Fin.elim0 i : (h' : !p[].dir i = .V_to_P) → VCVCompatible (!p[].Challenge ⟨i, h'⟩)) h

-- @@ L288-290 verbatim
instance : ∀ i, SampleableType (Challenge !p[] i) :=
  fun ⟨i, h⟩ =>
    (Fin.elim0 i : (h' : !p[].dir i = .V_to_P) → SampleableType (!p[].Challenge ⟨i, h'⟩)) h

-- @@ L291-293 verbatim
instance : ∀ i, OracleInterface (Message !p[] i) :=
  fun ⟨i, h⟩ =>
    (Fin.elim0 i : (h' : !p[].dir i = .P_to_V) → OracleInterface (!p[].Message ⟨i, h'⟩)) h


-- @@ L295-295 verbatim
instance : ∀ i, VCVCompatible ((default : ProtocolSpec 0).Challenge i) := fun ⟨i, _⟩ => Fin.elim0 i

-- @@ L296-296 verbatim
instance : ∀ i, SampleableType ((default : ProtocolSpec 0).Challenge i) := fun ⟨i, _⟩ => Fin.elim0 i

-- @@ L297-297 verbatim
instance : ∀ i, OracleInterface ((default : ProtocolSpec 0).Message i) := fun ⟨i, _⟩ => Fin.elim0 i


-- @@ L299-299 verbatim
variable {Msg Chal : Type}


-- @@ L301-302 verbatim
instance : IsEmpty (ChallengeIdx ⟨!v[.P_to_V], !v[Msg]⟩) :=
  ⟨fun ⟨i, h⟩ => by aesop⟩

-- @@ L303-305 verbatim
instance : Unique (MessageIdx ⟨!v[.P_to_V], !v[Msg]⟩) where
  default := ⟨0, by simp⟩
  uniq := fun i => by ext; simp

-- @@ L306-307 verbatim
instance [inst : OracleInterface Msg] : ∀ i, OracleInterface (Message ⟨!v[.P_to_V], !v[Msg]⟩ i)
  | ⟨0, _⟩ => inst

-- @@ L308-309 verbatim
instance : ∀ i, VCVCompatible (Challenge ⟨!v[.P_to_V], !v[Msg]⟩ i)
  | ⟨0, h⟩ => nomatch h

-- @@ L310-311 verbatim
instance : ∀ i, SampleableType (Challenge ⟨!v[.P_to_V], !v[Msg]⟩ i)
  | ⟨0, h⟩ => nomatch h


-- @@ L313-314 verbatim
instance : IsEmpty (MessageIdx ⟨!v[.V_to_P], !v[Chal]⟩) :=
  ⟨fun ⟨i, h⟩ => by aesop⟩

-- @@ L315-317 verbatim
instance : Unique (ChallengeIdx ⟨!v[.V_to_P], !v[Chal]⟩) where
  default := ⟨0, by simp⟩
  uniq := fun i => by ext; simp

-- @@ L318-319 verbatim
instance : ∀ i, OracleInterface (Message ⟨!v[.V_to_P], !v[Chal]⟩ i)
  | ⟨0, h⟩ => nomatch h

-- @@ L320-321 verbatim
instance [inst : VCVCompatible Chal] : ∀ i, VCVCompatible (Challenge ⟨!v[.V_to_P], !v[Chal]⟩ i)
  | ⟨0, _⟩ => inst

-- @@ L322-323 verbatim
instance [inst : SampleableType Chal] : ∀ i, SampleableType (Challenge ⟨!v[.V_to_P], !v[Chal]⟩ i)
  | ⟨0, _⟩ => inst


-- @@ L325-325 verbatim
variable {pSpec : ProtocolSpec n}


-- @@ L327-327 verbatim
instance : Fintype (pSpec.MessageIdx) := Subtype.fintype (fun i => pSpec.dir i = .P_to_V)

-- @@ L328-328 verbatim
instance : Fintype (pSpec.ChallengeIdx) := Subtype.fintype (fun i => pSpec.dir i = .V_to_P)

-- @@ L329-330 verbatim
instance {k : Fin (n + 1)} : Fintype (pSpec.MessageIdxUpTo k) :=
  inferInstanceAs (Fintype <| MessageIdx (pSpec.take k k.is_le))

-- @@ L331-332 verbatim
instance {k : Fin (n + 1)} : Fintype (pSpec.ChallengeIdxUpTo k) :=
  inferInstanceAs (Fintype <| ChallengeIdx (pSpec.take k k.is_le))


-- @@ L334-334 verbatim
end Instances


-- @@ L336-336 verbatim
variable {pSpec : ProtocolSpec n}


-- @@ L338-338 verbatim
namespace MessagesUpTo


-- @@ L340-340 verbatim
variable {k : Fin (n + 1)}


-- @@ L342-345 verbatim
/-- For a tuple of messages up to round `k`, take the messages up to round `j : Fin (k + 1)` -/
def take (j : Fin (k + 1)) (messages : MessagesUpTo k pSpec) :
    MessagesUpTo (j.castLE (by omega)) pSpec :=
  fun i => messages ⟨i.val.castLE (by simp; omega), i.property⟩


-- @@ L347-347 verbatim
end MessagesUpTo


-- @@ L349-349 verbatim
namespace Messages


-- @@ L351-353 verbatim
/-- Take the messages up to round `j : Fin (n + 1)` -/
def take (j : Fin (n + 1)) (messages : Messages pSpec) : MessagesUpTo j pSpec :=
  by exact (by exact messages : MessagesUpTo (Fin.last n) pSpec).take j


-- @@ L355-355 verbatim
end Messages


-- @@ L357-357 verbatim
namespace ChallengesUpTo


-- @@ L359-359 verbatim
variable {k : Fin (n + 1)}


-- @@ L361-364 verbatim
/-- For a tuple of challenges up to round `k`, take the challenges up to round `j : Fin (k + 1)` -/
def take (j : Fin (k + 1)) (challenges : ChallengesUpTo k pSpec) :
    ChallengesUpTo (j.castLE (by omega)) pSpec :=
  fun i => challenges ⟨i.val.castLE (by simp; omega), i.property⟩


-- @@ L366-366 verbatim
end ChallengesUpTo


-- @@ L368-368 verbatim
namespace Challenges


-- @@ L370-372 verbatim
/-- Take the challenges up to round `j : Fin (n + 1)` -/
def take (j : Fin (n + 1)) (challenges : Challenges pSpec) : ChallengesUpTo j pSpec :=
  by exact (by exact challenges : ChallengesUpTo (Fin.last n) pSpec).take j


-- @@ L374-374 verbatim
end Challenges


-- @@ L376-376 verbatim
namespace MessagesUpTo


-- @@ L378-382 verbatim
/-- There is only one transcript for the empty protocol,
  represented as `default : ProtocolSpec 0` -/
instance {k : Fin 1} : Unique (MessagesUpTo k (default : ProtocolSpec 0)) where
  default := fun i => ()
  uniq := by solve_by_elim


-- @@ L384-392 verbatim
/-- There is only one transcript for the empty protocol, represented as `![]` -/
instance {k : Fin 1} : Unique (MessagesUpTo k !p[]) where
  default := fun ⟨⟨i, h⟩, _⟩ => by
    have : k = 0 := Fin.fin_one_eq_zero k
    subst this; simp at h
  uniq := fun _ => by
    ext ⟨⟨i, h⟩, _⟩
    have : k = 0 := Fin.fin_one_eq_zero k
    subst this; simp at h


-- @@ L394-397 verbatim
/-- There is only one transcript for any protocol specification with cutoff index 0 -/
instance : Unique (MessagesUpTo 0 pSpec) where
  default := fun ⟨i, _⟩ => Fin.elim0 i
  uniq := fun T => by ext ⟨i, _⟩; exact Fin.elim0 i


-- @@ L399-405 verbatim
def concat' {k : Fin n}
    (messages : (i : Fin k) → (pSpec.dir (i.castLE (by omega)) = .P_to_V
      → pSpec.«Type» (i.castLE (by omega))))
    (msg : (h : pSpec.dir k = .P_to_V) → pSpec.Message ⟨k, h⟩) :
    (i : Fin (k + 1)) → (pSpec.dir (i.castLE (by omega)) = .P_to_V) →
      pSpec.«Type» (i.castLE (by omega)) :=
  Fin.dconcat messages msg


-- @@ L407-413 verbatim
/-- Concatenate the `k`-th message to the end of the tuple of messages up to round `k`, assuming
  round `k` is a message round. -/
def concat {k : Fin n} (messages : MessagesUpTo k.castSucc pSpec)
    (h : pSpec.dir k = .P_to_V) (msg : pSpec.Message ⟨k, h⟩) : MessagesUpTo k.succ pSpec :=
  fun ⟨i, h⟩ => (concat' (pSpec := pSpec) (fun i hi => messages ⟨i, hi⟩) (fun _ => msg)) i h
  -- fun i => if hi : i.1.1 < k then messages ⟨⟨i.1.1, hi⟩, i.property⟩ else
  --   (by simp [MessageUpTo, Fin.eq_last_of_not_lt hi]; exact msg)


-- @@ L415-427 verbatim
/-- Extend the tuple of messages up to round `k` to up to round `k + 1`, assuming round `k` is a
  challenge round (so no message from the prover is sent). -/
def extend {k : Fin n} (messages : MessagesUpTo k.castSucc pSpec)
    (h : pSpec.dir k = .V_to_P) : MessagesUpTo k.succ pSpec :=
  fun ⟨i, h⟩ => (concat' (pSpec := pSpec) (fun i hi => messages ⟨i, hi⟩) (fun h' => by aesop)) i h
  -- fun i => if hi : i.1.1 < k then messages ⟨⟨i.1.1, hi⟩, i.property⟩ else
  --   -- contradiction proof
  --   (by
  --     haveI hik : i.1 = Fin.last k := Fin.eq_last_of_not_lt hi
  --     haveI := i.property
  --     simp [hik] at this
  --     have : pSpec.dir k = .P_to_V := this
  --     aesop)


-- @@ L429-431 verbatim
instance [inst : ∀ i, DecidableEq (pSpec.Message i)] {k : Fin (n + 1)} :
    DecidableEq (MessagesUpTo k pSpec) :=
  @Fintype.decidablePiFintype _ _ (fun i => inst ⟨i.1.castLE (by omega), i.property⟩) _


-- @@ L433-433 verbatim
end MessagesUpTo


-- @@ L435-435 verbatim
namespace ChallengesUpTo


-- @@ L437-441 verbatim
/-- There is only one transcript for the empty protocol,
  represented as `default : ProtocolSpec 0` -/
instance {k : Fin 1} : Unique (ChallengesUpTo k (default : ProtocolSpec 0)) where
  default := fun i => ()
  uniq := by solve_by_elim


-- @@ L443-451 verbatim
/-- There is only one transcript for the empty protocol, represented as `![]` -/
instance {k : Fin 1} : Unique (ChallengesUpTo k !p[]) where
  default := fun ⟨⟨i, h⟩, _⟩ => by
    have : k = 0 := Fin.fin_one_eq_zero k
    subst this; simp at h
  uniq := fun _ => by
    ext ⟨⟨i, h⟩, _⟩
    have : k = 0 := Fin.fin_one_eq_zero k
    subst this; simp at h


-- @@ L453-456 verbatim
/-- There is only one transcript for any protocol specification with cutoff index 0 -/
instance : Unique (ChallengesUpTo 0 pSpec) where
  default := fun ⟨i, _⟩ => Fin.elim0 i
  uniq := fun T => by ext ⟨i, _⟩; exact Fin.elim0 i


-- @@ L458-464 verbatim
def concat' {k : Fin n}
    (challenges : (i : Fin k) → (pSpec.dir (i.castLE (by omega)) = .V_to_P
      → pSpec.«Type» (i.castLE (by omega))))
    (chal : (h : pSpec.dir k = .V_to_P) → pSpec.Challenge ⟨k, h⟩) :
    (i : Fin (k + 1)) → (pSpec.dir (i.castLE (by omega)) = .V_to_P) →
      pSpec.«Type» (i.castLE (by omega)) :=
  Fin.dconcat challenges chal


-- @@ L466-472 verbatim
/-- Concatenate the `k`-th challenge to the end of the tuple of challenges up to round `k`, assuming
  round `k` is a challenge round. -/
def concat {k : Fin n} (challenges : ChallengesUpTo k.castSucc pSpec)
    (h : pSpec.dir k = .V_to_P) (chal : pSpec.Challenge ⟨k, h⟩) : ChallengesUpTo k.succ pSpec :=
  fun ⟨i, h⟩ => (concat' (pSpec := pSpec) (fun i hi => challenges ⟨i, hi⟩) (fun _ => chal)) i h
  -- fun i => if hi : i.1.1 < k then challenges ⟨⟨i.1.1, hi⟩, i.property⟩ else
  --   (by simp [Fin.eq_last_of_not_lt hi]; exact chal)


-- @@ L474-484 verbatim
/-- Extend the tuple of challenges up to round `k` to up to round `k + 1`, assuming round `k` is a
  message round (so no challenge from the verifier is sent). -/
def extend {k : Fin n} (challenges : ChallengesUpTo k.castSucc pSpec)
    (h : pSpec.dir k = .P_to_V) : ChallengesUpTo k.succ pSpec :=
  fun ⟨i, h⟩ => (concat' (pSpec := pSpec) (fun i hi => challenges ⟨i, hi⟩) (fun h' => by aesop)) i h
  -- fun i => if hi : i.1.1 < k then challenges ⟨⟨i.1.1, hi⟩, i.property⟩ else
  --   -- contradiction proof
  --   (by
  --     haveI := Fin.eq_last_of_not_lt hi
  --     haveI := i.property
  --     simp_all [Fin.castLE])


-- @@ L486-486 verbatim
end ChallengesUpTo


-- @@ L488-488 verbatim
namespace Transcript


-- @@ L490-493 verbatim
/-- There is only one transcript for the empty protocol -/
instance {k : Fin 1} : Unique (Transcript k (default : ProtocolSpec 0)) where
  default := fun i => ()
  uniq := by solve_by_elim


-- @@ L495-503 verbatim
/-- There is only one transcript for the empty protocol, represented as `![]` -/
instance {k : Fin 1} : Unique (Transcript k !p[]) where
  default := fun ⟨i, h⟩ => by
    have : k = 0 := Fin.fin_one_eq_zero k
    subst this; simp at h
  uniq := fun _ => by
    ext ⟨i, h⟩
    have : k = 0 := Fin.fin_one_eq_zero k
    subst this; simp at h


-- @@ L505-516 verbatim
/-- There is only one transcript for any protocol with cutoff index 0 -/
instance : Unique (Transcript 0 pSpec) where
  default := fun i => Fin.elim0 i
  uniq := fun T => by ext i; exact Fin.elim0 i

-- Potential natural re-indexing of messages and challenges.
-- Not needed for now, but could be useful.

-- instance instFinEnumMessageIdx : FinEnum pSpec.MessageIdx :=
--   FinEnum.Subtype.finEnum fun x ↦ pSpec.dir x = Direction.P_to_V
-- instance instFinEnumChallengeIdx : FinEnum pSpec.ChallengeIdx :=
--   FinEnum.Subtype.finEnum fun x ↦ pSpec.dir x = Direction.V_to_P


-- @@ L518-523 verbatim
/-- Concatenate a message to the end of a partial transcript. This is definitionally equivalent to
    `Fin.snoc`. -/
@[inline]
abbrev concat {m : Fin n} (msg : pSpec.«Type» m) (T : Transcript m.castSucc pSpec) :
    Transcript m.succ pSpec :=
  Fin.snoc T msg


-- @@ L525-530 verbatim
/-- Appending a message preserves every earlier transcript entry. -/
@[simp]
lemma concat_castSucc {m : Fin n} (msg : pSpec.«Type» m) (T : Transcript m.castSucc pSpec)
    (i : Fin m) : T.concat msg i.castSucc = T i := by
  unfold concat
  exact @Fin.snoc_castSucc m.val (fun i => pSpec⟦:m.succ.val⟧.«Type» i) msg T i


-- @@ L532-537 verbatim
/-- The last entry of a transcript after appending a message is that message. -/
@[simp]
lemma concat_last {m : Fin n} (msg : pSpec.«Type» m) (T : Transcript m.castSucc pSpec) :
    T.concat msg (Fin.last m) = msg := by
  unfold concat
  exact @Fin.snoc_last m.val (fun i => pSpec⟦:m.succ.val⟧.«Type» i) msg T


-- @@ L539-543 verbatim
/-- The sole entry of a one-round transcript after appending its message. -/
@[simp]
lemma concat_zero {pSpec : ProtocolSpec 1} (msg : pSpec.«Type» (0 : Fin 1))
    (T : Transcript (Fin.castSucc (0 : Fin 1)) pSpec) : T.concat msg (0 : Fin 1) = msg := by
  exact concat_last msg T


-- @@ L545-549 verbatim
/-! `concat_castSucc` and `concat_last` above index the transcript by `Fin`, which forces the caller
to already hold the index in the right `Fin` type. Composition proofs instead carry their index
arithmetic in `ℕ` and discharge it with `omega`, so they need the same two computation rules stated
at a raw `ℕ` index with its bound supplied separately. Those forms conclude in `HEq`, since the two
sides then sit at indices that are only propositionally equal. -/


-- @@ L551-558 verbatim
/-- Below the last round, `Transcript.concat` agrees with the transcript it extends.
`ℕ`-indexed, `HEq`-valued form of `concat_castSucc`. -/
lemma concat_apply_lt {m : Fin n} (T : Transcript m.castSucc pSpec) (msg : pSpec.«Type» m)
    (i : ℕ) (hi : i < m.val) (hi' : i < (m.succ : Fin (n + 1)).val) :
    HEq (T.concat msg ⟨i, hi'⟩) (T ⟨i, hi⟩) := by
  unfold concat Fin.snoc
  rw [dif_pos hi]
  exact cast_heq _ _


-- @@ L560-570 verbatim
/-- At the last round, `Transcript.concat` returns the newly appended message.
`ℕ`-indexed, `HEq`-valued form of `concat_last`. -/
lemma concat_apply_last {m : Fin n} (T : Transcript m.castSucc pSpec) (msg : pSpec.«Type» m)
    (i : ℕ) (him : i = m.val) (hi' : i < (m.succ : Fin (n + 1)).val) :
    HEq (T.concat msg ⟨i, hi'⟩) msg := by
  subst him
  unfold concat Fin.snoc
  rw [dif_neg (Nat.lt_irrefl m.val)]
  exact cast_heq _ _

-- Define conversions to and from `Transcript` with `MessagesUpTo` and `ChallengesUpTo`


-- @@ L572-572 verbatim
variable {k : Fin (n + 1)}


-- @@ L574-576 verbatim
/-- Extract messages from a transcript up to round `k` -/
def toMessagesUpTo (transcript : Transcript k pSpec) : MessagesUpTo k pSpec :=
  fun ⟨i, _⟩ => transcript i


-- @@ L578-580 verbatim
/-- Extract challenges from a transcript up to round `k` -/
def toChallengesUpTo (transcript : Transcript k pSpec) : ChallengesUpTo k pSpec :=
  fun ⟨i, _⟩ => transcript i


-- @@ L582-584 verbatim
def toMessagesChallenges (transcript : Transcript k pSpec) :
    MessagesUpTo k pSpec × ChallengesUpTo k pSpec :=
  (transcript.toMessagesUpTo, transcript.toChallengesUpTo)


-- @@ L586-590 verbatim
def ofMessagesChallenges (messages : MessagesUpTo k pSpec)
    (challenges : ChallengesUpTo k pSpec) : Transcript k pSpec :=
  fun i => match h : pSpec.dir (i.castLE (by omega)) with
  | Direction.P_to_V => messages ⟨i.castLE (by omega), h⟩
  | Direction.V_to_P => challenges ⟨i.castLE (by omega), h⟩


-- @@ L592-613 verbatim
/-- An equivalence between transcripts up to round `k` and the tuple of messages and challenges up
  to round `k`. -/
@[simps!]
def equivMessagesChallenges :
    Transcript k pSpec ≃ (MessagesUpTo k pSpec × ChallengesUpTo k pSpec) where
  toFun := toMessagesChallenges
  invFun := ofMessagesChallenges.uncurry
  left_inv := fun T => by
    ext i
    simp [ofMessagesChallenges, toMessagesChallenges, toMessagesUpTo, toChallengesUpTo]
    split <;> simp
  right_inv := fun ⟨messages, challenges⟩ => by
    ext i
    · have : pSpec.dir (i.val.castLE (by omega)) = Direction.P_to_V := i.property
      simp [ofMessagesChallenges, toMessagesChallenges, toMessagesUpTo]
      split <;> aesop
    · have : pSpec.dir (i.val.castLE (by omega)) = Direction.V_to_P := i.property
      simp [ofMessagesChallenges, toMessagesChallenges, toChallengesUpTo]
      split <;> aesop

-- TODO: state theorem that `Transcript.concat` is equivalent to `MessagesUpTo.{concat/extend}` with
-- `ChallengesUpTo.{extend/concat}`, depending on the direction of the round


-- @@ L615-615 verbatim
end Transcript


-- @@ L617-617 verbatim
namespace FullTranscript


-- @@ L619-621 verbatim
@[reducible, inline, specialize]
def messages (transcript : FullTranscript pSpec) (i : MessageIdx pSpec) :=
  transcript i.val


-- @@ L623-625 verbatim
@[reducible, inline, specialize]
def challenges (transcript : FullTranscript pSpec) (i : ChallengeIdx pSpec) :=
  transcript i.val


-- @@ L627-628 verbatim
/-- There is only one full transcript (the empty one) for an empty protocol -/
instance : Unique (FullTranscript (default : ProtocolSpec 0)) := inferInstance


-- @@ L630-632 verbatim
/-- Convert a full transcript to the tuple of messages and challenges -/
def toMessagesChallenges (transcript : FullTranscript pSpec) : Messages pSpec × Challenges pSpec :=
  by exact Transcript.toMessagesChallenges (by exact transcript : Transcript (Fin.last n) pSpec)


-- @@ L634-640 verbatim
/-- Convert the tuple of messages and challenges to a full transcript -/
def ofMessagesChallenges (messages : Messages pSpec) (challenges : Challenges pSpec) :
    FullTranscript pSpec :=
  by exact
    (Transcript.ofMessagesChallenges
      (by exact messages : MessagesUpTo (Fin.last n) pSpec)
      (by exact challenges : ChallengesUpTo (Fin.last n) pSpec))


-- @@ L642-647 verbatim
/-- An equivalence between full transcripts and the tuple of messages and challenges. -/
@[simps!]
def equivMessagesChallenges : FullTranscript pSpec ≃ (Messages pSpec × Challenges pSpec) := by
  change Transcript (Fin.last n) pSpec ≃
    (MessagesUpTo (Fin.last n) pSpec × ChallengesUpTo (Fin.last n) pSpec)
  exact Transcript.equivMessagesChallenges


-- @@ L649-649 verbatim
end FullTranscript


-- @@ L651-656 verbatim
/-- The specification of whether each message in a protocol specification is available in full
    (`None`) or received as an oracle (`Some (instOracleInterface (pSpec.Message i))`).

    This is defined as a type class for notational convenience. -/
class OracleInterfaces (pSpec : ProtocolSpec n) where
  oracleInterfaces : ∀ i, Option (OracleInterface (pSpec.Message i))


-- @@ L658-658 verbatim
section OracleInterfaces


-- @@ L660-660 verbatim
variable (pSpec : ProtocolSpec n) [inst : OracleInterfaces pSpec]


-- @@ L662-664 verbatim
/-- Subtype of `pSpec.MessageIdx` for messages that are received as oracles -/
@[reducible, inline, specialize]
def OracleMessageIdx := {i : pSpec.MessageIdx // (inst.oracleInterfaces i).isSome }


-- @@ L666-668 verbatim
/-- The oracle interface instances for messages that are received as oracles -/
instance {i : OracleMessageIdx pSpec} : OracleInterface (pSpec.Message i) :=
  (inst.oracleInterfaces i).get i.2


-- @@ L670-672 verbatim
/-- Subtype of `pSpec.MessageIdx` for messages that are received in full -/
@[reducible, inline, specialize]
def PlainMessageIdx := {i : pSpec.MessageIdx // (inst.oracleInterfaces i).isNone }


-- @@ L674-676 verbatim
/-- The type of messages that are received in full -/
@[reducible, inline, specialize]
def PlainMessage (i : pSpec.PlainMessageIdx) := pSpec.Message i.1


-- @@ L678-680 verbatim
/-- The type of messages that are received as oracles -/
@[reducible, inline, specialize]
def OracleMessage (i : pSpec.OracleMessageIdx) := pSpec.Message i.1


-- @@ L682-683 verbatim
def PlainMessages (pSpec : ProtocolSpec n) [OracleInterfaces pSpec] : Type :=
  ∀ i, pSpec.PlainMessage i


-- @@ L685-692 verbatim
def OracleMessages (pSpec : ProtocolSpec n) [OracleInterfaces pSpec] : Type :=
  ∀ i, pSpec.OracleMessage i

-- TODO: re-define `OracleReduction` to depend on these oracle interfaces, since currently we
-- assume that _all_ messages are available as oracles in an oracle reduction

-- Alternatively, we can define a `HybridReduction` structure, where the oracle interface for each
-- message is optional, that can be specialized to `OracleReduction` and `Reduction`


-- @@ L694-694 verbatim
end OracleInterfaces


-- @@ L696-708 verbatim
/-- Turn each verifier's challenge into an oracle, where querying a unit type gives back the
    challenge.

  This is the default instance for the challenge oracle interface. It may be overridden by
  `challengeOracleInterface{SR/FS}` for state-restoration and/or Fiat-Shamir. -/
@[reducible, inline, specialize]
instance challengeOracleInterface {pSpec : ProtocolSpec n} :
    ∀ i, OracleInterface (pSpec.Challenge i) := fun i =>
  { Query := Unit
    toOC.spec := fun _ => pSpec.Challenge i
    toOC.impl := fun _ => do read }

-- dtumad: Longer term I think you want this, but need to change `[_]ₒ` stuff for that

-- @@ L709-714 verbatim
@[instance_reducible]
def challengeOracleInterface' {pSpec : ProtocolSpec n} :
    OracleInterface (∀ i, pSpec.Challenge i) where
  Query := pSpec.ChallengeIdx
  toOC.spec := pSpec.Challenge
  toOC.impl i := do return (← read) i


-- @@ L716-725 verbatim
/-- Query a verifier's challenge for a given challenge round `i`, given the default challenge
  oracle interface `challengeOracleInterface`.

  This is the default version for getting challenges, where we query the default
  `challengeOracleInterface`, which accepts trivial input. In contrast, `getChallenge{SR/FS}`
  requires an input statement and prior messages up to that round. -/
@[reducible, inline, specialize]
def getChallenge (pSpec : ProtocolSpec n) (i : pSpec.ChallengeIdx) :
    OracleComp ([pSpec.Challenge]ₒ'challengeOracleInterface) (pSpec.Challenge i) :=
  query (spec := [pSpec.Challenge]ₒ'challengeOracleInterface) ⟨i, ()⟩


-- @@ L727-734 verbatim
/-- Define the query implementation for the verifier's challenge in terms of `ProbComp`.

This is a randomness oracle: it simply calls the `selectElem` method inherited from the
  `SampleableType` instance on the challenge types.
-/
def challengeQueryImpl {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)] :
    QueryImpl ([pSpec.Challenge]ₒ'challengeOracleInterface) ProbComp :=
  fun q => $ᵗ (pSpec.Challenge q.1)


-- @@ L736-736 verbatim
section ChallengeReindex


-- @@ L738-755 verbatim
/-! ### Reindexing challenge oracles

A protocol's challenge oracles embed into another's whenever challenge *indices* embed in a way
that preserves the challenge *types*. That data — an index map `f` together with the transport
`∀ i, q.Challenge (f i) = p.Challenge i` — is all a `SubSpec` needs, so we build the
`SubSpec` / `LawfulSubSpec` / `DisjointSubSpec` package from it once here rather than case by case.

Scope: this is stated for the *default* `challengeOracleInterface`, whose `Query` is `Unit` at
every index — which is what lets `challengeReindexQuery` reuse the query payload across the
reindexing. It does not apply to `challengeOracleInterfaceSR` / `..FS`, whose query type is
index-dependent (`Statement × MessagesUpTo i`); those are `def`s rather than instances, so the
interface is fixed at each declaration below and cannot be silently swapped.

Clients are the composition operators, each of which supplies an index map and a transport lemma.
`++ₚ` supplies `ChallengeIdx.inl` / `ChallengeIdx.inr` with `challenge_append_inl` /
`challenge_append_inr`; `seqCompose` would supply `sigmaChallengeIdxToSeqCompose`, whose transport
follows from `seqCompose_challenge_eq` and `seqComposeChallengeEquiv.left_inv` (not instantiated
here, as nothing consumes it yet). -/


-- @@ L757-758 verbatim
variable {k l : ℕ} {p : ProtocolSpec k} {q : ProtocolSpec l}
  (f : p.ChallengeIdx → q.ChallengeIdx) (hf : ∀ i, q.Challenge (f i) = p.Challenge i)


-- @@ L760-762 verbatim
/-- Forward map on challenge queries induced by an index map: reindex, keep the (trivial) query. -/
@[reducible] def challengeReindexQuery (t : [p.Challenge]ₒ.Domain) : [q.Challenge]ₒ.Domain :=
  ⟨f t.1, t.2⟩


-- @@ L764-775 verbatim
/-- Backward map on challenge responses induced by an index map with matching challenge types:
transport the response along `hf`.

This is the intended transport, but note what does and does not force it. Neither `SubSpec` nor
`LawfulSubSpec` nor `DisjointSubSpec` pins it down: post-composing any fibrewise automorphism of
`p.Challenge t.1` yields a different `onResponse` with the *same* `onQuery` that is equally lawful
and equally disjoint. What pins this definition down is defeq evidence at the client sites — see
the `@[simp]` lemmas `liftM_challenge_append_inl` / `_inr` in `ProtocolSpec/SeqCompose.lean`, which
compute the lifted query and would break if the transport were changed. -/
@[reducible] def challengeReindexResponse (t : [p.Challenge]ₒ.Domain)
    (r : [q.Challenge]ₒ.Range (challengeReindexQuery f t)) : [p.Challenge]ₒ.Range t :=
  show p.Challenge t.1 from (hf t.1) ▸ (show q.Challenge (f t.1) from r)


-- @@ L777-779 verbatim
/-- `challengeReindexResponse` is exactly `cast` along the challenge-type transport. -/
theorem challengeReindexResponse_eq_cast (t : [p.Challenge]ₒ.Domain) :
    challengeReindexResponse f hf t = cast (hf t.1) := rfl


-- @@ L781-785 verbatim
/-- Transporting a challenge response along an equality of challenge types is a bijection.
This is what makes the induced inclusion *lawful*, i.e. uniform-challenge preserving. -/
theorem challengeReindexResponse_bijective (t : [p.Challenge]ₒ.Domain) :
    Function.Bijective (challengeReindexResponse f hf t) :=
  (Equiv.cast (hf t.1)).bijective


-- @@ L787-796 verbatim
/-- An embedding of challenge indices that preserves challenge types induces an inclusion of
challenge oracles.

`monadLift` is spelled out in lens form (rather than left to the class default) so that the lifted
query reduces during `simp` / `rw` matching; see the `OracleSpec.SubSpec` docstring. -/
@[reducible] def subSpecOfChallengeReindex : [p.Challenge]ₒ ⊂ₒ [q.Challenge]ₒ where
  monadLift qry := ⟨challengeReindexQuery f qry.input,
    qry.cont ∘ challengeReindexResponse f hf qry.input⟩
  onQuery := challengeReindexQuery f
  onResponse := challengeReindexResponse f hf


-- @@ L798-805 verbatim
/-- The induced inclusion is lawful: `onResponse` is bijective on every fibre, which is exactly
what VCV-io needs to preserve the uniform distribution on challenges under the lift
(`evalDist_liftComp`, `probEvent_liftComp`, `support_liftComp`). -/
theorem lawfulSubSpecOfChallengeReindex :
    letI := subSpecOfChallengeReindex f hf
    [p.Challenge]ₒ ˡ⊂ₒ [q.Challenge]ₒ := by
  let := subSpecOfChallengeReindex f hf
  exact ⟨challengeReindexResponse_bijective f hf⟩


-- @@ L807-818 verbatim
/-- Two reindexings into a common protocol have disjoint query images as soon as their index maps
do. Completes the package: given the index-level disjointness, no oracle-spec-level reasoning is
needed. -/
theorem disjointSubSpecOfChallengeReindex {k' : ℕ} {p' : ProtocolSpec k'}
    (f' : p'.ChallengeIdx → q.ChallengeIdx) (hf' : ∀ i, q.Challenge (f' i) = p'.Challenge i)
    (hdisj : ∀ i i', f i ≠ f' i') :
    letI := subSpecOfChallengeReindex f hf
    letI := subSpecOfChallengeReindex f' hf'
    OracleSpec.DisjointSubSpec [p.Challenge]ₒ [p'.Challenge]ₒ [q.Challenge]ₒ := by
  let := subSpecOfChallengeReindex f hf
  let := subSpecOfChallengeReindex f' hf'
  exact ⟨fun t t' h => hdisj t.1 t'.1 (congrArg Sigma.fst h)⟩


-- @@ L820-820 verbatim
end ChallengeReindex


-- @@ L822-836 verbatim
/-- The oracle interface for state-restoration and (basic) Fiat-Shamir.

This is the version where we hash the input statement and the entire transcript up to
the point of deriving a new challenge. To be precise:
- The domain of the oracle is `Statement × pSpec.MessagesUpTo i.1.castSucc`
- The range of the oracle is `pSpec.Challenge i`
- The oracle just returns the challenge -/
@[reducible, inline, specialize]
def challengeOracleInterfaceSR (StmtIn : Type) (pSpec : ProtocolSpec n) :
    ∀ i, OracleInterface (pSpec.Challenge i) := fun i =>
  { Query := StmtIn × pSpec.MessagesUpTo i.1.castSucc
    toOC.spec := fun _ => pSpec.Challenge i
    toOC.impl := fun _ => read }

alias challengeOracleInterfaceFS := challengeOracleInterfaceSR


-- @@ L838-856 verbatim
/-- The oracle interface for Fiat-Shamir.

This is the (inefficient) version where we hash the input statement and the entire transcript up to
the point of deriving a new challenge. To be precise:
- The domain of the oracle is `Statement × pSpec.MessagesUpTo i.1.castSucc`
- The range of the oracle is `pSpec.Challenge i`

Some variants of Fiat-Shamir takes in a salt each round. We assume that such salts are included in
the input statement (i.e. we can always transform a given reduction into one where every round has a
random salt). -/
@[inline, reducible]
def srChallengeOracle (Statement : Type) {n : ℕ} (pSpec : ProtocolSpec n) :
    OracleSpec
      ((i : pSpec.ChallengeIdx) × (challengeOracleInterfaceSR Statement pSpec i).Query) :=
  [pSpec.Challenge]ₒ'(challengeOracleInterfaceSR Statement pSpec)

alias fsChallengeOracle := srChallengeOracle

-- dtumad: If we keep these they should just move to VCV about `OracleContext`.

-- @@ L857-871 verbatim
/-- Decidable equality for the state-restoration / (slow) Fiat-Shamir oracle -/
instance {pSpec : ProtocolSpec n} {Statement : Type}
    [DecidableEq Statement]
    [∀ i, DecidableEq (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Challenge i)] :
    OracleSpec.DecidableEq (srChallengeOracle Statement pSpec) := by
  refine { decidableEqA := ?_, decidableEqB := fun q => ?_ }
  · dsimp only [srChallengeOracle, OracleInterface.toOracleSpec,
      challengeOracleInterfaceSR, OracleSpec.toPFunctor,
      OracleInterface.Query]
    infer_instance
  · dsimp only [srChallengeOracle, OracleInterface.toOracleSpec,
      challengeOracleInterfaceSR, OracleSpec.toPFunctor,
      OracleInterface.Response]
    infer_instance


-- @@ L873-878 verbatim
instance {pSpec : ProtocolSpec n} {Statement : Type} [∀ i, VCVCompatible (pSpec.Challenge i)] :
    OracleSpec.Fintype (srChallengeOracle Statement pSpec) := by
  refine { fintypeB := fun q => ?_ }
  dsimp only [srChallengeOracle, OracleInterface.toOracleSpec,
    challengeOracleInterfaceSR, OracleSpec.toPFunctor, OracleInterface.Response]
  infer_instance


-- @@ L880-885 verbatim
instance {pSpec : ProtocolSpec n} {Statement : Type} [∀ i, VCVCompatible (pSpec.Challenge i)] :
    OracleSpec.Fintype (fsChallengeOracle Statement pSpec) := by
  refine { fintypeB := fun q => ?_ }
  dsimp only [fsChallengeOracle, srChallengeOracle, OracleInterface.toOracleSpec,
    challengeOracleInterfaceSR, OracleSpec.toPFunctor, OracleInterface.Response]
  infer_instance


-- @@ L887-903 verbatim
/-- Define the query implementation for the state-restoration / (slow) Fiat-Shamir oracle (returns a
    challenge given messages up to that point) in terms of `ProbComp`.

  This is a randomness oracle: it simply calls the `selectElem` method inherited from the
  `SampleableType` instance on the challenge types. We may then augment this with `withCaching` to
  obtain a function-like implementation (caches and replays previous queries).

  For implementation with caching, we add `withCaching`.

  For implementation where the whole function is sampled ahead of time, and we answer with that
  function, see `srChallengeQueryImpl'`.
-/
@[reducible, inline, specialize, simp]
def srChallengeQueryImpl {Statement : Type} {pSpec : ProtocolSpec n}
    [∀ i, SampleableType (pSpec.Challenge i)] :
    QueryImpl (srChallengeOracle Statement pSpec) ProbComp :=
  fun q => $ᵗ (pSpec.Challenge q.1)


-- @@ L905-916 verbatim
/-- Alternate version of query implementation that takes in a cached function `f` and returns
  the result and the updated function.

  TODO: upstream this as a more general construction in VCVio -/
@[reducible, inline, specialize, simp]
def srChallengeQueryImpl' {Statement : Type} {pSpec : ProtocolSpec n}
    [∀ i, SampleableType (pSpec.Challenge i)] :
    QueryImpl (srChallengeOracle Statement pSpec)
      (StateT (QueryImpl (srChallengeOracle Statement pSpec) Id) ProbComp) :=
  fun | ⟨i, t⟩ => fun f => pure (f ⟨i, t⟩, f)

alias fsChallengeQueryImpl' := srChallengeQueryImpl'


-- @@ L918-918 verbatim
namespace MessagesUpTo


-- @@ L920-940 verbatim
/-- Auxiliary function for deriving the transcript up to round `k` from the (full) messages, via
  querying the state-restoration / Fiat-Shamir oracle for the challenges.

  This is used to define `deriveTranscriptFS`. -/
def deriveTranscriptSRAux {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type}
    (stmt : StmtIn) (k : Fin (n + 1)) (messages : pSpec.MessagesUpTo k)
    (j : Fin (k + 1)) :
    OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)
      (pSpec.Transcript (j.castLE (by omega))) := do
  Fin.induction (n := k)
    (pure (fun i => i.elim0))
    (fun i ih => do
      let prevTranscript ← ih
      match hDir : pSpec.dir (i.castLE (by omega)) with
      | .V_to_P =>
        let challenge : pSpec.Challenge ⟨i.castLE (by omega), hDir⟩ ←
          query (spec := fsChallengeOracle _ _) ⟨⟨i.castLE (by omega), hDir⟩,
            (stmt, messages.take i.castSucc)⟩
        return prevTranscript.concat challenge
      | .P_to_V => return prevTranscript.concat (messages ⟨i, hDir⟩))
    j


-- @@ L942-949 verbatim
/-- Derive the transcript up to round `k` from the (full) messages, via querying the
    state-restoration / Fiat-Shamir oracle for the challenges. -/
def deriveTranscriptSR {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type}
    (stmt : StmtIn) (k : Fin (n + 1)) (messages : pSpec.MessagesUpTo k) :
    OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) (pSpec.Transcript k) := do
  deriveTranscriptSRAux stmt k messages (Fin.last k)

alias deriveTranscriptFS := deriveTranscriptSR


-- @@ L951-951 verbatim
end MessagesUpTo


-- @@ L953-953 verbatim
namespace Messages


-- @@ L955-962 verbatim
/-- Derive the transcript up to round `k` from the (full) messages, via querying the
    state-restoration / Fiat-Shamir oracle for the challenges. -/
def deriveTranscriptSR {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type}
    (stmt : StmtIn) (messages : pSpec.Messages) :
    OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) pSpec.FullTranscript := do
  MessagesUpTo.deriveTranscriptSR stmt (Fin.last n) messages

alias deriveTranscriptFS := deriveTranscriptSR


-- @@ L964-964 verbatim
end Messages


-- @@ L966-975 verbatim
end ProtocolSpec

-- -- Notation for the type signature of an interactive protocol
-- notation "𝒫——⟦" term "⟧⟶𝒱" => (Direction.P_to_V, term)
-- notation "𝒫⟵⟦" term "⟧——𝒱" => (Direction.V_to_P, term)

-- -- Test notation
-- def pSpecNotationTest : ProtocolSpec 2 :=
--   ![ 𝒫——⟦ Polynomial (ZMod 101) ⟧⟶𝒱,
--      𝒫⟵⟦ ZMod 101 ⟧——𝒱]
