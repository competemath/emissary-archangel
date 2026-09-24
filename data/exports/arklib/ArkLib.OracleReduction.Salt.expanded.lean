/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.OracleReduction.Execution
public import ArkLib.OracleReduction.Cast


-- @@ L11-25 verbatim
/-!
  # Adding Salt to an (Oracle) Reduction

  This file defines the `addSalt` transformation, which adds a salt type to every prover's message
  in an (oracle) reduction.

  Salting is useful for the following reasons:
  - To add zero-knowledge to the prover in Fiat-Shamir and (interactive) BCS
  - To add dummy slots for "tagging" the extracted messages in the state-restoration knowledge
    soundness proof of BCS

  We will show (in another file) that round-by-round security for an (oracle) reduction implies
  state-restoration security for that same (oracle) reduction with any (finite, non-empty) salt type
  added.
-/


-- @@ L27-27 verbatim
@[expose] public section


-- @@ L29-29 verbatim
open OracleComp OracleSpec


-- @@ L31-31 verbatim
namespace ProtocolSpec


-- @@ L33-33 verbatim
variable {n : ℕ}


-- @@ L35-41 verbatim
/-- Add a salt type to every prover's message in a protocol specification -/
@[reducible]
def addSalt (pSpec : ProtocolSpec n) (Salt : pSpec.MessageIdx → Type) :
    ProtocolSpec n :=
  ⟨pSpec.dir, fun i => match hDir : pSpec.dir i with
    | .P_to_V => (pSpec.«Type» i) × Salt ⟨i, hDir⟩
    | .V_to_P => pSpec.«Type» i⟩


-- @@ L43-43 verbatim
variable {pSpec : ProtocolSpec n} {Salt : pSpec.MessageIdx → Type}


-- @@ L45-46 verbatim
@[simp]
lemma addSalt_dir : (pSpec.addSalt Salt).dir = pSpec.dir := rfl


-- @@ L48-64 verbatim
@[simp]
lemma addSalt_Type (i : Fin n) :
    (pSpec.addSalt Salt).«Type» i = match hDir : pSpec.dir i with
      | .P_to_V => (pSpec.«Type» i) × Salt ⟨i, hDir⟩
      | .V_to_P => pSpec.«Type» i := rfl

lemma addSalt_Message (i : pSpec.MessageIdx) :
    (pSpec.addSalt Salt).Message i = (pSpec.Message i × Salt i) := by
  obtain ⟨i, hDir⟩ := i
  simp only [Message, addSalt]
  split <;> simp_all

lemma addSalt_Challenge (i : pSpec.ChallengeIdx) :
    (pSpec.addSalt Salt).Challenge i = pSpec.Challenge i := by
  obtain ⟨i, hDir⟩ := i
  simp only [Challenge, addSalt]
  split <;> simp_all


-- @@ L66-75 verbatim
/-- Remove the salt from a (partial) transcript of a salted protocol -/
def Transcript.removeSalt {k : Fin (n + 1)} (transcript : (pSpec.addSalt Salt).Transcript k) :
    pSpec.Transcript k :=
-- TODO: would be nice not to need `by` block
  fun i => by
  letI data := transcript i
  dsimp [addSalt, SliceLT.sliceLT, take] at data ⊢
  split at data
  · exact data.1
  · exact data


-- @@ L77-90 verbatim
/-- Extract the salt from a (partial) transcript of a salted protocol -/
def Transcript.extractSalt {k : Fin (n + 1)} (transcript : (pSpec.addSalt Salt).Transcript k) :
    (i : pSpec.MessageIdxUpTo k) → Salt ⟨i.val.castLE (by omega), by
      have hi := i.property
      change (Fin.take k.val (by omega) pSpec.dir) i.val = Direction.P_to_V at hi
      exact hi⟩ :=
  fun i => by
    letI data := transcript i
    dsimp [addSalt, SliceLT.sliceLT, take, Fin.castLE] at data ⊢
    split at data
    · exact data.2
    · haveI := i.property;
      simp [SliceLT.sliceLT, take, Fin.castLE] at this
      simp_all


-- @@ L92-95 verbatim
/-- Remove the salt from a full transcript of a salted protocol -/
def FullTranscript.removeSalt (transcript : (pSpec.addSalt Salt).FullTranscript) :
    pSpec.FullTranscript :=
  Transcript.removeSalt (pSpec := pSpec) (k := Fin.last n) transcript


-- @@ L97-99 verbatim
def FullTranscript.extractSalt (transcript : (pSpec.addSalt Salt).FullTranscript) :
    (i : pSpec.MessageIdx) → Salt i :=
  Transcript.extractSalt (pSpec := pSpec) (k := Fin.last n) transcript


-- @@ L101-104 verbatim
/-- Remove the salt from the family of prover messages. -/
def Messages.removeSalt (messages : (pSpec.addSalt Salt).Messages) :
    pSpec.Messages :=
  fun i => ((addSalt_Message i) ▸ messages i).1


-- @@ L106-109 verbatim
/-- Transport the verifier challenges back to the unsalted protocol. -/
def Challenges.removeSalt (challenges : (pSpec.addSalt Salt).Challenges) :
    pSpec.Challenges :=
  fun i => cast (addSalt_Challenge i) (challenges i)


-- @@ L111-122 verbatim
/-- The oracle interface for each of the prover's messages in a salted protocol is defined to be
  the same as the oracle interface for the original message (ignoring the salt). -/
instance (priority := 10000) instAddSaltMessage
    [Oₘ : ∀ i, OracleInterface (pSpec.Message i)] :
    ∀ i, OracleInterface ((pSpec.addSalt Salt).Message i) :=
  fun i => {
    Query := (Oₘ i).Query
    toOC.spec := (Oₘ i).Response
    toOC.impl q := ReaderT.mk fun msg =>
      ((Oₘ i).toOC.impl q).run
        (((addSalt_Message (pSpec := pSpec) (Salt := Salt) i) ▸ msg).1)
  }


-- @@ L124-133 verbatim
@[simp]
lemma addSalt_answer [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
    (i : pSpec.MessageIdx) (msg : (pSpec.addSalt Salt).Message i)
    (q : (Oₘ i).Query) :
    (instAddSaltMessage (pSpec := pSpec) (Salt := Salt) i).answer msg q =
      (Oₘ i).answer ((addSalt_Message i ▸ msg).1) q := by
  obtain ⟨i, hDir⟩ := i
  rfl

--  (i : ChallengeIdx saltedPSpec) → SampleableType (Challenge saltedPSpec i)


-- @@ L135-140 verbatim
instance [inst : ∀ i, SampleableType (pSpec.Challenge i)] :
    ∀ i, SampleableType ((pSpec.addSalt Salt).Challenge i) :=
  fun i => by
    dsimp at i ⊢; split
    · haveI := i.property; simp_all
    · exact inst i


-- @@ L142-142 verbatim
end ProtocolSpec


-- @@ L144-144 verbatim
open ProtocolSpec


-- @@ L146-152 verbatim
variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
  {WitIn : Type}
  {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
  {WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
  (Salt : pSpec.MessageIdx → Type)


-- @@ L154-173 verbatim
/-- Transform a prover for a protocol specification `pSpec` into a prover for the salted protocol
  specification `pSpec.addSalt Salt`. Require additional computation of the salt for each prover's
  round. -/
def Prover.addSalt (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (saltComp : (i : pSpec.MessageIdx) → P.PrvState i.1.castSucc → OracleComp oSpec (Salt i)) :
  Prover oSpec StmtIn WitIn StmtOut WitOut (pSpec.addSalt Salt) where
  PrvState := P.PrvState
  input := P.input
  sendMessage := fun i st => by
    dsimp; split
    · exact (do
      let ⟨msg, newSt⟩ ← P.sendMessage i st
      let salt : Salt i ← saltComp i st
      return ⟨⟨msg, salt⟩, newSt⟩)
    · haveI := i.property; simp_all
  receiveChallenge := fun i st => by
    dsimp; split
    · haveI := i.property; simp_all
    · exact P.receiveChallenge i st
  output := P.output


-- @@ L175-181 verbatim
/-- Transform an oracle prover for a protocol specification `pSpec` into an oracle prover for the
  salted protocol specification `pSpec.addSalt Salt`. Require additional computation of the salt
  for each prover's round. -/
def OracleProver.addSalt (P : OracleProver oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec)
    (saltComp : (i : pSpec.MessageIdx) → P.PrvState i.1.castSucc → OracleComp oSpec (Salt i)) :
  OracleProver oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut (pSpec.addSalt Salt) :=
  Prover.addSalt Salt P saltComp


-- @@ L183-188 verbatim
/-- Transform a verifier for a protocol specification `pSpec` into a verifier for the salted
  protocol. The new verifier takes in the salted transcript, remove the salt, then run the
  original verifier. -/
def Verifier.addSalt (V : Verifier oSpec StmtIn StmtOut pSpec) :
    Verifier oSpec StmtIn StmtOut (pSpec.addSalt Salt) where
  verify := fun stmtIn transcript => V.verify stmtIn transcript.removeSalt


-- @@ L190-194 verbatim
def addSaltQueryImpl :
    QueryImpl (oSpec + ([OStmtIn]ₒ + [pSpec.Message]ₒ))
      (OracleComp (oSpec + ([OStmtIn]ₒ + [(pSpec.addSalt Salt).Message]ₒ))) :=
  fun q => liftM <| OracleSpec.query
    (show (oSpec + ([OStmtIn]ₒ + [(pSpec.addSalt Salt).Message]ₒ)).Domain from q)


-- @@ L196-223 verbatim
private theorem simulateAddSaltQueryImpl
    (oStmt : ∀ i, OStmtIn i) (messages : (pSpec.addSalt Salt).Messages)
    (q : (oSpec + ([OStmtIn]ₒ + [pSpec.Message]ₒ)).Domain) :
    simulateQ (OracleInterface.simOracle2 oSpec oStmt messages)
        (addSaltQueryImpl (OStmtIn := OStmtIn) (Salt := Salt) q) =
      OracleInterface.simOracle2 oSpec oStmt
        (Messages.removeSalt (pSpec := pSpec) (Salt := Salt) messages) q := by
  rcases q with q | q
  · simp only [addSaltQueryImpl, simulateQ_query]
    rfl
  · rcases q with q | q
    · rcases q with ⟨i, q⟩
      simp only [addSaltQueryImpl, simulateQ_query]
      rfl
    · rcases q with ⟨i, q⟩
      obtain ⟨i, hDir⟩ := i
      simp only [addSaltQueryImpl]
      simp only [OracleInterface.simOracle2, QueryImpl.addLift,
        QueryImpl.add_apply_inr, QueryImpl.liftTarget_apply]
      change id <$> (liftM (OracleInterface.simOracle0
          (pSpec.addSalt Salt).Message messages ⟨⟨i, hDir⟩, q⟩) :
            OracleComp _ _) =
        (liftM (OracleInterface.simOracle0 pSpec.Message
          (Messages.removeSalt (pSpec := pSpec) (Salt := Salt) messages)
          ⟨⟨i, hDir⟩, q⟩) : OracleComp _ _)
      unfold OracleInterface.simOracle0
      simp only [addSalt_answer, Messages.removeSalt]
      congr 1


-- @@ L225-235 verbatim
private theorem simulateAddSaltQueryImplComp
    (oStmt : ∀ i, OStmtIn i) (messages : (pSpec.addSalt Salt).Messages)
    {α : Type} (oa : OracleComp (oSpec + ([OStmtIn]ₒ + [pSpec.Message]ₒ)) α) :
    simulateQ (OracleInterface.simOracle2 oSpec oStmt messages)
        (simulateQ (addSaltQueryImpl (OStmtIn := OStmtIn) (Salt := Salt)) oa) =
      simulateQ (OracleInterface.simOracle2 oSpec oStmt
        (Messages.removeSalt (pSpec := pSpec) (Salt := Salt) messages)) oa := by
  rw [← QueryImpl.simulateQ_compose]
  apply congrArg (fun impl => simulateQ impl oa)
  apply QueryImpl.ext
  exact simulateAddSaltQueryImpl (Salt := Salt) oStmt messages


-- @@ L237-253 verbatim
def addSaltOutputSimulation
    (V : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) :
    OracleOutputSimulation oSpec OStmtIn OStmtOut (pSpec.addSalt Salt) where
  materializeOutput := fun challenges oStmt messages =>
    V.materializeOutput
      (Challenges.removeSalt (pSpec := pSpec) (Salt := Salt) challenges) oStmt
      (Messages.removeSalt (pSpec := pSpec) (Salt := Salt) messages)
  simulateOutputQuery := fun challenges q =>
    simulateQ (addSaltQueryImpl (OStmtIn := OStmtIn) (Salt := Salt))
      (V.simulateOutputQuery
        (Challenges.removeSalt (pSpec := pSpec) (Salt := Salt) challenges) q)
  simulateOutputQuery_eq := by
    intro challenges oStmt messages q
    rw [simulateAddSaltQueryImplComp]
    exact V.simulateOutputQuery_eq
      (Challenges.removeSalt (pSpec := pSpec) (Salt := Salt) challenges) oStmt
      (Messages.removeSalt (pSpec := pSpec) (Salt := Salt) messages) q


-- @@ L255-264 verbatim
/-- Transform an oracle verifier for a protocol specification `pSpec` into an oracle verifier for
  the salted protocol specification `pSpec.addSalt Salt`. The new oracle verifier is the same as
  the old one, modulo casting of oracle interfaces. -/
def OracleVerifier.addSalt (V : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) :
    OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut (pSpec.addSalt Salt) where
  verify := fun stmtIn challenges =>
    simulateQ (addSaltQueryImpl (OStmtIn := OStmtIn) (Salt := Salt))
      (V.verify stmtIn
        (Challenges.removeSalt (pSpec := pSpec) (Salt := Salt) challenges))
  outputOracle := .inr (addSaltOutputSimulation (Salt := Salt) V)


-- @@ L266-274 verbatim
/-- Transform a reduction for a protocol specification `pSpec` into a reduction for the salted
  protocol specification `pSpec.addSalt Salt`. Require additional computation of the salt for each
  prover's round. -/
def Reduction.addSalt (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (saltComp : (i : pSpec.MessageIdx) → R.prover.PrvState i.1.castSucc →
      OracleComp oSpec (Salt i)) :
    Reduction oSpec StmtIn WitIn StmtOut WitOut (pSpec.addSalt Salt) where
  prover := R.prover.addSalt Salt saltComp
  verifier := R.verifier.addSalt Salt


-- @@ L276-296 verbatim
/-- Transform an oracle reduction for a protocol specification `pSpec` into an oracle reduction
  for the salted protocol specification `pSpec.addSalt Salt`. Require additional computation of
  the salt for each prover's round. -/
def OracleReduction.addSalt
    (R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec)
    (saltComp : (i : pSpec.MessageIdx) → R.prover.PrvState i.1.castSucc →
      OracleComp oSpec (Salt i)) :
    OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut (pSpec.addSalt Salt) where
  prover := R.prover.addSalt Salt saltComp
  verifier := R.verifier.addSalt Salt

-- The virtual-output semantics of the transformed verifier are covered by `addSalt_toVerifier` and
-- the ToyProblem runtime regression. Whole-reduction execution, completeness, and security remain
-- separate obligations; in particular the comments below are not proved by the semantic bridge.
-- Theorems to prove
-- Execution returns the same transcript as the original reduction (modulo salt)
-- Completeness is preserved (for any salt computation)
-- (Knowledge) soundness should be preserved
-- HOWEVER, state-restoration (knowledge) soundness is _not_ preserved
-- There are counter-examples that we can formalize
-- (the verifier sends one random bit per round, and accepts iff it sends zero for every round)
