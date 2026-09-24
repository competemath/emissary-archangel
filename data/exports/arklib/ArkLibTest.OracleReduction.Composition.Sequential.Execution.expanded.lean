/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Composition.Sequential.Append.Simulation


-- @@ L9-15 verbatim
/-!
# Sequential-composition regression cases

These compile checks exercise effectful output at an empty or message-opening seam and the
two distinct challenge inclusions when the component specifications coincide. Named results below
also assert their standard-only axiom closures.
-/


-- @@ L17-17 verbatim
open OracleComp OracleSpec ProtocolSpec


-- @@ L19-19 verbatim
namespace AppendExecutionRegression


-- @@ L21-22 verbatim
/-- Ambient oracle whose output queries remain effectful. -/
abbrev oracle : OracleSpec Unit := fun _ => Bool


-- @@ L24-26 verbatim
/-- An opening message followed by a genuine challenge. -/
abbrev messageThenChallenge : ProtocolSpec 2 :=
  ⟨fun i => if i.val = 0 then .P_to_V else .V_to_P, fun _ => Bool⟩


-- @@ L28-34 verbatim
/-- An empty prefix with an ambient oracle query in its output. -/
def effectfulLeft : Prover oracle Unit Unit Bool Unit !p[] where
  PrvState := fun _ => Unit
  input := fun _ => ()
  sendMessage := fun i => Fin.elim0 i.1
  receiveChallenge := fun i => Fin.elim0 i.1
  output := fun _ => do return (← query (spec := oracle) (), ())


-- @@ L36-45 verbatim
/-- A suffix that sends its input, then receives a challenge. -/
def mixedRight : Prover oracle Bool Unit Bool Unit messageThenChallenge where
  PrvState := fun _ => Bool
  input := Prod.fst
  sendMessage := fun _ st => pure (st, st)
  receiveChallenge := fun _ _ => pure id
  output := fun st => pure (st, ())

-- The right protocol has a challenge after its opening message. The seam result requires
-- only the direction of the opening round, and needs no purity instance for effectfulLeft.

-- @@ L46-46 verbatim
example : messageThenChallenge.dir ⟨1, by decide⟩ = .V_to_P := rfl


-- @@ L48-56 verbatim
/-- An opening message permits effectful output despite later challenges. -/
theorem message_opening_effectful : (effectfulLeft.append mixedRight).run () () = (do
    let ⟨tr₁, stmt₂, wit₂⟩ ←
      liftAppendLeft messageThenChallenge (effectfulLeft.run () ())
    let ⟨tr₂, stmt₃, wit₃⟩ ← liftAppendRight !p[] (mixedRight.run stmt₂ wit₂)
    return ⟨tr₁ ++ₜ tr₂, stmt₃, wit₃⟩) :=
  Prover.append_run_of_seam (fun _ => Or.inr rfl) () ()

-- With both protocols empty, both output steps may perform arbitrary oracle queries.

-- @@ L57-63 verbatim
/-- Both empty protocols permit arbitrary output effects. -/
theorem both_empty_effectful (P : Prover oracle Bool Unit Bool Unit !p[]) :
    (effectfulLeft.append P).run () () = (do
      let ⟨tr₁, stmt₂, wit₂⟩ ← liftAppendLeft !p[] (effectfulLeft.run () ())
      let ⟨tr₂, stmt₃, wit₃⟩ ← liftAppendRight !p[] (P.run stmt₂ wit₂)
      return ⟨tr₁ ++ₜ tr₂, stmt₃, wit₃⟩) :=
  Prover.append_run_of_seam (fun hn => (Nat.not_lt_zero _ hn).elim) () ()


-- @@ L65-65 verbatim
section CoincidentSpecifications


-- @@ L67-71 verbatim
variable {ι : Type} {oSpec : OracleSpec ι} {σ α : Type} {n : ℕ} {p : ProtocolSpec n}
  [∀ i, SampleableType (p.Challenge i)]

-- When both specifications coincide, typeclass inference alone cannot identify the intended
-- copy of a challenge. Both explicitly pinned inclusions must still simulate correctly.

-- @@ L72-78 verbatim
/-- Simulation respects the pinned inclusion even when both specifications coincide. -/
theorem coincident_left (impl : QueryImpl oSpec (StateT σ ProbComp))
    (oa : OracleComp (oSpec + [p.Challenge]ₒ) α) :
    simulateQ (impl.addLift (challengeQueryImpl (pSpec := p ++ₚ p)) :
      QueryImpl _ (StateT σ ProbComp)) (liftAppendLeft p oa) =
    simulateQ (impl.addLift (challengeQueryImpl (pSpec := p)) :
      QueryImpl _ (StateT σ ProbComp)) oa := simulateQ_liftAppendLeft impl oa


-- @@ L80-86 verbatim
/-- The coincident right inclusion also preserves all simulated state. -/
theorem coincident_right (impl : QueryImpl oSpec (StateT σ ProbComp))
    (oa : OracleComp (oSpec + [p.Challenge]ₒ) α) :
    simulateQ (impl.addLift (challengeQueryImpl (pSpec := p ++ₚ p)) :
      QueryImpl _ (StateT σ ProbComp)) (liftAppendRight p oa) =
    simulateQ (impl.addLift (challengeQueryImpl (pSpec := p)) :
      QueryImpl _ (StateT σ ProbComp)) oa := simulateQ_liftAppendRight impl oa


-- @@ L88-88 verbatim
end CoincidentSpecifications


-- @@ L90-90 verbatim
section RawCoincidentRoutes


-- @@ L92-93 verbatim
/-- A concrete challenge-bearing specification, repeated on both sides. -/
abbrev oneChallenge : ProtocolSpec 1 := ⟨fun _ => .V_to_P, fun _ => Bool⟩


-- @@ L95-99 verbatim
/-- Query the only challenge in the component specification. -/
def componentChallenge :
    OracleComp (oracle + [oneChallenge.Challenge]ₒ'challengeOracleInterface) Bool :=
  query (spec := oracle + [oneChallenge.Challenge]ₒ'challengeOracleInterface)
    (Sum.inr ⟨⟨⟨0, by decide⟩, rfl⟩, ()⟩)


-- @@ L101-105 verbatim
/-- Observe the raw index of the first challenge query, without sampling its answer. -/
def headChallengeIndex {n : ℕ} {p : ProtocolSpec n} {α : Type} :
    OracleComp (oracle + [p.Challenge]ₒ) α → Option ℕ
  | PFunctor.FreeM.liftBind (Sum.inr ⟨i, _⟩) _ => some i.1.val
  | _ => none


-- @@ L107-109 verbatim
/-- The left copy queries appended round zero, independent of any simulation equality. -/
theorem coincident_left_index :
    headChallengeIndex (liftAppendLeft oneChallenge componentChallenge) = some 0 := rfl


-- @@ L111-113 verbatim
/-- The right copy queries appended round one. -/
theorem coincident_right_index :
    headChallengeIndex (liftAppendRight oneChallenge componentChallenge) = some 1 := rfl


-- @@ L115-120 verbatim
/-- Coincident component types still have distinct raw challenge routes. -/
theorem coincident_routes_distinct :
    liftAppendLeft oneChallenge componentChallenge ≠
      liftAppendRight oneChallenge componentChallenge := by
  intro h
  exact Nat.zero_ne_one (Option.some.inj (congrArg headChallengeIndex h))


-- @@ L122-122 verbatim
end RawCoincidentRoutes


-- @@ L124-124 verbatim
section Boundaries


-- @@ L126-128 verbatim
variable {ι : Type} {oSpec : OracleSpec ι} {m n : ℕ}
  {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}


-- @@ L130-139 verbatim
/-- An empty suffix permits arbitrary output effects in an interactive prefix. -/
theorem empty_right_effectful
    (P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ !p[])
    (stmt : Stmt₁) (wit : Wit₁) :
    (P₁.append P₂).run stmt wit = (do
      let ⟨tr₁, stmt₂, wit₂⟩ ← liftAppendLeft !p[] (P₁.run stmt wit)
      let ⟨tr₂, stmt₃, wit₃⟩ ← liftAppendRight pSpec₁ (P₂.run stmt₂ wit₂)
      return ⟨tr₁ ++ₜ tr₂, stmt₃, wit₃⟩) :=
  Prover.append_run_of_seam (fun hn => (Nat.not_lt_zero _ hn).elim) stmt wit


-- @@ L141-150 verbatim
/-- Pure left output permits every interactive suffix, including challenge-opening protocols. -/
theorem pure_output_interactive
    (P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    [P₁.OutputIsPure] (stmt : Stmt₁) (wit : Wit₁) :
    (P₁.append P₂).run stmt wit = (do
      let ⟨tr₁, stmt₂, wit₂⟩ ← liftAppendLeft pSpec₂ (P₁.run stmt wit)
      let ⟨tr₂, stmt₃, wit₃⟩ ← liftAppendRight pSpec₁ (P₂.run stmt₂ wit₂)
      return ⟨tr₁ ++ₜ tr₂, stmt₃, wit₃⟩) :=
  Prover.append_run stmt wit


-- @@ L152-152 verbatim
end Boundaries


-- @@ L154-154 verbatim
end AppendExecutionRegression


-- @@ L156-160 verbatim
/--
info: 'AppendExecutionRegression.message_opening_effectful' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in

-- @@ L161-161 verbatim
#print axioms AppendExecutionRegression.message_opening_effectful


-- @@ L163-167 verbatim
/--
info: 'AppendExecutionRegression.both_empty_effectful' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in

-- @@ L168-168 verbatim
#print axioms AppendExecutionRegression.both_empty_effectful


-- @@ L170-174 verbatim
/--
info: 'AppendExecutionRegression.coincident_left' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in

-- @@ L175-175 verbatim
#print axioms AppendExecutionRegression.coincident_left


-- @@ L177-181 verbatim
/--
info: 'AppendExecutionRegression.coincident_right' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in

-- @@ L182-182 verbatim
#print axioms AppendExecutionRegression.coincident_right


-- @@ L184-188 verbatim
/--
info: 'AppendExecutionRegression.empty_right_effectful' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in

-- @@ L189-189 verbatim
#print axioms AppendExecutionRegression.empty_right_effectful


-- @@ L191-195 verbatim
/--
info: 'AppendExecutionRegression.pure_output_interactive' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in

-- @@ L196-196 verbatim
#print axioms AppendExecutionRegression.pure_output_interactive


-- @@ L198-202 verbatim
/--
info: 'Prover.append_run_of_seam' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in

-- @@ L203-203 verbatim
#print axioms Prover.append_run_of_seam


-- @@ L205-209 verbatim
/--
info: 'ProtocolSpec.simulateQ_liftAppendLeft' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in

-- @@ L210-210 verbatim
#print axioms ProtocolSpec.simulateQ_liftAppendLeft


-- @@ L212-216 verbatim
/--
info: 'ProtocolSpec.simulateQ_liftAppendRight' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in

-- @@ L217-217 verbatim
#print axioms ProtocolSpec.simulateQ_liftAppendRight


-- @@ L219-223 verbatim
/--
info: 'Prover.simulateQ_append_run_of_seam' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in

-- @@ L224-224 verbatim
#print axioms Prover.simulateQ_append_run_of_seam


-- @@ L226-230 verbatim
/--
info: 'Prover.simulateQ_append_run' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in

-- @@ L231-231 verbatim
#print axioms Prover.simulateQ_append_run


-- @@ L233-237 verbatim
/--
info: 'Verifier.StateFunction.append_transition_left' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in

-- @@ L238-238 verbatim
#print axioms Verifier.StateFunction.append_transition_left


-- @@ L240-244 verbatim
/--
info: 'Verifier.StateFunction.append_transition_right' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in

-- @@ L245-245 verbatim
#print axioms Verifier.StateFunction.append_transition_right


-- @@ L247-251 verbatim
/--
info: 'AppendExecutionRegression.coincident_left_index' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in

-- @@ L252-252 verbatim
#print axioms AppendExecutionRegression.coincident_left_index


-- @@ L254-258 verbatim
/--
info: 'AppendExecutionRegression.coincident_right_index' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in

-- @@ L259-259 verbatim
#print axioms AppendExecutionRegression.coincident_right_index


-- @@ L261-265 verbatim
/--
info: 'AppendExecutionRegression.coincident_routes_distinct' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in

-- @@ L266-266 verbatim
#print axioms AppendExecutionRegression.coincident_routes_distinct
