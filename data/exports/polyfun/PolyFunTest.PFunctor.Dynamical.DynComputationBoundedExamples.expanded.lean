/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Dynamical.DynComputation.Bounded
import Mathlib.Tactic.NormNum


-- @@ L11-11 verbatim
/-! # Bounded returning-computation examples -/


-- @@ L13-13 verbatim
@[expose] public section


-- @@ L15-15 verbatim
open PFunctor


-- @@ L17-20 verbatim
namespace PFunctor.DynSystem.DynComputation

/- Lean 4.33 compares assigned metavariable types at implicit transparency;
the boundary examples below unfold these constants there. -/

-- @@ L21-21 verbatim
attribute [local implicit_reducible] PFunctor.y PFunctor.monomial FreeM.IsTotalRollBound


-- @@ L23-23 verbatim
/-! ## Boundary behavior and universes -/


-- @@ L25-26 verbatim
def emptyReturn : DynComputation (0 : PFunctor.{0, 0}) Nat Nat :=
  ofFn (· + 1)


-- @@ L28-29 verbatim
example : emptyReturn.run 0 4 = FreeM.pure (some 5) := by
  simp [emptyReturn]


-- @@ L31-31 verbatim
universe uA uB uα uβ uγ uState uState₂


-- @@ L33-35 verbatim
def boundedUniverseCanary {p : PFunctor.{uA, uB}} {α : Type uα} {β : Type uβ}
    (M : DynComputation.{uState} p α β) (k : ℕ) (state : M.State) : FreeM p (Option β) :=
  M.unroll k state


-- @@ L37-39 verbatim
def closedTrajectoryUniverseCanary {α : Type uα} {β : Type uβ}
    (M : DynComputation.{uState} y.{uA, uB} α β) (state : M.State) (k : ℕ) : M.State :=
  M.closedStutterIterate state k


-- @@ L41-47 verbatim
theorem boundedSeqUniverseCanary {p : PFunctor.{uA, uB}} {α : Type uα} {β : Type uβ} {γ : Type uγ}
    (M₁ : DynComputation.{uState} p α β) (M₂ : DynComputation.{uState₂} p β γ)
    (program₁ : α → FreeM p β) (program₂ : β → FreeM p γ) (k₁ k₂ : ℕ)
    (h₁ : M₁.ImplementsWithin program₁ k₁) (h₂ : M₂.ImplementsWithin program₂ k₂) :
    (M₁.seqComp M₂).ImplementsWithin
      (fun input => FreeM.bind (program₁ input) program₂) (k₁ + k₂) :=
  h₁.seqComp h₂


-- @@ L49-49 verbatim
abbrev branchP : PFunctor := Bool y^ Bool


-- @@ L51-53 verbatim
def branchProgram (_ : Unit) : FreeM branchP Nat :=
  FreeM.liftBind false fun answer : Bool =>
    pure (if answer = true then 11 else 10)


-- @@ L55-56 verbatim
def branchMachine : DynComputation branchP Unit Nat :=
  ofFreeM branchProgram


-- @@ L58-64 verbatim
theorem branchProgram_bound : (branchProgram ()).IsTotalRollBound 1 := by
  unfold branchP
  rw [show branchProgram () = FreeM.liftBind false (fun answer : Bool =>
    pure (if answer = true then 11 else 10)) from rfl,
    FreeM.liftBind_eq,
    FreeM.isTotalRollBound_lift_bind_iff]
  exact ⟨by omega, fun _ => by simp⟩


-- @@ L66-66 verbatim
example : branchMachine.run 0 () = FreeM.pure none := rfl


-- @@ L68-68 verbatim
example : branchMachine.run 1 () = FreeM.map some (branchProgram ()) := rfl


-- @@ L70-74 verbatim
example : branchMachine.ResolvesIn 1 (branchMachine.init ()) := by
  rw [resolvesIn_iff_isTotalRollBound_of_behavior_eq branchMachine 1 _
    (branchProgram ())]
  · exact branchProgram_bound
  · exact denote_ofFreeM branchProgram ()


-- @@ L76-78 verbatim
example : ¬branchMachine.ResolvesIn 0 (branchMachine.init ()) := by
  apply branchMachine.not_resolvesIn_query_zero _ false _
  rfl


-- @@ L80-83 verbatim
example : branchMachine.unroll 1 (branchMachine.init ()) =
    Resumption.truncate 1
      (branchMachine.toDynSystem.behavior (branchMachine.init ())) :=
  branchMachine.unroll_eq_truncate 1 _


-- @@ L85-89 verbatim
example : branchMachine.ImplementsWithin branchProgram 1 := by
  rw [implementsWithin_iff_implements_and_bound]
  refine ⟨implements_ofFreeM branchProgram, fun input => ?_⟩
  cases input
  exact branchProgram_bound


-- @@ L91-96 verbatim
example : branchMachine.ImplementsWithin branchProgram 4 :=
  (show branchMachine.ImplementsWithin branchProgram 1 by
    rw [implementsWithin_iff_implements_and_bound]
    refine ⟨implements_ofFreeM branchProgram, fun input => ?_⟩
    cases input
    exact branchProgram_bound).mono (by omega)


-- @@ L98-101 verbatim
example : ¬branchMachine.ImplementsWithin branchProgram 0 := by
  intro h
  have := h ()
  cases this


-- @@ L103-103 verbatim
def wrongBranchProgram (_ : Unit) : FreeM branchP Nat := pure 99


-- @@ L105-108 verbatim
example : ¬branchMachine.ImplementsWithin wrongBranchProgram 1 := by
  intro h
  have := h ()
  cases this


-- @@ L110-111 verbatim
/-! An empty direction type makes a query branch vacuously resolve after one
layer, while zero fuel still cuts it off. -/


-- @@ L113-113 verbatim
def emptyDirectionP : PFunctor := Unit y^ Empty


-- @@ L115-116 verbatim
def emptyDirectionTree : Resumption emptyDirectionP Nat :=
  Resumption.query () fun direction => Empty.elim direction


-- @@ L118-119 verbatim
def emptyDirectionMachine : DynComputation emptyDirectionP Unit Nat :=
  ofResumption fun _ => emptyDirectionTree


-- @@ L121-123 verbatim
example : ¬emptyDirectionMachine.ResolvesIn 0 (emptyDirectionMachine.init ()) := by
  apply emptyDirectionMachine.not_resolvesIn_query_zero _ () _
  rfl


-- @@ L125-127 verbatim
example : emptyDirectionMachine.ResolvesIn 1 (emptyDirectionMachine.init ()) := by
  rw [emptyDirectionMachine.resolvesIn_query_succ_iff 0 _ () _ rfl]
  exact fun direction => Empty.elim direction


-- @@ L129-129 verbatim
/-! ## Closed deterministic trajectories -/


-- @@ L131-134 verbatim
/-- One Collatz step. The small trajectory below is used only as an executable
closed-system canary; no global Collatz termination claim is made. -/
def collatzNext (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1


-- @@ L136-139 verbatim
/-- The return-or-query view of the Collatz producer. -/
def collatzView (n : ℕ) : ℕ ⊕ y.{0, 0}.Obj ℕ :=
  if n = 1 then Sum.inl n
  else Sum.inr ⟨PUnit.unit, fun _ => collatzNext n⟩


-- @@ L141-143 verbatim
/-- The polynomial coalgebra step corresponding to `collatzView`. -/
def collatzOut (n : ℕ) : (y.{0, 0} + C.{0, 0} ℕ).Obj ℕ :=
  Resumption.pack (collatzView n)


-- @@ L145-150 verbatim
/-- A closed deterministic Collatz producer that returns at `1` and otherwise
makes the unique `y` query before advancing. -/
def collatzMachine : DynComputation y.{0, 0} ℕ ℕ where
  State := ℕ
  toDynSystem := (fun n => (collatzOut n).1) ⇆ fun n => (collatzOut n).2
  init := id


-- @@ L152-152 verbatim
@[simp] theorem init_collatzMachine (n : ℕ) : collatzMachine.init n = n := rfl


-- @@ L154-157 verbatim
@[simp] theorem view_collatzMachine (n : ℕ) :
    collatzMachine.view n = collatzView n := by
  change Resumption.unpack (collatzOut n) = collatzView n
  exact Resumption.unpack_pack (collatzView n)


-- @@ L159-163 verbatim
@[simp] theorem closedStutterStep_collatzMachine (n : ℕ) :
    collatzMachine.closedStutterStep n =
      if n = 1 then n else collatzNext n := by
  -- Lean 4.33: simp stops at literal goals `1 = 1` here; close them with `rfl`.
  by_cases h : n = 1 <;> simp [closedStutterStep, collatzView, h] <;> rfl


-- @@ L165-167 verbatim
example : collatzMachine.view (collatzMachine.init 1) = Sum.inl 1 := by
  simp [collatzView]
  rfl


-- @@ L169-173 verbatim
example : collatzMachine.closedStutterStep (collatzMachine.init 1) =
    collatzMachine.init 1 := by
  -- Lean 4.33: simp stops at the literal goal `1 = 1`; close it with `rfl`.
  simp
  rfl


-- @@ L175-180 verbatim
example : collatzMachine.closedStutterIterate (collatzMachine.init 6) 8 =
    collatzMachine.init 1 := by
  -- Lean 4.33: `Function.iterate_succ_apply` no longer fires from `norm_num`'s
  -- default simp set here, and the final step needs `rfl`.
  norm_num [closedStutterIterate, Function.iterate_succ_apply, collatzNext]
  rfl


-- @@ L182-184 verbatim
theorem collatz_resolvesIn_eight :
    collatzMachine.ResolvesIn 8 (collatzMachine.init 6) := by
  norm_num [ResolvesIn, collatzView, collatzNext]


-- @@ L186-190 verbatim
example : collatzMachine.ResolvesIn 8 (collatzMachine.init 6) := by
  rw [collatzMachine.resolvesIn_iff_exists_le_closedStutterIterate_return]
  refine ⟨8, le_rfl, 1, ?_⟩
  norm_num [closedStutterIterate, collatzView, collatzNext]
  rfl


-- @@ L192-197 verbatim
example : ∃ j ≤ 8, ∃ value,
    collatzMachine.view
      (collatzMachine.closedStutterIterate (collatzMachine.init 6) j) =
        Sum.inl value :=
  (collatzMachine.resolvesIn_iff_exists_le_closedStutterIterate_return 8 _).mp
    collatz_resolvesIn_eight


-- @@ L199-200 verbatim
example : ¬collatzMachine.ResolvesIn 7 (collatzMachine.init 6) := by
  norm_num [ResolvesIn, collatzView, collatzNext]


-- @@ L202-206 verbatim
example : ∃ k, collatzMachine.ResolvesIn k (collatzMachine.init 6) := by
  rw [collatzMachine.exists_resolvesIn_iff_exists_closedStutterIterate_return]
  refine ⟨8, 1, ?_⟩
  norm_num [closedStutterIterate, collatzView, collatzNext]
  rfl


-- @@ L208-208 verbatim
/-! ## Bounded simulation -/


-- @@ L210-219 verbatim
def boolRealization : DynComputation branchP Unit Nat where
  State := Bool
  toDynSystem :=
    (fun
      | false => Sum.inl false
      | true => Sum.inr (10 : Nat)) ⇆
    fun
      | false => fun _ => true
      | true => PEmpty.elim
  init := fun _ => false


-- @@ L221-222 verbatim
def constantBranchProgram (_ : Unit) : FreeM branchP Nat :=
  FreeM.liftBind false fun _ => pure 10


-- @@ L224-230 verbatim
theorem constantBranchProgram_bound : (constantBranchProgram ()).IsTotalRollBound 1 := by
  unfold branchP
  rw [show constantBranchProgram () =
      FreeM.liftBind false (fun _ : Bool => pure 10) from rfl,
    FreeM.liftBind_eq,
    FreeM.isTotalRollBound_lift_bind_iff]
  exact ⟨by omega, fun _ => by simp⟩


-- @@ L232-234 verbatim
inductive BoolResidual : Bool → FreeM branchP Nat → Prop
  | start : BoolResidual false (constantBranchProgram ())
  | done : BoolResidual true (FreeM.pure 10)


-- @@ L236-245 verbatim
theorem boolSimulation : IsSimulation boolRealization.toDynSystem
    (ofFreeM constantBranchProgram).toDynSystem BoolResidual where
  expose_eq := by
    intro state residual related
    cases related <;> rfl
  update_rel := by
    intro state residual related direction
    cases related with
    | start => exact BoolResidual.done
    | done => exact PEmpty.elim direction


-- @@ L247-255 verbatim
example : boolRealization.ImplementsWithin constantBranchProgram 1 := by
  apply implementsWithin_of_isSimulation boolRealization constantBranchProgram
    BoolResidual boolSimulation
  · intro input
    cases input
    exact BoolResidual.start
  · intro input
    cases input
    exact constantBranchProgram_bound


-- @@ L257-257 verbatim
/-! ## Additive sequencing -/


-- @@ L259-260 verbatim
def firstProgram (_ : Unit) : FreeM branchP Bool :=
  FreeM.liftBind false fun answer : Bool => pure answer


-- @@ L262-265 verbatim
def secondProgram (first : Bool) : FreeM branchP Nat :=
  FreeM.liftBind first fun answer : Bool =>
    pure (if first = true then if answer = true then 11 else 12
      else if answer = true then 20 else 21)


-- @@ L267-267 verbatim
def firstMachine : DynComputation branchP Unit Bool := ofFreeM firstProgram


-- @@ L269-269 verbatim
def secondMachine : DynComputation branchP Bool Nat := ofFreeM secondProgram


-- @@ L271-277 verbatim
theorem firstProgram_bound : (firstProgram ()).IsTotalRollBound 1 := by
  unfold branchP
  rw [show firstProgram () =
      FreeM.liftBind false (fun answer : Bool => pure answer) from rfl,
    FreeM.liftBind_eq,
    FreeM.isTotalRollBound_lift_bind_iff]
  exact ⟨by omega, fun _ => by simp⟩


-- @@ L279-286 verbatim
theorem secondProgram_bound (first : Bool) : (secondProgram first).IsTotalRollBound 1 := by
  unfold branchP
  rw [show secondProgram first = FreeM.liftBind first (fun answer : Bool =>
      pure (if first = true then if answer = true then 11 else 12
        else if answer = true then 20 else 21)) from rfl,
    FreeM.liftBind_eq,
    FreeM.isTotalRollBound_lift_bind_iff]
  exact ⟨by omega, fun _ => by simp⟩


-- @@ L288-292 verbatim
theorem firstWithin : firstMachine.ImplementsWithin firstProgram 1 := by
  rw [implementsWithin_iff_implements_and_bound]
  refine ⟨implements_ofFreeM firstProgram, fun input => ?_⟩
  cases input
  exact firstProgram_bound


-- @@ L294-296 verbatim
theorem secondWithin : secondMachine.ImplementsWithin secondProgram 1 := by
  rw [implementsWithin_iff_implements_and_bound]
  exact ⟨implements_ofFreeM secondProgram, secondProgram_bound⟩


-- @@ L298-300 verbatim
example : (firstMachine.seqComp secondMachine).ImplementsWithin
    (fun input => FreeM.bind (firstProgram input) secondProgram) 2 :=
  firstWithin.seqComp secondWithin


-- @@ L302-304 verbatim
example : (firstMachine.seqComp secondMachine).ResolvesIn 2
    ((firstMachine.seqComp secondMachine).init ()) :=
  (firstWithin.resolvesIn ()).seqComp_init secondWithin.resolvesIn


-- @@ L306-326 verbatim
example : ¬(firstMachine.seqComp secondMachine).ResolvesIn 1
    ((firstMachine.seqComp secondMachine).init ()) := by
  rw [resolvesIn_iff_isTotalRollBound_of_behavior_eq
    (firstMachine.seqComp secondMachine) 1 _
      (FreeM.bind (firstProgram ()) secondProgram)]
  · unfold branchP
    rw [show FreeM.bind (firstProgram ()) secondProgram =
        FreeM.liftBind false (fun first : Bool => secondProgram first) from rfl,
      FreeM.liftBind_eq,
      FreeM.isTotalRollBound_lift_bind_iff]
    intro h
    have hfalse := h.2 false
    rw [show secondProgram false = FreeM.liftBind false (fun answer : Bool =>
        pure (if false = true then if answer = true then 11 else 12
          else if answer = true then 20 else 21)) from rfl,
      FreeM.liftBind_eq, FreeM.isTotalRollBound_lift_bind_iff] at hfalse
    simp at hfalse
  · change (firstMachine.seqComp secondMachine).denote () =
      FreeM.toResumption (FreeM.bind (firstProgram ()) secondProgram)
    exact (implements_ofFreeM firstProgram).seqComp
      (implements_ofFreeM secondProgram) ()


-- @@ L328-328 verbatim
def positionHandler : Handler Option branchP := fun position => some position


-- @@ L330-330 verbatim
def failingHandler : Handler Option branchP := fun _ => none


-- @@ L332-336 verbatim
example : (firstMachine.seqComp secondMachine).runWithInput positionHandler 2 () =
    some (some 21) := by
  rw [runWithInput_seqComp firstMachine secondMachine positionHandler 1 1 ()
    (firstWithin.resolvesIn ()) secondWithin.resolvesIn]
  rfl


-- @@ L338-338 verbatim
example : (firstMachine.seqComp secondMachine).runWithInput failingHandler 2 () = none := rfl


-- @@ L340-340 verbatim
def immediateBool : DynComputation branchP Unit Bool := ofFn fun _ => true


-- @@ L342-350 verbatim
example : (immediateBool.seqComp secondMachine).runWithInput positionHandler 1 () =
    some (some 11) := by
  have hfirst : immediateBool.ResolvesIn 0 (immediateBool.init ()) := by
    apply immediateBool.resolvesIn_return 0 _ true
    rfl
  rw [show 1 = 0 + 1 by omega,
    runWithInput_seqComp immediateBool secondMachine positionHandler 0 1 ()
      hfirst secondWithin.resolvesIn]
  rfl


-- @@ L352-352 verbatim
def immediateNat : DynComputation branchP Bool Nat := ofFn fun value => if value then 7 else 8


-- @@ L354-363 verbatim
example : (firstMachine.seqComp immediateNat).runWithInput positionHandler 1 () =
    some (some 8) := by
  have hsecond : ∀ value, immediateNat.ResolvesIn 0 (immediateNat.init value) := by
    intro value
    apply immediateNat.resolvesIn_return 0 _ (if value then 7 else 8)
    rfl
  rw [show 1 = 1 + 0 by omega,
    runWithInput_seqComp firstMachine immediateNat positionHandler 1 0 ()
      (firstWithin.resolvesIn ()) hsecond]
  rfl


-- @@ L365-365 verbatim
/-! ## Stateful handler branch order -/


-- @@ L367-368 verbatim
def answerOppositeState : Handler (StateT Bool Option) branchP :=
  fun _ state => some (!state, state)


-- @@ L370-371 verbatim
example : (firstMachine.runWith answerOppositeState 1 (firstMachine.init ())).run false =
    some (some true, false) := rfl


-- @@ L373-374 verbatim
def failingStateHandler : Handler (StateT Bool Option) branchP :=
  fun _ _ => none


-- @@ L376-377 verbatim
example : (immediateBool.runWith failingStateHandler 5 (immediateBool.init ())).run false =
    some (some true, false) := rfl


-- @@ L379-379 verbatim
end PFunctor.DynSystem.DynComputation
