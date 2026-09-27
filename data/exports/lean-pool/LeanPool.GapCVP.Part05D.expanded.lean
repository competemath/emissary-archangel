/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

module

public import LeanPool.GapCVP.Part05C


-- @@ L11-11 verbatim
/-! # GapCVP proof, part 05, continuation 04 -/


-- @@ L13-13 verbatim
public section


-- @@ L15-15 verbatim
noncomputable section


-- @@ L17-17 verbatim
open StateTransition (EvalsToInTime)


-- @@ L19-19 verbatim
open scoped BigOperators


-- @@ L21-21 verbatim
namespace GapCVP


-- @@ L23-23 verbatim
open GapCVP.TraceGolf (oneStep rebound)


-- @@ L25-25 verbatim
namespace SourceCanonicalUnaryGridIndexTM


-- @@ L27-27 verbatim
open Turing GapCVP.BinaryEncoding GapCVP.SourceWholeOutputValidBranchRecordTM


-- @@ L29-54 verbatim
private def sourceGridIndex_prefixTrace
    (count : ℕ)
    (source counter scratch archive output : List Bool) :
    EvalsToInTime sourceCanonicalUnaryGridIndexMachine.step
      (sourceGridIndexConfiguration 0
        (List.replicate count true ++ false :: source)
        counter scratch archive output)
      (some (sourceGridIndexConfiguration 1
        source (List.replicate count true ++ counter)
        scratch archive output))
      (count + 1) := by
  induction count generalizing counter with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (sourceGridIndex_prefix_false source counter scratch archive output)
  | succ count ih =>
      have hfirst := oneStep _ _ (sourceGridIndex_prefix_true
          (List.replicate count true ++ false :: source)
          counter scratch archive output)
      have hrest := ih (true :: counter)
      have hfull := EvalsToInTime.trans sourceCanonicalUnaryGridIndexMachine.step
        1 (count + 1) _ _ _ hfirst hrest
      rw [GapCVP.CNFUnaryPairIndexTotalCert.unaryPair_replicate_append_true count counter] at hfull
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_comm,
          Nat.add_left_comm,
          Nat.reduceAdd] using hfull


-- @@ L56-77 verbatim
private def sourceGridIndex_archiveTrace
    (source counter scratch archive output : List Bool) :
    EvalsToInTime sourceCanonicalUnaryGridIndexMachine.step
      (sourceGridIndexConfiguration 1
        source counter scratch archive output)
      (some (sourceGridIndexConfiguration 2
        [] counter scratch (source.reverse ++ archive) output))
      (source.length + 1) := by
  induction source generalizing archive with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.reverse_nil, List.nil_append, List.length_nil,
          zero_add] using
          oneStep _ _ (sourceGridIndex_archive_finish counter scratch archive output)
  | cons bit remaining ih =>
      have hfirst := oneStep _ _ (sourceGridIndex_archive_step
          bit remaining counter scratch archive output)
      have hrest := ih (bit :: archive)
      have hfull := EvalsToInTime.trans sourceCanonicalUnaryGridIndexMachine.step
        1 (remaining.length + 1) _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.reverse_cons, List.append_assoc, List.cons_append,
          List.nil_append,
          List.length_cons, Nat.add_comm, Nat.add_left_comm, Nat.reduceAdd] using hfull


-- @@ L79-100 verbatim
private def sourceGridIndex_sourceRestoreTrace
    (archive counter scratch output : List Bool) :
    EvalsToInTime sourceCanonicalUnaryGridIndexMachine.step
      (sourceGridIndexConfiguration 2
        [] counter scratch archive output)
      (some (sourceGridIndexConfiguration 3
        [] counter scratch [] (archive.reverse ++ output)))
      (archive.length + 1) := by
  induction archive generalizing output with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.reverse_nil, List.nil_append, List.length_nil,
          zero_add] using
          oneStep _ _ (sourceGridIndex_source_restore_finish counter scratch output)
  | cons bit remaining ih =>
      have hfirst := oneStep _ _ (sourceGridIndex_source_restore_step
          bit counter scratch remaining output)
      have hrest := ih (bit :: output)
      have hfull := EvalsToInTime.trans sourceCanonicalUnaryGridIndexMachine.step
        1 (remaining.length + 1) _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.reverse_cons, List.append_assoc, List.cons_append,
          List.nil_append,
          List.length_cons, Nat.add_comm, Nat.add_left_comm, Nat.reduceAdd] using hfull


-- @@ L102-125 verbatim
private def sourceGridIndex_copyTrace
    (count : ℕ) (scratch output : List Bool) :
    EvalsToInTime sourceCanonicalUnaryGridIndexMachine.step
      (sourceGridIndexConfiguration 4
        [] (List.replicate count true) scratch [] output)
      (some (sourceGridIndexConfiguration 5
        [] [] (List.replicate count true ++ scratch) []
        (false :: (List.replicate count true ++ output))))
      (count + 1) := by
  induction count generalizing scratch output with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (sourceGridIndex_copy_finish scratch output)
  | succ count ih =>
      have hfirst := oneStep _ _ (sourceGridIndex_copy_step
          (List.replicate count true) scratch output)
      have hrest := ih (true :: scratch) (true :: output)
      have hfull := EvalsToInTime.trans sourceCanonicalUnaryGridIndexMachine.step
        1 (count + 1) _ _ _ hfirst hrest
      rw [GapCVP.CNFUnaryPairIndexTotalCert.unaryPair_replicate_append_true count scratch,
        GapCVP.CNFUnaryPairIndexTotalCert.unaryPair_replicate_append_true count output] at hfull
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_comm,
          Nat.add_left_comm,
          Nat.reduceAdd] using hfull


-- @@ L127-150 verbatim
private def sourceGridIndex_templateRestoreTrace
    (count : ℕ) (counter output : List Bool) :
    EvalsToInTime sourceCanonicalUnaryGridIndexMachine.step
      (sourceGridIndexConfiguration 5
        [] counter (List.replicate count true) [] output)
      (some (sourceGridIndexConfiguration 3
        [] (List.replicate count true ++ counter) [] []
        (List.replicate count true ++ output)))
      (count + 1) := by
  induction count generalizing counter output with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (sourceGridIndex_template_restore_finish counter output)
  | succ count ih =>
      have hfirst := oneStep _ _ (sourceGridIndex_template_restore_step
          counter (List.replicate count true) output)
      have hrest := ih (true :: counter) (true :: output)
      have hfull := EvalsToInTime.trans sourceCanonicalUnaryGridIndexMachine.step
        1 (count + 1) _ _ _ hfirst hrest
      rw [GapCVP.CNFUnaryPairIndexTotalCert.unaryPair_replicate_append_true count counter,
        GapCVP.CNFUnaryPairIndexTotalCert.unaryPair_replicate_append_true count output] at hfull
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_comm,
          Nat.add_left_comm,
          Nat.reduceAdd] using hfull


-- @@ L152-200 verbatim
private def sourceGridIndex_enumerationTrace
    (count : ℕ) (output : List Bool) :
    EvalsToInTime sourceCanonicalUnaryGridIndexMachine.step
      (sourceGridIndexConfiguration 3
        [] (List.replicate count true) [] [] output)
      (some (Turing.haltList
        sourceCanonicalUnaryGridIndexMachine
        (sourceCanonicalUnaryGridIndexDescriptors count ++ output)))
      (count * count + 2 * count + 1) := by
  induction count generalizing output with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero,
          sourceCanonicalUnaryGridIndexDescriptors,
          List.range_zero, List.flatMap_nil, List.nil_append, mul_zero, add_zero, zero_add] using
          oneStep _ _ (sourceGridIndex_outer_finish output)
  | succ count ih =>
      have houter := oneStep _ _ (sourceGridIndex_outer_step
          (List.replicate count true) output)
      have hcopy := sourceGridIndex_copyTrace count [] output
      simp only [List.append_nil] at hcopy
      have hrestore := sourceGridIndex_templateRestoreTrace
        count [] (false :: (List.replicate count true ++ output))
      simp only [List.append_nil] at hrestore
      have hfirst := EvalsToInTime.trans sourceCanonicalUnaryGridIndexMachine.step
        _ _ _ _ _ houter hcopy
      have hsecond := EvalsToInTime.trans sourceCanonicalUnaryGridIndexMachine.step
        _ _ _ _ _ hfirst hrestore
      have htail := ih
        (sourceCanonicalUnaryGridIndexDescriptor count ++ output)
      have hdescriptor :
          List.replicate count true ++
              false :: (List.replicate count true ++ output) =
            sourceCanonicalUnaryGridIndexDescriptor count ++ output := by
        simp only [sourceCanonicalUnaryGridIndexDescriptor, lengthPrefixedWord,
            List.length_replicate,
            List.append_assoc, List.cons_append]
      rw [hdescriptor] at hsecond
      have hfull := EvalsToInTime.trans sourceCanonicalUnaryGridIndexMachine.step
        _ _ _ _ _ hsecond htail
      rw [sourceCanonicalUnaryGridIndexDescriptors_succ]
      have hbudget :
          count * count + 2 * count + 1 +
              (count + 1 + (count + 1 + 1)) ≤
            (count + 1) * (count + 1) +
              2 * (count + 1) + 1 := by
        simp only [Nat.succ_mul, one_mul, Nat.mul_succ]
        omega
      have hbounded := rebound hfull hbudget
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.append_assoc] using hbounded


-- @@ L202-223 verbatim
private def sourceGridIndex_missingPrefixTrace
    (count : ℕ) (counter : List Bool) :
    EvalsToInTime sourceCanonicalUnaryGridIndexMachine.step
      (sourceGridIndexConfiguration 0
        (List.replicate count true) counter [] [] [])
      (some (sourceGridIndexConfiguration 6
        [] (List.replicate count true ++ counter) [] [] []))
      (count + 1) := by
  induction count generalizing counter with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (sourceGridIndex_prefix_missing counter [] [] [])
  | succ count ih =>
      have hfirst := oneStep _ _ (sourceGridIndex_prefix_true
          (List.replicate count true) counter [] [] [])
      have hrest := ih (true :: counter)
      have hfull := EvalsToInTime.trans sourceCanonicalUnaryGridIndexMachine.step
        1 (count + 1) _ _ _ hfirst hrest
      rw [GapCVP.CNFUnaryPairIndexTotalCert.unaryPair_replicate_append_true count counter] at hfull
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_comm,
          Nat.add_left_comm,
          Nat.reduceAdd] using hfull


-- @@ L225-243 verbatim
private def sourceGridIndex_failureTrace
    (count : ℕ) :
    EvalsToInTime sourceCanonicalUnaryGridIndexMachine.step
      (sourceGridIndexConfiguration 6
        [] (List.replicate count true) [] [] [])
      (some (Turing.haltList
        sourceCanonicalUnaryGridIndexMachine []))
      (count + 1) := by
  induction count with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, zero_add] using
          oneStep _ _ sourceGridIndex_failure_finish
  | succ count ih =>
      have hfirst := oneStep _ _ (sourceGridIndex_failure_step
          (List.replicate count true))
      have hfull := EvalsToInTime.trans sourceCanonicalUnaryGridIndexMachine.step
        1 (count + 1) _ _ _ hfirst ih
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, Nat.add_comm, Nat.add_left_comm,
          Nat.reduceAdd] using hfull


-- @@ L245-246 verbatim
private noncomputable def sourceCanonicalUnaryGridIndexTimePolynomial : Polynomial ℕ :=
  2 * Polynomial.X ^ 2 + 8 * Polynomial.X + 8


-- @@ L248-321 verbatim
private noncomputable def sourceCanonicalUnaryGridIndex_totalTrace
    (input : List Bool) :
    EvalsToInTime sourceCanonicalUnaryGridIndexMachine.step
      (Turing.initList sourceCanonicalUnaryGridIndexMachine input)
      (some (Turing.haltList
        sourceCanonicalUnaryGridIndexMachine
        (sourceCanonicalUnaryGridIndexOutput input)))
      (sourceCanonicalUnaryGridIndexTimePolynomial.eval input.length) := by
  cases hread : readUnaryPrefix input with
  | none =>
      have hshape := GapCVP.SourceInterpolationRowTM.readUnaryPrefix_none_eq_replicate
        input hread
      have hprefix := sourceGridIndex_missingPrefixTrace
        input.length []
      simp only [List.append_nil] at hprefix
      rw [← hshape, ← sourceCanonicalUnaryGridIndexMachine_init]
        at hprefix
      have hclean := sourceGridIndex_failureTrace input.length
      rw [← hshape] at hclean
      have hfull := EvalsToInTime.trans sourceCanonicalUnaryGridIndexMachine.step
        _ _ _ _ _ hprefix hclean
      have houtput : sourceCanonicalUnaryGridIndexOutput input = [] := by
        simp only [sourceCanonicalUnaryGridIndexOutput, hread]
      rw [houtput]
      exact rebound hfull (by
        simp only [sourceCanonicalUnaryGridIndexTimePolynomial, pow_two, Polynomial.eval_add,
            Polynomial.eval_mul,
            Polynomial.eval_ofNat, Polynomial.eval_X]
        omega)
  | some parsed =>
      obtain ⟨count, source⟩ := parsed
      have hshape := GapCVP.SourceInterpolationRowTM.readUnaryPrefix_some_decompose
        input count source hread
      have hprefix := sourceGridIndex_prefixTrace
        count source [] [] [] []
      simp only [List.append_nil] at hprefix
      rw [← hshape, ← sourceCanonicalUnaryGridIndexMachine_init]
        at hprefix
      have harchive := sourceGridIndex_archiveTrace
        source (List.replicate count true) [] [] []
      simp only [List.append_nil] at harchive
      have hrestore := sourceGridIndex_sourceRestoreTrace
        source.reverse (List.replicate count true) [] []
      simp only [List.reverse_reverse, List.append_nil,
        List.length_reverse] at hrestore
      have hemit := sourceGridIndex_enumerationTrace count source
      have hfirst := EvalsToInTime.trans sourceCanonicalUnaryGridIndexMachine.step
        _ _ _ _ _ hprefix harchive
      have hsecond := EvalsToInTime.trans sourceCanonicalUnaryGridIndexMachine.step
        _ _ _ _ _ hfirst hrestore
      have hfull := EvalsToInTime.trans sourceCanonicalUnaryGridIndexMachine.step
        _ _ _ _ _ hsecond hemit
      have houtput :
          sourceCanonicalUnaryGridIndexOutput input =
            sourceCanonicalUnaryGridIndexDescriptors count ++ source := by
        simp only [sourceCanonicalUnaryGridIndexOutput, hread]
      rw [houtput]
      exact rebound hfull (by
        have hlength : count ≤ input.length := by
          rw [hshape]
          simp only [List.length_append, List.length_replicate,
            List.length_cons]
          omega
        have hsquare : count * count ≤ input.length * input.length :=
          Nat.mul_le_mul hlength hlength
        have hsource : source.length ≤ input.length := by
          rw [hshape]
          simp only [List.length_append, List.length_replicate,
            List.length_cons]
          omega
        simp only [sourceCanonicalUnaryGridIndexTimePolynomial, pow_two, Polynomial.eval_add,
            Polynomial.eval_mul,
            Polynomial.eval_ofNat, Polynomial.eval_X, ge_iff_le]
        omega)


-- @@ L323-342 verbatim
/-- GapCVP reduction support. -/
noncomputable def sourceCanonicalUnaryGridIndexComputable :
    BitTM
      sourceCanonicalUnaryGridIndexOutput where
  tm := sourceCanonicalUnaryGridIndexMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := sourceCanonicalUnaryGridIndexTimePolynomial
  outputsFun input := {
    steps := (sourceCanonicalUnaryGridIndex_totalTrace input).steps
    evals_in_steps := by
      simpa only [Option.bind_eq_bind, FinTM2.step, Fin.isValue, Equiv.invFun_as_coe,
          Equiv.refl_symm,
          Equiv.coe_refl, bitEncoding, id_eq, List.map_id_fun, Option.map_some] using
          (sourceCanonicalUnaryGridIndex_totalTrace input).evals_in_steps
    steps_le_m := by
      have hsteps :=
        (sourceCanonicalUnaryGridIndex_totalTrace input).steps_le_m
      simpa only [FinTM2.step, Fin.isValue, bitEncoding, id_eq, ge_iff_le] using hsteps
  }


-- @@ L344-344 verbatim
end SourceCanonicalUnaryGridIndexTM


-- @@ L346-346 verbatim
namespace SourceOriginalSourcePreservingTM


-- @@ L348-348 verbatim
section


-- @@ L350-350 verbatim
open Turing


-- @@ L352-353 verbatim
private abbrev OriginalSourcePreservingStack (tm : Turing.FinTM2) :=
  tm.K ⊕ Fin 3


-- @@ L355-358 verbatim
private abbrev originalSourcePreservingAlphabet (tm : Turing.FinTM2) :
    OriginalSourcePreservingStack tm → Type
  | .inl stack => tm.Γ stack
  | .inr _ => Bool


-- @@ L360-361 verbatim
private abbrev OriginalSourcePreservingLabel (tm : Turing.FinTM2) :=
  tm.Λ ⊕ Fin 5


-- @@ L363-364 verbatim
private abbrev OriginalSourcePreservingState (tm : Turing.FinTM2) :=
  Option Bool × tm.σ


-- @@ L366-371 verbatim
private abbrev liftOriginalSourcePreservingStatement (tm : Turing.FinTM2) :=
  liftStatement (K := tm.K) (Γ := originalSourcePreservingAlphabet tm)
    Sum.inl (Sum.inl : tm.Λ → OriginalSourcePreservingLabel tm)
    (Prod.snd : Option Bool × tm.σ → tm.σ) (fun state value => (state.1, value))
    (.load (fun state => (none, state.2))
      (.goto (fun _ => .inr (2 : Fin 5))))


-- @@ L373-458 verbatim
private noncomputable def originalSourcePreservingMachine
    {f : List Bool → List Bool}
    (computer : BitTM f) : Turing.FinTM2 := by
  classical
  letI : DecidableEq computer.tm.K := computer.tm.kDecidableEq
  letI : Fintype computer.tm.K := computer.tm.kFin
  letI : Fintype computer.tm.Λ := computer.tm.ΛFin
  letI : Fintype computer.tm.σ := computer.tm.σFin
  letI : Fintype (computer.tm.Γ computer.tm.k₀) :=
    computer.tm.Γk₀Fin
  exact {
    K := OriginalSourcePreservingStack computer.tm
    k₀ := .inl computer.tm.k₀
    k₁ := .inl computer.tm.k₁
    Γ := originalSourcePreservingAlphabet computer.tm
    Λ := OriginalSourcePreservingLabel computer.tm
    main := .inr (0 : Fin 5)
    σ := OriginalSourcePreservingState computer.tm
    initialState := (none, computer.tm.initialState)
    m := fun
      | .inl phase =>
          liftOriginalSourcePreservingStatement
            computer.tm (computer.tm.m phase)
      | .inr phase =>
          if phase = (0 : Fin 5) then
            .pop (.inl computer.tm.k₀)
              (fun state symbol =>
                (symbol.map computer.inputAlphabet, state.2))
              (.branch (fun state => state.1.isSome)
                (.push (.inr (0 : Fin 3))
                  (fun state => state.1.getD false)
                  (.push (.inr (1 : Fin 3))
                    (fun state => state.1.getD false)
                    (.load (fun state => (none, state.2))
                      (.goto (fun _ => .inr (0 : Fin 5))))))
                (.load (fun state => (none, state.2))
                  (.goto (fun _ => .inr (1 : Fin 5)))))
          else if phase = (1 : Fin 5) then
            .pop (.inr (1 : Fin 3))
              (fun state symbol => (symbol, state.2))
              (.branch (fun state => state.1.isSome)
                (.push (.inl computer.tm.k₀)
                  (fun state =>
                    computer.inputAlphabet.invFun
                      (state.1.getD false))
                  (.load (fun state => (none, state.2))
                    (.goto (fun _ => .inr (1 : Fin 5)))))
                (.load (fun state => (none, state.2))
                  (.goto (fun _ => .inl computer.tm.main))))
          else if phase = (2 : Fin 5) then
            .pop (.inl computer.tm.k₁)
              (fun state symbol =>
                (symbol.map computer.outputAlphabet, state.2))
              (.branch (fun state => state.1.isSome)
                (.push (.inr (2 : Fin 3))
                  (fun state => state.1.getD false)
                  (.load (fun state => (none, state.2))
                    (.goto (fun _ => .inr (2 : Fin 5)))))
                (.load (fun state => (none, state.2))
                  (.goto (fun _ => .inr (3 : Fin 5)))))
          else if phase = (3 : Fin 5) then
            .pop (.inr (0 : Fin 3))
              (fun state symbol => (symbol, state.2))
              (.branch (fun state => state.1.isSome)
                (.push (.inl computer.tm.k₁)
                  (fun state =>
                    computer.outputAlphabet.invFun
                      (state.1.getD false))
                  (.load (fun state => (none, state.2))
                    (.goto (fun _ => .inr (3 : Fin 5)))))
                (.push (.inl computer.tm.k₁)
                  (fun _ => computer.outputAlphabet.invFun false)
                  (.load (fun state => (none, state.2))
                    (.goto (fun _ => .inr (4 : Fin 5))))))
          else
            .pop (.inr (2 : Fin 3))
              (fun state symbol => (symbol, state.2))
              (.branch (fun state => state.1.isSome)
                (.push (.inl computer.tm.k₁)
                  (fun state =>
                    computer.outputAlphabet.invFun
                      (state.1.getD false))
                  (.load (fun state => (none, state.2))
                    (.goto (fun _ => .inr (4 : Fin 5)))))
                (.load (fun state => (none, state.2)) .halt))
  }


-- @@ L460-469 verbatim
private def originalSourcePreservingStacks (tm : Turing.FinTM2)
    (source : (stack : tm.K) → List (tm.Γ stack))
    (backup scratch result : List Bool) :
    (stack : OriginalSourcePreservingStack tm) →
      List (originalSourcePreservingAlphabet tm stack)
  | .inl stack => source stack
  | .inr stack =>
      if stack = (0 : Fin 3) then backup
      else if stack = (1 : Fin 3) then scratch
      else result


-- @@ L471-479 verbatim
@[simp] private theorem originalSourcePreservingStacks_apply_worker
    (tm : Turing.FinTM2)
    (source : (stack : tm.K) → List (tm.Γ stack))
    (backup scratch result : List Bool)
    (stack : tm.K) :
    originalSourcePreservingStacks tm
        source backup scratch result (.inl stack) =
      source stack := by
  rfl


-- @@ L481-487 verbatim
@[simp] private theorem originalSourcePreservingStacks_apply_backup
    (tm : Turing.FinTM2)
    (source : (stack : tm.K) → List (tm.Γ stack))
    (backup scratch result : List Bool) :
    originalSourcePreservingStacks tm
        source backup scratch result (.inr (0 : Fin 3)) = backup := by
  simp only [Fin.isValue, originalSourcePreservingStacks, ↓reduceIte]


-- @@ L489-495 verbatim
@[simp] private theorem originalSourcePreservingStacks_apply_scratch
    (tm : Turing.FinTM2)
    (source : (stack : tm.K) → List (tm.Γ stack))
    (backup scratch result : List Bool) :
    originalSourcePreservingStacks tm
        source backup scratch result (.inr (1 : Fin 3)) = scratch := by
  simp only [Fin.isValue, originalSourcePreservingStacks, one_ne_zero, ↓reduceIte]


-- @@ L497-503 verbatim
@[simp] private theorem originalSourcePreservingStacks_apply_result
    (tm : Turing.FinTM2)
    (source : (stack : tm.K) → List (tm.Γ stack))
    (backup scratch result : List Bool) :
    originalSourcePreservingStacks tm
        source backup scratch result (.inr (2 : Fin 3)) = result := by
  simp only [Fin.isValue, originalSourcePreservingStacks, Fin.reduceEq, ↓reduceIte]


-- @@ L505-528 verbatim
private theorem sourceStacks_update_worker
    (tm : Turing.FinTM2)
    (source : (stack : tm.K) → List (tm.Γ stack))
    (backup scratch result : List Bool)
    (stack : tm.K) (value : List (tm.Γ stack)) :
    originalSourcePreservingStacks tm
        (Function.update source stack value)
        backup scratch result =
      Function.update
        (originalSourcePreservingStacks tm
          source backup scratch result)
        (.inl stack) value := by
  classical
  funext current
  cases current with
  | inl current =>
      by_cases hequal : current = stack
      · subst current
        simp only [originalSourcePreservingStacks, Function.update_self]
      · simp only [originalSourcePreservingStacks, Function.update, hequal, ↓reduceDIte,
          Sum.inl.injEq]
  | inr current =>
      simp only [originalSourcePreservingStacks, Fin.isValue, Function.update, reduceCtorEq,
          ↓reduceDIte]


-- @@ L530-548 verbatim
private theorem originalSourcePreservingStacks_update_backup
    (tm : Turing.FinTM2)
    (source : (stack : tm.K) → List (tm.Γ stack))
    (backup scratch result value : List Bool) :
    originalSourcePreservingStacks tm
        source value scratch result =
      Function.update
        (originalSourcePreservingStacks tm
          source backup scratch result)
        (.inr (0 : Fin 3)) value := by
  classical
  funext current
  cases current with
  | inl current =>
      simp only [originalSourcePreservingStacks, Function.update, Fin.isValue, reduceCtorEq,
          ↓reduceDIte]
  | inr current =>
      fin_cases current <;>
        simp [originalSourcePreservingStacks, Function.update]


-- @@ L550-568 verbatim
private theorem sourceStacks_update_scratch
    (tm : Turing.FinTM2)
    (source : (stack : tm.K) → List (tm.Γ stack))
    (backup scratch result value : List Bool) :
    originalSourcePreservingStacks tm
        source backup value result =
      Function.update
        (originalSourcePreservingStacks tm
          source backup scratch result)
        (.inr (1 : Fin 3)) value := by
  classical
  funext current
  cases current with
  | inl current =>
      simp only [originalSourcePreservingStacks, Function.update, Fin.isValue, reduceCtorEq,
          ↓reduceDIte]
  | inr current =>
      fin_cases current <;>
        simp [originalSourcePreservingStacks, Function.update]


-- @@ L570-588 verbatim
private theorem sourceStacks_update_result
    (tm : Turing.FinTM2)
    (source : (stack : tm.K) → List (tm.Γ stack))
    (backup scratch result value : List Bool) :
    originalSourcePreservingStacks tm
        source backup scratch value =
      Function.update
        (originalSourcePreservingStacks tm
          source backup scratch result)
        (.inr (2 : Fin 3)) value := by
  classical
  funext current
  cases current with
  | inl current =>
      simp only [originalSourcePreservingStacks, Function.update, Fin.isValue, reduceCtorEq,
          ↓reduceDIte]
  | inr current =>
      fin_cases current <;>
        simp [originalSourcePreservingStacks, Function.update]


-- @@ L590-601 verbatim
private noncomputable def sourcePhaseConfiguration
    {f : List Bool → List Bool}
    (computer : BitTM f)
    (phase : Fin 5)
    (source : (stack : computer.tm.K) →
      List (computer.tm.Γ stack))
    (backup scratch result : List Bool) :
    (originalSourcePreservingMachine computer).Cfg where
  l := some (.inr phase)
  var := (none, computer.tm.initialState)
  stk := originalSourcePreservingStacks computer.tm
    source backup scratch result


-- @@ L603-614 verbatim
private noncomputable def sourceWorkerConfiguration
    {f : List Bool → List Bool}
    (computer : BitTM f)
    (backup scratch result : List Bool)
    (configuration : computer.tm.Cfg) :
    (originalSourcePreservingMachine computer).Cfg where
  l := match configuration.l with
    | some phase => some (.inl phase)
    | none => some (.inr (2 : Fin 5))
  var := (none, configuration.var)
  stk := originalSourcePreservingStacks computer.tm
    configuration.stk backup scratch result


-- @@ L616-643 verbatim
private theorem liftOriginalSourcePreservingStatement_stepAux
    {f : List Bool → List Bool}
    (computer : BitTM f)
    (backup scratch result : List Bool)
    (statement : Turing.TM2.Stmt
      computer.tm.Γ computer.tm.Λ computer.tm.σ)
    (state : computer.tm.σ)
    (source : (stack : computer.tm.K) →
      List (computer.tm.Γ stack)) :
    Turing.TM2.stepAux
        (liftOriginalSourcePreservingStatement
          computer.tm statement)
        (none, state)
        (originalSourcePreservingStacks computer.tm
          source backup scratch result) =
      sourceWorkerConfiguration
        computer backup scratch result
        (Turing.TM2.stepAux statement state source) := by
  classical
  exact liftStatement_stepAux Sum.inl Sum.inl Prod.snd (fun state value => (state.1, value))
    (.load (fun state => (none, state.2)) (.goto (fun _ => .inr (2 : Fin 5))))
    (fun state => (none, state))
    (fun source => originalSourcePreservingStacks computer.tm source backup scratch result)
    (sourceWorkerConfiguration computer backup scratch result)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun source k value =>
      sourceStacks_update_worker computer.tm source backup scratch result k value)
    (fun _ _ _ => rfl) (fun _ _ => rfl) statement state source


-- @@ L645-672 verbatim
private theorem originalSourcePreservingWorkerConfiguration_step
    {f : List Bool → List Bool}
    (computer : BitTM f)
    (backup scratch result : List Bool)
    (configuration next : computer.tm.Cfg)
    (hstep : computer.tm.step configuration = some next) :
    (originalSourcePreservingMachine computer).step
        (sourceWorkerConfiguration
          computer backup scratch result configuration) =
      some (sourceWorkerConfiguration
        computer backup scratch result next) := by
  rcases configuration with ⟨phase, state, source⟩
  cases phase with
  | none =>
      simp only [FinTM2.step, TM2.step, reduceCtorEq] at hstep
  | some phase =>
      change some (Turing.TM2.stepAux
        (computer.tm.m phase) state source) = some next at hstep
      have hnext := Option.some.inj hstep
      subst next
      change some (Turing.TM2.stepAux
        (liftOriginalSourcePreservingStatement
          computer.tm (computer.tm.m phase))
        (none, state)
        (originalSourcePreservingStacks computer.tm
          source backup scratch result)) = _
      rw [liftOriginalSourcePreservingStatement_stepAux]
      rfl


-- @@ L674-694 verbatim
private noncomputable def originalSourcePreservingWorker_evalsToInTime
    {f : List Bool → List Bool}
    (computer : BitTM f)
    (backup scratch result : List Bool)
    {source target : computer.tm.Cfg}
    {budget : ℕ}
    (trace : EvalsToInTime
      computer.tm.step source (some target) budget) :
    EvalsToInTime (originalSourcePreservingMachine computer).step
      (sourceWorkerConfiguration
        computer backup scratch result source)
      (some (sourceWorkerConfiguration
        computer backup scratch result target)) budget :=
  GapCVP.TMComposition.evalsToInTimeMapOfStep
    computer.tm.step
    (originalSourcePreservingMachine computer).step
    (fun state => sourceWorkerConfiguration
      computer backup scratch result state)
    (originalSourcePreservingWorkerConfiguration_step
      computer backup scratch result)
    trace


-- @@ L696-699 verbatim
/-- Append the original input after the computed output, separated by a false bit. -/
@[expose] def originalSourcePreservingOutput
    (f : List Bool → List Bool) (input : List Bool) : List Bool :=
  f input ++ false :: input


-- @@ L701-706 verbatim
private def sourceInputSymbols
    {f : List Bool → List Bool}
    (computer : BitTM f)
    (input : List Bool) :
    List (computer.tm.Γ computer.tm.k₀) :=
  List.map computer.inputAlphabet.invFun input


-- @@ L708-713 verbatim
private def sourceOutputSymbols
    {f : List Bool → List Bool}
    (computer : BitTM f)
    (output : List Bool) :
    List (computer.tm.Γ computer.tm.k₁) :=
  List.map computer.outputAlphabet.invFun output


-- @@ L715-723 verbatim
private def originalSourceCopyConfiguration
    {f : List Bool → List Bool}
    (computer : BitTM f)
    (phase : Fin 5) (input backup scratch result : List Bool) :
    (originalSourcePreservingMachine computer).Cfg :=
  sourcePhaseConfiguration computer phase
    (Turing.initList computer.tm
      (sourceInputSymbols computer input)).stk
    backup scratch result


-- @@ L725-733 verbatim
private def originalSourceOutputConfiguration
    {f : List Bool → List Bool}
    (computer : BitTM f)
    (phase : Fin 5) (output backup scratch result : List Bool) :
    (originalSourcePreservingMachine computer).Cfg :=
  sourcePhaseConfiguration computer phase
    (Turing.haltList computer.tm
      (sourceOutputSymbols computer output)).stk
    backup scratch result


-- @@ L735-758 verbatim
private theorem originalSourcePreservingMachine_init
    {f : List Bool → List Bool}
    (computer : BitTM f)
    (input : List Bool) :
    Turing.initList (originalSourcePreservingMachine computer)
        (sourceInputSymbols computer input) =
      originalSourceCopyConfiguration
        computer 0 input [] [] [] := by
  classical
  simp only [originalSourcePreservingMachine, Fin.isValue, Equiv.invFun_as_coe, initList,
      sourceInputSymbols,
      eq_mpr_eq_cast, originalSourceCopyConfiguration, sourcePhaseConfiguration]
  congr 1
  funext stack
  cases stack with
  | inl stack =>
      by_cases hequal : stack = computer.tm.k₀
      · subst stack
        simp only [↓reduceDIte, cast_eq, originalSourcePreservingStacks]
        rfl
      · simp only [Sum.inl.injEq, hequal, ↓reduceDIte, originalSourcePreservingStacks]
  | inr stack =>
      fin_cases stack <;>
        simp [originalSourcePreservingStacks]


-- @@ L760-771 verbatim
@[simp] private theorem originalSourcePreserving_initialStacks_update
    (tm : Turing.FinTM2)
    (input value : List (tm.Γ tm.k₀)) :
    Function.update
        (Turing.initList tm input).stk tm.k₀ value =
      (Turing.initList tm value).stk := by
  classical
  funext stack
  by_cases hequal : stack = tm.k₀
  · subst stack
    simp only [initList, eq_mpr_eq_cast, Function.update_self, ↓reduceDIte, cast_eq]
  · simp only [Function.update, hequal, ↓reduceDIte, initList, eq_mpr_eq_cast]


-- @@ L773-784 verbatim
@[simp] private theorem originalSourcePreserving_haltStacks_update
    (tm : Turing.FinTM2)
    (output value : List (tm.Γ tm.k₁)) :
    Function.update
        (Turing.haltList tm output).stk tm.k₁ value =
      (Turing.haltList tm value).stk := by
  classical
  funext stack
  by_cases hequal : stack = tm.k₁
  · subst stack
    simp only [haltList, eq_mpr_eq_cast, Function.update_self, ↓reduceDIte, cast_eq]
  · simp only [Function.update, hequal, ↓reduceDIte, haltList, eq_mpr_eq_cast]


-- @@ L786-799 verbatim
@[simp] private theorem originalSourcePreserving_embedded_update_worker
    (tm : Turing.FinTM2)
    (source : (stack : tm.K) → List (tm.Γ stack))
    (backup scratch result : List Bool)
    (stack : tm.K) (value : List (tm.Γ stack)) :
    Function.update
        (originalSourcePreservingStacks tm
          source backup scratch result)
        (.inl stack) value =
      originalSourcePreservingStacks tm
        (Function.update source stack value)
        backup scratch result :=
  (sourceStacks_update_worker
    tm source backup scratch result stack value).symm


-- @@ L801-812 verbatim
@[simp] private theorem originalSourcePreserving_embedded_update_backup
    (tm : Turing.FinTM2)
    (source : (stack : tm.K) → List (tm.Γ stack))
    (backup scratch result value : List Bool) :
    Function.update
        (originalSourcePreservingStacks tm
          source backup scratch result)
        (.inr (0 : Fin 3)) value =
      originalSourcePreservingStacks tm
        source value scratch result :=
  (originalSourcePreservingStacks_update_backup
    tm source backup scratch result value).symm


-- @@ L814-825 verbatim
@[simp] private theorem originalSourcePreserving_embedded_update_scratch
    (tm : Turing.FinTM2)
    (source : (stack : tm.K) → List (tm.Γ stack))
    (backup scratch result value : List Bool) :
    Function.update
        (originalSourcePreservingStacks tm
          source backup scratch result)
        (.inr (1 : Fin 3)) value =
      originalSourcePreservingStacks tm
        source backup value result :=
  (sourceStacks_update_scratch
    tm source backup scratch result value).symm


-- @@ L827-838 verbatim
@[simp] private theorem originalSourcePreserving_embedded_update_result
    (tm : Turing.FinTM2)
    (source : (stack : tm.K) → List (tm.Γ stack))
    (backup scratch result value : List Bool) :
    Function.update
        (originalSourcePreservingStacks tm
          source backup scratch result)
        (.inr (2 : Fin 3)) value =
      originalSourcePreservingStacks tm
        source backup scratch value :=
  (sourceStacks_update_result
    tm source backup scratch result value).symm


-- @@ L840-862 verbatim
private theorem originalSourcePreserving_embedded_haltStacks
    {f : List Bool → List Bool}
    (computer : BitTM f)
    (output : List (computer.tm.Γ computer.tm.k₁)) :
    originalSourcePreservingStacks computer.tm
        (Turing.haltList computer.tm output).stk [] [] [] =
      (Turing.haltList
        (originalSourcePreservingMachine computer) output).stk := by
  classical
  funext stack
  cases stack with
  | inl stack =>
      by_cases hequal : stack = computer.tm.k₁
      · subst stack
        simp only [originalSourcePreservingStacks, haltList, eq_mpr_eq_cast, ↓reduceDIte, cast_eq,
            originalSourcePreservingMachine, Fin.isValue, Equiv.invFun_as_coe]
        rfl
      · simp only [originalSourcePreservingStacks, haltList, eq_mpr_eq_cast, hequal, ↓reduceDIte,
            originalSourcePreservingMachine, Fin.isValue, Equiv.invFun_as_coe, Sum.inl.injEq]
  | inr stack =>
      fin_cases stack <;>
        simp [originalSourcePreservingStacks,
          originalSourcePreservingMachine, Turing.haltList]


-- @@ L864-913 verbatim
/-- Executes the `originalSourcePreservationStepTac` machine-step simplifier. -/
macro "originalSourcePreservationStepTac" : tactic =>
  `(tactic|
    (first
      | rfl
      | (simp +instances [originalSourcePreservingMachine,
          originalSourceCopyConfiguration,
          originalSourceOutputConfiguration,
          sourcePhaseConfiguration,
          sourceInputSymbols,
          sourceOutputSymbols,
          Turing.FinTM2.step, Turing.TM2.step,
          Turing.TM2.stepAux] <;>
          first
          | rfl
          | (congr 2
             first
             | exact originalSourcePreserving_embedded_haltStacks _ _
             | rw! (castMode := .all)
                 [← sourceStacks_update_worker,
                 ← originalSourcePreservingStacks_update_backup,
                 ← sourceStacks_update_scratch,
                 originalSourcePreserving_initialStacks_update]
             | rw! (castMode := .all)
                 [← sourceStacks_update_worker,
                 originalSourcePreserving_initialStacks_update]
             | rw! (castMode := .all)
                 [← sourceStacks_update_scratch,
                 ← sourceStacks_update_worker,
                 originalSourcePreserving_initialStacks_update]
             | rw! (castMode := .all)
                 [← sourceStacks_update_scratch]
             | rw! (castMode := .all)
                 [← sourceStacks_update_worker,
                 ← sourceStacks_update_result,
                 originalSourcePreserving_haltStacks_update]
             | rw! (castMode := .all)
                 [← sourceStacks_update_worker,
                 originalSourcePreserving_haltStacks_update]
             | rw! (castMode := .all)
                 [← originalSourcePreservingStacks_update_backup,
                 ← sourceStacks_update_worker,
                 originalSourcePreserving_haltStacks_update]
             | rw! (castMode := .all)
                 [← sourceStacks_update_result,
                 ← sourceStacks_update_worker,
                 originalSourcePreserving_haltStacks_update]
             | rw! (castMode := .all)
                 [← sourceStacks_update_result,
                 originalSourcePreserving_embedded_haltStacks]))))


-- @@ L915-927 expanded
private theorem originalSourcePreserving_copy_step {f : List Bool → List Bool} (computer : BitTM f)
    (bit : Bool) (input backup scratch result : List Bool) :
    (originalSourcePreservingMachine computer).step
        (originalSourceCopyConfiguration computer 0 (bit :: input) backup scratch result) =
      some
        (originalSourceCopyConfiguration computer 0 input (bit :: backup) (bit :: scratch)
          result) :=
  by
  classical
    cases bit <;>
    (first
      | rfl
      |
        (simp +instances [originalSourcePreservingMachine, originalSourceCopyConfiguration,
              originalSourceOutputConfiguration, sourcePhaseConfiguration, sourceInputSymbols,
              sourceOutputSymbols, Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux] <;>
            first
            | rfl
            | ( congr 2
                first
                | exact originalSourcePreserving_embedded_haltStacks _ _
                |
                  rw! (castMode := .all) [← sourceStacks_update_worker, ←
                    originalSourcePreservingStacks_update_backup, ← sourceStacks_update_scratch,
                    originalSourcePreserving_initialStacks_update]
                |
                  rw! (castMode := .all) [← sourceStacks_update_worker,
                    originalSourcePreserving_initialStacks_update]
                |
                  rw! (castMode := .all) [← sourceStacks_update_scratch, ←
                    sourceStacks_update_worker, originalSourcePreserving_initialStacks_update]
                | rw! (castMode := .all) [← sourceStacks_update_scratch]
                |
                  rw! (castMode := .all) [← sourceStacks_update_worker, ←
                    sourceStacks_update_result, originalSourcePreserving_haltStacks_update]
                |
                  rw! (castMode := .all) [← sourceStacks_update_worker,
                    originalSourcePreserving_haltStacks_update]
                |
                  rw! (castMode := .all) [← originalSourcePreservingStacks_update_backup, ←
                    sourceStacks_update_worker, originalSourcePreserving_haltStacks_update]
                |
                  rw! (castMode := .all) [← sourceStacks_update_result, ←
                    sourceStacks_update_worker, originalSourcePreserving_haltStacks_update]
                |
                  rw! (castMode := .all) [← sourceStacks_update_result,
                    originalSourcePreserving_embedded_haltStacks])))


-- @@ L929-939 expanded
private theorem originalSourcePreserving_copy_finish {f : List Bool → List Bool}
    (computer : BitTM f) (backup scratch result : List Bool) :
    (originalSourcePreservingMachine computer).step
        (originalSourceCopyConfiguration computer 0 [] backup scratch result) =
      some (originalSourceCopyConfiguration computer 1 [] backup scratch result) :=
  by
  classical(first
    | rfl
    |
      (simp +instances [originalSourcePreservingMachine, originalSourceCopyConfiguration,
            originalSourceOutputConfiguration, sourcePhaseConfiguration, sourceInputSymbols,
            sourceOutputSymbols, Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux] <;>
          first
          | rfl
          | ( congr 2
              first
              | exact originalSourcePreserving_embedded_haltStacks _ _
              |
                rw! (castMode := .all) [← sourceStacks_update_worker, ←
                  originalSourcePreservingStacks_update_backup, ← sourceStacks_update_scratch,
                  originalSourcePreserving_initialStacks_update]
              |
                rw! (castMode := .all) [← sourceStacks_update_worker,
                  originalSourcePreserving_initialStacks_update]
              |
                rw! (castMode := .all) [← sourceStacks_update_scratch, ← sourceStacks_update_worker,
                  originalSourcePreserving_initialStacks_update]
              | rw! (castMode := .all) [← sourceStacks_update_scratch]
              |
                rw! (castMode := .all) [← sourceStacks_update_worker, ← sourceStacks_update_result,
                  originalSourcePreserving_haltStacks_update]
              |
                rw! (castMode := .all) [← sourceStacks_update_worker,
                  originalSourcePreserving_haltStacks_update]
              |
                rw! (castMode := .all) [← originalSourcePreservingStacks_update_backup, ←
                  sourceStacks_update_worker, originalSourcePreserving_haltStacks_update]
              |
                rw! (castMode := .all) [← sourceStacks_update_result, ← sourceStacks_update_worker,
                  originalSourcePreserving_haltStacks_update]
              |
                rw! (castMode := .all) [← sourceStacks_update_result,
                  originalSourcePreserving_embedded_haltStacks])))


-- @@ L941-952 expanded
private theorem originalSourcePreserving_input_restore_step {f : List Bool → List Bool}
    (computer : BitTM f) (bit : Bool) (input backup scratch result : List Bool) :
    (originalSourcePreservingMachine computer).step
        (originalSourceCopyConfiguration computer 1 input backup (bit :: scratch) result) =
      some (originalSourceCopyConfiguration computer 1 (bit :: input) backup scratch result) :=
  by
  classical
    cases bit <;>
    (first
      | rfl
      |
        (simp +instances [originalSourcePreservingMachine, originalSourceCopyConfiguration,
              originalSourceOutputConfiguration, sourcePhaseConfiguration, sourceInputSymbols,
              sourceOutputSymbols, Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux] <;>
            first
            | rfl
            | ( congr 2
                first
                | exact originalSourcePreserving_embedded_haltStacks _ _
                |
                  rw! (castMode := .all) [← sourceStacks_update_worker, ←
                    originalSourcePreservingStacks_update_backup, ← sourceStacks_update_scratch,
                    originalSourcePreserving_initialStacks_update]
                |
                  rw! (castMode := .all) [← sourceStacks_update_worker,
                    originalSourcePreserving_initialStacks_update]
                |
                  rw! (castMode := .all) [← sourceStacks_update_scratch, ←
                    sourceStacks_update_worker, originalSourcePreserving_initialStacks_update]
                | rw! (castMode := .all) [← sourceStacks_update_scratch]
                |
                  rw! (castMode := .all) [← sourceStacks_update_worker, ←
                    sourceStacks_update_result, originalSourcePreserving_haltStacks_update]
                |
                  rw! (castMode := .all) [← sourceStacks_update_worker,
                    originalSourcePreserving_haltStacks_update]
                |
                  rw! (castMode := .all) [← originalSourcePreservingStacks_update_backup, ←
                    sourceStacks_update_worker, originalSourcePreserving_haltStacks_update]
                |
                  rw! (castMode := .all) [← sourceStacks_update_result, ←
                    sourceStacks_update_worker, originalSourcePreserving_haltStacks_update]
                |
                  rw! (castMode := .all) [← sourceStacks_update_result,
                    originalSourcePreserving_embedded_haltStacks])))


-- @@ L954-966 expanded
private theorem originalSourcePreserving_input_restore_finish {f : List Bool → List Bool}
    (computer : BitTM f) (input backup result : List Bool) :
    (originalSourcePreservingMachine computer).step
        (originalSourceCopyConfiguration computer 1 input backup [] result) =
      some
        (sourceWorkerConfiguration computer backup [] result
          (Turing.initList computer.tm (sourceInputSymbols computer input))) :=
  by
  classical(first
    | rfl
    |
      (simp +instances [originalSourcePreservingMachine, originalSourceCopyConfiguration,
            originalSourceOutputConfiguration, sourcePhaseConfiguration, sourceInputSymbols,
            sourceOutputSymbols, Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux] <;>
          first
          | rfl
          | ( congr 2
              first
              | exact originalSourcePreserving_embedded_haltStacks _ _
              |
                rw! (castMode := .all) [← sourceStacks_update_worker, ←
                  originalSourcePreservingStacks_update_backup, ← sourceStacks_update_scratch,
                  originalSourcePreserving_initialStacks_update]
              |
                rw! (castMode := .all) [← sourceStacks_update_worker,
                  originalSourcePreserving_initialStacks_update]
              |
                rw! (castMode := .all) [← sourceStacks_update_scratch, ← sourceStacks_update_worker,
                  originalSourcePreserving_initialStacks_update]
              | rw! (castMode := .all) [← sourceStacks_update_scratch]
              |
                rw! (castMode := .all) [← sourceStacks_update_worker, ← sourceStacks_update_result,
                  originalSourcePreserving_haltStacks_update]
              |
                rw! (castMode := .all) [← sourceStacks_update_worker,
                  originalSourcePreserving_haltStacks_update]
              |
                rw! (castMode := .all) [← originalSourcePreservingStacks_update_backup, ←
                  sourceStacks_update_worker, originalSourcePreserving_haltStacks_update]
              |
                rw! (castMode := .all) [← sourceStacks_update_result, ← sourceStacks_update_worker,
                  originalSourcePreserving_haltStacks_update]
              |
                rw! (castMode := .all) [← sourceStacks_update_result,
                  originalSourcePreserving_embedded_haltStacks])))


-- @@ L968-979 expanded
private theorem originalSourcePreserving_output_archive_step {f : List Bool → List Bool}
    (computer : BitTM f) (bit : Bool) (output backup scratch result : List Bool) :
    (originalSourcePreservingMachine computer).step
        (originalSourceOutputConfiguration computer 2 (bit :: output) backup scratch result) =
      some (originalSourceOutputConfiguration computer 2 output backup scratch (bit :: result)) :=
  by
  classical
    cases bit <;>
    (first
      | rfl
      |
        (simp +instances [originalSourcePreservingMachine, originalSourceCopyConfiguration,
              originalSourceOutputConfiguration, sourcePhaseConfiguration, sourceInputSymbols,
              sourceOutputSymbols, Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux] <;>
            first
            | rfl
            | ( congr 2
                first
                | exact originalSourcePreserving_embedded_haltStacks _ _
                |
                  rw! (castMode := .all) [← sourceStacks_update_worker, ←
                    originalSourcePreservingStacks_update_backup, ← sourceStacks_update_scratch,
                    originalSourcePreserving_initialStacks_update]
                |
                  rw! (castMode := .all) [← sourceStacks_update_worker,
                    originalSourcePreserving_initialStacks_update]
                |
                  rw! (castMode := .all) [← sourceStacks_update_scratch, ←
                    sourceStacks_update_worker, originalSourcePreserving_initialStacks_update]
                | rw! (castMode := .all) [← sourceStacks_update_scratch]
                |
                  rw! (castMode := .all) [← sourceStacks_update_worker, ←
                    sourceStacks_update_result, originalSourcePreserving_haltStacks_update]
                |
                  rw! (castMode := .all) [← sourceStacks_update_worker,
                    originalSourcePreserving_haltStacks_update]
                |
                  rw! (castMode := .all) [← originalSourcePreservingStacks_update_backup, ←
                    sourceStacks_update_worker, originalSourcePreserving_haltStacks_update]
                |
                  rw! (castMode := .all) [← sourceStacks_update_result, ←
                    sourceStacks_update_worker, originalSourcePreserving_haltStacks_update]
                |
                  rw! (castMode := .all) [← sourceStacks_update_result,
                    originalSourcePreserving_embedded_haltStacks])))


-- @@ L981-991 expanded
private theorem originalSourcePreserving_output_archive_finish {f : List Bool → List Bool}
    (computer : BitTM f) (backup scratch result : List Bool) :
    (originalSourcePreservingMachine computer).step
        (originalSourceOutputConfiguration computer 2 [] backup scratch result) =
      some (originalSourceOutputConfiguration computer 3 [] backup scratch result) :=
  by
  classical(first
    | rfl
    |
      (simp +instances [originalSourcePreservingMachine, originalSourceCopyConfiguration,
            originalSourceOutputConfiguration, sourcePhaseConfiguration, sourceInputSymbols,
            sourceOutputSymbols, Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux] <;>
          first
          | rfl
          | ( congr 2
              first
              | exact originalSourcePreserving_embedded_haltStacks _ _
              |
                rw! (castMode := .all) [← sourceStacks_update_worker, ←
                  originalSourcePreservingStacks_update_backup, ← sourceStacks_update_scratch,
                  originalSourcePreserving_initialStacks_update]
              |
                rw! (castMode := .all) [← sourceStacks_update_worker,
                  originalSourcePreserving_initialStacks_update]
              |
                rw! (castMode := .all) [← sourceStacks_update_scratch, ← sourceStacks_update_worker,
                  originalSourcePreserving_initialStacks_update]
              | rw! (castMode := .all) [← sourceStacks_update_scratch]
              |
                rw! (castMode := .all) [← sourceStacks_update_worker, ← sourceStacks_update_result,
                  originalSourcePreserving_haltStacks_update]
              |
                rw! (castMode := .all) [← sourceStacks_update_worker,
                  originalSourcePreserving_haltStacks_update]
              |
                rw! (castMode := .all) [← originalSourcePreservingStacks_update_backup, ←
                  sourceStacks_update_worker, originalSourcePreserving_haltStacks_update]
              |
                rw! (castMode := .all) [← sourceStacks_update_result, ← sourceStacks_update_worker,
                  originalSourcePreserving_haltStacks_update]
              |
                rw! (castMode := .all) [← sourceStacks_update_result,
                  originalSourcePreserving_embedded_haltStacks])))


-- @@ L993-1004 expanded
private theorem originalSourcePreserving_source_restore_step {f : List Bool → List Bool}
    (computer : BitTM f) (bit : Bool) (output backup result : List Bool) :
    (originalSourcePreservingMachine computer).step
        (originalSourceOutputConfiguration computer 3 output (bit :: backup) [] result) =
      some (originalSourceOutputConfiguration computer 3 (bit :: output) backup [] result) :=
  by
  classical
    cases bit <;>
    (first
      | rfl
      |
        (simp +instances [originalSourcePreservingMachine, originalSourceCopyConfiguration,
              originalSourceOutputConfiguration, sourcePhaseConfiguration, sourceInputSymbols,
              sourceOutputSymbols, Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux] <;>
            first
            | rfl
            | ( congr 2
                first
                | exact originalSourcePreserving_embedded_haltStacks _ _
                |
                  rw! (castMode := .all) [← sourceStacks_update_worker, ←
                    originalSourcePreservingStacks_update_backup, ← sourceStacks_update_scratch,
                    originalSourcePreserving_initialStacks_update]
                |
                  rw! (castMode := .all) [← sourceStacks_update_worker,
                    originalSourcePreserving_initialStacks_update]
                |
                  rw! (castMode := .all) [← sourceStacks_update_scratch, ←
                    sourceStacks_update_worker, originalSourcePreserving_initialStacks_update]
                | rw! (castMode := .all) [← sourceStacks_update_scratch]
                |
                  rw! (castMode := .all) [← sourceStacks_update_worker, ←
                    sourceStacks_update_result, originalSourcePreserving_haltStacks_update]
                |
                  rw! (castMode := .all) [← sourceStacks_update_worker,
                    originalSourcePreserving_haltStacks_update]
                |
                  rw! (castMode := .all) [← originalSourcePreservingStacks_update_backup, ←
                    sourceStacks_update_worker, originalSourcePreserving_haltStacks_update]
                |
                  rw! (castMode := .all) [← sourceStacks_update_result, ←
                    sourceStacks_update_worker, originalSourcePreserving_haltStacks_update]
                |
                  rw! (castMode := .all) [← sourceStacks_update_result,
                    originalSourcePreserving_embedded_haltStacks])))


-- @@ L1006-1016 expanded
private theorem originalSourcePreserving_source_restore_finish {f : List Bool → List Bool}
    (computer : BitTM f) (output result : List Bool) :
    (originalSourcePreservingMachine computer).step
        (originalSourceOutputConfiguration computer 3 output [] [] result) =
      some (originalSourceOutputConfiguration computer 4 (false :: output) [] [] result) :=
  by
  classical(first
    | rfl
    |
      (simp +instances [originalSourcePreservingMachine, originalSourceCopyConfiguration,
            originalSourceOutputConfiguration, sourcePhaseConfiguration, sourceInputSymbols,
            sourceOutputSymbols, Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux] <;>
          first
          | rfl
          | ( congr 2
              first
              | exact originalSourcePreserving_embedded_haltStacks _ _
              |
                rw! (castMode := .all) [← sourceStacks_update_worker, ←
                  originalSourcePreservingStacks_update_backup, ← sourceStacks_update_scratch,
                  originalSourcePreserving_initialStacks_update]
              |
                rw! (castMode := .all) [← sourceStacks_update_worker,
                  originalSourcePreserving_initialStacks_update]
              |
                rw! (castMode := .all) [← sourceStacks_update_scratch, ← sourceStacks_update_worker,
                  originalSourcePreserving_initialStacks_update]
              | rw! (castMode := .all) [← sourceStacks_update_scratch]
              |
                rw! (castMode := .all) [← sourceStacks_update_worker, ← sourceStacks_update_result,
                  originalSourcePreserving_haltStacks_update]
              |
                rw! (castMode := .all) [← sourceStacks_update_worker,
                  originalSourcePreserving_haltStacks_update]
              |
                rw! (castMode := .all) [← originalSourcePreservingStacks_update_backup, ←
                  sourceStacks_update_worker, originalSourcePreserving_haltStacks_update]
              |
                rw! (castMode := .all) [← sourceStacks_update_result, ← sourceStacks_update_worker,
                  originalSourcePreserving_haltStacks_update]
              |
                rw! (castMode := .all) [← sourceStacks_update_result,
                  originalSourcePreserving_embedded_haltStacks])))


-- @@ L1018-1029 expanded
private theorem originalSourcePreserving_result_restore_step {f : List Bool → List Bool}
    (computer : BitTM f) (bit : Bool) (output result : List Bool) :
    (originalSourcePreservingMachine computer).step
        (originalSourceOutputConfiguration computer 4 output [] [] (bit :: result)) =
      some (originalSourceOutputConfiguration computer 4 (bit :: output) [] [] result) :=
  by
  classical
    cases bit <;>
    (first
      | rfl
      |
        (simp +instances [originalSourcePreservingMachine, originalSourceCopyConfiguration,
              originalSourceOutputConfiguration, sourcePhaseConfiguration, sourceInputSymbols,
              sourceOutputSymbols, Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux] <;>
            first
            | rfl
            | ( congr 2
                first
                | exact originalSourcePreserving_embedded_haltStacks _ _
                |
                  rw! (castMode := .all) [← sourceStacks_update_worker, ←
                    originalSourcePreservingStacks_update_backup, ← sourceStacks_update_scratch,
                    originalSourcePreserving_initialStacks_update]
                |
                  rw! (castMode := .all) [← sourceStacks_update_worker,
                    originalSourcePreserving_initialStacks_update]
                |
                  rw! (castMode := .all) [← sourceStacks_update_scratch, ←
                    sourceStacks_update_worker, originalSourcePreserving_initialStacks_update]
                | rw! (castMode := .all) [← sourceStacks_update_scratch]
                |
                  rw! (castMode := .all) [← sourceStacks_update_worker, ←
                    sourceStacks_update_result, originalSourcePreserving_haltStacks_update]
                |
                  rw! (castMode := .all) [← sourceStacks_update_worker,
                    originalSourcePreserving_haltStacks_update]
                |
                  rw! (castMode := .all) [← originalSourcePreservingStacks_update_backup, ←
                    sourceStacks_update_worker, originalSourcePreserving_haltStacks_update]
                |
                  rw! (castMode := .all) [← sourceStacks_update_result, ←
                    sourceStacks_update_worker, originalSourcePreserving_haltStacks_update]
                |
                  rw! (castMode := .all) [← sourceStacks_update_result,
                    originalSourcePreserving_embedded_haltStacks])))


-- @@ L1031-1042 expanded
private theorem originalSourcePreserving_result_restore_finish {f : List Bool → List Bool}
    (computer : BitTM f) (output : List Bool) :
    (originalSourcePreservingMachine computer).step
        (originalSourceOutputConfiguration computer 4 output [] [] []) =
      some
        (Turing.haltList (originalSourcePreservingMachine computer)
          (sourceOutputSymbols computer output)) :=
  by
  classical(first
    | rfl
    |
      (simp +instances [originalSourcePreservingMachine, originalSourceCopyConfiguration,
            originalSourceOutputConfiguration, sourcePhaseConfiguration, sourceInputSymbols,
            sourceOutputSymbols, Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux] <;>
          first
          | rfl
          | ( congr 2
              first
              | exact originalSourcePreserving_embedded_haltStacks _ _
              |
                rw! (castMode := .all) [← sourceStacks_update_worker, ←
                  originalSourcePreservingStacks_update_backup, ← sourceStacks_update_scratch,
                  originalSourcePreserving_initialStacks_update]
              |
                rw! (castMode := .all) [← sourceStacks_update_worker,
                  originalSourcePreserving_initialStacks_update]
              |
                rw! (castMode := .all) [← sourceStacks_update_scratch, ← sourceStacks_update_worker,
                  originalSourcePreserving_initialStacks_update]
              | rw! (castMode := .all) [← sourceStacks_update_scratch]
              |
                rw! (castMode := .all) [← sourceStacks_update_worker, ← sourceStacks_update_result,
                  originalSourcePreserving_haltStacks_update]
              |
                rw! (castMode := .all) [← sourceStacks_update_worker,
                  originalSourcePreserving_haltStacks_update]
              |
                rw! (castMode := .all) [← originalSourcePreservingStacks_update_backup, ←
                  sourceStacks_update_worker, originalSourcePreserving_haltStacks_update]
              |
                rw! (castMode := .all) [← sourceStacks_update_result, ← sourceStacks_update_worker,
                  originalSourcePreserving_haltStacks_update]
              |
                rw! (castMode := .all) [← sourceStacks_update_result,
                  originalSourcePreserving_embedded_haltStacks])))


-- @@ L1044-1069 verbatim
private def originalSourcePreserving_copyTrace
    {f : List Bool → List Bool}
    (computer : BitTM f)
    (input backup scratch result : List Bool) :
    EvalsToInTime (originalSourcePreservingMachine computer).step
      (originalSourceCopyConfiguration
        computer 0 input backup scratch result)
      (some (originalSourceCopyConfiguration
        computer 1 []
        (input.reverse ++ backup)
        (input.reverse ++ scratch) result))
      (input.length + 1) := by
  induction input generalizing backup scratch with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.reverse_nil, List.nil_append, List.length_nil,
          zero_add] using
          oneStep _ _ (originalSourcePreserving_copy_finish computer backup scratch result)
  | cons bit remaining ih =>
      have hfirst := oneStep _ _ (originalSourcePreserving_copy_step
          computer bit remaining backup scratch result)
      have hrest := ih (bit :: backup) (bit :: scratch)
      have hfull := EvalsToInTime.trans (originalSourcePreservingMachine computer).step
        1 (remaining.length + 1) _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.reverse_cons, List.append_assoc, List.cons_append,
          List.nil_append,
          List.length_cons, Nat.add_comm, Nat.add_left_comm, Nat.reduceAdd] using hfull


-- @@ L1071-1097 verbatim
private def originalSourcePreserving_inputRestoreTrace
    {f : List Bool → List Bool}
    (computer : BitTM f)
    (scratch input backup result : List Bool) :
    EvalsToInTime (originalSourcePreservingMachine computer).step
      (originalSourceCopyConfiguration
        computer 1 input backup scratch result)
      (some (sourceWorkerConfiguration
        computer backup [] result
        (Turing.initList computer.tm
          (sourceInputSymbols computer
            (scratch.reverse ++ input)))))
      (scratch.length + 1) := by
  induction scratch generalizing input with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.reverse_nil, List.nil_append, List.length_nil,
          zero_add] using
          oneStep _ _ (originalSourcePreserving_input_restore_finish computer input backup result)
  | cons bit remaining ih =>
      have hfirst := oneStep _ _ (originalSourcePreserving_input_restore_step
          computer bit input backup remaining result)
      have hrest := ih (bit :: input)
      have hfull := EvalsToInTime.trans (originalSourcePreservingMachine computer).step
        1 (remaining.length + 1) _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.reverse_cons, List.append_assoc, List.cons_append,
          List.nil_append,
          List.length_cons, Nat.add_comm, Nat.add_left_comm, Nat.reduceAdd] using hfull


-- @@ L1099-1112 verbatim
private theorem originalSourcePreservingWorkerConfiguration_halt
    {f : List Bool → List Bool}
    (computer : BitTM f)
    (output backup scratch result : List Bool) :
    sourceWorkerConfiguration
        computer backup scratch result
        (Turing.haltList computer.tm
          (sourceOutputSymbols
            computer output)) =
      originalSourceOutputConfiguration
        computer 2 output backup scratch result := by
  simp only [sourceWorkerConfiguration, haltList, eq_mpr_eq_cast, Fin.isValue,
      originalSourceOutputConfiguration, sourcePhaseConfiguration]
  rfl


-- @@ L1114-1142 verbatim
private def originalSourcePreserving_workerTrace
    {f : List Bool → List Bool}
    (computer : BitTM f)
    (input backup scratch result : List Bool) :
    EvalsToInTime (originalSourcePreservingMachine computer).step
      (sourceWorkerConfiguration
        computer backup scratch result
        (Turing.initList computer.tm
          (sourceInputSymbols computer input)))
      (some (originalSourceOutputConfiguration
        computer 2 (f input) backup scratch result))
      (computer.time.eval input.length) := by
  have hworker := originalSourcePreservingWorker_evalsToInTime
    computer backup scratch result (computer.outputsFun input)
  simp only [bitEncoding] at hworker
  change EvalsToInTime
    (originalSourcePreservingMachine computer).step
    (sourceWorkerConfiguration
      computer backup scratch result
      (Turing.initList computer.tm
        (sourceInputSymbols computer input)))
    (some (sourceWorkerConfiguration
      computer backup scratch result
      (Turing.haltList computer.tm
        (sourceOutputSymbols
          computer (f input)))))
    (computer.time.eval input.length) at hworker
  rw [originalSourcePreservingWorkerConfiguration_halt] at hworker
  exact hworker


-- @@ L1144-1169 verbatim
private def originalSourcePreserving_outputArchiveTrace
    {f : List Bool → List Bool}
    (computer : BitTM f)
    (output backup scratch result : List Bool) :
    EvalsToInTime (originalSourcePreservingMachine computer).step
      (originalSourceOutputConfiguration
        computer 2 output backup scratch result)
      (some (originalSourceOutputConfiguration
        computer 3 [] backup scratch
        (output.reverse ++ result)))
      (output.length + 1) := by
  induction output generalizing result with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.reverse_nil, List.nil_append, List.length_nil,
          zero_add] using
          oneStep _ _ (originalSourcePreserving_output_archive_finish computer backup scratch
              result)
  | cons bit remaining ih =>
      have hfirst := oneStep _ _ (originalSourcePreserving_output_archive_step
          computer bit remaining backup scratch result)
      have hrest := ih (bit :: result)
      have hfull := EvalsToInTime.trans (originalSourcePreservingMachine computer).step
        1 (remaining.length + 1) _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.reverse_cons, List.append_assoc, List.cons_append,
          List.nil_append,
          List.length_cons, Nat.add_comm, Nat.add_left_comm, Nat.reduceAdd] using hfull


-- @@ L1171-1195 verbatim
private def originalSourcePreserving_sourceRestoreTrace
    {f : List Bool → List Bool}
    (computer : BitTM f)
    (backup output result : List Bool) :
    EvalsToInTime (originalSourcePreservingMachine computer).step
      (originalSourceOutputConfiguration
        computer 3 output backup [] result)
      (some (originalSourceOutputConfiguration
        computer 4
        (false :: (backup.reverse ++ output)) [] [] result))
      (backup.length + 1) := by
  induction backup generalizing output with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.reverse_nil, List.nil_append, List.length_nil,
          zero_add] using
          oneStep _ _ (originalSourcePreserving_source_restore_finish computer output result)
  | cons bit remaining ih =>
      have hfirst := oneStep _ _ (originalSourcePreserving_source_restore_step
          computer bit output remaining result)
      have hrest := ih (bit :: output)
      have hfull := EvalsToInTime.trans (originalSourcePreservingMachine computer).step
        1 (remaining.length + 1) _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.reverse_cons, List.append_assoc, List.cons_append,
          List.nil_append,
          List.length_cons, Nat.add_comm, Nat.add_left_comm, Nat.reduceAdd] using hfull


-- @@ L1197-1222 verbatim
private def originalSourcePreserving_resultRestoreTrace
    {f : List Bool → List Bool}
    (computer : BitTM f)
    (result output : List Bool) :
    EvalsToInTime (originalSourcePreservingMachine computer).step
      (originalSourceOutputConfiguration
        computer 4 output [] [] result)
      (some (Turing.haltList
        (originalSourcePreservingMachine computer)
        (sourceOutputSymbols computer
          (result.reverse ++ output))))
      (result.length + 1) := by
  induction result generalizing output with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.reverse_nil, List.nil_append, List.length_nil,
          zero_add] using
          oneStep _ _ (originalSourcePreserving_result_restore_finish computer output)
  | cons bit remaining ih =>
      have hfirst := oneStep _ _ (originalSourcePreserving_result_restore_step
          computer bit output remaining)
      have hrest := ih (bit :: output)
      have hfull := EvalsToInTime.trans (originalSourcePreservingMachine computer).step
        1 (remaining.length + 1) _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.reverse_cons, List.append_assoc, List.cons_append,
          List.nil_append,
          List.length_cons, Nat.add_comm, Nat.add_left_comm, Nat.reduceAdd] using hfull


-- @@ L1224-1228 verbatim
private def sourceTimePolynomial
    {f : List Bool → List Bool}
    (computer : BitTM f) : Polynomial ℕ :=
  computer.time + 3 * Polynomial.X +
    2 * GapCVP.TMComposition.outputLengthPolynomial computer + 8


-- @@ L1230-1279 verbatim
private def originalSourcePreserving_totalTrace
    {f : List Bool → List Bool}
    (computer : BitTM f)
    (input : List Bool) :
    EvalsToInTime (originalSourcePreservingMachine computer).step
      (Turing.initList (originalSourcePreservingMachine computer)
        (sourceInputSymbols computer input))
      (some (Turing.haltList
        (originalSourcePreservingMachine computer)
        (sourceOutputSymbols computer
          (originalSourcePreservingOutput f input))))
      ((sourceTimePolynomial computer).eval
        input.length) := by
  have hcopy := originalSourcePreserving_copyTrace
    computer input [] [] []
  simp only [List.append_nil] at hcopy
  rw [← originalSourcePreservingMachine_init] at hcopy
  have hrestore := originalSourcePreserving_inputRestoreTrace
    computer input.reverse [] input.reverse []
  simp only [List.reverse_reverse, List.append_nil,
    List.length_reverse] at hrestore
  have hworker := originalSourcePreserving_workerTrace
    computer input input.reverse [] []
  have harchive := originalSourcePreserving_outputArchiveTrace
    computer (f input) input.reverse [] []
  simp only [List.append_nil] at harchive
  have hsource := originalSourcePreserving_sourceRestoreTrace
    computer input.reverse [] (f input).reverse
  simp only [List.reverse_reverse, List.append_nil,
    List.length_reverse] at hsource
  have hresult := originalSourcePreserving_resultRestoreTrace
    computer (f input).reverse (false :: input)
  simp only [List.reverse_reverse, List.length_reverse] at hresult
  have hfirst := EvalsToInTime.trans (originalSourcePreservingMachine computer).step
    _ _ _ _ _ hcopy hrestore
  have hsecond := EvalsToInTime.trans (originalSourcePreservingMachine computer).step
    _ _ _ _ _ hfirst hworker
  have hthird := EvalsToInTime.trans (originalSourcePreservingMachine computer).step
    _ _ _ _ _ hsecond harchive
  have hfourth := EvalsToInTime.trans (originalSourcePreservingMachine computer).step
    _ _ _ _ _ hthird hsource
  have hfull := EvalsToInTime.trans (originalSourcePreservingMachine computer).step
    _ _ _ _ _ hfourth hresult
  have hlength :=
    GapCVP.TMComposition.outputLengthPolynomial_bounds
      computer input
  apply rebound hfull
  simp only [sourceTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X]
  omega


-- @@ L1281-1302 verbatim
/-- GapCVP reduction support. -/
noncomputable def originalSourcePreservingComputable
    {f : List Bool → List Bool}
    (computer : BitTM f) :
    BitTM
      (originalSourcePreservingOutput f) where
  tm := originalSourcePreservingMachine computer
  inputAlphabet := computer.inputAlphabet
  outputAlphabet := computer.outputAlphabet
  time := sourceTimePolynomial computer
  outputsFun input := by
    change EvalsToInTime
      (originalSourcePreservingMachine computer).step
      (Turing.initList (originalSourcePreservingMachine computer)
        (sourceInputSymbols computer input))
      (some (Turing.haltList
        (originalSourcePreservingMachine computer)
        (sourceOutputSymbols computer
          (originalSourcePreservingOutput f input))))
      ((sourceTimePolynomial computer).eval
        input.length)
    exact originalSourcePreserving_totalTrace computer input


-- @@ L1304-1304 verbatim
end


-- @@ L1306-1306 verbatim
end SourceOriginalSourcePreservingTM


-- @@ L1308-1308 verbatim
namespace CNFGuardedSourceDescriptorRotationBoundedFoldTM


-- @@ L1310-1310 verbatim
open Computability Turing GapCVP.BinaryEncoding GapCVP.SourceTotalStructuralDecoder


-- @@ L1312-1317 verbatim
theorem guardedRotation_readUnaryPrefix_some_reconstruct
    (input : List Bool) (count : ℕ) (tail : List Bool)
    (hread : readUnaryPrefix input = some (count, tail)) :
    input = List.replicate count true ++ false :: tail := by
  exact GapCVP.SourceInterpolationRowTM.readUnaryPrefix_some_decompose
    input count tail hread


-- @@ L1319-1324 verbatim
theorem guardedRotation_readLengthPrefixedWord_some_reconstruct
    (input payload suffix : List Bool)
    (hread : readLengthPrefixedWord input = some (payload, suffix)) :
    input = lengthPrefixedWord payload ++ suffix := by
  exact GapCVP.FormulaSemanticCert.readLengthPrefixedWord_some_reconstruct
    input payload suffix hread


-- @@ L1326-1326 verbatim
end CNFGuardedSourceDescriptorRotationBoundedFoldTM


-- @@ L1328-1328 verbatim
namespace CNFFlatAdjacentRecordSwapTM


-- @@ L1330-1330 verbatim
open Turing GapCVP.BinaryEncoding GapCVP.CNFGuardedSourceDescriptorRotationBoundedFoldTM


-- @@ L1332-1341 verbatim
/-- Swap the first two length-prefixed records while preserving the suffix. -/
@[expose] def flatAdjacentRecordSwapOutput (input : List Bool) : List Bool :=
  match readLengthPrefixedWord input with
  | none => []
  | some (first, rest) =>
      match readLengthPrefixedWord rest with
      | none => []
      | some (second, suffix) =>
          lengthPrefixedWord second ++
            lengthPrefixedWord first ++ suffix


-- @@ L1343-1350 verbatim
theorem flatAdjacentRecordSwapOutput_records
    (first second suffix : List Bool) :
    flatAdjacentRecordSwapOutput
      (lengthPrefixedWord first ++
        lengthPrefixedWord second ++ suffix) =
      lengthPrefixedWord second ++
        lengthPrefixedWord first ++ suffix := by
  simp only [flatAdjacentRecordSwapOutput, List.append_assoc, readLengthPrefixedWord_append]


-- @@ L1352-1373 verbatim
theorem flatAdjacentRecordSwapOutput_length_le
    (input : List Bool) :
    (flatAdjacentRecordSwapOutput input).length ≤ input.length := by
  cases hfirst : readLengthPrefixedWord input with
  | none => simp only [flatAdjacentRecordSwapOutput, hfirst, List.length_nil, zero_le]
  | some parsed =>
      obtain ⟨first, rest⟩ := parsed
      cases hsecond : readLengthPrefixedWord rest with
      | none => simp only [flatAdjacentRecordSwapOutput, hfirst, hsecond, List.length_nil, zero_le]
      | some parsed =>
          obtain ⟨second, suffix⟩ := parsed
          have horiginal :=
            guardedRotation_readLengthPrefixedWord_some_reconstruct
              input first rest hfirst
          have hrest :=
            guardedRotation_readLengthPrefixedWord_some_reconstruct
              rest second suffix hsecond
          simp only [flatAdjacentRecordSwapOutput, hfirst, hsecond,
            List.length_append]
          rw [horiginal, hrest]
          simp only [List.length_append]
          omega


-- @@ L1375-1381 verbatim
private def flatAdjacentRecordPeek (stack : Fin 4)
    (present absent : Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 7) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 7) (Option Bool) :=
  .peek stack (fun _ symbol => symbol)
    (.branch (fun symbol => symbol.isSome) present absent)


-- @@ L1383-1388 verbatim
private def flatAdjacentRecordPop (stack : Fin 4)
    (next : Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 7) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 7) (Option Bool) :=
  .pop stack (fun state _ => state) next


-- @@ L1390-1395 verbatim
private def flatAdjacentRecordPushBit (stack : Fin 4)
    (next : Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 7) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 7) (Option Bool) :=
  .push stack (fun state => state.getD false) next


-- @@ L1397-1402 verbatim
private def flatAdjacentRecordPushConstant (stack : Fin 4) (bit : Bool)
    (next : Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 7) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 7) (Option Bool) :=
  .push stack (fun _ => bit) next


-- @@ L1404-1407 verbatim
private def flatAdjacentRecordGoto (phase : Fin 7) :
    Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 7) (Option Bool) :=
  .load (fun _ => none) (.goto (fun _ => phase))


-- @@ L1409-1422 verbatim
/-- GapCVP reduction support. -/
def flatAdjacentRecordFirstPrefixStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 7) (Option Bool) :=
  flatAdjacentRecordPeek 0
    (.branch (fun state => state.getD false)
      (flatAdjacentRecordPop 0
        (flatAdjacentRecordPushConstant 1 true
          (flatAdjacentRecordPushConstant 3 true
            (flatAdjacentRecordGoto 0))))
      (flatAdjacentRecordPop 0
        (flatAdjacentRecordPushConstant 1 false
          (flatAdjacentRecordGoto 1))))
    (flatAdjacentRecordGoto 6)


-- @@ L1424-1435 verbatim
/-- GapCVP reduction support. -/
def flatAdjacentRecordFirstPayloadStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 7) (Option Bool) :=
  flatAdjacentRecordPeek 3
    (flatAdjacentRecordPeek 0
      (flatAdjacentRecordPop 3
        (flatAdjacentRecordPop 0
          (flatAdjacentRecordPushBit 1
            (flatAdjacentRecordGoto 1))))
      (flatAdjacentRecordGoto 6))
    (flatAdjacentRecordGoto 2)


-- @@ L1437-1450 verbatim
/-- GapCVP reduction support. -/
def flatAdjacentRecordSecondPrefixStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 7) (Option Bool) :=
  flatAdjacentRecordPeek 0
    (.branch (fun state => state.getD false)
      (flatAdjacentRecordPop 0
        (flatAdjacentRecordPushConstant 2 true
          (flatAdjacentRecordPushConstant 3 true
            (flatAdjacentRecordGoto 2))))
      (flatAdjacentRecordPop 0
        (flatAdjacentRecordPushConstant 2 false
          (flatAdjacentRecordGoto 3))))
    (flatAdjacentRecordGoto 6)


-- @@ L1452-1463 verbatim
/-- GapCVP reduction support. -/
def flatAdjacentRecordSecondPayloadStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 7) (Option Bool) :=
  flatAdjacentRecordPeek 3
    (flatAdjacentRecordPeek 0
      (flatAdjacentRecordPop 3
        (flatAdjacentRecordPop 0
          (flatAdjacentRecordPushBit 2
            (flatAdjacentRecordGoto 3))))
      (flatAdjacentRecordGoto 6))
    (flatAdjacentRecordGoto 4)


-- @@ L1465-1473 verbatim
/-- GapCVP reduction support. -/
def flatAdjacentRecordRestoreFirstStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 7) (Option Bool) :=
  flatAdjacentRecordPeek 1
    (flatAdjacentRecordPop 1
      (flatAdjacentRecordPushBit 0
        (flatAdjacentRecordGoto 4)))
    (flatAdjacentRecordGoto 5)


-- @@ L1475-1483 verbatim
/-- GapCVP reduction support. -/
def flatAdjacentRecordRestoreSecondStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 7) (Option Bool) :=
  flatAdjacentRecordPeek 2
    (flatAdjacentRecordPop 2
      (flatAdjacentRecordPushBit 0
        (flatAdjacentRecordGoto 5)))
    .halt


-- @@ L1485-1497 verbatim
/-- GapCVP reduction support. -/
def flatAdjacentRecordFailureStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 4 => Bool) (Fin 7) (Option Bool) :=
  flatAdjacentRecordPeek 0
    (flatAdjacentRecordPop 0 (flatAdjacentRecordGoto 6))
    (flatAdjacentRecordPeek 1
      (flatAdjacentRecordPop 1 (flatAdjacentRecordGoto 6))
      (flatAdjacentRecordPeek 2
        (flatAdjacentRecordPop 2 (flatAdjacentRecordGoto 6))
        (flatAdjacentRecordPeek 3
          (flatAdjacentRecordPop 3 (flatAdjacentRecordGoto 6))
          .halt)))


-- @@ L1499-1523 verbatim
/-- GapCVP reduction support. -/
abbrev actualFlatAdjacentRecordSwapMachine : Turing.FinTM2 where
  K := Fin 4
  k₀ := 0
  k₁ := 0
  Γ _ := Bool
  Λ := Fin 7
  main := 0
  σ := Option Bool
  initialState := none
  m phase :=
    if phase = (0 : Fin 7) then
      flatAdjacentRecordFirstPrefixStatement
    else if phase = (1 : Fin 7) then
      flatAdjacentRecordFirstPayloadStatement
    else if phase = (2 : Fin 7) then
      flatAdjacentRecordSecondPrefixStatement
    else if phase = (3 : Fin 7) then
      flatAdjacentRecordSecondPayloadStatement
    else if phase = (4 : Fin 7) then
      flatAdjacentRecordRestoreFirstStatement
    else if phase = (5 : Fin 7) then
      flatAdjacentRecordRestoreSecondStatement
    else
      flatAdjacentRecordFailureStatement


-- @@ L1525-1531 verbatim
/-- GapCVP reduction support. -/
def flatAdjacentRecordConfiguration (phase : Fin 7)
    (input first second counter : List Bool) :
    actualFlatAdjacentRecordSwapMachine.Cfg where
  l := some phase
  var := none
  stk := ![input, first, second, counter]


-- @@ L1533-1542 verbatim
theorem actualFlatAdjacentRecordSwapMachine_init
    (input : List Bool) :
    Turing.initList actualFlatAdjacentRecordSwapMachine input =
      flatAdjacentRecordConfiguration 0 input [] [] [] := by
  simp only [actualFlatAdjacentRecordSwapMachine, Fin.isValue, initList, eq_mpr_eq_cast, cast_eq,
      dite_eq_ite,
      flatAdjacentRecordConfiguration]
  congr 1
  funext stack
  fin_cases stack <;> simp


-- @@ L1544-1565 verbatim
/-- Executes the `flatAdjacentRecordStepTac` machine-step simplifier. -/
macro "flatAdjacentRecordStepTac" : tactic =>
  `(tactic|
    (first
      | rfl
      | (simp [actualFlatAdjacentRecordSwapMachine,
          flatAdjacentRecordConfiguration,
          flatAdjacentRecordPeek, flatAdjacentRecordPop,
          flatAdjacentRecordPushBit, flatAdjacentRecordPushConstant,
          flatAdjacentRecordGoto,
          flatAdjacentRecordFirstPrefixStatement,
          flatAdjacentRecordFirstPayloadStatement,
          flatAdjacentRecordSecondPrefixStatement,
          flatAdjacentRecordSecondPayloadStatement,
          flatAdjacentRecordRestoreFirstStatement,
          flatAdjacentRecordRestoreSecondStatement,
          flatAdjacentRecordFailureStatement,
          Turing.haltList, Turing.FinTM2.step,
          Turing.TM2.step, Turing.TM2.stepAux] <;>
          try { congr 2; funext stack; fin_cases stack <;>
            (first | rfl | simp [Function.update]) } <;>
          try rfl)))


-- @@ L1567-1575 expanded
/-- Internal support shared across GapCVP continuation modules. -/
theorem flatAdjacentRecord_firstPrefix_true (input first second counter : List Bool) :
    actualFlatAdjacentRecordSwapMachine.step
        (flatAdjacentRecordConfiguration 0 (true :: input) first second counter) =
      some (flatAdjacentRecordConfiguration 0 input (true :: first) second (true :: counter)) :=
  by
  (first
    | rfl
    |
      (simp [actualFlatAdjacentRecordSwapMachine, flatAdjacentRecordConfiguration,
              flatAdjacentRecordPeek, flatAdjacentRecordPop, flatAdjacentRecordPushBit,
              flatAdjacentRecordPushConstant, flatAdjacentRecordGoto,
              flatAdjacentRecordFirstPrefixStatement, flatAdjacentRecordFirstPayloadStatement,
              flatAdjacentRecordSecondPrefixStatement, flatAdjacentRecordSecondPayloadStatement,
              flatAdjacentRecordRestoreFirstStatement, flatAdjacentRecordRestoreSecondStatement,
              flatAdjacentRecordFailureStatement, Turing.haltList, Turing.FinTM2.step,
              Turing.TM2.step, Turing.TM2.stepAux] <;>
            try { congr 2; funext stack;
              fin_cases stack <;>
                (first
                  | rfl
                  | simp [Function.update])
            } <;>
          try rfl))


-- @@ L1577-1585 expanded
/-- Internal support shared across GapCVP continuation modules. -/
theorem flatAdjacentRecord_firstPrefix_false (input first second counter : List Bool) :
    actualFlatAdjacentRecordSwapMachine.step
        (flatAdjacentRecordConfiguration 0 (false :: input) first second counter) =
      some (flatAdjacentRecordConfiguration 1 input (false :: first) second counter) :=
  by
  (first
    | rfl
    |
      (simp [actualFlatAdjacentRecordSwapMachine, flatAdjacentRecordConfiguration,
              flatAdjacentRecordPeek, flatAdjacentRecordPop, flatAdjacentRecordPushBit,
              flatAdjacentRecordPushConstant, flatAdjacentRecordGoto,
              flatAdjacentRecordFirstPrefixStatement, flatAdjacentRecordFirstPayloadStatement,
              flatAdjacentRecordSecondPrefixStatement, flatAdjacentRecordSecondPayloadStatement,
              flatAdjacentRecordRestoreFirstStatement, flatAdjacentRecordRestoreSecondStatement,
              flatAdjacentRecordFailureStatement, Turing.haltList, Turing.FinTM2.step,
              Turing.TM2.step, Turing.TM2.stepAux] <;>
            try { congr 2; funext stack;
              fin_cases stack <;>
                (first
                  | rfl
                  | simp [Function.update])
            } <;>
          try rfl))


-- @@ L1587-1594 expanded
/-- Internal support shared across GapCVP continuation modules. -/
theorem flatAdjacentRecord_firstPrefix_missing (first second counter : List Bool) :
    actualFlatAdjacentRecordSwapMachine.step
        (flatAdjacentRecordConfiguration 0 [] first second counter) =
      some (flatAdjacentRecordConfiguration 6 [] first second counter) :=
  by
  (first
    | rfl
    |
      (simp [actualFlatAdjacentRecordSwapMachine, flatAdjacentRecordConfiguration,
              flatAdjacentRecordPeek, flatAdjacentRecordPop, flatAdjacentRecordPushBit,
              flatAdjacentRecordPushConstant, flatAdjacentRecordGoto,
              flatAdjacentRecordFirstPrefixStatement, flatAdjacentRecordFirstPayloadStatement,
              flatAdjacentRecordSecondPrefixStatement, flatAdjacentRecordSecondPayloadStatement,
              flatAdjacentRecordRestoreFirstStatement, flatAdjacentRecordRestoreSecondStatement,
              flatAdjacentRecordFailureStatement, Turing.haltList, Turing.FinTM2.step,
              Turing.TM2.step, Turing.TM2.stepAux] <;>
            try { congr 2; funext stack;
              fin_cases stack <;>
                (first
                  | rfl
                  | simp [Function.update])
            } <;>
          try rfl))


-- @@ L1596-1604 expanded
/-- Internal support shared across GapCVP continuation modules. -/
theorem flatAdjacentRecord_firstPayload_step (bit : Bool) (input first second counter : List Bool) :
    actualFlatAdjacentRecordSwapMachine.step
        (flatAdjacentRecordConfiguration 1 (bit :: input) first second (true :: counter)) =
      some (flatAdjacentRecordConfiguration 1 input (bit :: first) second counter) :=
  by
  cases bit <;>
    (first
      | rfl
      |
        (simp [actualFlatAdjacentRecordSwapMachine, flatAdjacentRecordConfiguration,
                flatAdjacentRecordPeek, flatAdjacentRecordPop, flatAdjacentRecordPushBit,
                flatAdjacentRecordPushConstant, flatAdjacentRecordGoto,
                flatAdjacentRecordFirstPrefixStatement, flatAdjacentRecordFirstPayloadStatement,
                flatAdjacentRecordSecondPrefixStatement, flatAdjacentRecordSecondPayloadStatement,
                flatAdjacentRecordRestoreFirstStatement, flatAdjacentRecordRestoreSecondStatement,
                flatAdjacentRecordFailureStatement, Turing.haltList, Turing.FinTM2.step,
                Turing.TM2.step, Turing.TM2.stepAux] <;>
              try { congr 2; funext stack;
                fin_cases stack <;>
                  (first
                    | rfl
                    | simp [Function.update])
              } <;>
            try rfl))


-- @@ L1606-1614 expanded
/-- Internal support shared across GapCVP continuation modules. -/
theorem flatAdjacentRecord_firstPayload_missing (first second counter : List Bool) :
    actualFlatAdjacentRecordSwapMachine.step
        (flatAdjacentRecordConfiguration 1 [] first second (true :: counter)) =
      some (flatAdjacentRecordConfiguration 6 [] first second (true :: counter)) :=
  by
  (first
    | rfl
    |
      (simp [actualFlatAdjacentRecordSwapMachine, flatAdjacentRecordConfiguration,
              flatAdjacentRecordPeek, flatAdjacentRecordPop, flatAdjacentRecordPushBit,
              flatAdjacentRecordPushConstant, flatAdjacentRecordGoto,
              flatAdjacentRecordFirstPrefixStatement, flatAdjacentRecordFirstPayloadStatement,
              flatAdjacentRecordSecondPrefixStatement, flatAdjacentRecordSecondPayloadStatement,
              flatAdjacentRecordRestoreFirstStatement, flatAdjacentRecordRestoreSecondStatement,
              flatAdjacentRecordFailureStatement, Turing.haltList, Turing.FinTM2.step,
              Turing.TM2.step, Turing.TM2.stepAux] <;>
            try { congr 2; funext stack;
              fin_cases stack <;>
                (first
                  | rfl
                  | simp [Function.update])
            } <;>
          try rfl))


-- @@ L1616-1622 expanded
/-- Internal support shared across GapCVP continuation modules. -/
theorem flatAdjacentRecord_firstPayload_finish (input first second : List Bool) :
    actualFlatAdjacentRecordSwapMachine.step
        (flatAdjacentRecordConfiguration 1 input first second []) =
      some (flatAdjacentRecordConfiguration 2 input first second []) :=
  by
  (first
    | rfl
    |
      (simp [actualFlatAdjacentRecordSwapMachine, flatAdjacentRecordConfiguration,
              flatAdjacentRecordPeek, flatAdjacentRecordPop, flatAdjacentRecordPushBit,
              flatAdjacentRecordPushConstant, flatAdjacentRecordGoto,
              flatAdjacentRecordFirstPrefixStatement, flatAdjacentRecordFirstPayloadStatement,
              flatAdjacentRecordSecondPrefixStatement, flatAdjacentRecordSecondPayloadStatement,
              flatAdjacentRecordRestoreFirstStatement, flatAdjacentRecordRestoreSecondStatement,
              flatAdjacentRecordFailureStatement, Turing.haltList, Turing.FinTM2.step,
              Turing.TM2.step, Turing.TM2.stepAux] <;>
            try { congr 2; funext stack;
              fin_cases stack <;>
                (first
                  | rfl
                  | simp [Function.update])
            } <;>
          try rfl))


-- @@ L1624-1632 expanded
/-- Internal support shared across GapCVP continuation modules. -/
theorem flatAdjacentRecord_secondPrefix_true (input first second counter : List Bool) :
    actualFlatAdjacentRecordSwapMachine.step
        (flatAdjacentRecordConfiguration 2 (true :: input) first second counter) =
      some (flatAdjacentRecordConfiguration 2 input first (true :: second) (true :: counter)) :=
  by
  (first
    | rfl
    |
      (simp [actualFlatAdjacentRecordSwapMachine, flatAdjacentRecordConfiguration,
              flatAdjacentRecordPeek, flatAdjacentRecordPop, flatAdjacentRecordPushBit,
              flatAdjacentRecordPushConstant, flatAdjacentRecordGoto,
              flatAdjacentRecordFirstPrefixStatement, flatAdjacentRecordFirstPayloadStatement,
              flatAdjacentRecordSecondPrefixStatement, flatAdjacentRecordSecondPayloadStatement,
              flatAdjacentRecordRestoreFirstStatement, flatAdjacentRecordRestoreSecondStatement,
              flatAdjacentRecordFailureStatement, Turing.haltList, Turing.FinTM2.step,
              Turing.TM2.step, Turing.TM2.stepAux] <;>
            try { congr 2; funext stack;
              fin_cases stack <;>
                (first
                  | rfl
                  | simp [Function.update])
            } <;>
          try rfl))


-- @@ L1634-1642 expanded
/-- Internal support shared across GapCVP continuation modules. -/
theorem flatAdjacentRecord_secondPrefix_false (input first second counter : List Bool) :
    actualFlatAdjacentRecordSwapMachine.step
        (flatAdjacentRecordConfiguration 2 (false :: input) first second counter) =
      some (flatAdjacentRecordConfiguration 3 input first (false :: second) counter) :=
  by
  (first
    | rfl
    |
      (simp [actualFlatAdjacentRecordSwapMachine, flatAdjacentRecordConfiguration,
              flatAdjacentRecordPeek, flatAdjacentRecordPop, flatAdjacentRecordPushBit,
              flatAdjacentRecordPushConstant, flatAdjacentRecordGoto,
              flatAdjacentRecordFirstPrefixStatement, flatAdjacentRecordFirstPayloadStatement,
              flatAdjacentRecordSecondPrefixStatement, flatAdjacentRecordSecondPayloadStatement,
              flatAdjacentRecordRestoreFirstStatement, flatAdjacentRecordRestoreSecondStatement,
              flatAdjacentRecordFailureStatement, Turing.haltList, Turing.FinTM2.step,
              Turing.TM2.step, Turing.TM2.stepAux] <;>
            try { congr 2; funext stack;
              fin_cases stack <;>
                (first
                  | rfl
                  | simp [Function.update])
            } <;>
          try rfl))


-- @@ L1644-1651 expanded
/-- Internal support shared across GapCVP continuation modules. -/
theorem flatAdjacentRecord_secondPrefix_missing (first second counter : List Bool) :
    actualFlatAdjacentRecordSwapMachine.step
        (flatAdjacentRecordConfiguration 2 [] first second counter) =
      some (flatAdjacentRecordConfiguration 6 [] first second counter) :=
  by
  (first
    | rfl
    |
      (simp [actualFlatAdjacentRecordSwapMachine, flatAdjacentRecordConfiguration,
              flatAdjacentRecordPeek, flatAdjacentRecordPop, flatAdjacentRecordPushBit,
              flatAdjacentRecordPushConstant, flatAdjacentRecordGoto,
              flatAdjacentRecordFirstPrefixStatement, flatAdjacentRecordFirstPayloadStatement,
              flatAdjacentRecordSecondPrefixStatement, flatAdjacentRecordSecondPayloadStatement,
              flatAdjacentRecordRestoreFirstStatement, flatAdjacentRecordRestoreSecondStatement,
              flatAdjacentRecordFailureStatement, Turing.haltList, Turing.FinTM2.step,
              Turing.TM2.step, Turing.TM2.stepAux] <;>
            try { congr 2; funext stack;
              fin_cases stack <;>
                (first
                  | rfl
                  | simp [Function.update])
            } <;>
          try rfl))


-- @@ L1653-1661 expanded
/-- Internal support shared across GapCVP continuation modules. -/
theorem flatAdjacentRecord_secondPayload_step (bit : Bool)
    (input first second counter : List Bool) :
    actualFlatAdjacentRecordSwapMachine.step
        (flatAdjacentRecordConfiguration 3 (bit :: input) first second (true :: counter)) =
      some (flatAdjacentRecordConfiguration 3 input first (bit :: second) counter) :=
  by
  cases bit <;>
    (first
      | rfl
      |
        (simp [actualFlatAdjacentRecordSwapMachine, flatAdjacentRecordConfiguration,
                flatAdjacentRecordPeek, flatAdjacentRecordPop, flatAdjacentRecordPushBit,
                flatAdjacentRecordPushConstant, flatAdjacentRecordGoto,
                flatAdjacentRecordFirstPrefixStatement, flatAdjacentRecordFirstPayloadStatement,
                flatAdjacentRecordSecondPrefixStatement, flatAdjacentRecordSecondPayloadStatement,
                flatAdjacentRecordRestoreFirstStatement, flatAdjacentRecordRestoreSecondStatement,
                flatAdjacentRecordFailureStatement, Turing.haltList, Turing.FinTM2.step,
                Turing.TM2.step, Turing.TM2.stepAux] <;>
              try { congr 2; funext stack;
                fin_cases stack <;>
                  (first
                    | rfl
                    | simp [Function.update])
              } <;>
            try rfl))


-- @@ L1663-1671 expanded
/-- Internal support shared across GapCVP continuation modules. -/
theorem flatAdjacentRecord_secondPayload_missing (first second counter : List Bool) :
    actualFlatAdjacentRecordSwapMachine.step
        (flatAdjacentRecordConfiguration 3 [] first second (true :: counter)) =
      some (flatAdjacentRecordConfiguration 6 [] first second (true :: counter)) :=
  by
  (first
    | rfl
    |
      (simp [actualFlatAdjacentRecordSwapMachine, flatAdjacentRecordConfiguration,
              flatAdjacentRecordPeek, flatAdjacentRecordPop, flatAdjacentRecordPushBit,
              flatAdjacentRecordPushConstant, flatAdjacentRecordGoto,
              flatAdjacentRecordFirstPrefixStatement, flatAdjacentRecordFirstPayloadStatement,
              flatAdjacentRecordSecondPrefixStatement, flatAdjacentRecordSecondPayloadStatement,
              flatAdjacentRecordRestoreFirstStatement, flatAdjacentRecordRestoreSecondStatement,
              flatAdjacentRecordFailureStatement, Turing.haltList, Turing.FinTM2.step,
              Turing.TM2.step, Turing.TM2.stepAux] <;>
            try { congr 2; funext stack;
              fin_cases stack <;>
                (first
                  | rfl
                  | simp [Function.update])
            } <;>
          try rfl))


-- @@ L1673-1679 expanded
/-- Internal support shared across GapCVP continuation modules. -/
theorem flatAdjacentRecord_secondPayload_finish (input first second : List Bool) :
    actualFlatAdjacentRecordSwapMachine.step
        (flatAdjacentRecordConfiguration 3 input first second []) =
      some (flatAdjacentRecordConfiguration 4 input first second []) :=
  by
  (first
    | rfl
    |
      (simp [actualFlatAdjacentRecordSwapMachine, flatAdjacentRecordConfiguration,
              flatAdjacentRecordPeek, flatAdjacentRecordPop, flatAdjacentRecordPushBit,
              flatAdjacentRecordPushConstant, flatAdjacentRecordGoto,
              flatAdjacentRecordFirstPrefixStatement, flatAdjacentRecordFirstPayloadStatement,
              flatAdjacentRecordSecondPrefixStatement, flatAdjacentRecordSecondPayloadStatement,
              flatAdjacentRecordRestoreFirstStatement, flatAdjacentRecordRestoreSecondStatement,
              flatAdjacentRecordFailureStatement, Turing.haltList, Turing.FinTM2.step,
              Turing.TM2.step, Turing.TM2.stepAux] <;>
            try { congr 2; funext stack;
              fin_cases stack <;>
                (first
                  | rfl
                  | simp [Function.update])
            } <;>
          try rfl))


-- @@ L1681-1689 expanded
/-- Internal support shared across GapCVP continuation modules. -/
theorem flatAdjacentRecord_restoreFirst_step (bit : Bool) (input first second : List Bool) :
    actualFlatAdjacentRecordSwapMachine.step
        (flatAdjacentRecordConfiguration 4 input (bit :: first) second []) =
      some (flatAdjacentRecordConfiguration 4 (bit :: input) first second []) :=
  by
  cases bit <;>
    (first
      | rfl
      |
        (simp [actualFlatAdjacentRecordSwapMachine, flatAdjacentRecordConfiguration,
                flatAdjacentRecordPeek, flatAdjacentRecordPop, flatAdjacentRecordPushBit,
                flatAdjacentRecordPushConstant, flatAdjacentRecordGoto,
                flatAdjacentRecordFirstPrefixStatement, flatAdjacentRecordFirstPayloadStatement,
                flatAdjacentRecordSecondPrefixStatement, flatAdjacentRecordSecondPayloadStatement,
                flatAdjacentRecordRestoreFirstStatement, flatAdjacentRecordRestoreSecondStatement,
                flatAdjacentRecordFailureStatement, Turing.haltList, Turing.FinTM2.step,
                Turing.TM2.step, Turing.TM2.stepAux] <;>
              try { congr 2; funext stack;
                fin_cases stack <;>
                  (first
                    | rfl
                    | simp [Function.update])
              } <;>
            try rfl))


-- @@ L1691-1697 expanded
/-- Internal support shared across GapCVP continuation modules. -/
theorem flatAdjacentRecord_restoreFirst_finish (input second : List Bool) :
    actualFlatAdjacentRecordSwapMachine.step
        (flatAdjacentRecordConfiguration 4 input [] second []) =
      some (flatAdjacentRecordConfiguration 5 input [] second []) :=
  by
  (first
    | rfl
    |
      (simp [actualFlatAdjacentRecordSwapMachine, flatAdjacentRecordConfiguration,
              flatAdjacentRecordPeek, flatAdjacentRecordPop, flatAdjacentRecordPushBit,
              flatAdjacentRecordPushConstant, flatAdjacentRecordGoto,
              flatAdjacentRecordFirstPrefixStatement, flatAdjacentRecordFirstPayloadStatement,
              flatAdjacentRecordSecondPrefixStatement, flatAdjacentRecordSecondPayloadStatement,
              flatAdjacentRecordRestoreFirstStatement, flatAdjacentRecordRestoreSecondStatement,
              flatAdjacentRecordFailureStatement, Turing.haltList, Turing.FinTM2.step,
              Turing.TM2.step, Turing.TM2.stepAux] <;>
            try { congr 2; funext stack;
              fin_cases stack <;>
                (first
                  | rfl
                  | simp [Function.update])
            } <;>
          try rfl))


-- @@ L1699-1707 expanded
/-- Internal support shared across GapCVP continuation modules. -/
theorem flatAdjacentRecord_restoreSecond_step (bit : Bool) (input second : List Bool) :
    actualFlatAdjacentRecordSwapMachine.step
        (flatAdjacentRecordConfiguration 5 input [] (bit :: second) []) =
      some (flatAdjacentRecordConfiguration 5 (bit :: input) [] second []) :=
  by
  cases bit <;>
    (first
      | rfl
      |
        (simp [actualFlatAdjacentRecordSwapMachine, flatAdjacentRecordConfiguration,
                flatAdjacentRecordPeek, flatAdjacentRecordPop, flatAdjacentRecordPushBit,
                flatAdjacentRecordPushConstant, flatAdjacentRecordGoto,
                flatAdjacentRecordFirstPrefixStatement, flatAdjacentRecordFirstPayloadStatement,
                flatAdjacentRecordSecondPrefixStatement, flatAdjacentRecordSecondPayloadStatement,
                flatAdjacentRecordRestoreFirstStatement, flatAdjacentRecordRestoreSecondStatement,
                flatAdjacentRecordFailureStatement, Turing.haltList, Turing.FinTM2.step,
                Turing.TM2.step, Turing.TM2.stepAux] <;>
              try { congr 2; funext stack;
                fin_cases stack <;>
                  (first
                    | rfl
                    | simp [Function.update])
              } <;>
            try rfl))


-- @@ L1709-1715 expanded
/-- Internal support shared across GapCVP continuation modules. -/
theorem flatAdjacentRecord_restoreSecond_finish (input : List Bool) :
    actualFlatAdjacentRecordSwapMachine.step (flatAdjacentRecordConfiguration 5 input [] [] []) =
      some (Turing.haltList actualFlatAdjacentRecordSwapMachine input) :=
  by
  (first
    | rfl
    |
      (simp [actualFlatAdjacentRecordSwapMachine, flatAdjacentRecordConfiguration,
              flatAdjacentRecordPeek, flatAdjacentRecordPop, flatAdjacentRecordPushBit,
              flatAdjacentRecordPushConstant, flatAdjacentRecordGoto,
              flatAdjacentRecordFirstPrefixStatement, flatAdjacentRecordFirstPayloadStatement,
              flatAdjacentRecordSecondPrefixStatement, flatAdjacentRecordSecondPayloadStatement,
              flatAdjacentRecordRestoreFirstStatement, flatAdjacentRecordRestoreSecondStatement,
              flatAdjacentRecordFailureStatement, Turing.haltList, Turing.FinTM2.step,
              Turing.TM2.step, Turing.TM2.stepAux] <;>
            try { congr 2; funext stack;
              fin_cases stack <;>
                (first
                  | rfl
                  | simp [Function.update])
            } <;>
          try rfl))


-- @@ L1717-1725 expanded
/-- Internal support shared across GapCVP continuation modules. -/
theorem flatAdjacentRecord_failure_input (bit : Bool) (input first second counter : List Bool) :
    actualFlatAdjacentRecordSwapMachine.step
        (flatAdjacentRecordConfiguration 6 (bit :: input) first second counter) =
      some (flatAdjacentRecordConfiguration 6 input first second counter) :=
  by
  cases bit <;>
    (first
      | rfl
      |
        (simp [actualFlatAdjacentRecordSwapMachine, flatAdjacentRecordConfiguration,
                flatAdjacentRecordPeek, flatAdjacentRecordPop, flatAdjacentRecordPushBit,
                flatAdjacentRecordPushConstant, flatAdjacentRecordGoto,
                flatAdjacentRecordFirstPrefixStatement, flatAdjacentRecordFirstPayloadStatement,
                flatAdjacentRecordSecondPrefixStatement, flatAdjacentRecordSecondPayloadStatement,
                flatAdjacentRecordRestoreFirstStatement, flatAdjacentRecordRestoreSecondStatement,
                flatAdjacentRecordFailureStatement, Turing.haltList, Turing.FinTM2.step,
                Turing.TM2.step, Turing.TM2.stepAux] <;>
              try { congr 2; funext stack;
                fin_cases stack <;>
                  (first
                    | rfl
                    | simp [Function.update])
              } <;>
            try rfl))


-- @@ L1727-1735 expanded
/-- Internal support shared across GapCVP continuation modules. -/
theorem flatAdjacentRecord_failure_first (bit : Bool) (first second counter : List Bool) :
    actualFlatAdjacentRecordSwapMachine.step
        (flatAdjacentRecordConfiguration 6 [] (bit :: first) second counter) =
      some (flatAdjacentRecordConfiguration 6 [] first second counter) :=
  by
  cases bit <;>
    (first
      | rfl
      |
        (simp [actualFlatAdjacentRecordSwapMachine, flatAdjacentRecordConfiguration,
                flatAdjacentRecordPeek, flatAdjacentRecordPop, flatAdjacentRecordPushBit,
                flatAdjacentRecordPushConstant, flatAdjacentRecordGoto,
                flatAdjacentRecordFirstPrefixStatement, flatAdjacentRecordFirstPayloadStatement,
                flatAdjacentRecordSecondPrefixStatement, flatAdjacentRecordSecondPayloadStatement,
                flatAdjacentRecordRestoreFirstStatement, flatAdjacentRecordRestoreSecondStatement,
                flatAdjacentRecordFailureStatement, Turing.haltList, Turing.FinTM2.step,
                Turing.TM2.step, Turing.TM2.stepAux] <;>
              try { congr 2; funext stack;
                fin_cases stack <;>
                  (first
                    | rfl
                    | simp [Function.update])
              } <;>
            try rfl))


-- @@ L1737-1745 expanded
/-- Internal support shared across GapCVP continuation modules. -/
theorem flatAdjacentRecord_failure_second (bit : Bool) (second counter : List Bool) :
    actualFlatAdjacentRecordSwapMachine.step
        (flatAdjacentRecordConfiguration 6 [] [] (bit :: second) counter) =
      some (flatAdjacentRecordConfiguration 6 [] [] second counter) :=
  by
  cases bit <;>
    (first
      | rfl
      |
        (simp [actualFlatAdjacentRecordSwapMachine, flatAdjacentRecordConfiguration,
                flatAdjacentRecordPeek, flatAdjacentRecordPop, flatAdjacentRecordPushBit,
                flatAdjacentRecordPushConstant, flatAdjacentRecordGoto,
                flatAdjacentRecordFirstPrefixStatement, flatAdjacentRecordFirstPayloadStatement,
                flatAdjacentRecordSecondPrefixStatement, flatAdjacentRecordSecondPayloadStatement,
                flatAdjacentRecordRestoreFirstStatement, flatAdjacentRecordRestoreSecondStatement,
                flatAdjacentRecordFailureStatement, Turing.haltList, Turing.FinTM2.step,
                Turing.TM2.step, Turing.TM2.stepAux] <;>
              try { congr 2; funext stack;
                fin_cases stack <;>
                  (first
                    | rfl
                    | simp [Function.update])
              } <;>
            try rfl))


-- @@ L1747-1755 expanded
/-- Internal support shared across GapCVP continuation modules. -/
theorem flatAdjacentRecord_failure_counter (bit : Bool) (counter : List Bool) :
    actualFlatAdjacentRecordSwapMachine.step
        (flatAdjacentRecordConfiguration 6 [] [] [] (bit :: counter)) =
      some (flatAdjacentRecordConfiguration 6 [] [] [] counter) :=
  by
  cases bit <;>
    (first
      | rfl
      |
        (simp [actualFlatAdjacentRecordSwapMachine, flatAdjacentRecordConfiguration,
                flatAdjacentRecordPeek, flatAdjacentRecordPop, flatAdjacentRecordPushBit,
                flatAdjacentRecordPushConstant, flatAdjacentRecordGoto,
                flatAdjacentRecordFirstPrefixStatement, flatAdjacentRecordFirstPayloadStatement,
                flatAdjacentRecordSecondPrefixStatement, flatAdjacentRecordSecondPayloadStatement,
                flatAdjacentRecordRestoreFirstStatement, flatAdjacentRecordRestoreSecondStatement,
                flatAdjacentRecordFailureStatement, Turing.haltList, Turing.FinTM2.step,
                Turing.TM2.step, Turing.TM2.stepAux] <;>
              try { congr 2; funext stack;
                fin_cases stack <;>
                  (first
                    | rfl
                    | simp [Function.update])
              } <;>
            try rfl))


-- @@ L1757-1762 expanded
/-- Internal support shared across GapCVP continuation modules. -/
theorem flatAdjacentRecord_failure_finish :
    actualFlatAdjacentRecordSwapMachine.step (flatAdjacentRecordConfiguration 6 [] [] [] []) =
      some (Turing.haltList actualFlatAdjacentRecordSwapMachine []) :=
  by
  (first
    | rfl
    |
      (simp [actualFlatAdjacentRecordSwapMachine, flatAdjacentRecordConfiguration,
              flatAdjacentRecordPeek, flatAdjacentRecordPop, flatAdjacentRecordPushBit,
              flatAdjacentRecordPushConstant, flatAdjacentRecordGoto,
              flatAdjacentRecordFirstPrefixStatement, flatAdjacentRecordFirstPayloadStatement,
              flatAdjacentRecordSecondPrefixStatement, flatAdjacentRecordSecondPayloadStatement,
              flatAdjacentRecordRestoreFirstStatement, flatAdjacentRecordRestoreSecondStatement,
              flatAdjacentRecordFailureStatement, Turing.haltList, Turing.FinTM2.step,
              Turing.TM2.step, Turing.TM2.stepAux] <;>
            try { congr 2; funext stack;
              fin_cases stack <;>
                (first
                  | rfl
                  | simp [Function.update])
            } <;>
          try rfl))


-- @@ L1764-1764 verbatim
end CNFFlatAdjacentRecordSwapTM


-- @@ L1766-1766 verbatim
namespace CNFFlatAdjacentRecordSwapTotalCert


-- @@ L1768-1768 verbatim
open Turing GapCVP.BinaryEncoding GapCVP.SourceTotalStructuralDecoder

-- @@ L1769-1769 verbatim
open GapCVP.SourceFormulaStructuralDecoder GapCVP.CNFFlatAdjacentRecordSwapTM


-- @@ L1771-1775 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
@[simp] theorem flatAdjacent_readLengthPrefixedWord_missing
    (count : ℕ) :
    readLengthPrefixedWord (List.replicate count true) = none := by
  simp only [readLengthPrefixedWord, readUnaryPrefix_missing]


-- @@ L1777-1785 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
@[simp] theorem flatAdjacent_readLengthPrefixedWord_short
    (payload : List Bool) (extra : ℕ) :
    readLengthPrefixedWord
      (List.replicate (payload.length + extra + 1) true ++
        false :: payload) = none := by
  have hshort : ¬ payload.length + extra + 1 ≤ payload.length := by
    omega
  simp only [readLengthPrefixedWord, readUnaryPrefix_replicate, hshort, ↓reduceIte]


-- @@ L1787-1787 verbatim
end CNFFlatAdjacentRecordSwapTotalCert


-- @@ L1789-1789 verbatim
end GapCVP


-- @@ L1791-1791 verbatim
end
