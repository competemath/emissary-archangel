/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
Whether the gap between ordinary and fresh witnessedness survives the
proof-theoretic alpha bridge.
-/
module

public import LeanPool.MatchingLogic.EntryIII.WitnessedCollapse
import LeanPool.MatchingLogic.EntryIII.Conclusion
import LeanPool.MatchingLogic.EntryIII.MCSAlpha
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.SuccPred
import Mathlib.Tactic.FinCases


-- @@ L21-23 verbatim
/-!
# MatchingLogic.EntryIII.AlphaFreshWitnessed
-/


-- @@ L25-25 verbatim
@[expose] public section


-- @@ L27-27 verbatim
namespace MatchingLogic


-- @@ L29-29 verbatim
open Set


-- @@ L31-31 verbatim
noncomputable section


-- @@ L33-42 verbatim
/-- A witness may be taken after replacing the existential by any pattern
related by the repository's proof-theoretic alpha bridge. -/
def AlphaFreshWitnessed {S : Signature}
    (Gamma : Set (Pattern S Nat)) : Prop :=
  ∀ {x : Nat} {p : Pattern S Nat}, Pattern.ex x p ∈ Gamma →
    ∃ (x' : Nat) (p' : Pattern S Nat) (y : Nat),
      Pattern.AlphaEq (Pattern.ex x p) (Pattern.ex x' p') ∧
      y ∉ p'.allVars ∧
      Pattern.imp (Pattern.ex x' p')
        (Pattern.captureAvoidingSubst x' y p') ∈ Gamma


-- @@ L44-55 verbatim
private theorem provable_empty_of_local_valid {S : Signature}
    {p : Pattern S Nat} (h : LocalCons (∅ : Set (Pattern S Nat)) p) :
    Provable (∅ : Set (Pattern S Nat)) p := by
  obtain ⟨l, hl, hp⟩ := strongLocalCompleteness_nat
    (∅ : Set (Pattern S Nat)) p h
  have hempty : l = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro q hq
    exact (hl q hq).elim
  subst l
  exact Provable.mp (provable_top (∅ : Set (Pattern S Nat)))
    (by simpa [conj] using hp)


-- @@ L57-77 verbatim
private theorem alphaEq_of_denote_eq {S : Signature}
    {p q : Pattern S Nat}
    (hden : ∀ (M : Model S) (rho : Nat → M.carrier),
      M.denote rho p = M.denote rho q)
    (hcomplexity : p.complexity = q.complexity) :
    Pattern.AlphaEq p q := by
  refine ⟨?_, ?_, hcomplexity⟩
  · intro Gamma
    apply (provable_empty_of_local_valid (p := Pattern.imp p q) ?_).weaken_empty
    intro M rho u _hu
    simp only [denote_imp, Set.mem_union, Set.mem_compl_iff]
    by_cases hp : u ∈ M.denote rho p
    · exact Or.inr (by simpa [hden M rho] using hp)
    · exact Or.inl hp
  · intro Gamma
    apply (provable_empty_of_local_valid (p := Pattern.imp q p) ?_).weaken_empty
    intro M rho u _hu
    simp only [denote_imp, Set.mem_union, Set.mem_compl_iff]
    by_cases hq : u ∈ M.denote rho q
    · exact Or.inr (by simpa [hden M rho] using hq)
    · exact Or.inl hq


-- @@ L79-100 verbatim
/-- The candidate from the probe has a proof-theoretic alpha-equivalent,
vacuously quantified representative.  Thus it is not a counterexample to the
alpha-relaxed condition. -/
theorem fvBlocked_has_alpha_fresh_witness :
    ∃ (x' : Nat) (p' : Pattern WitnessCollapseSig Nat) (y : Nat),
      Pattern.AlphaEq
        (.ex 1 (Pattern.and (.var 1) (.var 0))) (.ex x' p') ∧
      y ∉ p'.allVars ∧
      Pattern.imp (.ex x' p')
        (Pattern.captureAvoidingSubst x' y p') ∈ witnessCollapseTheory := by
  let p' : Pattern WitnessCollapseSig Nat :=
    Pattern.and (.var 0) (.var 0)
  refine ⟨1, p', 1, ?_, ?_, ?_⟩
  · apply alphaEq_of_denote_eq
    · intro M rho
      ext u
      simp [p', Pattern.and, Pattern.nt]
    · simp [p', Pattern.complexity]
  · simp [p', Pattern.allVars]
  · change true ∈ witnessCollapseModel.denote witnessCollapseRho _
    simp [p', Pattern.captureAvoidingSubst, Pattern.avoidBinder,
      Pattern.and, Pattern.nt, witnessCollapseRho]


-- @@ L102-104 verbatim
/-! A binary-symbol countermodel.  The small complexity of the distinguished
existential leaves no room for a proof-theoretically equivalent vacuous copy
of its body. -/


-- @@ L106-109 verbatim
/-- The binary operation symbol used by the alpha-equivalence countermodels. -/
inductive AlphaWitnessSym
  | pair
  deriving DecidableEq


-- @@ L111-113 verbatim
instance : Fintype AlphaWitnessSym where
  elems := {AlphaWitnessSym.pair}
  complete s := by cases s; simp


-- @@ L115-118 verbatim
/-- The signature containing the binary alpha-witness operation. -/
abbrev AlphaWitnessSig : Signature where
  Sym := AlphaWitnessSym
  arity _ := 2


-- @@ L120-125 verbatim
/-- Public because `alphaBlocked` is public and unfolds through it: a private
name in the type of a public declaration cannot be reached by the pin list. -/
def pairArgs (p q : Pattern AlphaWitnessSig Nat) :
    Fin 2 → Pattern AlphaWitnessSig Nat
  | ⟨0, _⟩ => p
  | ⟨1, _⟩ => q


-- @@ L127-128 verbatim
@[simp] theorem pairArgs_zero (p q : Pattern AlphaWitnessSig Nat) :
    pairArgs p q 0 = p := rfl


-- @@ L130-131 verbatim
@[simp] theorem pairArgs_one (p q : Pattern AlphaWitnessSig Nat) :
    pairArgs p q 1 = q := rfl


-- @@ L133-135 verbatim
private def boolPair (p q : Bool) : Fin 2 → Bool
  | ⟨0, _⟩ => p
  | ⟨1, _⟩ => q


-- @@ L137-137 verbatim
@[simp] private theorem boolPair_zero (p q : Bool) : boolPair p q 0 = p := rfl

-- @@ L138-138 verbatim
@[simp] private theorem boolPair_one (p q : Bool) : boolPair p q 1 = q := rfl


-- @@ L140-144 verbatim
/-- The Boolean model used to witness the alpha-renaming obstruction. -/
abbrev alphaWitnessModel : Model AlphaWitnessSig where
  carrier := Bool
  nonempty := ⟨false⟩
  interp _ a := if a 0 = true ∧ a 1 = true then {true} else ∅


-- @@ L146-147 verbatim
/-- The valuation that maps exactly variable zero to `true`. -/
def alphaWitnessRho : Nat → alphaWitnessModel.carrier := fun n => n = 0


-- @@ L149-151 verbatim
/-- The complete pointed theory of `alphaWitnessModel` at `true`. -/
def alphaWitnessTheory : Set (Pattern AlphaWitnessSig Nat) :=
  pointedTheory alphaWitnessModel alphaWitnessRho true


-- @@ L153-158 verbatim
private theorem alphaWitnessRho_surjective :
    Function.Surjective alphaWitnessRho := by
  intro b
  cases b with
  | false => exact ⟨1, by simp [alphaWitnessRho]⟩
  | true => exact ⟨0, by simp [alphaWitnessRho]⟩


-- @@ L160-161 verbatim
theorem alphaWitnessTheory_isMCS : IsMCS alphaWitnessTheory := by
  exact pointedTheory_isMCS alphaWitnessModel alphaWitnessRho true


-- @@ L163-165 verbatim
theorem alphaWitnessTheory_witnessed : Witnessed alphaWitnessTheory := by
  exact pointedTheory_witnessed alphaWitnessModel alphaWitnessRho true
    alphaWitnessRho_surjective


-- @@ L167-169 verbatim
/-- The existential pattern whose binder cannot be renamed to variable zero. -/
def alphaBlocked : Pattern AlphaWitnessSig Nat :=
  .ex 1 (.app .pair (pairArgs (.var 1) (.var 0)))


-- @@ L171-179 verbatim
theorem alphaBlocked_mem : alphaBlocked ∈ alphaWitnessTheory := by
  change true ∈ alphaWitnessModel.denote alphaWitnessRho alphaBlocked
  simp only [alphaWitnessModel, Fin.isValue, alphaBlocked, denote_ex,
    denote_app, Model.app, Fin.forall_fin_two, pairArgs_zero, denote_var,
    Function.update_self, Set.mem_singleton_iff, pairArgs_one, ne_eq,
    zero_ne_one, not_false_eq_true, Function.update_of_ne, alphaWitnessRho,
    decide_true, Set.mem_ite_empty_right, Set.mem_iUnion, Set.mem_ofPred_eq,
    and_true, Bool.exists_bool, and_self]
  exact Or.inr ⟨fun _ => true, by simp⟩


-- @@ L181-188 verbatim
private theorem alphaWitness_complexity_pos
    (p : Pattern AlphaWitnessSig Nat) : 0 < p.complexity := by
  cases p with
  | var => simp [Pattern.complexity]
  | bot => simp [Pattern.complexity]
  | app sigma args => simp [Pattern.complexity]
  | imp p q => simp [Pattern.complexity]
  | ex x p => simp [Pattern.complexity]


-- @@ L190-208 verbatim
private theorem alphaWitness_complexity_one
    (p : Pattern AlphaWitnessSig Nat) (h : p.complexity = 1) :
    (∃ z, p = .var z) ∨ p = .bot := by
  cases p with
  | var z => exact Or.inl ⟨z, rfl⟩
  | bot => exact Or.inr rfl
  | app sigma args =>
      have hp := alphaWitness_complexity_pos (args 0)
      simp [Pattern.complexity] at h
      omega
  | imp p q =>
      have hp := alphaWitness_complexity_pos p
      have hq := alphaWitness_complexity_pos q
      simp [Pattern.complexity] at h
      omega
  | ex x p =>
      have hp := alphaWitness_complexity_pos p
      simp [Pattern.complexity] at h
      omega


-- @@ L210-231 verbatim
private theorem alphaWitness_complexity_two
    (p : Pattern AlphaWitnessSig Nat) (h : p.complexity = 2) :
    ∃ z q, p = .ex z q ∧ ((∃ a, q = .var a) ∨ q = .bot) := by
  cases p with
  | var z => simp [Pattern.complexity] at h
  | bot => simp [Pattern.complexity] at h
  | app sigma args =>
      have hp := alphaWitness_complexity_pos (args 0)
      have hq := alphaWitness_complexity_pos (args 1)
      cases sigma
      rw [Pattern.complexity, Fin.sum_univ_two] at h
      omega
  | imp p q =>
      have hp := alphaWitness_complexity_pos p
      have hq := alphaWitness_complexity_pos q
      simp [Pattern.complexity] at h
      omega
  | ex z q =>
      have hq : q.complexity = 1 := by
        simp [Pattern.complexity] at h
        omega
      exact ⟨z, q, rfl, alphaWitness_complexity_one q hq⟩


-- @@ L233-277 verbatim
private theorem alphaWitness_body_shape
    (p : Pattern AlphaWitnessSig Nat) (h : p.complexity = 3) :
    (∃ a b, p = .app .pair (pairArgs a b) ∧
      ((∃ z, a = .var z) ∨ a = .bot) ∧
      ((∃ z, b = .var z) ∨ b = .bot)) ∨
    (∃ a b, p = .imp a b ∧
      ((∃ z, a = .var z) ∨ a = .bot) ∧
      ((∃ z, b = .var z) ∨ b = .bot)) ∨
    (∃ z w a, p = .ex z (.ex w a) ∧
      ((∃ v, a = .var v) ∨ a = .bot)) := by
  cases p with
  | var z => simp [Pattern.complexity] at h
  | bot => simp [Pattern.complexity] at h
  | app sigma args =>
      cases sigma
      have hsum : (args 0).complexity + (args 1).complexity = 2 := by
        rw [Pattern.complexity, Fin.sum_univ_two] at h
        omega
      have hp := alphaWitness_complexity_pos (args 0)
      have hq := alphaWitness_complexity_pos (args 1)
      have hp1 : (args 0).complexity = 1 := by omega
      have hq1 : (args 1).complexity = 1 := by omega
      refine Or.inl ⟨args 0, args 1, ?_,
        alphaWitness_complexity_one _ hp1,
        alphaWitness_complexity_one _ hq1⟩
      congr
      funext i
      fin_cases i <;> rfl
  | imp a b =>
      have hsum : a.complexity + b.complexity = 2 := by
        simp [Pattern.complexity] at h
        omega
      have ha := alphaWitness_complexity_pos a
      have hb := alphaWitness_complexity_pos b
      have ha1 : a.complexity = 1 := by omega
      have hb1 : b.complexity = 1 := by omega
      exact Or.inr (Or.inl ⟨a, b, rfl,
        alphaWitness_complexity_one _ ha1,
        alphaWitness_complexity_one _ hb1⟩)
  | ex z q =>
      have hq : q.complexity = 2 := by
        simp [Pattern.complexity] at h
        omega
      obtain ⟨w, a, rfl, ha⟩ := alphaWitness_complexity_two q hq
      exact Or.inr (Or.inr ⟨z, w, a, rfl, ha⟩)


-- @@ L279-283 verbatim
/-- The singleton model with an empty interpretation. -/
abbrev alphaUnitEmptyModel : Model AlphaWitnessSig where
  carrier := Unit
  nonempty := ⟨()⟩
  interp _ _ := ∅


-- @@ L285-289 verbatim
/-- The singleton model with a total interpretation. -/
abbrev alphaUnitFullModel : Model AlphaWitnessSig where
  carrier := Unit
  nonempty := ⟨()⟩
  interp _ _ := {()}


-- @@ L291-292 verbatim
/-- The unique valuation into the singleton carrier. -/
def alphaUnitRho : Nat → alphaUnitEmptyModel.carrier := fun _ => ()


-- @@ L294-298 verbatim
/-- The Boolean model selecting the `(true, false)` input pair. -/
abbrev alphaFirstSelectorModel : Model AlphaWitnessSig where
  carrier := Bool
  nonempty := ⟨false⟩
  interp _ a := if a 0 = true ∧ a 1 = false then {true} else ∅


-- @@ L300-304 verbatim
/-- The Boolean model selecting the `(false, true)` input pair. -/
abbrev alphaCornerSelectorModel : Model AlphaWitnessSig where
  carrier := Bool
  nonempty := ⟨false⟩
  interp _ a := if a 0 = false ∧ a 1 = true then {true} else ∅


-- @@ L306-322 verbatim
private theorem alphaBlocked_alphaEq_app_no_bot {x' : Nat}
    {a b : Pattern AlphaWitnessSig Nat}
    (halpha : Pattern.AlphaEq alphaBlocked
      (.ex x' (.app .pair (pairArgs a b)))) : a ≠ .bot ∧ b ≠ .bot := by
  constructor
  · intro ha
    subst a
    have hden := halpha.denote_eq
      (M := alphaUnitFullModel) (rho := alphaUnitRho)
    simp [alphaBlocked, alphaUnitFullModel, Model.app, pairArgs,
      alphaUnitRho] at hden
  · intro hb
    subst b
    have hden := halpha.denote_eq
      (M := alphaUnitFullModel) (rho := alphaUnitRho)
    simp [alphaBlocked, alphaUnitFullModel, Model.app, pairArgs,
      alphaUnitRho] at hden


-- @@ L324-363 verbatim
private theorem alphaBlocked_alphaEq_app_variables {x' a b : Nat}
    (halpha : Pattern.AlphaEq alphaBlocked
      (.ex x' (.app .pair (pairArgs (.var a) (.var b))))) :
    a = x' ∧ b = 0 := by
  have hax : a = x' := by
    by_contra hax
    have hden := halpha.denote_eq
      (M := alphaFirstSelectorModel) (rho := fun _ => false)
    have hleft : true ∈ alphaFirstSelectorModel.denote
        (fun _ => false) alphaBlocked := by
      simp only [alphaFirstSelectorModel, Fin.isValue, alphaBlocked,
        denote_ex, denote_app, Model.app, pairArgs, Fin.forall_fin_two,
        denote_var, Function.update_self, Set.mem_singleton_iff, ne_eq,
        zero_ne_one, not_false_eq_true, Function.update_of_ne,
        Set.mem_ite_empty_right, Set.mem_iUnion, Set.mem_ofPred_eq,
        and_true, Bool.exists_bool, and_self]
      exact Or.inr ⟨boolPair true false, by simp [boolPair]⟩
    rw [hden] at hleft
    simp [alphaFirstSelectorModel, Model.app, pairArgs, hax] at hleft
    aesop
  refine ⟨hax, ?_⟩
  subst a
  by_contra hb0
  have hden := halpha.denote_eq
    (M := alphaCornerSelectorModel) (rho := fun n => n = 0)
  have hleft : true ∈ alphaCornerSelectorModel.denote
      (fun n => n = 0) alphaBlocked := by
    simp only [alphaCornerSelectorModel, Fin.isValue, alphaBlocked,
      denote_ex, denote_app, Model.app, pairArgs, Fin.forall_fin_two,
      denote_var, Function.update_self, Set.mem_singleton_iff, ne_eq,
      zero_ne_one, not_false_eq_true, Function.update_of_ne, decide_true,
      Set.mem_ite_empty_right, Set.mem_iUnion, Set.mem_ofPred_eq, and_true,
      Bool.exists_bool, and_self]
    exact Or.inl ⟨boolPair false true, by simp [boolPair]⟩
  rw [hden] at hleft
  by_cases hbx : b = x'
  · simp [alphaCornerSelectorModel, Model.app, pairArgs, hbx] at hleft
    aesop
  · simp [alphaCornerSelectorModel, Model.app, pairArgs, hb0, hbx] at hleft
    aesop


-- @@ L365-411 verbatim
private theorem alphaBlocked_not_alphaEq_imp {x' : Nat}
    {a b : Pattern AlphaWitnessSig Nat}
    (ha : (∃ z, a = .var z) ∨ a = .bot)
    (hb : (∃ z, b = .var z) ∨ b = .bot)
    (halpha : Pattern.AlphaEq alphaBlocked (.ex x' (.imp a b))) : False := by
  rcases ha with ⟨a, rfl⟩ | rfl <;>
    rcases hb with ⟨b, rfl⟩ | rfl
  · have hden := halpha.denote_eq
      (M := alphaUnitEmptyModel) (rho := alphaUnitRho)
    simp only [alphaUnitEmptyModel, alphaBlocked, denote_ex,
      Function.update_eq_self, denote_app, Model.app, pairArgs,
      Fin.forall_fin_two, denote_var, alphaUnitRho, Fin.isValue,
      Set.mem_singleton_iff, and_self, Set.mem_empty_iff_false, and_false,
      exists_const, Set.ofPred_false, Set.iUnion_empty, denote_imp,
      Set.union_singleton] at hden
    have hmem := Set.ext_iff.mp hden ()
    simp at hmem
  · have hden := halpha.denote_eq
      (M := alphaUnitFullModel) (rho := alphaUnitRho)
    simp only [alphaUnitFullModel, alphaBlocked, denote_ex,
      Function.update_eq_self, denote_app, Model.app, pairArgs,
      Fin.forall_fin_two, denote_var, alphaUnitRho, Fin.isValue,
      Set.mem_singleton_iff, and_self, exists_const, Set.ofPred_true,
      denote_imp, denote_bot, Set.union_empty] at hden
    have hmem := Set.ext_iff.mp hden ()
    simp at hmem
  · have hden := halpha.denote_eq
      (M := alphaUnitEmptyModel) (rho := alphaUnitRho)
    simp only [alphaUnitEmptyModel, alphaBlocked, denote_ex,
      Function.update_eq_self, denote_app, Model.app, pairArgs,
      Fin.forall_fin_two, denote_var, alphaUnitRho, Fin.isValue,
      Set.mem_singleton_iff, and_self, Set.mem_empty_iff_false, and_false,
      exists_const, Set.ofPred_false, Set.iUnion_empty, denote_imp,
      denote_bot, Set.compl_empty, Set.union_singleton, Set.mem_univ,
      Set.insert_eq_of_mem] at hden
    have hmem := Set.ext_iff.mp hden ()
    simp at hmem
  · have hden := halpha.denote_eq
      (M := alphaUnitEmptyModel) (rho := alphaUnitRho)
    simp only [alphaUnitEmptyModel, alphaBlocked, denote_ex,
      Function.update_eq_self, denote_app, Model.app, pairArgs,
      Fin.forall_fin_two, denote_var, alphaUnitRho, Fin.isValue,
      Set.mem_singleton_iff, and_self, Set.mem_empty_iff_false, and_false,
      exists_const, Set.ofPred_false, Set.iUnion_empty, denote_imp,
      denote_bot, Set.compl_empty, Set.union_empty] at hden
    have hmem := Set.ext_iff.mp hden ()
    simp at hmem


-- @@ L413-431 verbatim
private theorem alphaBlocked_not_alphaEq_nested_ex {x' z w : Nat}
    {a : Pattern AlphaWitnessSig Nat}
    (ha : (∃ v, a = .var v) ∨ a = .bot)
    (halpha : Pattern.AlphaEq alphaBlocked (.ex x' (.ex z (.ex w a)))) : False := by
  rcases ha with ⟨a, rfl⟩ | rfl
  · have hden := halpha.denote_eq
      (M := alphaUnitEmptyModel) (rho := alphaUnitRho)
    simp only [alphaUnitEmptyModel, alphaBlocked, denote_ex,
      Function.update_eq_self, denote_app, Model.app, pairArgs,
      Fin.forall_fin_two, denote_var, alphaUnitRho, Fin.isValue,
      Set.mem_singleton_iff, and_self, Set.mem_empty_iff_false, and_false,
      exists_const, Set.ofPred_false, Set.iUnion_empty,
      Set.iUnion_singleton_eq_range, Set.range_id'] at hden
    have hmem := Set.ext_iff.mp hden ()
    simp at hmem
  · have hden := halpha.denote_eq
      (M := alphaUnitFullModel) (rho := alphaUnitRho)
    simp [alphaBlocked, alphaUnitFullModel, Model.app, pairArgs,
      alphaUnitRho] at hden


-- @@ L433-453 verbatim
private theorem alphaBlocked_alphaEq_body_shape {x' : Nat}
    {p' : Pattern AlphaWitnessSig Nat}
    (halpha : Pattern.AlphaEq alphaBlocked (.ex x' p')) :
    ∃ a b, p' = .app .pair (pairArgs (.var a) (.var b)) ∧
      a = x' ∧ b = 0 := by
  have hpComplexity : p'.complexity = 3 := by
    have hc := halpha.complexity_eq
    simp [alphaBlocked, Pattern.complexity, Fin.sum_univ_two, pairArgs] at hc
    omega
  rcases alphaWitness_body_shape p' hpComplexity with
      ⟨a, b, rfl, ha, hb⟩ | ⟨a, b, rfl, ha, hb⟩ |
        ⟨z, w, a, rfl, ha⟩
  · obtain ⟨hna, hnb⟩ := alphaBlocked_alphaEq_app_no_bot halpha
    rcases ha with ⟨a, rfl⟩ | rfl
    · rcases hb with ⟨b, rfl⟩ | rfl
      · obtain ⟨hax, hb0⟩ := alphaBlocked_alphaEq_app_variables halpha
        exact ⟨a, b, rfl, hax, hb0⟩
      · exact (hnb rfl).elim
    · exact (hna rfl).elim
  · exact (alphaBlocked_not_alphaEq_imp ha hb halpha).elim
  · exact (alphaBlocked_not_alphaEq_nested_ex ha halpha).elim


-- @@ L455-489 verbatim
/-- No proof-theoretic alpha variant of `alphaBlocked` has a fresh usable
witness in the pointed binary model. -/
theorem alphaWitnessTheory_not_alphaFreshWitnessed :
    ¬ AlphaFreshWitnessed alphaWitnessTheory := by
  intro hFresh
  obtain ⟨x', p', y, halpha, hyFresh, hyImp⟩ := hFresh alphaBlocked_mem
  obtain ⟨a, b, hp', hax, hb⟩ := alphaBlocked_alphaEq_body_shape halpha
  subst a
  subst b
  subst p'
  have hy0 : y ≠ 0 := by
    intro hy
    subst y
    apply hyFresh
    simp [Pattern.allVars, pairArgs]
  have he' : Pattern.ex x'
      (.app AlphaWitnessSym.pair (pairArgs (.var x') (.var 0))) ∈
        alphaWitnessTheory :=
    (alphaWitnessTheory_isMCS.alphaEq_mem_iff halpha).mp alphaBlocked_mem
  change true ∈ alphaWitnessModel.denote alphaWitnessRho
    (.imp (.ex x' (.app .pair (pairArgs (.var x') (.var 0))))
      (Pattern.captureAvoidingSubst x' y
        (.app .pair (pairArgs (.var x') (.var 0))))) at hyImp
  simp only [denote_imp, Set.mem_union, Set.mem_compl_iff] at hyImp
  rcases hyImp with hnot | hinstance
  · exact hnot he'
  · by_cases hx0 : x' = 0
    · subst x'
      simp [Pattern.captureAvoidingSubst, Pattern.avoidBinder, substVar,
        alphaWitnessModel, Model.app, pairArgs, alphaWitnessRho, hy0] at hinstance
      aesop
    · simp [Pattern.captureAvoidingSubst, Pattern.avoidBinder, substVar,
        alphaWitnessModel, Model.app, pairArgs, alphaWitnessRho, hy0,
        Ne.symm hx0] at hinstance
      aesop


-- @@ L491-497 verbatim
/-- Concrete MCS counterexample to the alpha-relaxed collapse. -/
theorem witnessed_alphaFreshWitnessed_of_isMCS_counterexample :
    ∃ Gamma : Set (Pattern AlphaWitnessSig Nat),
      IsMCS Gamma ∧ Witnessed Gamma ∧ ¬ AlphaFreshWitnessed Gamma := by
  exact ⟨alphaWitnessTheory, alphaWitnessTheory_isMCS,
    alphaWitnessTheory_witnessed,
    alphaWitnessTheory_not_alphaFreshWitnessed⟩


-- @@ L499-506 verbatim
/-- The proposed implication is false, even with the broad proof-theoretic
definition of `Pattern.AlphaEq`. -/
theorem witnessed_alphaFreshWitnessed_of_isMCS_refuted :
    ¬ (∀ {Gamma : Set (Pattern AlphaWitnessSig Nat)},
      IsMCS Gamma → Witnessed Gamma → AlphaFreshWitnessed Gamma) := by
  intro hCollapse
  exact alphaWitnessTheory_not_alphaFreshWitnessed
    (hCollapse alphaWitnessTheory_isMCS alphaWitnessTheory_witnessed)


-- @@ L508-508 verbatim
end


-- @@ L510-510 verbatim
end MatchingLogic
