/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.AltLadder
import DescriptiveComplexity.Problems.Machine.Membership


-- @@ L9-38 verbatim
/-!
# The ladder, written with the relations a second-order block guesses

A second-order block cannot guess a *function* `A → Config A`; it guesses the
three relations of `DescriptiveComplexity.tmGuessBlock` – `Q t q`, “the state at
time `t` is `q`”, `H t p`, “the head is on `p`”, and `T t p a`, “the cell `p`
holds `a`”. `DescriptiveComplexity.Problems.Machine.Walk` already relates the
two forms *existentially*
(`DescriptiveComplexity.TMData.exists_relWalk_iff_exists_walk`); the ladder
needs more, because its rounds alternate: a universal round quantifies over
*all* assignments and must be able to assume that the one it is given is
functional.

So this file is the pointwise dictionary. `DescriptiveComplexity.Graphs ρ w`
says the assignment `ρ` is the graph of the walk `w`; every assignment that is
functional is a graph (`DescriptiveComplexity.exists_graphs`) and every walk has
one (`DescriptiveComplexity.graphOf`), and each condition the game puts on a
walk gets a relational twin that agrees with it along the dictionary. The
transfer of a whole quantifier is
`DescriptiveComplexity.bareQ_transfer`, and the result is
`DescriptiveComplexity.ATMData.altLadder_iff_runAltLadder`.

One condition is not a transcription: “the walk stands still because it is
*stuck*” quantifies over the successor configurations, which a first-order
formula cannot do. It does not have to:
`DescriptiveComplexity.TMData.exists_step_iff_appTr` says a successor exists
exactly when an *applicable transition* does – the successor configuration can
be assembled from the transition's own data – and that is a first-order
condition on the transition table.
-/


-- @@ L40-40 verbatim
namespace DescriptiveComplexity


-- @@ L42-42 verbatim
open FirstOrder


-- @@ L44-44 verbatim
open Language Structure


-- @@ L46-46 verbatim
/-! ### Applicable transitions -/


-- @@ L48-48 verbatim
namespace TMData


-- @@ L50-50 verbatim
variable {A : Type} (M : TMData A)


-- @@ L52-60 verbatim
/-- **A transition applies to the configuration `c`**: it fires on the state
and the symbol under the head, it has a target state and a symbol to write, and
the head has somewhere to move. Unlike “`c` has a successor” this quantifies
only over elements of the universe. -/
def AppTr (c : Config A) : Prop :=
  ∃ τ, M.Tr τ ∧ M.Src τ c.state ∧ M.Read τ (c.tape c.head) ∧ (∃ q, M.Dst τ q) ∧
    (∃ a, M.Write τ a) ∧
    ((M.Right τ ∧ ∃ p, SuccPos M.Le M.Posn c.head p) ∨
      (¬M.Right τ ∧ ∃ p, SuccPos M.Le M.Posn p c.head))


-- @@ L62-62 verbatim
variable {M}


-- @@ L64-81 verbatim
/-- **Having a successor is having an applicable transition**: the successor
configuration is assembled from the transition, writing under the head and
leaving every other cell alone. -/
theorem exists_step_iff_appTr {c : Config A} : (∃ c', M.Step c c') ↔ M.AppTr c := by
  classical
  constructor
  · rintro ⟨c', τ, hτ, hsrc, hread, hdst, hwrite, -, hmove⟩
    exact ⟨τ, hτ, hsrc, hread, ⟨_, hdst⟩, ⟨_, hwrite⟩,
      hmove.imp (fun h => ⟨h.1, _, h.2⟩) fun h => ⟨h.1, _, h.2⟩⟩
  · rintro ⟨τ, hτ, hsrc, hread, ⟨q, hq⟩, ⟨a, ha⟩, hmove⟩
    obtain ⟨p, hp⟩ : ∃ p, (M.Right τ ∧ SuccPos M.Le M.Posn c.head p) ∨
        (¬M.Right τ ∧ SuccPos M.Le M.Posn p c.head) := by
      rcases hmove with ⟨hr, p, hp⟩ | ⟨hr, p, hp⟩
      · exact ⟨p, Or.inl ⟨hr, hp⟩⟩
      · exact ⟨p, Or.inr ⟨hr, hp⟩⟩
    refine ⟨⟨q, p, Function.update c.tape c.head a⟩, τ, hτ, hsrc, hread, hq, ?_, ?_, hp⟩
    · simpa using ha
    · exact fun r hr => Function.update_of_ne hr _ _


-- @@ L83-83 verbatim
end TMData


-- @@ L85-85 verbatim
/-! ### A guessed run, and the walk it is the graph of -/


-- @@ L87-87 verbatim
section Run


-- @@ L89-89 verbatim
variable {A : Type}


-- @@ L91-92 verbatim
/-- The state relation of a guessed run: at time `t` the state is `q`. -/
def runQ (ρ : tmGuessBlock.Assignment A) (t q : A) : Prop := ρ .state ![t, q]


-- @@ L94-95 verbatim
/-- The head relation of a guessed run: at time `t` the head is on `p`. -/
def runH (ρ : tmGuessBlock.Assignment A) (t p : A) : Prop := ρ .head ![t, p]


-- @@ L97-98 verbatim
/-- The tape relation of a guessed run: at time `t` the cell `p` holds `a`. -/
def runT (ρ : tmGuessBlock.Assignment A) (t p a : A) : Prop := ρ .tape ![t, p, a]


-- @@ L100-105 verbatim
/-- **The guess is functional**, the six clauses that make it read as one
configuration per time. -/
def RunFun (ρ : tmGuessBlock.Assignment A) : Prop :=
  (∀ t, ∃ q, runQ ρ t q) ∧ (∀ t q q', runQ ρ t q → runQ ρ t q' → q = q') ∧
    (∀ t, ∃ p, runH ρ t p) ∧ (∀ t p p', runH ρ t p → runH ρ t p' → p = p') ∧
      (∀ t p, ∃ a, runT ρ t p a) ∧ ∀ t p a a', runT ρ t p a → runT ρ t p a' → a = a'


-- @@ L107-110 verbatim
/-- **The guess is the graph of the walk `w`.** -/
def Graphs (ρ : tmGuessBlock.Assignment A) (w : A → Config A) : Prop :=
  (∀ t q, runQ ρ t q ↔ q = (w t).state) ∧ (∀ t p, runH ρ t p ↔ p = (w t).head) ∧
    ∀ t p a, runT ρ t p a ↔ a = (w t).tape p


-- @@ L112-117 verbatim
/-- The graph of a walk, as an assignment of the guessing block. -/
def graphOf (w : A → Config A) : tmGuessBlock.Assignment A := fun i =>
  match i with
  | .state => fun v : Fin 2 → A => v 1 = (w (v 0)).state
  | .head => fun v : Fin 2 → A => v 1 = (w (v 0)).head
  | .tape => fun v : Fin 3 → A => v 2 = (w (v 0)).tape (v 1)


-- @@ L119-121 verbatim
@[simp] theorem graphs_graphOf (w : A → Config A) : Graphs (graphOf w) w := by
  refine ⟨fun t q => ?_, fun t p => ?_, fun t p a => ?_⟩ <;>
    · simp [runQ, runH, runT, graphOf]


-- @@ L123-124 verbatim
/-- Two values with the same graph are equal. -/
theorem eq_of_iff_eq {α : Type} {x y : α} (h : ∀ a, a = x ↔ a = y) : x = y := (h x).mp rfl


-- @@ L126-126 verbatim
variable {ρ : tmGuessBlock.Assignment A} {w : A → Config A}


-- @@ L128-135 verbatim
/-- A graph is functional. -/
theorem RunFun.of_graphs (h : Graphs ρ w) : RunFun ρ := by
  refine ⟨fun t => ⟨_, (h.1 t _).mpr rfl⟩, fun t q q' hq hq' => ?_,
    fun t => ⟨_, (h.2.1 t _).mpr rfl⟩, fun t p p' hp hp' => ?_,
    fun t p => ⟨_, (h.2.2 t p _).mpr rfl⟩, fun t p a a' ha ha' => ?_⟩
  · rw [(h.1 t q).mp hq, (h.1 t q').mp hq']
  · rw [(h.2.1 t p).mp hp, (h.2.1 t p').mp hp']
  · rw [(h.2.2 t p a).mp ha, (h.2.2 t p a').mp ha']


-- @@ L137-147 verbatim
/-- **A functional guess is a graph**: the configuration at each time is the
one its three relations single out. -/
theorem exists_graphs (h : RunFun ρ) : ∃ w, Graphs ρ w := by
  classical
  refine ⟨fun t => ⟨(h.1 t).choose, (h.2.2.1 t).choose, fun p => (h.2.2.2.2.1 t p).choose⟩,
    fun t q => ?_, fun t p => ?_, fun t p a => ?_⟩
  · exact ⟨fun hq => h.2.1 t _ _ hq (h.1 t).choose_spec, fun hq => hq ▸ (h.1 t).choose_spec⟩
  · exact ⟨fun hp => h.2.2.2.1 t _ _ hp (h.2.2.1 t).choose_spec,
      fun hp => hp ▸ (h.2.2.1 t).choose_spec⟩
  · exact ⟨fun ha => h.2.2.2.2.2 t p _ _ ha (h.2.2.2.2.1 t p).choose_spec,
      fun ha => ha ▸ (h.2.2.2.2.1 t p).choose_spec⟩


-- @@ L149-149 verbatim
end Run


-- @@ L151-151 verbatim
/-! ### Transferring a quantifier -/


-- @@ L153-175 verbatim
/-- **A quantifier over walks is a quantifier over functional guesses.** The
guard picks up the functionality clauses; everything else is read through the
dictionary. -/
theorem bareQ_transfer {A : Type} (pol : Bool) {Cw Pw : (A → Config A) → Prop}
    {Cρ Pρ : tmGuessBlock.Assignment A → Prop}
    (hC : ∀ ρ w, Graphs ρ w → (Cρ ρ ↔ Cw w)) (hP : ∀ ρ w, Graphs ρ w → (Pρ ρ ↔ Pw w)) :
    bareQ pol Cw Pw ↔ bareQ pol (fun ρ => RunFun ρ ∧ Cρ ρ) Pρ := by
  cases pol
  · constructor
    · intro h ρ hρ
      obtain ⟨w, hg⟩ := exists_graphs hρ.1
      exact (hP ρ w hg).mpr (h w ((hC ρ w hg).mp hρ.2))
    · intro h w hw
      exact (hP _ w (graphs_graphOf w)).mp
        (h (graphOf w) ⟨RunFun.of_graphs (graphs_graphOf w),
          (hC _ w (graphs_graphOf w)).mpr hw⟩)
  · constructor
    · rintro ⟨w, hCw, hPw⟩
      exact ⟨graphOf w, ⟨RunFun.of_graphs (graphs_graphOf w),
        (hC _ w (graphs_graphOf w)).mpr hCw⟩, (hP _ w (graphs_graphOf w)).mpr hPw⟩
    · rintro ⟨ρ, ⟨hρ, hCρ⟩, hPρ⟩
      obtain ⟨w, hg⟩ := exists_graphs hρ
      exact ⟨w, (hC ρ w hg).mp hCρ, (hP ρ w hg).mp hPρ⟩


-- @@ L177-177 verbatim
/-! ### The conditions of the game, relationally -/


-- @@ L179-179 verbatim
namespace ATMData


-- @@ L181-181 verbatim
variable {A : Type} (M : ATMData A) (ρ ρ' : tmGuessBlock.Assignment A)


-- @@ L183-184 verbatim
/-- The state at time `t` is accepting. -/
def RunAcc (t : A) : Prop := ∀ q, runQ ρ t q → M.Acc q


-- @@ L186-187 verbatim
/-- The state at time `t` is in block `j`. -/
def RunBlk (j : ℕ) (t : A) : Prop := ∀ q, runQ ρ t q → M.Blk j q


-- @@ L189-190 verbatim
/-- The state at time `t` is in a block below `i`. -/
def RunBlkLt (i : ℕ) (t : A) : Prop := ∀ q, runQ ρ t q → M.BlkLt i q


-- @@ L192-195 verbatim
/-- The configuration at time `t` is initial. -/
def RunInit (t : A) : Prop :=
  (∀ q, runQ ρ t q → M.Start q) ∧ (∀ p, runH ρ t p → MinPos M.Le M.Posn p) ∧
    ∀ p a, runT ρ t p a → M.InitTape p a


-- @@ L197-202 verbatim
/-- Some transition applies to the configuration at time `t`. -/
def RunAppTr (t : A) : Prop :=
  ∃ τ, M.Tr τ ∧ (∀ q, runQ ρ t q → M.Src τ q) ∧
    (∀ p a, runH ρ t p → runT ρ t p a → M.Read τ a) ∧ (∃ q, M.Dst τ q) ∧ (∃ a, M.Write τ a) ∧
    ((M.Right τ ∧ ∀ p, runH ρ t p → ∃ p', SuccPos M.Le M.Posn p p') ∨
      (¬M.Right τ ∧ ∀ p, runH ρ t p → ∃ p', SuccPos M.Le M.Posn p' p))


-- @@ L204-207 verbatim
/-- The configuration at time `t'` of `ρ'` is the one at time `t` of `ρ`. -/
def RunSame (t t' : A) : Prop :=
  (∀ q, runQ ρ' t' q ↔ runQ ρ t q) ∧ (∀ p, runH ρ' t' p ↔ runH ρ t p) ∧
    ∀ p a, runT ρ' t' p a ↔ runT ρ t p a


-- @@ L209-209 verbatim
variable {ρ ρ'}


-- @@ L211-214 verbatim
/-- The step clause, relationally, is
`DescriptiveComplexity.TMData.RelStep` of the three relations. -/
abbrev RunStep (t t' : A) : Prop :=
  TMData.RelStep M.toTMData (runQ ρ) (runH ρ) (runT ρ) t t'


-- @@ L216-216 verbatim
variable (ρ)


-- @@ L218-221 verbatim
/-- The blocks of a guessed run never decrease. -/
def RunBlkMono : Prop :=
  ∀ p q, SuccPos M.Le M.Posn p q → ∀ x y, runQ ρ p x → runQ ρ q y →
    ∀ j j', M.Blk j x → M.Blk j' y → j ≤ j'


-- @@ L223-228 verbatim
/-- A guessed run legal below block `i`. -/
def RunLegalBelow (i : ℕ) : Prop :=
  (∀ p, MinPos M.Le M.Posn p → M.RunInit ρ p) ∧ M.RunBlkMono ρ ∧
    ∀ p q, SuccPos M.Le M.Posn p q → M.RunBlkLt ρ i p →
      (M.RunStep (ρ := ρ) p q ∧ ¬M.RunAcc ρ p) ∨
        (RunSame ρ ρ p q ∧ (M.RunAcc ρ p ∨ ¬M.RunAppTr ρ p))


-- @@ L230-231 verbatim
/-- The guessed run accepts: its state at the highest time is accepting. -/
def RunAccAt : Prop := ∀ p, MaxPos M.Le M.Posn p → M.RunAcc ρ p


-- @@ L233-233 verbatim
variable (ρ')


-- @@ L235-238 verbatim
/-- The guessed run `ρ'` reproduces what `ρ` committed below block `i`. -/
def RunAgreeBelow (i : ℕ) : Prop :=
  (∀ t, M.Posn t → M.RunBlkLt ρ i t → RunSame ρ ρ' t t) ∧
    ∀ t t', SuccPos M.Le M.Posn t t' → M.RunBlkLt ρ i t → RunSame ρ ρ' t' t'


-- @@ L240-242 verbatim
/-- The condition round `i` puts on its guess. -/
def RunRoundCond (i : ℕ) : Prop :=
  M.RunLegalBelow ρ' (i + 1) ∧ M.RunAgreeBelow ρ ρ' i


-- @@ L244-244 verbatim
/-! ### The dictionary -/


-- @@ L246-246 verbatim
section Dict


-- @@ L248-248 verbatim
variable {M} {ρ ρ'} {w w' : A → Config A}


-- @@ L250-251 verbatim
theorem runAcc_iff (h : Graphs ρ w) (t : A) : M.RunAcc ρ t ↔ M.Acc (w t).state :=
  ⟨fun hacc => hacc _ ((h.1 t _).mpr rfl), fun hacc q hq => (h.1 t q).mp hq ▸ hacc⟩


-- @@ L253-255 verbatim
theorem runBlkLt_iff (h : Graphs ρ w) (i : ℕ) (t : A) :
    M.RunBlkLt ρ i t ↔ M.BlkLt i (w t).state :=
  ⟨fun hb => hb _ ((h.1 t _).mpr rfl), fun hb q hq => (h.1 t q).mp hq ▸ hb⟩


-- @@ L257-263 verbatim
theorem runInit_iff (h : Graphs ρ w) (t : A) : M.RunInit ρ t ↔ M.IsInit (w t) := by
  refine ⟨fun hi => ⟨hi.1 _ ((h.1 t _).mpr rfl), hi.2.1 _ ((h.2.1 t _).mpr rfl),
    fun p => hi.2.2 p _ ((h.2.2 t p _).mpr rfl)⟩, fun hi => ⟨fun q hq => ?_, fun p hp => ?_,
      fun p a ha => ?_⟩⟩
  · exact (h.1 t q).mp hq ▸ hi.1
  · exact (h.2.1 t p).mp hp ▸ hi.2.1
  · exact (h.2.2 t p a).mp ha ▸ hi.2.2 p


-- @@ L265-278 verbatim
theorem runSame_iff (hg : Graphs ρ w) (hg' : Graphs ρ' w') (t t' : A) :
    RunSame ρ ρ' t t' ↔ w' t' = w t := by
  constructor
  · rintro ⟨hq, hp, ha⟩
    refine Config.ext (eq_of_iff_eq fun q => ?_) (eq_of_iff_eq fun p => ?_)
      (funext fun p => eq_of_iff_eq fun a => ?_)
    · exact ((hg'.1 t' q).symm.trans (hq q)).trans (hg.1 t q)
    · exact ((hg'.2.1 t' p).symm.trans (hp p)).trans (hg.2.1 t p)
    · exact ((hg'.2.2 t' p a).symm.trans (ha p a)).trans (hg.2.2 t p a)
  · intro heq
    refine ⟨fun q => ?_, fun p => ?_, fun p a => ?_⟩
    · rw [hg'.1 t' q, hg.1 t q, heq]
    · rw [hg'.2.1 t' p, hg.2.1 t p, heq]
    · rw [hg'.2.2 t' p a, hg.2.2 t p a, heq]


-- @@ L280-287 verbatim
theorem runAppTr_iff (h : Graphs ρ w) (t : A) : M.RunAppTr ρ t ↔ M.toTMData.AppTr (w t) := by
  refine exists_congr fun τ => and_congr_right fun _ => ?_
  refine and_congr ⟨fun hs => hs _ ((h.1 t _).mpr rfl), fun hs q hq => (h.1 t q).mp hq ▸ hs⟩
    (and_congr ⟨fun hr => hr _ _ ((h.2.1 t _).mpr rfl) ((h.2.2 t _ _).mpr rfl),
      fun hr p a hp ha => by rw [(h.2.1 t p).mp hp] at ha; exact (h.2.2 t _ a).mp ha ▸ hr⟩
      (and_congr Iff.rfl (and_congr Iff.rfl ?_)))
  refine or_congr (and_congr Iff.rfl ?_) (and_congr Iff.rfl ?_) <;>
    exact ⟨fun hm => hm _ ((h.2.1 t _).mpr rfl), fun hm p hp => (h.2.1 t p).mp hp ▸ hm⟩


-- @@ L289-291 verbatim
theorem runStuck_iff (h : Graphs ρ w) (t : A) : ¬M.RunAppTr ρ t ↔ M.Stuck (w t) := by
  rw [runAppTr_iff h, ← TMData.exists_step_iff_appTr]
  exact stuck_iff_not_exists_step.symm


-- @@ L293-312 verbatim
theorem runStep_iff (h : Graphs ρ w) (t t' : A) :
    M.RunStep (ρ := ρ) t t' ↔ M.Step (w t) (w t') := by
  refine exists_congr fun τ => and_congr_right fun _ => ?_
  refine and_congr ⟨fun hs => hs _ ((h.1 t _).mpr rfl), fun hs q hq => (h.1 t q).mp hq ▸ hs⟩
    (and_congr ⟨fun hr => hr _ _ ((h.2.1 t _).mpr rfl) ((h.2.2 t _ _).mpr rfl),
        fun hr p a hp ha => by rw [(h.2.1 t p).mp hp] at ha; exact (h.2.2 t _ a).mp ha ▸ hr⟩
      (and_congr ⟨fun hs => hs _ ((h.1 t' _).mpr rfl), fun hs q hq => (h.1 t' q).mp hq ▸ hs⟩
        (and_congr ⟨fun hr => hr _ _ ((h.2.1 t _).mpr rfl) ((h.2.2 t' _ _).mpr rfl),
            fun hr p a hp ha => by rw [(h.2.1 t p).mp hp] at ha; exact (h.2.2 t' _ a).mp ha ▸ hr⟩
          (and_congr ?_ ?_))))
  · constructor
    · intro hf p hp
      refine (eq_of_iff_eq fun a => ?_).symm
      exact ((h.2.2 t p a).symm.trans (hf p a fun hcon => hp ((h.2.1 t p).mp hcon))).trans
        (h.2.2 t' p a)
    · intro hf p a hp
      rw [h.2.2 t p a, h.2.2 t' p a, hf p fun hcon => hp ((h.2.1 t p).mpr hcon)]
  · refine or_congr (and_congr Iff.rfl ?_) (and_congr Iff.rfl ?_) <;>
      exact ⟨fun hm => hm _ _ ((h.2.1 t _).mpr rfl) ((h.2.1 t' _).mpr rfl),
        fun hm p p' hp hp' => (h.2.1 t p).mp hp ▸ (h.2.1 t' p').mp hp' ▸ hm⟩


-- @@ L314-321 verbatim
theorem runBlkMono_iff (h : Graphs ρ w) : M.RunBlkMono ρ ↔ M.BlkMono w := by
  constructor
  · intro hm p q hpq j j' hj hj'
    exact hm p q hpq _ _ ((h.1 p _).mpr rfl) ((h.1 q _).mpr rfl) j j' hj hj'
  · intro hm p q hpq x y hx hy j j' hj hj'
    rw [(h.1 p x).mp hx] at hj
    rw [(h.1 q y).mp hy] at hj'
    exact hm p q hpq j j' hj hj'


-- @@ L323-330 verbatim
theorem runLegalBelow_iff (h : Graphs ρ w) (i : ℕ) :
    M.RunLegalBelow ρ i ↔ M.LegalBelow i w := by
  refine and_congr (forall_congr' fun p => forall_congr' fun _ => runInit_iff h p)
    (and_congr (runBlkMono_iff h) ?_)
  refine forall_congr' fun p => forall_congr' fun q => forall_congr' fun _ => ?_
  rw [runBlkLt_iff h]
  exact imp_congr Iff.rfl (or_congr (and_congr (runStep_iff h p q) (not_congr (runAcc_iff h p)))
    (and_congr (runSame_iff h h p q) (or_congr (runAcc_iff h p) (runStuck_iff h p))))


-- @@ L332-333 verbatim
theorem runAccAt_iff (h : Graphs ρ w) : M.RunAccAt ρ ↔ M.AccAt w :=
  forall_congr' fun p => forall_congr' fun _ => runAcc_iff h p


-- @@ L335-340 verbatim
theorem runAgreeBelow_iff (hg : Graphs ρ w) (hg' : Graphs ρ' w') (i : ℕ) :
    M.RunAgreeBelow ρ ρ' i ↔ M.AgreeBelow i w' w := by
  refine and_congr (forall_congr' fun t => forall_congr' fun _ => ?_)
    (forall_congr' fun t => forall_congr' fun t' => forall_congr' fun _ => ?_) <;>
    rw [runBlkLt_iff hg] <;>
    exact imp_congr Iff.rfl (runSame_iff hg hg' _ _)


-- @@ L342-344 verbatim
theorem runRoundCond_iff (hg : Graphs ρ w) (hg' : Graphs ρ' w') (i : ℕ) :
    M.RunRoundCond ρ ρ' i ↔ M.RoundCond i w w' :=
  and_congr (runLegalBelow_iff hg' (i + 1)) (runAgreeBelow_iff hg hg' i)


-- @@ L346-346 verbatim
end Dict


-- @@ L348-348 verbatim
/-! ### The ladder over guesses -/


-- @@ L350-355 verbatim
/-- **The ladder from round `i` on, over guessed runs.** -/
def runLadder (start : Bool) (i : ℕ) : ℕ → tmGuessBlock.Assignment A → Prop
  | 0, ρprev => M.RunAccAt ρprev
  | m + 1, ρprev =>
      bareQ (blockPol start i) (fun ρ => RunFun ρ ∧ M.RunRoundCond ρprev ρ i)
        fun ρ => runLadder start (i + 1) m ρ


-- @@ L357-362 verbatim
/-- **The whole ladder, over guessed runs**: the sentence's semantics. -/
def RunAltLadder (start : Bool) : ℕ → Prop
  | 0 => False
  | m + 1 =>
      bareQ (blockPol start 0) (fun ρ => RunFun ρ ∧ M.RunLegalBelow ρ 1)
        fun ρ => M.runLadder start 1 m ρ


-- @@ L364-374 verbatim
/-- **The ladder over walks is the ladder over guesses**, from round `i` on. -/
theorem gameLadder_iff_runLadder (start : Bool) :
    ∀ (m i : ℕ) (ρprev : tmGuessBlock.Assignment A) (prev : A → Config A),
      Graphs ρprev prev → (M.gameLadder start i m prev ↔ M.runLadder start i m ρprev) := by
  intro m
  induction m with
  | zero => intro _ ρprev prev hg; exact (runAccAt_iff hg).symm
  | succ m ih =>
    intro i ρprev prev hg
    refine bareQ_transfer _ (fun ρ w hgw => ?_) fun ρ w hgw => (ih (i + 1) ρ w hgw).symm
    exact runRoundCond_iff hg hgw i


-- @@ L376-383 verbatim
/-- **The whole ladder over walks is the whole ladder over guesses.** -/
theorem altLadder_iff_runAltLadder (start : Bool) (n : ℕ) :
    M.AltLadder start n ↔ M.RunAltLadder start n := by
  cases n with
  | zero => exact Iff.rfl
  | succ m =>
    refine bareQ_transfer _ (fun ρ w hgw => runLegalBelow_iff hgw 1)
      fun ρ w hgw => (gameLadder_iff_runLadder M start m 1 ρ w hgw).symm


-- @@ L385-385 verbatim
end ATMData


-- @@ L387-387 verbatim
end DescriptiveComplexity
