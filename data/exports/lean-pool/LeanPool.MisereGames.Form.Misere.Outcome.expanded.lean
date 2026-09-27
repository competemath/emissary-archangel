/-
Copyright (c) 2025 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alfie Davies, Tomasz Maciosowski
-/
module

public import LeanPool.MisereGames.Form.Classes
public import LeanPool.MisereGames.Outcome
public meta import Mathlib.Tactic.ToDual
import LeanPool.MisereGames.Form.Birthday


-- @@ L13-15 verbatim
/-!
Misere combinatorial games.
-/


-- @@ L17-17 verbatim
namespace MisereGames


-- @@ L19-19 verbatim
public section


-- @@ L21-21 verbatim
namespace Form.Misere.Outcome


-- @@ L23-23 verbatim
open Form


-- @@ L25-25 verbatim
universe u


-- @@ L27-27 verbatim
variable {G : Type (u + 1)} [Form G]


-- @@ L29-33 verbatim
/-- In misère play, `p` can force a win when moving first from `g`. -/
def WinsGoingFirst (p : Player) (g : G) : Prop := IsEndLike p g ∨ (∃ g', ∃ (_ : g' ∈ moves p g),
  ¬WinsGoingFirst (-p) g')
  termination_by g
  decreasing_by exact Moves.Subposition.of_mem_moves (by assumption)


-- @@ L35-41 verbatim
theorem winsGoingFirst_iff (g : G) (p : Player)
    : WinsGoingFirst p g ↔ IsEndLike p g ∨ (∃ g' ∈ moves p g, ¬WinsGoingFirst (-p) g') := by
  apply Iff.intro <;> intro h1
  · unfold WinsGoingFirst at h1
    simp_all
  · unfold WinsGoingFirst
    simp_all


-- @@ L43-46 verbatim
@[simp]
theorem winsGoingFirst_of_isEndLike {g : G} {p : Player} (h1 : IsEndLike p g) :
    WinsGoingFirst p g :=
  (winsGoingFirst_iff g p).mpr (Or.inl h1)


-- @@ L48-50 verbatim
@[simp]
theorem winsGoingFirst_of_isEnd {g : G} {p : Player} (h1 : IsEnd p g) : WinsGoingFirst p g :=
  (winsGoingFirst_iff g p).mpr (Or.inl (isEndLike_of_isEnd h1))


-- @@ L52-56 verbatim
theorem winsGoingFirst_of_moves {g : G} {p : Player}
    (h1 : ∃ g' ∈ Form.moves p g, ¬WinsGoingFirst (-p) g')
    : WinsGoingFirst p g := by
  rw [winsGoingFirst_iff]
  exact Or.inr h1


-- @@ L58-87 verbatim
theorem winsGoingFirst_neg_iff (g : G) (p : Player) :
    (WinsGoingFirst p (-g)) ↔ (WinsGoingFirst (-p) g) := by
  constructor
    <;> intro h1
    <;> rw [winsGoingFirst_iff] at h1
    <;> apply Or.elim h1
    <;> intro h1
  · simp_all
  · obtain ⟨gp, h1, h2⟩ := h1
    rw [(winsGoingFirst_iff g (-p))]
    refine Or.inr ?_
    use -gp
    constructor
    · rwa [moves_neg, Set.mem_neg] at h1
    · rwa [neg_neg, winsGoingFirst_neg_iff]
  · simp_all
  · obtain ⟨gp, h1, h2⟩ := h1
    rw [neg_neg] at h2
    rw [winsGoingFirst_iff]
    apply Or.inr
    use -gp
    constructor
    · rwa [moves_neg, Set.mem_neg, neg_neg]
    · rwa [winsGoingFirst_neg_iff, neg_neg]
termination_by birthday g
decreasing_by
  all_goals
    first
    | exact Form.birthday_lt_of_mem_moves h1
    | simpa only [Form.birthday_neg] using Form.birthday_lt_of_mem_moves h1


-- @@ L89-93 verbatim
theorem not_winsGoingFirst_iff {g : G} {p : Player}
    : ¬WinsGoingFirst p g ↔ (¬Form.IsEndLike p g ∧ (∀ g' ∈ Form.moves p g,
      WinsGoingFirst (-p) g')) := by
  rw [winsGoingFirst_iff]
  simp only [not_or, not_exists, not_and, not_not]


-- @@ L95-96 verbatim
theorem winsGoingFirst_zero (p : Player) : WinsGoingFirst p (0 : G) :=
  winsGoingFirst_of_isEnd isEnd_zero


-- @@ L98-101 verbatim
open scoped Classical in
/-- The winning player when `p` starts from `g`. -/
@[expose] noncomputable def MiserePlayerOutcome : G → Player → Player :=
  fun g p => if WinsGoingFirst p g then p else -p


-- @@ L103-106 verbatim
open scoped Classical in
/-- The four-outcome misère outcome of a form. -/
@[expose] noncomputable def MisereOutcome : G → Outcome :=
  fun g => Outcome.ofPlayers (MiserePlayerOutcome g .left) (MiserePlayerOutcome g .right)


-- @@ L108-117 verbatim
@[simp]
theorem miserePlayerOutcome_eq_iff_winsGoingFirst {g : G} {p : Player}
    : (MiserePlayerOutcome g p = p) ↔ WinsGoingFirst p g := by
  apply Iff.intro <;> intro h1
  · simp only [MiserePlayerOutcome] at h1
    by_cases h2 : WinsGoingFirst p g
    · exact h2
    · simp [h2] at h1
      cases p <;> simp at h1
  · simp only [MiserePlayerOutcome, h1, ↓reduceIte]


-- @@ L119-125 verbatim
theorem misereOutcome_L_iff_miserePlayerOutcome {g : G}
    : (MisereOutcome g = .L) ↔
      ((MiserePlayerOutcome g .left = .left) ∧ (MiserePlayerOutcome g .right = .left)) := by
  simp [MiserePlayerOutcome, MisereOutcome, Outcome.ofPlayers]
  by_cases h1 : WinsGoingFirst Player.left g
  <;> by_cases h2 : WinsGoingFirst Player.right g
  <;> simp [h1, h2]


-- @@ L127-133 verbatim
theorem misereOutcome_N_iff_miserePlayerOutcome {g : G}
    : (MisereOutcome g = .N) ↔
      ((MiserePlayerOutcome g .left = .left) ∧ (MiserePlayerOutcome g .right = .right)) := by
  simp [MiserePlayerOutcome, MisereOutcome, Outcome.ofPlayers]
  by_cases h1 : WinsGoingFirst Player.left g
  <;> by_cases h2 : WinsGoingFirst Player.right g
  <;> simp [h1, h2]


-- @@ L135-141 verbatim
theorem misereOutcome_P_iff_miserePlayerOutcome {g : G}
    : (MisereOutcome g = .P) ↔
      ((MiserePlayerOutcome g .left = .right) ∧ (MiserePlayerOutcome g .right = .left)) := by
  simp [MiserePlayerOutcome, MisereOutcome, Outcome.ofPlayers]
  by_cases h1 : WinsGoingFirst Player.left g
  <;> by_cases h2 : WinsGoingFirst Player.right g
  <;> simp [h1, h2]


-- @@ L143-149 verbatim
theorem misereOutcome_R_iff_miserePlayerOutcome {g : G}
    : (MisereOutcome g = .R) ↔
      ((MiserePlayerOutcome g .left = .right) ∧ (MiserePlayerOutcome g .right = .right)) := by
  simp [MiserePlayerOutcome, MisereOutcome, Outcome.ofPlayers]
  by_cases h1 : WinsGoingFirst Player.left g
  <;> by_cases h2 : WinsGoingFirst Player.right g
  <;> simp [h1, h2]


-- @@ L151-155 verbatim
@[simp]
theorem minsGoingFirst_left_of_misereOutcome_L {g : G}
    (h1 : MisereOutcome g = .L) : WinsGoingFirst .left g := by
  rw [misereOutcome_L_iff_miserePlayerOutcome, miserePlayerOutcome_eq_iff_winsGoingFirst] at h1
  exact h1.left


-- @@ L157-161 verbatim
@[simp]
theorem winsGoingFirst_right_of_misereOutcome_R {g : G}
    (h1 : MisereOutcome g = .R) : WinsGoingFirst .right g := by
  rw [misereOutcome_R_iff_miserePlayerOutcome, miserePlayerOutcome_eq_iff_winsGoingFirst] at h1
  exact h1.right


-- @@ L163-170 verbatim
private theorem conjugate_misereOutcome_of_ofPlayers_neg (g : G) :
    Outcome.ofPlayers
      (-(MiserePlayerOutcome g .right))
      (-(MiserePlayerOutcome g .left))
    = Outcome.Conjugate (MisereOutcome g) := by
  cases h1 : MiserePlayerOutcome g .right
  <;> cases h2 : MiserePlayerOutcome g .left
  all_goals simp only [h1, h2, Outcome.Conjugate, Outcome.ofPlayers, MisereOutcome]


-- @@ L172-179 verbatim
@[simp]
theorem miserePlayerOutcome_neg_player_neg (g : G) (p : Player) :
    MiserePlayerOutcome (-g) p = -(MiserePlayerOutcome g (-p)) := by
  unfold MiserePlayerOutcome
  rw [winsGoingFirst_neg_iff g p, neg_neg]
  cases p
  · by_cases h1 : WinsGoingFirst .right g <;> simp [h1]
  · by_cases h1 : WinsGoingFirst .left g <;> simp [h1]


-- @@ L181-191 verbatim
@[simp]
theorem misereOutcome_conjugate_neg (g : G) :
    (MisereOutcome g).Conjugate = MisereOutcome (-g) := by
  unfold Outcome.Conjugate
  cases h1 : MisereOutcome g
  all_goals
  · unfold MisereOutcome
    rw [miserePlayerOutcome_neg_player_neg, Player.neg_left,
        miserePlayerOutcome_neg_player_neg, Player.neg_right,
        conjugate_misereOutcome_of_ofPlayers_neg g, h1]
    rfl


-- @@ L193-197 verbatim
theorem misereOutcome_ge_P_of_not_winsGoingFirst_right {g : G} (h1 : ¬WinsGoingFirst .right g) :
    MisereOutcome g ≥ Outcome.P := by
  unfold MisereOutcome Outcome.ofPlayers MiserePlayerOutcome
  by_cases h2 : WinsGoingFirst .left g
  all_goals simp only [h1, h2, reduceIte, ge_iff_le, le_refl, Outcome.L_ge]


-- @@ L199-202 verbatim
theorem misereOutcome_le_N_of_winsGoingFirst_right {g : G} (h1 : WinsGoingFirst .right g) :
    MisereOutcome g ≤ Outcome.N := by
  unfold MisereOutcome Outcome.ofPlayers MiserePlayerOutcome
  by_cases h2 : WinsGoingFirst .left g <;> simp [h1, h2]


-- @@ L204-213 verbatim
theorem not_winsGoingFirst_of_misereOutcome_P {g : G} {p : Player}
    (h1 : MisereOutcome g = Outcome.P) : ¬WinsGoingFirst p g := by
  intro h2
  unfold MisereOutcome Outcome.ofPlayers MiserePlayerOutcome at h1
  by_cases h3 : WinsGoingFirst .left g
  <;> by_cases h4 : WinsGoingFirst .right g
  <;> simp only [h3, h4, reduceIte, reduceCtorEq, Player.neg_left, Player.neg_right] at h1
  cases p
  · exact h3 h2
  · exact h4 h2


-- @@ L215-219 verbatim
theorem misereOutcome_P_of_miserePlayerOutcome_neg {g : G} (h1 : ∀ p,
  MiserePlayerOutcome g p = -p) :
    MisereOutcome g = Outcome.P := by
  unfold MisereOutcome Outcome.ofPlayers
  simp only [h1 .left, h1 .right]


-- @@ L221-236 verbatim
@[simp]
theorem misereOutcome_eq_player_iff (g : G) (p : Player) :
    (MisereOutcome g = Outcome.ofPlayer p) ↔ (WinsGoingFirst p g ∧ ¬WinsGoingFirst (-p) g) := by
  constructor <;> intro h1
  · unfold MisereOutcome Outcome.ofPlayers MiserePlayerOutcome at h1
    by_cases h2 : WinsGoingFirst .left g
      <;> by_cases h3 : WinsGoingFirst .right g
      <;> cases p
      <;> simp only [h2, h3, Outcome.ofPlayer, Player.neg_left, Player.neg_right, reduceIte,
                     reduceCtorEq] at h1
    · exact And.intro h2 h3
    · exact And.intro h3 h2
  · unfold MisereOutcome Outcome.ofPlayers MiserePlayerOutcome
    cases p
    <;> simp only [Player.neg_left, Player.neg_right] at h1
    <;> simp only [h1, reduceIte, Player.neg_right, Outcome.ofPlayer]


-- @@ L238-243 verbatim
theorem misereOutcome_L_iff_winsGoingFirst {g : G} :
    (MisereOutcome g = .L) ↔ (WinsGoingFirst .left g ∧ ¬WinsGoingFirst .right g) := by
  have h1 : Outcome.L = Outcome.ofPlayer .left := by rfl
  have h2 : Player.right = -Player.left := rfl
  rw [h1, h2]
  exact misereOutcome_eq_player_iff g Player.left


-- @@ L245-250 verbatim
theorem misereOutcome_R_iff_winsGoingFirst {g : G} :
    (MisereOutcome g = .R) ↔ (WinsGoingFirst .right g ∧ ¬WinsGoingFirst .left g) := by
  have h1 : Outcome.R = Outcome.ofPlayer .right := by rfl
  have h2 : Player.left = -Player.right := by rfl
  rw [h1, h2]
  exact misereOutcome_eq_player_iff g Player.right


-- @@ L252-262 verbatim
theorem misereOutcome_P_iff_winsGoingFirst' {g : G} {p : Player} :
    (MisereOutcome g = .P) ↔ (¬WinsGoingFirst p g ∧ ¬WinsGoingFirst (-p) g) := by
  constructor
  · intro h1
    exact ⟨not_winsGoingFirst_of_misereOutcome_P h1, not_winsGoingFirst_of_misereOutcome_P h1⟩
  · intro ⟨h1, h2⟩
    unfold MisereOutcome Outcome.ofPlayers MiserePlayerOutcome
    cases p
    all_goals
    · simp only [Player.neg_right, Player.neg_left] at h2
      simp only [h1, h2, Player.neg_left, Player.neg_right, Player.neg_right, reduceIte]


-- @@ L264-267 verbatim
theorem misereOutcome_P_iff_winsGoingFirst {g : G} :
    (MisereOutcome g = .P) ↔ (¬WinsGoingFirst .right g ∧ ¬WinsGoingFirst .left g) := by
  rw [<-Player.neg_right]
  exact misereOutcome_P_iff_winsGoingFirst'


-- @@ L269-274 verbatim
theorem misereOutcome_N_iff_winsGoingFirst {g : G} :
    (MisereOutcome g = .N) ↔ (WinsGoingFirst .left g ∧ WinsGoingFirst .right g) := by
  simp only [← miserePlayerOutcome_eq_iff_winsGoingFirst]
  cases h_left : MiserePlayerOutcome g .left
  <;> cases h_right : MiserePlayerOutcome g .right
  <;> simp [MisereOutcome, Outcome.ofPlayers, h_left, h_right]


-- @@ L276-285 verbatim
/--
If `o(x) ≥ N` then Left wins going first on `x`.
-/
theorem winsGoingFirst_left_of_ge_N {x : G} (h : MisereOutcome x ≥ .N) :
    WinsGoingFirst .left x := by
  rcases hc : MisereOutcome x with _ | _ | _ | _
  · exact (misereOutcome_L_iff_winsGoingFirst.mp hc).1
  · exact (misereOutcome_N_iff_winsGoingFirst.mp hc).1
  · rw [hc] at h; exact absurd h (by decide)
  · rw [hc] at h; exact absurd h (by decide)


-- @@ L287-289 verbatim
@[simp]
theorem miserePlayerOutcome_zero (p : Player) : MiserePlayerOutcome (0 : G) p = p := by
  simp_all


-- @@ L291-294 verbatim
@[simp]
theorem misereOutcome_zero_N : MisereOutcome (0 : G) = .N := by
  unfold MisereOutcome Outcome.ofPlayers
  simp only [miserePlayerOutcome_zero]


-- @@ L296-303 verbatim
@[simp]
theorem misereOutcome_neg_R_iff_misereOutcome {g : G}
    : (MisereOutcome (-g) = .R) ↔ (MisereOutcome g = .L) := by
  unfold MisereOutcome Outcome.ofPlayers
  simp only [miserePlayerOutcome_neg_player_neg, Player.neg_left, Player.neg_right]
  cases MiserePlayerOutcome g Player.right
  <;> cases MiserePlayerOutcome g Player.left
  <;> simp


-- @@ L305-308 verbatim
@[simp]
theorem misereOutcome_neg_L_iff_misereOutcome {g : G}
    : (MisereOutcome (-g) = .L) ↔ (MisereOutcome g = .R) := by
  rw [<-neg_neg g, misereOutcome_neg_R_iff_misereOutcome, neg_neg]


-- @@ L310-314 verbatim
@[simp]
theorem misereOutcome_neg_N_iff_misereOutcome {g : G}
    : (MisereOutcome (-g) = .N) ↔ (MisereOutcome g = .N) := by
  rw [← misereOutcome_conjugate_neg]
  cases MisereOutcome g <;> simp [Outcome.Conjugate]


-- @@ L316-324 verbatim
theorem winsGoingFirst_left_of_move_misereOutcome_P {g gl : G} (h1 : gl ∈ moves .left g)
    (h2 : MisereOutcome gl = Outcome.P) : WinsGoingFirst .left g := by
  unfold MisereOutcome Outcome.ofPlayers MiserePlayerOutcome at h2
  by_cases h3 : WinsGoingFirst .left gl
    <;> by_cases h4 : WinsGoingFirst .right gl
    <;> simp only [h3, h4, reduceIte, reduceCtorEq] at h2
  apply winsGoingFirst_of_moves
  simp only [Player.neg_left]
  use gl


-- @@ L326-328 verbatim
theorem winsGoingFirst_add_of_isEndLike {g h : G} {p : Player} (h1 : IsEndLike p g)
    (h2 : IsEndLike p h) : WinsGoingFirst p (g + h) :=
  winsGoingFirst_of_isEndLike (IsEndLike.add_iff.mpr ⟨h1, h2⟩)


-- @@ L330-332 verbatim
theorem winsGoingFirst_add_of_isEnd {g h : G} {p : Player} (h1 : IsEnd p g)
    (h2 : IsEnd p h) : WinsGoingFirst p (g + h) :=
  winsGoingFirst_of_isEnd (IsEnd.add_iff.mpr ⟨h1, h2⟩)


-- @@ L334-342 verbatim
theorem miserePlayerOutcome_of_leftMoves {g gl : G} (h1 : gl ∈ moves .left g)
    (h2 : MiserePlayerOutcome gl .right = .left) : MiserePlayerOutcome g .left = .left := by
  rw [miserePlayerOutcome_eq_iff_winsGoingFirst, winsGoingFirst_iff]
  apply Or.inr
  use gl
  apply And.intro h1
  simp only [Player.neg_left, Player.right_le, Player.le_right_eq]
  unfold MiserePlayerOutcome at h2
  simp_all


-- @@ L344-351 verbatim
theorem miserePlayerOutcome_of_rightMoves {g gr : G} (h1 : gr ∈ moves .right g)
    (h2 : MiserePlayerOutcome gr .left = .right) : MiserePlayerOutcome g .right = .right := by
  rw [miserePlayerOutcome_eq_iff_winsGoingFirst, winsGoingFirst_iff]
  refine Or.inr ⟨gr, h1, ?_⟩
  intro h3
  have h4 : MiserePlayerOutcome gr .left = .left := by
    rwa [miserePlayerOutcome_eq_iff_winsGoingFirst]
  simp_all


-- @@ L353-360 verbatim
theorem misereOutcome_ge_iff_miserePlayerOutcome_ge {g h : G}
    : MisereOutcome g ≥ MisereOutcome h ↔ (∀ p,
      MiserePlayerOutcome g p ≥ MiserePlayerOutcome h p) := by
  cases hgl : MiserePlayerOutcome g .left <;>
    cases hgr : MiserePlayerOutcome g .right <;>
    cases hhl : MiserePlayerOutcome h .left <;>
    cases hhr : MiserePlayerOutcome h .right <;>
    simp [MisereOutcome, Outcome.ofPlayers, hgl, hgr, hhl, hhr, LE.le, LT.lt]


-- @@ L362-366 verbatim
/--
Restricted misère equivalence, working modulo a set `A`.
-/
@[expose] def MisereEQ (A : G → Prop) (g h : G) : Prop :=
  ∀ (x : G), A x → MisereOutcome (g + x) = MisereOutcome (h + x)


-- @@ L368-369 verbatim
@[inherit_doc MisereEQ]
syntax (name := misereEQ) term:51 " =m " term:max term:51 : term


-- @@ L371-372 expanded
macro_rules (kind:=misereEQ)
  | `(MisereEQ $u $x $y) => `(MisereEQ $u $x $y)


-- @@ L374-374 verbatim
recommended_spelling "misereEQ" for "=m" in [MisereEQ, misereEQ]


-- @@ L376-376 verbatim
open Lean PrettyPrinter Delaborator SubExpr


-- @@ L378-384 expanded
/-- Delaborator for restricted misère equivalence notation. -/
@[app_delab MisereEQ]
meta def delabMisereEQ : Delab := do
  let y ← withAppArg delab
  let x ←
    withAppFn do
        withAppArg delab
  let u ←
    withAppFn do
        withAppFn do
            withAppArg delab
  `(MisereEQ $u $x $y)


-- @@ L386-389 expanded
theorem MisereEQ.symm {A : G → Prop} {g h : G} (h1 : MisereEQ A g h) : MisereEQ A h g :=
  by
  intro x h2
  have h3 := h1 x h2
  exact Eq.symm h3


-- @@ L391-394 expanded
theorem MisereEQ.trans {A : G → Prop} {g h k : G} (h1 : MisereEQ A g h) (h2 : MisereEQ A h k) :
    MisereEQ A g k := by
  unfold MisereEQ at *
  simp_all


-- @@ L396-400 verbatim
/--
The restricted misère preorder, working modulo a set `A`.
-/
@[expose] def MisereGE (A : G → Prop) (g h : G) : Prop :=
  ∀ x, (A x → MisereOutcome (g + x) ≥ MisereOutcome (h + x))


-- @@ L402-403 verbatim
@[inherit_doc MisereGE]
syntax (name := misereGE) term:51 " ≥m " term:max term:51 : term


-- @@ L405-406 expanded
macro_rules (kind:=misereGE)
  | `(MisereGE $u $x $y) => `(MisereGE $u $x $y)


-- @@ L408-408 verbatim
recommended_spelling "misereGE" for "≥m" in [MisereGE, misereGE]


-- @@ L410-416 expanded
/-- Delaborator for restricted misère preorder notation. -/
@[app_delab MisereGE]
meta def delabMisereGE : Delab := do
  let y ← withAppArg delab
  let x ←
    withAppFn do
        withAppArg delab
  let u ←
    withAppFn do
        withAppFn do
            withAppArg delab
  `(MisereGE $u $x $y)


-- @@ L418-420 expanded
theorem MisereEq.of_antisymm {A : G → Prop} {g h : G} (h1 : MisereGE A g h) (h2 : MisereGE A h g) :
    MisereEQ A g h := fun x h3 =>
  PartialOrder.le_antisymm (MisereOutcome (g + x)) (MisereOutcome (h + x)) (h2 x h3) (h1 x h3)


-- @@ L422-426 expanded
theorem MisereGE.trans {A : G → Prop} {g h k : G} (h1 : MisereGE A g h) (h2 : MisereGE A h k) :
    MisereGE A g k := by
  unfold MisereGE at *
  intro x h3
  exact le_trans (h2 x h3) (h1 x h3)


-- @@ L428-431 expanded
theorem misereGE_rw_left {A : G → Prop} {a b c : G} (h2 : MisereEQ A b c) (h1 : MisereGE A b a) :
    MisereGE A c a := by
  unfold MisereGE at h1 ⊢
  unfold MisereEQ at h2
  simp_all


-- @@ L433-437 expanded
theorem misereGE_rw_right {A : G → Prop} {a b c : G} (h2 : MisereEQ A b c) (h1 : MisereGE A a c) :
    MisereGE A a b := by
  unfold MisereGE at h1 ⊢
  unfold MisereEQ at h2
  simp_all


-- @@ L439-442 expanded
theorem misereGE_of_misereEQ {A : G → Prop} {g h : G} (h1 : MisereEQ A g h) : MisereGE A g h :=
  by
  intro x hx
  have := h1 x hx
  exact Std.le_of_eq (Eq.symm this)


-- @@ L444-447 expanded
theorem misereGE_of_subset (U : G → Prop) {V : G → Prop} (h_v_subset_u : ∀ g, V g → U g) (g h : G)
    (h2 : MisereGE U g h) : MisereGE V g h :=
  by
  unfold MisereGE at h2 ⊢
  simp_all


-- @@ L449-458 expanded
/-- Adding a fixed element `c ∈ A` on the right preserves the restricted misère
inequality.
-/
theorem misereGE_add_right {A : G → Prop} [ClosedUnderAdd A] {g h c : G} (hc : A c)
    (h1 : MisereGE A g h) : MisereGE A (g + c) (h + c) :=
  by
  intro x hx
  have hcx : A (c + x) := ClosedUnderAdd.has_add c x hc hx
  have := h1 (c + x) hcx
  rwa [← add_assoc, ← add_assoc] at this


-- @@ L460-469 expanded
/-- Adding a fixed element `c ∈ A` on the right preserves the restricted misère
equivalence.
-/
theorem misereEQ_add_right {A : G → Prop} [ClosedUnderAdd A] {g h c : G} (hc : A c)
    (h1 : MisereEQ A g h) : MisereEQ A (g + c) (h + c) :=
  by
  intro x hx
  have hcx : A (c + x) := ClosedUnderAdd.has_add c x hc hx
  have := h1 (c + x) hcx
  rwa [← add_assoc, ← add_assoc] at this


-- @@ L471-480 expanded
/-- Adding a fixed element `c ∈ A` on the left preserves the restricted misère
equivalence.
-/
theorem misereEQ_add_left {A : G → Prop} [ClosedUnderAdd A] {g h c : G} (hc : A c)
    (h1 : MisereEQ A g h) : MisereEQ A (c + g) (c + h) :=
  by
  have := misereEQ_add_right hc h1
  intro x hx
  have h2 := this x hx
  rwa [add_comm c g, add_comm c h]


-- @@ L482-485 expanded
@[simp]
theorem MisereGE.refl {A : G → Prop} (g : G) : MisereGE A g g :=
  by
  unfold MisereGE
  simp_all


-- @@ L487-494 expanded
theorem not_misereEQ_of_not_misereGE {A : G → Prop} {g h : G} (h1 : ¬(MisereGE A g h)) :
    ¬(MisereEQ A g h) := by
  simp only [MisereGE, ge_iff_le, not_forall] at h1
  obtain ⟨x, ⟨h1, h2⟩⟩ := h1
  simp only [MisereEQ, not_forall]
  use x
  use h1
  exact Ne.symm (ne_of_not_le h2)


-- @@ L496-510 expanded
private theorem ClosedUnderNeg.not_ge_neg_iff.aux {A : G → Prop} [ClosedUnderNeg A] {g h : G}
    (h1 : MisereGE A g h) : MisereGE A (-h) (-g) :=
  by
  unfold MisereGE at *
  intro x h0
  have h2 := h1 (-x) (ClosedUnderNeg.neg_iff.mpr h0)
  have h4 : MisereOutcome (-h + x) = (MisereOutcome (-h + x)).Conjugate.Conjugate :=
    Eq.symm Outcome.conjugate_conjugate_eq_self
  have h5 : (MisereOutcome (-h + x)).Conjugate.Conjugate = (MisereOutcome (h + (-x))).Conjugate :=
    by simp only [misereOutcome_conjugate_neg, neg_add_rev, neg_neg, add_comm]
  rw [h4, h5]
  have h6 : (MisereOutcome (g + (-x))).Conjugate = MisereOutcome (-g + x) := by
    simp only [misereOutcome_conjugate_neg, neg_add_rev, neg_neg, add_comm]
  rw [← h6]
  apply Outcome.outcome_ge_conjugate_le
  exact h2


-- @@ L512-518 expanded
@[simp]
theorem ClosedUnderNeg.neg_ge_neg_iff {A : G → Prop} [ClosedUnderNeg A] (g h : G) :
    MisereGE A (-h) (-g) ↔ MisereGE A g h :=
  by
  constructor <;> intro h1
  · have h2 := not_ge_neg_iff.aux h1
    simp_all
  · exact not_ge_neg_iff.aux h1


-- @@ L520-527 expanded
private theorem misereEQ_neg' {A : G → Prop} [ClosedUnderNeg A] {g h : G}
    (h1 : MisereEQ A (-g) (-h)) : MisereEQ A g h :=
  by
  apply MisereEq.of_antisymm
  · have := misereGE_of_misereEQ (MisereEQ.symm h1)
    rwa [← ClosedUnderNeg.neg_ge_neg_iff, neg_neg, neg_neg] at this
  · have := misereGE_of_misereEQ h1
    rwa [← ClosedUnderNeg.neg_ge_neg_iff, neg_neg, neg_neg] at this


-- @@ L529-534 expanded
theorem misereEQ_neg_iff {A : G → Prop} [ClosedUnderNeg A] {g h : G} :
    (MisereEQ A (-g) (-h)) ↔ (MisereEQ A g h) :=
  by
  constructor <;> intro h1
  · exact misereEQ_neg' h1
  · rw [← neg_neg g, ← neg_neg h] at h1
    exact misereEQ_neg' h1


-- @@ L536-556 verbatim
@[simp]
theorem winsGoingFirst_left_intCast_iff (n : ℤ) : WinsGoingFirst .left (n : G) ↔ n ≤ 0 := by
  have not_winsGoingFirst_left_natCast_pos {n : ℕ} (h_pos : 0 < n) :
      ¬WinsGoingFirst .left (n : G) := by
    rw [not_winsGoingFirst_iff]
    constructor
    · simp [Nat.ne_zero_iff_zero_lt.mpr h_pos]
    · simp_all
  constructor <;> intro h1
  · match n with
    | .ofNat n =>
      simp only [Int.ofNat_eq_natCast] at h1
      have : n = 0 := by
        by_contra h2
        absurd h1
        apply not_winsGoingFirst_left_natCast_pos
        exact Nat.ne_zero_iff_zero_lt.mp h2
      exact Int.toNat_eq_zero.mp this
    | .negSucc n =>
      exact Int.negSucc_le_zero n
  · simp_all


-- @@ L558-561 verbatim
@[simp]
theorem winsGoingFirst_left_natCast_iff (n : ℕ) : WinsGoingFirst .left (n : G) ↔ n = 0 := by
  rw [<-Form.intCast_nat, winsGoingFirst_left_intCast_iff]
  exact Int.natCast_nonpos_iff


-- @@ L563-584 verbatim
@[simp]
theorem winsGoingFirst_right_intCast_iff (n : ℤ) : WinsGoingFirst .right (n : G) ↔ 0 ≤ n := by
  constructor <;> intro h1
  · match n with
    | .ofNat n => simp
    | .negSucc n =>
      absurd h1
      rw [not_winsGoingFirst_iff]
      simp only [Form.intCast_negSucc, neg_add_rev, IsEndLike.add_iff, IsEndLike.neg_iff_neg,
        Player.neg_right, not_isEndLike_left_one, natCast_isEndLike_iff,
        isEnd_left_natCast_iff, false_and, not_false_eq_true, moves_add, moves_neg,
        leftMoves_one, Set.neg_singleton, neg_zero, Set.image_singleton, zero_add,
        Set.singleton_union, Set.mem_insert_iff, Set.mem_image, Set.mem_neg,
        Set.exists_neg_mem, forall_eq_or_imp, Player.neg_left, isEnd_right_natCast,
        winsGoingFirst_of_isEndLike, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
        true_and]
      intro g h_g
      match n with
      | 0 => simp at h_g
      | n + 1 =>
        simp_all
  · simp_all


-- @@ L586-587 verbatim
theorem winsGoingFirst_right_natCast (n : ℕ) : WinsGoingFirst .right (n : G) := by
  simp_all


-- @@ L589-592 verbatim
@[simp]
theorem not_winsGoingFirst_left_one : ¬WinsGoingFirst .left (1 : G) := by
  rw [<-Form.intCast_one, winsGoingFirst_left_intCast_iff]
  omega


-- @@ L594-595 verbatim
theorem winsGoingFirst_right_one : WinsGoingFirst .right (1 : G) := by
  simp_all


-- @@ L597-599 verbatim
@[simp]
theorem one_misereOutcome_R : MisereOutcome (1 : G) = .R := by
  simp [misereOutcome_R_iff_winsGoingFirst]


-- @@ L601-608 verbatim
@[simp]
theorem misereOutcome_R_intCast_iff (n : ℤ) : MisereOutcome (n : G) = .R ↔ 0 < n := by
  rw [misereOutcome_R_iff_winsGoingFirst]
  constructor <;> intro h
  · exact not_le.mp ((winsGoingFirst_left_intCast_iff n).not.mp h.right)
  · constructor
    · exact (winsGoingFirst_right_intCast_iff n).mpr h.le
    · exact (winsGoingFirst_left_intCast_iff n).not.mpr (not_le.mpr h)


-- @@ L610-613 verbatim
@[simp]
theorem misereOutcome_R_natCast_iff (n : ℕ) : MisereOutcome (n : G) = .R ↔ 0 < n := by
  rw [<-Form.intCast_nat, misereOutcome_R_intCast_iff]
  simp only [Int.natCast_pos]


-- @@ L615-622 verbatim
@[simp]
theorem misereOutcome_L_intCast_iff (n : ℤ) : MisereOutcome (n : G) = .L ↔ n < 0 := by
  rw [misereOutcome_L_iff_winsGoingFirst]
  constructor <;> intro h
  · exact not_le.mp ((winsGoingFirst_right_intCast_iff n).not.mp h.right)
  · constructor
    · exact (winsGoingFirst_left_intCast_iff n).mpr h.le
    · exact (winsGoingFirst_right_intCast_iff n).not.mpr (not_le.mpr h)


-- @@ L624-627 verbatim
@[simp]
theorem misereOutcome_L_natCast (n : ℕ) : ¬MisereOutcome (n : G) = .L := by
  rw [<-Form.intCast_nat, misereOutcome_L_intCast_iff]
  simp only [not_lt, Int.natCast_nonneg]


-- @@ L629-636 verbatim
@[simp]
theorem misereOutcome_N_intCast_iff (n : ℤ) : MisereOutcome (n : G) = .N ↔ n = 0 := by
  rw [misereOutcome_N_iff_winsGoingFirst]
  constructor <;> intro h
  · have h1 := (winsGoingFirst_left_intCast_iff (G := G) n).mp h.left
    have h2 := (winsGoingFirst_right_intCast_iff (G := G) n).mp h.right
    exact Eq.symm (Int.le_antisymm h2 h1)
  · simp_all


-- @@ L638-641 verbatim
@[simp]
theorem misereOutcome_N_natCast_iff (n : ℕ) : MisereOutcome (n : G) = .N ↔ n = 0 := by
  rw [<-Form.intCast_nat, misereOutcome_N_intCast_iff]
  simp only [Int.natCast_eq_zero]


-- @@ L643-652 verbatim
@[simp]
theorem misereOutcome_P_intCast (n : ℤ) : ¬MisereOutcome (n : G) = .P := by
  apply Or.elim3 (Int.lt_trichotomy n 0) <;> intro h
  · rw [<-misereOutcome_L_intCast_iff (G := G)] at h
    rw [h]
    decide
  · simp_all
  · rw [<-misereOutcome_R_intCast_iff (G := G)] at h
    rw [h]
    decide


-- @@ L654-657 verbatim
@[simp]
theorem misereOutcome_P_natCast (n : ℕ) : ¬MisereOutcome (n : G) = .P := by
  rw [<-Form.intCast_nat]
  exact misereOutcome_P_intCast (G := G) _


-- @@ L659-659 verbatim
end Form.Misere.Outcome


-- @@ L661-661 verbatim
end


-- @@ L663-663 verbatim
end MisereGames
