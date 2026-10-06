/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.HaltHard.Table


-- @@ L8-30 verbatim
/-!
# The simulating machine on a zipper tape

The simulation of `Turing.ToPartrec.step` by
`DescriptiveComplexity.HaltHard.simStep` is proved against a concrete
sequential semantics first: a configuration is a *zipper*
(`DescriptiveComplexity.HaltHard.LCfg`) – the state, the letters left of the
head (nearest first), the letter under the head, and the letters right of the
head (nearest first) – and one step (`DescriptiveComplexity.HaltHard.lstep`)
applies the table and moves, materializing a blank when the head leaves the
recorded region. This keeps every walk argument a plain list induction; the
sibling `Bridge` file identifies runs of `lstep` with derivations of the
rewriting system `DescriptiveComplexity.HaltPcp.MRule` of the drawn machine,
so nothing here mentions words or rules.

Beside the step and its reachability
(`DescriptiveComplexity.HaltHard.Reach`, and the step-counted
`DescriptiveComplexity.HaltHard.stepsTo` the deterministic backward reading
needs), the file provides the two **walk combinators**: a state that passes a
set of letters unchanged in one direction crosses any run of them
(`DescriptiveComplexity.HaltHard.reach_walkR`/`reach_walkL`). Every phase of
the simulation is a chain of these.
-/


-- @@ L32-32 verbatim
namespace DescriptiveComplexity


-- @@ L34-34 verbatim
namespace HaltHard


-- @@ L36-36 verbatim
open Turing.ToPartrec


-- @@ L38-38 verbatim
variable {c : Code}


-- @@ L40-52 verbatim
/-- A configuration of the simulating machine, as a zipper: the letters left
of the head are listed nearest-first, the letters right of the head
nearest-first. Cells outside the recorded region are blank; a move beyond it
materializes the blank. -/
structure LCfg (c : Code) where
  /-- The current state. -/
  q : SimQ c
  /-- The letters left of the head, nearest first. -/
  L : List (SimSym c)
  /-- The letter under the head. -/
  s : SimSym c
  /-- The letters right of the head, nearest first. -/
  R : List (SimSym c)


-- @@ L54-65 verbatim
/-- One step of the machine on the zipper tape: apply the table, write, move;
a move beyond the recorded region reads a fresh blank. -/
def lstep (x : LCfg c) : Option (LCfg c) :=
  (simStep x.q x.s).map fun a =>
    if a.2.2 then
      match x.R with
      | [] => ⟨a.2.1, a.1 :: x.L, .bk, []⟩
      | t :: R' => ⟨a.2.1, a.1 :: x.L, t, R'⟩
    else
      match x.L with
      | [] => ⟨a.2.1, [], .bk, a.1 :: x.R⟩
      | t :: L' => ⟨a.2.1, L', t, a.1 :: x.R⟩


-- @@ L67-69 verbatim
/-- Reachability in any number of machine steps. -/
def Reach : LCfg c → LCfg c → Prop :=
  Relation.ReflTransGen fun x y => lstep x = some y


-- @@ L71-74 verbatim
/-- Reaching one configuration from another in exactly `n` steps. -/
def stepsTo : ℕ → LCfg c → LCfg c → Prop
  | 0, x, y => x = y
  | n + 1, x, y => ∃ d, lstep x = some d ∧ stepsTo n d y


-- @@ L76-76 verbatim
/-! ### The four single steps -/


-- @@ L78-78 verbatim
section Steps


-- @@ L80-80 verbatim
variable {q q' : SimQ c} {σ σ' : SimSym c}


-- @@ L82-86 verbatim
/-- A right move with a recorded cell to enter. -/
theorem lstep_right (h : simStep q σ = some (σ', q', true)) (L : List (SimSym c))
    (t : SimSym c) (R : List (SimSym c)) :
    lstep ⟨q, L, σ, t :: R⟩ = some ⟨q', σ' :: L, t, R⟩ := by
  simp [lstep, h]


-- @@ L88-91 verbatim
/-- A right move off the recorded region: the entered cell is blank. -/
theorem lstep_right_end (h : simStep q σ = some (σ', q', true)) (L : List (SimSym c)) :
    lstep ⟨q, L, σ, []⟩ = some ⟨q', σ' :: L, .bk, []⟩ := by
  simp [lstep, h]


-- @@ L93-97 verbatim
/-- A left move with a recorded cell to enter. -/
theorem lstep_left (h : simStep q σ = some (σ', q', false)) (t : SimSym c)
    (L R : List (SimSym c)) :
    lstep ⟨q, t :: L, σ, R⟩ = some ⟨q', L, t, σ' :: R⟩ := by
  simp [lstep, h]


-- @@ L99-102 verbatim
/-- A left move off the recorded region: the entered cell is blank. -/
theorem lstep_left_end (h : simStep q σ = some (σ', q', false)) (R : List (SimSym c)) :
    lstep ⟨q, [], σ, R⟩ = some ⟨q', [], .bk, σ' :: R⟩ := by
  simp [lstep, h]


-- @@ L104-112 verbatim
/-- A right move into a run of blanks – recorded or materialized, the
entered cell is blank either way. -/
theorem lstep_right_pad (h : simStep q σ = some (σ', q', true)) (L : List (SimSym c))
    (t : ℕ) :
    lstep ⟨q, L, σ, List.replicate t .bk⟩ =
      some ⟨q', σ' :: L, .bk, List.replicate (t - 1) .bk⟩ := by
  rcases t with - | t
  · exact lstep_right_end h L
  · exact lstep_right (h := h) L .bk (List.replicate t .bk)


-- @@ L114-122 verbatim
/-- A left move into a run of blanks – recorded or materialized, the entered
cell is blank either way. -/
theorem lstep_left_pad (h : simStep q σ = some (σ', q', false)) (g : ℕ)
    (R : List (SimSym c)) :
    lstep ⟨q, List.replicate g .bk, σ, R⟩ =
      some ⟨q', List.replicate (g - 1) .bk, .bk, σ' :: R⟩ := by
  rcases g with - | g
  · exact lstep_left_end h R
  · exact lstep_left (h := h) .bk (List.replicate g .bk) R


-- @@ L124-124 verbatim
end Steps


-- @@ L126-126 verbatim
/-! ### Reachability -/


-- @@ L128-128 verbatim
namespace Reach


-- @@ L130-130 verbatim
theorem refl (x : LCfg c) : Reach x x := Relation.ReflTransGen.refl


-- @@ L132-133 verbatim
theorem single {x y : LCfg c} (h : lstep x = some y) : Reach x y :=
  Relation.ReflTransGen.single h


-- @@ L135-136 verbatim
theorem head {x y z : LCfg c} (h : lstep x = some y) (hr : Reach y z) : Reach x z :=
  Relation.ReflTransGen.head h hr


-- @@ L138-139 verbatim
theorem trans {x y z : LCfg c} (h : Reach x y) (h' : Reach y z) : Reach x z :=
  Relation.ReflTransGen.trans h h'


-- @@ L141-141 verbatim
end Reach


-- @@ L143-143 verbatim
/-! ### Counted steps, and determinism -/


-- @@ L145-153 verbatim
/-- A counted run, extended by one step at its end. -/
theorem stepsTo.trans_step : ∀ {n : ℕ} {x y z : LCfg c},
    stepsTo n x y → lstep y = some z → stepsTo (n + 1) x z := by
  intro n
  induction n with
  | zero => intro x y z hxy hyz; exact ⟨z, by rw [show x = y from hxy]; exact hyz, rfl⟩
  | succ n ih =>
    rintro x y z ⟨d, hstep, hrest⟩ hyz
    exact ⟨d, hstep, ih hrest hyz⟩


-- @@ L155-167 verbatim
/-- Counted runs compose. -/
theorem stepsTo.trans : ∀ {n m : ℕ} {x y z : LCfg c},
    stepsTo n x y → stepsTo m y z → stepsTo (n + m) x z := by
  intro n
  induction n with
  | zero =>
    intro m x y z hxy hyz
    rw [show x = y from hxy, Nat.zero_add]
    exact hyz
  | succ n ih =>
    rintro m x y z ⟨d, hstep, hrest⟩ hyz
    rw [Nat.succ_add]
    exact ⟨d, hstep, ih hrest hyz⟩


-- @@ L169-183 verbatim
/-- Reachability is a counted run of some length. -/
theorem reach_iff_stepsTo {x y : LCfg c} : Reach x y ↔ ∃ n, stepsTo n x y := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | tail _ hstep ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, hn.trans_step hstep⟩
  · rintro ⟨n, hn⟩
    induction n generalizing x with
    | zero => exact (show x = y from hn) ▸ Reach.refl x
    | succ n ih =>
      obtain ⟨d, hstep, hrest⟩ := hn
      exact Reach.head hstep (ih hrest)


-- @@ L185-203 verbatim
/-- **The machine is deterministic**: a counted run to anywhere follows the
run to a terminal configuration, step for step. -/
theorem stepsTo_det : ∀ {m n : ℕ} {x y z : LCfg c},
    stepsTo m x y → stepsTo n x z → m ≤ n → stepsTo (n - m) y z := by
  intro m
  induction m with
  | zero =>
    intro n x y z hxy hxz _
    rw [Nat.sub_zero, ← show x = y from hxy]
    exact hxz
  | succ m ih =>
    rintro n x y z ⟨d, hstep, hrest⟩ hxz hmn
    rcases n with - | n
    · omega
    obtain ⟨d', hstep', hrest'⟩ := hxz
    rw [hstep] at hstep'
    obtain rfl : d = d' := Option.some_injective _ hstep'
    rw [Nat.succ_sub_succ]
    exact ih hrest hrest' (by omega)


-- @@ L205-217 verbatim
/-- A run cannot leave a terminal configuration, so it is at least as long as
any run from the same start. -/
theorem le_of_stepsTo_terminal : ∀ {n m : ℕ} {x y z : LCfg c},
    stepsTo n x y → lstep y = none → stepsTo m x z → m ≤ n := by
  intro n m x y z hxy hy hxz
  by_contra hcon
  have h := stepsTo_det hxy hxz (by omega)
  rcases hd : m - n with - | d
  · omega
  · rw [hd] at h
    obtain ⟨e, hstep, -⟩ := h
    rw [hy] at hstep
    exact absurd hstep (by simp)


-- @@ L219-224 verbatim
/-! ### The walk combinators

A state that passes a set of letters unchanged in one direction crosses any
run of them. The head starts *on* the first letter of the run and ends on the
first letter beyond it; the crossed letters pile up behind the head in
reverse. -/


-- @@ L226-226 verbatim
section Walk


-- @@ L228-228 verbatim
variable {q : SimQ c} {P : SimSym c → Prop} {f : SimSym c → SimSym c}


-- @@ L230-246 verbatim
/-- **Walking right** over a run of passed letters, rewriting each by `f` –
the transducing form: erasure sweeps take `f := fun _ => .bk`, unpriming
takes the unpriming map. -/
theorem reach_walkR_map (hq : ∀ σ, P σ → simStep q σ = some (f σ, q, true)) :
    ∀ (w : List (SimSym c)), (∀ σ ∈ w, P σ) → ∀ {s : SimSym c}, P s →
      ∀ (L : List (SimSym c)) (t : SimSym c) (R : List (SimSym c)),
      Reach ⟨q, L, s, w ++ t :: R⟩ ⟨q, (w.map f).reverse ++ f s :: L, t, R⟩ := by
  intro w
  induction w with
  | nil =>
    intro _ s hs L t R
    exact Reach.single (lstep_right (hq s hs) L t R)
  | cons a w ih =>
    intro hw s hs L t R
    refine Reach.head (lstep_right (hq s hs) L a (w ++ t :: R)) ?_
    have h := ih (fun σ hσ => hw σ (by simp [hσ])) (hw a (by simp)) (f s :: L) t R
    simpa using h


-- @@ L248-262 verbatim
/-- **Walking left** over a run of passed letters, rewriting each by `f`. -/
theorem reach_walkL_map (hq : ∀ σ, P σ → simStep q σ = some (f σ, q, false)) :
    ∀ (w : List (SimSym c)), (∀ σ ∈ w, P σ) → ∀ {s : SimSym c}, P s →
      ∀ (t : SimSym c) (L R : List (SimSym c)),
      Reach ⟨q, w ++ t :: L, s, R⟩ ⟨q, L, t, (w.map f).reverse ++ f s :: R⟩ := by
  intro w
  induction w with
  | nil =>
    intro _ s hs t L R
    exact Reach.single (lstep_left (hq s hs) t L R)
  | cons a w ih =>
    intro hw s hs t L R
    refine Reach.head (lstep_left (hq s hs) a (w ++ t :: L) R) ?_
    have h := ih (fun σ hσ => hw σ (by simp [hσ])) (hw a (by simp)) t L (f s :: R)
    simpa using h


-- @@ L264-271 verbatim
/-- **Walking right** over a run of passed letters, unchanged. -/
theorem reach_walkR (hq : ∀ σ, P σ → simStep q σ = some (σ, q, true)) :
    ∀ (w : List (SimSym c)), (∀ σ ∈ w, P σ) → ∀ {s : SimSym c}, P s →
      ∀ (L : List (SimSym c)) (t : SimSym c) (R : List (SimSym c)),
      Reach ⟨q, L, s, w ++ t :: R⟩ ⟨q, w.reverse ++ s :: L, t, R⟩ := by
  intro w hw s hs L t R
  have h := reach_walkR_map (f := id) (fun σ hσ => hq σ hσ) w hw hs L t R
  simpa using h


-- @@ L273-280 verbatim
/-- **Walking left** over a run of passed letters, unchanged. -/
theorem reach_walkL (hq : ∀ σ, P σ → simStep q σ = some (σ, q, false)) :
    ∀ (w : List (SimSym c)), (∀ σ ∈ w, P σ) → ∀ {s : SimSym c}, P s →
      ∀ (t : SimSym c) (L R : List (SimSym c)),
      Reach ⟨q, w ++ t :: L, s, R⟩ ⟨q, L, t, w.reverse ++ s :: R⟩ := by
  intro w hw s hs t L R
  have h := reach_walkL_map (f := id) (fun σ hσ => hq σ hσ) w hw hs t L R
  simpa using h


-- @@ L282-282 verbatim
end Walk


-- @@ L284-284 verbatim
end HaltHard


-- @@ L286-286 verbatim
end DescriptiveComplexity
