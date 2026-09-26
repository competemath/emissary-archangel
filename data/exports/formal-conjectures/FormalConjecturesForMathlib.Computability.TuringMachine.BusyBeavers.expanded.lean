/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import FormalConjecturesForMathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Computability.TuringMachine.StackTuringMachine
public import Mathlib.Data.ENat.Lattice


-- @@ L22-22 verbatim
@[expose] public section



-- @@ L25-37 verbatim
/-! # Turing Machines, Busy Beaver version.
A variant on the definition of the TM0 model in Mathlib: while the statements the
`TM` can make in the usual `TM0` are split into two categories (either write at the
current position or move left/right), we want to combine the two to stick to the
`BB` convention: first write at the current position and then move left/right.

Note that this Turing Machine model also works with states of type `Option Γ`. This
is because in the busy beaver context, the turing machines also have an addition
"halting" state

See also https://git.sr.ht/~vigoux/busybeaver for a different approach to formalising
these objects.
-/


-- @@ L39-39 verbatim
namespace Turing


-- @@ L41-41 verbatim
open Mathlib

-- @@ L42-42 verbatim
open Relation StateTransition


-- @@ L44-44 verbatim
open Nat


-- @@ L46-48 verbatim
namespace BusyBeaver

-- type of tape symbols

-- @@ L49-51 verbatim
variable (Γ : Type*)

-- type of "labels" or TM states

-- @@ L52-52 verbatim
variable (Λ : Type*)


-- @@ L54-59 verbatim
/-- A Turing machine "statement" is just a command to write a symbol on the tape
(at the current position) and then move left or right. -/
structure Stmt where write ::
  symbol : Γ
  dir : Dir
deriving Inhabited


-- @@ L61-76 verbatim
/-- A Post-Turing machine with symbol type `Γ` and label type `Λ`
  is a function which, given the current state `q : Λ` and
  the tape head `a : Γ`, either halts (returns `none`) or returns
  a new state `q' : Option Λ` and a `Stmt` describing what to do: a
  command to write a symbol and move left or right. Notice that there
  are two ways of halting at a given `(state, head)` pair: either
  the machine halts immediately (i.e. the function returns `none`),
  or the machine moves to the "halting state", i.e. `none : Option Λ`
  and performs one last action.

  Typically, both `Λ` and `Γ` are required to be inhabited; the default value
  for `Γ` is the "blank" tape value, and the default value of `Λ` is
  the initial state. -/
@[nolint unusedArguments]
def Machine [Inhabited Λ] :=
  Λ → Γ → Option (Option Λ × Stmt Γ)


-- @@ L78-79 verbatim
instance Machine.inhabited [Inhabited Λ] : Inhabited (Machine Γ Λ) := by
  unfold Machine; infer_instance


-- @@ L81-92 verbatim
/-- The configuration state of a Turing machine during operation
  consists of a label (machine state), and a tape.
  The tape is represented in the form `(a, L, R)`, meaning the tape
  looks like `L.rev ++ [a] ++ R` with the machine currently reading
  the `a`. The lists are automatically extended with blanks as the
  machine moves around. -/
@[ext]
structure Cfg [Inhabited Γ] where
  /-- The current machine state. -/
  q : Option Λ
  /-- The current state of the tape: current symbol, left and right parts. -/
  tape : Tape Γ


-- @@ L94-94 verbatim
variable {Γ Λ}

-- @@ L95-95 verbatim
variable [Inhabited Λ]


-- @@ L97-97 verbatim
variable [Inhabited Γ]


-- @@ L99-99 verbatim
instance Cfg.inhabited : Inhabited (Cfg Γ Λ) := ⟨⟨default, default⟩⟩


-- @@ L101-101 verbatim
namespace Machine


-- @@ L103-108 verbatim
/-- Execution semantics of the Turing machine. -/
def step (M : Machine Γ Λ) : Cfg Γ Λ → Option (Cfg Γ Λ)
| ⟨none, _⟩ => none
| ⟨some q, T⟩ => (M q T.1).map
    fun ⟨q', a⟩ ↦ ⟨q', match a with
    | Stmt.write a d => (T.write a).move d⟩


-- @@ L110-112 verbatim
/-- The statement `Reaches M s₁ s₂` means that `s₂` is obtained
  starting from `s₁` after a finite number of steps from `s₂`. -/
def Reaches (M : Machine Γ Λ) : Cfg Γ Λ → Cfg Γ Λ → Prop := ReflTransGen fun a b ↦ b ∈ step M a


-- @@ L114-115 verbatim
/-- The initial configuration. -/
def init (l : List Γ) : Cfg Γ Λ := ⟨some default, Tape.mk₁ l⟩


-- @@ L117-120 verbatim
/-- Evaluate a Turing machine on initial input to a final state,
  if it terminates. -/
def eval (M : Machine Γ Λ) (l : List Γ) : Part (ListBlank Γ) :=
  (StateTransition.eval (step M) (init l)).map fun c ↦ c.tape.right₀


-- @@ L122-123 verbatim
def multiStep (M : Machine Γ Λ) (config : Cfg Γ Λ) (n : ℕ) : Option (Cfg Γ Λ) :=
    (Option.bind · (step M))^[n] config


-- @@ L125-127 verbatim
@[simp]
lemma multiStep_zero (M : Machine Γ Λ) (config : Cfg Γ Λ) : M.multiStep config 0 = some config :=
  rfl


-- @@ L129-131 verbatim
@[simp]
lemma multiStep_one (M : Machine Γ Λ) (config : Cfg Γ Λ) : M.multiStep config 1 = M.step config :=
  rfl


-- @@ L133-136 verbatim
@[simp]
lemma multiStep_succ (M : Machine Γ Λ) (config : Cfg Γ Λ) (n : ℕ) :
    M.multiStep config (n + 1) = Option.bind (M.multiStep config n) M.step := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]


-- @@ L138-146 verbatim
@[simp]
lemma multiStep_eq_none_mono {M : Machine Γ Λ} {config : Cfg Γ Λ} {m n : ℕ}
    (H : M.multiStep config n = none) (hnm : n ≤ m) :
    M.multiStep config m = none := by
  induction hnm with
  | refl => exact H
  | @step m hnm H =>
    rw [multiStep_succ, H]
    rfl


-- @@ L148-148 verbatim
variable {Γ Λ : Type*} [Inhabited Λ] [Inhabited Γ]

-- @@ L149-149 verbatim
variable (M : Machine Γ Λ)


-- @@ L151-157 verbatim
/--
`M.IsHaltingInput l` is the predicate that `M` is a halting configuration for `M`.
-/
def IsHaltingInput (l : List Γ) : Prop := (eval M l).Dom


-- TODO(Paul-Lez): Do we actually need this?

-- @@ L158-161 verbatim
/--
`M.HaltsAtConfiguration s` is the predicate that `M` is a halting configuration for `M`.
-/
def IsHaltingConfiguration (s : Cfg Γ Λ) : Prop := (step M s).isNone


-- @@ L163-167 verbatim
/--
The property that a Turing Machine `M` eventually halts when starting from an empty tape
-/
class IsHalting : Prop where
  halts : M.IsHaltingInput []


-- @@ L169-174 verbatim
/--
The predicate that a machine starting at configuration `s` stops after at most `n` steps, i.e.
reaches a configuration from which there are no defined transitions.
-/
def HaltsAfter (s : Cfg Γ Λ) (n : ℕ) : Prop :=
  M.multiStep s (n+1) = none


-- @@ L176-178 verbatim
lemma haltsAfter_zero_iff (s : Cfg Γ Λ) :
    HaltsAfter M s 0 ↔ step M s = none := by
  rw [HaltsAfter, multiStep, Function.iterate_one, Option.bind_some]


-- @@ L180-181 verbatim
lemma isHalting_iff_exists_haltsAt : IsHalting M ↔ ∃ n, M.HaltsAfter (init []) n :=
  ⟨fun _ ↦ eval_dom_iff.mpr IsHalting.halts, fun H ↦ ⟨eval_dom_iff.mp H⟩⟩


-- @@ L183-193 verbatim
lemma exists_of_not_haltsAfter (s : Cfg Γ Λ) (n : ℕ) (H : ¬M.HaltsAfter s n) :
    ∃ (a : Λ) (b : Tape Γ), M.multiStep s n = some ⟨a, b⟩ := by
  contrapose! H
  rw [HaltsAfter, multiStep_succ]
  obtain H | ⟨⟨u, u'⟩, hu⟩ := (Option.eq_none_or_eq_some (M.multiStep s n))
  · simp [H]
  · suffices u = none by rw [hu, this] ; rfl
    rw [Option.eq_none_iff_forall_ne_some]
    intro a hc
    subst hc
    simp [hu] at H ⊢


-- @@ L195-199 verbatim
lemma not_isHalting_iff_forall_isSome_multiStep :
    ¬ IsHalting M ↔ ∀ n, M.multiStep (init []) (n + 1) |>.isSome := by
  simp_rw [isHalting_iff_exists_haltsAt, HaltsAfter, Option.isSome_iff_ne_none]
  push Not
  rfl


-- @@ L201-213 verbatim
lemma not_isHalting_of_forall_isSome (H : ∀ l s, ∃ a b, M l s = some (some a, b)) :
    ¬IsHalting M := by
  rw [not_isHalting_iff_forall_isSome_multiStep]
  intro n
  induction n with
  | zero =>
    obtain ⟨a, b, H⟩ := H default (Tape.mk₁ []).head
    simp [init, step, H]
  | succ n ih =>
    obtain ⟨a, b, hab⟩ := exists_of_not_haltsAfter _ _ _ (by rwa [Option.isSome_iff_ne_none] at ih)
    obtain ⟨c, d, hcd⟩ := H a b.head
    obtain ⟨e, f, hef⟩ := H c (Tape.move d.dir (Tape.write d.symbol b)).head
    simp [multiStep_succ, multiStep_succ, hab, step, hcd, hef]


-- @@ L215-218 verbatim
noncomputable def haltingNumber : ENat :=
  -- The smallest `n` such that `M` halts after `n` steps when starting from an empty tape.
  -- If no such `n` exists then this is equal to `⊤`.
  sInf {(n : ENat) |  (n : ℕ) (_ : HaltsAfter M (init []) n) }


-- @@ L220-227 verbatim
theorem haltingNumber_def (n : ℕ) (hn : ∃ a, M.multiStep (init []) n = some a)
    (ha' : M.multiStep (init []) (n + 1) = none) :
    M.haltingNumber = n := by
  refine IsGLB.sInf_eq (IsLeast.isGLB ⟨⟨n, by rwa [HaltsAfter], rfl⟩, fun m ⟨k, _, _⟩ ↦ ?_⟩)
  cases m
  · exact le_top
  · by_contra! hc
    simp_all [multiStep_eq_none_mono ‹_› (show k + 1 ≤ n by aesop)]


-- @@ L229-229 verbatim
end Machine


-- @@ L231-231 verbatim
end BusyBeaver


-- @@ L233-233 verbatim
end Turing
