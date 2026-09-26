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

public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Set.Card
import Mathlib.Tactic.IntervalCases


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-34 verbatim
/-! # Arithmetic Progressions

Main definitions:
- `Set.IsAPOfLengthWith (s : Set α) (l : ℕ∞) (a d : α)` : predicate asserting that `s` is the
  set consisting of an arithmetic progression of length `l` (possibly infinite) with first term
  `a` and difference `d`. Useful for cases in which additional conditions need to be applied to
  the individual terms and/or difference.
- `Set.IsAPOfLength (s : Set α) (l : ℕ∞)` : predicate asserting that `s` is the set consisting
  of an arithmetic progression of length `l`, for some some first term and difference.
-/


-- @@ L36-36 verbatim
variable {α : Type*} [AddCommMonoid α]


-- @@ L38-45 verbatim
/--
A set $S$ is an arithmetic progression of length $l$ with first term $a$ and difference $d$
if $S = \{a, a + d, ..., a + (l - 1)d\}$, if $l$ if finite, else $S = \{a, a + d, a + 2d, ...\}.
This can be written as `s.IsAPOfLengthWith l a d`, where `l : ℕ∞` may take the infinite
value `⊤`.
-/
def Set.IsAPOfLengthWith (s : Set α) (l : ℕ∞) (a d : α) : Prop :=
  ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}


-- @@ L47-52 verbatim
/--
A list version of `Set.IsAPOfLengthWith`. Useful when order preservation is required, for example
when considering images under arbitrary functions.
-/
def List.IsAPOfLengthWith (s : List α) (l : ℕ) (a d : α) : Prop :=
  s = (List.range l).map (fun n ↦ a + n • d) ∨ s = (List.range l).reverse.map (fun n ↦ a + n • d)


-- @@ L54-54 verbatim
namespace Set.IsAPOfLengthWith


-- @@ L56-56 verbatim
variable {s : Set α} {l : ℕ∞} {a d : α}


-- @@ L58-58 verbatim
theorem card (h : s.IsAPOfLengthWith l a d) : ENat.card s = l := h.1

-- @@ L59-59 verbatim
theorem eq (h : s.IsAPOfLengthWith l a d) : s = {a + n • d | (n : ℕ) (_ : n < l)} := h.2


-- @@ L61-64 verbatim
/-- An arithmetic progression with first term `a` and difference `d` is of length zero if and only
if `s` is empty. -/
@[simp]
theorem zero : s.IsAPOfLengthWith 0 a d ↔ s = ∅ := by simp [IsAPOfLengthWith]


-- @@ L66-69 verbatim
/-- An arithmetic progression with first term `a` and difference `d` is of length one if and only
if `s` is a singleton. -/
@[simp]
theorem one : s.IsAPOfLengthWith 1 a d ↔ s = {a} := by simp +contextual [IsAPOfLengthWith]


-- @@ L71-71 verbatim
end Set.IsAPOfLengthWith


-- @@ L73-73 verbatim
namespace List.IsAPOfLengthWith


-- @@ L75-75 verbatim
variable {s : List α} {l : ℕ} {a d : α}


-- @@ L77-78 verbatim
theorem length (h : s.IsAPOfLengthWith l a d) : s.length = l := by
  cases h <;> simp_all


-- @@ L80-84 verbatim
/-- An arithmetic progression with first term `a` and difference `d` is of length zero if and only
if `s` is empty. -/
@[simp]
theorem zero : s.IsAPOfLengthWith 0 a d ↔ s = [] := by
  simp [IsAPOfLengthWith]


-- @@ L86-90 verbatim
/-- An arithmetic progression with first term `a` and difference `d` is of length one if and only
if `s` is a singleton. -/
@[simp]
theorem one : s.IsAPOfLengthWith 1 a d ↔ s = [a] := by
  simp [IsAPOfLengthWith]


-- @@ L92-92 verbatim
end List.IsAPOfLengthWith


-- @@ L94-108 verbatim
/-- In an abelian additive group `α`, the set `{a, b}` with `a ≠ b` is an arithmetic progression of
length `2` with first term `a` and difference `b - a`. -/
theorem Set.isAPOfLengthWith_pair {α : Type*} [DecidableEq α] [AddCommGroup α]
    {a b : α} (hab : a ≠ b) :
    Set.IsAPOfLengthWith {a, b} 2 a (b - a) := by
  simp [IsAPOfLengthWith]
  rw [Finset.card_insert_of_notMem (by simpa only [Finset.mem_singleton])]
  simp
  refine Set.ext fun x => ⟨fun h ↦ ?_, fun ⟨n, ⟨_, _⟩⟩ ↦ by interval_cases n <;> simp_all⟩
  cases h with
  | inl hl => use 0; simp [hl]
  | inr hr => exact ⟨1, by norm_num, by simp_all⟩

-- Formalisation note: separate result needed for `ℕ` since this is not covered by
-- the `AddCommGroup` result above.

-- @@ L109-115 verbatim
/-- The set `{a, b} : Set ℕ` with `a < b` is an arithmetic progression of length `2` with
first term `a` and difference `b - a`. -/
theorem Nat.isAPOfLengthWith_pair {a b : ℕ} (hab : a < b) :
    Set.IsAPOfLengthWith {a, b} 2 a (b - a) := by
  let ⟨n, h⟩ := Nat.exists_eq_add_of_lt hab
  simp [Set.IsAPOfLengthWith, h, add_assoc]
  exact Set.ext fun x => ⟨fun a => by aesop, fun ⟨w, ⟨_, _⟩⟩ => by interval_cases w <;> simp_all⟩


-- @@ L117-123 verbatim
/--
The predicate that a set `s` is an arithmetic progression of length `l` (possibly infinite).
This predicate does not assert a specific value for the first term or the difference of the
arithmetic progression.
-/
def Set.IsAPOfLength (s : Set α) (l : ℕ∞) : Prop :=
  ∃ a d : α, s.IsAPOfLengthWith l a d


-- @@ L125-130 verbatim
/--
A list version of `Set.IsAPOfLength`. Useful when order preservation is required, for example
when considering images under arbitrary functions.
-/
def List.IsAPOfLength (s : List α) (l : ℕ) : Prop :=
  ∃ a d : α, s.IsAPOfLengthWith l a d


-- @@ L132-132 verbatim
namespace Set.IsAPOfLength


-- @@ L134-134 verbatim
open Set.IsAPOfLengthWith


-- @@ L136-136 verbatim
variable {s : Set α} {l : ℕ∞}


-- @@ L138-138 verbatim
theorem card (h : s.IsAPOfLength l) : ENat.card s = l := h.choose_spec.choose_spec.1


-- @@ L140-141 verbatim
theorem eq (h : s.IsAPOfLength l) : ∃ a d : α, s = {a + n • d | (n : ℕ) (_ : n < l)} :=
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.2⟩


-- @@ L143-144 verbatim
/-- Only the empty set is a finite arithmetic progression of length $0$. -/
@[simp] theorem zero : s.IsAPOfLength 0 ↔ s = ∅ := by simp [Set.IsAPOfLength]


-- @@ L146-147 verbatim
/-- Only singletons are finite arithmetic progressions of length $1$. -/
@[simp] theorem one : s.IsAPOfLength 1 ↔ ∃ a, s = {a} := by simp [IsAPOfLength]


-- @@ L149-154 verbatim
/-- If a set is an arithmetic progression of lengths `l₁` and `l₂`, then the lengths are
equal. -/
theorem congr {s : Set α} {l₁ l₂ : ℕ∞}
    (h₁ : s.IsAPOfLength l₁) (h₂ : s.IsAPOfLength l₂) :
    l₁ = l₂ := by
  rw [← h₁.card, h₂.card]


-- @@ L156-156 verbatim
end Set.IsAPOfLength


-- @@ L158-158 verbatim
namespace List.IsAPOfLength


-- @@ L160-160 verbatim
open List.IsAPOfLengthWith


-- @@ L162-162 verbatim
variable {s : List α} {l : ℕ}


-- @@ L164-166 verbatim
theorem length (h : s.IsAPOfLength l) : s.length = l := by
  obtain ⟨_, _, h⟩ := h
  exact h.length


-- @@ L168-169 verbatim
/-- Only the empty list is a finite arithmetic progression of length $0$. -/
@[simp] theorem zero : s.IsAPOfLength 0 ↔ s = [] := by simp [IsAPOfLength]


-- @@ L171-172 verbatim
/-- Only singletons are finite arithmetic progressions of length $1$. -/
@[simp] theorem one : s.IsAPOfLength 1 ↔ ∃ a, s = [a] := by simp [IsAPOfLength]


-- @@ L174-179 verbatim
/-- If a list is an arithmetic progression of lengths `l₁` and `l₂`, then the lengths are
equal. -/
theorem congr {s : List α} {l₁ l₂ : ℕ}
    (h₁ : s.IsAPOfLength l₁) (h₂ : s.IsAPOfLength l₂) :
    l₁ = l₂ := by
  rw [← h₁.length, h₂.length]


-- @@ L181-181 verbatim
end List.IsAPOfLength


-- @@ L183-185 verbatim
theorem Set.isAPOfLength_pair {α : Type*} [DecidableEq α] [AddCommGroup α] {a b : α} (hab : a ≠ b) :
    Set.IsAPOfLength {a, b} 2 :=
  ⟨a, b - a, Set.isAPOfLengthWith_pair hab⟩


-- @@ L187-189 verbatim
theorem Nat.isAPOfLength_pair {a b : ℕ} (hab : a < b) :
    Set.IsAPOfLength {a, b} 2 :=
  ⟨a, b - a, Nat.isAPOfLengthWith_pair hab⟩


-- @@ L191-194 verbatim
/-- The empty set is not an arithmetic progression of positive length. -/
theorem Set.not_isAPOfLength_empty {l : ℕ∞} (hl : 0 < l) :
    ¬Set.IsAPOfLength (∅ : Set α) l :=
  fun h ↦ by simp_all [h.congr <| Set.IsAPOfLength.zero.2 rfl]


-- @@ L196-199 verbatim
/-- We say that a set `s` is free of arithmetic progressions of length `l` if `s` contains no
non-trivial arithmetic progressions of length `l`. Written as `Set.IsAPOfLengthFree s l`. --/
def Set.IsAPOfLengthFree (s : Set α) (l : ℕ∞) : Prop :=
  ∀ t ⊆ s, t.IsAPOfLength l → l ≤ 1


-- @@ L201-203 verbatim
/-- Any set is free of arithmetic progressions of length `1`, because such APs are all trivial. -/
theorem Set.isAPOfLengthFree_one (s : Set α) : s.IsAPOfLengthFree 1 := by
  simp [Set.IsAPOfLengthFree]


-- @@ L205-207 verbatim
/-- Any set is free of arithmetic progressions of length `0`, because such APs are all trivial. -/
theorem Set.isAPOfLengthFree_zero (s : Set α) : s.IsAPOfLengthFree 0 := by
  simp [Set.IsAPOfLengthFree]


-- @@ L209-212 verbatim
/-- Any non-trivial arithmetic progression cannot be free of arithmetic progressions. -/
theorem Set.IsAPOfLength.not_isAPOfLengthFree {s : Set α} {l : ℕ∞}
    (hs : s.IsAPOfLength l) (hl : 1 < l) : ¬s.IsAPOfLengthFree l := by
  simpa [Set.IsAPOfLengthFree] using ⟨s, le_rfl, ⟨hs, hl⟩⟩


-- @@ L214-219 verbatim
/--
Define the largest possible size of a subset of $\{1, \dots, N\}$ that does not contain
any non-trivial $k$-term arithmetic progression.
-/
noncomputable def Set.IsAPOfLengthFree.maxCard (k : ℕ) (N : ℕ) : ℕ :=
  sSup {Finset.card S | (S) (_ : S ⊆ Finset.Icc 1 N) (_ : (S : Set ℕ).IsAPOfLengthFree k)}


-- @@ L221-226 verbatim
theorem Set.IsAPOfLengthFree.maxCard_zero (N : ℕ) : maxCard 0 N = N := by
  simp only [maxCard, Nat.cast_zero, isAPOfLengthFree_zero, exists_const, exists_prop]
  apply IsGreatest.csSup_eq
  refine ⟨⟨Finset.Icc 1 N, Subset.rfl, Nat.card_Icc _ _⟩, ?_⟩
  rintro n ⟨S, hS, rfl⟩
  exact S.card_mono hS |>.trans_eq (Nat.card_Icc _ _)


-- @@ L228-230 verbatim
theorem Set.IsAPOfLengthFree.maxCard_one (N : ℕ) : maxCard 1 N = N := by
  nth_rw 2 [← maxCard_zero N]
  simp [maxCard, isAPOfLengthFree_one, isAPOfLengthFree_zero]


-- @@ L232-234 verbatim
/-- A set `A` contains an arithmetic progression of length `k` with difference `d`. -/
def Set.ContainsAP (A : Set α) (k : ℕ) (d : α) : Prop :=
  ∃ a, ∃ s, s ⊆ A ∧ s.IsAPOfLengthWith (k : ℕ∞) a d


-- @@ L236-239 verbatim
def ContainsMonoAPofLength {κ : Type} [Finite κ] {M : Set α}
    (coloring : M → κ) (k : ℕ) : Prop :=
  ∃ c : κ, ∃ ap : Set M, ((·.1) '' ap).IsAPOfLength k ∧
    ∀ m ∈ ap, coloring m = c


-- @@ L241-247 verbatim
/--
A function `f : β → α` has a monotone `k`-term arithmetic progression if there exists a choice
of indices `b 1 < b 2 < ... < b k` such that the subsequence `f (b i)` forms an increasing or
decreasing arithmetic progression of length `k`.
-/
def HasMonotoneAP {β : Type*} [Preorder β] (f : β → α) (k : ℕ) : Prop :=
  ∃ l : List β, (l.map f).IsAPOfLength k ∧ l.Pairwise (· < ·)


-- @@ L249-255 verbatim
/--
Define the largest possible size of a subset of a finset `s` that does not contain
any non-trivial `k`-term arithmetic progression.
-/
noncomputable def Finset.maxAPFreeCard (k : ℕ) (s : Finset α) : ℕ :=
  open scoped Classical in
  (s.powerset.filter fun t : Finset α ↦ (t : Set α).IsAPOfLengthFree k).sup Finset.card
