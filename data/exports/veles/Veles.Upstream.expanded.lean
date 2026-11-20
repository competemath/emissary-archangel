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
import Mathlib


-- @@ L18-36 verbatim
/-!
# Upstream definitions

Copied verbatim from google-deepmind/formal-conjectures (Apache-2.0, notice above),
commit 137aec5c7abd3aa61f7a73138a97279acfc79e93 (snapshots in `upstream/`):

* `SimpleGraph.johnson` and the `J(n, k)` notation, from
  `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Johnson.lean`;
* `Erdos835.Property` and `Erdos835.johnsonBound`, from
  `FormalConjectures/ErdosProblems/835.lean`;
* `SteinerSystems.SteinerSystem`, the `S(t, k, n)` notation and
  `SteinerSystems.LargeSteinerSystemWitness`, from
  `FormalConjectures/Wikipedia/SteinerSystem.lean`.

Changes: the module header, `public import` lines and `@[expose] public section`
are dropped, and `import Mathlib` replaces the upstream imports. Every copied
declaration block is byte-identical to upstream; `scripts/check_upstream.py`
tests this.
-/


-- @@ L38-38 verbatim
open Finset


-- @@ L40-40 verbatim
namespace SimpleGraph

-- @@ L41-41 verbatim
variable {n k : ℕ}


-- @@ L43-51 verbatim
/--
The Johnson graph $J(n, k)$ has as vertices the $k$-subsets of an $n$-set.
Two vertices are adjacent if their intersection has size $k - 1$.
-/
@[simps -isSimp]
def johnson (n k : ℕ) : SimpleGraph {s : Finset (Fin n) // #s = k} where
  Adj s t := #(s.val ∩ t.val) + 1 = k
  symm.symm s t h := by simpa [inter_comm]
  loopless.irrefl := by simp +contextual


-- @@ L53-53 verbatim
scoped notation "J(" n ", " k ")" => johnson n k


-- @@ L55-55 verbatim
end SimpleGraph


-- @@ L57-57 verbatim
open SimpleGraph

-- @@ L58-58 verbatim
open scoped Nat

-- @@ L59-59 verbatim
namespace Erdos835


-- @@ L61-61 verbatim
variable {n k : ℕ}


-- @@ L63-71 verbatim
/--
The property that for a given $k$, the $k$-subsets of a $2k$-set can be colored with $k+1$ colors
such that any $(k+1)$-subset contains all colors.
-/
def Property (k : ℕ) : Prop :=
  let K := {s : Finset (Fin (2 * k)) // s.card = k}
  ∃ c : K → Fin (k + 1),
    ∀ A : Finset (Fin (2 * k)), A.card = k + 1 →
      (image c {s : K | s.val ⊂ A}) = (univ : Finset (Fin (k+1)))


-- @@ L73-80 verbatim
/-- Johnson's upper bound on the maximum size `A(n, d, w)` of a `n`-dimensional binary code of
distance `d` and weight `w` is as follows:
* If `d > 2 * w`, then `A(n, d, w) = 1`.
* If `d ≤ 2 * w`, then `A(n, d, w) ≤ ⌊n / w * A(n - 1, d, w - 1)⌋`. -/
def johnsonBound : ℕ → ℕ → ℕ → ℕ
  | 0, _d, _w => 1
  | _n, _d, 0 => 1
  | n + 1, d, w + 1 => if 2 * (w + 1) < d then 1 else (n + 1) * johnsonBound n d w / (w + 1)


-- @@ L82-82 verbatim
end Erdos835


-- @@ L84-84 verbatim
namespace SteinerSystems


-- @@ L86-103 verbatim
/--
An $S(t, k, n)$-Steiner system is a collection of $k$-element subsets (called blocks) of
$\{0, \ldots, n-1\}$ such that every $t$-element subset is contained in exactly one block.

This is the standard notation from combinatorics, where:
- $n$ is the number of points
- $k$ is the block size
- $t$ is the covering parameter (every $t$-subset is in exactly one block)
-/
structure SteinerSystem (t k n : ℕ) where
  /-- The blocks of the Steiner system. -/
  blocks : Finset (Finset (Fin n))
  /-- Every block has exactly $k$ elements. -/
  block_card : ∀ B ∈ blocks, B.card = k
  /-- Every $t$-element subset is contained in exactly one block.
  Note: We use `.filter.card = 1` instead of `∃!` because `∃! B ∈ blocks, R ⊆ B` desugars to
  a quantifier over all `Finset (Fin n)`, which loses `Decidable` and breaks `native_decide`. -/
  cover_unique : ∀ R : Finset (Fin n), R.card = t → (blocks.filter (R ⊆ ·)).card = 1


-- @@ L105-107 verbatim
/-- Notation for Steiner systems: `S(t, k, n)` denotes a Steiner system with
covering parameter `t`, block size `k`, and `n` points. -/
scoped notation "S(" t ", " k ", " n ")" => SteinerSystem t k n


-- @@ L109-126 verbatim
/--
A constructive witness for a large Steiner system: concrete values of $n$, $k$, $t$
satisfying $n > k > t > 5$, $t < 10$, $n < 200$, together with an explicit Steiner system.
-/
structure LargeSteinerSystemWitness where
  /-- The size of the ground set. -/
  n : ℕ
  /-- The block size. -/
  k : ℕ
  /-- The covering parameter. -/
  t : ℕ
  h_nk : n > k
  h_kt : k > t
  h_t_lower : t > 5
  h_t_upper : t < 10
  h_n_upper : n < 200
  /-- The explicit Steiner system. -/
  system : S(t, k, n)


-- @@ L128-128 verbatim
end SteinerSystems
