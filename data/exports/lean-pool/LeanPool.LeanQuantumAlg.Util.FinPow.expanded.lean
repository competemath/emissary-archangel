/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Algebra.Group.Nat.Defs


-- @@ L12-26 verbatim
/-!
# Index plumbing for `Fin (2 ^ n)` registers (quantum-free)

The big-endian pairing of computational-basis labels used to compose qubit
registers, factored out of the quantum framework so it carries no dependency
on `Gate`/`PureState`.

## Main definition

- `LeanPool.LeanQuantumAlg.prodEquiv` — `Fin (2 ^ m) × Fin (2 ^ n) ≃ Fin (2 ^ (m + n))`,
  `(x, y) ↦ y + 2 ^ n * x`, so the first (lower-qubit-index) factor carries
  the most significant bits.

Pinned Mathlib API: `finProdFinEquiv` (`(x, y) ↦ y + n * x`), `finCongr`.
-/


-- @@ L28-28 verbatim
@[expose] public section


-- @@ L30-30 verbatim
namespace QuantumAlg


-- @@ L32-32 verbatim
variable {m n : ℕ}


-- @@ L34-37 verbatim
/-- Big-endian pairing of basis labels: `(x, y) ↦ y + 2 ^ n * x`, so the
first (lower-qubit-index) factor carries the most significant bits. -/
def prodEquiv : Fin (2 ^ m) × Fin (2 ^ n) ≃ Fin (2 ^ (m + n)) :=
  finProdFinEquiv.trans (finCongr (pow_add (2 : ℕ) m n).symm)


-- @@ L39-39 verbatim
end QuantumAlg
