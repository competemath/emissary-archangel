/-
Copyright (c) 2026 Tom Adamczewski and Epoch AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GPT-6 Astra, Tom Adamczewski
-/
module

public import LeanPool.Koethe.ShiftWitness.Band
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.LinearAlgebra.Matrix.Ideal
public import Mathlib.RingTheory.SimpleRing.Principal
import LeanPool.Koethe.ShiftWitness.Eigenvector
import LeanPool.Koethe.ShiftWitness.Endpoint


-- @@ L15-26 verbatim
/-!
# Downstream witness from a universal mortal sequence

The only theorem hypothesis in the final construction is scalar linearization,
stated at the concrete backward-shift operator algebra. The unrestricted
`nil_of_all_pencils_nil` theorem can be supplied directly to this hypothesis.
All window-to-polynomial and nonnilpotent-matrix bridges are proved here.

The witness ring is the unitization over `k` of the positive shift algebra,
and its nil ideal is the kernel of the scalar projection. The universe of the
existential witness is exactly the universe of the ground field.
-/


-- @@ L28-28 verbatim
@[expose] public section


-- @@ L30-30 verbatim
noncomputable section


-- @@ L32-32 verbatim
namespace KoetheCounterexample

-- @@ L33-33 verbatim
namespace ShiftWitness


-- @@ L35-35 verbatim
universe u

-- @@ L36-36 verbatim
variable {k : Type u} [Field k]


-- @@ L38-41 verbatim
/-- The `k`-module structure on the endomorphism algebra, chosen to be definitionally the
one coming from its `k`-algebra structure so that `NonUnitalSubalgebra` and `Module.End`
agree. -/
local instance moduleEnd : Module k (End (RatFunc k)) := Algebra.toModule


-- @@ L43-45 verbatim
/-- The positive algebra is generated over `k`, NOT over `RatFunc k`. -/
def positiveAlgebra (v : ℕ → Triple k) : NonUnitalSubalgebra k (End (RatFunc k)) :=
  NonUnitalAlgebra.adjoin k (Set.range (backShift (K := RatFunc k) v))


-- @@ L47-60 verbatim
/-- Once the positive shift algebra is nil, the rational-function eigenvector
gives a nil ideal and nonnilpotent matrix in its actual unitization. -/
theorem witness_from_nil_positive (v : ℕ → Triple k) (hv : ∀ n, v n ≠ 0)
    (hA : ∀ x ∈ positiveAlgebra v, IsNilpotent x) :
    ∃ (R : Type u) (_ : Ring R) (I : TwoSidedIdeal R),
      (∀ x ∈ I, IsNilpotent x) ∧
        ∃ W : Matrix (Fin 2) (Fin 2) R,
          W ∈ TwoSidedIdeal.matrix (Fin 2) I ∧ ¬ IsNilpotent W := by
  refine exists_witness_of_nil_subalgebra (positiveAlgebra v) hA
    (RingHom.id (End (RatFunc k))) (backShift (K := RatFunc k) v) ?_
    (RatFunc.X : RatFunc k) RatFunc.X_ne_zero (eigenvector v) (eigenvector_ne_zero v) ?_
  · intro i
    exact NonUnitalAlgebra.subset_adjoin k (Set.mem_range_self i)
  · simpa only [RingHom.id_apply] using combined_shift_eigenvector v hv


-- @@ L62-76 verbatim
/-- Universe-preserving existential form of the requested nil-ideal plus
nonnilpotent `Fin 2` matrix witness. Scalar linearization is an explicit theorem
argument, not an axiom. Only its specialization to the concrete operator algebra
is needed, so a universe-polymorphic linearization theorem plugs in directly. -/
theorem exists_nilideal_nonnil_matrix
    (v : ℕ → Triple k) (hv : UniversalMortalSequence k v)
    (hlinear : ∀ (a : Fin 3 → End (RatFunc k)),
      (∀ (d : ℕ) (P : Pencil k d), IsNilpotent (P.lift a)) →
        ∀ x ∈ NonUnitalAlgebra.adjoin k (Set.range a), IsNilpotent x) :
    ∃ (R : Type u) (_ : Ring R) (I : TwoSidedIdeal R),
      (∀ x ∈ I, IsNilpotent x) ∧
        ∃ W : Matrix (Fin 2) (Fin 2) R,
          W ∈ TwoSidedIdeal.matrix (Fin 2) I ∧ ¬ IsNilpotent W := by
  apply witness_from_nil_positive v hv.1
  exact hlinear (backShift v) (all_pencils_nil (K := RatFunc k) v hv)


-- @@ L78-78 verbatim
end ShiftWitness

-- @@ L79-79 verbatim
end KoetheCounterexample


-- @@ L81-81 verbatim
end
