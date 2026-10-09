import OAI.Analysis.MetricEntropy.SymmetricForms
import OAI.Analysis.MetricEntropy.FormDimension
import Mathlib.SetTheory.Cardinal.Finite


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
universe uK


-- @@ L9-16 verbatim
/-!
# Cardinality and dimension of actual symmetric multilinear forms

The coefficient count is transported through the proved linear equivalence
with permutation-invariant multilinear maps. No extra representation or
symmetry hypothesis is assumed. `Nat.card` avoids choosing a global
`Fintype` instance for the invariant-map submodule.
-/


-- @@ L18-18 verbatim
namespace MetricEntropyDuality


-- @@ L20-20 verbatim
namespace SymmetricForm


-- @@ L22-25 verbatim
/-- The cardinality of the coefficient carrier. -/
theorem card (p r j : ℕ) [NeZero p] :
    Fintype.card (SymmetricForm (ZMod p) r j) = p ^ formDimension r j :=
  card_form_coefficients p r j


-- @@ L27-32 verbatim
/-- Actual permutation-invariant multilinear maps have the same dimension
as their freely specified multiset coefficients. -/
theorem finrank_invariantMultilinearSubmodule (K : Type uK) [Field K] (r j : ℕ) :
    Module.finrank K (invariantMultilinearSubmodule K r j) = formDimension r j :=
  (equivInvariantMultilinear (K := K) (r := r) (j := j)).finrank_eq.symm.trans
    (finrank_form_coefficients K r j)


-- @@ L34-45 verbatim
/-- The actual invariant multilinear maps over `ZMod p` have cardinality
`p` raised to the symmetric-form dimension. -/
theorem natCard_invariantMultilinearSubmodule (p r j : ℕ) [NeZero p] :
    Nat.card (invariantMultilinearSubmodule (ZMod p) r j) =
      p ^ formDimension r j := by
  calc
    Nat.card (invariantMultilinearSubmodule (ZMod p) r j) =
        Nat.card (SymmetricForm (ZMod p) r j) :=
      Nat.card_congr
        (equivInvariantMultilinear (K := ZMod p) (r := r) (j := j)).toEquiv.symm
    _ = Fintype.card (SymmetricForm (ZMod p) r j) := Nat.card_eq_fintype_card
    _ = p ^ formDimension r j := card p r j


-- @@ L47-47 verbatim
end SymmetricForm


-- @@ L49-52 verbatim
/-- The cardinality of the symmetric-form coefficient space. -/
theorem card_symmetricForm (p r j : ℕ) [NeZero p] :
    Fintype.card (SymmetricForm (ZMod p) r j) = p ^ formDimension r j :=
  SymmetricForm.card p r j


-- @@ L54-54 verbatim
end MetricEntropyDuality


-- @@ L56-56 verbatim
end OAI
