import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination


-- @@ L8-8 verbatim
namespace OAI


-- @@ L10-17 verbatim
/-!
# The zero-fiber elimination

The quotient by the specialized defining equation of Section 2 is a polynomial
algebra in three independent variables.  The construction is an algebra
isomorphism, not merely a bijection on points, and works over any commutative
coefficient ring.
-/


-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
namespace StableCoordinate.ZeroFiber


-- @@ L23-23 verbatim
open MvPolynomial


-- @@ L25-25 verbatim
variable (K : Type*) [CommRing K]


-- @@ L27-27 verbatim
abbrev Four := MvPolynomial (Fin 4) K

-- @@ L28-28 verbatim
abbrev Three := MvPolynomial (Fin 3) K


-- @@ L30-30 verbatim
def squareDifference : Four K := X 0 ^ 2 - X 1 ^ 2


-- @@ L32-33 verbatim
def relation : Four K :=
  squareDifference K ^ 2 * X 2 - (1 + 2 * X 0 * squareDifference K) * X 3 - X 1


-- @@ L35-35 verbatim
def relationIdeal : Ideal (Four K) := Ideal.span {relation K}


-- @@ L37-37 verbatim
abbrev Ring := Four K ⧸ relationIdeal K


-- @@ L39-39 verbatim
def qmk : Four K →ₐ[K] Ring K := Ideal.Quotient.mkₐ K _


-- @@ L41-44 verbatim
def forward : Four K →ₐ[K] Three K :=
  aeval ![X 0, X 1,
    4 * X 0 ^ 2 * X 1 + (1 + 2 * X 0 * (X 0 ^ 2 - X 1 ^ 2)) * X 2,
    -(1 - 2 * X 0 * (X 0 ^ 2 - X 1 ^ 2)) * X 1 + (X 0 ^ 2 - X 1 ^ 2) ^ 2 * X 2]


-- @@ L46-50 verbatim
lemma forward_relation : forward K (relation K) = 0 := by
  simp only [forward, relation, squareDifference, map_sub, map_add, map_mul, map_pow,
    map_ofNat, aeval_X, map_one]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring


-- @@ L52-59 verbatim
lemma forward_vanishes : ∀ a ∈ relationIdeal K, forward K a = 0 := by
  intro a ha
  have h : relationIdeal K ≤ RingHom.ker (forward K).toRingHom := by
    rw [relationIdeal, Ideal.span_le]
    intro b hb
    rcases Set.mem_singleton_iff.mp hb with rfl
    exact forward_relation K
  exact h ha


-- @@ L61-62 verbatim
def toThree : Ring K →ₐ[K] Three K :=
  Ideal.Quotient.liftₐ _ (forward K) (forward_vanishes K)


-- @@ L64-64 verbatim
@[simp] lemma toThree_qmk (a : Four K) : toThree K (qmk K a) = forward K a := rfl


-- @@ L66-68 verbatim
def backward : Three K →ₐ[K] Ring K :=
  aeval ![qmk K (X 0), qmk K (X 1),
    qmk K ((1 - 2 * X 0 * squareDifference K) * X 2 + 4 * X 0 ^ 2 * X 3)]


-- @@ L70-73 verbatim
lemma forward_backward : (toThree K).comp (backward K) = AlgHom.id K (Three K) := by
  ext i : 1
  fin_cases i <;> simp [backward, forward, squareDifference, map_ofNat]
  ring


-- @@ L75-77 verbatim
lemma qmk_relation : qmk K (relation K) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (Set.mem_singleton _)


-- @@ L79-92 verbatim
lemma backward_forward : (backward K).comp (toThree K) = AlgHom.id K (Ring K) := by
  apply Ideal.Quotient.algHom_ext
  ext i : 1
  change backward K (toThree K (qmk K (X i))) = qmk K (X i)
  rw [toThree_qmk]
  fin_cases i <;> simp [forward, backward, map_ofNat]
  · have h := qmk_relation K
    simp only [relation, squareDifference, map_sub, map_add, map_mul, map_pow,
      map_ofNat, map_one] at h ⊢
    linear_combination -4 * (qmk K (X 0)) ^ 2 * h
  · have h := qmk_relation K
    simp only [relation, squareDifference, map_sub, map_add, map_mul, map_pow,
      map_ofNat, map_one] at h ⊢
    linear_combination (1 - 2 * qmk K (X 0) * (qmk K (X 0) ^ 2 - qmk K (X 1) ^ 2)) * h


-- @@ L94-97 verbatim
/-- The zero fiber of the five-generator hypersurface presentation is affine
three-space, expressed by an isomorphism of coordinate algebras. -/
def presentationEquiv : Ring K ≃ₐ[K] Three K :=
  AlgEquiv.ofAlgHom (toThree K) (backward K) (forward_backward K) (backward_forward K)


-- @@ L99-99 verbatim
end StableCoordinate.ZeroFiber


-- @@ L101-101 verbatim
end


-- @@ L103-103 verbatim
end OAI
