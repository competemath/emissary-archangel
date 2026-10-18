import OAI.AlgebraicGeometry.StableCoordinate.ObstructionDefinitions
import OAI.AlgebraicGeometry.StableCoordinate.FiltrationSeparation
import OAI.AlgebraicGeometry.StableCoordinate.IntegerFiltrationDegree


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-14 verbatim
/-!
# A proper zeroth filtration layer in the actual source algebra

The two points `(p,s,u,F,J) = (0,0,0,0,0)` and `(0,0,0,1,0)` lie on
`H = 0`. They agree on every polynomial of source weight at most zero,
but not on `F`. Thus the zeroth layer of the actual quotient filtration is
proper, without any associated-graded presentation assumption.
-/


-- @@ L16-16 verbatim
noncomputable section


-- @@ L18-18 verbatim
namespace StableCoordinate.SourceFiltration


-- @@ L20-20 verbatim
open MvPolynomial

-- @@ L21-21 verbatim
open Obstruction Filtration


-- @@ L23-23 verbatim
variable (k : Type*) [CommRing k]


-- @@ L25-26 verbatim
/-- The actual quotient presentation homomorphism. -/
def presentation : P k 5 →ₐ[k] A k := Ideal.Quotient.mkₐ k (idealA k)


-- @@ L28-29 verbatim
/-- A line of points on `H = 0`, varying only the coordinate `F`. -/
def testPoint (t : k) : Fin 5 → k := ![0, 0, 0, t, 0]


-- @@ L31-32 verbatim
@[simp] theorem aeval_H_testPoint (t : k) : aeval (testPoint k t) (H k) = 0 := by
  simp [H, Hstar, xP, testPoint]


-- @@ L34-41 verbatim
/-- Evaluation on the actual hypersurface algebra along the test line. -/
def testEval (t : k) : A k →ₐ[k] k :=
  Ideal.Quotient.liftₐ (idealA k) (aeval (testPoint k t)) (by
    change idealA k ≤ RingHom.ker (aeval (testPoint k t)).toRingHom
    apply Ideal.span_le.mpr
    intro q hq
    rcases Set.mem_singleton_iff.mp hq with rfl
    exact aeval_H_testPoint k t)


-- @@ L43-44 verbatim
@[simp] theorem testEval_presentation (t : k) (q : P k 5) :
    testEval k t (presentation k q) = aeval (testPoint k t) q := rfl


-- @@ L46-49 verbatim
@[simp] theorem testEval_aX (t : k) (i : Fin 5) :
    testEval k t (aX k i) = testPoint k t i := by
  change aeval (testPoint k t) (X i) = _
  simp


-- @@ L51-66 verbatim
/-- Weight-zero bound removes dependence on `F` after setting `p=0`. -/
theorem testPoint_monomial_eq (t : k) (e : Fin 5 →₀ ℕ)
    (he : monomialWeight e ≤ 0) (c : k) :
    aeval (testPoint k t) (monomial e c) =
      aeval (testPoint k 0) (monomial e c) := by
  classical
  rw [aeval_monomial, aeval_monomial]
  congr 1
  rw [Finsupp.prod_fintype _ _ (by intros; simp),
    Finsupp.prod_fintype _ _ (by intros; simp)]
  by_cases h0 : e 0 = 0
  · have h3 : e 3 = 0 := by
      simp only [monomialWeight_apply, h0, Nat.cast_zero, sub_zero] at he
      omega
    simp [Fin.prod_univ_succ, testPoint, h3]
  · simp [Fin.prod_univ_succ, testPoint, zero_pow h0]


-- @@ L68-77 verbatim
/-- All evaluations along the test line agree on the zeroth polynomial layer. -/
theorem testPoint_eq_of_mem_piece_zero (t : k) {q : P k 5} (hq : q ∈ piece k 0) :
    aeval (testPoint k t) q = aeval (testPoint k 0) q := by
  induction hq using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨e, he, rfl⟩ := hq
    exact testPoint_monomial_eq k t e he 1
  | zero => simp
  | add q r hq hr ihq ihr => simp only [map_add, ihq, ihr]
  | smul c q hq ihq => simp only [map_smul, ihq]


-- @@ L79-83 verbatim
/-- The same constancy holds on the zeroth layer of the quotient filtration. -/
theorem testEval_eq_of_mem_zero_layer (t : k) {a : A k}
    (ha : a ∈ imagePiece (presentation k) 0) : testEval k t a = testEval k 0 a := by
  obtain ⟨q, hq, rfl⟩ := ha
  exact testPoint_eq_of_mem_piece_zero k t hq


-- @@ L85-90 verbatim
/-- The class `F` is genuinely not in the zeroth layer of the source algebra. -/
theorem F_not_mem_zero_layer [Nontrivial k] :
    aX k 3 ∉ imagePiece (presentation k) 0 := by
  intro h
  have he := testEval_eq_of_mem_zero_layer k 1 h
  simp [testPoint] at he


-- @@ L92-95 verbatim
/-- The class `F` belongs to the first layer of the source filtration. -/
theorem F_mem_one_layer : aX k 3 ∈ imagePiece (presentation k) 1 := by
  refine ⟨X 3, ?_, rfl⟩
  simpa [monomialWeight] using (X_mem_piece (K := k) 3)


-- @@ L97-105 verbatim
/-- Its least integer filtration index is exactly one. -/
theorem degree_F [Nontrivial k] :
    IntegerFiltration.degree (fun d => (imagePiece (presentation k) d : Set (A k)))
      (aX k 3) = 1 := by
  apply IntegerFiltration.degree_eq_of_least _ (F_mem_one_layer k)
  intro d hd
  by_contra h
  have hd0 : d ≤ 0 := by omega
  exact F_not_mem_zero_layer k (imagePiece_mono (presentation k) hd0 hd)


-- @@ L107-121 verbatim
/-- The zeroth layer, with its actual subalgebra structure. -/
def zeroLayerSubalgebra : Subalgebra k (A k) where
  carrier := imagePiece (presentation k) 0
  zero_mem' := (imagePiece (presentation k) 0).zero_mem
  add_mem' := fun ha hb => (imagePiece (presentation k) 0).add_mem ha hb
  one_mem' := ⟨1, one_mem_piece k, map_one (presentation k)⟩
  mul_mem' := fun ha hb => by
    change _ ∈ imagePiece (presentation k) 0
    simpa only [add_zero] using mul_mem_imagePiece (presentation k) ha hb
  algebraMap_mem' r := by
    change _ ∈ imagePiece (presentation k) 0
    have h1 : (1 : A k) ∈ imagePiece (presentation k) 0 :=
      ⟨1, one_mem_piece k, map_one (presentation k)⟩
    simpa only [Algebra.smul_def, mul_one] using
      (imagePiece (presentation k) 0).smul_mem r h1


-- @@ L123-124 verbatim
@[simp] theorem mem_zeroLayerSubalgebra (a : A k) :
    a ∈ zeroLayerSubalgebra k ↔ a ∈ imagePiece (presentation k) 0 := Iff.rfl


-- @@ L126-130 verbatim
/-- The distinguished element `p` is in the zeroth-layer subalgebra. -/
theorem p_mem_zeroLayerSubalgebra : aX k 0 ∈ zeroLayerSubalgebra k := by
  change aX k 0 ∈ imagePiece (presentation k) 0
  exact imagePiece_mono (presentation k) (by omega : (-1 : ℤ) ≤ 0)
    (image_X_zero_mem_neg_one (presentation k))


-- @@ L132-139 verbatim
/-- The proper-subalgebra premise in the coordinate-derivation argument is
proved for the actual source filtration, not added as an external assumption. -/
theorem zeroLayerSubalgebra_ne_top [Nontrivial k] : zeroLayerSubalgebra k ≠ ⊤ := by
  intro h
  apply F_not_mem_zero_layer k
  change aX k 3 ∈ zeroLayerSubalgebra k
  rw [h]
  trivial


-- @@ L141-141 verbatim
end StableCoordinate.SourceFiltration


-- @@ L143-143 verbatim
end


-- @@ L145-145 verbatim
end OAI
