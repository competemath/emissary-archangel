import OAI.Geometry.QuadricBundles.SymmetricFlags


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u1 u2


-- @@ L7-7 verbatim
noncomputable section


-- @@ L9-9 verbatim
namespace QuadricCounterexample

-- @@ L10-10 verbatim
open Set MvPolynomial Matrix

-- @@ L11-11 verbatim
open scoped BigOperators

-- @@ L12-12 verbatim
noncomputable section


-- @@ L14-19 verbatim
structure PolynomialGeneration (n : ℕ) (ι : Type u1) [Fintype ι] where
  coefficient : StandardChart → Fin (n+1) → ι → BasePolynomial
  recovery : StandardChart → Fin (n+1) → ι → BasePolynomial
  leftInverse : ∀ i z (w : Fin (n+1) → ℂ),
    Matrix.mulVec (fun a q ↦ baseEval (recovery i a q) z)
      (Matrix.mulVec (Matrix.transpose (fun a q ↦ baseEval (coefficient i a q) z)) w)=w

-- @@ L20-20 verbatim
namespace PolynomialGeneration

-- @@ L21-21 verbatim
variable {n : ℕ} {ι : Type u2} [Fintype ι] (B : PolynomialGeneration n ι)

-- @@ L22-23 verbatim
def matrix (i : StandardChart) (z : BaseCoordinates) : Matrix (Fin (n+1)) ι ℂ :=
  fun a q ↦ baseEval (B.coefficient i a q) z

-- @@ L24-25 verbatim
def recover (i : StandardChart) (z : BaseCoordinates) : Matrix (Fin (n+1)) ι ℂ :=
  fun a q ↦ baseEval (B.recovery i a q) z

-- @@ L26-27 verbatim
lemma recover_matrix (i : StandardChart) (z : BaseCoordinates) (w : Fin (n+1) → ℂ) :
    (B.recover i z).mulVec ((B.matrix i z).transpose.mulVec w)=w := B.leftInverse i z w

-- @@ L28-32 verbatim
lemma matrix_injective (i : StandardChart) (z : BaseCoordinates) :
    Function.Injective ((B.matrix i z).transpose.mulVec) := by
  intro w w' h
  have he := congrArg (B.recover i z).mulVec h
  simpa only [B.recover_matrix] using he

-- @@ L33-38 verbatim
lemma matrix_nonzero (i : StandardChart) (z : BaseCoordinates) {w : Fin (n+1) → ℂ} (hw : w≠0) :
    (B.matrix i z).transpose.mulVec w≠0 := by
  intro hh
  apply hw
  apply B.matrix_injective i z
  simpa only [mulVec_zero] using hh

-- @@ L39-39 verbatim
end PolynomialGeneration

-- @@ L40-40 verbatim
end

-- @@ L41-41 verbatim
end QuadricCounterexample


-- @@ L43-43 verbatim
namespace QuadricCounterexample

-- @@ L44-44 verbatim
open Set MvPolynomial Matrix BinaryForms LaurentCech

-- @@ L45-45 verbatim
open scoped BigOperators

-- @@ L46-46 verbatim
noncomputable section


-- @@ L48-48 verbatim
namespace EqualizerData

-- @@ L49-49 verbatim
variable (D : EqualizerData) (m e t : ℕ) (he : 3*m≤e)

-- @@ L50-50 verbatim
abbrev SymmetricGeneratorIndex := StandardChart × Fin (2*t+1)

-- @@ L51-54 verbatim
def symmetricGeneratorValue (i : StandardChart) (z : BaseCoordinates) :
    Matrix (Fin (2*t+1)) (SymmetricGeneratorIndex t) ℂ :=
  fun a q ↦ ((D.flagBasis m t i z).mulVec
    (TriangularCechBundle.polynomialValue ((D.symmetricFlag m e t he).generator q.1 q.2).polynomial i z)) a

-- @@ L55-62 verbatim
lemma symmetricGeneratorValue_regular (i : StandardChart) (a : Fin (2*t+1))
    (q : SymmetricGeneratorIndex t) :
    UniformlyRegularOn univ (fun z ↦ D.symmetricGeneratorValue m e t he i z a q) := by
  change UniformlyRegularOn univ (fun z ↦ ∑ b, D.flagBasis m t i z a b *
    baseEval (((D.symmetricFlag m e t he).generator q.1 q.2).polynomial i b) z)
  apply UniformlyRegularOn.fintype_sum
  intro b
  exact (D.flagBasis_regular m t i a b).mul (uniformlyRegular_polynomial univ _)


-- @@ L64-66 verbatim
def localGeneratorMatrix (i : StandardChart) (z : BaseCoordinates) :
    Matrix (Fin (2*t+1)) (Fin (2*t+1)) ℂ :=
  fun a b ↦ D.symmetricGeneratorValue m e t he i z a (i,b)

-- @@ L67-82 verbatim
lemma localGeneratorMatrix_det_unit (i : StandardChart) (z : BaseCoordinates) :
    IsUnit (D.localGeneratorMatrix m e t he i z).det := by
  let B := D.symmetricFlag m e t he
  let Q : Matrix (Fin (2*t+1)) (Fin (2*t+1)) ℂ := fun a b ↦
    baseEval ((B.generator i b).polynomial i a) z
  have hQ : Q.det=1 := by
    rw [Matrix.det_of_isUpperTriangular (fun a b hab ↦ by
      dsimp [Q]; rw [B.generator_high i i b a hab]; simp)]
    apply Finset.prod_eq_one
    intro b _
    dsimp [Q]
    rw [B.generator_diagonal]
    simp [lineGenerator]
  have hmat : D.localGeneratorMatrix m e t he i z=D.flagBasis m t i z*Q := rfl
  rw [hmat,Matrix.det_mul,hQ,mul_one]
  exact D.flagBasis_det_unit m t i z

-- @@ L83-85 verbatim
lemma localGeneratorMatrix_regular (i : StandardChart) (a b : Fin (2*t+1)) :
    UniformlyRegularOn univ (fun z ↦ D.localGeneratorMatrix m e t he i z a b) :=
  D.symmetricGeneratorValue_regular m e t he i a (i,b)


-- @@ L87-89 verbatim
def generatorRecoveryValue (i : StandardChart) (z : BaseCoordinates) :
    Matrix (Fin (2*t+1)) (SymmetricGeneratorIndex t) ℂ :=
  fun a q ↦ if q.1=i then ((D.localGeneratorMatrix m e t he i z).transpose)⁻¹ a q.2 else 0

-- @@ L90-100 verbatim
lemma generatorRecoveryValue_regular (i : StandardChart) (a : Fin (2*t+1))
    (q : SymmetricGeneratorIndex t) :
    UniformlyRegularOn univ (fun z ↦ D.generatorRecoveryValue m e t he i z a q) := by
  by_cases h : q.1=i
  · simp only [generatorRecoveryValue,ite_eq_left h]
    apply UniformlyRegularOn.matrix_inv
    · intro a b
      exact D.localGeneratorMatrix_regular m e t he i b a
    · intro z _
      simpa only [Matrix.det_transpose] using D.localGeneratorMatrix_det_unit m e t he i z
  · simpa only [generatorRecoveryValue,ite_eq_right h] using uniformlyRegular_const univ (0 : ℂ)

-- @@ L101-129 verbatim
lemma generatorRecoveryValue_leftInverse (i : StandardChart) (z : BaseCoordinates)
    (w : Fin (2*t+1) → ℂ) :
    (D.generatorRecoveryValue m e t he i z).mulVec
      ((D.symmetricGeneratorValue m e t he i z).transpose.mulVec w)=w := by
  have hh := Matrix.nonsing_inv_mul ((D.localGeneratorMatrix m e t he i z).transpose)
    (by simpa only [Matrix.det_transpose] using D.localGeneratorMatrix_det_unit m e t he i z)
  have hv := congrArg (fun A : Matrix (Fin (2*t+1)) (Fin (2*t+1)) ℂ ↦ A.mulVec w) hh
  rw [← Matrix.mulVec_mulVec,Matrix.one_mulVec] at hv
  calc
    _ = (((D.localGeneratorMatrix m e t he i z).transpose)⁻¹).mulVec
        ((D.localGeneratorMatrix m e t he i z).transpose.mulVec w) := by
      ext a
      change (∑ q : StandardChart × Fin (2*t+1),
        (if q.1=i then ((D.localGeneratorMatrix m e t he i z).transpose)⁻¹ a q.2 else 0)*
          ((D.symmetricGeneratorValue m e t he i z).transpose.mulVec w) q)=_
      rw [Fintype.sum_prod_type]
      simp only [ite_mul,zero_mul]
      have hi (j : StandardChart) :
          (∑ b : Fin (2*t+1),if j=i then
            ((D.localGeneratorMatrix m e t he i z).transpose)⁻¹ a b*
              ((D.symmetricGeneratorValue m e t he i z).transpose.mulVec w) (j,b) else 0)=
          if j=i then ∑ b : Fin (2*t+1),
            ((D.localGeneratorMatrix m e t he i z).transpose)⁻¹ a b*
              ((D.symmetricGeneratorValue m e t he i z).transpose.mulVec w) (j,b) else 0 := by
        split_ifs <;> simp
      simp_rw [hi]
      simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      rfl
    _ = w := hv


-- @@ L131-145 verbatim
def symmetricGeneration : PolynomialGeneration (2*t) (SymmetricGeneratorIndex t) where
  coefficient := fun i a q ↦ (D.symmetricGeneratorValue_regular m e t he i a q).exists_polynomial.choose
  recovery := fun i a q ↦ (D.generatorRecoveryValue_regular m e t he i a q).exists_polynomial.choose
  leftInverse := by
    intro i z w
    have hQ : (fun a q ↦ baseEval ((D.symmetricGeneratorValue_regular m e t he i a q).exists_polynomial.choose) z)=
        D.symmetricGeneratorValue m e t he i z := by
      funext a q
      exact (congrFun (D.symmetricGeneratorValue_regular m e t he i a q).exists_polynomial.choose_spec z).symm
    have hR : (fun a q ↦ baseEval ((D.generatorRecoveryValue_regular m e t he i a q).exists_polynomial.choose) z)=
        D.generatorRecoveryValue m e t he i z := by
      funext a q
      exact (congrFun (D.generatorRecoveryValue_regular m e t he i a q).exists_polynomial.choose_spec z).symm
    rw [hQ,hR]
    exact D.generatorRecoveryValue_leftInverse m e t he i z w

-- @@ L146-149 verbatim
lemma symmetricGeneration_matrix (i : StandardChart) (z : BaseCoordinates) :
    (D.symmetricGeneration m e t he).matrix i z=D.symmetricGeneratorValue m e t he i z := by
  funext a q
  exact (congrFun (D.symmetricGeneratorValue_regular m e t he i a q).exists_polynomial.choose_spec z).symm

-- @@ L150-164 verbatim
lemma symmetricGeneratorValue_compatible (i j : StandardChart) {z : BaseCoordinates}
    (hz : z∈coordinateOverlap i j) (q : SymmetricGeneratorIndex t) :
    (D.symmetricGeneratorValue m e t he i z).col q=
      lineFactor (e,e) i j z • (symmetricMatrix (2*t) (D.coordinateTransition i j (powerCoordinates m z))).mulVec
        ((D.symmetricGeneratorValue m e t he j (coordinateChange i j z)).col q) := by
  let B := D.symmetricFlag m e t he
  have hc := (B.generator q.1 q.2).compatible i j z hz
  change (D.flagBasis m t i z).mulVec (TriangularCechBundle.polynomialValue (B.generator q.1 q.2).polynomial i z)=_
  rw [← hc]
  change (D.flagBasis m t i z).mulVec ((D.flagMatrix m e t i j z).mulVec _)=_
  rw [flagMatrix,Matrix.smul_mulVec,Matrix.mulVec_smul,Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc,← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (D.flagBasis_det_unit m t i z),Matrix.one_mul]
  rw [← Matrix.mulVec_mulVec]
  rfl

-- @@ L165-165 verbatim
end EqualizerData

-- @@ L166-166 verbatim
end

-- @@ L167-167 verbatim
end QuadricCounterexample


-- @@ L169-169 verbatim
end


-- @@ L171-171 verbatim
end OAI
