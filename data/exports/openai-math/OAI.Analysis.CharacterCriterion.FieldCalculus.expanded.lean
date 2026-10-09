import OAI.Analysis.CharacterCriterion.WeightedUnits


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped TensorProduct

-- @@ L7-7 verbatim
open scoped InnerProductSpace

-- @@ L8-8 verbatim
open scoped BigOperators

-- @@ L9-9 verbatim
open Set Module

-- @@ L10-10 verbatim
open Topology

-- @@ L11-11 verbatim
open NormedSpace

-- @@ L12-12 verbatim
open scoped ComplexOrder

-- @@ L13-13 verbatim
open scoped ComplexOrder

-- @@ L14-14 verbatim
open scoped InnerProductSpace

-- @@ L15-15 verbatim
open scoped InnerProductSpace

-- @@ L16-16 verbatim
open NormedSpace

-- @@ L17-17 verbatim
open scoped TensorProduct InnerProductSpace

-- @@ L18-18 verbatim
open UniformSpace

-- @@ L19-19 verbatim
variable [instSize : KirchbergRordam.GenericRW.Size]

-- @@ L20-20 verbatim
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n




-- @@ L24-24 verbatim
namespace KirchbergRordam.GenericRW


-- @@ L26-26 verbatim
open scoped Matrix Kronecker ComplexOrder


-- @@ L28-28 verbatim
abbrev M2 := CStarMatrix (Fin rankNum) (Fin rankNum) ℂ

-- @@ L29-29 verbatim
abbrev M3 := CStarMatrix (Fin (rankNum+1)) (Fin (rankNum+1)) ℂ

-- @@ L30-30 verbatim
abbrev M6 := CStarMatrix (Fin rankNum × Fin (rankNum+1)) (Fin rankNum × Fin (rankNum+1)) ℂ



-- @@ L33-47 verbatim
def leftMatrixAlgebra : Matrix (Fin rankNum) (Fin rankNum) ℂ →⋆ₐ[ℂ]
    Matrix (Fin rankNum × Fin (rankNum+1)) (Fin rankNum × Fin (rankNum+1)) ℂ where
  toFun a := a ⊗ₖ (1 : Matrix (Fin (rankNum+1)) (Fin (rankNum+1)) ℂ)
  map_zero' := Matrix.zero_kronecker _
  map_one' := Matrix.one_kronecker_one
  map_add' a b := Matrix.add_kronecker _ _ _
  map_mul' a b := by
    simpa only [mul_one] using Matrix.mul_kronecker_mul a b
      (1 : Matrix (Fin (rankNum+1)) (Fin (rankNum+1)) ℂ) (1 : Matrix (Fin (rankNum+1)) (Fin (rankNum+1)) ℂ)
  commutes' z := by
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.smul_kronecker,
      Matrix.one_kronecker_one]
  map_star' a := by
    change aᴴ ⊗ₖ (1 : Matrix (Fin (rankNum+1)) (Fin (rankNum+1)) ℂ) = (a ⊗ₖ 1)ᴴ
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]



-- @@ L50-64 verbatim
def rightMatrixAlgebra : Matrix (Fin (rankNum+1)) (Fin (rankNum+1)) ℂ →⋆ₐ[ℂ]
    Matrix (Fin rankNum × Fin (rankNum+1)) (Fin rankNum × Fin (rankNum+1)) ℂ where
  toFun a := (1 : Matrix (Fin rankNum) (Fin rankNum) ℂ) ⊗ₖ a
  map_zero' := Matrix.kronecker_zero _
  map_one' := Matrix.one_kronecker_one
  map_add' a b := Matrix.kronecker_add _ _ _
  map_mul' a b := by
    simpa only [mul_one] using Matrix.mul_kronecker_mul
      (1 : Matrix (Fin rankNum) (Fin rankNum) ℂ) (1 : Matrix (Fin rankNum) (Fin rankNum) ℂ) a b
  commutes' z := by
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.kronecker_smul,
      Matrix.one_kronecker_one]
  map_star' a := by
    change (1 : Matrix (Fin rankNum) (Fin rankNum) ℂ) ⊗ₖ aᴴ = (1 ⊗ₖ a)ᴴ
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]



-- @@ L67-69 verbatim
def leftMatrix : M2 →⋆ₐ[ℂ] M6 :=
  CStarMatrix.ofMatrixStarAlgEquiv.toStarAlgHom.comp
    (leftMatrixAlgebra.comp CStarMatrix.ofMatrixStarAlgEquiv.symm.toStarAlgHom)



-- @@ L72-74 verbatim
def rightMatrix : M3 →⋆ₐ[ℂ] M6 :=
  CStarMatrix.ofMatrixStarAlgEquiv.toStarAlgHom.comp
    (rightMatrixAlgebra.comp CStarMatrix.ofMatrixStarAlgEquiv.symm.toStarAlgHom)



-- @@ L77-84 verbatim
def matrixEval (t : unitInterval) : C(unitInterval, M6) →⋆ₐ[ℂ] M6 where
  toFun f := f t
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl



-- @@ L87-88 verbatim
def dimensionDropSubalgebra : StarSubalgebra ℂ C(unitInterval, M6) :=
  leftMatrix.range.comap (matrixEval 0) ⊓ rightMatrix.range.comap (matrixEval 1)


-- @@ L90-91 verbatim
instance : FiniteDimensional ℂ M6 :=
  inferInstanceAs (FiniteDimensional ℂ (Matrix (Fin rankNum × Fin (rankNum+1)) (Fin rankNum × Fin (rankNum+1)) ℂ))


-- @@ L93-100 verbatim
instance dimensionDropClosed : IsClosed
    (dimensionDropSubalgebra : Set C(unitInterval, M6)) := by
  change IsClosed ((fun f : C(unitInterval, M6) => f 0) ⁻¹' (leftMatrix.range : Set M6) ∩
    (fun f : C(unitInterval, M6) => f 1) ⁻¹' (rightMatrix.range : Set M6))
  exact ((leftMatrix.range.toSubalgebra.toSubmodule.closed_of_finiteDimensional).preimage
    (continuous_eval_const (0 : unitInterval))).inter
    ((rightMatrix.range.toSubalgebra.toSubmodule.closed_of_finiteDimensional).preimage
    (continuous_eval_const (1 : unitInterval)))



-- @@ L103-103 verbatim
abbrev DimensionDrop23 := dimensionDropSubalgebra


-- @@ L105-107 verbatim
instance dropSubringClass : SubringClass
    (StarSubalgebra ℂ C(unitInterval, M6)) C(unitInterval, M6) :=
  StarSubalgebra.subringClass (R := ℂ) (A := C(unitInterval, M6))


-- @@ L109-110 verbatim
instance : CStarAlgebra DimensionDrop23 :=
  StarSubalgebra.cstarAlgebra dimensionDropSubalgebra

-- @@ L111-111 verbatim
example : Nontrivial DimensionDrop23 := inferInstance



-- @@ L114-121 verbatim
def dropCoordinate : DimensionDrop23 :=
  ⟨⟨fun t => ((t : ℝ) : ℂ) • (1 : M6), by fun_prop⟩,
    by
      constructor
      · change ∃ a : M2, leftMatrix a = ((0 : unitInterval) : ℝ) • (1 : M6)
        exact ⟨0, by simp⟩
      · change ∃ a : M3, rightMatrix a = ((1 : unitInterval) : ℝ) • (1 : M6)
        exact ⟨1, by simp⟩⟩



-- @@ L124-133 verbatim
def leftCone (a : M2) : DimensionDrop23 :=
  ⟨⟨fun t => (1 - ((t : ℝ) : ℂ)) • leftMatrix a, by fun_prop⟩,
    by
      constructor
      · refine ⟨a, ?_⟩
        change leftMatrix a = (1 - (((0 : unitInterval) : ℝ) : ℂ)) • leftMatrix a
        simp
      · refine ⟨0, ?_⟩
        change rightMatrix 0 = (1 - (((1 : unitInterval) : ℝ) : ℂ)) • leftMatrix a
        simp⟩



-- @@ L136-145 verbatim
def rightCone (a : M3) : DimensionDrop23 :=
  ⟨⟨fun t => ((t : ℝ) : ℂ) • rightMatrix a, by fun_prop⟩,
    by
      constructor
      · refine ⟨0, ?_⟩
        change leftMatrix 0 = (((0 : unitInterval) : ℝ) : ℂ) • rightMatrix a
        simp
      · refine ⟨a, ?_⟩
        change rightMatrix a = (((1 : unitInterval) : ℝ) : ℂ) • rightMatrix a
        simp⟩



-- @@ L148-149 verbatim
def matrixUnit {n : ℕ} (i j : Fin n) : CStarMatrix (Fin n) (Fin n) ℂ :=
  CStarMatrix.ofMatrixStarAlgEquiv (Matrix.single i j 1)


-- @@ L151-155 verbatim
@[ext]
theorem drop_ext {f g : DimensionDrop23}
    (h : ∀ t, (f : C(unitInterval, M6)) t = (g : C(unitInterval, M6)) t) : f = g := by
  apply Subtype.ext
  exact ContinuousMap.ext h


-- @@ L157-165 verbatim
omit instSize in
@[simp]
theorem matrixUnit_mul
    [KirchbergRordam.GenericRW.Size]
    {n : ℕ} (i j k : Fin n) :
    matrixUnit i j * matrixUnit j k = matrixUnit i k := by
  unfold matrixUnit
  rw [← map_mul]
  simp only [Matrix.single_mul_single_same, mul_one]


-- @@ L167-173 verbatim
omit instSize in
theorem matrixUnit_mul_self
    [KirchbergRordam.GenericRW.Size]
    {n : ℕ} (i j : Fin n) (h : i ≠ j) :
    matrixUnit i j * matrixUnit i j = 0 := by
  unfold matrixUnit
  rw [← map_mul, Matrix.single_mul_single_of_ne (1 : ℂ) i j i h.symm (1 : ℂ), map_zero]


-- @@ L175-181 verbatim
theorem leftCone_mul_self (a : M2) (ha : a * a = 0) :
    leftCone a * leftCone a = 0 := by
  apply drop_ext
  intro t
  change ((1 - ((t : ℝ) : ℂ)) • leftMatrix a) *
    ((1 - ((t : ℝ) : ℂ)) • leftMatrix a) = 0
  rw [smul_mul_smul, ← map_mul, ha, map_zero, smul_zero]


-- @@ L183-189 verbatim
theorem rightCone_mul_self (a : M3) (ha : a * a = 0) :
    rightCone a * rightCone a = 0 := by
  apply drop_ext
  intro t
  change (((t : ℝ) : ℂ) • rightMatrix a) *
    (((t : ℝ) : ℂ) • rightMatrix a) = 0
  rw [smul_mul_smul, ← map_mul, ha, map_zero, smul_zero]


-- @@ L191-191 verbatim
end KirchbergRordam.GenericRW


-- @@ L193-193 verbatim
namespace KirchbergRordam.GenericRW.FieldCalculus

-- @@ L194-194 verbatim
open scoped BigOperators

-- @@ L195-195 verbatim
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]

-- @@ L196-196 verbatim
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- @@ L197-197 verbatim
variable {A : Type*} [CStarAlgebra A]



-- @@ L200-209 verbatim
structure Data (X ι A : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [Fintype ι] [DecidableEq ι] [CStarAlgebra A] where
  p : C(X,ℂ)
  selfAdjoint_p : IsSelfAdjoint p
  eval : C(X,ℂ) →⋆ₐ[ℂ] A
  x : ι → ι → A
  star_x : ∀ i j, star (x i j) = x j i
  mul_x : ∀ i j k l, x i j*x k l = if j=k then eval p*x i l else 0
  commute_eval : ∀ i j f, Commute (x i j) (eval f)
  bound : ∀ i j f, ‖x i j*eval f‖ ≤ ‖p*f‖


-- @@ L211-211 verbatim
namespace Data

-- @@ L212-212 verbatim
variable (D : Data X ι A)

-- @@ L213-213 verbatim
abbrev Domain := Vanish.Functions {t | D.p t=0}


-- @@ L215-218 verbatim
def aux (i j : ι) : C(X,ℂ) →ₗ[ℂ] A where
  toFun f := D.x i j*D.eval f
  map_add' _ _ := by simp [mul_add]
  map_smul' _ _ := by simp


-- @@ L220-220 verbatim
def coeff (i j : ι) : D.Domain →L[ℂ] A := (D.aux i j).extendOfNorm (Vanish.multiplier D.p)


-- @@ L222-225 verbatim
lemma coeff_mul (i j : ι) (f : C(X,ℂ)) :
    D.coeff i j (Vanish.multiplier D.p f) = D.x i j*D.eval f := by
  exact LinearMap.extendOfNorm_eq (Vanish.multiplier_dense D.p)
    ⟨1,fun f => by change ‖D.x i j*D.eval f‖ ≤ 1*‖D.p*f‖; simpa only [one_mul] using D.bound i j f⟩ f


-- @@ L227-230 verbatim
lemma norm_coeff_le (i j : ι) (f : D.Domain) : ‖D.coeff i j f‖ ≤ ‖f‖ := by
  simpa only [coeff,one_mul] using LinearMap.norm_extendOfNorm_apply_le
    (f := D.aux i j) (Vanish.multiplier_dense D.p) 1
    (fun f => by change ‖D.x i j*D.eval f‖ ≤ 1*‖D.p*f‖; simpa only [one_mul] using D.bound i j f) f


-- @@ L232-249 verbatim
omit instSize in
lemma multiplier_star.{contextLevel1, contextLevel2, contextLevel3}
    [KirchbergRordam.GenericRW.Size]
    {X : Type contextLevel1}
    [TopologicalSpace X]
    [CompactSpace X]
    [T2Space X]
    {ι : Type contextLevel2}
    [Fintype ι]
    [DecidableEq ι]
    {A : Type contextLevel3}
    [CStarAlgebra A]
    (D : KirchbergRordam.GenericRW.FieldCalculus.Data X ι A)
    (f : C(X,ℂ)) :
    star (Vanish.multiplier D.p f) = Vanish.multiplier D.p (star f) := by
  apply Subtype.ext
  change star (D.p*f)=D.p*star f
  rw [star_mul,D.selfAdjoint_p.star_eq,mul_comm]


-- @@ L251-269 verbatim
omit instSize in
lemma multiplier_product.{contextLevel1, contextLevel2, contextLevel3}
    [KirchbergRordam.GenericRW.Size]
    {X : Type contextLevel1}
    [TopologicalSpace X]
    [CompactSpace X]
    [T2Space X]
    {ι : Type contextLevel2}
    [Fintype ι]
    [DecidableEq ι]
    {A : Type contextLevel3}
    [CStarAlgebra A]
    (D : KirchbergRordam.GenericRW.FieldCalculus.Data X ι A)
    (f g : C(X,ℂ)) :
    Vanish.multiplier D.p f * Vanish.multiplier D.p g =
      Vanish.multiplier D.p (D.p*f*g) := by
  apply Subtype.ext
  change (D.p*f)*(D.p*g)=D.p*(D.p*f*g)
  ring


-- @@ L271-276 verbatim
lemma star_coeff (i j : ι) (f : D.Domain) :
    star (D.coeff i j f) = D.coeff j i (star f) := by
  refine (Vanish.multiplier_dense D.p).induction_on f (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro g
  rw [D.multiplier_star,D.coeff_mul,D.coeff_mul,star_mul,D.star_x,map_star]
  simpa only [map_star] using (D.commute_eval j i (star g)).symm.eq


-- @@ L278-293 verbatim
lemma product_coeff (i j k l : ι) (f g : D.Domain) :
    D.coeff i j f * D.coeff k l g = if j=k then D.coeff i l (f*g) else 0 := by
  refine (Vanish.multiplier_dense D.p).induction_on₂ (p := fun f g =>
    D.coeff i j f * D.coeff k l g = if j=k then D.coeff i l (f*g) else 0)
    (isClosed_eq (by fun_prop) (by by_cases hjk : j=k <;> simp only [hjk,↓reduceIte] <;> fun_prop)) ?_ f g
  intro f g
  rw [D.multiplier_product,D.coeff_mul,D.coeff_mul,D.coeff_mul]
  have he : (D.x i j*D.eval f)*(D.x k l*D.eval g) =
      (D.x i j*D.x k l)*(D.eval f*D.eval g) := by
    rw [mul_assoc (D.x i j),← mul_assoc (D.eval f),(D.commute_eval k l f).symm.eq]
    noncomm_ring
  rw [he,D.mul_x]
  split_ifs with hjk
  · rw [map_mul,map_mul,← (D.commute_eval i l D.p).eq]
    noncomm_ring
  · simp



-- @@ L296-300 verbatim
def scalarMul (f : C(X,ℂ)) : D.Domain →L[ℂ] D.Domain :=
  { toFun := fun g => ⟨f*(g:C(X,ℂ)), by intro t ht; simp [g.property t ht]⟩
    map_add' := by intro g h; ext t; simp [mul_add]
    map_smul' := by intro c g; ext t; simp
    cont := by fun_prop }


-- @@ L302-311 verbatim
lemma scalar_coeff (i j : ι) (f : C(X,ℂ)) (g : D.Domain) :
    D.coeff i j (D.scalarMul f g) = D.eval f * D.coeff i j g := by
  refine (Vanish.multiplier_dense D.p).induction_on g (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro u
  have he : D.scalarMul f (Vanish.multiplier D.p u) = Vanish.multiplier D.p (f*u) := by
    apply Subtype.ext
    change f*(D.p*u)=D.p*(f*u)
    ring
  rw [he,D.coeff_mul,D.coeff_mul,map_mul]
  rw [← mul_assoc, (D.commute_eval i j f).eq, mul_assoc]


-- @@ L313-313 verbatim
abbrev Matrices := Matrix ι ι D.Domain


-- @@ L315-318 verbatim
def matrices : D.Matrices →ₗ[ℂ] A where
  toFun m := ∑ i,∑ j,D.coeff i j (m i j)
  map_add' m n := by simp [Finset.sum_add_distrib]
  map_smul' c m := by simp [Finset.smul_sum]


-- @@ L320-335 verbatim
omit instSize in
lemma matrices_single.{contextLevel1, contextLevel2, contextLevel3}
    [KirchbergRordam.GenericRW.Size]
    {X : Type contextLevel1}
    [TopologicalSpace X]
    [CompactSpace X]
    [T2Space X]
    {ι : Type contextLevel2}
    [Fintype ι]
    [DecidableEq ι]
    {A : Type contextLevel3}
    [CStarAlgebra A]
    (D : KirchbergRordam.GenericRW.FieldCalculus.Data X ι A)
    (i j : ι) (f : D.Domain) :
    D.matrices (Matrix.single i j f) = D.coeff i j f := by
  simp [matrices,Matrix.single,ite_and,apply_ite]


-- @@ L337-351 verbatim
lemma matrices_product (m n : D.Matrices) : D.matrices (m*n) = D.matrices m*D.matrices n := by
  induction m using Matrix.induction_on' with
  | h_zero => simp
  | h_add m m' hm hm' => simp only [add_mul,map_add,hm,hm']
  | h_std_basis i j f =>
    induction n using Matrix.induction_on' with
    | h_zero => simp
    | h_add n n' hn hn' => simp only [mul_add,map_add,hn,hn']
    | h_std_basis k l g =>
      by_cases h : j=k
      · subst k
        rw [Matrix.single_mul_single_same,D.matrices_single,D.matrices_single,
          D.matrices_single,D.product_coeff,ite_eq_left rfl]
      · rw [Matrix.single_mul_single_of_ne (h := h),D.matrices_single,D.matrices_single,
          D.product_coeff,ite_eq_right h,map_zero]


-- @@ L353-355 verbatim
lemma matrices_star (m : D.Matrices) : D.matrices (star m) = star (D.matrices m) := by
  simp only [matrices,LinearMap.coe_mk,AddHom.coe_mk,star_sum,D.star_coeff]
  exact Finset.sum_comm



-- @@ L358-364 verbatim
def hom : D.Matrices →⋆ₙₐ[ℂ] A where
  toFun := D.matrices
  map_zero' := map_zero _
  map_add' := map_add _
  map_smul' := map_smul _
  map_mul' := D.matrices_product
  map_star' := D.matrices_star

-- @@ L365-365 verbatim
end Data

-- @@ L366-366 verbatim
end KirchbergRordam.GenericRW.FieldCalculus

-- @@ L367-367 verbatim
namespace KirchbergRordam.GenericRW.OrderZero

-- @@ L368-368 verbatim
open scoped BigOperators

-- @@ L369-369 verbatim
open IntervalCalculus

-- @@ L370-370 verbatim
variable {ι κ A : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

-- @@ L371-371 verbatim
variable [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]



-- @@ L374-379 verbatim
structure Pair (ι κ A : Type*) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [CStarAlgebra A] [PartialOrder A] where
  left : WeightedUnits ι A
  right : WeightedUnits κ A
  commute : ∀ i j k l, Commute (left.x i j) (right.x k l)
  sum_one : left.h+right.h=1


-- @@ L381-381 verbatim
namespace Pair

-- @@ L382-382 verbatim
variable (P : Pair ι κ A)

-- @@ L383-397 verbatim
omit [Nontrivial A] [StarOrderedRing A] in
omit instSize in
lemma left_h.{contextLevel1, contextLevel2, contextLevel3}
    [KirchbergRordam.GenericRW.Size]
    {ι : Type contextLevel1}
    {κ : Type contextLevel2}
    {A : Type contextLevel3}
    [Fintype ι]
    [DecidableEq ι]
    [Fintype κ]
    [DecidableEq κ]
    [CStarAlgebra A]
    [PartialOrder A]
    (P : KirchbergRordam.GenericRW.OrderZero.Pair ι κ A)
    : P.left.h=1-P.right.h := (eq_sub_iff_add_eq).mpr P.sum_one


-- @@ L399-416 verbatim
omit [Nontrivial A] [StarOrderedRing A] in
omit instSize in
lemma left_commute_right_h.{contextLevel1, contextLevel2, contextLevel3}
    [KirchbergRordam.GenericRW.Size]
    {ι : Type contextLevel1}
    {κ : Type contextLevel2}
    {A : Type contextLevel3}
    [Fintype ι]
    [DecidableEq ι]
    [Fintype κ]
    [DecidableEq κ]
    [CStarAlgebra A]
    [PartialOrder A]
    (P : KirchbergRordam.GenericRW.OrderZero.Pair ι κ A)
    (i j : ι) : Commute (P.left.x i j) P.right.h := by
  change P.left.x i j*P.right.h=P.right.h*P.left.x i j
  rw [← P.right.diagonal,Finset.mul_sum,Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => (P.commute i j k k).eq


-- @@ L418-421 verbatim
omit [Nontrivial A] [StarOrderedRing A] in
lemma right_commute_left_h (i j : κ) : Commute (P.right.x i j) P.left.h := by
  rw [P.left_h]
  exact (Commute.one_right _).sub_right (P.right.commute_h i j)


-- @@ L423-423 verbatim
abbrev eval : C(unitInterval,ℂ) →⋆ₐ[ℂ] A := IntervalCalculus.hom P.right.nonneg P.right.norm_le


-- @@ L425-428 verbatim
lemma commute_eval {x : A} (hc : Commute x P.right.h) (f : C(unitInterval,ℂ)) :
    Commute x (P.eval f) := by
  exact ((IsSelfAdjoint.of_nonneg P.right.nonneg).commute_cfcHom
    (IsSelfAdjoint.of_nonneg P.right.nonneg).isStarNormal hc.symm _).symm


-- @@ L430-430 verbatim
def weight (_P : Pair ι κ A) : C(unitInterval,ℂ) := (1-coord)*coord


-- @@ L432-448 verbatim
omit [Nontrivial A] [StarOrderedRing A] in
omit instSize in
lemma selfAdjoint_weight.{contextLevel1, contextLevel2, contextLevel3}
    [KirchbergRordam.GenericRW.Size]
    {ι : Type contextLevel1}
    {κ : Type contextLevel2}
    {A : Type contextLevel3}
    [Fintype ι]
    [DecidableEq ι]
    [Fintype κ]
    [DecidableEq κ]
    [CStarAlgebra A]
    [PartialOrder A]
    (P : KirchbergRordam.GenericRW.OrderZero.Pair ι κ A)
    : IsSelfAdjoint P.weight := by
  ext t
  simp [weight,coord]


-- @@ L450-451 verbatim
lemma eval_weight : P.eval P.weight = P.left.h*P.right.h := by
  rw [weight,map_mul,map_sub,map_one,hom_coord,P.left_h]


-- @@ L453-466 verbatim
lemma norm_product (i j : ι) (k l : κ) (f : C(unitInterval,ℂ)) :
    ‖(P.left.x i j*P.right.x k l)*P.eval f‖ ≤ ‖P.weight*f‖ := by
  calc
    _ ≤ ‖P.left.h*(P.right.x k l*P.eval f)‖ := by
      rw [mul_assoc]
      exact P.left.norm_mul_le i j _
    _ = ‖P.right.x k l*(P.left.h*P.eval f)‖ := by
      rw [← mul_assoc,(P.right_commute_left_h k l).symm.eq,mul_assoc]
    _ ≤ ‖P.right.h*(P.left.h*P.eval f)‖ := P.right.norm_mul_le k l _
    _ = ‖P.eval (P.weight*f)‖ := by
      rw [map_mul,P.eval_weight,P.left_h]
      congr 1
      noncomm_ring
    _ ≤ ‖P.weight*f‖ := norm_hom_le _ _ _



-- @@ L469-498 verbatim
def field : FieldCalculus.Data unitInterval (ι × κ) A where
  p := P.weight
  selfAdjoint_p := P.selfAdjoint_weight
  eval := P.eval
  x u v := P.left.x u.1 v.1*P.right.x u.2 v.2
  star_x u v := by
    rw [star_mul,P.left.star_x,P.right.star_x]
    exact (P.commute v.1 u.1 v.2 u.2).symm.eq
  mul_x u v w z := by
    have he : (P.left.x u.1 v.1*P.right.x u.2 v.2)*(P.left.x w.1 z.1*P.right.x w.2 z.2) =
        (P.left.x u.1 v.1*P.left.x w.1 z.1)*(P.right.x u.2 v.2*P.right.x w.2 z.2) := by
      rw [mul_assoc (P.left.x u.1 v.1),← mul_assoc (P.right.x u.2 v.2),
        (P.commute w.1 z.1 u.2 v.2).symm.eq]
      noncomm_ring
    rw [he,P.left.mul_x,P.right.mul_x,P.eval_weight]
    by_cases h1 : v.1=w.1 <;> by_cases h2 : v.2=w.2
    · have h : v=w := Prod.ext h1 h2
      simp only [h,↓reduceIte]
      rw [mul_assoc P.left.h,← mul_assoc (P.left.x u.1 z.1),
        (P.left_commute_right_h u.1 z.1).eq]
      noncomm_ring
    · have h : v ≠ w := fun he => h2 (congrArg Prod.snd he)
      simp [h1,h2,h]
    · have h : v ≠ w := fun he => h1 (congrArg Prod.fst he)
      simp [h1,h2,h]
    · have h : v ≠ w := fun he => h1 (congrArg Prod.fst he)
      simp [h1,h2,h]
  commute_eval u v f := P.commute_eval
    ((P.left_commute_right_h u.1 v.1).mul_left (P.right.commute_h u.2 v.2)) f
  bound u v f := P.norm_product _ _ _ _ f


-- @@ L500-505 verbatim
lemma left_x_field (i j : ι) (u v : ι × κ) :
    P.left.x i j * P.field.x u v =
      if j=u.1 then P.left.h*P.field.x (i,u.2) v else 0 := by
  change _*(P.left.x u.1 v.1*P.right.x u.2 v.2) = _
  rw [← mul_assoc,P.left.mul_x]
  by_cases h : j=u.1 <;> simp [h,field,mul_assoc]


-- @@ L507-517 verbatim
lemma right_x_field (i j : κ) (u v : ι × κ) :
    P.right.x i j * P.field.x u v =
      if j=u.2 then P.right.h*P.field.x (u.1,i) v else 0 := by
  change _*(P.left.x u.1 v.1*P.right.x u.2 v.2) = _
  rw [← mul_assoc,(P.commute u.1 v.1 i j).symm.eq,mul_assoc,P.right.mul_x]
  by_cases h : j=u.2
  · simp only [h,↓reduceIte]
    change P.left.x u.1 v.1*(P.right.h*P.right.x i v.2) =
      P.right.h*(P.left.x u.1 v.1*P.right.x i v.2)
    rw [← mul_assoc, (P.left_commute_right_h u.1 v.1).eq,mul_assoc]
  · simp [h]


-- @@ L519-532 verbatim
lemma left_x_coeff (i j : ι) (u v : ι × κ) (f : P.field.Domain) :
    P.left.x i j*P.field.coeff u v f =
      if j=u.1 then P.field.coeff (i,u.2) v (P.field.scalarMul (1-coord) f) else 0 := by
  refine (Vanish.multiplier_dense P.field.p).induction_on f
    (isClosed_eq (by fun_prop) (by by_cases h : j=u.1 <;> simp only [h,↓reduceIte] <;> fun_prop)) ?_
  intro g
  rw [P.field.coeff_mul]
  rw [← mul_assoc,P.left_x_field]
  by_cases h : j=u.1
  · rw [ite_eq_left h,ite_eq_left h,P.field.scalar_coeff,P.field.coeff_mul]
    change (P.left.h*P.field.x (i,u.2) v)*P.eval g =
      P.eval (1-coord)*(P.field.x (i,u.2) v*P.eval g)
    rw [map_sub,map_one,hom_coord,← P.left_h,mul_assoc]
  · simp [h]


-- @@ L534-546 verbatim
lemma right_x_coeff (i j : κ) (u v : ι × κ) (f : P.field.Domain) :
    P.right.x i j*P.field.coeff u v f =
      if j=u.2 then P.field.coeff (u.1,i) v (P.field.scalarMul coord f) else 0 := by
  refine (Vanish.multiplier_dense P.field.p).induction_on f
    (isClosed_eq (by fun_prop) (by by_cases h : j=u.2 <;> simp only [h,↓reduceIte] <;> fun_prop)) ?_
  intro g
  rw [P.field.coeff_mul,← mul_assoc,P.right_x_field]
  by_cases h : j=u.2
  · rw [ite_eq_left h,ite_eq_left h,P.field.scalar_coeff,P.field.coeff_mul]
    change (P.right.h*P.field.x (u.1,i) v)*P.eval g =
      P.eval coord*(P.field.x (u.1,i) v*P.eval g)
    rw [hom_coord,mul_assoc]
  · simp [h]

-- @@ L547-547 verbatim
end Pair

-- @@ L548-548 verbatim
end KirchbergRordam.GenericRW.OrderZero

-- @@ L549-549 verbatim
end


-- @@ L551-551 verbatim
end OAI
