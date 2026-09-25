/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.ForMathlib.Matrix
public import QuantumInfo.ForMathlib.IsMaximalSelfAdjoint
public import QuantumInfo.ForMathlib.ContinuousLinearMap
public import QuantumInfo.ForMathlib.Tactic.Commutes



-- @@ L14-14 verbatim
@[expose] public section


-- @@ L16-19 verbatim
/-- The type of Hermitian matrices, as a `Subtype`. Equivalent to a `Matrix n n α` bundled
with the fact that `Matrix.IsHermitian`. -/
def HermitianMat (n : Type*) (α : Type*) [AddGroup α] [StarAddMonoid α] :=
  (selfAdjoint (Matrix n n α) : Type (max u_1 u_2))


-- @@ L21-21 verbatim
namespace HermitianMat


-- @@ L23-23 verbatim
variable {α R 𝕜 : Type*} {m n : Type*}

-- @@ L24-24 verbatim
variable [Star R] [TrivialStar R]

-- @@ L25-25 verbatim
variable [RCLike 𝕜]


-- @@ L27-27 verbatim
section addgroup


-- @@ L29-29 verbatim
variable [AddGroup α] [StarAddMonoid α]


-- @@ L31-32 verbatim
theorem eq_IsHermitian : HermitianMat n α  = { m : Matrix n n α // m.IsHermitian} := by
  rfl


-- @@ L34-35 verbatim
@[coe] def mat : HermitianMat n α → Matrix n n α :=
  Subtype.val


-- @@ L37-37 verbatim
instance : Coe (HermitianMat n α) (Matrix n n α) := ⟨mat⟩


-- @@ L39-41 verbatim
@[simp]
theorem val_eq_coe (A : HermitianMat n α) : A.val = A := by
  rfl


-- @@ L43-45 verbatim
@[simp]
theorem mat_mk (x : Matrix n n α) (h) : mat ⟨x, h⟩ = x := by
  rfl


-- @@ L47-49 verbatim
@[simp]
theorem mk_mat {A : HermitianMat n α} (h : A.mat.IsHermitian) : ⟨A.mat, h⟩ = A := by
  rfl


-- @@ L51-54 verbatim
/-- Alias for HermitianMat.property or HermitianMat.2, this gets the fact that the value
  is actually `IsHermitian`.-/
theorem H (A : HermitianMat n α) : A.mat.IsHermitian :=
  A.2


-- @@ L56-57 verbatim
@[ext] protected theorem ext {A B : HermitianMat n α} : A.mat = B.mat → A = B :=
  Subtype.ext


-- @@ L59-61 verbatim
instance instFun : FunLike (HermitianMat n α) n (n → α) where
  coe M := (M : Matrix n n α)
  coe_injective _ _ h := HermitianMat.ext h


-- @@ L63-65 verbatim
@[simp]
theorem mat_apply {A : HermitianMat n α} {i j : n} : A.mat i j = A i j := by
  rfl


-- @@ L67-70 verbatim
@[simp]
theorem conjTranspose_mat (A : HermitianMat n α) :
    A.mat.conjTranspose = A.mat :=
  A.H


-- @@ L72-73 verbatim
instance : AddGroup (HermitianMat n α) :=
  AddSubgroup.toAddGroup _


-- @@ L75-77 verbatim
instance [IsEmpty n] : Unique (HermitianMat n α) where
  default := 0
  uniq a := by ext; exact (IsEmpty.false ‹_›).elim


-- @@ L79-81 verbatim
@[simp, norm_cast]
theorem mat_zero : (0 : HermitianMat n α).mat = 0 := by
  rfl


-- @@ L83-85 verbatim
@[simp]
theorem mk_zero (h : (0 : Matrix n n α).IsHermitian) : ⟨0, h⟩ = (0 : HermitianMat n α) := by
  rfl


-- @@ L87-89 verbatim
@[simp]
theorem zero_apply (i j : n) : (0 : HermitianMat n 𝕜) i j = 0 := by
  rfl


-- @@ L91-94 verbatim
@[simp, norm_cast]
theorem mat_add (A B : HermitianMat n α) :
    (A + B).mat = A.mat + B.mat := by
  rfl


-- @@ L96-99 verbatim
@[simp, norm_cast]
theorem mat_sub (A B : HermitianMat n α) :
    (A - B).mat = A.mat - B.mat := by
  rfl


-- @@ L101-104 verbatim
@[simp, norm_cast]
theorem mat_neg (A : HermitianMat n α) :
    (-A).mat = -A.mat := by
  rfl


-- @@ L106-106 verbatim
section smul

-- @@ L107-107 verbatim
variable [SMul R α] [StarModule R α]


-- @@ L109-110 verbatim
instance : SMul R (HermitianMat n α) :=
  ⟨fun c A ↦ ⟨c • A.mat, (IsSelfAdjoint.all _).smul A.H⟩⟩


-- @@ L112-115 verbatim
@[simp, norm_cast]
theorem mat_smul (c : R) (A : HermitianMat n α) :
    (c • A).mat = c • A.mat := by
  rfl


-- @@ L117-120 verbatim
@[simp]
theorem smul_apply (c : R) (A : HermitianMat n α) (i j : n) :
    (c • A) i j = c • A i j := by
  rfl

-- @@ L121-121 verbatim
end smul

-- @@ L122-122 verbatim
section topology


-- @@ L124-124 verbatim
variable [TopologicalSpace α]


-- @@ L126-131 verbatim
instance : TopologicalSpace (HermitianMat n α) :=
  inferInstanceAs (TopologicalSpace (selfAdjoint _))

/- Amusingly, if we don't tag this fun_prop, then fun_prop fails to prove other things! Because
it will look through and see that `HermitianMat.mat` is `Subtype.val` *here*, but not in downstream
applications of the tactic. -/

-- @@ L132-134 verbatim
@[fun_prop]
theorem continuous_mat : Continuous (HermitianMat.mat : HermitianMat n α → Matrix n n α) := by
  fun_prop


-- @@ L136-143 verbatim
lemma continuousOn_iff_coe {X : Type*} [TopologicalSpace X] {s : Set X}
    (f : X → HermitianMat n α) :
    ContinuousOn f s ↔ ContinuousOn (fun x => (f x).mat) s := by
  constructor
  · intro; fun_prop
  · intro h
    rw [continuousOn_iff_continuous_domRestrict] at *
    apply Continuous.subtype_mk h


-- @@ L145-148 verbatim
variable [IsTopologicalAddGroup α]

--In principle, ContinuousAdd and ContinuousNeg just need corresponding instances for α,
-- not all of IsTopologicalAddGroup.


-- @@ L150-151 verbatim
instance : ContinuousAdd (HermitianMat n α) :=
  inferInstanceAs (ContinuousAdd (selfAdjoint _))


-- @@ L153-154 verbatim
instance : ContinuousNeg (HermitianMat n α) :=
  inferInstanceAs (ContinuousNeg (selfAdjoint _))


-- @@ L156-156 verbatim
instance : IsTopologicalAddGroup (HermitianMat n α) where


-- @@ L158-158 verbatim
variable  [TopologicalSpace R] [SMul R α] [ContinuousSMul R α] [StarModule R α]


-- @@ L160-166 verbatim
set_option backward.isDefEq.respectTransparency false in
instance : ContinuousSMul R (HermitianMat n α) where
  continuous_smul := by
    rw [continuous_induced_rng]
    fun_prop

--Shorcut instances:

-- @@ L167-167 verbatim
instance : IsTopologicalAddGroup (HermitianMat n 𝕜) := inferInstance


-- @@ L169-171 verbatim
instance : ContinuousSMul ℝ (HermitianMat n ℂ) := inferInstance

--TODO: Would be good to figure out the general (not just RCLike) version of this.

-- @@ L172-173 verbatim
instance : T3Space (HermitianMat n 𝕜) :=
  inferInstanceAs (T3Space (selfAdjoint _))


-- @@ L175-175 verbatim
end topology


-- @@ L177-177 verbatim
section mulAction

-- @@ L178-178 verbatim
variable [Monoid R] [MulAction R α] [StarModule R α]


-- @@ L180-181 verbatim
instance : MulAction R (HermitianMat n α) :=
  Function.Injective.mulAction Subtype.val Subtype.coe_injective mat_smul


-- @@ L183-183 verbatim
end mulAction

-- @@ L184-184 verbatim
end addgroup

-- @@ L185-185 verbatim
section addcommgroup


-- @@ L187-187 verbatim
variable [AddCommGroup α] [StarAddMonoid α]


-- @@ L189-190 verbatim
instance : AddCommGroup (HermitianMat n α) :=
  AddSubgroup.toAddCommGroup _


-- @@ L192-195 verbatim
@[simp, norm_cast]
theorem mat_finset_sum (f : ι → HermitianMat n α) (s : Finset ι) :
    (∑ i ∈ s, f i).mat = ∑ i ∈ s, (f i).mat := by
  apply AddSubgroup.val_finsetSum


-- @@ L197-197 verbatim
section module


-- @@ L199-199 verbatim
variable [Semiring R] [Module R α] [StarModule R α]


-- @@ L201-202 verbatim
instance : Module R (HermitianMat n α) :=
  inferInstanceAs (Module R (selfAdjoint (Matrix n n α)))


-- @@ L204-204 verbatim
variable [TopologicalSpace α]


-- @@ L206-212 verbatim
/-- The projection from HermitianMat to Matrix, as a continuous linear map. -/
@[simps]
def matₗ : HermitianMat n α →L[R] Matrix n n α where
  toFun := mat
  cont := by fun_prop
  map_add' := by simp
  map_smul' := by simp


-- @@ L214-214 verbatim
end module

-- @@ L215-215 verbatim
end addcommgroup

-- @@ L216-216 verbatim
section ring


-- @@ L218-218 verbatim
variable [NonAssocRing α] [StarRing α] [DecidableEq n]


-- @@ L220-223 verbatim
instance : One (HermitianMat n α) :=
  ⟨1, by
    simp [selfAdjoint.mem_iff, ← Matrix.ext_iff,
      Matrix.one_apply, apply_ite (β := α), eq_comm]⟩


-- @@ L225-227 verbatim
@[simp, norm_cast]
theorem mat_one : (1 : HermitianMat n α).mat = 1 := by
  rfl


-- @@ L229-231 verbatim
@[simp]
theorem mk_one (h : (1 : Matrix n n α).IsHermitian) : ⟨1, h⟩ = (1 : HermitianMat n α) := by
  rfl


-- @@ L233-235 verbatim
@[simp]
theorem one_apply (i j : n) : (1 : HermitianMat n α) i j = (1 : Matrix n n α) i j := by
  rfl


-- @@ L237-237 verbatim
noncomputable instance : AddCommMonoidWithOne (HermitianMat n 𝕜) where


-- @@ L239-242 verbatim
instance [i : Nonempty n] : NeZero (1 : HermitianMat n 𝕜) := by
  constructor
  intro h
  simpa using congr($h i.some i.some)


-- @@ L244-244 verbatim
end ring

-- @@ L245-245 verbatim
section commring


-- @@ L247-247 verbatim
variable [CommRing α] [StarRing α] [DecidableEq m] [Fintype m]

-- @@ L248-248 verbatim
variable (A : HermitianMat m α) (n : ℕ) (z : ℤ)


-- @@ L250-251 verbatim
noncomputable instance instInv : Inv (HermitianMat m α) :=
  ⟨fun x ↦ ⟨x⁻¹, x.H.inv⟩⟩


-- @@ L253-255 verbatim
@[simp, norm_cast]
theorem mat_inv : (A⁻¹).mat = A.mat⁻¹ := by
  rfl


-- @@ L257-259 verbatim
@[simp]
theorem zero_inv : ((0 : HermitianMat m α)⁻¹) = 0 := by
  ext1; simp


-- @@ L261-263 verbatim
@[simp]
theorem one_inv : ((1 : HermitianMat m α)⁻¹) = 1 := by
  ext1; simp


-- @@ L265-266 verbatim
noncomputable instance instPow : Pow (HermitianMat m α) ℕ :=
  ⟨fun x n ↦ ⟨x ^ n, x.H.pow n⟩⟩


-- @@ L268-270 verbatim
@[simp, norm_cast]
theorem mat_pow (n : ℕ) : (A ^ n).mat = A.mat ^ n := by
  rfl


-- @@ L272-274 verbatim
@[simp]
theorem pow_zero : A ^ 0 = 1 := by
  ext1; simp


-- @@ L276-278 verbatim
@[simp]
theorem zero_pow (hn : n ≠ 0): (0 : HermitianMat m α) ^ n = 0 := by
  ext1; simp [hn]


-- @@ L280-282 verbatim
@[simp]
theorem one_pow : ((1 : HermitianMat m α) ^ n) = 1 := by
  ext1; simp


-- @@ L284-285 verbatim
noncomputable instance instZPow : Pow (HermitianMat m α) ℤ :=
  ⟨fun x z ↦ ⟨x ^ z, x.H.zpow z⟩⟩


-- @@ L287-289 verbatim
@[simp]
theorem mat_zpow (z : ℤ) : (A ^ z).mat = A.mat ^ z := by
  rfl


-- @@ L291-293 verbatim
@[simp, norm_cast]
theorem zpow_natCast : A ^ (n : ℤ) = A ^ n := by
  rfl


-- @@ L295-297 verbatim
@[simp]
theorem zpow_zero : A ^ (0 : ℤ) = 1 := by
  ext1; simp


-- @@ L299-301 verbatim
@[simp]
theorem zpow_one : A ^ (1 : ℤ) = A := by
  ext1; simp


-- @@ L303-305 verbatim
@[simp]
theorem one_zpow : ((1 : HermitianMat m α) ^ z) = 1 := by
  ext1; simp


-- @@ L307-309 verbatim
@[simp]
theorem zpow_neg_one : A ^ (-1 : ℤ) = A⁻¹ := by
  ext1; exact A.mat.zpow_neg_one


-- @@ L311-313 verbatim
@[simp]
theorem inv_zpow : A⁻¹ ^ z = (A ^ z)⁻¹ := by
  ext1; exact A.mat.inv_zpow z


-- @@ L315-316 verbatim
add_aesop_rules safe norm (rule_sets := [Commutes])
  [mat_zero, mat_one, mat_smul, mat_add, mat_sub, mat_neg, mat_pow, mat_zpow, mat_inv]


-- @@ L318-322 verbatim
@[aesop safe apply (rule_sets := [Commutes])]
theorem _root_.Matrix.inv_commute {α : Type*} {A : Matrix m m α} [CommRing α] : Commute A⁻¹ A := by
  rcases A.nonsing_inv_cancel_or_zero with h | h
  · simp [Commute, SemiconjBy, h]
  . simp [h]


-- @@ L324-326 expanded
@[aesop safe apply (rule_sets := [Commutes])]
theorem commute_inv_self : Commute A⁻¹.mat A.mat := by
  (aesop
       (config :=
        { introsTransparency? := some .reducible, terminal := true, useSimpAll := false,
          useDefaultSimpSet := false })
       (rule_sets := [Commutes, -default]))


-- @@ L328-330 expanded
@[aesop safe apply (rule_sets := [Commutes])]
theorem commute_self_inv : Commute A.mat A⁻¹.mat := by
  (aesop
       (config :=
        { introsTransparency? := some .reducible, terminal := true, useSimpAll := false,
          useDefaultSimpSet := false })
       (rule_sets := [Commutes, -default]))


-- @@ L332-332 verbatim
end commring

-- @@ L333-333 verbatim
section rclike


-- @@ L335-337 verbatim
variable [Finite n] in
instance FiniteDimensional : FiniteDimensional ℝ (HermitianMat n 𝕜) :=
  FiniteDimensional.finiteDimensional_submodule (selfAdjoint.submodule ℝ (Matrix n n 𝕜))


-- @@ L339-344 verbatim
@[simp]
theorem im_diag_eq_zero (A : HermitianMat n 𝕜) (x : n) :
    RCLike.im (A x x) = 0 := by
  simpa [CharZero.eq_neg_self_iff] using congrArg (RCLike.im <| · x x) A.H.symm

--Repeat it explicitly for Complex.im so that simp can find it

-- @@ L345-348 verbatim
@[simp]
theorem complex_im_eq_zero (A : HermitianMat n ℂ) (x : n) :
    (A x x).im = 0 :=
  A.im_diag_eq_zero x


-- @@ L350-350 verbatim
end rclike


-- @@ L352-352 verbatim
section conj


-- @@ L354-354 verbatim
variable [CommRing α] [StarRing α] [Fintype n]

-- @@ L355-355 verbatim
variable (A : HermitianMat n α)


-- @@ L357-372 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The Hermitian matrix given by conjugating by a (possibly rectangular) Matrix. If we required `B` to be
square, this would apply to any `Semigroup`+`StarMul` (as proved by `IsSelfAdjoint.conjugate`). But this lets
us conjugate to other sizes too, as is done in e.g. Kraus operators. That is, it's a _heterogeneous_ conjguation.
-/
def conj {m} (B : Matrix m n α) : HermitianMat n α →+ HermitianMat m α where
  toFun A :=
    ⟨B * A.mat * B.conjTranspose, by
    ext
    simp only [Matrix.star_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul,
      star_sum, star_mul', star_star, show ∀ (a b : n), star (A.mat b a) = A.mat a b from congrFun₂ A.property]
    rw [Finset.sum_comm]
    congr! 2
    ring⟩
  map_add' _ _ := by ext1; simp [Matrix.mul_add, Matrix.add_mul]
  map_zero' := by simp


-- @@ L374-376 verbatim
theorem conj_apply (B : Matrix m n α) (A : HermitianMat n α) :
    conj B A = ⟨B * A.mat * B.conjTranspose, (conj B A).2⟩ := by
  rfl


-- @@ L378-381 verbatim
@[simp]
theorem conj_apply_mat (B : Matrix m n α) (A : HermitianMat n α) :
    (A.conj B).mat = B * A.mat * B.conjTranspose := by
  rfl


-- @@ L383-386 verbatim
theorem conj_conj {m l} [Fintype m] (B : Matrix m n α) (C : Matrix l m α) :
    (A.conj B).conj C = A.conj (C * B) := by
  ext1
  simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]


-- @@ L388-388 verbatim
variable (B : HermitianMat n α)


-- @@ L390-393 verbatim
set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem conj_zero [DecidableEq n] : A.conj (0 : Matrix m n α) = 0 := by
  simp [conj_apply]


-- @@ L395-398 verbatim
set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem conj_one [DecidableEq n] : A.conj 1 = A := by
  simp [conj_apply]


-- @@ L400-405 verbatim
@[simp]
lemma conj_one_unitary [DecidableEq n] (U : Matrix.unitaryGroup n α) :
    conj U.val 1 = 1 := by
  ext1
  have h : U * U.val.conjTranspose = 1 := U.prop.2
  simp [h]


-- @@ L407-407 verbatim
variable (R : Type*) [Star R] [TrivialStar R] [CommSemiring R] [Algebra R α] [StarModule R α]


-- @@ L409-414 verbatim
/-- `HermitianMat.conj` as an `R`-linear map, where `R` is the ring of relevant reals. -/
def conjLinear {m} (B : Matrix m n α) : HermitianMat n α →ₗ[R] HermitianMat m α where
  toAddHom := conj B
  map_smul' _ _ := by
    ext1
    simp


-- @@ L416-418 verbatim
@[simp]
theorem conjLinear_apply (B : Matrix m n α) : conjLinear R B A = conj B A  := by
  rfl


-- @@ L420-424 verbatim
set_option backward.isDefEq.respectTransparency false in
@[fun_prop]
lemma continuous_conj (ρ : HermitianMat n 𝕜) : Continuous (ρ.conj (m := m) ·) := by
  simp only [HermitianMat.conj, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  fun_prop


-- @@ L426-426 verbatim
end conj


-- @@ L428-428 verbatim
section eigenspace


-- @@ L430-430 verbatim
variable [Fintype n] [DecidableEq n] (A : HermitianMat n 𝕜)


-- @@ L432-434 verbatim
instance [i : Nonempty n] : FaithfulSMul ℝ (HermitianMat n 𝕜) where
  eq_of_smul_eq_smul h := by
    simpa [RCLike.smul_re, -mat_apply] using congr(RCLike.re ($(h 1).val i.some i.some))


-- @@ L436-439 verbatim
/-- The continuous linear map associated with a Hermitian matrix. -/
noncomputable def lin : EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n where
  toLinearMap := A.mat.toEuclideanLin
  cont := LinearMap.continuous_of_finiteDimensional _


-- @@ L441-443 verbatim
@[simp]
theorem isSymmetric : A.lin.IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.symm.mp A.H


-- @@ L445-447 verbatim
@[simp]
theorem lin_zero : (0 : HermitianMat n 𝕜).lin = 0 := by
  simp [lin]; rfl


-- @@ L449-451 verbatim
@[simp]
theorem lin_one : (1 : HermitianMat n 𝕜).lin = 1 := by
  simp [lin]; rfl


-- @@ L453-454 verbatim
noncomputable def eigenspace (μ : 𝕜) : Submodule 𝕜 (EuclideanSpace 𝕜 n) :=
  Module.End.eigenspace A.lin μ


-- @@ L456-459 verbatim
/-- The kernel of a Hermitian matrix `A` as a submodule of Euclidean space, defined by
`LinearMap.ker A.toMat.toEuclideanLin`. Equivalently, the zero-eigenspace. -/
noncomputable def ker : Submodule 𝕜 (EuclideanSpace 𝕜 n) :=
  LinearMap.ker A.lin.toLinearMap


-- @@ L461-462 verbatim
theorem mem_ker_iff_mulVec_zero (x : EuclideanSpace 𝕜 n) : x ∈ A.ker ↔ A.mat.mulVec x = 0 := by
  simp [ker, LinearMap.mem_ker, lin, Matrix.toLpLin_apply]


-- @@ L464-467 verbatim
/-- The kernel of a Hermitian matrix is its zero eigenspace. -/
theorem ker_eq_eigenspace_zero : A.ker = A.eigenspace 0 := by
  ext
  simp [ker, eigenspace]


-- @@ L469-471 verbatim
@[simp]
theorem ker_zero : (0 : HermitianMat n 𝕜).ker = ⊤ := by
  simp [ker]


-- @@ L473-475 verbatim
@[simp]
theorem ker_one : (1 : HermitianMat n 𝕜).ker = ⊥ := by
  simp [ker]; rfl


-- @@ L477-479 verbatim
theorem ker_pos_smul {c : ℝ} (hc : c ≠ 0) : (c • A).ker = A.ker := by
  ext x
  simp [mem_ker_iff_mulVec_zero, Matrix.smul_mulVec, hc]


-- @@ L481-484 verbatim
/-- The support of a Hermitian matrix `A` as a submodule of Euclidean space, defined by
`LinearMap.range A.toMat.toEuclideanLin`. Equivalently, the sum of all nonzero eigenspaces. -/
noncomputable def support : Submodule 𝕜 (EuclideanSpace 𝕜 n) :=
  LinearMap.range A.lin.toLinearMap


-- @@ L486-488 verbatim
/-- The support of a Hermitian matrix is the sum of its nonzero eigenspaces. -/
theorem support_eq_sup_eigenspace_nonzero : A.support = ⨆ μ ≠ 0, A.eigenspace μ := by
  exact A.lin.support_eq_sup_eigenspace_nonzero A.isSymmetric


-- @@ L490-492 verbatim
@[simp]
theorem support_zero : (0 : HermitianMat n 𝕜).support = ⊥ := by
  simp [support]


-- @@ L494-496 verbatim
@[simp]
theorem support_one : (1 : HermitianMat n 𝕜).support = ⊤ := by
  simpa [support] using LinearMap.ker_eq_bot_iff_range_eq_top.mp rfl


-- @@ L498-502 verbatim
@[simp]
theorem ker_orthogonal_eq_support : A.kerᗮ = A.support := by
  rw [ker, support]
  convert ContinuousLinearMap.orthogonal_ker A.lin
  simp


-- @@ L504-508 verbatim
@[simp]
theorem support_orthogonal_eq_range : A.supportᗮ = A.ker := by
  rw [ker, support]
  convert! ContinuousLinearMap.orthogonal_range A.lin
  simp


-- @@ L510-510 verbatim
end eigenspace


-- @@ L512-512 verbatim
section diagonal


-- @@ L514-514 verbatim
variable {𝕜 : Type*} [RCLike 𝕜] [DecidableEq n]


-- @@ L516-519 verbatim
variable (𝕜) in
def diagonal (f : n → ℝ) : HermitianMat n 𝕜 :=
  ⟨Matrix.diagonal (f ·),
    by simp [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]⟩


-- @@ L521-521 verbatim
variable (f g : n → ℝ)


-- @@ L523-525 verbatim
@[simp]
theorem diagonal_mat : (diagonal 𝕜 f).mat = Matrix.diagonal (f · : n → 𝕜) := by
  rfl


-- @@ L527-529 verbatim
@[simp]
theorem diagonal_zero : (diagonal 𝕜 0) = (0 : HermitianMat n 𝕜) := by
  ext1; simp


-- @@ L531-533 verbatim
@[simp]
theorem diagonal_one : (diagonal 𝕜 1) = (1 : HermitianMat n 𝕜) := by
  ext; rw [diagonal_mat]; simp


-- @@ L535-536 verbatim
lemma diagonal_add : diagonal 𝕜 (f + g) = diagonal 𝕜 f + diagonal 𝕜 g := by
  ext1; simp


-- @@ L538-539 verbatim
lemma diagonal_add_apply : diagonal 𝕜 (fun x ↦ f x + g x) = diagonal 𝕜 f + diagonal 𝕜 g := by
  ext1; simp


-- @@ L541-542 verbatim
lemma diagonal_sub : diagonal 𝕜 (f - g) = diagonal 𝕜 f - diagonal 𝕜 g := by
  ext1; simp


-- @@ L544-545 verbatim
theorem diagonal_mul (c : ℝ) : diagonal 𝕜 (fun x ↦ c * f x) = c • diagonal 𝕜 f := by
  ext1; simp [← Matrix.diagonal_smul]


-- @@ L547-553 verbatim
set_option backward.isDefEq.respectTransparency false in
theorem diagonal_conj_diagonal [Fintype n] :
    (diagonal 𝕜 f).conj (diagonal 𝕜 g) = diagonal 𝕜 (fun i ↦ f i * (g i)^2) := by
  ext1
  simp [diagonal, conj]
  intro
  ring


-- @@ L555-561 verbatim
/--
A Hermitian matrix is equal to its diagonalization conjugated by its eigenvector unitary matrix.
-/
lemma eq_conj_diagonal [Fintype n] (A : HermitianMat n 𝕜) :
    A = (diagonal 𝕜 A.H.eigenvalues).conj A.H.eigenvectorUnitary := by
  ext1
  exact Matrix.IsHermitian.spectral_theorem A.2


-- @@ L563-563 verbatim
end diagonal


-- @@ L565-565 verbatim
section kronecker

-- @@ L566-566 verbatim
open Kronecker


-- @@ L568-568 verbatim
variable {p q : Type*}

-- @@ L569-569 verbatim
variable [CommRing α] [StarRing α]


-- @@ L571-574 verbatim
/-- The kronecker product of two HermitianMats, see `Matrix.kroneckerMap`. -/
def kronecker (A : HermitianMat m α) (B : HermitianMat n α) : HermitianMat (m × n) α where
  val := A.mat ⊗ₖ B.mat
  property := Matrix.kroneckerMap_IsHermitian A.H B.H


-- @@ L576-577 verbatim
@[inherit_doc HermitianMat.kronecker]
scoped[HermitianMat] infixl:100 " ⊗ₖ " => HermitianMat.kronecker


-- @@ L579-582 expanded
@[simp, norm_cast]
theorem kronecker_mat (A : HermitianMat m α) (B : HermitianMat n α) :
    (A ⊗ₖ B).mat = A.mat ⊗ₖ B.mat := by rfl


-- @@ L584-586 expanded
@[simp]
theorem zero_kronecker (A : HermitianMat m α) : (0 : HermitianMat n α) ⊗ₖ A = 0 := by ext1; simp


-- @@ L588-590 expanded
@[simp]
theorem kronecker_zero (A : HermitianMat m α) : A ⊗ₖ (0 : HermitianMat n α) = 0 := by ext1; simp


-- @@ L592-595 expanded
variable [DecidableEq m] [DecidableEq n] in
@[simp]
theorem kronecker_one_one : (1 : HermitianMat m α) ⊗ₖ (1 : HermitianMat n α) = 1 := by ext1; simp


-- @@ L597-599 expanded
variable (A B : HermitianMat m α) (C : HermitianMat n α) in
theorem add_kronecker : (A + B) ⊗ₖ C = A ⊗ₖ C + B ⊗ₖ C := by ext1; simp [Matrix.add_kronecker]


-- @@ L601-603 expanded
variable (A : HermitianMat m α) (B C : HermitianMat n α) in
theorem kronecker_add : A ⊗ₖ (B + C) = A ⊗ₖ B + A ⊗ₖ C := by ext1; simp [Matrix.kronecker_add]


-- @@ L605-608 expanded
lemma kronecker_diagonal [DecidableEq m] [DecidableEq n] (d₁ : m → ℝ) (d₂ : n → ℝ) :
    (diagonal 𝕜 d₁ ⊗ₖ diagonal 𝕜 d₂) = diagonal 𝕜 (fun (i : m × n) => d₁ i.1 * d₂ i.2) :=
  by
  ext1
  simp [Matrix.diagonal_kronecker_diagonal]


-- @@ L610-621 expanded
/-- A ⊗ₖ B always commutes with C ⊗ₖ D if the pairs commute.
-/
--Apply safely. It will almost always work, but there are cases where it's not sound,
-- such as `A = 0`. But these can all get easily simp'ed away anyway.

@[aesop safe apply (rule_sets := [Commutes])]
theorem kron_commute [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {A C : HermitianMat m α} {B D : HermitianMat n α} (hAC : Commute A.mat C.mat)
    (hBD : Commute B.mat D.mat) : Commute (A ⊗ₖ B).mat (C ⊗ₖ D).mat :=
  by
  rw [commute_iff_eq] at hAC hBD ⊢
  simp only [kronecker_mat, ← Matrix.mul_kronecker_mul, hAC, hBD]


-- @@ L623-634 expanded
/-- A ⊗ₖ 1 always commutes with 1 ⊗ₖ B
-/
@[aesop safe apply (rule_sets := [Commutes])] --redundant but important shortcut
  
theorem kron_id_commute_id_kro [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : HermitianMat m α) (B : HermitianMat n α) :
    Commute (A ⊗ₖ (1 : HermitianMat n α)).mat ((1 : HermitianMat m α) ⊗ₖ B).mat := by
  (aesop
       (config :=
        { introsTransparency? := some .reducible, terminal := true, useSimpAll := false,
          useDefaultSimpSet := false })
       (rule_sets := [Commutes, -default]))


-- @@ L635-639 expanded
lemma kronecker_conj [Fintype m] [Fintype n] (A : HermitianMat m α) (B : HermitianMat n α)
    (C : Matrix p m α) (D : Matrix q n α) : (A ⊗ₖ B).conj (C ⊗ₖ D) = (A.conj C) ⊗ₖ (B.conj D) :=
  by
  ext1
  exact Matrix.kronecker_conj_eq A.mat B.mat C D


-- @@ L641-641 verbatim
end kronecker


-- @@ L643-643 verbatim
section more_range_stuff


-- @@ L645-649 verbatim
variable {d d₂ : Type*} [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂]

/-
If the range of a Hermitian matrix is contained in its kernel, the matrix is zero.
-/

-- @@ L650-674 verbatim
theorem range_le_ker_imp_zero {A : HermitianMat d 𝕜}
    (h : LinearMap.range A.mat.toEuclideanLin ≤ LinearMap.ker A.mat.toEuclideanLin) : A = 0 := by
  rw [HermitianMat.ext_iff, mat_zero]
  ext i j
  have hA_sq : (A.mat * A.mat) = 0 := by
    simp_all only [SetLike.le_def, LinearMap.mem_range, LinearMap.mem_ker, forall_exists_index,
      forall_apply_eq_imp_iff]
    simp_all only [← Matrix.ext_iff, Matrix.mul_apply, mat_apply, Matrix.zero_apply]
    intro i j
    specialize h ( EuclideanSpace.single j 1 )
    simpa [ Matrix.mulVec, dotProduct ] using congr(WithLp.ofLp $(h) i)
  simp_all only [mat_apply, Matrix.zero_apply]
  replace hA_sq := congr_fun ( congr_fun hA_sq i ) i
  simp_all only [Matrix.mul_apply, mat_apply, Matrix.zero_apply] ;
  -- Since $A$ is Hermitian, we have $A i x * A x i = |A i x|^2$.
  have h_abs : ∀ x, (A i x) * (A x i) = ‖A i x‖ ^ 2 := by
    intro x; have := A.2
    simp_all only [val_eq_coe, sq] ;
    have := congr_fun ( congr_fun this i ) x
    simp_all only [Matrix.star_apply, mat_apply, RCLike.star_def] ;
    simp only [← this, mul_comm, RCLike.norm_conj];
    simp [ ← sq, RCLike.mul_conj ];
  simp_rw [h_abs] at hA_sq
  norm_cast at hA_sq
  simp_all [Finset.sum_eq_zero_iff_of_nonneg]


-- @@ L676-718 verbatim
/--
If ker M ⊆ ker A, then range (A Mᴴ) = range A.
-/
theorem _root_.Matrix.range_mul_conjTranspose_of_ker_le_ker {A : Matrix d d 𝕜} {M : Matrix d₂ d 𝕜}
    (h : LinearMap.ker M.toEuclideanLin ≤ LinearMap.ker A.toEuclideanLin) :
    LinearMap.range (A * M.conjTranspose).toEuclideanLin = LinearMap.range A.toEuclideanLin := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    use (M.conjTranspose.toEuclideanLin) y;
    simp [Matrix.toEuclideanLin]
  · intro x hx;
    -- Since $x \in \text{range}(A)$, there exists $y \in \text{range}(Mᴴ)$ such that $A y = x$.
    obtain ⟨y, hy⟩ : ∃ y ∈ LinearMap.range (Matrix.toEuclideanLin (M.conjTranspose)), A.toEuclideanLin y = x := by
      have h_range_MH : LinearMap.range (Matrix.toEuclideanLin (M.conjTranspose)) = (LinearMap.ker (Matrix.toEuclideanLin M))ᗮ := by
        have h_orthogonal : (LinearMap.range (Matrix.toEuclideanLin (M.conjTranspose)))ᗮ = LinearMap.ker (Matrix.toEuclideanLin M) := by
          ext x
          rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
          simp only [Submodule.mem_orthogonal, LinearMap.mem_ker, LinearMap.mem_range]
          constructor
          · intro h
            rw [← inner_self_eq_zero (𝕜 := 𝕜)]
            have : ∀ y, @inner 𝕜 _ _ y (Matrix.toEuclideanLin M x) = 0 := by
              intro y
              rw [← LinearMap.adjoint_inner_left]
              exact h _ ⟨y, rfl⟩
            exact this _
          · intro h y ⟨z, hz⟩
            rw [← hz, LinearMap.adjoint_inner_left, h, inner_zero_right]
        rw [← h_orthogonal, Submodule.orthogonal_orthogonal]
      obtain ⟨ y, rfl ⟩ := hx;
      -- Since $y$ is in the range of $Mᴴ$, we can write $y$ as $y = y_1 + y_2$ where $y_1 \in \text{range}(Mᴴ)$ and $y_2 \in \text{ker}(M)$.
      obtain ⟨y1, y2, hy1, hy2, hy⟩ : ∃ y1 y2 : EuclideanSpace 𝕜 d, y1 ∈ LinearMap.range (Matrix.toEuclideanLin (M.conjTranspose)) ∧ y2 ∈ LinearMap.ker (Matrix.toEuclideanLin M) ∧ y = y1 + y2 := by
        have h_decomp : ∀ y : EuclideanSpace 𝕜 d, ∃ y1 ∈ LinearMap.range (Matrix.toEuclideanLin (M.conjTranspose)), ∃ y2 ∈ LinearMap.ker (Matrix.toEuclideanLin M), y = y1 + y2 := by
          intro y
          have h_decomp : y ∈ (LinearMap.range (Matrix.toEuclideanLin (M.conjTranspose))) ⊔ (LinearMap.ker (Matrix.toEuclideanLin M)) := by
            rw [ h_range_MH ];
            rw [ sup_comm, Submodule.sup_orthogonal_of_hasOrthogonalProjection ];
            exact Submodule.mem_top;
          rw [ Submodule.mem_sup ] at h_decomp ; tauto;
        exact ⟨ _, _, h_decomp y |> Classical.choose_spec |> And.left, h_decomp y |> Classical.choose_spec |> And.right |> Classical.choose_spec |> And.left, h_decomp y |> Classical.choose_spec |> And.right |> Classical.choose_spec |> And.right ⟩;
      exact ⟨ y1, hy1, by rw [ hy, map_add, LinearMap.mem_ker.mp ( h hy2 ) ] ; simp ⟩;
    obtain ⟨ z, rfl ⟩ := hy.1;
    exact ⟨ z, by simpa [ Matrix.toEuclideanLin ] using hy.2 ⟩


-- @@ L720-730 verbatim
theorem conj_ne_zero {A : HermitianMat d 𝕜} {M : Matrix d₂ d 𝕜} (hA : A ≠ 0)
    (h : LinearMap.ker M.toEuclideanLin ≤ A.ker) : A.conj M ≠ 0 := by
  by_contra h_contra
  have h_range : LinearMap.range A.mat.toEuclideanLin ≤ LinearMap.ker A.mat.toEuclideanLin := by
    have h_range : LinearMap.range (A.mat * M.conjTranspose).toEuclideanLin ≤ LinearMap.ker M.toEuclideanLin := by
      rintro x ⟨y, rfl⟩
      replace h_contra := congr($(h_contra).mat)
      simp_all [Matrix.toLpLin_apply, Matrix.mul_assoc]
    rw [← Matrix.range_mul_conjTranspose_of_ker_le_ker h]
    exact h_range.trans h
  exact hA (range_le_ker_imp_zero h_range)


-- @@ L732-735 verbatim
theorem conj_ne_zero_iff {A : HermitianMat d 𝕜} {M : Matrix d₂ d 𝕜}
    (h : LinearMap.ker M.toEuclideanLin ≤ A.ker) : A.conj M ≠ 0 ↔ A ≠ 0  := by
  refine ⟨?_, (conj_ne_zero · h)⟩
  intro h rfl; grind


-- @@ L737-737 verbatim
section spectrum


-- @@ L739-739 verbatim
variable [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]


-- @@ L741-743 verbatim
theorem _root_.Matrix.IsHermitian.spectrum_rcLike {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    RCLike.ofReal '' spectrum ℝ A = spectrum 𝕜 A := by
  rw [hA.spectrum_eq_image_range, hA.spectrum_real_eq_range_eigenvalues]


-- @@ L745-750 verbatim
/-- We fix a simp-normal form that, for HermitianMat, we always work in terms
of the real spectrum. -/
@[simp]
theorem spectrum_rcLike (A : HermitianMat n 𝕜) :
    spectrum 𝕜 A.mat = RCLike.ofReal '' spectrum ℝ A.mat := by
  exact A.H.spectrum_rcLike.symm


-- @@ L752-765 verbatim
theorem ne_zero_iff_ne_zero_spectrum (A : HermitianMat n 𝕜) :
    A ≠ 0 ↔ ∃ x ∈ spectrum ℝ A.mat, x ≠ 0 := by
  constructor;
  · intro h_nonzero
    contrapose! h_nonzero
    simp only [HermitianMat.ext_iff, mat_zero]
    rw [A.H.spectral_theorem]
    ext i j
    simp [Matrix.mul_apply, Matrix.diagonal]
    refine Finset.sum_eq_zero fun x _ ↦ ?_
    simp [h_nonzero _ <| A.H.spectrum_real_eq_range_eigenvalues.symm ▸ Set.mem_range_self _]
  · rintro ⟨x, hx, hx'⟩ h
    simp [h, spectrum, resolventSet, Algebra.algebraMap_eq_smul_one,
      hx', Matrix.isUnit_iff_isUnit_det] at hx


-- @@ L767-771 expanded
open scoped Pointwise in
theorem spectrum_prod {A : HermitianMat m 𝕜} {B : HermitianMat n 𝕜} :
    spectrum ℝ (HermitianMat.kronecker A B).mat = spectrum ℝ A.mat * spectrum ℝ B.mat :=
  Matrix.spectrum_prod A.H B.H


-- @@ L773-775 verbatim
end spectrum

--Shortcut instance

-- @@ L776-777 verbatim
noncomputable instance : AddCommMonoid (HermitianMat d ℂ) :=
  inferInstance
