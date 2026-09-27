/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import LeanPool.Monlib4.LinearAlgebra.Matrix.IsAlmostHermitian
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Matrix.PosDef
import LeanPool.Monlib4.LinearAlgebra.End
import LeanPool.Monlib4.LinearAlgebra.MySpec
import LeanPool.Monlib4.LinearAlgebra.TensorProduct.BasicLemmas
import LeanPool.Monlib4.RepTheory.AutMat
import Mathlib.Analysis.Matrix.Order


-- @@ L17-25 verbatim
/-!
# Inner Automorphisms

This file ports the upstream monlib4 unitary inner-automorphism interface.  In
current Mathlib the general star-algebra automorphism by unitary conjugation is
available as `Unitary.conjStarAlgAut`; the declarations here keep monlib4's
names for the matrix-algebra specialization and its trace, spectrum, and
Hermitian-preservation lemmas.
-/


-- @@ L27-27 verbatim
@[expose] public section


-- @@ L29-29 verbatim
open scoped ComplexOrder


-- @@ L31-33 verbatim
lemma RCLike.neg_ofReal {𝕜 : Type*} [RCLike 𝕜] (a : ℝ) :
    (a : 𝕜) < 0 ↔ a < 0 :=
  RCLike.ofReal_lt_zero


-- @@ L35-37 verbatim
instance Pi.coe {k : Type _} {s r : k → Type _} [∀ i, CoeTC (s i) (r i)] :
    CoeTC (Π i, s i) (Π i, r i) :=
  ⟨fun U i => U i⟩


-- @@ L39-42 verbatim
lemma Pi.coe_eq {k : Type _} {s r : k → Type _} [∀ i, CoeTC (s i) (r i)]
    (U : Π i, s i) :
    HEq (fun i => (U i : r i)) (↑U : Π i, r i) :=
  HEq.rfl


-- @@ L44-44 verbatim
section


-- @@ L46-46 verbatim
variable {n 𝕜 : Type _} [Fintype n] [Field 𝕜] [StarRing 𝕜]


-- @@ L48-52 verbatim
@[simp]
theorem StarAlgEquiv.trace_preserving (f : Matrix n n 𝕜 ≃⋆ₐ[𝕜] Matrix n n 𝕜)
    (x : Matrix n n 𝕜) : (f x).trace = x.trace := by
  classical
  exact Matrix.aut_mat_inner_trace_preserving f.toAlgEquiv x


-- @@ L54-54 verbatim
end


-- @@ L56-56 verbatim
namespace unitary


-- @@ L58-62 verbatim
/-- The star-algebra automorphism given by conjugation with a unitary element. -/
abbrev innerAutStarAlg (K : Type _) {R : Type _} [Semiring R] [StarMul R]
    [SMul K R] [IsScalarTower K R R] [SMulCommClass K R R] (a : unitary R) :
    R ≃⋆ₐ[K] R :=
  Unitary.conjStarAlgAut K R a


-- @@ L64-67 verbatim
theorem innerAutStarAlg_apply {K R : Type _} [Semiring R] [StarMul R]
    [SMul K R] [IsScalarTower K R R] [SMulCommClass K R R] (U : unitary R) (x : R) :
    innerAutStarAlg K U x = U * x * (star U : unitary R) :=
  rfl


-- @@ L69-72 verbatim
theorem innerAutStarAlg_apply' {K R : Type _} [Semiring R] [StarMul R]
    [SMul K R] [IsScalarTower K R R] [SMulCommClass K R R] (U : unitary R) (x : R) :
    innerAutStarAlg K U x = U * x * (U⁻¹ : unitary R) :=
  rfl


-- @@ L74-77 verbatim
theorem innerAutStarAlg_apply'' {K R : Type _} [Semiring R] [StarMul R]
    [SMul K R] [IsScalarTower K R R] [SMulCommClass K R R] (U : unitary R) (x : R) :
    innerAutStarAlg K U x = U * x * star (U : R) :=
  rfl


-- @@ L79-82 verbatim
theorem innerAutStarAlg_symm_apply {K R : Type _} [Semiring R] [StarMul R]
    [SMul K R] [IsScalarTower K R R] [SMulCommClass K R R] (U : unitary R) (x : R) :
    (innerAutStarAlg K U).symm x = (star U : unitary R) * x * U :=
  rfl


-- @@ L84-87 verbatim
theorem innerAutStarAlg_symm_apply' {K R : Type _} [Semiring R] [StarMul R]
    [SMul K R] [IsScalarTower K R R] [SMulCommClass K R R] (U : unitary R) (x : R) :
    (innerAutStarAlg K U).symm x = (U⁻¹ : unitary R) * x * U :=
  rfl


-- @@ L89-92 verbatim
theorem innerAutStarAlg_symm_apply'' {K R : Type _} [Semiring R] [StarMul R]
    [SMul K R] [IsScalarTower K R R] [SMulCommClass K R R] (U : unitary R) (x : R) :
    (innerAutStarAlg K U).symm x = star (U : R) * x * U :=
  rfl


-- @@ L94-97 verbatim
theorem innerAutStarAlg_symm {K R : Type _} [Semiring R] [StarMul R]
    [SMul K R] [IsScalarTower K R R] [SMulCommClass K R R] (U : unitary R) :
    (innerAutStarAlg K U).symm = innerAutStarAlg K (star U) :=
  Unitary.conjStarAlgAut_symm U


-- @@ L99-103 verbatim
theorem innerAutStarAlg_symm' {K R : Type _} [Semiring R] [StarMul R]
    [SMul K R] [IsScalarTower K R R] [SMulCommClass K R R] (U : unitary R) :
    (innerAutStarAlg K U).symm = innerAutStarAlg K U⁻¹ := by
  rw [innerAutStarAlg_symm]
  rfl


-- @@ L105-107 verbatim
instance instCoeTCSubtypeMemSubmonoidLeanPool (R : Type*) [Monoid R] [StarMul R] :
    CoeTC (unitary R) R :=
  ⟨fun x => x⟩


-- @@ L109-115 verbatim
theorem pi_mem {k : Type _} {s : k → Type _} [∀ i, Semiring (s i)]
    [∀ i, StarMul (s i)] (U : Π i, unitary (s i)) :
    (fun i => (U i : s i)) ∈ unitary (∀ i, s i) := by
  rw [Unitary.mem_iff]
  simp only [Pi.mul_def, Pi.star_apply, Unitary.coe_star_mul_self]
  simp only [← Unitary.coe_star, Unitary.coe_mul_star_self, and_self]
  rfl


-- @@ L117-122 verbatim
/-- Build a unitary element of a dependent function type from pointwise unitaries. -/
@[inline]
abbrev pi {k : Type _} {s : k → Type _} [∀ i, Semiring (s i)]
    [∀ i, StarMul (s i)] (U : ∀ i, unitary (s i)) :
    unitary (∀ i, s i) :=
  ⟨fun i => U i, pi_mem U⟩


-- @@ L124-127 verbatim
theorem pi_apply {k : Type _} {s : k → Type _} [∀ i, Semiring (s i)]
    [∀ i, StarMul (s i)] (U : ∀ i, unitary (s i)) {i : k} :
    (pi U : ∀ i, s i) i = U i :=
  rfl


-- @@ L129-129 verbatim
end unitary


-- @@ L131-131 verbatim
namespace Matrix


-- @@ L133-133 verbatim
variable {n 𝕜 : Type _} [Fintype n]


-- @@ L135-135 verbatim
section


-- @@ L137-137 verbatim
variable [Field 𝕜] [StarRing 𝕜]


-- @@ L139-142 verbatim
theorem _root_.Matrix.unitaryGroup.coe_hMul_star_self [DecidableEq n]
    (a : Matrix.unitaryGroup n 𝕜) :
    (HMul.hMul a (star a) : Matrix n n 𝕜) = (1 : Matrix n n 𝕜) := by
  simp_all


-- @@ L144-147 verbatim
theorem _root_.Matrix.unitaryGroup.star_coe_eq_coe_star [DecidableEq n]
    (U : unitaryGroup n 𝕜) :
    (star (U : unitaryGroup n 𝕜) : Matrix n n 𝕜) = (star U : unitaryGroup n 𝕜) :=
  rfl


-- @@ L149-153 verbatim
/-- The star-algebra automorphism `x ↦ U * x * U⁻¹`. -/
@[inline]
abbrev innerAutStarAlg [DecidableEq n] (a : unitaryGroup n 𝕜) :
    Matrix n n 𝕜 ≃⋆ₐ[𝕜] Matrix n n 𝕜 :=
  unitary.innerAutStarAlg 𝕜 a


-- @@ L155-155 verbatim
open scoped Matrix


-- @@ L157-159 verbatim
theorem innerAutStarAlg_apply [DecidableEq n] (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    innerAutStarAlg U x = U * x * (star U : unitaryGroup n 𝕜) :=
  rfl


-- @@ L161-163 verbatim
theorem innerAutStarAlg_apply' [DecidableEq n] (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    innerAutStarAlg U x = U * x * (U⁻¹ : unitaryGroup n 𝕜) :=
  rfl


-- @@ L165-168 verbatim
theorem innerAutStarAlg_symm_apply [DecidableEq n] (U : unitaryGroup n 𝕜)
    (x : Matrix n n 𝕜) :
    (innerAutStarAlg U).symm x = (star U : unitaryGroup n 𝕜) * x * U :=
  rfl


-- @@ L170-173 verbatim
theorem innerAutStarAlg_symm_apply' [DecidableEq n] (U : unitaryGroup n 𝕜)
    (x : Matrix n n 𝕜) :
    (innerAutStarAlg U).symm x = (U⁻¹ : unitaryGroup n 𝕜) * x * U :=
  rfl


-- @@ L175-177 verbatim
theorem innerAutStarAlg_symm [DecidableEq n] (U : unitaryGroup n 𝕜) :
    (innerAutStarAlg U).symm = innerAutStarAlg U⁻¹ :=
  unitary.innerAutStarAlg_symm' U


-- @@ L179-182 verbatim
/-- The unitary inner automorphism as a linear map. -/
abbrev innerAut [DecidableEq n] (U : unitaryGroup n 𝕜) :
    Matrix n n 𝕜 →ₗ[𝕜] Matrix n n 𝕜 :=
  (innerAutStarAlg U).toAlgEquiv.toLinearMap


-- @@ L184-187 verbatim
@[simp]
theorem innerAut_coe [DecidableEq n] (U : unitaryGroup n 𝕜) :
    ⇑(innerAut U) = innerAutStarAlg U :=
  rfl


-- @@ L189-192 verbatim
theorem innerAut_inv_coe [DecidableEq n] (U : unitaryGroup n 𝕜) :
    ⇑(innerAut U⁻¹) = (innerAutStarAlg U).symm := by
  simp_rw [innerAutStarAlg_symm]
  rfl


-- @@ L194-196 verbatim
theorem innerAut_apply [DecidableEq n] (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    innerAut U x = U * x * (U⁻¹ : unitaryGroup n 𝕜) :=
  rfl


-- @@ L198-200 verbatim
theorem innerAut_apply' [DecidableEq n] (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    innerAut U x = U * x * (star U : unitaryGroup n 𝕜) :=
  rfl


-- @@ L202-204 verbatim
theorem innerAut_inv_apply [DecidableEq n] (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    innerAut U⁻¹ x = (U⁻¹ : unitaryGroup n 𝕜) * x * U := by
  simp only [innerAut_apply, inv_inv _]


-- @@ L206-208 verbatim
theorem innerAut_star_apply [DecidableEq n] (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    innerAut (star U) x = (star U : unitaryGroup n 𝕜) * x * U := by
  simp_rw [innerAut_apply', star_star]


-- @@ L210-214 verbatim
theorem innerAut_conjTranspose [DecidableEq n] (U : unitaryGroup n 𝕜)
    (x : Matrix n n 𝕜) :
    (innerAut U x)ᴴ = innerAut U xᴴ := by
  change star ((innerAutStarAlg U) x) = (innerAutStarAlg U) (star x)
  exact (map_star (innerAutStarAlg U) x).symm


-- @@ L216-219 verbatim
theorem innerAut_comp_innerAut [DecidableEq n] (U₁ U₂ : unitaryGroup n 𝕜) :
    innerAut U₁ ∘ₗ innerAut U₂ = innerAut (U₁ * U₂) := by
  simp_rw [LinearMap.ext_iff, LinearMap.comp_apply, innerAut_apply, UnitaryGroup.inv_apply,
    UnitaryGroup.mul_apply, star_mul, Matrix.mul_assoc, forall_true_iff]


-- @@ L221-224 verbatim
theorem innerAut_apply_innerAut [DecidableEq n] (U₁ U₂ : unitaryGroup n 𝕜)
    (x : Matrix n n 𝕜) :
    innerAut U₁ (innerAut U₂ x) = innerAut (U₁ * U₂) x := by
  rw [← innerAut_comp_innerAut, LinearMap.comp_apply]


-- @@ L226-229 verbatim
theorem innerAut_eq_iff [DecidableEq n] (U : unitaryGroup n 𝕜) (x y : Matrix n n 𝕜) :
    innerAut U x = y ↔ x = innerAut U⁻¹ y := by
  rw [innerAut_coe, innerAut_inv_coe]
  exact (innerAutStarAlg U).toEquiv.eq_symm_apply.symm


-- @@ L231-234 verbatim
theorem _root_.Matrix.unitaryGroup.toLinearEquiv_apply [DecidableEq n] (U : unitaryGroup n 𝕜)
    (x : n → 𝕜) :
    (UnitaryGroup.toLinearEquiv U) x = (↑(U : unitaryGroup n 𝕜) : Matrix n n 𝕜).mulVec x :=
  rfl


-- @@ L236-239 verbatim
theorem _root_.Matrix.unitaryGroup.toLinearEquiv_eq [DecidableEq n]
    (U : unitaryGroup n 𝕜) (x : n → 𝕜) :
    (UnitaryGroup.toLinearEquiv U) x = (UnitaryGroup.toLin' U) x :=
  rfl


-- @@ L241-244 verbatim
theorem _root_.Matrix.unitaryGroup.toLin'_apply [DecidableEq n] (U : unitaryGroup n 𝕜)
    (x : n → 𝕜) :
    (UnitaryGroup.toLin' U) x = (↑(U : unitaryGroup n 𝕜) : Matrix n n 𝕜).mulVec x :=
  rfl


-- @@ L246-249 verbatim
theorem _root_.Matrix.unitaryGroup.toLin'_eq [DecidableEq n] (U : unitaryGroup n 𝕜)
    (x : n → 𝕜) :
    (UnitaryGroup.toLin' U) x = (toLin' U) x :=
  rfl


-- @@ L251-255 verbatim
omit [StarRing 𝕜] in
theorem toLinAlgEquiv'_apply' [DecidableEq n] (x : Matrix n n 𝕜) :
    toLinAlgEquiv' x =
      (toLin' : Matrix n n 𝕜 ≃ₗ[𝕜] (n → 𝕜) →ₗ[𝕜] (n → 𝕜)) x :=
  rfl


-- @@ L257-262 verbatim
/-- The spectrum of `U * x * U⁻¹` is the spectrum of `x`. -/
theorem _root_.Matrix.innerAut.spectrum_eq [DecidableEq n] (U : unitaryGroup n 𝕜)
    (x : Matrix n n 𝕜) :
    spectrum 𝕜 (toLin' (innerAut U x)) = spectrum 𝕜 (toLin' x) := by
  simp_rw [← toLinAlgEquiv'_apply', AlgEquiv.spectrum_eq, innerAut_coe,
    AlgEquiv.spectrum_eq]


-- @@ L264-266 verbatim
theorem innerAut_one [DecidableEq n] : innerAut (1 : unitaryGroup n 𝕜) = 1 := by
  simp_rw [LinearMap.ext_iff, innerAut_apply, UnitaryGroup.inv_apply, UnitaryGroup.one_apply,
    star_one, Matrix.mul_one, Matrix.one_mul, Module.End.one_apply, forall_true_iff]


-- @@ L268-273 verbatim
theorem innerAut_comp_innerAut_inv [DecidableEq n] (U : unitaryGroup n 𝕜) :
    innerAut U ∘ₗ innerAut U⁻¹ = 1 := by
  rw [LinearMap.ext_iff]
  intro x
  rw [LinearMap.comp_apply, innerAut_coe, innerAut_inv_coe, StarAlgEquiv.apply_symm_apply]
  rfl


-- @@ L275-278 verbatim
theorem innerAut_apply_innerAut_inv [DecidableEq n] (U₁ U₂ : unitaryGroup n 𝕜)
    (x : Matrix n n 𝕜) :
    innerAut U₁ (innerAut U₂⁻¹ x) = innerAut (U₁ * U₂⁻¹) x := by
  rw [innerAut_apply_innerAut]


-- @@ L280-283 verbatim
theorem innerAut_apply_innerAut_inv_self [DecidableEq n] (U : unitaryGroup n 𝕜)
    (x : Matrix n n 𝕜) :
    innerAut U (innerAut U⁻¹ x) = x := by
  rw [innerAut_apply_innerAut_inv, mul_inv_cancel, innerAut_one, Module.End.one_apply]


-- @@ L285-289 verbatim
theorem innerAut_inv_apply_innerAut_self [DecidableEq n] (U : unitaryGroup n 𝕜)
    (x : Matrix n n 𝕜) :
    innerAut U⁻¹ (innerAut U x) = x := by
  rw [innerAut_inv_coe, innerAut_coe]
  exact StarAlgEquiv.symm_apply_apply _ _


-- @@ L291-293 verbatim
theorem innerAut_apply_zero [DecidableEq n] (U : unitaryGroup n 𝕜) :
    innerAut U 0 = 0 :=
  map_zero _


-- @@ L295-298 verbatim
theorem innerAut_conj_spectrum_eq [DecidableEq n] (U : unitaryGroup n 𝕜)
    (x : Matrix n n 𝕜 →ₗ[𝕜] Matrix n n 𝕜) :
    spectrum 𝕜 (innerAut U⁻¹ ∘ₗ x ∘ₗ innerAut U) = spectrum 𝕜 x := by
  rw [spectrum.comm, LinearMap.comp_assoc, innerAut_comp_innerAut_inv, LinearMap.comp_one]


-- @@ L300-302 verbatim
theorem innerAut_apply_one [DecidableEq n] (U : unitaryGroup n 𝕜) :
    innerAut U 1 = 1 := by
  rw [innerAut_coe, _root_.map_one]


-- @@ L304-306 verbatim
theorem innerAutStarAlg_apply_eq_innerAut_apply [DecidableEq n] (U : unitaryGroup n 𝕜)
    (x : Matrix n n 𝕜) : innerAutStarAlg U x = innerAut U x :=
  rfl


-- @@ L308-311 verbatim
theorem _root_.Matrix.innerAut.map_mul [DecidableEq n] (U : unitaryGroup n 𝕜)
    (x y : Matrix n n 𝕜) :
    innerAut U (x * y) = innerAut U x * innerAut U y := by
  rw [innerAut_coe, _root_.map_mul (innerAutStarAlg U)]


-- @@ L313-316 verbatim
theorem _root_.Matrix.innerAut.map_star [DecidableEq n] (U : unitaryGroup n 𝕜)
    (x : Matrix n n 𝕜) :
    star (innerAut U x) = innerAut U (star x) :=
  innerAut_conjTranspose _ _


-- @@ L318-320 verbatim
theorem innerAut_inv_eq_star [DecidableEq n] {x : unitaryGroup n 𝕜} :
    innerAut x⁻¹ = innerAut (star x) :=
  rfl


-- @@ L322-326 verbatim
theorem _root_.Matrix.unitaryGroup.coe_inv [DecidableEq n] (U : unitaryGroup n 𝕜) :
    ⇑(U⁻¹ : unitaryGroup n 𝕜) = ((U : Matrix n n 𝕜)⁻¹ : Matrix n n 𝕜) := by
  symm
  apply inv_eq_left_inv
  simp_rw [UnitaryGroup.inv_apply, UnitaryGroup.star_mul_self]


-- @@ L328-331 verbatim
theorem _root_.Matrix.innerAut.map_inv [DecidableEq n] (U : unitaryGroup n 𝕜)
    (x : Matrix n n 𝕜) :
    (innerAut U x)⁻¹ = innerAut U x⁻¹ := by
  simp_rw [innerAut_apply, Matrix.mul_inv_rev, ← unitaryGroup.coe_inv, inv_inv, Matrix.mul_assoc]


-- @@ L333-337 verbatim
/-- The trace of `U * x * U⁻¹` is the trace of `x`. -/
theorem innerAut_apply_trace_eq [DecidableEq n] (U : unitaryGroup n 𝕜)
    (x : Matrix n n 𝕜) :
    (innerAut U x).trace = x.trace := by
  rw [innerAut_coe, StarAlgEquiv.trace_preserving]


-- @@ L339-339 verbatim
variable [DecidableEq n]


-- @@ L341-346 verbatim
theorem exists_innerAut_iff_exists_innerAut_inv {P : Matrix n n 𝕜 → Prop}
    (x : Matrix n n 𝕜) :
    (∃ U : unitaryGroup n 𝕜, P (innerAut U x)) ↔
      ∃ U : unitaryGroup n 𝕜, P (innerAut U⁻¹ x) := by
  constructor <;> rintro ⟨U, hU⟩ <;> use U⁻¹
  simp_all


-- @@ L348-351 verbatim
theorem _root_.Matrix.innerAut.is_injective (U : unitaryGroup n 𝕜) :
    Function.Injective (innerAut U) := by
  intro u v huv
  rw [← innerAut_inv_apply_innerAut_self U u, huv, innerAut_inv_apply_innerAut_self]


-- @@ L353-357 verbatim
/-- A matrix is Hermitian iff its image under a unitary inner automorphism is Hermitian. -/
theorem innerAut_isHermitian_iff (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    x.IsHermitian ↔ (innerAut U x).IsHermitian := by
  simp_rw [IsHermitian, innerAut_conjTranspose,
    Function.Injective.eq_iff (innerAut.is_injective U)]


-- @@ L359-363 verbatim
theorem _root_.Matrix.unitaryGroup.injective_hMul (U : unitaryGroup n 𝕜) (x y : Matrix n n 𝕜) :
    x = y ↔ x * (U : Matrix n n 𝕜) = y * (U : Matrix n n 𝕜) := by
  refine ⟨fun h => by rw [h], fun h => ?_⟩
  have h' := congrArg (fun z : Matrix n n 𝕜 => z * (U⁻¹ : unitaryGroup n 𝕜)) h
  simpa [Matrix.mul_assoc, UnitaryGroup.inv_apply] using h'


-- @@ L365-367 verbatim
lemma unitaryGroup_conjTranspose (U : unitaryGroup n 𝕜) :
    (↑U)ᴴ = (↑(U⁻¹ : unitaryGroup n 𝕜) : Matrix n n 𝕜) :=
  rfl


-- @@ L369-369 verbatim
end


-- @@ L371-371 verbatim
section Positivity


-- @@ L373-373 verbatim
variable [RCLike 𝕜] [DecidableEq n]


-- @@ L375-375 verbatim
open scoped ComplexOrder MatrixOrder


-- @@ L377-391 verbatim
/-- A unitary inner automorphism preserves positive semidefinite matrices. -/
theorem _root_.Matrix.innerAut_posSemidef_iff (U : unitaryGroup n 𝕜) {a : Matrix n n 𝕜} :
    (innerAut U a).PosSemidef ↔ a.PosSemidef := by
  constructor
  · intro h
    rw [← Matrix.nonneg_iff_posSemidef] at h ⊢
    rcases CStarAlgebra.nonneg_iff_eq_star_mul_self.mp h with ⟨b, hb⟩
    rw [← innerAut_inv_apply_innerAut_self U a, hb, Matrix.innerAut.map_mul,
      ← Matrix.innerAut.map_star]
    exact CStarAlgebra.nonneg_iff_eq_star_mul_self.mpr ⟨innerAut U⁻¹ b, rfl⟩
  · intro h
    rw [← Matrix.nonneg_iff_posSemidef] at h ⊢
    rcases CStarAlgebra.nonneg_iff_eq_star_mul_self.mp h with ⟨b, hb⟩
    rw [hb, Matrix.innerAut.map_mul, ← Matrix.innerAut.map_star]
    exact CStarAlgebra.nonneg_iff_eq_star_mul_self.mpr ⟨innerAut U b, rfl⟩


-- @@ L393-396 verbatim
theorem _root_.Matrix.posSemidef_innerAut {a : Matrix n n 𝕜} (ha : a.PosSemidef)
    (U : unitaryGroup n 𝕜) :
    (innerAut U a).PosSemidef :=
  (innerAut_posSemidef_iff U).mpr ha


-- @@ L398-401 verbatim
theorem _root_.Matrix.PosSemidef.innerAut {a : Matrix n n 𝕜}
    (ha : a.PosSemidef) (U : unitaryGroup n 𝕜) :
    (innerAut U a).PosSemidef :=
  Matrix.posSemidef_innerAut ha U


-- @@ L403-405 verbatim
theorem _root_.Matrix.innerAut_isUnit_iff (U : unitaryGroup n 𝕜) {x : Matrix n n 𝕜} :
    IsUnit (innerAut U x) ↔ IsUnit x := by
  simpa [innerAut_coe] using (isUnit_map_iff (innerAutStarAlg U).toAlgEquiv.toMulEquiv x)


-- @@ L407-414 verbatim
/-- A unitary inner automorphism preserves positive definite matrices. -/
theorem _root_.Matrix.innerAut_posDef_iff (U : unitaryGroup n 𝕜) {x : Matrix n n 𝕜} :
    (innerAut U x).PosDef ↔ x.PosDef := by
  constructor <;> intro h
  · exact ((innerAut_posSemidef_iff U).mp h.posSemidef).posDef_iff_isUnit.mpr
      ((innerAut_isUnit_iff U).mp h.isUnit)
  · exact ((innerAut_posSemidef_iff U).mpr h.posSemidef).posDef_iff_isUnit.mpr
      ((innerAut_isUnit_iff U).mpr h.isUnit)


-- @@ L416-419 verbatim
theorem _root_.Matrix.posDef_innerAut {a : Matrix n n 𝕜} (ha : a.PosDef)
    (U : unitaryGroup n 𝕜) :
    (innerAut U a).PosDef :=
  (innerAut_posDef_iff U).mpr ha


-- @@ L421-424 verbatim
theorem _root_.Matrix.PosDef.innerAut {a : Matrix n n 𝕜}
    (ha : a.PosDef) (U : unitaryGroup n 𝕜) :
    (innerAut U a).PosDef :=
  Matrix.posDef_innerAut ha U


-- @@ L426-426 verbatim
open scoped BigOperators


-- @@ L428-526 verbatim
/-- Every star-algebra equivalence of `Mₙ` is implemented by a unitary conjugation. -/
theorem _root_.StarAlgEquiv.of_matrix_is_inner
    (f : Matrix n n 𝕜 ≃⋆ₐ[𝕜] Matrix n n 𝕜) :
    ∃ U : unitaryGroup n 𝕜, innerAutStarAlg U = f := by
  by_cases h : IsEmpty n
  · have := h
    use 1
    ext a
    have : a = 0 := by simp only [eq_iff_true_of_subsingleton]
    simp_rw [this, map_zero]
  rw [not_isEmpty_iff] at h
  have := h
  let f' := f.toAlgEquiv
  obtain ⟨y', hy⟩ := aut_mat_inner f'
  let y := LinearMap.toMatrix' (y'.toLinearMap)
  let yinv := LinearMap.toMatrix' y'.symm.toLinearMap
  have Hy : y * yinv = 1 ∧ yinv * y = 1 := by
    simp_rw [y, yinv, ← LinearMap.toMatrix'_comp,
      LinearEquiv.comp_coe, LinearEquiv.symm_trans_self, LinearEquiv.self_trans_symm,
      LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id, and_self_iff]
  have H : y⁻¹ = yinv := inv_eq_left_inv Hy.2
  have hf' : ∀ x : Matrix n n 𝕜, f' x = y * x * y⁻¹ := by
    intro x
    simp_rw [hy, Algebra.autInner_apply, H]
    rfl
  have hf : ∀ x : Matrix n n 𝕜, f x = y * x * y⁻¹ := by
    intro x
    rw [← hf']
    rfl
  have hstar : ∀ x : Matrix n n 𝕜, (f x)ᴴ = f xᴴ :=
    fun _ => (map_star f _).symm
  simp_rw [hf, conjTranspose_mul, conjTranspose_nonsing_inv] at hstar
  have hcomm_aux : ∀ x : Matrix n n 𝕜, yᴴ * y * xᴴ * y⁻¹ = xᴴ * yᴴ := by
    intro x
    simp_rw [Matrix.mul_assoc, ← Matrix.mul_assoc y, ← hstar, ← Matrix.mul_assoc, ←
      conjTranspose_nonsing_inv, ← conjTranspose_mul, H, Hy.2, Matrix.mul_one]
  have hcomm_star : ∀ x : Matrix n n 𝕜, Commute xᴴ (yᴴ * y) := by
    intro x
    simp_rw [Commute, SemiconjBy, ← Matrix.mul_assoc, ← hcomm_aux, Matrix.mul_assoc, H,
      Hy.2, Matrix.mul_one]
  have hcomm : ∀ x : Matrix n n 𝕜, Commute x (yᴴ * y) := by
    intro x
    specialize hcomm_star xᴴ
    simp_all
  obtain ⟨α, hα⟩ := commutes_with_all_iff.mp hcomm
  have hpos_semidef : (yᴴ * y).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self y
  have hy_unit : IsUnit y := ⟨⟨y, yinv, Hy.1, Hy.2⟩, rfl⟩
  have hunit_yhy : IsUnit (yᴴ * y) := by
    simpa [star_eq_conjTranspose] using (isUnit_star.mpr hy_unit).mul hy_unit
  have hpos_def := hpos_semidef.posDef_iff_isUnit.mpr hunit_yhy
  have hα_re : α = RCLike.re α := by
    have hdiag := IsHermitian.coe_re_diag hpos_semidef.1
    simp_rw [hα, diag_smul, diag_one, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one] at hdiag
    have hone_ne_zero : (1 : n → 𝕜) ≠ 0 := by
      simp_all
    have hsmul : (RCLike.re α : 𝕜) • (1 : n → 𝕜) = α • 1 := by
      rw [← hdiag]
      ext1
      simp only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    rw [(smul_left_injective _ hone_ne_zero).eq_iff] at hsmul
    rw [hsmul]
  have hdiag_pos : (diagonal fun _ : n => α).PosDef := by
    rwa [← Matrix.smul_one_eq_diagonal α, ← hα]
  have hpositive : 0 < RCLike.re α := by
    have hαpos : 0 < α := (Matrix.posDef_diagonal_iff.mp hdiag_pos) h.some
    rw [hα_re, RCLike.ofReal_pos] at hαpos
    exact hαpos
  have hunitary :
      (((RCLike.re α : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : 𝕜) • y ∈ unitaryGroup n 𝕜 := by
    rw [mem_unitaryGroup_iff', star_eq_conjTranspose]
    simp_rw [conjTranspose_smul, RCLike.star_def, Matrix.smul_mul, Matrix.mul_smul,
      RCLike.conj_ofReal, smul_smul, ← RCLike.ofReal_mul]
    rw [← Real.rpow_add hpositive, hα, hα_re, smul_smul, ← RCLike.ofReal_mul,
      RCLike.ofReal_re, ← Real.rpow_add_one (NeZero.of_pos hpositive).out]
    norm_num
  let U : unitaryGroup n 𝕜 := ⟨_, hunitary⟩
  have hU : (U : Matrix n n 𝕜) =
      (((RCLike.re α : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : 𝕜) • y := rfl
  have hU_inv :
      ((((RCLike.re α : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : 𝕜) • y)⁻¹ =
        ((U⁻¹ : _) : Matrix n n 𝕜) := by
    apply inv_eq_left_inv
    rw [← hU, UnitaryGroup.inv_apply, UnitaryGroup.star_mul_self]
  have hscalar_inv :
      ((((RCLike.re α : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : 𝕜) • y)⁻¹ =
        (((RCLike.re α : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : 𝕜)⁻¹ • y⁻¹ := by
    apply inv_eq_left_inv
    simp_rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [inv_mul_cancel₀, one_smul, H, Hy.2]
    · simp_rw [ne_eq, RCLike.ofReal_eq_zero, Real.rpow_eq_zero_iff_of_nonneg (le_of_lt hpositive),
        (NeZero.of_pos hpositive).out, false_and]
      exact not_false
  use U
  ext1 x
  simp_rw [innerAutStarAlg_apply_eq_innerAut_apply, innerAut_apply, ← hU_inv, hscalar_inv, hf,
    hU, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← RCLike.ofReal_inv, ←
    RCLike.ofReal_mul, ← Real.rpow_neg_one, ← Real.rpow_mul (le_of_lt hpositive),
    ← Real.rpow_add hpositive]
  norm_num


-- @@ L528-532 verbatim
/-- A unitary matrix implementing a star-algebra equivalence of full matrix algebras. -/
noncomputable def _root_.StarAlgEquiv.ofMatrixUnitary
    (f : Matrix n n 𝕜 ≃⋆ₐ[𝕜] Matrix n n 𝕜) : unitaryGroup n 𝕜 := by
  choose U _ using f.of_matrix_is_inner
  exact U


-- @@ L534-539 verbatim
lemma _root_.StarAlgEquiv.eq_innerAut
    (f : Matrix n n 𝕜 ≃⋆ₐ[𝕜] Matrix n n 𝕜) :
    innerAutStarAlg f.ofMatrixUnitary = f := by
  rw [StarAlgEquiv.ofMatrixUnitary]
  generalize_proofs
  simp_all


-- @@ L541-545 verbatim
/-- Spectral theorem in Monlib's inner-automorphism notation. -/
theorem _root_.Matrix.IsHermitian.spectral_theorem'' {x : Matrix n n 𝕜}
    (hx : x.IsHermitian) :
    x = innerAut hx.eigenvectorUnitary (diagonal (RCLike.ofReal ∘ hx.eigenvalues)) := by
  simpa [innerAut, innerAutStarAlg] using hx.spectral_theorem


-- @@ L547-570 verbatim
theorem _root_.Matrix.diagonal.spectrum {𝕜 n : Type _} [Field 𝕜] [Fintype n]
    [DecidableEq n] (A : n → 𝕜) :
    spectrum 𝕜 (toLin' (diagonal A : Matrix n n 𝕜)) = {x : 𝕜 | ∃ i : n, A i = x} := by
  simp_rw [Set.ext_iff, ← Module.End.hasEigenvalue_iff_mem_spectrum, ←
    Module.End.has_eigenvector_iff_hasEigenvalue, toLin'_apply, funext_iff, mulVec,
    diagonal_dotProduct, Pi.smul_apply, smul_eq_mul, mul_eq_mul_right_iff, ne_eq,
    Set.mem_ofPred_eq, funext_iff, Pi.zero_apply, Classical.not_forall]
  intro x
  constructor
  · rintro ⟨v, ⟨h, ⟨j, hj⟩⟩⟩
    specialize h j
    rcases h with (h | h)
    · exact ⟨j, h⟩
    · contradiction
  · rintro ⟨i, hi⟩
    let v : n → 𝕜 := fun j => if j = i then 1 else 0
    use v
    simp_rw [v, ite_eq_right_iff, one_ne_zero, imp_false, Classical.not_not]
    constructor
    · intro j
      by_cases h : j = i
      · simp_all
      · simp_all
    · use i


-- @@ L572-577 verbatim
theorem _root_.Matrix.IsHermitian.spectrum {x : Matrix n n 𝕜}
    (hx : x.IsHermitian) :
    spectrum 𝕜 (toLin' x) = {x : 𝕜 | ∃ i : n, (hx.eigenvalues i : 𝕜) = x} := by
  nth_rw 1 [Matrix.IsHermitian.spectral_theorem'' hx]
  simp_rw [innerAut.spectrum_eq, diagonal.spectrum]
  rfl


-- @@ L579-582 verbatim
theorem _root_.Matrix.IsHermitian.hasEigenvalue_iff {x : Matrix n n 𝕜}
    (hx : x.IsHermitian) (α : 𝕜) :
    Module.End.HasEigenvalue (toLin' x) α ↔ ∃ i, (hx.eigenvalues i : 𝕜) = α := by
  rw [Module.End.hasEigenvalue_iff_mem_spectrum, hx.spectrum, Set.mem_ofPred]


-- @@ L584-592 verbatim
theorem _root_.Matrix.IsAlmostHermitian.schur_decomp {A : Matrix n n 𝕜}
    (hA : A.IsAlmostHermitian) :
    ∃ (D : n → 𝕜) (U : unitaryGroup n 𝕜), innerAut U (diagonal D) = A := by
  rcases hA with ⟨α, B, ⟨rfl, hB⟩⟩
  use α • RCLike.ofReal ∘ hB.eigenvalues, hB.eigenvectorUnitary
  simp_rw [diagonal_smul, _root_.map_smul, innerAut_apply, UnitaryGroup.inv_apply]
  change α • innerAut hB.eigenvectorUnitary
      (diagonal (RCLike.ofReal ∘ hB.eigenvalues)) = α • B
  rw [← Matrix.IsHermitian.spectral_theorem'' hB]


-- @@ L594-597 verbatim
lemma _root_.toEuclideanLin_one :
    Matrix.toEuclideanLin (1 : Matrix n n 𝕜) = 1 := by
  simp_rw [Matrix.toLpLin_eq_toLin, Matrix.toLin_one]
  rfl


-- @@ L599-599 verbatim
end Positivity


-- @@ L601-601 verbatim
variable [Field 𝕜] [StarRing 𝕜] [DecidableEq n]


-- @@ L603-608 verbatim
theorem _root_.Matrix.coe_diagonal_eq_diagonal_coe {n 𝕜 : Type _} [RCLike 𝕜]
    [DecidableEq n] (x : n → ℝ) :
    (diagonal (RCLike.ofReal ∘ x) : Matrix n n 𝕜) = CoeTC.coe ∘ diagonal x := by
  ext i j
  change (if i = j then (x i : 𝕜) else 0) = ((if i = j then x i else 0 : ℝ) : 𝕜)
  by_cases h : i = j <;> simp [h]


-- @@ L610-612 verbatim
theorem _root_.Matrix.innerAutStarAlg_equiv_toLinearMap (U : unitaryGroup n 𝕜) :
    (innerAutStarAlg U).toAlgEquiv.toLinearMap = innerAut U :=
  rfl


-- @@ L614-618 verbatim
theorem _root_.Matrix.innerAutStarAlg_equiv_symm_toLinearMap (U : unitaryGroup n 𝕜) :
    (innerAutStarAlg U).symm.toAlgEquiv.toLinearMap = innerAut U⁻¹ := by
  ext1
  simp only [innerAut_apply, inv_inv]
  simp_all


-- @@ L620-627 verbatim
theorem _root_.Matrix.innerAut_commutes_with_map_lid_symm (U : Matrix.unitaryGroup n 𝕜) :
    TensorProduct.map 1 (innerAut U) ∘ₗ
        (TensorProduct.lid 𝕜 (Matrix n n 𝕜)).symm.toLinearMap =
      (TensorProduct.lid 𝕜 (Matrix n n 𝕜)).symm.toLinearMap ∘ₗ innerAut U := by
  simp_rw [LinearMap.ext_iff, LinearMap.comp_apply,
    LinearEquiv.coe_coe, TensorProduct.lid_symm_apply, TensorProduct.map_tmul,
    Module.End.one_apply]
  simp_all


-- @@ L629-638 verbatim
theorem _root_.Matrix.innerAut_commutes_with_lid_comm (U : Matrix.unitaryGroup n 𝕜) :
    (TensorProduct.lid 𝕜 (Matrix n n 𝕜)).toLinearMap ∘ₗ
        (TensorProduct.comm 𝕜 (Matrix n n 𝕜) 𝕜).toLinearMap ∘ₗ
          TensorProduct.map (innerAut U) 1 =
      innerAut U ∘ₗ
        (TensorProduct.lid 𝕜 (Matrix n n 𝕜)).toLinearMap ∘ₗ
          (TensorProduct.comm 𝕜 (Matrix n n 𝕜) 𝕜).toLinearMap := by
  simp_rw [TensorProduct.ext_iff', LinearMap.comp_apply, TensorProduct.map_apply,
    LinearEquiv.coe_coe, TensorProduct.comm_tmul, TensorProduct.lid_tmul,
    Module.End.one_apply, _root_.map_smul, forall₂_true_iff]


-- @@ L640-643 verbatim
theorem _root_.Matrix.innerAut_comp_inj (U : Matrix.unitaryGroup n 𝕜)
    (S T : Matrix n n 𝕜 →ₗ[𝕜] Matrix n n 𝕜) :
    S = T ↔ innerAut U ∘ₗ S = innerAut U ∘ₗ T := by
  simp_all


-- @@ L645-648 verbatim
theorem _root_.Matrix.innerAut_inj_comp (U : unitaryGroup n 𝕜)
    (S T : Matrix n n 𝕜 →ₗ[𝕜] Matrix n n 𝕜) :
    S = T ↔ S ∘ₗ innerAut U = T ∘ₗ innerAut U := by
  simp_all


-- @@ L650-653 verbatim
theorem _root_.Matrix.innerAut.comp_inj (U : Matrix.unitaryGroup n 𝕜)
    (S T : Matrix n n 𝕜 →ₗ[𝕜] Matrix n n 𝕜) :
    S = T ↔ innerAut U ∘ₗ S = innerAut U ∘ₗ T :=
  Matrix.innerAut_comp_inj U S T


-- @@ L655-658 verbatim
theorem _root_.Matrix.innerAut.inj_comp (U : unitaryGroup n 𝕜)
    (S T : Matrix n n 𝕜 →ₗ[𝕜] Matrix n n 𝕜) :
    S = T ↔ S ∘ₗ innerAut U = T ∘ₗ innerAut U :=
  Matrix.innerAut_inj_comp U S T


-- @@ L660-660 verbatim
section ConjKronecker


-- @@ L662-662 verbatim
variable {n p 𝕜 : Type _} [RCLike 𝕜]


-- @@ L664-674 verbatim
theorem _root_.Matrix.unitaryGroup.conj_mem [Fintype n] [DecidableEq n]
    (U : unitaryGroup n 𝕜) :
    (U : Matrix n n 𝕜)ᴴᵀ ∈ unitaryGroup n 𝕜 := by
  rw [Matrix.mem_unitaryGroup_iff]
  calc (U : Matrix n n 𝕜)ᴴᵀ * star ((U : Matrix n n 𝕜)ᴴᵀ)
      = ((U : Matrix n n 𝕜) * star (U : Matrix n n 𝕜))ᴴᵀ := by
        rw [Matrix.conj_mul]
        rfl
    _ = 1 := by
        rw [U.2.2]
        simp [Matrix.conj_one]


-- @@ L676-680 verbatim
/-- Entrywise conjugate of a unitary matrix as a unitary. -/
def _root_.Matrix.unitaryGroup.conj [Fintype n] [DecidableEq n]
    (U : unitaryGroup n 𝕜) :
    unitaryGroup n 𝕜 :=
  ⟨(U : Matrix n n 𝕜)ᴴᵀ, Matrix.unitaryGroup.conj_mem U⟩


-- @@ L682-686 verbatim
@[norm_cast]
theorem _root_.Matrix.unitaryGroup.conj_coe [Fintype n] [DecidableEq n]
    (U : unitaryGroup n 𝕜) :
    (unitaryGroup.conj U : Matrix n n 𝕜) = (U : Matrix n n 𝕜)ᴴᵀ :=
  rfl


-- @@ L688-692 verbatim
theorem _root_.Matrix.innerAut.conj [Fintype n] [DecidableEq n]
    (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    (innerAut U x)ᴴᵀ = innerAut (unitaryGroup.conj U) xᴴᵀ := by
  simp_rw [innerAut_apply, Matrix.conj_mul, UnitaryGroup.inv_apply, unitaryGroup.conj_coe]
  rfl


-- @@ L694-697 verbatim
theorem _root_.Matrix.UnitaryGroup.mul_star_self [Fintype n] [DecidableEq n]
    (U : unitaryGroup n 𝕜) :
    (U : Matrix n n 𝕜) * star (U : Matrix n n 𝕜) = 1 :=
  Matrix.mem_unitaryGroup_iff.mp (SetLike.coe_mem U)


-- @@ L699-699 verbatim
open scoped Kronecker


-- @@ L701-706 verbatim
theorem _root_.Matrix.kronecker_mem_unitaryGroup [Fintype n] [DecidableEq n]
    [Fintype p] [DecidableEq p] (U₁ : unitaryGroup n 𝕜) (U₂ : unitaryGroup p 𝕜) :
    (U₁ : Matrix n n 𝕜) ⊗ₖ (U₂ : Matrix p p 𝕜) ∈ unitaryGroup (n × p) 𝕜 := by
  simp_rw [mem_unitaryGroup_iff, star_eq_conjTranspose, kronecker_conjTranspose, ←
    mul_kronecker_mul, ← star_eq_conjTranspose, Matrix.UnitaryGroup.mul_star_self,
    one_kronecker_one]


-- @@ L708-712 verbatim
/-- The Kronecker product of two unitary matrices as a unitary matrix. -/
def _root_.Matrix.unitaryGroup.kronecker [Fintype n] [DecidableEq n]
    [Fintype p] [DecidableEq p] (U₁ : unitaryGroup n 𝕜) (U₂ : unitaryGroup p 𝕜) :
    unitaryGroup (n × p) 𝕜 :=
  ⟨(U₁ : Matrix n n 𝕜) ⊗ₖ (U₂ : Matrix p p 𝕜), kronecker_mem_unitaryGroup U₁ U₂⟩


-- @@ L714-718 verbatim
theorem _root_.Matrix.unitaryGroup.kronecker_coe [Fintype n] [DecidableEq n]
    [Fintype p] [DecidableEq p] (U₁ : unitaryGroup n 𝕜) (U₂ : unitaryGroup p 𝕜) :
    (unitaryGroup.kronecker U₁ U₂ : Matrix (n × p) (n × p) 𝕜) =
      (U₁ : Matrix n n 𝕜) ⊗ₖ (U₂ : Matrix p p 𝕜) :=
  rfl


-- @@ L720-725 verbatim
theorem _root_.Matrix.innerAut_kronecker [Fintype n] [DecidableEq n]
    [Fintype p] [DecidableEq p] (U₁ : unitaryGroup n 𝕜) (U₂ : unitaryGroup p 𝕜)
    (x : Matrix n n 𝕜) (y : Matrix p p 𝕜) :
    innerAut U₁ x ⊗ₖ innerAut U₂ y = innerAut (unitaryGroup.kronecker U₁ U₂) (x ⊗ₖ y) := by
  simp_rw [innerAut_apply, UnitaryGroup.inv_apply, unitaryGroup.kronecker_coe,
    star_eq_conjTranspose, kronecker_conjTranspose, ← mul_kronecker_mul]


-- @@ L727-727 verbatim
end ConjKronecker


-- @@ L729-729 verbatim
end Matrix
