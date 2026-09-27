/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic
public import LeanPool.Monlib4.LinearAlgebra.LmulRmul
public meta import Mathlib.Tactic.Basic
public meta import Mathlib.Tactic.ToAdditive
import LeanPool.Monlib4.LinearAlgebra.End
import LeanPool.Monlib4.LinearAlgebra.TensorProduct.BasicLemmas
import LeanPool.Monlib4.Preq.Finset


-- @@ L16-21 verbatim
/-!
# (A-A)-Bimodules

We define (A-A)-bimodules, where A is a commutative semiring, and show basic
properties of them.
-/


-- @@ L23-23 verbatim
@[expose] public section



-- @@ L26-27 verbatim
variable {R H₁ H₂ : Type _} [CommSemiring R] [Semiring H₁] [Semiring H₂] [Algebra R H₁]
  [Algebra R H₂]


-- @@ L29-29 verbatim
open scoped TensorProduct


-- @@ L31-31 verbatim
local notation x " ⊗ₘ " y => TensorProduct.map x y


-- @@ L33-35 expanded
/-- Left multiplication on the left tensor factor. -/
noncomputable def Bimodule.lsmul (x : H₁) (y : H₁ ⊗[R] H₂) : H₁ ⊗[R] H₂ :=
  (TensorProduct.map (LinearMap.mulLeft R x) 1) y


-- @@ L37-39 expanded
/-- Right multiplication on the right tensor factor. -/
noncomputable def Bimodule.rsmul (x : H₁ ⊗[R] H₂) (y : H₂) : H₁ ⊗[R] H₂ :=
  (TensorProduct.map 1 (LinearMap.mulRight R y)) x


-- @@ L41-42 verbatim
/-- Scoped notation for left multiplication on the left tensor factor. -/
scoped[Bimodule] infixl:72 " •ₗ " => Bimodule.lsmul


-- @@ L44-45 verbatim
/-- Scoped notation for right multiplication on the right tensor factor. -/
scoped[Bimodule] infixl:72 " •ᵣ " => Bimodule.rsmul


-- @@ L47-47 verbatim
open scoped Bimodule BigOperators


-- @@ L49-50 expanded
theorem Bimodule.lsmul_apply (x a : H₁) (b : H₂) : Bimodule.lsmul x (a ⊗ₜ b) = (x * a) ⊗ₜ[R] b :=
  rfl


-- @@ L52-53 expanded
theorem Bimodule.rsmul_apply (a : H₁) (x b : H₂) : Bimodule.rsmul (a ⊗ₜ b) x = a ⊗ₜ[R] (b * x) :=
  rfl


-- @@ L55-58 expanded
theorem Bimodule.lsmul_rsmul_assoc (x : H₁) (y : H₂) (a : H₁ ⊗[R] H₂) :
    Bimodule.rsmul (Bimodule.lsmul x a) y = Bimodule.lsmul x (Bimodule.rsmul a y) := by
  simp_rw [Bimodule.lsmul, Bimodule.rsmul, ← LinearMap.comp_apply, ← TensorProduct.map_comp,
    LinearMap.one_comp, LinearMap.comp_one]


-- @@ L60-61 expanded
theorem Bimodule.lsmul_zero (x : H₁) : Bimodule.lsmul x (0 : H₁ ⊗[R] H₂) = 0 :=
  rfl


-- @@ L63-65 expanded
theorem Bimodule.zero_lsmul (x : H₁ ⊗[R] H₂) : Bimodule.lsmul 0 x = 0 := by
  rw [Bimodule.lsmul, LinearMap.mulLeft_zero_eq_zero, TensorProduct.map_zero_left,
    LinearMap.zero_apply]


-- @@ L67-68 expanded
theorem Bimodule.zero_rsmul (x : H₂) : Bimodule.rsmul (0 : H₁ ⊗[R] H₂) x = 0 :=
  rfl


-- @@ L70-72 expanded
theorem Bimodule.rsmul_zero (x : H₁ ⊗[R] H₂) : Bimodule.rsmul x 0 = 0 := by
  rw [Bimodule.rsmul, LinearMap.mulRight_zero_eq_zero, TensorProduct.map_zero_right,
    LinearMap.zero_apply]


-- @@ L74-75 expanded
theorem Bimodule.lsmul_add (x : H₁) (a b : H₁ ⊗[R] H₂) :
    Bimodule.lsmul x (a + b) = Bimodule.lsmul x a + Bimodule.lsmul x b :=
  map_add _ _ _


-- @@ L77-78 expanded
theorem Bimodule.add_rsmul (x : H₂) (a b : H₁ ⊗[R] H₂) :
    Bimodule.rsmul (a + b) x = Bimodule.rsmul a x + Bimodule.rsmul b x :=
  map_add _ _ _


-- @@ L80-82 expanded
theorem Bimodule.lsmul_sum (x : H₁) {k : Type _} {s : Finset k} (a : k → H₁ ⊗[R] H₂) :
    Bimodule.lsmul x (∑ i ∈ s, a i) = ∑ i ∈ s, Bimodule.lsmul x (a i) :=
  map_sum _ _ _


-- @@ L84-86 expanded
theorem Bimodule.sum_rsmul (x : H₂) {k : Type _} {s : Finset k} (a : k → H₁ ⊗[R] H₂) :
    Bimodule.rsmul (∑ i ∈ s, a i) x = ∑ i ∈ s, Bimodule.rsmul (a i) x :=
  map_sum _ _ _


-- @@ L88-90 expanded
theorem Bimodule.one_lsmul (x : H₁ ⊗[R] H₂) : Bimodule.lsmul 1 x = x := by
  rw [Bimodule.lsmul, LinearMap.mulLeft_one, ← Module.End.one_eq_id, TensorProduct.map_one,
    Module.End.one_apply]


-- @@ L92-94 expanded
theorem Bimodule.rsmul_one (x : H₁ ⊗[R] H₂) : Bimodule.rsmul x 1 = x := by
  rw [Bimodule.rsmul, LinearMap.mulRight_one, ← Module.End.one_eq_id, TensorProduct.map_one,
    Module.End.one_apply]


-- @@ L96-97 expanded
theorem Bimodule.lsmul_one (x : H₁) : Bimodule.lsmul x (1 : H₁ ⊗[R] H₂) = x ⊗ₜ 1 := by
  rw [Algebra.TensorProduct.one_def, Bimodule.lsmul_apply, mul_one]


-- @@ L99-100 expanded
theorem Bimodule.one_rsmul (x : H₂) : Bimodule.rsmul (1 : H₁ ⊗[R] H₂) x = 1 ⊗ₜ x := by
  rw [Algebra.TensorProduct.one_def, Bimodule.rsmul_apply, one_mul]


-- @@ L102-103 expanded
theorem Bimodule.lsmul_smul (α : R) (x : H₁) (a : H₁ ⊗[R] H₂) :
    Bimodule.lsmul x (α • a) = α • (Bimodule.lsmul x a) := by
  simp_rw [Bimodule.lsmul, _root_.map_smul]


-- @@ L105-106 expanded
theorem Bimodule.smul_rsmul (α : R) (x : H₂) (a : H₁ ⊗[R] H₂) :
    Bimodule.rsmul (α • a) x = α • (Bimodule.rsmul a x) := by
  simp_rw [Bimodule.rsmul, _root_.map_smul]


-- @@ L108-111 expanded
theorem Bimodule.lsmul_lsmul (x y : H₁) (a : H₁ ⊗[R] H₂) :
    Bimodule.lsmul x (Bimodule.lsmul y a) = Bimodule.lsmul (x * y) a :=
  by
  simp_rw [Bimodule.lsmul, ← LinearMap.comp_apply, ← TensorProduct.map_comp, ←
    LinearMap.mulLeft_mul]
  rfl


-- @@ L113-116 expanded
theorem Bimodule.rsmul_rsmul (x y : H₂) (a : H₁ ⊗[R] H₂) :
    Bimodule.rsmul (Bimodule.rsmul a x) y = Bimodule.rsmul a (x * y) :=
  by
  simp_rw [Bimodule.rsmul, ← LinearMap.comp_apply, ← TensorProduct.map_comp, ←
    LinearMap.mulRight_mul]
  rfl


-- @@ L118-118 verbatim
local notation "l(" x "," y ")" => y →ₗ[x] y


-- @@ L120-122 expanded
/-- A linear map commuting with the left and right tensor-factor actions. -/
def LinearMap.IsBimoduleMap (P : H₁ ⊗[R] H₂ →ₗ[R] H₁ ⊗[R] H₂) : Prop :=
  ∀ (x : H₁) (y : H₂) (a : H₁ ⊗[R] H₂),
    P (Bimodule.rsmul (Bimodule.lsmul x a) y) = Bimodule.rsmul (Bimodule.lsmul x (P a)) y


-- @@ L124-127 expanded
theorem LinearMap.IsBimoduleMap.lsmul {P : H₁ ⊗[R] H₂ →ₗ[R] H₁ ⊗[R] H₂} (hP : P.IsBimoduleMap)
    (x : H₁) (a : H₁ ⊗[R] H₂) : P (Bimodule.lsmul x a) = Bimodule.lsmul x (P a) :=
  by
  nth_rw 1 [← Bimodule.rsmul_one a]
  rw [← Bimodule.lsmul_rsmul_assoc, hP, Bimodule.rsmul_one]


-- @@ L129-132 expanded
theorem LinearMap.IsBimoduleMap.rsmul {P : H₁ ⊗[R] H₂ →ₗ[R] H₁ ⊗[R] H₂} (hP : P.IsBimoduleMap)
    (x : H₂) (a : H₁ ⊗[R] H₂) : P (Bimodule.rsmul a x) = Bimodule.rsmul (P a) x :=
  by
  nth_rw 1 [← Bimodule.one_lsmul a]
  rw [hP, Bimodule.one_lsmul]


-- @@ L134-138 expanded
theorem LinearMap.IsBimoduleMap.add {P Q : H₁ ⊗[R] H₂ →ₗ[R] H₁ ⊗[R] H₂} (hP : P.IsBimoduleMap)
    (hQ : Q.IsBimoduleMap) : (P + Q).IsBimoduleMap :=
  by
  simp_rw [LinearMap.IsBimoduleMap, LinearMap.add_apply, Bimodule.lsmul_add, Bimodule.add_rsmul]
  intro x y a
  rw [hP, hQ]


-- @@ L140-142 expanded
theorem LinearMap.isBimoduleMap.zero : (0 : H₁ ⊗[R] H₂ →ₗ[R] H₁ ⊗[R] H₂).IsBimoduleMap :=
  by
  intro x y a
  simp_rw [LinearMap.zero_apply, Bimodule.lsmul_zero, Bimodule.zero_rsmul]


-- @@ L144-148 expanded
theorem LinearMap.IsBimoduleMap.smul {x : H₁ ⊗[R] H₂ →ₗ[R] H₁ ⊗[R] H₂} (hx : x.IsBimoduleMap)
    (k : R) : (k • x).IsBimoduleMap := by
  intro x y a
  simp only [LinearMap.smul_apply, Bimodule.lsmul_smul, Bimodule.smul_rsmul]
  rw [hx]


-- @@ L150-155 expanded
theorem LinearMap.IsBimoduleMap.nsmul {x : H₁ ⊗[R] H₂ →ₗ[R] H₁ ⊗[R] H₂} (hx : x.IsBimoduleMap)
    (k : ℕ) : (k • x).IsBimoduleMap := by
  intro x y a
  simp only [LinearMap.smul_apply, ← Nat.cast_smul_eq_nsmul R k, Bimodule.lsmul_smul,
    Bimodule.smul_rsmul]
  rw [hx]


-- @@ L157-166 expanded
/-- The submodule of bimodule endomorphisms of a tensor product. -/
noncomputable def LinearMap.IsBimoduleMaps (R H₁ H₂ : Type _) [CommSemiring R] [Semiring H₁]
    [Semiring H₂] [Algebra R H₁] [Algebra R H₂] : Submodule R (H₁ ⊗[R] H₂ →ₗ[R] H₁ ⊗[R] H₂)
    where
  carrier x := x.IsBimoduleMap
  add_mem' x y := x.add y
  zero_mem' := LinearMap.isBimoduleMap.zero
  smul_mem' r _ x := x.smul r


-- @@ L170-171 verbatim
@[simp] lemma LinearMap.IsBimoduleMaps.coe_add (x y : IsBimoduleMaps R H₁ H₂) :
   ((x + y : IsBimoduleMaps R H₁ H₂) : H₁ ⊗[R] H₂ →ₗ[R] H₁ ⊗[R] H₂) = ↑x + ↑y := rfl

-- @@ L172-174 verbatim
@[simp] lemma LinearMap.IsBimoduleMaps.coe_smul (x : IsBimoduleMaps R H₁ H₂)
  (r : R) :
   ((r • x : IsBimoduleMaps R H₁ H₂) : H₁ ⊗[R] H₂ →ₗ[R] H₁ ⊗[R] H₂) = r • ↑x := rfl

-- @@ L175-177 verbatim
@[simp] lemma LinearMap.IsBimoduleMaps.coe_nsmul (x : IsBimoduleMaps R H₁ H₂)
  (r : ℕ) :
   ((r • x : IsBimoduleMaps R H₁ H₂) : H₁ ⊗[R] H₂ →ₗ[R] H₁ ⊗[R] H₂) = r • ↑x := rfl

-- @@ L178-179 verbatim
@[simp] lemma LinearMap.IsBimoduleMaps.coe_zero :
   ((0 : IsBimoduleMaps R H₁ H₂) : H₁ ⊗[R] H₂ →ₗ[R] H₁ ⊗[R] H₂) = 0 := rfl



-- @@ L182-186 verbatim
theorem LinearMap.IsBimoduleMap.add_smul (a b : R) (x : (IsBimoduleMaps R H₁ H₂)) :
    (a + b) • x = a • x + b • x := by
  rw [← Subtype.coe_inj]
  simp_rw [IsBimoduleMaps.coe_smul, IsBimoduleMaps.coe_add, _root_.add_smul]
  rfl






-- @@ L192-197 expanded
theorem LinearMap.isBimoduleMap_iff {T : H₁ ⊗[R] H₂ →ₗ[R] H₁ ⊗[R] H₂} :
    T.IsBimoduleMap ↔
      ∀ a b x y, T ((a * x) ⊗ₜ[R] (y * b)) = Bimodule.rsmul (Bimodule.lsmul a (T (x ⊗ₜ[R] y))) b :=
  ⟨fun h a b x y => by rw [← h]; rfl, fun h a b x =>
    x.inductionOn (fun _ _ => h _ _ _ _)
      (fun _ _ hc hd => by simp only [map_add, Bimodule.lsmul_add, Bimodule.add_rsmul, hc, hd])⟩


-- @@ L199-228 expanded
theorem LinearMap.isBimoduleMap_iff_ltensor_lsmul_rtensor_rsmul {R H₁ H₂ : Type _} [Field R]
    [Ring H₁] [Ring H₂] [Algebra R H₁] [Algebra R H₂] {x : H₁ →ₗ[R] H₁} {y : H₂ →ₗ[R] H₂} :
    (TensorProduct.map x y).IsBimoduleMap ↔
      (TensorProduct.map x y) = 0 ∨
        x = LinearMap.mulRight R (x 1) ∧ y = LinearMap.mulLeft R (y 1) :=
  by
  rw [← left_module_map_iff, ← right_module_map_iff]
  by_cases h : (TensorProduct.map x y) = 0
  · simp_rw [h, true_or, iff_true, LinearMap.isBimoduleMap.zero]
  simp_rw [isBimoduleMap_iff, TensorProduct.map_tmul, Bimodule.lsmul_apply, Bimodule.rsmul_apply, h,
    false_or]
  have hy : y ≠ 0 := by
    intro hy
    simp_all
  have hx : x ≠ 0 := by
    intro hx
    simp_all
  simp_rw [ne_eq, LinearMap.ext_iff, LinearMap.zero_apply, Classical.not_forall] at hx hy
  refine ⟨fun hxy => ?_, fun hxy a b c d => by rw [hxy.1, hxy.2]⟩
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  have H : ∀ x_4 x_2 x_1 x_3, x (x_1 * x_3) ⊗ₜ y (x_4 * x_2) = (x_1 * x x_3) ⊗ₜ (y x_4 * x_2) :=
    fun x_4 x_2 x_1 x_3 => hxy x_1 x_2 x_3 x_4
  rw [Forall.rotate] at hxy
  specialize hxy a 1
  specialize H b 1
  simp_rw [mul_one, one_mul, ← @sub_eq_zero _ _ _ (_ ⊗ₜ[R] (_ * _) : H₁ ⊗[R] H₂), ←
    @sub_eq_zero _ _ _ ((_ * _) ⊗ₜ[R] _), ← TensorProduct.sub_tmul, ← TensorProduct.tmul_sub,
    TensorProduct.tmul_eq_zero, sub_eq_zero, ha, hb, false_or, or_false] at H hxy
  exact ⟨H, fun _ _ => hxy _ _⟩


-- @@ L231-234 verbatim
theorem LinearMap.IsBimoduleMap.sum_coe {p : Type _} {s : Finset p}
  (x : p → (IsBimoduleMaps R H₁ H₂)) :
  (∑ i ∈ s, x i : IsBimoduleMaps R H₁ H₂).1 = ∑ i ∈ s, (x i).1 :=
Submodule.coe_sum _ _ _


-- @@ L236-244 expanded
theorem rmulMapLmul_apply_apply (x : H₁ ⊗[R] H₂) (a : H₁) (b : H₂) :
    rmulMapLmul x (a ⊗ₜ b) = Bimodule.rsmul (Bimodule.lsmul a x) b :=
  x.inductionOn
    (fun α β =>
      by
      simp_rw [rmulMapLmul_apply, TensorProduct.map_tmul, rmul_apply, lmul_apply]
      rfl)
    (fun α β hα hβ => by
      simp_rw [map_add, LinearMap.add_apply]
      rw [hα, hβ, Bimodule.lsmul_add, Bimodule.add_rsmul])


-- @@ L246-257 expanded
theorem LinearMap.isBimoduleMap_iff' {f : H₁ ⊗[R] H₂ →ₗ[R] H₁ ⊗[R] H₂} :
    f.IsBimoduleMap ↔ rmulMapLmul (f 1) = f :=
  by
  constructor
  · intro h
    apply TensorProduct.ext'
    intro x y
    rw [rmulMapLmul_apply_apply, ← h, Bimodule.lsmul_one, Bimodule.rsmul_apply, one_mul]
  · intro h
    rw [isBimoduleMap_iff]
    intro a b c d
    rw [← h, rmulMapLmul_apply_apply, rmulMapLmul_apply_apply, ← Bimodule.lsmul_lsmul, ←
      Bimodule.rsmul_rsmul, Bimodule.lsmul_rsmul_assoc]


-- @@ L259-263 verbatim
@[simp]
theorem rmulMapLmul_apply_one (x : H₁ ⊗[R] H₂) :
  rmulMapLmul x 1 = x := by
  rw [show (1 : H₁ ⊗[R] H₂) = 1 ⊗ₜ[R] 1 from rfl, rmulMapLmul_apply_apply,
    Bimodule.one_lsmul, Bimodule.rsmul_one]


-- @@ L265-268 expanded
@[simp]
theorem LinearMap.mem_isBimoduleMaps_iff {x : H₁ ⊗[R] H₂ →ₗ[R] H₁ ⊗[R] H₂} :
    x ∈ LinearMap.IsBimoduleMaps R H₁ H₂ ↔ x.IsBimoduleMap := by rfl


-- @@ L270-273 verbatim
theorem rmulMapLmul_mem_isBimoduleMaps (x : H₁ ⊗[R] H₂) :
  rmulMapLmul x ∈ LinearMap.IsBimoduleMaps R H₁ H₂ := by
  simp_rw [LinearMap.mem_isBimoduleMaps_iff, LinearMap.isBimoduleMap_iff',
    rmulMapLmul_apply_one]


-- @@ L275-289 expanded
/-- The tensor product is linearly equivalent to its bimodule endomorphism submodule. -/
@[simps]
noncomputable def TensorProduct.toIsBimoduleMap {R : Type*} {H₁ H₂ : Type*} [CommSemiring R]
    [Semiring H₁] [Semiring H₂] [Algebra R H₁] [Algebra R H₂] :
    (H₁ ⊗[R] H₂) ≃ₗ[R] LinearMap.IsBimoduleMaps R H₁ H₂
    where
  toFun x := ⟨rmulMapLmul x, rmulMapLmul_mem_isBimoduleMaps _⟩
  invFun x := (x : H₁ ⊗[R] H₂ →ₗ[R] H₁ ⊗[R] H₂) 1
  map_add' _ _ := by simp only [_root_.map_add]; rfl
  map_smul' _ _ := by simp only [map_smulₛₗ]; rfl
  left_inv _ := by simp only [rmulMapLmul_apply_one]
  right_inv
    f := by
    simp only
    congr
    rw [LinearMap.isBimoduleMap_iff'.mp f.property]

