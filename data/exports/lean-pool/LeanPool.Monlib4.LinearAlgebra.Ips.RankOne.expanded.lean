/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import LeanPool.Monlib4.LinearAlgebra.IsProjPrime
import LeanPool.Monlib4.LinearAlgebra.Ips.Basic


-- @@ L12-19 verbatim
/-!

# rank one operators

This defines the rank one operator $| x \rangle\langle y |$ for continuous linear maps
  (see `rank_one`) and linear maps (see `rank_one_lm`).

-/


-- @@ L21-21 verbatim
@[expose] public section



-- @@ L24-24 verbatim
section rankOne


-- @@ L26-31 verbatim
/-- The bra map sending a vector to the corresponding inner-product functional. -/
@[simps!]
noncomputable abbrev bra (𝕜 : Type*) {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] :
    E →L⋆[𝕜] (E →L[𝕜] 𝕜) :=
innerSL 𝕜

-- @@ L32-47 verbatim
/-- The ket map sending a vector to scalar multiplication by that vector. -/
@[simps!]
noncomputable def ket (𝕜 : Type*) {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] :
    E →L[𝕜] (𝕜 →L[𝕜] E) where
  toFun x :=
  { toFun := fun α => α • x
    map_add' := fun _ _ => by simp only [add_smul]
    map_smul' := fun _ _ => by simp only [smul_smul, smul_eq_mul]; rfl }
  map_add' := fun _ _ => by simp only [smul_add]; rfl
  map_smul' := fun α _ => by simp_rw [smul_smul, mul_comm _ α, ← smul_smul]; rfl
  cont := by
    refine continuous_clm_apply.mpr ?_
    intro
    simp only [ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
    exact continuous_const_smul _

-- @@ L48-53 verbatim
@[simp high]
lemma ket_one_apply
  {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  (x : E) :
  ket 𝕜 x 1 = x :=
by simp only [ket_apply_apply, one_smul]


-- @@ L55-58 verbatim
theorem ket_RCLike {𝕜 : Type*} [RCLike 𝕜] (x : 𝕜) :
  ket 𝕜 x = ContinuousLinearMap.mul 𝕜 𝕜 x := by
  ext
  simp only [ket_one_apply, ContinuousLinearMap.mul_apply', mul_one]


-- @@ L60-64 verbatim
lemma ContinuousLinearMap.mul_one_apply {𝕜 𝕜' : Type*}
  [NontriviallyNormedField 𝕜] [SeminormedRing 𝕜']
  [NormedSpace 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' 𝕜'] [SMulCommClass 𝕜 𝕜' 𝕜'] :
  mul 𝕜 𝕜' 1 = 1 :=
by ext; rw [mul_apply', one_mul]; rfl


-- @@ L66-68 verbatim
theorem ket_RCLike_one {𝕜 : Type*} [RCLike 𝕜] :
  ket 𝕜 (1 : 𝕜) = 1 :=
by rw [ket_RCLike, ContinuousLinearMap.mul_one_apply]


-- @@ L70-73 verbatim
theorem bra_RCLike {𝕜 : Type*} [RCLike 𝕜] (x : 𝕜) :
  bra 𝕜 x = ContinuousLinearMap.mul 𝕜 𝕜 ((starRingEnd 𝕜) x) := by
  ext
  simp_all


-- @@ L75-77 verbatim
theorem bra_RCLike_one {𝕜 : Type*} [RCLike 𝕜] :
  bra 𝕜 (1 : 𝕜) = 1 :=
by rw [bra_RCLike, map_one, ContinuousLinearMap.mul_one_apply]


-- @@ L79-86 verbatim
lemma bra_adjoint_eq_ket {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] (x : E) :
  ContinuousLinearMap.adjoint (bra 𝕜 x : E →L[𝕜] 𝕜) = (ket 𝕜 x) := by
  ext
  apply ext_inner_left 𝕜
  intro y
  simp only [ket_apply_apply, one_smul, ContinuousLinearMap.adjoint_inner_right,
    bra_apply_apply, RCLike.inner_apply, inner_conj_symm, one_mul]


-- @@ L88-91 verbatim
lemma _root_.ket_adjoint_eq_bra {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] (x : E) :
  ContinuousLinearMap.adjoint (ket 𝕜 x) = bra 𝕜 x := by
  rw [← bra_adjoint_eq_ket, ContinuousLinearMap.adjoint_adjoint]


-- @@ L93-93 verbatim
open scoped InnerProductSpace


-- @@ L95-99 verbatim
lemma bra_ket_apply {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (x y : E) :
  (bra 𝕜 x) ∘L (ket 𝕜 y) = ket 𝕜 ⟪x, y⟫_𝕜 := by
  ext
  simp_all


-- @@ L101-104 verbatim
lemma bra_ket_one_eq_inner {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (x y : E) :
  ((bra 𝕜 x) ∘L (ket 𝕜 y)) 1 = ⟪x, y⟫_𝕜 := by
  rw [bra_ket_apply, ket_one_apply]


-- @@ L106-112 verbatim
lemma continuousLinearMap_comp_ket {𝕜 E₁ E₂ : Type*} [RCLike 𝕜] [NormedAddCommGroup E₁]
  [InnerProductSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
  (f : E₁ →L[𝕜] E₂) (x : E₁) :
  f ∘L ket 𝕜 x = ket 𝕜 (f x) := by
  ext
  simp only [ContinuousLinearMap.comp_apply, ket_one_apply]


-- @@ L114-122 verbatim
lemma bra_comp_continuousLinearMap {𝕜 E₁ E₂ : Type*} [RCLike 𝕜] [NormedAddCommGroup E₁]
  [InnerProductSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
  [CompleteSpace E₁] [CompleteSpace E₂]
  (x : E₂) (f : E₁ →L[𝕜] E₂) :
  bra 𝕜 x ∘L f = bra 𝕜 (ContinuousLinearMap.adjoint f x) := by
  ext
  simp only [ContinuousLinearMap.comp_apply, bra_apply_apply,
    ContinuousLinearMap.adjoint_inner_left]


-- @@ L124-142 verbatim
/-- we define the rank one operator $| x \rangle\langle y |$ by
  $x \mapsto \langle y,z\rangle x$ -/
@[simps]
def rankOne (𝕜 : Type*) {E₁ E₂ : Type*} [RCLike 𝕜] [NormedAddCommGroup E₁]
  [InnerProductSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] :
    E₁ →ₗ[𝕜] (E₂ →ₗ⋆[𝕜] (E₂ →L[𝕜] E₁)) where
  toFun x :=
  { toFun := fun y =>
    { toFun := fun z => ⟪y,z⟫_𝕜 • x
      map_add' := fun _ _ => by simp_rw [inner_add_right, add_smul]
      map_smul' := fun _ _ => by simp_rw [inner_smul_right, RingHom.id_apply, smul_smul]
      cont := Continuous.smul (Continuous.inner continuous_const continuous_id') continuous_const }
    map_add' := fun a b => by simp only [inner_add_left, add_smul]; rfl
    map_smul' := fun r x => by simp only [inner_smul_left, ← smul_smul]; rfl }
  map_add' a b := by simp only [smul_add]; rfl
  map_smul' r a := by
    simp only [smul_smul, RingHom.id_apply, mul_comm _ r]
    simp only [← smul_smul]; rfl


-- @@ L144-145 verbatim
variable {𝕜 E₁ E₂ : Type*} [RCLike 𝕜] [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]


-- @@ L147-149 verbatim
@[simp]
theorem rankOne_apply {x : E₁} {y : E₂} (z : E₂) : rankOne 𝕜 x y z = ⟪y,z⟫_𝕜 • x :=
rfl


-- @@ L151-153 verbatim
theorem ket_bra_eq_rankOne {x : E₁} {y : E₂} :
  ket 𝕜 x ∘L bra 𝕜 y = rankOne 𝕜 x y :=
rfl


-- @@ L155-158 verbatim
theorem ket_eq_rankOne_one (x : E₁) :
  ket 𝕜 x = rankOne 𝕜 x 1 := by
  ext
  simp_all

-- @@ L159-162 verbatim
theorem bra_eq_one_rankOne (x : E₁) :
  bra 𝕜 x = rankOne 𝕜 1 x := by
  ext
  simp only [innerSL_apply_apply, rankOne_apply_apply_apply, smul_eq_mul, mul_one]



-- @@ L165-165 verbatim
open ContinuousLinearMap


-- @@ L167-169 verbatim
theorem rankOne.smul_real_apply {x : E₁} {y : E₂} {α : ℝ} :
    rankOne 𝕜 x ((α : 𝕜) • y) = (α : 𝕜) • rankOne 𝕜 x y := by
  simp only [LinearMap.map_smulₛₗ, RCLike.conj_ofReal]


-- @@ L171-181 verbatim
/--
$| x \rangle\langle y | | z \rangle\langle w | =
\langle y, z \rangle \cdot  | x \rangle\langle w |$
-/
@[simp]
theorem rankOne.apply_rankOne {E₃ : Type*} [NormedAddCommGroup E₃] [InnerProductSpace 𝕜 E₃]
  (x : E₁) (y z : E₂) (w : E₃) :
    (rankOne 𝕜 x y) ∘L rankOne 𝕜 z w = ⟪y,z⟫_𝕜 • rankOne 𝕜 x w := by
  ext r
  simp_rw [smul_apply, comp_apply, rankOne_apply,
    inner_smul_right, mul_comm, smul_smul]


-- @@ L183-189 verbatim
/-- $u \circ | x \rangle\langle y | = | u(x) \rangle\langle y |$ -/
theorem ContinuousLinearMap.comp_rankOne {E₃ : Type*} [NormedAddCommGroup E₃]
  [InnerProductSpace 𝕜 E₃]
  (x : E₁) (y : E₂) (u : E₁ →L[𝕜] E₃) :
    u ∘L rankOne 𝕜 x y = rankOne 𝕜 (u x) y := by
  ext r
  simp_rw [comp_apply, rankOne_apply, map_smul]


-- @@ L191-197 verbatim
/-- $| x \rangle\langle y | \circ u  = | x \rangle\langle u^*(y) |$ -/
theorem ContinuousLinearMap.rankOne_comp {E₃ : Type*} [NormedAddCommGroup E₃]
  [InnerProductSpace 𝕜 E₃]
  [CompleteSpace E₂] [CompleteSpace E₃] (x : E₁) (y : E₂) (u : E₃ →L[𝕜] E₂) :
    rankOne 𝕜 x y ∘L u = rankOne 𝕜 x (adjoint u y) := by
  ext r
  simp_rw [comp_apply, rankOne_apply, adjoint_inner_left]


-- @@ L199-204 verbatim
/-- rank one operators given by norm one vectors are automatically idempotent -/
theorem rankOne_self_isIdempotentElem_of_normOne {x : E₁} (h : ‖x‖ = 1) :
  IsIdempotentElem (rankOne 𝕜 x x) := by
  simp_rw [IsIdempotentElem, ContinuousLinearMap.ext_iff, mul_def, rankOne.apply_rankOne,
    inner_self_eq_norm_sq_to_K, h, RCLike.ofReal_one, one_pow, one_smul,
    forall_const]


-- @@ L206-209 verbatim
theorem rankOne_self_isSymmetric {x : E₁} :
  LinearMap.IsSymmetric ((rankOne 𝕜 x x) : E₁ →ₗ[𝕜] E₁) := by
  simp_rw [LinearMap.IsSymmetric, ContinuousLinearMap.coe_coe, rankOne_apply, inner_smul_left,
    inner_smul_right, inner_conj_symm, mul_comm, forall₂_true_iff]


-- @@ L211-215 verbatim
/-- rank one operators are automatically self-adjoint -/
@[simp]
theorem rankOne_self_isSelfAdjoint [CompleteSpace E₁] {x : E₁} :
  IsSelfAdjoint (rankOne 𝕜 x x) :=
isSelfAdjoint_iff_isSymmetric.mpr rankOne_self_isSymmetric


-- @@ L217-221 verbatim
/-- $| x \rangle\langle y |^* = | y \rangle\langle x |$ -/
theorem rankOne_adjoint [CompleteSpace E₁] [CompleteSpace E₂] (x : E₁) (y : E₂) :
  adjoint (rankOne 𝕜 x y) = rankOne 𝕜 y x := by
  rw [← ket_bra_eq_rankOne, adjoint_comp, bra_adjoint_eq_ket, ket_adjoint_eq_bra]
  rfl


-- @@ L223-225 verbatim
theorem rankOne_inner_left (x w : E₁) (y z : E₂) :
  ⟪rankOne 𝕜 x y z,w⟫_𝕜 = ⟪z,y⟫_𝕜 * ⟪x,w⟫_𝕜 := by
  rw [rankOne_apply, inner_smul_left, inner_conj_symm]


-- @@ L227-229 verbatim
theorem rankOne_inner_right (x y : E₁) (z w : E₂) :
  ⟪x, rankOne 𝕜 y z w⟫_𝕜 = ⟪z,w⟫_𝕜 * ⟪x,y⟫_𝕜 := by
  rw [rankOne_apply, inner_smul_right]


-- @@ L231-253 verbatim
theorem ContinuousLinearMap.commutes_with_all_iff [CompleteSpace E₁] {T : E₁ →L[𝕜] E₁} :
    (∀ S, Commute S T) ↔ ∃ α : 𝕜, T = α • 1 := by
  constructor
  · intro h
    have h' : ∀ x y : E₁, rankOne 𝕜 x y ∘L T = T ∘L rankOne 𝕜 x y := fun x y => h _
    simp_rw [ContinuousLinearMap.rankOne_comp, ContinuousLinearMap.comp_rankOne] at h'
    have h'' : ∀ x y : E₁, rankOne 𝕜 (adjoint T y) x = rankOne 𝕜 y (T x) := by
      intro x y
      nth_rw 1 [← rankOne_adjoint]
      rw [h', rankOne_adjoint]
    simp_rw [ContinuousLinearMap.ext_iff, rankOne_apply] at h' h''
    by_cases H : ∀ x : E₁, x = 0
    · use 0
      simp_rw [ContinuousLinearMap.ext_iff]
      simp_all
    push Not at H
    obtain ⟨x, hx⟩ := H
    use (⟪x,x⟫_𝕜)⁻¹ * ⟪adjoint T x, x⟫_𝕜
    simp_rw [ContinuousLinearMap.ext_iff, smul_apply,
      one_apply_eq_self, mul_smul, h', smul_smul]
    simp_all
  · rintro ⟨α, hα⟩ S
    simp_rw [Commute, SemiconjBy, mul_def, hα, comp_smul, smul_comp, one_def, comp_id, id_comp]


-- @@ L255-258 verbatim
theorem ContinuousLinearMap.centralizer [CompleteSpace E₁] :
    (@Set.univ (E₁ →L[𝕜] E₁)).centralizer = { x : E₁ →L[𝕜] E₁ | ∃ α : 𝕜, x = α • 1 } := by
  simp_rw [Set.centralizer, Set.mem_univ, true_imp_iff, ← ContinuousLinearMap.commutes_with_all_iff]
  rfl


-- @@ L260-263 verbatim
theorem ContinuousLinearMap.scalar_centralizer :
    {x : E₁ →L[𝕜] E₁ | ∃ α : 𝕜, x = α • 1}.centralizer = @Set.univ (E₁ →L[𝕜] E₁) := by
  simp_rw [Set.centralizer, Set.ext_iff, Set.mem_ofPred, Set.mem_univ, iff_true]
  simp_all


-- @@ L265-267 verbatim
theorem ContinuousLinearMap.centralizer_centralizer [CompleteSpace E₁] :
    (@Set.univ (E₁ →L[𝕜] E₁)).centralizer.centralizer = Set.univ := by
  rw [ContinuousLinearMap.centralizer, ContinuousLinearMap.scalar_centralizer]


-- @@ L269-291 verbatim
theorem colinear_of_rankOne_self_eq_rankOne_self
  (x y : E₁) (h : rankOne 𝕜 x x = rankOne 𝕜 y y) :
      ∃ α : 𝕜ˣ, x = (α : 𝕜) • y := by
  have : x = 0 ↔ y = 0 := by
    constructor <;> intro hh <;>
      simp only [hh, ContinuousLinearMap.ext_iff, map_zero, zero_apply,
        @eq_comm _ (0 : E₁ →L[𝕜] E₁), rankOne_apply, smul_eq_zero] at h
    on_goal 1 => specialize h y
    on_goal 2 => specialize h x
    all_goals
      simp_rw [inner_self_eq_zero, or_self_iff] at h
      exact h
  simp_rw [ContinuousLinearMap.ext_iff, rankOne_apply] at h
  by_cases Hx : x = 0
  · simp_all
  · have ugh : inner 𝕜 y x ≠ 0 := by
      intro hy
      specialize h x
      simp_all
    use Units.mk0 (inner 𝕜 y x / inner 𝕜 x x)
        (div_ne_zero ugh ((@inner_self_ne_zero 𝕜 _ _ _ _ _).mpr Hx))
    simp_rw [div_eq_inv_mul, Units.val_mk0, mul_smul, ← h, smul_smul,
      inv_mul_cancel₀ ((@inner_self_ne_zero 𝕜 _ _ _ _ _).mpr Hx), one_smul]


-- @@ L293-296 verbatim
theorem rankOne.ext_iff {x y : E₁} (_hx : x ≠ 0) (_hy : y ≠ 0)
    (h : rankOne 𝕜 x x = rankOne 𝕜 y y) :
    ∃ α : 𝕜ˣ, x = (α : 𝕜) • y :=
  colinear_of_rankOne_self_eq_rankOne_self x y h


-- @@ L298-332 verbatim
theorem colinear_of_ne_zero_rankOne_eq_rankOne [CompleteSpace E₂] [CompleteSpace E₁]
  {a c : E₁} {b d : E₂} (h : rankOne 𝕜 a b = rankOne 𝕜 c d)
  (ha : a ≠ 0) (hb : b ≠ 0) :
    (∃ α β : 𝕜ˣ, a = (α : 𝕜) • c ∧ b = (α * β : 𝕜) • d) := by
  have h₂ := h
  apply_fun ContinuousLinearMap.adjoint at h₂
  simp only [rankOne_adjoint, ContinuousLinearMap.ext_iff, rankOne_apply] at h h₂
  specialize h b
  specialize h₂ a
  have h₃ : a = (⟪d, b⟫_𝕜 / ⟪b, b⟫_𝕜) • c := by
    calc a = (⟪b, b⟫_𝕜 / ⟪b, b⟫_𝕜) • a := by
          simp_all
      _ = (1 / ⟪b, b⟫_𝕜) • (⟪b, b⟫_𝕜 • a) := by simp only [smul_smul]; ring_nf
      _ = (1 / ⟪b, b⟫_𝕜) • (⟪d, b⟫_𝕜 • c) := by rw [h]
      _ = (⟪d, b⟫_𝕜 / ⟪b, b⟫_𝕜) • c := by simp only [smul_smul]; ring_nf
  have h₄ :=
  calc b = (⟪a, a⟫_𝕜 / ⟪a, a⟫_𝕜) • b := by
          simp_all
      _ = (1 / ⟪a, a⟫_𝕜) • (⟪a, a⟫_𝕜 • b) := by simp only [smul_smul]; ring_nf
      _ = (1 / ⟪a, a⟫_𝕜) • (⟪c, a⟫_𝕜 • d) := by rw [h₂]
      _ = (1 / ⟪a, a⟫_𝕜) • (⟪c, (⟪d, b⟫_𝕜 / ⟪b, b⟫_𝕜) • c⟫_𝕜 • d) := by rw [h₃]
      _ = ((⟪d, b⟫_𝕜 / ⟪b, b⟫_𝕜) * (⟪c, c⟫_𝕜 / (⟪a, a⟫_𝕜))) • d := by
        simp only [inner_smul_right, smul_smul]; ring_nf
  have h₅ : ⟪d, b⟫_𝕜 ≠ 0 := by
    intro h
    rw [h, zero_div, zero_mul, zero_smul] at h₄
    exact hb h₄
  let α := Units.mk0 (⟪d, b⟫_𝕜 / ⟪b, b⟫_𝕜) (div_ne_zero h₅ (inner_self_ne_zero.mpr hb))
  have h₆ : c ≠ 0 := by
    rintro rfl
    simp only [smul_zero] at h₃
    exact ha h₃
  let β := Units.mk0 (⟪c, c⟫_𝕜 / ⟪a, a⟫_𝕜)
    (div_ne_zero (inner_self_ne_zero.mpr h₆) (inner_self_ne_zero.mpr ha))
  exact ⟨α, β, h₃, h₄⟩


-- @@ L334-342 verbatim
theorem ket_eq_ket_iff {x y : E₁} :
  ket 𝕜 x = ket 𝕜 y ↔ x = y := by
  simp only [ContinuousLinearMap.ext_iff, ket_apply_apply,
    ← @sub_eq_zero _ _ (_ • _), ← @sub_eq_zero _ _ x]
  simp only [← smul_sub, smul_eq_zero, forall_or_right,
    or_iff_right_iff_imp]
  intro h
  specialize h 1
  simp only [one_ne_zero] at h


-- @@ L344-346 verbatim
theorem bra_eq_bra_iff {x y : E₁} :
  bra 𝕜 x = bra 𝕜 y ↔ x = y := by
  simp_all


-- @@ L348-352 verbatim
theorem ContinuousLinearMap.ext_inner_map {F : Type _} [NormedAddCommGroup F]
  [InnerProductSpace 𝕜 F] (T S : E₁ →L[𝕜] F) :
      T = S ↔ ∀ x y, ⟪T x,y⟫_𝕜 = ⟪S x,y⟫_𝕜 := by
  simp only [ContinuousLinearMap.ext_iff]
  exact ⟨fun h x _ => by rw [h], fun h x => ext_inner_right 𝕜 (h x)⟩

-- @@ L353-357 verbatim
theorem LinearMap.ext_inner_map {F : Type _} [NormedAddCommGroup F]
  [InnerProductSpace 𝕜 F] (T S : E₁ →ₗ[𝕜] F) :
      T = S ↔ ∀ x y, ⟪T x,y⟫_𝕜 = ⟪S x,y⟫_𝕜 := by
  simp only [LinearMap.ext_iff]
  exact ⟨fun h x _ => by rw [h], fun h x => ext_inner_right 𝕜 (h x)⟩


-- @@ L359-359 verbatim
open scoped BigOperators


-- @@ L361-388 verbatim
theorem ContinuousLinearMap.exists_sum_rankOne
  [FiniteDimensional 𝕜 E₁] [FiniteDimensional 𝕜 E₂] (T : E₁ →L[𝕜] E₂) :
    ∃ (x : Fin (Module.finrank 𝕜 E₁) × Fin (Module.finrank 𝕜 E₂) → E₂)
      (y : Fin (Module.finrank 𝕜 E₁) × Fin (Module.finrank 𝕜 E₂) → E₁),
      T = ∑ i, rankOne 𝕜 (x i) (y i) := by
  let := FiniteDimensional.complete 𝕜 E₁
  let := FiniteDimensional.complete 𝕜 E₂
  let e₁ := stdOrthonormalBasis 𝕜 E₁
  let e₂ := stdOrthonormalBasis 𝕜 E₂
  let b : Fin (Module.finrank 𝕜 E₁) × Fin (Module.finrank 𝕜 E₂) → E₁ := fun ij =>
    e₁ ij.1
  let a : Fin (Module.finrank 𝕜 E₁) × Fin (Module.finrank 𝕜 E₂) → E₂ := fun ij =>
    e₂.repr (T (e₁ ij.1)) ij.2 • e₂ ij.2
  refine ⟨a, b, ?_⟩
  simp only [a, b]
  simp only [ContinuousLinearMap.ext_inner_map, sum_apply, sum_inner, rankOne_inner_left,
    inner_smul_left, OrthonormalBasis.repr_apply_apply, inner_conj_symm]
  intro u v
  symm
  calc
    ∑ x : Fin (Module.finrank 𝕜 E₁) × Fin (Module.finrank 𝕜 E₂),
          ⟪u,e₁ x.fst⟫_𝕜 * (⟪T (e₁ x.fst),e₂ x.snd⟫_𝕜 * ⟪e₂ x.snd,v⟫_𝕜) =
        ∑ x_1, ∑ x_2,
          ⟪u,e₁ x_1⟫_𝕜 * (⟪T (e₁ x_1),e₂ x_2⟫_𝕜 * ⟪e₂ x_2,v⟫_𝕜) :=
      by simp_rw [← Finset.sum_product', Finset.univ_product_univ]
    _ = ∑ x_1, ⟪u,e₁ x_1⟫_𝕜 * ⟪T (e₁ x_1),v⟫_𝕜 := by
      simp_rw [← Finset.mul_sum, OrthonormalBasis.sum_inner_mul_inner]
    _ = ⟪T u,v⟫_𝕜 := by simp_rw [← adjoint_inner_right T, OrthonormalBasis.sum_inner_mul_inner]


-- @@ L390-393 verbatim
example [FiniteDimensional 𝕜 E₁] (T : E₁ →L[𝕜] E₁) :
    ∃ x y : Fin (Module.finrank 𝕜 E₁) × Fin (Module.finrank 𝕜 E₁) → E₁,
      T = ∑ i, rankOne 𝕜 (x i) (y i) :=
ContinuousLinearMap.exists_sum_rankOne T


-- @@ L395-402 verbatim
theorem LinearMap.exists_sum_rankOne [FiniteDimensional 𝕜 E₁] [FiniteDimensional 𝕜 E₂]
    (T : E₁ →ₗ[𝕜] E₂) :
    ∃ (x : Fin (Module.finrank 𝕜 E₁) × Fin (Module.finrank 𝕜 E₂) → E₂)
      (y : Fin (Module.finrank 𝕜 E₁) × Fin (Module.finrank 𝕜 E₂) → E₁),
      T = ∑ i, ↑(rankOne 𝕜 (x i) (y i)) := by
  obtain ⟨a, b, h⟩ := ContinuousLinearMap.exists_sum_rankOne (toContinuousLinearMap T)
  refine ⟨a, b, ?_⟩
  simpa using congrArg ContinuousLinearMap.toLinearMap h


-- @@ L404-412 verbatim
theorem rankOne.sum_orthonormalBasis_eq_id {𝕜 E : Type _} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {ι : Type _} [Fintype ι] (b : OrthonormalBasis ι 𝕜 E) :
    ∑ i, rankOne 𝕜 (b i) (b i) = 1 := by
  rw [ContinuousLinearMap.ext_iff]
  intros
  apply @ext_inner_left 𝕜 _
  intro v
  simp_rw [sum_apply, rankOne_apply, ← OrthonormalBasis.repr_apply_apply,
    OrthonormalBasis.sum_repr, one_apply_eq_self]


-- @@ L414-414 verbatim
end rankOne


-- @@ L416-416 verbatim
section rankOneLm



-- @@ L419-423 verbatim
/-- Same as `rankOne`, but as a linear map. -/
abbrev rankOneLm {𝕜 E₁ E₂ : Type*} [RCLike 𝕜] [NormedAddCommGroup E₁]
    [InnerProductSpace 𝕜 E₁] [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
    (x : E₁) (y : E₂) : E₂ →ₗ[𝕜] E₁ :=
  (rankOne 𝕜 x y).toLinearMap


-- @@ L425-426 verbatim
variable {𝕜 E₁ E₂ : Type _} [RCLike 𝕜] [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]

-- @@ L427-427 verbatim
variable {E : Type _} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]


-- @@ L429-431 verbatim
theorem rankOneLm_eq_rankOne (x : E₁) (y : E₂) :
    rankOneLm (𝕜 := 𝕜) x y = (rankOne 𝕜 x y).toLinearMap :=
  rfl


-- @@ L433-435 verbatim
theorem rankOne_eq_rankOneLm (x : E₁) (y : E₂) :
    (rankOne 𝕜 x y : E₂ →ₗ[𝕜] E₁) = rankOneLm (𝕜 := 𝕜) x y :=
  rfl


-- @@ L437-439 verbatim
theorem rankOneLm_apply (x : E₁) (y z : E₂) :
    rankOneLm (𝕜 := 𝕜) x y z = inner 𝕜 y z • x :=
  rankOne_apply (𝕜 := 𝕜) (x := x) (y := y) (z := z)


-- @@ L441-444 verbatim
theorem rankOneLm_smul (x : E₁) (y : E₂) (r : 𝕜) :
    rankOneLm (𝕜 := 𝕜) (r • x) y = r • rankOneLm (𝕜 := 𝕜) x y := by
  ext z
  simp [rankOneLm_apply, smul_smul, mul_comm]


-- @@ L446-449 verbatim
theorem smul_rankOneLm (x : E₁) (y : E₂) (r : 𝕜) :
    rankOneLm (𝕜 := 𝕜) x (star r • y) = r • rankOneLm (𝕜 := 𝕜) x y := by
  ext z
  simp [rankOneLm_apply, smul_smul, inner_smul_left]


-- @@ L451-453 verbatim
theorem smul_rankOneLm' (x : E₁) (y : E₂) (r : 𝕜) :
    rankOneLm (𝕜 := 𝕜) x (r • y) = star r • rankOneLm (𝕜 := 𝕜) x y := by
  simpa using smul_rankOneLm (𝕜 := 𝕜) x y (star r)


-- @@ L455-461 verbatim
theorem rankOneLm_comp_rankOneLm (x : E₁) (y z : E₂) (w : E) :
  rankOneLm (𝕜 := 𝕜) x y ∘ₗ rankOneLm (𝕜 := 𝕜) z w =
      inner 𝕜 y z • rankOneLm (𝕜 := 𝕜) x w := by
  ext v
  rw [LinearMap.comp_apply, rankOneLm_apply, rankOneLm_apply, LinearMap.smul_apply,
    rankOneLm_apply, inner_smul_right, mul_smul, smul_smul]
  rw [smul_smul, mul_comm]


-- @@ L463-463 verbatim
open scoped BigOperators



-- @@ L466-475 verbatim
theorem ContinuousLinearMap.ext_of_rankOne {𝕜 H₁ H₂ H' : Type _} [RCLike 𝕜]
    [NormedAddCommGroup H'] [Module 𝕜 H']
    [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
    [FiniteDimensional 𝕜 H₁] [FiniteDimensional 𝕜 H₂]
    {x y : (H₁ →L[𝕜] H₂) →L[𝕜] H'}
    (h : ∀ a b, x (rankOne 𝕜 a b) = y (rankOne 𝕜 a b)) : x = y := by
  ext a
  obtain ⟨α, β, rfl⟩ := ContinuousLinearMap.exists_sum_rankOne a
  simp_rw [map_sum, h]


-- @@ L477-485 verbatim
theorem LinearMap.ext_of_rankOne {𝕜 H₁ H₂ H' : Type _} [RCLike 𝕜] [AddCommMonoid H'] [Module 𝕜 H']
    [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
    [FiniteDimensional 𝕜 H₁] [FiniteDimensional 𝕜 H₂]
    {x y : (H₁ →L[𝕜] H₂) →ₗ[𝕜] H'}
    (h : ∀ a b, x (rankOne 𝕜 a b) = y (rankOne 𝕜 a b)) : x = y := by
  ext a
  obtain ⟨α, β, rfl⟩ := ContinuousLinearMap.exists_sum_rankOne a
  simp_rw [map_sum, h]


-- @@ L487-497 verbatim
theorem AddMonoidHom.ext_of_rank_one' {𝕜 H₁ H₂ H' : Type _} [RCLike 𝕜]
    [AddCommMonoid H']
    [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
    [FiniteDimensional 𝕜 H₁] [FiniteDimensional 𝕜 H₂]
    {x y : (H₁ →ₗ[𝕜] H₂) →+ H'}
    (h : ∀ a b, x (rankOne 𝕜 a b).toLinearMap = y (rankOne 𝕜 a b).toLinearMap) :
    x = y := by
  ext a
  obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne a
  simp_rw [map_sum, h]


-- @@ L499-507 verbatim
theorem LinearMap.ext_of_rank_one' {𝕜 H₁ H₂ H' : Type _} [RCLike 𝕜] [AddCommMonoid H'] [Module 𝕜 H']
    [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
    [FiniteDimensional 𝕜 H₁] [FiniteDimensional 𝕜 H₂]
    {x y : (H₁ →ₗ[𝕜] H₂) →ₗ[𝕜] H'}
    (h : ∀ a b, x (rankOne 𝕜 a b).toLinearMap = y (rankOne 𝕜 a b).toLinearMap) : x = y := by
  ext a
  obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne a
  simp_rw [map_sum, h]


-- @@ L509-509 verbatim
open scoped BigOperators


-- @@ L511-516 verbatim
theorem rankOne.sum_orthonormalBasis_eq_id_lm {𝕜 : Type _} {E : Type _} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {ι : Type _} [Fintype ι]
    (b : OrthonormalBasis ι 𝕜 E) :
    ∑ i, (rankOne 𝕜 (b i) (b i) : E →L[𝕜] E).toLinearMap = 1 := by
  simp only [← ContinuousLinearMap.toLinearMap_sum, rankOne.sum_orthonormalBasis_eq_id b]
  rfl


-- @@ L518-520 verbatim
theorem ContinuousLinearMap.coe_eq_zero {𝕜 E₁ E₂ : Type _} [RCLike 𝕜] [NormedAddCommGroup E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₁] [InnerProductSpace 𝕜 E₂] (f : E₁ →L[𝕜] E₂) :
    (f : E₁ →ₗ[𝕜] E₂) = 0 ↔ f = 0 := by norm_cast


-- @@ L522-526 verbatim
theorem rankOne.left_sub {𝕜 E₁ E₂ : Type _} [RCLike 𝕜] [NormedAddCommGroup E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₁] [InnerProductSpace 𝕜 E₂]
    (x y : E₁) (z : E₂) :
    rankOne 𝕜 (x - y) z = rankOne 𝕜 x z - rankOne 𝕜 y z := by
  simp_all


-- @@ L528-532 verbatim
theorem rankOne.smul_right_to_left {𝕜 E₁ E₂ : Type _} [RCLike 𝕜] [NormedAddCommGroup E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₁] [InnerProductSpace 𝕜 E₂]
    (x : E₁) (y : E₂) (r : 𝕜) :
    rankOne 𝕜 x (r • y) = rankOne 𝕜 (star r • x) y := by
  simp_all


-- @@ L534-539 verbatim
theorem rankOne.eq_zero_iff {𝕜 E₁ E₂ : Type _} [RCLike 𝕜] [NormedAddCommGroup E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₁] [InnerProductSpace 𝕜 E₂]
    (x : E₁) (y : E₂) :
    rankOne 𝕜 x y = 0 ↔ x = 0 ∨ y = 0 := by
  simp_rw [ContinuousLinearMap.ext_iff, rankOne_apply, zero_apply,
    smul_eq_zero, forall_or_right, forall_inner_eq_zero_iff, or_comm]


-- @@ L541-548 verbatim
theorem LinearMap.rankOne_comp {𝕜 E₁ E₂ E₃ : Type _} [RCLike 𝕜] [NormedAddCommGroup E₁]
  [NormedAddCommGroup E₂] [NormedAddCommGroup E₃] [InnerProductSpace 𝕜 E₁]
  [InnerProductSpace 𝕜 E₂] [InnerProductSpace 𝕜 E₃] [FiniteDimensional 𝕜 E₂]
  [FiniteDimensional 𝕜 E₃] (x : E₁) (y : E₂) (u : E₃ →ₗ[𝕜] E₂) :
    (rankOne 𝕜 x y).toLinearMap ∘ₗ u = (rankOne 𝕜 x (adjoint u y)) := by
  ext
  simp_rw [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, rankOne_apply,
    LinearMap.adjoint_inner_left]


-- @@ L550-555 verbatim
theorem LinearMap.rankOne_comp' {𝕜 E₁ E₂ E₃ : Type _} [RCLike 𝕜] [NormedAddCommGroup E₁]
  [NormedAddCommGroup E₂] [NormedAddCommGroup E₃] [InnerProductSpace 𝕜 E₁]
  [InnerProductSpace 𝕜 E₂] [InnerProductSpace 𝕜 E₃] [FiniteDimensional 𝕜 E₂]
  [FiniteDimensional 𝕜 E₃] (x : E₁) (y : E₂) (u : E₂ →ₗ[𝕜] E₃) :
    (rankOne 𝕜 x y).toLinearMap ∘ₗ adjoint u = (rankOne 𝕜 x (u y)) :=
by rw [LinearMap.rankOne_comp, LinearMap.adjoint_adjoint]


-- @@ L557-563 verbatim
theorem OrthonormalBasis.orthogonalProjection'_eq_sum_rankOne {ι 𝕜 : Type _} [RCLike 𝕜] {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype ι] {U : Submodule 𝕜 E}
    [CompleteSpace U] (b : OrthonormalBasis ι 𝕜 ↥U) :
    orthogonalProjection' U = ∑ i : ι, rankOne 𝕜 (b i : E) (b i : E) := by
  ext
  simp_rw [orthogonalProjection'_apply, OrthonormalBasis.orthogonalProjectionOnto_apply_eq_sum b,
    sum_apply, rankOne_apply, Submodule.coe_sum, Submodule.coe_smul_of_tower]


-- @@ L565-571 verbatim
theorem LinearMap.comp_rankOne {𝕜 E₁ E₂ E₃ : Type _} [RCLike 𝕜] [NormedAddCommGroup E₁]
  [NormedAddCommGroup E₂] [NormedAddCommGroup E₃] [InnerProductSpace 𝕜 E₁]
  [InnerProductSpace 𝕜 E₂]
  [InnerProductSpace 𝕜 E₃] (x : E₁) (y : E₂) (u : E₁ →ₗ[𝕜] E₃) :
    u ∘ₗ (rankOne 𝕜 x y).toLinearMap = rankOne 𝕜 (u x) y := by
  ext
  simp_rw [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, rankOne_apply, _root_.map_smul]



-- @@ L574-579 verbatim
theorem _root_.rankOne_smul_smul {𝕜 E₁ E₂ : Type _} [RCLike 𝕜] [NormedAddCommGroup E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₁] [InnerProductSpace 𝕜 E₂]
    (x : E₁) (y : E₂) (r₁ r₂ : 𝕜) :
    rankOne 𝕜 (r₁ • x) (star r₂ • y) = (r₁ * r₂) • rankOne 𝕜 x y := by
  simp only [map_smulₛₗ, LinearMap.smul_apply, smul_smul, starRingEnd_apply, star_star, mul_comm,
    RingHom.id_apply]


-- @@ L581-586 verbatim
theorem _root_.rankOne_lm_smul_smul {𝕜 E₁ E₂ : Type _} [RCLike 𝕜] [NormedAddCommGroup E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₁] [InnerProductSpace 𝕜 E₂]
    (x : E₁) (y : E₂) (r₁ r₂ : 𝕜) :
    (rankOne 𝕜 (r₁ • x) (star r₂ • y)).toLinearMap =
      (r₁ * r₂) • ((rankOne 𝕜 x y : _ →L[𝕜] _).toLinearMap) :=
  by rw [rankOne_smul_smul, ContinuousLinearMap.toLinearMap_smul]


-- @@ L588-594 verbatim
theorem _root_.rankOne_lm_sum_sum {𝕜 E₁ E₂ : Type _} [RCLike 𝕜] [NormedAddCommGroup E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₁] [InnerProductSpace 𝕜 E₂]
    {ι₁ ι₂ : Type _} {k : Finset ι₁} {k₂ : Finset ι₂} (f : ι₁ → E₁) (g : ι₂ → E₂) :
    (rankOne 𝕜 (∑ i ∈ k, f i) (∑ i ∈ k₂, g i)).toLinearMap =
      ∑ i ∈ k, ∑ j ∈ k₂, (rankOne 𝕜 (f i) (g j)).toLinearMap := by
  simp_rw [map_sum, LinearMap.sum_apply, ContinuousLinearMap.toLinearMap_sum]
  rw [Finset.sum_comm]


-- @@ L596-602 verbatim
theorem ContinuousLinearMap.linearMap_adjoint {𝕜 B C : Type _} [RCLike 𝕜] [NormedAddCommGroup B]
    [NormedAddCommGroup C] [InnerProductSpace 𝕜 B] [InnerProductSpace 𝕜 C] [FiniteDimensional 𝕜 B]
    [FiniteDimensional 𝕜 C] (x : B →L[𝕜] C) :
    LinearMap.adjoint (x : B →ₗ[𝕜] C) =
      @ContinuousLinearMap.adjoint 𝕜 _ _ _ _ _ _ _ (FiniteDimensional.complete 𝕜 B)
        (FiniteDimensional.complete 𝕜 C) x :=
  rfl


-- @@ L604-611 verbatim
theorem LinearMap.toContinuousLinearMap_adjoint {𝕜 B C : Type _} [RCLike 𝕜] [NormedAddCommGroup B]
    [NormedAddCommGroup C] [InnerProductSpace 𝕜 B] [InnerProductSpace 𝕜 C] [FiniteDimensional 𝕜 B]
    [FiniteDimensional 𝕜 C] {x : B →ₗ[𝕜] C} :
  letI := FiniteDimensional.complete 𝕜 B
  letI := FiniteDimensional.complete 𝕜 C
  ContinuousLinearMap.adjoint (toContinuousLinearMap x) =
    toContinuousLinearMap (LinearMap.adjoint x) :=
rfl

-- @@ L612-619 verbatim
theorem LinearMap.toContinuousLinearMap_adjoint' {𝕜 B C : Type _} [RCLike 𝕜] [NormedAddCommGroup B]
    [NormedAddCommGroup C] [InnerProductSpace 𝕜 B] [InnerProductSpace 𝕜 C] [FiniteDimensional 𝕜 B]
    [FiniteDimensional 𝕜 C] {x : B →ₗ[𝕜] C} :
  letI := FiniteDimensional.complete 𝕜 B
  letI := FiniteDimensional.complete 𝕜 C
  ContinuousLinearMap.toLinearMap (ContinuousLinearMap.adjoint (toContinuousLinearMap x)) =
    LinearMap.adjoint x :=
rfl


-- @@ L621-621 verbatim
open scoped InnerProductSpace


-- @@ L623-629 verbatim
theorem OrthonormalBasis.repr_adjoint {ι 𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [Fintype ι] (b : OrthonormalBasis ι 𝕜 E) :
  letI := Module.Basis.finiteDimensional_of_finite b.toBasis
  letI := FiniteDimensional.complete 𝕜 E
  ContinuousLinearMap.adjoint b.repr.toContinuousLinearEquiv.toContinuousLinearMap
    = b.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap := by
  simp_all


-- @@ L631-642 verbatim
theorem OrthonormalBasis.repr_adjoint'
  {ι 𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [Fintype ι] (b : OrthonormalBasis ι 𝕜 E) :
  haveI := Module.Basis.finiteDimensional_of_finite b.toBasis
  haveI := FiniteDimensional.complete 𝕜 E
  LinearMap.adjoint b.repr.toLinearMap
    = b.repr.symm.toLinearMap :=
haveI := Module.Basis.finiteDimensional_of_finite b.toBasis
haveI := FiniteDimensional.complete 𝕜 E
calc LinearMap.adjoint b.repr.toLinearMap
    =  ContinuousLinearMap.adjoint b.repr.toContinuousLinearEquiv.toContinuousLinearMap := rfl
  _ = b.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap := by rw [b.repr_adjoint]


-- @@ L644-644 verbatim
open scoped Matrix

-- @@ L645-660 verbatim
theorem rankOne_toMatrix_of_onb
  {ι₁ ι₂ 𝕜 E₁ E₂ : Type*} [RCLike 𝕜] [NormedAddCommGroup E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₁] [InnerProductSpace 𝕜 E₂]
  [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₂]
  (b₁ : OrthonormalBasis ι₁ 𝕜 E₁) (b₂ : OrthonormalBasis ι₂ 𝕜 E₂) (x : E₁) (y : E₂) :
  LinearMap.toMatrix b₂.toBasis b₁.toBasis (rankOne 𝕜 x y).toLinearMap
    =
    (Matrix.replicateCol (Fin 1) (b₁.repr x)) * (Matrix.replicateCol (Fin 1) (b₂.repr y))ᴴ := by
  ext1 i j
  simp_rw [LinearMap.toMatrix_apply, ContinuousLinearMap.coe_coe, rankOne_apply,
    map_smul, Finsupp.smul_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.coe_toBasis,
    Matrix.conjTranspose_replicateCol]
  simp [Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply,
    Pi.star_apply, OrthonormalBasis.repr_apply_apply, RCLike.star_def, inner_conj_symm,
    smul_eq_mul, mul_comm]


-- @@ L662-662 verbatim
end rankOneLm
