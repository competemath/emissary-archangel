/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.Analysis.Normed.Operator.Extend
public import Physlib.Meta.TODO.Basic

-- @@ L12-54 verbatim
/-!

# Complete tensor product

## i. Overview

Given two inner product spaces `E` and `F` over `𝕜`, their tensor product `E ⊗[𝕜] F` consists
of finite sums of simple (a.k.a. pure) tensors `m ⊗ₜ[𝕜] n`. This tensor product is again an inner
product space with inner product defined by `⟪m ⊗ₜ n, m' ⊗ₜ n'⟫_𝕜 = ⟪m, m'⟫_𝕜 * ⟪n, n'⟫_𝕜`
on simple tensors and then extended by linearity (c.f. `TensorProduct.instInnerProductSpace`).

However, in general this procedure does not result in a Hilbert space: Cauchy sequences need not
converge because the tensor product does not contain any _infinite_ sums of simple tensors.
In order to obtain a Hilbert space for use in quantum mechanics, we must _add in_ the limits
of Cauchy sequences by taking the completion.

In this module we define the complete tensor product,
`CompleteTensorProduct 𝕜 E F := Completion (E ⊗[𝕜] F)` with notation `E ⊗ₕ[𝕜] F` and `E ⊗ₕ F`,
provide some basic properties for the maps which embed `E ⊗[𝕜] F` into `E ⊗ₕ[𝕜] F`
and prove that `⊗ₕ` is commutative and associative (up to linear isometric equivalence).

## ii. Key results

- `CompleteTensorProduct 𝕜 E F` (notation `E ⊗ₕ[𝕜] F` and `E ⊗ₕ F`) :
    The _completion_ of the tensor product of a pair of inner product spaces `E` and `F` over `𝕜`.
- `CompleteTensorProduct.comm 𝕜 E F` : The linear isometric equivalence between
    `E ⊗ₕ[𝕜] F` and `F ⊗ₕ[𝕜] E`.
- `CompleteTensorProduct.assoc 𝕜 E F G` : The linear isometric equivalence between
    `E ⊗ₕ[𝕜] F ⊗ₕ[𝕜] G` and `E ⊗ₕ[𝕜] (F ⊗ₕ[𝕜] G)`.

## iii. Table of contents

- A. Definition
- B. Nontrivial
- C. Coercions
- D. Induction principle
- E. Commutative
- F. Associative

## iv. References

* None.
-/


-- @@ L56-56 verbatim
@[expose] public section


-- @@ L58-58 verbatim
noncomputable section


-- @@ L60-60 verbatim
open UniformSpace

-- @@ L61-61 verbatim
open scoped InnerProductSpace TensorProduct


-- @@ L63-65 verbatim
/-!
## A. Definition
-/


-- @@ L67-73 verbatim
/-- The _completion_ of the tensor product of two inner product spaces `E` and `F` over `𝕜`.
  By construction this produces a Hilbert space. The localized notations are `E ⊗ₕ F`
  and `E ⊗ₕ[𝕜] F`, accessed by `open scoped CompleteTensorProduct`. -/
def CompleteTensorProduct (𝕜 : Type*) [RCLike 𝕜]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] : Type _ := Completion (E ⊗[𝕜] F)
deriving NormedAddCommGroup, InnerProductSpace 𝕜, CompleteSpace


-- @@ L75-76 verbatim
@[inherit_doc CompleteTensorProduct]
scoped[CompleteTensorProduct] infixl:100 " ⊗ₕ " => CompleteTensorProduct _


-- @@ L78-80 verbatim
@[inherit_doc]
scoped[CompleteTensorProduct]
notation:100 E:100 " ⊗ₕ[" 𝕜 "] " F:101 => CompleteTensorProduct 𝕜 E F


-- @@ L82-82 verbatim
namespace CompleteTensorProduct


-- @@ L84-84 verbatim
variable (𝕜 : Type*) [RCLike 𝕜]

-- @@ L85-85 verbatim
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

-- @@ L86-86 verbatim
variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]


-- @@ L88-90 verbatim
/-!
## B. Nontrivial
-/


-- @@ L92-92 verbatim
section Nontrivial


-- @@ L94-94 verbatim
variable [Nontrivial E] [Nontrivial F]


-- @@ L96-100 verbatim
instance _root_.TensorProduct.instNontrivial : Nontrivial (E ⊗[𝕜] F) where
  exists_pair_ne := by
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    obtain ⟨y, hy⟩ := exists_ne (0 : F)
    exact ⟨x ⊗ₜ y, 0, norm_pos_iff.mp (by simp [hx, hy])⟩


-- @@ L102-105 verbatim
instance instNontrivial : Nontrivial (E ⊗ₕ[𝕜] F) where
  exists_pair_ne := by
    obtain ⟨x, hx⟩ := exists_ne (0 : E ⊗[𝕜] F)
    exact ⟨Completion.coe' x, 0, fun h ↦ hx <| Completion.coe_eq_zero_iff.mp h⟩


-- @@ L107-107 verbatim
end Nontrivial


-- @@ L109-111 verbatim
/-!
## C. Coercions
-/


-- @@ L113-113 verbatim
section Coercion


-- @@ L115-115 verbatim
variable {𝕜 E F} (c : 𝕜) (x y : E ⊗[𝕜] F)


-- @@ L117-119 verbatim
/-- The canonical embedding of the tensor product into its completion. -/
@[coe]
def coe' : E ⊗[𝕜] F → E ⊗ₕ[𝕜] F := Completion.coe'


-- @@ L121-122 verbatim
/-- Coercion from `E ⊗[𝕜] F` to its completion. -/
instance : Coe (E ⊗[𝕜] F) (E ⊗ₕ[𝕜] F) := ⟨coe'⟩


-- @@ L124-124 verbatim
lemma denseRange_coe : DenseRange (coe' : E ⊗[𝕜] F → E ⊗ₕ[𝕜] F) := Completion.denseRange_coe


-- @@ L126-127 verbatim
@[norm_cast]
lemma coe_zero : (0 : E ⊗[𝕜] F) = (0 : E ⊗ₕ[𝕜] F) := rfl


-- @@ L129-131 verbatim
variable {x} in
@[simp]
lemma coe_eq_zero_iff : (x : E ⊗ₕ[𝕜] F) = 0 ↔ x = 0 := Completion.coe_eq_zero_iff


-- @@ L133-134 verbatim
@[norm_cast]
lemma coe_neg : (-x : E ⊗[𝕜] F) = (-x : E ⊗ₕ[𝕜] F) := Completion.coe_neg _


-- @@ L136-137 verbatim
@[norm_cast]
lemma coe_sub : (x - y : E ⊗[𝕜] F) = (x - y : E ⊗ₕ[𝕜] F) := Completion.coe_sub _ _


-- @@ L139-140 verbatim
@[norm_cast]
lemma coe_add : (x + y : E ⊗[𝕜] F) = (x + y : E ⊗ₕ[𝕜] F) := Completion.coe_add _ _


-- @@ L142-143 verbatim
@[simp, norm_cast]
lemma coe_smul : (c • x : E ⊗[𝕜] F) = (c • x : E ⊗ₕ[𝕜] F) := Completion.coe_smul _ _


-- @@ L145-146 verbatim
@[simp]
lemma inner_coe : ⟪(x : E ⊗ₕ[𝕜] F), (y : E ⊗ₕ[𝕜] F)⟫_𝕜 = ⟪x, y⟫_𝕜 := Completion.inner_coe _ _


-- @@ L148-149 verbatim
@[simp]
lemma norm_coe : ‖(x : E ⊗ₕ[𝕜] F)‖ = ‖x‖ := Completion.norm_coe _


-- @@ L151-152 verbatim
/-- The canonical embedding of the tensor product into its completion as a linear isometry. -/
def tInclₗᵢ : E ⊗[𝕜] F →ₗᵢ[𝕜] E ⊗ₕ[𝕜] F := Completion.toComplₗᵢ


-- @@ L154-155 verbatim
@[simp]
lemma coe_tInclₗᵢ : ⇑(tInclₗᵢ : E ⊗ F →ₗᵢ[𝕜] E ⊗ₕ F) = coe' := rfl


-- @@ L157-158 verbatim
/-- The canonical embedding of the tensor product into its completion as a continuous linear map. -/
def tInclL : E ⊗[𝕜] F →L[𝕜] E ⊗ₕ[𝕜] F := tInclₗᵢ.toContinuousLinearMap


-- @@ L160-161 verbatim
@[simp]
lemma coe_tInclL : ⇑(tInclL : E ⊗ F →L[𝕜] E ⊗ₕ F) = coe' := rfl


-- @@ L163-165 verbatim
@[simp]
lemma norm_tInclL [Nontrivial E] [Nontrivial F] : ‖(tInclL : E ⊗ F →L[𝕜] E ⊗ₕ F)‖ = 1 :=
  (tInclₗᵢ : E ⊗ F →ₗᵢ[𝕜] E ⊗ₕ F).norm_toContinuousLinearMap


-- @@ L167-167 verbatim
end Coercion


-- @@ L169-171 verbatim
/-!
## D. Induction principle
-/


-- @@ L173-173 verbatim
section Induction


-- @@ L175-175 verbatim
variable {𝕜 E F}


-- @@ L177-184 verbatim
/-- An induction principle for `CompleteTensorProduct` combining those of `Completion`
  and `TensorProduct`. -/
@[elab_as_elim]
lemma induction_on {motive : E ⊗ₕ[𝕜] F → Prop} (z : E ⊗ₕ[𝕜] F)
    (zero : motive 0) (tmul : ∀ (x : E) (y : F), motive (x ⊗ₜ[𝕜] y))
    (add : ∀ x y : E ⊗[𝕜] F, motive x → motive y → motive ↑(x + y))
    (closed : IsClosed {x | motive x}) : motive z :=
  Completion.induction_on z closed fun x ↦ x.induction_on zero tmul add


-- @@ L186-186 verbatim
end Induction


-- @@ L188-190 verbatim
/-!
## E. Commutative
-/


-- @@ L192-192 verbatim
section Commutative


-- @@ L194-198 verbatim
/-- The complete tensor product of inner product spaces is commutative,
  up to linear isometric equivalence. -/
def comm : E ⊗ₕ[𝕜] F ≃ₗᵢ[𝕜] F ⊗ₕ[𝕜] E :=
  (TensorProduct.comm 𝕜 E F).extendOfIsometry tInclₗᵢ.toLinearMap tInclₗᵢ.toLinearMap
    denseRange_coe denseRange_coe (by simp)


-- @@ L200-201 verbatim
@[simp]
lemma comm_symm : (comm 𝕜 E F).symm = comm 𝕜 F E := rfl


-- @@ L203-206 verbatim
variable {𝕜 E F} in
@[simp]
lemma comm_coe (x : E ⊗[𝕜] F) : comm 𝕜 E F x = TensorProduct.comm 𝕜 E F x :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ _


-- @@ L208-208 verbatim
end Commutative


-- @@ L210-212 verbatim
/-!
## F. Associative
-/


-- @@ L214-214 verbatim
section Associative


-- @@ L216-238 verbatim
/-- The tensor product of a pair of linear maps with dense range also has dense range. -/
lemma _root_.TensorProduct.denseRange_map
    {R 𝕜 : Type*} [CommSemiring R] [RCLike 𝕜] {σ : R →+* 𝕜} [RingHomSurjective σ]
    {M : Type*} [AddCommMonoid M] [Module R M] {N : Type*} [AddCommMonoid N] [Module R N]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    {f : M →ₛₗ[σ] E} (hf : DenseRange f) {g : N →ₛₗ[σ] F} (hg : DenseRange g) :
    DenseRange (TensorProduct.map f g) := by
  intro x
  change x ∈ (TensorProduct.map f g).range.topologicalClosure
  refine x.induction_on (Submodule.zero_mem _) (fun a b ↦ ?_) (fun _ _ ↦ Submodule.add_mem _)
  refine map_mem_closure₂' (fun u ↦ ?_) (fun v ↦ ?_) (hf a) (hg b) ?_
  · refine Metric.continuous_iff.mpr fun v ε hε ↦ ⟨ε / (1 + ‖u‖), by positivity, fun s hs ↦ ?_⟩
    rw [dist_eq_norm, ← TensorProduct.tmul_sub, TensorProduct.norm_tmul] at *
    refine lt_of_le_of_lt (b := (1 + ‖u‖) * ‖s - v‖) ?_ ?_
    · exact mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg _)
    · exact (lt_div_iff₀' <| by positivity).mp hs
  · refine Metric.continuous_iff.mpr fun u ε hε ↦ ⟨ε / (1 + ‖v‖), by positivity, fun s hs ↦ ?_⟩
    rw [dist_eq_norm, ← TensorProduct.sub_tmul, TensorProduct.norm_tmul] at *
    refine lt_of_le_of_lt (b := ‖s - u‖ * (1 + ‖v‖)) ?_ ?_
    · exact mul_le_mul_of_nonneg_left (by norm_num) (norm_nonneg _)
    · exact (lt_div_iff₀ <| by positivity).mp hs
  · exact fun _ ⟨u, hu⟩ _ ⟨v, hv⟩ ↦ ⟨u ⊗ₜ v, by simp [hu, hv]⟩


-- @@ L240-240 verbatim
variable (G : Type*) [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]


-- @@ L242-255 verbatim
/-- The compete tensor product of inner product spaces is associative,
  up to linear isometric equivalence. -/
def assoc : E ⊗ₕ[𝕜] F ⊗ₕ[𝕜] G ≃ₗᵢ[𝕜] E ⊗ₕ[𝕜] (F ⊗ₕ[𝕜] G) :=
  (TensorProduct.assoc 𝕜 E F G).extendOfIsometry
    (tInclₗᵢ.comp (tInclₗᵢ.rTensor G)).toLinearMap (tInclₗᵢ.comp (tInclₗᵢ.lTensor E)).toLinearMap
    (by
      rw [LinearIsometry.coe_toLinearMap, LinearIsometry.coe_comp]
      refine DenseRange.comp denseRange_coe ?_ tInclₗᵢ.continuous
      exact TensorProduct.denseRange_map denseRange_coe denseRange_id)
    (by
      rw [LinearIsometry.coe_toLinearMap, LinearIsometry.coe_comp]
      refine DenseRange.comp denseRange_coe ?_ tInclₗᵢ.continuous
      exact TensorProduct.denseRange_map denseRange_id denseRange_coe)
    fun _ ↦ by simp only [LinearIsometry.norm_map', TensorProduct.norm_assoc]


-- @@ L257-261 verbatim
TODO "Prove CompleteTensorProduct.assoc acting on elements of the tensor product
  reduces to TensorProduct.assoc. It may be worthwhile to extract and name the linear isometries
  (tInclₗᵢ.comp (tInclₗᵢ.rTensor G) : E ⊗[𝕜] F ⊗[𝕜] G →ₗᵢ[𝕜] E ⊗ₕ[𝕜] F ⊗ₕ[𝕜] G) and
  (tInclₗᵢ.comp (tInclₗᵢ.lTensor E) : E ⊗[𝕜] (F ⊗[𝕜] G) →ₗᵢ[𝕜] E ⊗ₕ[𝕜] (F ⊗ₕ[𝕜] G))
  which embed 3-fold tensor products into their completion."


-- @@ L263-263 verbatim
end Associative


-- @@ L265-268 verbatim
TODO "Define LinearPMap.lTensor/rTensor, TensorProduct.mapP (P = 'partial'?) for the tensor product.
  See LinearMap/LinearEquiv/ContinuousLinearMap/LinearIsometry/LinearIsometryEquiv.lTensor/rTensor
  and TensorProduct.map/congr/mapL/mapIsometry/congrIsometry for the desired pattern. The tensor
  product of two LinearPMaps f and g is the canonical LinearPMap with domain f.domain ⊗ g.domain."


-- @@ L270-273 verbatim
TODO "Define CompleteTensorProduct.mapLₕ/mapPₕ/etc. (or a different naming scheme) which take pairs
  of continuous/partial/etc. maps or congruences and construct the corresponding map/congruence
  on complete tensor products (using, for example, ContinuousLinearMap.extend with tInclL).
  c.f. TensorProduct.map/congr/mapL/mapIsometry/congrIsometry."


-- @@ L275-275 verbatim
end CompleteTensorProduct

-- @@ L276-276 verbatim
end
