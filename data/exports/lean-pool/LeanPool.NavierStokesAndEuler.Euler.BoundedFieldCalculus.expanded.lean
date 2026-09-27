/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ContinuousPathCalculus
public import LeanPool.NavierStokesAndEuler.Euler.TransverseGramInverse
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus
import Mathlib.Analysis.Calculus.ContDiff.Comp


-- @@ L14-21 verbatim
/-!
# Actual bounded-field bilinear and adjoint calculus

Pointwise application/composition are bounded bilinear maps in the genuine
uniform field norm, including on a noncompact spatial domain. Lifting these
maps to compact time paths preserves their norm bounds. These are the
coefficient maps used to construct the actual source forward generator.
-/


-- @@ L23-23 verbatim
@[expose] public section



-- @@ L26-26 verbatim
noncomputable section


-- @@ L28-28 verbatim
namespace EulerBoundedFieldCalculus


-- @@ L30-30 verbatim
open ContinuousLinearMap EulerTransverseGramInverse EulerOperatorGevreyCalculus EulerGevrey

-- @@ L31-31 verbatim
open scoped BoundedContinuousFunction ContDiff


-- @@ L33-33 verbatim
variable {α : Type*} [TopologicalSpace α]


-- @@ L35-35 verbatim
section Bilinear


-- @@ L37-40 verbatim
variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]


-- @@ L42-43 verbatim
/-- Cache the standard `NormedAddCommGroup (F →L[ℝ] G)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus1 : NormedAddCommGroup (F →L[ℝ] G) := inferInstance

-- @@ L44-45 verbatim
/-- Cache the standard `NormedSpace ℝ (F →L[ℝ] G)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus2 : NormedSpace ℝ (F →L[ℝ] G) := inferInstance

-- @@ L46-48 verbatim
/-- Cache the standard `NormedAddCommGroup (E →L[ℝ] F →L[ℝ] G)` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldCalculus3 : NormedAddCommGroup (E →L[ℝ] F →L[ℝ] G) := inferInstance

-- @@ L49-51 verbatim
/-- Cache the standard `NormedSpace ℝ (E →L[ℝ] F →L[ℝ] G)` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldCalculus4 : NormedSpace ℝ (E →L[ℝ] F →L[ℝ] G) := inferInstance

-- @@ L52-53 verbatim
/-- Cache the standard `NormedAddCommGroup (α →ᵇ E)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus5 : NormedAddCommGroup (α →ᵇ E) := inferInstance

-- @@ L54-55 verbatim
/-- Cache the standard `NormedSpace ℝ (α →ᵇ E)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus6 : NormedSpace ℝ (α →ᵇ E) := inferInstance

-- @@ L56-57 verbatim
/-- Cache the standard `NormedAddCommGroup (α →ᵇ F)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus7 : NormedAddCommGroup (α →ᵇ F) := inferInstance

-- @@ L58-59 verbatim
/-- Cache the standard `NormedSpace ℝ (α →ᵇ F)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus8 : NormedSpace ℝ (α →ᵇ F) := inferInstance

-- @@ L60-61 verbatim
/-- Cache the standard `NormedAddCommGroup (α →ᵇ G)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus9 : NormedAddCommGroup (α →ᵇ G) := inferInstance

-- @@ L62-63 verbatim
/-- Cache the standard `NormedSpace ℝ (α →ᵇ G)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus10 : NormedSpace ℝ (α →ᵇ G) := inferInstance


-- @@ L65-71 verbatim
/-- The literal pointwise bounded bilinear field. -/
def bilinearValue (B : E →L[ℝ] F →L[ℝ] G) (f : α →ᵇ E) (g : α →ᵇ F) : α →ᵇ G :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => B (f x) (g x))
    ((B.continuous.comp f.continuous).clm_apply g.continuous) (‖B‖*‖f‖*‖g‖)
    (fun x => (B.le_opNorm₂ (f x) (g x)).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) (norm_nonneg B))
        (g.norm_coe_le_norm x) (norm_nonneg _) (mul_nonneg (norm_nonneg B) (norm_nonneg f))))


-- @@ L73-74 verbatim
@[simp] theorem bilinearValue_apply (B : E →L[ℝ] F →L[ℝ] G) (f : α →ᵇ E) (g : α →ᵇ F) (x : α) :
    bilinearValue B f g x = B (f x) (g x) := rfl


-- @@ L76-78 verbatim
theorem bilinearValue_norm (B : E →L[ℝ] F →L[ℝ] G) (f : α →ᵇ E) (g : α →ᵇ F) :
    ‖bilinearValue B f g‖ ≤ ‖B‖*‖f‖*‖g‖ :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (by positivity) _


-- @@ L80-103 verbatim
/-- Bilinearity is proved on the actual coefficient functions. -/
def bilinearLinear (B : E →L[ℝ] F →L[ℝ] G) : (α →ᵇ E) →ₗ[ℝ] (α →ᵇ F) →ₗ[ℝ] (α →ᵇ G) where
  toFun f :=
    { toFun := bilinearValue B f
      map_add' g h := by
        apply BoundedContinuousFunction.ext
        intro x
        exact map_add (B (f x)) (g x) (h x)
      map_smul' r g := by
        apply BoundedContinuousFunction.ext
        intro x
        exact map_smul (B (f x)) r (g x) }
  map_add' f g := by
    apply LinearMap.ext
    intro h
    apply BoundedContinuousFunction.ext
    intro x
    exact congrArg (fun L : F →L[ℝ] G => L (h x)) (map_add B (f x) (g x))
  map_smul' r f := by
    apply LinearMap.ext
    intro h
    apply BoundedContinuousFunction.ext
    intro x
    exact congrArg (fun L : F →L[ℝ] G => L (h x)) (map_smul B r (f x))


-- @@ L105-107 verbatim
/-- The actual bilinear map on bounded continuous fields. -/
def bilinearMap (B : E →L[ℝ] F →L[ℝ] G) : (α →ᵇ E) →L[ℝ] (α →ᵇ F) →L[ℝ] (α →ᵇ G) :=
  (bilinearLinear B).mkContinuous₂ ‖B‖ (bilinearValue_norm B)


-- @@ L109-110 verbatim
@[simp] theorem bilinearMap_apply (B : E →L[ℝ] F →L[ℝ] G) (f : α →ᵇ E) (g : α →ᵇ F) (x : α) :
    bilinearMap B f g x = B (f x) (g x) := rfl


-- @@ L112-113 verbatim
theorem bilinearMap_norm (B : E →L[ℝ] F →L[ℝ] G) : ‖bilinearMap (α := α) B‖ ≤ ‖B‖ :=
  (bilinearLinear B).mkContinuous₂_norm_le (norm_nonneg B) (bilinearValue_norm B)


-- @@ L115-121 verbatim
/-- Pointwise postcomposition preserves the coefficient map's norm bound. -/
theorem postcomposition_norm (L : E →L[ℝ] F) : ‖L.compLeftContinuousBounded α‖ ≤ ‖L‖ := by
  apply opNorm_le_bound _ (norm_nonneg L)
  intro f
  apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg L) (norm_nonneg f))).2
  intro x
  exact (L.le_opNorm (f x)).trans (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) (norm_nonneg L))


-- @@ L123-123 verbatim
end Bilinear


-- @@ L125-125 verbatim
section Composition


-- @@ L127-130 verbatim
variable {U E F : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


-- @@ L132-133 verbatim
/-- Cache the standard `NormedAddCommGroup (U →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus11 : NormedAddCommGroup (U →L[ℝ] E) := inferInstance

-- @@ L134-135 verbatim
/-- Cache the standard `NormedSpace ℝ (U →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus12 : NormedSpace ℝ (U →L[ℝ] E) := inferInstance

-- @@ L136-137 verbatim
/-- Cache the standard `NormedAddCommGroup (E →L[ℝ] F)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus13 : NormedAddCommGroup (E →L[ℝ] F) := inferInstance

-- @@ L138-139 verbatim
/-- Cache the standard `NormedSpace ℝ (E →L[ℝ] F)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus14 : NormedSpace ℝ (E →L[ℝ] F) := inferInstance

-- @@ L140-141 verbatim
/-- Cache the standard `NormedAddCommGroup (U →L[ℝ] F)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus15 : NormedAddCommGroup (U →L[ℝ] F) := inferInstance

-- @@ L142-143 verbatim
/-- Cache the standard `NormedSpace ℝ (U →L[ℝ] F)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus16 : NormedSpace ℝ (U →L[ℝ] F) := inferInstance

-- @@ L144-146 verbatim
/-- Cache the standard `NormedAddCommGroup (α →ᵇ U →L[ℝ] E)` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldCalculus17 : NormedAddCommGroup (α →ᵇ U →L[ℝ] E) := inferInstance

-- @@ L147-148 verbatim
/-- Cache the standard `NormedSpace ℝ (α →ᵇ U →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus18 : NormedSpace ℝ (α →ᵇ U →L[ℝ] E) := inferInstance

-- @@ L149-151 verbatim
/-- Cache the standard `NormedAddCommGroup (α →ᵇ E →L[ℝ] F)` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldCalculus19 : NormedAddCommGroup (α →ᵇ E →L[ℝ] F) := inferInstance

-- @@ L152-153 verbatim
/-- Cache the standard `NormedSpace ℝ (α →ᵇ E →L[ℝ] F)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus20 : NormedSpace ℝ (α →ᵇ E →L[ℝ] F) := inferInstance

-- @@ L154-156 verbatim
/-- Cache the standard `NormedAddCommGroup (α →ᵇ U →L[ℝ] F)` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldCalculus21 : NormedAddCommGroup (α →ᵇ U →L[ℝ] F) := inferInstance

-- @@ L157-158 verbatim
/-- Cache the standard `NormedSpace ℝ (α →ᵇ U →L[ℝ] F)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus22 : NormedSpace ℝ (α →ᵇ U →L[ℝ] F) := inferInstance

-- @@ L159-163 verbatim
/-- Cache the standard `NormedAddCommGroup ((α →ᵇ U →L[ℝ] E) →L[ℝ] (α →ᵇ U →L[ℝ] F))` instance
to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus23 : NormedAddCommGroup ((α →ᵇ U →L[ℝ] E) →L[ℝ] (α →ᵇ U
    →L[ℝ] F)) :=
    inferInstance

-- @@ L164-167 verbatim
/-- Cache the standard `NormedSpace ℝ ((α →ᵇ U →L[ℝ] E) →L[ℝ] (α →ᵇ U →L[ℝ] F))` instance to
shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus24 : NormedSpace ℝ ((α →ᵇ U →L[ℝ] E) →L[ℝ] (α →ᵇ U →L[ℝ] F))
    := inferInstance


-- @@ L169-171 verbatim
/-- The literal composition of two bounded operator fields. -/
def compositionMap : (α →ᵇ E →L[ℝ] F) →L[ℝ] (α →ᵇ U →L[ℝ] E) →L[ℝ] (α →ᵇ U →L[ℝ] F) :=
  bilinearMap (compL ℝ U E F)


-- @@ L173-174 verbatim
theorem compositionMap_norm : ‖compositionMap (α := α) (U := U) (E := E) (F := F)‖ ≤ 1 :=
  (bilinearMap_norm (compL ℝ U E F)).trans (norm_compL_le ℝ U E F)


-- @@ L176-177 verbatim
@[simp] theorem compositionMap_apply (A : α →ᵇ E →L[ℝ] F) (B : α →ᵇ U →L[ℝ] E) (x : α) :
    compositionMap (α := α) (U := U) (E := E) (F := F) A B x = (A x).comp (B x) := rfl


-- @@ L179-179 verbatim
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]


-- @@ L181-184 verbatim
/-- Cache the standard `NormedAddCommGroup (C(K,α →ᵇ U →L[ℝ] E))` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldCalculus25 : NormedAddCommGroup (C(K,α →ᵇ U →L[ℝ] E)) :=
    inferInstance

-- @@ L185-187 verbatim
/-- Cache the standard `NormedSpace ℝ (C(K,α →ᵇ U →L[ℝ] E))` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldCalculus26 : NormedSpace ℝ (C(K,α →ᵇ U →L[ℝ] E)) := inferInstance

-- @@ L188-191 verbatim
/-- Cache the standard `NormedAddCommGroup (C(K,α →ᵇ E →L[ℝ] F))` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldCalculus27 : NormedAddCommGroup (C(K,α →ᵇ E →L[ℝ] F)) :=
    inferInstance

-- @@ L192-194 verbatim
/-- Cache the standard `NormedSpace ℝ (C(K,α →ᵇ E →L[ℝ] F))` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldCalculus28 : NormedSpace ℝ (C(K,α →ᵇ E →L[ℝ] F)) := inferInstance

-- @@ L195-198 verbatim
/-- Cache the standard `NormedAddCommGroup (C(K,α →ᵇ U →L[ℝ] F))` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldCalculus29 : NormedAddCommGroup (C(K,α →ᵇ U →L[ℝ] F)) :=
    inferInstance

-- @@ L199-201 verbatim
/-- Cache the standard `NormedSpace ℝ (C(K,α →ᵇ U →L[ℝ] F))` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldCalculus30 : NormedSpace ℝ (C(K,α →ᵇ U →L[ℝ] F)) := inferInstance

-- @@ L202-206 verbatim
/-- Cache the standard `NormedAddCommGroup (C(K,(α →ᵇ U →L[ℝ] E) →L[ℝ] (α →ᵇ U →L[ℝ] F)))`
instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus31 : NormedAddCommGroup (C(K,(α →ᵇ U →L[ℝ] E) →L[ℝ] (α →ᵇ U
    →L[ℝ] F))) :=
    inferInstance

-- @@ L207-211 verbatim
/-- Cache the standard `NormedSpace ℝ (C(K,(α →ᵇ U →L[ℝ] E) →L[ℝ] (α →ᵇ U →L[ℝ] F)))` instance
to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus32 : NormedSpace ℝ (C(K,(α →ᵇ U →L[ℝ] E) →L[ℝ] (α →ᵇ U →L[ℝ]
    F))) :=
    inferInstance

-- @@ L212-216 verbatim
/-- Cache the standard `NormedAddCommGroup (C(K,α →ᵇ U →L[ℝ] E) →L[ℝ] C(K,α →ᵇ U →L[ℝ] F))`
instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus33 : NormedAddCommGroup (C(K,α →ᵇ U →L[ℝ] E) →L[ℝ] C(K,α →ᵇ
    U →L[ℝ] F)) :=
    inferInstance

-- @@ L217-221 verbatim
/-- Cache the standard `NormedSpace ℝ (C(K,α →ᵇ U →L[ℝ] E) →L[ℝ] C(K,α →ᵇ U →L[ℝ] F))` instance
to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus34 : NormedSpace ℝ (C(K,α →ᵇ U →L[ℝ] E) →L[ℝ] C(K,α →ᵇ U
    →L[ℝ] F)) :=
    inferInstance


-- @@ L223-228 verbatim
/-- Pointwise spatial composition, uniformly along a compact time path. -/
def pathCompositionMap : C(K,α →ᵇ E →L[ℝ] F) →L[ℝ]
    C(K,α →ᵇ U →L[ℝ] E) →L[ℝ] C(K,α →ᵇ U →L[ℝ] F) :=
  (EulerContinuousPathCalculus.coefficientMap (K := K)
    (E := α →ᵇ U →L[ℝ] E) (F := α →ᵇ U →L[ℝ] F)) ∘L
    ((compositionMap (α := α) (U := U) (E := E) (F := F)).compLeftContinuous ℝ K)


-- @@ L230-233 verbatim
@[simp] theorem pathCompositionMap_apply (A : C(K, α →ᵇ E →L[ℝ] F))
    (B : C(K, α →ᵇ U →L[ℝ] E)) (t : K) (x : α) :
    pathCompositionMap (α := α) (K := K) (U := U) (E := E) (F := F) A B t x =
      (A t x).comp (B t x) := rfl


-- @@ L235-248 verbatim
theorem pathCompositionMap_norm : ‖pathCompositionMap (α := α) (K := K) (U := U) (E := E) (F := F)‖
    ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro A
  rw [one_mul]
  apply opNorm_le_bound _ (norm_nonneg A)
  intro B
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg B))).2
  intro t
  apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg A) (norm_nonneg B))).2
  intro x
  exact (opNorm_comp_le (A t x) (B t x)).trans
    (mul_le_mul (((A t).norm_coe_le_norm x).trans (A.norm_coe_le_norm t))
      (((B t).norm_coe_le_norm x).trans (B.norm_coe_le_norm t)) (norm_nonneg _) (norm_nonneg A))


-- @@ L250-250 verbatim
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]


-- @@ L252-260 verbatim
/-- Genuine smoothness of pointwise field composition in the uniform time-space norm. -/
theorem pathComposition_contDiff (A : P → C(K, α →ᵇ E →L[ℝ] F))
    (B : P → C(K, α →ᵇ U →L[ℝ] E)) {n : ℕ∞ω} (hA : ContDiff ℝ n A) (hB : ContDiff ℝ n B) :
    ContDiff ℝ n (fun y =>
      pathCompositionMap (α := α) (K := K) (U := U) (E := E) (F := F) (A y) (B y)) :=
  ((ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := n)
    (E := C(K,α →ᵇ E →L[ℝ] F))
    (F := C(K,α →ᵇ U →L[ℝ] E) →L[ℝ] C(K,α →ᵇ U →L[ℝ] F))
    (pathCompositionMap (α := α) (K := K) (U := U) (E := E) (F := F))).comp hA).clm_apply hB


-- @@ L262-273 verbatim
/-- The actual field product has the same factorial convolution bound. -/
theorem pathComposition_bound (A : P → C(K, α →ᵇ E →L[ℝ] F))
    (B : P → C(K, α →ᵇ U →L[ℝ] E)) (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B)
    (R C D : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D) (c d : ℕ)
    (hbA : ∀ n x, ‖iteratedFDeriv ℝ n A x‖ ≤ C * majorant R c n)
    (hbB : ∀ n x, ‖iteratedFDeriv ℝ n B x‖ ≤ D * majorant R d n) (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y =>
      pathCompositionMap (α := α) (K := K) (U := U) (E := E) (F := F) (A y) (B y)) x‖ ≤
        (3*C*D)*majorant R (c+d) n :=
  bilinear_bound (pathCompositionMap (α := α) (K := K) (U := U) (E := E) (F := F))
    (pathCompositionMap_norm (α := α) (K := K) (U := U) (E := E) (F := F))
    A B hA hB R C D hR hC hD c d hbA hbB n x


-- @@ L275-275 verbatim
end Composition


-- @@ L277-277 verbatim
section Adjoint


-- @@ L279-281 verbatim
variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]


-- @@ L283-284 verbatim
/-- Cache the standard `NormedAddCommGroup (U →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus35 : NormedAddCommGroup (U →L[ℝ] E) := inferInstance

-- @@ L285-286 verbatim
/-- Cache the standard `NormedSpace ℝ (U →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus36 : NormedSpace ℝ (U →L[ℝ] E) := inferInstance

-- @@ L287-288 verbatim
/-- Cache the standard `NormedAddCommGroup (E →L[ℝ] U)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus37 : NormedAddCommGroup (E →L[ℝ] U) := inferInstance

-- @@ L289-290 verbatim
/-- Cache the standard `NormedSpace ℝ (E →L[ℝ] U)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus38 : NormedSpace ℝ (E →L[ℝ] U) := inferInstance

-- @@ L291-293 verbatim
/-- Cache the standard `NormedAddCommGroup (α →ᵇ U →L[ℝ] E)` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldCalculus39 : NormedAddCommGroup (α →ᵇ U →L[ℝ] E) := inferInstance

-- @@ L294-295 verbatim
/-- Cache the standard `NormedSpace ℝ (α →ᵇ U →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus40 : NormedSpace ℝ (α →ᵇ U →L[ℝ] E) := inferInstance

-- @@ L296-298 verbatim
/-- Cache the standard `NormedAddCommGroup (α →ᵇ E →L[ℝ] U)` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldCalculus41 : NormedAddCommGroup (α →ᵇ E →L[ℝ] U) := inferInstance

-- @@ L299-300 verbatim
/-- Cache the standard `NormedSpace ℝ (α →ᵇ E →L[ℝ] U)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus42 : NormedSpace ℝ (α →ᵇ E →L[ℝ] U) := inferInstance

-- @@ L301-305 verbatim
/-- Cache the standard `NormedAddCommGroup ((α →ᵇ U →L[ℝ] E) →L[ℝ] (α →ᵇ E →L[ℝ] U))` instance
to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus43 : NormedAddCommGroup ((α →ᵇ U →L[ℝ] E) →L[ℝ] (α →ᵇ E
    →L[ℝ] U)) :=
    inferInstance

-- @@ L306-309 verbatim
/-- Cache the standard `NormedSpace ℝ ((α →ᵇ U →L[ℝ] E) →L[ℝ] (α →ᵇ E →L[ℝ] U))` instance to
shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus44 : NormedSpace ℝ ((α →ᵇ U →L[ℝ] E) →L[ℝ] (α →ᵇ E →L[ℝ] U))
    := inferInstance


-- @@ L311-313 verbatim
/-- The actual adjoint of every bounded coefficient operator. -/
def adjointMap : (α →ᵇ U →L[ℝ] E) →L[ℝ] (α →ᵇ E →L[ℝ] U) :=
  (realAdjoint (U := U) (E := E)).compLeftContinuousBounded α


-- @@ L315-316 verbatim
@[simp] theorem adjointMap_apply (A : α →ᵇ U →L[ℝ] E) (x : α) : adjointMap A x = (A x).adjoint :=
    rfl


-- @@ L318-326 verbatim
theorem adjointMap_norm : ‖adjointMap (α := α) (U := U) (E := E)‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro A
  rw [one_mul]
  apply (BoundedContinuousFunction.norm_le (norm_nonneg A)).2
  intro x
  change ‖(A x).adjoint‖ ≤ ‖A‖
  rw [LinearIsometryEquiv.norm_map]
  exact A.norm_coe_le_norm x


-- @@ L328-328 verbatim
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]


-- @@ L330-333 verbatim
/-- Cache the standard `NormedAddCommGroup (C(K,α →ᵇ U →L[ℝ] E))` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldCalculus45 : NormedAddCommGroup (C(K,α →ᵇ U →L[ℝ] E)) :=
    inferInstance

-- @@ L334-336 verbatim
/-- Cache the standard `NormedSpace ℝ (C(K,α →ᵇ U →L[ℝ] E))` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldCalculus46 : NormedSpace ℝ (C(K,α →ᵇ U →L[ℝ] E)) := inferInstance

-- @@ L337-340 verbatim
/-- Cache the standard `NormedAddCommGroup (C(K,α →ᵇ E →L[ℝ] U))` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldCalculus47 : NormedAddCommGroup (C(K,α →ᵇ E →L[ℝ] U)) :=
    inferInstance

-- @@ L341-343 verbatim
/-- Cache the standard `NormedSpace ℝ (C(K,α →ᵇ E →L[ℝ] U))` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldCalculus48 : NormedSpace ℝ (C(K,α →ᵇ E →L[ℝ] U)) := inferInstance

-- @@ L344-348 verbatim
/-- Cache the standard `NormedAddCommGroup (C(K,α →ᵇ U →L[ℝ] E) →L[ℝ] C(K,α →ᵇ E →L[ℝ] U))`
instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus49 : NormedAddCommGroup (C(K,α →ᵇ U →L[ℝ] E) →L[ℝ] C(K,α →ᵇ
    E →L[ℝ] U)) :=
    inferInstance

-- @@ L349-353 verbatim
/-- Cache the standard `NormedSpace ℝ (C(K,α →ᵇ U →L[ℝ] E) →L[ℝ] C(K,α →ᵇ E →L[ℝ] U))` instance
to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus50 : NormedSpace ℝ (C(K,α →ᵇ U →L[ℝ] E) →L[ℝ] C(K,α →ᵇ E
    →L[ℝ] U)) :=
    inferInstance


-- @@ L355-357 verbatim
/-- The bounded adjoint map on entire coefficient paths. -/
def pathAdjointMap : C(K,α →ᵇ U →L[ℝ] E) →L[ℝ] C(K,α →ᵇ E →L[ℝ] U) :=
  (adjointMap (α := α) (U := U) (E := E)).compLeftContinuous ℝ K


-- @@ L359-361 verbatim
omit [CompactSpace K] in
@[simp] theorem pathAdjointMap_apply (A : C(K, α →ᵇ U →L[ℝ] E)) (t : K) (x : α) :
    pathAdjointMap (α := α) (K := K) (U := U) (E := E) A t x = (A t x).adjoint := rfl


-- @@ L363-373 verbatim
theorem pathAdjointMap_norm : ‖pathAdjointMap (α := α) (K := K) (U := U) (E := E)‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro A
  rw [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg A)).2
  intro t
  apply (BoundedContinuousFunction.norm_le (norm_nonneg A)).2
  intro x
  change ‖(A t x).adjoint‖ ≤ ‖A‖
  rw [LinearIsometryEquiv.norm_map]
  exact ((A t).norm_coe_le_norm x).trans (A.norm_coe_le_norm t)


-- @@ L375-375 verbatim
end Adjoint


-- @@ L377-377 verbatim
end EulerBoundedFieldCalculus
