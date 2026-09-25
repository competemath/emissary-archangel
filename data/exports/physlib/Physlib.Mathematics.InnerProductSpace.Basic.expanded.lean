/-
Copyright (c) 2025 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.ProdL2

-- @@ L10-28 verbatim
/-!

# Inner product space

In this module we define the type class `InnerProductSpace' 𝕜 E` which is a
generalization of `InnerProductSpace 𝕜 E`, as it does not require the condition `‖x‖^2 = ⟪x,x⟫`
but instead the condition `∃ (c > 0) (d > 0), c • ‖x‖^2 ≤ ⟪x,x⟫ ≤ d • ‖x‖^2`.
Instead `E` is equipped with a L₂ norm `‖x‖₂` which satisfies `‖x‖₂ = √⟪x,x⟫`.

This allows us to define the inner product space structure on product types `E × F` and
pi types `ι → E`, which would otherwise not be possible due to the use of max norm on these types.

We define the following maps:

- `InnerProductSpace 𝕜 E → InnerProductSpace' 𝕜 E` which sets `‖x‖₂ = ‖x‖`.
- `InnerProductSpace' 𝕜 E → InnerProductSpace 𝕜 (WithLp 2 E)` which uses the fact that the norm
  defined on `WithLp 2 E` is L₂ norm.

-/


-- @@ L30-30 verbatim
@[expose] public section


-- @@ L32-37 verbatim
/-- L₂ norm on `E`.

In particular, on product types `X×Y` and pi types `ι → X` this class provides L₂ norm unlike `‖·‖`.
-/
class Norm₂ (E : Type*) where
  norm₂ : E → ℝ


-- @@ L39-39 verbatim
export Norm₂ (norm₂)


-- @@ L41-41 verbatim
attribute [inherit_doc Norm₂] norm₂


-- @@ L43-44 verbatim
@[inherit_doc Norm₂]
notation:max "‖" x "‖₂" => norm₂ x


-- @@ L46-46 verbatim
open RCLike ComplexConjugate


-- @@ L48-81 expanded
/-- Effectively as `InnerProductSpace 𝕜 E` but it does not requires that `‖x‖^2 = ⟪x,x⟫`. It is
only required that they are equivalent `∃ (c > 0) (d > 0), c • ‖x‖^2 ≤ ⟪x,x⟫ ≤ d • ‖x‖^2`. The main
purpose of this class is to provide inner product space structure on product types `ExF` and
pi types `ι → E` without using `WithLp` gadget.

If you want to access L₂ norm use `‖x‖₂ := √⟪x,x⟫`.

This class induces `InnerProductSpace 𝕜 (WithLp 2 E)` which equips `‖·‖` on `X` with L₂ norm.
This is very useful when translating results from `InnerProductSpace` to `InnerProductSpace'`
together with `toL2 : E →L[𝕜] (WithLp 2 E)` and `fromL2 : (WithL2 2 E) →L[𝕜] E`.

In short we have these implications:
```
  InnerProductSpace 𝕜 E → InnerProductSpace' 𝕜 E
  InnerProductSpace' 𝕜 E → InnerProductSpace 𝕜 (WithLp 2 E)
```

The reason behind this type class is that with current mathlib design the requirement
`‖x‖^2 = ⟪x,x⟫` prevents us to give inner product space structure on product type `E×F` and pi
type `ι → E` as they are equipped with max norm. One has to work with `WithLp 2 (E×F)` and
`WithLp 2 (ι → E)`. This places quite a bit inconvenience on users in certain scenarios.
In particular, the main motivation behind this class is to make computations of `adjFDeriv` and
`gradient` easy.
-/
class InnerProductSpace' (𝕜 : Type*) (E : Type*) [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] extends Norm₂ E where
  /-- Core inner product properties. -/
  core : InnerProductSpace.Core 𝕜 E
  /-- The inner product induces the L₂ norm. -/
  norm₂_sq_eq_re_inner : ∀ x : E, norm₂ x ^ 2 = re (core.inner x x)
  /-- Norm induced by inner product is topologically equivalent to the given norm on E. -/
  inner_top_equiv_norm :
    ∃ c d : ℝ,
      0 < c ∧
        0 < d ∧ ∀ x : E, (c • ‖x‖ ^ 2 ≤ re (core.inner x x)) ∧ (re (core.inner x x) ≤ d • ‖x‖ ^ 2)


-- @@ L83-83 verbatim
section BasicInstances


-- @@ L85-85 verbatim
variable {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]


-- @@ L87-87 verbatim
instance [inst : InnerProductSpace' 𝕜 E] : InnerProductSpace.Core 𝕜 E := inst.core


-- @@ L89-89 verbatim
instance [inst : InnerProductSpace' 𝕜 E] : Inner 𝕜 E := inst.core.toInner


-- @@ L91-98 verbatim
instance {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [inst : InnerProductSpace 𝕜 E] :
    InnerProductSpace' 𝕜 E where
  norm₂ x := ‖x‖
  core := inst.toCore
  norm₂_sq_eq_re_inner := norm_sq_eq_re_inner
  inner_top_equiv_norm := by
    use 1; use 1
    simp


-- @@ L100-100 verbatim
end BasicInstances


-- @@ L102-102 verbatim
section InnerProductSpace'


-- @@ L104-108 verbatim
variable
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [hE : InnerProductSpace' 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [InnerProductSpace' 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [InnerProductSpace' 𝕜 G]


-- @@ L110-110 verbatim
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y


-- @@ L112-112 verbatim
local postfix:90 "†" => starRingEnd _


-- @@ L114-114 verbatim
namespace InnerProductSpace'

-- @@ L115-119 verbatim
/-!

## B. Deriving the inner product structure on `WithLp 2 E` from `InnerProductSpace' 𝕜 E`

-/


-- @@ L121-124 verbatim
/-- Attach L₂ norm to `WithLp 2 E` -/
noncomputable
scoped instance toNormWithL2 : Norm (WithLp 2 E) where
  norm x := √ (RCLike.re ⟪WithLp.equiv 2 E x, WithLp.equiv 2 E x⟫)


-- @@ L126-129 verbatim
/-- Attach inner product to `WithLp 2 E` -/
noncomputable
scoped instance toInnerWithL2 : Inner 𝕜 (WithLp 2 E) where
  inner x y := ⟪WithLp.equiv 2 E x, WithLp.equiv 2 E y⟫


-- @@ L131-144 verbatim
/-- Attach normed group structure to `WithLp 2 E` with L₂ norm. -/
noncomputable
scoped instance toNormedAddCommGroupWitL2 : NormedAddCommGroup (WithLp 2 E) :=
  let core : InnerProductSpace.Core (𝕜:=𝕜) (F:=E) := by infer_instance
  {
  dist_self x := core.toNormedAddCommGroup.dist_self (WithLp.equiv 2 E x)
  dist_comm x y := core.toNormedAddCommGroup.dist_comm (WithLp.equiv 2 E x) (WithLp.equiv 2 E y)
  dist_triangle x y z := core.toNormedAddCommGroup.dist_triangle (WithLp.equiv 2 E x)
    (WithLp.equiv 2 E y) (WithLp.ofLp z)
  eq_of_dist_eq_zero {x y} := by
    intro h
    simpa [-WithLp.equiv_apply] using core.toNormedAddCommGroup.eq_of_dist_eq_zero
      (x:= WithLp.equiv 2 E x) (y:= WithLp.equiv 2 E y) h
  }


-- @@ L146-149 verbatim
lemma norm_withLp2_eq_norm2 (x : WithLp 2 E) :
    ‖x‖ = |norm₂ (WithLp.equiv 2 E x)| := by
  rw [show ‖x‖ = √ (RCLike.re ⟪WithLp.equiv 2 E x, WithLp.equiv 2 E x⟫) from rfl,
    ← norm₂_sq_eq_re_inner (𝕜 := 𝕜) (WithLp.equiv 2 E x), Real.sqrt_sq_eq_abs]


-- @@ L151-157 verbatim
/-- Attach normed space structure to `WithLp 2 E` with L₂ norm. -/
noncomputable
scoped instance toNormedSpaceWithL2 : NormedSpace 𝕜 (WithLp 2 E) where
  norm_smul_le := by
    let core : PreInnerProductSpace.Core (𝕜:=𝕜) (F:=E) := by infer_instance
    intro a x
    apply (InnerProductSpace.Core.toNormedSpace (c := core)).norm_smul_le


-- @@ L159-165 verbatim
/-- Attach inner product space structure to `WithLp 2 E`. -/
noncomputable
instance toInnerProductSpaceWithL2 : InnerProductSpace 𝕜 (WithLp 2 E) where
  norm_sq_eq_re_inner := by intros; simp [norm, Real.sq_sqrt,hE.core.re_inner_nonneg]; rfl
  conj_inner_symm x y := hE.core.conj_inner_symm (WithLp.equiv 2 E x) (WithLp.equiv 2 E y)
  add_left x y z := hE.core.add_left _ _ _
  smul_left x y := hE.core.smul_left _ _


-- @@ L167-187 verbatim
variable (𝕜) in
/-- Continuous linear map from `E` to `WithLp 2 E`.

This map is continuous because we require topological equivalence between `‖·‖` and `‖·‖₂`. -/
noncomputable
def toL2 : E →L[𝕜] WithLp 2 E where
  toFun := (WithLp.equiv 2 _).symm
  map_add' := by simp
  map_smul' := by simp
  cont := by
    apply IsBoundedLinearMap.continuous (𝕜:=𝕜)
    constructor
    · constructor <;> simp
    · obtain ⟨c,d,hc,hd,h⟩ := InnerProductSpace'.inner_top_equiv_norm (𝕜:=𝕜) (E:=E)
      use √d
      constructor
      · apply Real.sqrt_pos.2 hd
      · intro x
        have h := Real.sqrt_le_sqrt (h x).2
        simp [smul_eq_mul] at h
        exact h


-- @@ L189-216 verbatim
variable (𝕜) in
/-- Continuous linear map from `WithLp 2 E` to `E`.

This map is continuous because we require topological equivalence between `‖·‖` and `‖·‖₂`.
-/
noncomputable
def fromL2 : WithLp 2 E →L[𝕜] E where
  toFun := (WithLp.equiv 2 _)
  map_add' := by simp
  map_smul' := by simp
  cont := by
    apply IsBoundedLinearMap.continuous (𝕜:=𝕜)
    constructor
    · constructor <;> simp
    · obtain ⟨c,d,hc,hd,h⟩ := InnerProductSpace'.inner_top_equiv_norm (𝕜:=𝕜) (E:=E)
      use (√c)⁻¹
      have hc : 0 < √c := Real.sqrt_pos.2 hc
      constructor
      · apply inv_pos.2 hc
      · intro x
        have h := Real.sqrt_le_sqrt (h ((WithLp.equiv 2 E) x)).1
        simp [smul_eq_mul] at h
        apply (le_inv_mul_iff₀' hc).2
        apply le_of_eq_of_le (b :=  √c * ‖x.ofLp‖ )
        · simp [WithLp.equiv_apply]
          ring
        · apply h.trans
          rfl


-- @@ L218-218 verbatim
lemma fromL2_inner_left (x : WithLp 2 E) (y : E) : ⟪fromL2 𝕜 x, y⟫ = ⟪x, toL2 𝕜 y⟫ := rfl


-- @@ L220-221 verbatim
lemma ofLp_inner_left (x : E) (y : WithLp 2 E) : ⟪WithLp.ofLp y, x⟫ = ⟪y, WithLp.toLp 2 x⟫ :=
  fromL2_inner_left y x


-- @@ L223-223 verbatim
lemma toL2_inner_left (x : E) (y : WithLp 2 E) : ⟪toL2 𝕜 x, y⟫ = ⟪x, fromL2 𝕜 y⟫ := rfl


-- @@ L225-226 verbatim
lemma toLp_inner_left (x : WithLp 2 E) (y : E) : ⟪WithLp.toLp 2 y, x⟫ = ⟪y, WithLp.ofLp x⟫ :=
  toL2_inner_left y x


-- @@ L228-229 verbatim
@[simp]
lemma toL2_fromL2 (x : WithLp 2 E) : toL2 𝕜 (fromL2 𝕜 x) = x := rfl

-- @@ L230-231 verbatim
@[simp]
lemma fromL2_toL2 (x : E) : fromL2 𝕜 (toL2 𝕜 x) = x := rfl


-- @@ L233-244 verbatim
variable (𝕜 E) in
/-- Continuous linear equivalence between `WithLp 2 E` and `E` under `InnerProductSpace' 𝕜 E`. -/
noncomputable
def equivL2 : (WithLp 2 E) ≃L[𝕜] E where
  toFun := fromL2 𝕜
  invFun := toL2 𝕜
  map_add' := (fromL2 𝕜).1.1.2
  map_smul' := (fromL2 𝕜).1.2
  left_inv := by intro _; rfl
  right_inv := by intro _; rfl
  continuous_toFun := (fromL2 𝕜).2
  continuous_invFun := (toL2 𝕜).2


-- @@ L246-250 verbatim
instance [CompleteSpace E] : CompleteSpace (WithLp 2 E) := by
  have e := (equivL2 𝕜 E)
  have he := ContinuousLinearEquiv.isUniformEmbedding e
  apply (completeSpace_congr (α:=WithLp 2 E) (β:=E) (e:=e) he).2
  infer_instance


-- @@ L252-252 verbatim
end InnerProductSpace'


-- @@ L254-254 verbatim
open InnerProductSpace'


-- @@ L256-262 verbatim
variable (𝕜) in

/-!

## C. Basic properties of the inner product

-/


-- @@ L264-266 verbatim
lemma ext_inner_left' {x y : E} (h : ∀ v, ⟪v, x⟫ = ⟪v, y⟫) : x = y :=
  (WithLp.equiv 2 E).symm.injective <| ext_inner_left (E := WithLp 2 E) 𝕜 <| by
  simpa [← ofLp_inner_left] using fun v => h (WithLp.ofLp v)


-- @@ L268-271 verbatim
variable (𝕜) in
lemma ext_inner_right' {x y : E} (h : ∀ v, ⟪x, v⟫ = ⟪y, v⟫) : x = y :=
  (WithLp.equiv 2 E).symm.injective <| ext_inner_right (E := WithLp 2 E) 𝕜 <|
    fun v => h (WithLp.ofLp v)


-- @@ L273-275 verbatim
@[simp]
lemma inner_conj_symm' (x y : E) : ⟪y, x⟫† = ⟪x, y⟫ :=
  inner_conj_symm (E:=WithLp 2 E) _ _


-- @@ L277-278 verbatim
lemma inner_smul_left' (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪x, y⟫ :=
  inner_smul_left (E:=WithLp 2 E) _ _ r


-- @@ L280-281 verbatim
lemma inner_smul_right' (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * ⟪x, y⟫ :=
  inner_smul_right (E:=WithLp 2 E) _ _ r


-- @@ L283-285 verbatim
@[simp]
lemma inner_zero_left' (x : E) : ⟪0, x⟫ = 0 :=
  inner_zero_left (E:=WithLp 2 E) _


-- @@ L287-289 verbatim
@[simp]
lemma inner_zero_right' (x : E) : ⟪x, 0⟫ = 0 :=
  inner_zero_right (E:=WithLp 2 E) _


-- @@ L291-292 verbatim
lemma inner_add_left' (x y z : E) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫ :=
  inner_add_left (E:=WithLp 2 E) _ _ _


-- @@ L294-295 verbatim
lemma inner_add_right' (x y z : E) : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫ :=
  inner_add_right (E:=WithLp 2 E) _ _ _


-- @@ L297-298 verbatim
lemma inner_sub_left' (x y z : E) : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫ :=
  inner_sub_left (E:=WithLp 2 E) _ _ _


-- @@ L300-301 verbatim
lemma inner_sub_right' (x y z : E) : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫ :=
  inner_sub_right (E:=WithLp 2 E) _ _ _


-- @@ L303-305 verbatim
@[simp]
lemma inner_neg_left' (x y : E) : ⟪-x, y⟫ = -⟪x, y⟫ :=
  inner_neg_left (E:=WithLp 2 E) _ _


-- @@ L307-309 verbatim
@[simp]
lemma inner_neg_right' (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫ :=
  inner_neg_right (E:=WithLp 2 E) _ _


-- @@ L311-314 verbatim
@[simp]
lemma inner_self_eq_zero' {x : E} : ⟪x, x⟫ = 0 ↔ x = 0 := by
  rw [show (⟪x, x⟫ : 𝕜) = inner 𝕜 (toL2 𝕜 x) (toL2 𝕜 x) from rfl, inner_self_eq_zero,
      map_eq_zero_iff _ (Function.LeftInverse.injective fromL2_toL2)]


-- @@ L316-319 verbatim
@[simp]
lemma inner_sum'{ι : Type*} [Fintype ι] (x : E) (g : ι → E) :
    ⟪x, ∑ i, g i⟫ = ∑ i, ⟪x, g i⟫ :=
  map_sum (AddMonoidHom.mk' (fun y => ⟪x, y⟫) (inner_add_right' x)) g Finset.univ


-- @@ L321-325 verbatim
@[fun_prop]
lemma Continuous.inner' {α} [TopologicalSpace α] (f g : α → E)
    (hf : Continuous f) (hg : Continuous g) : Continuous (fun a => ⟪f a, g a⟫) :=
  Continuous.inner (𝕜 := 𝕜) (E := WithLp 2 E) (f := fun x => toL2 𝕜 (f x))
    (g := fun x => toL2 𝕜 (g x)) (by fun_prop) (by fun_prop)


-- @@ L327-327 verbatim
section Real


-- @@ L329-331 verbatim
variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [InnerProductSpace' ℝ F]


-- @@ L333-333 verbatim
local notation "⟪" x ", " y "⟫" => inner ℝ x y


-- @@ L335-336 verbatim
lemma real_inner_self_nonneg' {x : F} : 0 ≤ re (⟪x, x⟫) :=
  real_inner_self_nonneg (F:=WithLp 2 F)


-- @@ L338-339 verbatim
lemma real_inner_comm' (x y : F) : ⟪y, x⟫ = ⟪x, y⟫ :=
  real_inner_comm (F:=WithLp 2 F) _ _


-- @@ L341-346 verbatim
@[fun_prop]
lemma ContDiffAt.inner' {f g : E → F} {x : E}
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x) :
    ContDiffAt ℝ n (fun x => ⟪f x, g x⟫) x :=
  ContDiffAt.inner ℝ (f := fun x => toL2 ℝ (f x)) (g := fun x => toL2 ℝ (g x))
    (by fun_prop) (by fun_prop)


-- @@ L348-353 verbatim
@[fun_prop]
lemma ContDiff.inner' {f g : E → F}
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (fun x => ⟪f x, g x⟫) :=
  ContDiff.inner ℝ (f := fun x => toL2 ℝ (f x)) (g := fun x => toL2 ℝ (g x))
    (by fun_prop) (by fun_prop)


-- @@ L355-355 verbatim
end Real


-- @@ L357-357 verbatim
end InnerProductSpace'


-- @@ L359-359 verbatim
section Constructions


-- @@ L361-365 verbatim
variable
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [InnerProductSpace' 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [InnerProductSpace' 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [InnerProductSpace' 𝕜 G]


-- @@ L367-367 verbatim
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y


-- @@ L369-373 verbatim
/-- Inner product on product types `E×F` defined as `⟪x,y⟫ = ⟪x.fst,y.fst⟫ + ⟪x.snd,y.snd⟫`.

This is just local instance as it is superseded by the following instance for
`InnerProductSpace'`. -/
local instance : Inner 𝕜 (E×F) := ⟨fun (x,y) (x',y') => ⟪x,x'⟫ + ⟪y,y'⟫⟩


-- @@ L375-376 verbatim
@[simp]
lemma prod_inner_apply' (x y : (E × F)) : ⟪x, y⟫ = ⟪x.fst, y.fst⟫ + ⟪x.snd, y.snd⟫ := rfl


-- @@ L378-442 verbatim
open InnerProductSpace' in
set_option backward.isDefEq.respectTransparency false in
noncomputable
instance : InnerProductSpace' 𝕜 (E × F) where
  norm₂ x := (WithLp.instProdNormedAddCommGroup 2 (WithLp 2 E) (WithLp 2 F)).toNorm.norm
    (WithLp.toLp 2 (WithLp.toLp 2 x.1, WithLp.toLp 2 x.2))
  core :=
    let _ := WithLp.instProdNormedAddCommGroup 2 (WithLp 2 E) (WithLp 2 F)
    let inst := (WithLp.instProdInnerProductSpace (𝕜:=𝕜) (E := WithLp 2 E) (F := WithLp 2 F)).toCore
  {
    inner x y := inst.inner (WithLp.toLp 2 (WithLp.toLp 2 x.1, WithLp.toLp 2 x.2))
        (WithLp.toLp 2 (WithLp.toLp 2 y.1, WithLp.toLp 2 y.2))
    conj_inner_symm x y := inst.conj_inner_symm _ _
    re_inner_nonneg x := inst.re_inner_nonneg _
    add_left x y z := inst.add_left (WithLp.toLp 2 (WithLp.toLp 2 x.1, WithLp.toLp 2 x.2))
        (WithLp.toLp 2 (WithLp.toLp 2 y.1, WithLp.toLp 2 y.2))
        (WithLp.toLp 2 (WithLp.toLp 2 z.1, WithLp.toLp 2 z.2))
    smul_left x y r := inst.smul_left (WithLp.toLp 2 (WithLp.toLp 2 x.1, WithLp.toLp 2 x.2))
        (WithLp.toLp 2 (WithLp.toLp 2 y.1, WithLp.toLp 2 y.2)) r
    definite x := by
      intro h
      have h1 := inst.definite (WithLp.toLp 2 (WithLp.toLp 2 x.1, WithLp.toLp 2 x.2)) h
      simp at h1
      exact Prod.ext_iff.mpr h1
  }

  norm₂_sq_eq_re_inner := by
    intro (x,y)
    have : 0 ≤ re ⟪x,x⟫ := PreInnerProductSpace.Core.re_inner_nonneg (𝕜:=𝕜) (F:=E) _ x
    have : 0 ≤ re ⟪y,y⟫ := PreInnerProductSpace.Core.re_inner_nonneg (𝕜:=𝕜) (F:=F) _ y
    simp only [norm, OfNat.ofNat_ne_zero, ↓reduceDIte, ENNReal.ofNat_ne_top, ↓reduceIte,
      WithLp.toLp_fst, WithLp.equiv_apply, ENNReal.toReal_ofNat, Real.rpow_ofNat, WithLp.toLp_snd,
      one_div, prod_inner_apply', map_add]
    repeat rw [Real.sq_sqrt (by assumption)]
    norm_num
    rw[← Real.rpow_mul_natCast (by linarith)]
    simp
  inner_top_equiv_norm := by
    obtain ⟨c₁,d₁,hc₁,hd₁,h₁⟩ := inner_top_equiv_norm (𝕜:=𝕜) (E:=E)
    have h₁₁ := fun x => (h₁ x).1
    have h₁₂ := fun x => (h₁ x).2
    obtain ⟨c₂,d₂,hc2,hd₂,h₂⟩ := inner_top_equiv_norm (𝕜:=𝕜) (E:=F)
    have h₂₁ := fun x => (h₂ x).1
    have h₂₂ := fun x => (h₂ x).2
    use min c₁ c₂; use 2 * max d₁ d₂
    constructor
    · positivity
    constructor
    · positivity
    · intro (x,y)
      have : 0 ≤ re ⟪y, y⟫ := by apply PreInnerProductSpace.Core.re_inner_nonneg
      have : 0 ≤ re ⟪x, x⟫ := by apply PreInnerProductSpace.Core.re_inner_nonneg
      simp only [Prod.norm_mk, smul_eq_mul, prod_inner_apply', map_add]
      simp only [smul_eq_mul] at h₁₁ h₁₂ h₂₁ h₂₂
      refine ⟨?_, ?_⟩
      · rcases le_total ‖x‖ ‖y‖ with h | h
        · rw [max_eq_right h]
          nlinarith [h₂₁ y, min_le_right c₁ c₂, sq_nonneg ‖y‖]
        · rw [max_eq_left h]
          nlinarith [h₁₁ x, min_le_left c₁ c₂, sq_nonneg ‖x‖]
      · rcases le_total (re ⟪x,x⟫) (re ⟪y,y⟫) with h | h
        · nlinarith [h₂₂ y, le_max_right d₁ d₂, sq_nonneg ‖y‖, norm_nonneg y,
            pow_le_pow_left₀ (norm_nonneg y) (le_max_right ‖x‖ ‖y‖) 2]
        · nlinarith [h₁₂ x, le_max_left d₁ d₂, sq_nonneg ‖x‖, norm_nonneg x,
            pow_le_pow_left₀ (norm_nonneg x) (le_max_left ‖x‖ ‖y‖) 2]


-- @@ L444-539 verbatim
open InnerProductSpace' in
noncomputable
instance {ι : Type*} [Fintype ι] : InnerProductSpace' 𝕜 (ι → E) where
  norm₂ x := (PiLp.seminormedAddCommGroup 2 (fun _ : ι => (WithLp 2 E))).toNorm.norm
    (WithLp.toLp 2 (fun i => WithLp.toLp 2 (x i)))
  core :=
    let _ := PiLp.normedAddCommGroup 2 (fun _ : ι => (WithLp 2 E))
    let inst := (PiLp.innerProductSpace (𝕜:=𝕜) (fun _ : ι => (WithLp 2 E)))
    {
    inner x y := inst.inner (WithLp.toLp 2 (fun i => WithLp.toLp 2 (x i)))
        (WithLp.toLp 2 (fun i => WithLp.toLp 2 (y i)))
    conj_inner_symm x y := inst.conj_inner_symm _ _
    re_inner_nonneg x := inst.toCore.re_inner_nonneg (WithLp.toLp 2 (fun i => WithLp.toLp 2 (x i)))
    add_left x y z := inst.add_left
      (WithLp.toLp 2 (fun i => WithLp.toLp 2 (x i)))
      (WithLp.toLp 2 (fun i => WithLp.toLp 2 (y i)))
      (WithLp.toLp 2 (fun i => WithLp.toLp 2 (z i)))
    smul_left x y r := inst.smul_left
      (WithLp.toLp 2 (fun i => WithLp.toLp 2 (x i)))
      (WithLp.toLp 2 (fun i => WithLp.toLp 2 (y i))) r
    definite x := by
      intro h
      have h1 := inst.toCore.definite (WithLp.toLp 2 (fun i => WithLp.toLp 2 (x i))) h
      simp at h1
      funext i
      simpa using congrFun h1 i
  }
  norm₂_sq_eq_re_inner := by
    intro x
    simp only [norm, OfNat.ofNat_ne_zero, ↓reduceIte, ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat,
      Real.rpow_two, one_div]
    conv_rhs => rw [inner]
    simp only [WithLp.equiv_apply, PiLp.inner_apply, inner_self_eq_norm_sq_to_K, map_sum,
      re_ofReal_pow]
    rw [← Real.rpow_two, ← Real.rpow_mul]
    swap
    · exact Finset.sum_nonneg fun i _ => sq_nonneg _
    simp only [isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      IsUnit.inv_mul_cancel, Real.rpow_one]
    rfl
  inner_top_equiv_norm := by
    rename_i i1 i2 i3 i4 i5 i6 i7 i8
    by_cases hnEmpty : Nonempty ι
    · obtain ⟨c, d, c_pos, d_pos, h⟩ := i1.inner_top_equiv_norm
      use c, Fintype.card ι * d
      simp_all
      constructor
      · positivity
      intro x
      obtain ⟨i, hi⟩ : ∃ i, ‖x‖ = ‖x i‖ := by
          simp [norm]
          obtain ⟨i,_, hi⟩:= Finset.exists_mem_eq_sup (Finset.univ : Finset ι)
            (Finset.univ_nonempty_iff.mpr hnEmpty) (fun i => ‖x i‖₊)
          rw [hi]
          use i
          simp
      have hj : ∀ j, ‖x j‖ ≤ ‖x i‖ := by
        rw [← hi]
        exact fun j => norm_le_pi_norm x j
      rw [hi]
      constructor
      · apply le_trans (h (x i)).1
        have h1 := Finset.sum_le_univ_sum_of_nonneg
          (f := fun i => re (@inner 𝕜 (WithLp 2 E) toInnerProductSpaceWithL2.2
            (WithLp.toLp 2 (x i)) (WithLp.toLp 2 (x i))))
          (s := {i}) (fun _ => InnerProductSpace.Core.inner_self_nonneg)
        apply le_trans _ (le_trans h1 _)
        · simp [norm]
          exact le_of_eq (Real.sq_sqrt InnerProductSpace.Core.inner_self_nonneg).symm
        · apply le_of_eq
          conv_rhs => rw [inner]
          simp [PiLp.inner_apply]
      · have h2 := (h (x i)).2
        trans ∑ j, re ⟪x j, x j⟫
        · apply le_of_eq
          conv_lhs => rw [inner]
          simp only [PiLp.inner_apply, inner_self_eq_norm_sq_to_K, map_sum, re_ofReal_pow]
          congr
          funext j
          exact Real.sq_sqrt InnerProductSpace.Core.inner_self_nonneg
        trans ∑ j, d * ‖x j‖ ^ 2
        · refine Finset.sum_le_sum ?_
          intro j _
          exact (h (x j)).2
        trans (Fintype.card ι) • (d * ‖x i‖ ^ 2)
        swap
        · apply le_of_eq
          ring
        apply Finset.sum_le_card_nsmul
        intro j _
        refine mul_le_mul_of_nonneg (by simp) ?_ (by positivity) (by positivity)
        exact (sq_le_sq₀ (norm_nonneg (x j)) (norm_nonneg (x i))).mpr (hj j)
    · rw [not_nonempty_iff] at hnEmpty
      refine ⟨1, 1, zero_lt_one, zero_lt_one, fun x => ?_⟩
      rw [Subsingleton.elim x 0]
      simp [norm, inner]


-- @@ L541-541 verbatim
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [hE : InnerProductSpace' ℝ E]

-- @@ L542-542 verbatim
local notation "⟪" x ", " y "⟫" => inner ℝ x y

-- @@ L543-543 verbatim
open InnerProductSpace'

-- @@ L544-575 expanded
lemma _root_.isBoundedBilinearMap_inner' : IsBoundedBilinearMap ℝ fun p : E × E => ⟪p.1, p.2⟫
    where
  add_left := inner_add_left'
  smul_left := fun r x y => by simpa using inner_smul_left' x y r
  add_right := inner_add_right'
  smul_right := fun r x y => by simpa using inner_smul_right' x y r
  bound := by
    obtain ⟨c, d, hc, hd, h⟩ := hE.inner_top_equiv_norm
    use d
    simp_all
    intro x y
    trans |norm₂ x| * |norm₂ y|
    · refine
        (norm_inner_le_norm (𝕜 := ℝ) (E := WithLp 2 E) (WithLp.toLp 2 x) (WithLp.toLp 2 y)).trans ?_
      simp [norm_withLp2_eq_norm2]
    · have key (z : E) : |norm₂ z| ≤ √d * ‖z‖ :=
        by
        apply le_of_sq_le_sq
        · simp [@mul_pow]
          rw [norm₂_sq_eq_re_inner (𝕜 := ℝ)]
          simp only [re_to_real]
          rw [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ d)]
          exact (h z).2
        · positivity
      have h1 := key x
      have h2 := key y
      trans (√d * ‖x‖) * (√d * ‖y‖)
      · exact mul_le_mul_of_nonneg h1 h2 (by positivity) (by positivity)
      · apply le_of_eq
        rw [mul_mul_mul_comm, Real.mul_self_sqrt (by linarith : (0 : ℝ) ≤ d)]
        ring


-- @@ L577-577 verbatim
end Constructions
