/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic

-- @@ L9-18 verbatim
/-!
# Pi Tensor Products

The purpose of this file is to define some results about Pi tensor products not currently
in Mathlib.

At some point these should either be up-streamed to Mathlib or replaced with definitions already
in Mathlib.

-/


-- @@ L20-20 verbatim
@[expose] public section

-- @@ L21-21 verbatim
namespace Physlib.PiTensorProduct


-- @@ L23-23 verbatim
noncomputable section tmulEquiv


-- @@ L25-30 verbatim
variable {R ι1 ι2 ι3 M N : Type} [CommSemiring R]
  {s1 : ι1 → Type} [inst1 : (i : ι1) → AddCommMonoid (s1 i)] [inst1' : (i : ι1) → Module R (s1 i)]
  {s2 : ι2 → Type} [inst2 : (i : ι2) → AddCommMonoid (s2 i)] [inst2' : (i : ι2) → Module R (s2 i)]
  {s3 : ι3 → Type} [inst3 : (i : ι3) → AddCommMonoid (s3 i)] [inst3' : (i : ι3) → Module R (s3 i)]
  [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]


-- @@ L32-32 verbatim
open TensorProduct


-- @@ L34-38 verbatim
/-!

## induction principals for pi tensor products

-/

-- @@ L39-39 verbatim
attribute [local ext] TensorProduct.ext


-- @@ L41-45 verbatim
lemma induction_tmul {f g : ((⨂[R] i : ι1, s1 i) ⊗[R] (⨂[R] i : ι2, s2 i)) →ₗ[R] M}
    (h : ∀ p q, f (PiTensorProduct.tprod R p ⊗ₜ[R] PiTensorProduct.tprod R q)
    = g (PiTensorProduct.tprod R p ⊗ₜ[R] PiTensorProduct.tprod R q)) : f = g := by
  ext
  exact h _ _


-- @@ L47-54 verbatim
lemma induction_assoc
    {f g : ((⨂[R] i : ι1, s1 i) ⊗[R] (⨂[R] i : ι2, s2 i) ⊗[R] (⨂[R] i : ι3, s3 i)) →ₗ[R] M}
    (h : ∀ p q m, f (PiTensorProduct.tprod R p ⊗ₜ[R]
    PiTensorProduct.tprod R q ⊗ₜ[R] PiTensorProduct.tprod R m)
    = g (PiTensorProduct.tprod R p ⊗ₜ[R] PiTensorProduct.tprod R q
    ⊗ₜ[R] PiTensorProduct.tprod R m)) : f = g := by
  ext
  exact h _ _ _


-- @@ L56-62 verbatim
lemma induction_assoc'
    {f g : (((⨂[R] i : ι1, s1 i) ⊗[R] (⨂[R] i : ι2, s2 i)) ⊗[R] (⨂[R] i : ι3, s3 i)) →ₗ[R] M}
    (h : ∀ p q m, f ((PiTensorProduct.tprod R p ⊗ₜ[R] PiTensorProduct.tprod R q) ⊗ₜ[R]
    PiTensorProduct.tprod R m) = g ((PiTensorProduct.tprod R p ⊗ₜ[R] PiTensorProduct.tprod R q)
    ⊗ₜ[R] PiTensorProduct.tprod R m)) : f = g := by
  ext
  exact h _ _ _


-- @@ L64-69 verbatim
lemma induction_tmul_mod
    {f g : ((⨂[R] i : ι1, s1 i) ⊗[R] N) →ₗ[R] M}
    (h : ∀ p m, f (PiTensorProduct.tprod R p ⊗ₜ[R] m) = g (PiTensorProduct.tprod R p ⊗ₜ[R] m)) :
    f = g := by
  ext
  exact h _ _


-- @@ L71-76 verbatim
lemma induction_mod_tmul
    {f g : (N ⊗[R] (⨂[R] i : ι1, s1 i)) →ₗ[R] M}
    (h : ∀ m p, f (m ⊗ₜ[R] PiTensorProduct.tprod R p) = g (m ⊗ₜ[R] PiTensorProduct.tprod R p)) :
    f = g := by
  ext
  exact h _ _


-- @@ L78-81 verbatim
/-!

# Dependent type version of PiTensorProduct.tmulEquiv
-/


-- @@ L83-88 verbatim
/-- Given two maps `s1` and `s2` whose targets carry an instance of an additive commutative
  monoid, the target of the sum of these two maps also carry an instance thereof. -/
instance : (i : ι1 ⊕ ι2) → AddCommMonoid ((fun i => Sum.elim s1 s2 i) i) := fun i =>
  match i with
  | Sum.inl i => inst1 i
  | Sum.inr i => inst2 i


-- @@ L90-95 verbatim
/-- Given two maps `s1` and `s2` whose targets carry an instance of a module over `R`,
  the target of the sum of these two maps also carry an instance thereof. -/
instance : (i : ι1 ⊕ ι2) → Module R ((fun i => Sum.elim s1 s2 i) i) := fun i =>
  match i with
  | Sum.inl i => inst1' i
  | Sum.inr i => inst2' i


-- @@ L97-99 verbatim
/-- Takes a map `(i : ι1 ⊕ ι2) → Sum.elim s1 s2 i` to the underlying map `(i : ι1) → s1 i `. -/
def pureInl (f : (i : ι1 ⊕ ι2) → Sum.elim s1 s2 i) : (i : ι1) → s1 i :=
  fun i => f (Sum.inl i)


-- @@ L101-103 verbatim
/-- Takes a map `(i : ι1 ⊕ ι2) → Sum.elim s1 s2 i` to the underlying map `(i : ι2) → s2 i `. -/
def pureInr (f : (i : ι1 ⊕ ι2) → Sum.elim s1 s2 i) : (i : ι2) → s2 i :=
  fun i => f (Sum.inr i)


-- @@ L105-105 verbatim
section


-- @@ L107-107 verbatim
variable [DecidableEq (ι1 ⊕ ι2)]

-- @@ L108-108 verbatim
omit inst1 inst2


-- @@ L110-120 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma pureInl_update_left [DecidableEq ι1] (f : (i : ι1 ⊕ ι2) → Sum.elim s1 s2 i) (x : ι1)
    (v1 : s1 x) : pureInl (Function.update f (Sum.inl x) v1) =
    Function.update (pureInl f) x v1 := by
  funext y
  simp only [pureInl, Function.update, Sum.inl.injEq, Sum.elim_inl]
  split
  · rename_i h
    subst h
    rfl
  · rfl


-- @@ L122-127 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma pureInr_update_left (f : (i : ι1 ⊕ ι2) → Sum.elim s1 s2 i) (x : ι1)
    (v2 : s1 x) :
    pureInr (Function.update f (Sum.inl x) v2) = (pureInr f) := by
  funext y
  simp [pureInr, Function.update]


-- @@ L129-139 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma pureInr_update_right [DecidableEq ι2] (f : (i : ι1 ⊕ ι2) → Sum.elim s1 s2 i) (x : ι2)
    (v2 : s2 x) : pureInr (Function.update f (Sum.inr x) v2) =
    Function.update (pureInr f) x v2 := by
  funext y
  simp only [pureInr, Function.update, Sum.inr.injEq, Sum.elim_inr]
  split
  · rename_i h
    subst h
    rfl
  · rfl


-- @@ L141-146 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma pureInl_update_right (f : (i : ι1 ⊕ ι2) → Sum.elim s1 s2 i) (x : ι2)
    (v1 : s2 x) :
    pureInl (Function.update f (Sum.inr x) v1) = (pureInl f) := by
  funext y
  simp [pureInl, Function.update]


-- @@ L148-148 verbatim
end


-- @@ L150-182 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The multilinear map from `(Sum.elim s1 s2)` to `((⨂[R] i : ι1, s1 i) ⊗[R] ⨂[R] i : ι2, s2 i)`
  defined by splitting elements of `(Sum.elim s1 s2)` into two parts. -/
def domCoprod :
    MultilinearMap R (Sum.elim s1 s2) ((⨂[R] i : ι1, s1 i) ⊗[R] (⨂[R] i : ι2, s2 i)) where
  toFun f := (PiTensorProduct.tprod R (pureInl f)) ⊗ₜ
    (PiTensorProduct.tprod R (pureInr f))
  map_update_add' f xy v1 v2 := by
    have : DecidableEq (ι1 ⊕ ι2) := inferInstance
    have : DecidableEq ι1 :=
      @Function.Injective.decidableEq ι1 (ι1 ⊕ ι2) Sum.inl _ Sum.inl_injective
    have : DecidableEq ι2 :=
      @Function.Injective.decidableEq ι2 (ι1 ⊕ ι2) Sum.inr _ Sum.inr_injective
    match xy with
    | Sum.inl xy =>
      simp only [Sum.elim_inl, pureInl_update_left, MultilinearMap.map_update_add,
        pureInr_update_left, ← add_tmul]
    | Sum.inr xy =>
      simp only [Sum.elim_inr, pureInl_update_right, pureInr_update_right,
        MultilinearMap.map_update_add, ← tmul_add]
  map_update_smul' f xy r p := by
    have : DecidableEq (ι1 ⊕ ι2) := inferInstance
    have : DecidableEq ι1 :=
      @Function.Injective.decidableEq ι1 (ι1 ⊕ ι2) Sum.inl _ Sum.inl_injective
    have : DecidableEq ι2 :=
      @Function.Injective.decidableEq ι2 (ι1 ⊕ ι2) Sum.inr _ Sum.inr_injective
    match xy with
    | Sum.inl x =>
      simp only [Sum.elim_inl, pureInl_update_left, MultilinearMap.map_update_smul,
        pureInr_update_left, smul_tmul, tmul_smul]
    | Sum.inr y =>
      simp only [Sum.elim_inr, pureInl_update_right, pureInr_update_right,
        MultilinearMap.map_update_smul, tmul_smul]


-- @@ L184-186 verbatim
/-- Expand `PiTensorProduct` on sums into a `TensorProduct` of two factors. -/
def tmulSymm : (⨂[R] i : ι1 ⊕ ι2, (Sum.elim s1 s2) i) →ₗ[R]
    ((⨂[R] i : ι1, s1 i) ⊗[R] (⨂[R] i : ι2, s2 i)) := PiTensorProduct.lift domCoprod


-- @@ L188-194 verbatim
/-- Produces a map `(i : ι1 ⊕ ι2) → Sum.elim s1 s2 i` from a map `(i : ι1) → s1 i` and a
  map `q : (i : ι2) → s2 i`. -/
def elimPureTensor (p : (i : ι1) → s1 i) (q : (i : ι2) → s2 i) : (i : ι1 ⊕ ι2) → Sum.elim s1 s2 i :=
  fun x =>
    match x with
    | Sum.inl x => p x
    | Sum.inr x => q x


-- @@ L196-196 verbatim
section


-- @@ L198-198 verbatim
variable [DecidableEq ι1] [DecidableEq ι2]

-- @@ L199-199 verbatim
omit inst1 inst2


-- @@ L201-216 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma elimPureTensor_update_right (p : (i : ι1) → s1 i) (q : (i : ι2) → s2 i)
    (y : ι2) (r : s2 y) : elimPureTensor p (Function.update q y r) =
    Function.update (elimPureTensor p q) (Sum.inr y) r := by
  funext x
  match x with
  | Sum.inl x =>
    rfl
  | Sum.inr x =>
    change Function.update q y r x = _
    simp only [Function.update, Sum.inr.injEq, Sum.elim_inr]
    split_ifs
    · rename_i h
      subst h
      rfl
    · rfl


-- @@ L218-234 verbatim
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma elimPureTensor_update_left (p : (i : ι1) → s1 i) (q : (i : ι2) → s2 i)
    (x : ι1) (r : s1 x) : elimPureTensor (Function.update p x r) q =
    Function.update (elimPureTensor p q) (Sum.inl x) r := by
  funext y
  match y with
  | Sum.inl y =>
    change (Function.update p x r) y = _
    simp only [Function.update, Sum.inl.injEq, Sum.elim_inl]
    split_ifs
    · rename_i h
      subst h
      rfl
    · rfl
  | Sum.inr y =>
    rfl


-- @@ L236-236 verbatim
end


-- @@ L238-264 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The multilinear map valued in multilinear maps defined by combining
  `(i : ι1) → s1 i` and `q : (i : ι2) → s2 i` into a PiTensorProduct. -/
def elimPureTensorMulLin : MultilinearMap R s1
    (MultilinearMap R s2 (⨂[R] i : ι1 ⊕ ι2, (Sum.elim s1 s2) i)) where
  toFun p := {
    toFun := fun q => PiTensorProduct.tprod R (elimPureTensor p q)
    map_update_add' := fun m x v1 v2 => by
      have : DecidableEq ι2 := inferInstance
      have := Classical.decEq ι1
      simp only [elimPureTensor_update_right, MultilinearMap.map_update_add]
    map_update_smul' := fun m x r v => by
      have : DecidableEq ι2 := inferInstance
      have := Classical.decEq ι1
      simp only [elimPureTensor_update_right, MultilinearMap.map_update_smul]}
  map_update_add' p x v1 v2 := by
    have : DecidableEq ι1 := inferInstance
    have := Classical.decEq ι2
    apply MultilinearMap.ext
    intro y
    simp
  map_update_smul' p x r v := by
    have : DecidableEq ι1 := inferInstance
    have := Classical.decEq ι2
    apply MultilinearMap.ext
    intro y
    simp


-- @@ L266-273 verbatim
/-- Collapse a `TensorProduct` of `PiTensorProduct` into a `PiTensorProduct`. -/
def tmul : ((⨂[R] i : ι1, s1 i) ⊗[R] (⨂[R] i : ι2, s2 i)) →ₗ[R]
    ⨂[R] i : ι1 ⊕ ι2, (Sum.elim s1 s2) i := TensorProduct.lift {
    toFun := fun a ↦
      PiTensorProduct.lift <|
          PiTensorProduct.lift elimPureTensorMulLin a,
    map_add' := fun a b ↦ by simp
    map_smul' := fun r a ↦ by simp}


-- @@ L275-298 verbatim
/-- The equivalence formed by combining a `TensorProduct` into a `PiTensorProduct`. -/
def tmulEquiv : ((⨂[R] i : ι1, s1 i) ⊗[R] (⨂[R] i : ι2, s2 i)) ≃ₗ[R]
    ⨂[R] i : ι1 ⊕ ι2, (Sum.elim s1 s2) i :=
  LinearEquiv.ofLinearMap tmul tmulSymm
  (by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro p
    simp only [tmul, tmulSymm, domCoprod, LinearMap.compMultilinearMap_apply,
      LinearMap.coe_comp, Function.comp_apply, PiTensorProduct.lift.tprod, MultilinearMap.coe_mk,
      lift.tmul, LinearMap.coe_mk, AddHom.coe_mk]
    simp only [elimPureTensorMulLin, MultilinearMap.coe_mk, LinearMap.id_coe, id_eq]
    apply congrArg
    funext x
    match x with
    | Sum.inl x => rfl
    | Sum.inr x => rfl)
  (by
    apply induction_tmul
    intro p q
    simp only [tmulSymm, domCoprod, tmul, elimPureTensorMulLin, LinearMap.coe_comp,
      Function.comp_apply, lift.tmul, LinearMap.coe_mk, AddHom.coe_mk, PiTensorProduct.lift.tprod,
      MultilinearMap.coe_mk, LinearMap.id_coe, id_eq]
    rfl)


-- @@ L300-305 verbatim
@[simp]
lemma tmulEquiv_tmul_tprod (p : (i : ι1) → s1 i) (q : (i : ι2) → s2 i) :
    tmulEquiv ((PiTensorProduct.tprod R) p ⊗ₜ[R] (PiTensorProduct.tprod R) q) =
    (PiTensorProduct.tprod R) (elimPureTensor p q) := by
  simp only [tmulEquiv, tmul, elimPureTensorMulLin, LinearEquiv.coe_ofLinearMap, lift.tmul,
    LinearMap.coe_mk, AddHom.coe_mk, PiTensorProduct.lift.tprod, MultilinearMap.coe_mk]


-- @@ L307-307 verbatim
end tmulEquiv

-- @@ L308-308 verbatim
end Physlib.PiTensorProduct
