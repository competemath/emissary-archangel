/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Salvatore Mercuri
-/
module

public import FLT.Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
--import Mathlib.Topology.Algebra.ContinuousMonoidHom


-- @@ L14-27 verbatim
/-!

# Isomorphisms of restricted products

Restricted products of isomorphic things are isomorphic.

Restricted products of matrices/products/units are isomorphic to matrices/products/units
of the restricted product.

Restricted product over a principal filter is isomorphic to a product.

We don't allow topological isomorphisms; they have to go into TopologicalSpace because of imports.

-/


-- @@ L29-29 verbatim
@[expose] public section


-- @@ L31-31 verbatim
open RestrictedProduct


-- @@ L33-33 verbatim
section pi_congr_right


-- @@ L35-35 verbatim
variable {ι : Type*}

-- @@ L36-37 verbatim
variable {R₁ : ι → Type*} {R₂ : ι → Type*} {S₁ : ι → Type*} {S₂ : ι → Type*}
  [(i : ι) → SetLike (S₁ i) (R₁ i)] [(i : ι) → SetLike (S₂ i) (R₂ i)]

-- @@ L38-38 verbatim
variable {A₁ : (i : ι) → Set (R₁ i)} {A₂ : (i : ι) → Set (R₂ i)}

-- @@ L39-39 verbatim
variable {𝓕 : Filter ι}


-- @@ L41-51 verbatim
/-- The equivalence between restricted products on the same index, when
each factor is equivalent, with compatibility on the restricted subsets. -/
@[simps]
def Equiv.restrictedProductCongrRight (φ : (i : ι) → R₁ i ≃ R₂ i)
    (hφ : ∀ᶠ i in 𝓕, Set.BijOn (φ i) (A₁ i) (A₂ i)) :
    Πʳ i, [R₁ i, A₁ i]_[𝓕] ≃ Πʳ i, [R₂ i, A₂ i]_[𝓕] where
  toFun := map (fun i ↦ φ i) (by filter_upwards [hφ]; exact fun i ↦ Set.BijOn.mapsTo)
  invFun := map (fun i ↦ (φ i).symm)
    (by filter_upwards [hφ]; exact fun i ↦ Set.BijOn.mapsTo ∘ Set.BijOn.equiv_symm)
  left_inv x := by ext; simp
  right_inv x := by ext; simp


-- @@ L53-53 verbatim
section add_mul_equiv


-- @@ L55-56 verbatim
variable [(i : ι) → Monoid (R₁ i)] [(i : ι) → Monoid (R₂ i)]
  [(i : ι) → SubmonoidClass (S₁ i) (R₁ i)] [(i : ι) → SubmonoidClass (S₂ i) (R₂ i)]

-- @@ L57-57 verbatim
variable {A₁ : (i : ι) → S₁ i} {A₂ : (i : ι) → S₂ i}


-- @@ L59-66 verbatim
/-- The `MulEquiv` between restricted products built from `MulEquiv`s on the factors. -/
@[to_additive (attr := simps! apply) /-- The `AddEquiv` between restricted products built from
  `AddEquiv`s on the factors. -/]
def MulEquiv.restrictedProductCongrRight (φ : (i : ι) → R₁ i ≃* R₂ i)
    (hφ : ∀ᶠ i in 𝓕, Set.BijOn (φ i) (A₁ i) (A₂ i)) :
    (Πʳ i, [R₁ i, A₁ i]_[𝓕]) ≃* (Πʳ i, [R₂ i, A₂ i]_[𝓕]) where
  __ := Equiv.restrictedProductCongrRight _ hφ
  map_mul' _ _ := by ext; simp


-- @@ L68-84 verbatim
/-- The isomorphism between the units of a restricted product of monoids,
and the restricted product of the units of the monoids. -/
def MulEquiv.restrictedProductUnits {ι : Type*} {ℱ : Filter ι}
    {M : ι → Type*} [(i : ι) → Monoid (M i)]
    {S : ι → Type*} [∀ i, SetLike (S i) (M i)] [∀ i, SubmonoidClass (S i) (M i)]
    {A : Π i, S i} :
    (Πʳ i, [M i, A i]_[ℱ])ˣ ≃*
      Πʳ i, [(M i)ˣ, (Submonoid.ofClass (A i)).units]_[ℱ] where
        toFun u := ⟨fun i ↦ ⟨u.1 i, u⁻¹.1 i, congr($u.mul_inv i), congr($u.inv_mul i)⟩,
          by filter_upwards [u.val.2, u⁻¹.val.2] using fun i hi hi' ↦ ⟨hi, hi'⟩⟩
        invFun ui := ⟨⟨fun i ↦ ui i, by filter_upwards [ui.2] using fun i hi ↦ hi.1⟩,
          ⟨fun i ↦ ui⁻¹ i, by filter_upwards [ui⁻¹.2] using fun i hi ↦ hi.1⟩,
          by ext i; exact (ui i).mul_inv,
          by ext i; exact (ui i).inv_mul⟩
        left_inv u := by ext; rfl
        right_inv ui := by ext; rfl
        map_mul' u v := by ext; rfl


-- @@ L86-86 verbatim
end add_mul_equiv


-- @@ L88-88 verbatim
section ring_equiv


-- @@ L90-91 verbatim
variable [(i : ι) → Semiring (R₁ i)] [(i : ι) → Semiring (R₂ i)]
  [(i : ι) → SubsemiringClass (S₁ i) (R₁ i)] [(i : ι) → SubsemiringClass (S₂ i) (R₂ i)]

-- @@ L92-92 verbatim
variable {A₁ : (i : ι) → S₁ i} {A₂ : (i : ι) → S₂ i}


-- @@ L94-101 verbatim
/-- The ring isomorphism between restricted products on the same index, when
each factor is equivalent, with compatibility on the restricted subsets. -/
@[simps! apply]
def RingEquiv.restrictedProductCongrRight (φ : (i : ι) → R₁ i ≃+* R₂ i)
    (hφ : ∀ᶠ i in 𝓕, Set.BijOn (φ i) (A₁ i) (A₂ i)) :
    (Πʳ i, [R₁ i, A₁ i]_[𝓕]) ≃+* (Πʳ i, [R₂ i, A₂ i]_[𝓕]) where
  __ := AddEquiv.restrictedProductCongrRight (fun _ ↦ (φ _).toAddEquiv) hφ
  map_mul' _ _ := by ext; simp [AddEquiv.restrictedProductCongrRight]


-- @@ L103-103 verbatim
end ring_equiv


-- @@ L105-105 verbatim
section linear_equiv


-- @@ L107-107 verbatim
variable {T : Type*} [Semiring T]

-- @@ L108-108 verbatim
variable [(i : ι) → AddCommMonoid (R₁ i)] [(i : ι) → AddCommMonoid (R₂ i)]

-- @@ L109-109 verbatim
variable [(i : ι) → Module T (R₁ i)] [(i : ι) → Module T (R₂ i)]

-- @@ L110-110 verbatim
variable [(i : ι) → AddSubmonoidClass (S₁ i) (R₁ i)] [(i : ι) → AddSubmonoidClass (S₂ i) (R₂ i)]

-- @@ L111-111 verbatim
variable {A₁ : (i : ι) → S₁ i} {A₂ : (i : ι) → S₂ i}

-- @@ L112-112 verbatim
variable [(i : ι) → SMulMemClass (S₁ i) T (R₁ i)] [(i : ι) → SMulMemClass (S₂ i) T (R₂ i)]


-- @@ L114-122 verbatim
/-- The `LinearEquiv` between restricted products built from `LinearEquiv`s on the factors. -/
def LinearEquiv.restrictedProductCongrRight (φ : (i : ι) → R₁ i ≃ₗ[T] R₂ i)
    (hφ : ∀ᶠ i in 𝓕, Set.BijOn (φ i) (A₁ i) (A₂ i)) :
    (Πʳ i, [R₁ i, A₁ i]_[𝓕]) ≃ₗ[T] (Πʳ i, [R₂ i, A₂ i]_[𝓕]) where
  __ := AddEquiv.restrictedProductCongrRight (fun i ↦ (φ i).toAddEquiv)
    (by filter_upwards [hφ]; exact fun i ↦ id)
  map_smul' m x := by
    ext i
    apply map_smul


-- @@ L124-124 verbatim
end linear_equiv


-- @@ L126-126 verbatim
end pi_congr_right


-- @@ L128-128 verbatim
section pi_congr_left


-- @@ L130-130 verbatim
variable {ι₁ ι₂ : Type*}

-- @@ L131-132 verbatim
variable {R₁ : ι₁ → Type*} {S₁ : ι₁ → Type*} {R₂ : ι₂ → Type*} {S₂ : ι₂ → Type*}
  [(i : ι₁) → SetLike (S₁ i) (R₁ i)] [(i : ι₂) → SetLike (S₂ i) (R₂ i)]

-- @@ L133-133 verbatim
variable {𝓕₁ : Filter ι₁} {𝓕₂ : Filter ι₂}

-- @@ L134-134 verbatim
variable {A₁ : (i : ι₁) → Set (R₁ i)} {A₂ : (i : ι₂) → Set (R₂ i)}


-- @@ L136-155 verbatim
/-- The equivalence between restricted products on the same factors on different
indices, when the indices are equivalent, with compatibility on the restriction
filters. Applying the equivalence on the right-hand side. -/
@[simps! apply, simps -isSimp symm_apply]
def Equiv.restrictedProductCongrLeft' (e : ι₁ ≃ ι₂) (h : 𝓕₂ = 𝓕₁.map e) :
    Πʳ i, [R₁ i, A₁ i]_[𝓕₁] ≃ Πʳ j, [R₁ (e.symm j), A₁ (e.symm j)]_[𝓕₂] where
  toFun x := ⟨fun i ↦ e.piCongrLeft' _ x i, by
    have := x.eventually
    simp only [piCongrLeft'_apply, h, Filter.eventually_map]; grind⟩
  invFun y := ⟨fun j ↦ (e.piCongrLeft' _).symm y j, by
    have := y.eventually
    simp_rw [h] at this
    have := Filter.eventually_map.1 this
    simp only [piCongrLeft'_symm_apply]; grind⟩
  left_inv x := by
    ext i
    exact funext_iff.1 ((e.piCongrLeft' _).left_inv x) i
  right_inv y := by
    ext j
    exact funext_iff.1 ((e.piCongrLeft' _).right_inv y) j


-- @@ L157-161 verbatim
@[simp]
theorem Equiv.restrictedProductCongrLeft'_symm_apply_apply (e : ι₁ ≃ ι₂) (h : 𝓕₂ = 𝓕₁.map e)
    (x : Πʳ j, [R₁ (e.symm j), A₁ (e.symm j)]_[𝓕₂]) (j : ι₂) :
    (restrictedProductCongrLeft' e h).symm x (e.symm j) = x j := by
  simp [restrictedProductCongrLeft'_symm_apply]


-- @@ L163-168 verbatim
/-- The equivalence between restricted products on the same factors on different
indices, when the indices are equivalent, with compatibility on the restriction
filters. Applying the equivalence on the left-hand side. -/
def Equiv.restrictedProductCongrLeft (e : ι₁ ≃ ι₂) (h : 𝓕₁ = 𝓕₂.comap e) :
    Πʳ i, [R₂ (e i), A₂ (e i)]_[𝓕₁] ≃ Πʳ j, [R₂ j, A₂ j]_[𝓕₂] :=
  ((e.symm).restrictedProductCongrLeft' (𝓕₂.map_equiv_symm _ ▸ h)).symm


-- @@ L170-174 verbatim
@[simp]
theorem Equiv.restrictedProductCongrLeft_apply_apply (e : ι₁ ≃ ι₂) (h : 𝓕₁ = 𝓕₂.comap e)
    (x : Πʳ i, [R₂ (e i), A₂ (e i)]_[𝓕₁]) (i : ι₁) :
    (restrictedProductCongrLeft e h) x (e i) = x i :=
  restrictedProductCongrLeft'_symm_apply_apply e.symm (𝓕₂.map_equiv_symm _ ▸ h) x _


-- @@ L176-178 verbatim
#adaptation_note /-- to_additive started failing in 4.28.0 . This should be fixed
in current mathlib; these lines to 200 can be deleted. See
https://github.com/ImperialCollegeLondon/FLT/pull/859/changes -/

-- @@ L179-179 verbatim
section add_equiv


-- @@ L181-183 verbatim
variable [(i : ι₁) → AddMonoid (R₁ i)] [(i : ι₂) → AddMonoid (R₂ i)]
  [(i : ι₁) → AddSubmonoidClass (S₁ i) (R₁ i)] [(i : ι₂) → AddSubmonoidClass (S₂ i) (R₂ i)]
  {A₁ : (i : ι₁) → S₁ i} {A₂ : (i : ι₂) → S₂ i}

-- @@ L184-192 verbatim
set_option backward.isDefEq.respectTransparency.types false in
/-- The additive monoid isomorphism between restricted
products on the same factors on different indices, when the indices are equivalent, with
compatibility on the restriction filters. Applying the equivalence on the right-hand side. -/
@[simps! apply]
def AddEquiv.restrictedProductCongrLeft' (e : ι₁ ≃ ι₂) (h : 𝓕₂ = 𝓕₁.map e) :
    (Πʳ i, [R₁ i, A₁ i]_[𝓕₁]) ≃+ (Πʳ j, [R₁ (e.symm j), A₁ (e.symm j)]_[𝓕₂]) where
  __ := Equiv.restrictedProductCongrLeft' e h
  map_add' _ _ := by ext; simp [Equiv.restrictedProductCongrLeft']


-- @@ L194-203 verbatim
/-- The additive monoid isomorphism between restricted
products on the same factors on different indices, when the indices are equivalent, with
compatibility on the restriction filters. Applying the equivalence on the left-hand side. -/
def AddEquiv.restrictedProductCongrLeft (e : ι₁ ≃ ι₂) (h : 𝓕₁ = 𝓕₂.comap e) :
    Πʳ i, [R₂ (e i), A₂ (e i)]_[𝓕₁] ≃+ Πʳ j, [R₂ j, A₂ j]_[𝓕₂] where
  __ := Equiv.restrictedProductCongrLeft e h
  map_add' _ _ := by
    ext j
    obtain ⟨i, rfl⟩ := e.surjective j
    simp


-- @@ L205-205 verbatim
end add_equiv


-- @@ L207-207 verbatim
section mul_equiv


-- @@ L209-215 verbatim
variable [(i : ι₁) → Monoid (R₁ i)] [(i : ι₂) → Monoid (R₂ i)]
  [(i : ι₁) → SubmonoidClass (S₁ i) (R₁ i)] [(i : ι₂) → SubmonoidClass (S₂ i) (R₂ i)]
  {A₁ : (i : ι₁) → S₁ i} {A₂ : (i : ι₂) → S₂ i}

-- @[to_additive (attr := simps! apply)  should be re-added when we bump beyond 4.28.0; we want
-- to revert the changes in this file made in
-- https://github.com/ImperialCollegeLondon/FLT/pull/859/changes

-- @@ L216-223 verbatim
set_option backward.isDefEq.respectTransparency.types false in
/-- The multiplicative monoid isomorphism between restricted products on the same factors on
different indices, when the indices are equivalent, with compatibility on the restriction
filters. Applying the equivalence on the right-hand side. -/
def MulEquiv.restrictedProductCongrLeft' (e : ι₁ ≃ ι₂) (h : 𝓕₂ = 𝓕₁.map e) :
    (Πʳ i, [R₁ i, A₁ i]_[𝓕₁]) ≃* (Πʳ j, [R₁ (e.symm j), A₁ (e.symm j)]_[𝓕₂]) where
  __ := Equiv.restrictedProductCongrLeft' e h
  map_mul' _ _ := by ext; simp [Equiv.restrictedProductCongrLeft']


-- @@ L225-234 verbatim
/-- The multiplicative monoid isomorphism between restricted products on the same factors on
different indices, when the indices are equivalent, with compatibility on the restriction
filters. Applying the equivalence on the left-hand side. -/
def MulEquiv.restrictedProductCongrLeft (e : ι₁ ≃ ι₂) (h : 𝓕₁ = 𝓕₂.comap e) :
    Πʳ i, [R₂ (e i), A₂ (e i)]_[𝓕₁] ≃* Πʳ j, [R₂ j, A₂ j]_[𝓕₂] where
  __ := Equiv.restrictedProductCongrLeft e h
  map_mul' _ _ := by
    ext j
    obtain ⟨i, rfl⟩ := e.surjective j
    simp


-- @@ L236-236 verbatim
end mul_equiv


-- @@ L238-238 verbatim
section ring_equiv


-- @@ L240-241 verbatim
variable [(i : ι₁) → Semiring (R₁ i)] [(i : ι₂) → Semiring (R₂ i)]
  [(i : ι₁) → SubsemiringClass (S₁ i) (R₁ i)] [(i : ι₂) → SubsemiringClass (S₂ i) (R₂ i)]

-- @@ L242-242 verbatim
variable {A₁ : (i : ι₁) → S₁ i} {A₂ : (i : ι₂) → S₂ i}


-- @@ L244-251 verbatim
/-- The ring isomorphism between restricted products on the same factors on
different indices, when the indices are equivalent, with compatibility on the restriction
filters. Applying the equivalence on the right-hand side. -/
@[simps! apply]
def RingEquiv.restrictedProductCongrLeft' (e : ι₁ ≃ ι₂) (h : 𝓕₂ = 𝓕₁.map e) :
    (Πʳ i, [R₁ i, A₁ i]_[𝓕₁]) ≃+* (Πʳ j, [R₁ (e.symm j), A₁ (e.symm j)]_[𝓕₂]) where
  __ := AddEquiv.restrictedProductCongrLeft' e h
  map_mul' _ _ := rfl


-- @@ L253-262 verbatim
/-- The ring isomorphism between restricted products on the same factors on
different indices, when the indices are equivalent, with compatibility on the restriction
filters. Applying the equivalence on the right-hand side. -/
def RingEquiv.restrictedProductCongrLeft (e : ι₁ ≃ ι₂) (h : 𝓕₁ = 𝓕₂.comap e) :
    Πʳ i, [R₂ (e i), A₂ (e i)]_[𝓕₁] ≃+* Πʳ j, [R₂ j, A₂ j]_[𝓕₂] where
  __ := AddEquiv.restrictedProductCongrLeft e h
  map_mul' _ _ := by
    ext j
    obtain ⟨i, rfl⟩ := e.surjective j
    simp [AddEquiv.restrictedProductCongrLeft]


-- @@ L264-264 verbatim
end ring_equiv


-- @@ L266-266 verbatim
section linear_equiv


-- @@ L268-268 verbatim
variable {T : Type*} [Semiring T]

-- @@ L269-269 verbatim
variable {A₁ : (i : ι₁) → S₁ i} {A₂ : (i : ι₂) → S₂ i}

-- @@ L270-273 verbatim
variable [(i : ι₁) → AddCommMonoid (R₁ i)] [(i : ι₂) → AddCommMonoid (R₂ i)]
  [(i : ι₁) → Module T (R₁ i)] [(i : ι₂) → Module T (R₂ i)]
  [(i : ι₁) → AddSubmonoidClass (S₁ i) (R₁ i)] [(i : ι₂) → AddSubmonoidClass (S₂ i) (R₂ i)]
  [(i : ι₁) → SMulMemClass (S₁ i) T (R₁ i)] [(i : ι₂) → SMulMemClass (S₂ i) T (R₂ i)]


-- @@ L275-282 verbatim
/-- The linear isomorphism between restricted products on the same factors on
different indices, when the indices are equivalent, with compatibility on the restriction
filters. Applying the equivalence on the right-hand side. -/
@[simps! apply]
def LinearEquiv.restrictedProductCongrLeft' (e : ι₁ ≃ ι₂) (h : 𝓕₂ = 𝓕₁.map e) :
    (Πʳ i, [R₁ i, A₁ i]_[𝓕₁]) ≃ₗ[T] (Πʳ j, [R₁ (e.symm j), A₁ (e.symm j)]_[𝓕₂]) where
  __ := AddEquiv.restrictedProductCongrLeft' e h
  map_smul' _ _ := rfl


-- @@ L284-293 verbatim
/-- The linear isomorphism between restricted products on the same factors on
different indices, when the indices are equivalent, with compatibility on the restriction
filters. Applying the equivalence on the left-hand side. -/
def LinearEquiv.restrictedProductCongrLeft (e : ι₁ ≃ ι₂) (h : 𝓕₁ = 𝓕₂.comap e) :
    Πʳ i, [R₂ (e i), A₂ (e i)]_[𝓕₁] ≃ₗ[T] Πʳ j, [R₂ j, A₂ j]_[𝓕₂] where
  __ := AddEquiv.restrictedProductCongrLeft e h
  map_smul' _ _ := by
    ext j
    obtain ⟨i, rfl⟩ := e.surjective j
    simp [AddEquiv.restrictedProductCongrLeft]


-- @@ L295-295 verbatim
end linear_equiv


-- @@ L297-297 verbatim
end pi_congr_left


-- @@ L299-299 verbatim
section pi_congr


-- @@ L301-301 verbatim
variable {ι₁ ι₂ : Type*}

-- @@ L302-303 verbatim
variable {R₁ : ι₁ → Type*} {S₁ : ι₁ → Type*} {R₂ : ι₂ → Type*} {S₂ : ι₂ → Type*}
  [(i : ι₁) → SetLike (S₁ i) (R₁ i)] [(i : ι₂) → SetLike (S₂ i) (R₂ i)]

-- @@ L304-304 verbatim
variable {𝓕₁ : Filter ι₁} {𝓕₂ : Filter ι₂}

-- @@ L305-305 verbatim
variable {A₁ : (i : ι₁) → Set (R₁ i)} {A₂ : (i : ι₂) → Set (R₂ i)}


-- @@ L307-314 verbatim
/-- The equivalence between restricted products when the indices and factors are equivalent,
provided compatibility criteria on the restriction filters and factors. -/
def Equiv.restrictedProductCongr (e : ι₁ ≃ ι₂) (h : 𝓕₁ = 𝓕₂.comap e)
    (φ : (i : ι₁) → R₁ i ≃ R₂ (e i))
    (hφ : ∀ᶠ i in 𝓕₁, Set.BijOn (φ i) (A₁ i) (A₂ (e i))) :
    Πʳ i, [R₁ i, A₁ i]_[𝓕₁] ≃ Πʳ j, [R₂ j, A₂ j]_[𝓕₂] :=
  (Equiv.restrictedProductCongrRight φ hφ).trans
    (e.restrictedProductCongrLeft h)


-- @@ L316-323 verbatim
@[simp]
theorem Equiv.restrictedProductCongr_apply_apply {e : ι₁ ≃ ι₂} {h : 𝓕₁ = 𝓕₂.comap e}
    {φ : (i : ι₁) → R₁ i ≃ R₂ (e i)}
    {hφ : ∀ᶠ i in 𝓕₁, Set.BijOn (φ i) (A₁ i) (A₂ (e i))}
    {x : Πʳ i, [R₁ i, A₁ i]_[𝓕₁]} {i : ι₁} :
    e.restrictedProductCongr h φ hφ x (e i) =
      φ i (x i) := by
  simp [restrictedProductCongr]


-- @@ L325-331 verbatim
@[simp]
theorem Equiv.restrictedProductCongr_symm_apply {e : ι₁ ≃ ι₂} {h : 𝓕₁ = 𝓕₂.comap e}
    {φ : (i : ι₁) → R₁ i ≃ R₂ (e i)}
    {hφ : ∀ᶠ i in 𝓕₁, Set.BijOn (φ i) (A₁ i) (A₂ (e i))}
    {x : Πʳ j, [R₂ j, A₂ j]_[𝓕₂]} :
    (e.restrictedProductCongr h φ hφ).symm x = fun a => (φ a).symm (x (e a)) :=
  rfl


-- @@ L333-336 verbatim
#adaptation_note /-- to_additive started failing in 4.28.0.
This should be fixed
in current mathlib; these lines to 200 can be deleted. See
https://github.com/ImperialCollegeLondon/FLT/pull/859/changes  -/

-- @@ L337-337 verbatim
section add_equiv


-- @@ L339-340 verbatim
variable [(i : ι₁) → AddMonoid (R₁ i)] [(i : ι₂) → AddMonoid (R₂ i)]
  [(i : ι₁) → AddSubmonoidClass (S₁ i) (R₁ i)] [(i : ι₂) → AddSubmonoidClass (S₂ i) (R₂ i)]

-- @@ L341-341 verbatim
variable {A₁ : (i : ι₁) → S₁ i} {A₂ : (i : ι₂) → S₂ i}


-- @@ L343-352 verbatim
/-- The additive monoid isomorphism between restricted
products when the indices and factors are equivalent, provided compatibility criteria on the
restriction filters and factors. -/
@[simps! apply]
def AddEquiv.restrictedProductCongr (e : ι₁ ≃ ι₂) (h : 𝓕₁ = 𝓕₂.comap e)
    (φ : (i : ι₁) → R₁ i ≃+ R₂ (e i))
    (hφ : ∀ᶠ i in 𝓕₁, Set.BijOn (φ i) (A₁ i) (A₂ (e i))) :
    (Πʳ i, [R₁ i, A₁ i]_[𝓕₁]) ≃+ (Πʳ j, [R₂ j, A₂ j]_[𝓕₂]) where
  __ := Equiv.restrictedProductCongr e h (fun _ ↦ (φ _).toEquiv) hφ
  map_add' _ _ := by ext j; obtain ⟨i, rfl⟩ := e.surjective j; simp


-- @@ L354-354 verbatim
end add_equiv


-- @@ L356-356 verbatim
section mul_equiv


-- @@ L358-359 verbatim
variable [(i : ι₁) → Monoid (R₁ i)] [(i : ι₂) → Monoid (R₂ i)]
  [(i : ι₁) → SubmonoidClass (S₁ i) (R₁ i)] [(i : ι₂) → SubmonoidClass (S₂ i) (R₂ i)]

-- @@ L360-360 verbatim
variable {A₁ : (i : ι₁) → S₁ i} {A₂ : (i : ι₂) → S₂ i}


-- @@ L362-369 verbatim
/-- The multiplicative monoid isomorphism between restricted products when the indices and factors
are equivalent, provided compatibility criteria on the restriction filters and factors. -/
def MulEquiv.restrictedProductCongr (e : ι₁ ≃ ι₂) (h : 𝓕₁ = 𝓕₂.comap e)
    (φ : (i : ι₁) → R₁ i ≃* R₂ (e i))
    (hφ : ∀ᶠ i in 𝓕₁, Set.BijOn (φ i) (A₁ i) (A₂ (e i))) :
    (Πʳ i, [R₁ i, A₁ i]_[𝓕₁]) ≃* (Πʳ j, [R₂ j, A₂ j]_[𝓕₂]) where
  __ := Equiv.restrictedProductCongr e h (fun _ ↦ (φ _).toEquiv) hφ
  map_mul' _ _ := by ext j; obtain ⟨i, rfl⟩ := e.surjective j; simp


-- @@ L371-371 verbatim
end mul_equiv


-- @@ L373-373 verbatim
section ring_equiv


-- @@ L375-376 verbatim
variable [(i : ι₁) → Semiring (R₁ i)] [(i : ι₂) → Semiring (R₂ i)]
  [(i : ι₁) → SubsemiringClass (S₁ i) (R₁ i)] [(i : ι₂) → SubsemiringClass (S₂ i) (R₂ i)]

-- @@ L377-377 verbatim
variable {A₁ : (i : ι₁) → S₁ i} {A₂ : (i : ι₂) → S₂ i}


-- @@ L379-387 verbatim
set_option backward.isDefEq.respectTransparency.types false in
/-- The ring isomorphism between restricted products when the indices and factors
are equivalent, provided compatibility criteria on the restriction filters and factors. -/
def RingEquiv.restrictedProductCongr (e : ι₁ ≃ ι₂) (h : 𝓕₁ = 𝓕₂.comap e)
    (φ : (i : ι₁) → R₁ i ≃+* R₂ (e i))
    (hφ : ∀ᶠ i in 𝓕₁, Set.BijOn (φ i) (A₁ i) (A₂ (e i))) :
    (Πʳ i, [R₁ i, A₁ i]_[𝓕₁]) ≃+* (Πʳ j, [R₂ j, A₂ j]_[𝓕₂]) where
  __ := AddEquiv.restrictedProductCongr e h (fun _ ↦ (φ _).toAddEquiv) hφ
  map_mul' _ _ := by ext j; obtain ⟨i, rfl⟩ := e.surjective j; simp


-- @@ L389-397 verbatim
set_option backward.isDefEq.respectTransparency.types false in
@[simp]
theorem RingEquiv.restrictedProductCongr_apply_apply {e : ι₁ ≃ ι₂} {h : 𝓕₁ = 𝓕₂.comap e}
    {φ : (i : ι₁) → R₁ i ≃+* R₂ (e i)}
    {hφ : ∀ᶠ i in 𝓕₁, Set.BijOn (φ i) (A₁ i) (A₂ (e i))}
    {x : Πʳ i, [R₁ i, A₁ i]_[𝓕₁]} {i : ι₁} :
    RingEquiv.restrictedProductCongr e h φ hφ x (e i) =
      φ i (x i) := by
  simp [restrictedProductCongr]


-- @@ L399-405 verbatim
@[simp]
theorem RingEquiv.restrictedProductCongr_symm_apply {e : ι₁ ≃ ι₂} {h : 𝓕₁ = 𝓕₂.comap e}
    {φ : (i : ι₁) → R₁ i ≃+* R₂ (e i)}
    {hφ : ∀ᶠ i in 𝓕₁, Set.BijOn (φ i) (A₁ i) (A₂ (e i))}
    {x : Πʳ j, [R₂ j, A₂ j]_[𝓕₂]} :
    (RingEquiv.restrictedProductCongr e h φ hφ).symm x = fun a => (φ a).symm (x (e a)) :=
  rfl


-- @@ L407-407 verbatim
end ring_equiv


-- @@ L409-409 verbatim
section linear_equiv


-- @@ L411-411 verbatim
variable {T : Type*} [Semiring T]

-- @@ L412-412 verbatim
variable [(i : ι₁) → AddCommMonoid (R₁ i)] [(i : ι₂) → AddCommMonoid (R₂ i)]

-- @@ L413-413 verbatim
variable {A₁ : (i : ι₁) → S₁ i} {A₂ : (i : ι₂) → S₂ i}

-- @@ L414-416 verbatim
variable [(i : ι₁) → Module T (R₁ i)] [(i : ι₂) → Module T (R₂ i)]
  [(i : ι₁) → AddSubmonoidClass (S₁ i) (R₁ i)] [(i : ι₂) → AddSubmonoidClass (S₂ i) (R₂ i)]
  [(i : ι₁) → SMulMemClass (S₁ i) T (R₁ i)] [(i : ι₂) → SMulMemClass (S₂ i) T (R₂ i)]


-- @@ L418-429 verbatim
set_option backward.isDefEq.respectTransparency.types false in
/-- The linear isomorphism between restricted products when the indices and factors
are equivalent, provided compatibility criteria on the restriction filters and factors. -/
def LinearEquiv.restrictedProductCongr (e : ι₁ ≃ ι₂) (h : 𝓕₁ = 𝓕₂.comap e)
    (φ : (i : ι₁) → R₁ i ≃ₗ[T] R₂ (e i))
    (hφ : ∀ᶠ i in 𝓕₁, Set.BijOn (φ i) (A₁ i) (A₂ (e i))) :
    (Πʳ i, [R₁ i, A₁ i]_[𝓕₁]) ≃ₗ[T] (Πʳ j, [R₂ j, A₂ j]_[𝓕₂]) where
  __ := AddEquiv.restrictedProductCongr e h (fun _ ↦ (φ _).toAddEquiv) hφ
  map_smul' _ _ := by
    ext j
    obtain ⟨i, rfl⟩ := e.surjective j
    simp


-- @@ L431-431 verbatim
end linear_equiv


-- @@ L433-433 verbatim
end pi_congr


-- @@ L435-435 verbatim
section structure_map


-- @@ L437-439 verbatim
variable {ι₁ ι₂ : Type*} {R₁ : ι₁ → Type*} {S₁ : ι₁ → Type*} {R₂ : ι₂ → Type*} {S₂ : ι₂ → Type*}
  [(i : ι₁) → SetLike (S₁ i) (R₁ i)] [(i : ι₂) → SetLike (S₂ i) (R₂ i)]
  {𝓕₁ : Filter ι₁} {𝓕₂ : Filter ι₂} {A₁ : (i : ι₁) → Set (R₁ i)} {A₂ : (i : ι₂) → Set (R₂ i)}


-- @@ L441-443 verbatim
variable [(i : ι₁) → Ring (R₁ i)] [(i : ι₂) → Ring (R₂ i)]
  [(i : ι₁) → SubringClass (S₁ i) (R₁ i)] [(i : ι₂) → SubringClass (S₂ i) (R₂ i)]
  {A₁ : (i : ι₁) → S₁ i} {A₂ : (i : ι₂) → S₂ i}


-- @@ L445-456 verbatim
theorem RingEquiv.restrictedProductCongr_bijOn_structureSubring (e : ι₁ ≃ ι₂) (h : 𝓕₁ = 𝓕₂.comap e)
    (φ : (i : ι₁) → R₁ i ≃+* R₂ (e i))
    (hφ : ∀ i, Set.BijOn (φ i) (A₁ i) (A₂ (e i))) :
    Set.BijOn (restrictedProductCongr e h φ (.of_forall hφ))
      (structureSubring R₁ A₁ 𝓕₁) (structureSubring R₂ A₂ 𝓕₂) := by
  have hm (i : _) := (hφ i).mapsTo
  have hs (i : _) := (hφ i).symm (φ i).toEquiv.invOn |>.mapsTo
  refine ⟨fun x hx ↦ ?_, (RingEquiv.injective _).injOn, fun y hy ↦ ?_⟩
  · refine mem_structureSubring_iff.2 fun i ↦ ?_
    obtain ⟨j, rfl⟩ := e.surjective i
    aesop
  · exact ⟨(restrictedProductCongr e h φ (.of_forall hφ)).symm y, by aesop⟩


-- @@ L458-458 verbatim
end structure_map


-- @@ L460-460 verbatim
section binary


-- @@ L462-463 verbatim
variable {ι : Type*} {ℱ : Filter ι} {A B : ι → Type*}
  {C : (i : ι) → Set (A i)} {D : (i : ι) → Set (B i)}


-- @@ L465-476 verbatim
/-- The bijection between a restricted product of binary products, and the binary product
of the restricted products. -/
@[simps]
def Equiv.restrictedProductProd :
    Πʳ i, [A i × B i, C i ×ˢ D i]_[ℱ] ≃ (Πʳ i, [A i, C i]_[ℱ]) × (Πʳ i, [B i, D i]_[ℱ]) where
  toFun x := (map (fun i (t : A i × B i) ↦ t.1) (by simp +contextual [Set.MapsTo]) x,
              map (fun i (t : A i × B i) ↦ t.2) (by simp +contextual [Set.MapsTo]) x)
  invFun yz :=
    ⟨fun i ↦ (yz.1 i, yz.2 i), by
    filter_upwards [yz.1.2, yz.2.2] with i using Set.mk_mem_prod⟩
  left_inv x := by ext <;> rfl
  right_inv y := by ext <;> rfl


-- @@ L478-481 verbatim
lemma Equiv.restrictedProductProd_symm_comp_inclusion {ℱ₁ ℱ₂ : Filter ι} (hℱ : ℱ₁ ≤ ℱ₂) :
    Equiv.restrictedProductProd.symm ∘ Prod.map (inclusion _ _ hℱ) (inclusion _ _ hℱ) =
      inclusion (fun i ↦ A i × B i) (fun i ↦ C i ×ˢ D i) hℱ ∘ Equiv.restrictedProductProd.symm :=
  rfl


-- @@ L483-483 verbatim
end binary


-- @@ L485-485 verbatim
section pi


-- @@ L487-492 verbatim
variable {ι : Type*} {ℱ : Filter ι} {n : Type*} [Fintype n]
    {A : n → ι → Type*}
    {C : (j : n) → (i : ι) → Set (A j i)}

-- Q: Is there a mathlibism for `{f | ∀ j, f j ∈ C j i}`?
-- A: Yes, `Set.pi Set.univ`, except that it's defeq to `{f | ∀ j ∈ univ, f j ∈ C j i}`


-- @@ L494-502 verbatim
/-- The bijection between a restricted product of finite products, and a finite product
of restricted products.
-/
def Equiv.restrictedProductPi :
    Πʳ i, [Π j, A j i, {f | ∀ j, f j ∈ C j i}]_[ℱ] ≃ Π j, Πʳ i, [A j i, C j i]_[ℱ] where
  toFun x j := map (fun i t ↦ t _) (by simp +contextual [Set.MapsTo]) x
  invFun y := .mk (fun i j ↦ y j i) (by simp)
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl


-- @@ L504-507 verbatim
lemma Equiv.restrictedProductPi_symm_comp_inclusion {ℱ₁ ℱ₂ : Filter ι} (hℱ : ℱ₁ ≤ ℱ₂) :
    Equiv.restrictedProductPi.symm ∘ Pi.map (fun i ↦ inclusion (A i) (C i) hℱ) =
      inclusion _ _ hℱ ∘ Equiv.restrictedProductPi.symm :=
  rfl


-- @@ L509-516 verbatim
/-- The bijection between a restricted product of m x n matrices, and m x n matrices
of restricted products.
-/
def Equiv.restrictedProductMatrix {ι : Type*} {m n : Type*} [Fintype m] [Fintype n]
    {A : ι → Type*}
    {C : (i : ι) → Set (A i)} :
    Πʳ i, [Matrix m n (A i), {f | ∀ a b, f a b ∈ C i}] ≃ Matrix m n (Πʳ i, [A i, C i]) :=
  Equiv.restrictedProductPi.trans (Equiv.piCongrRight fun _ ↦ Equiv.restrictedProductPi)


-- @@ L518-518 verbatim
end pi


-- @@ L520-520 verbatim
namespace RestrictedProduct


-- @@ L522-522 verbatim
section flatten


-- @@ L524-524 verbatim
variable {ι : Type*}

-- @@ L525-528 verbatim
variable {ℱ : Filter ι}
    {G H : ι → Type*}
    {C : (i : ι) → Set (G i)}
    {D : (i : ι) → Set (H i)}

-- @@ L529-529 verbatim
variable {ι₂ : Type*} {𝒢 : Filter ι₂} {f : ι → ι₂} (C)


-- @@ L531-536 verbatim
variable (hf : Filter.Tendsto f ℱ 𝒢) in
/-- The canonical map from a restricted product of products over fibres of a map on indexing sets
to the restricted product over the original indexing set. -/
def flatten : Πʳ j, [Π (i : f ⁻¹' {j}), G i, Set.pi Set.univ (fun (i : f ⁻¹' {j}) => C i)]_[𝒢] →
    Πʳ i, [G i, C i]_[ℱ] :=
  mapAlong _ G f hf (fun i x ↦ x ⟨i, rfl⟩) (by filter_upwards with x y hy using hy ⟨x, rfl⟩ trivial)


-- @@ L538-541 verbatim
@[simp]
lemma flatten_apply (hf : Filter.Tendsto f ℱ 𝒢) (x) (i : ι) :
    flatten C hf x i = x (f i) ⟨i, rfl⟩ :=
  rfl


-- @@ L543-543 verbatim
variable (hf : Filter.comap f 𝒢 = ℱ)


-- @@ L545-558 verbatim
/-- The canonical bijection from a restricted product of products over fibres of a map on indexing
sets to the restricted product over the original indexing set. -/
def flattenEquiv :
    Πʳ j, [Π (i : f ⁻¹' {j}), G i, Set.pi Set.univ (fun (i : f ⁻¹' {j}) => C i)]_[𝒢] ≃
    Πʳ i, [G i, C i]_[ℱ] where
  toFun := flatten C (by rw [Filter.tendsto_iff_comap]; exact hf.ge)
  invFun := fun ⟨x, hx⟩ ↦ ⟨fun _ i ↦ x i, by
    rw [← hf, Filter.eventually_comap] at hx
    filter_upwards [hx] with j hj ⟨i, hi⟩ _ using hj i hi⟩
  left_inv := by
    intro ⟨x, hx⟩
    ext _ ⟨i, rfl⟩
    rfl
  right_inv x := by ext i; rfl


-- @@ L560-563 verbatim
@[simp]
lemma flatten_equiv_apply (x) (i : ι) :
    flattenEquiv C hf x i = x (f i) ⟨i, rfl⟩ :=
  rfl


-- @@ L565-568 verbatim
@[simp]
lemma flatten_equiv_symm_apply (x) (i : ι₂) (j : f ⁻¹' {i}) :
    (flattenEquiv C hf).symm x i j = x j.1 :=
  rfl


-- @@ L570-570 verbatim
variable (hf : Filter.Tendsto f Filter.cofinite Filter.cofinite)


-- @@ L572-577 verbatim
/-- The equivalence given by `flatten` when both restricted products are over the cofinite
filter. -/
def flattenEquiv' :
    Πʳ j, [Π (i : f ⁻¹' {j}), G i, Set.pi Set.univ (fun (i : f ⁻¹' {j}) => C i)] ≃
    Πʳ i, [G i, C i] :=
  flattenEquiv C <| le_antisymm (Filter.comap_cofinite_le f) (Filter.map_le_iff_le_comap.mp hf)


-- @@ L579-582 verbatim
@[simp]
lemma flatten_equiv'_apply (x) (i : ι) :
    flattenEquiv' C hf x i = x (f i) ⟨i, rfl⟩ :=
  rfl


-- @@ L584-587 verbatim
@[simp]
lemma flatten_equiv'_symm_apply (x) (i : ι₂) (j : f ⁻¹' {i}) :
    (flattenEquiv' C hf).symm x i j = x j.1 :=
  rfl


-- @@ L589-589 verbatim
end flatten


-- @@ L591-591 verbatim
section principal

-- @@ L592-598 verbatim
/-!

## Principal filters

A restricted product over a principal filter is isomorphic to a product.

-/


-- @@ L600-600 verbatim
variable {ι : Type*} (R : ι → Type*) (S : Set ι) [∀ i, Decidable (i ∈ S)] (A : (i : ι) → Set (R i))


-- @@ L602-602 verbatim
open scoped Filter


-- @@ L604-604 verbatim
section type


-- @@ L606-618 verbatim
/-- The canonical isomorphism between `Πʳ i, [R i, A i]_[𝓟 S]` and
`(Π i ∈ S, R i) × (Π i ∉ S, A i)`
-/
def principalEquivProd : Πʳ i, [R i, A i]_[𝓟 S] ≃
    (Π i : S, A i) × (Π i : (Sᶜ : Set ι), R i) where
  toFun x := (fun i ↦ ⟨x i, x.2 i.2⟩, fun i ↦ x i)
  invFun y := ⟨fun i ↦ if hi : i ∈ S then y.1 ⟨i, hi⟩ else y.2 ⟨i, hi⟩,
  by aesop⟩
  left_inv x := by ext; simp
  right_inv x := by
    ext i
    · simp
    · simp [dite_eq_right i.2]


-- @@ L620-620 verbatim
end type


-- @@ L622-622 verbatim
variable {T : ι → Type*} [Π i, SetLike (T i) (R i)] {A : Π i, T i}


-- @@ L624-626 verbatim
section monoid

-- TODO move to FLT/Mathlib

-- @@ L627-632 verbatim
/-- Monoid equivalence version of `principalEquivProd`. -/
@[to_additive /-- Additive monoid equivalence of principalEquivProd. -/]
def principalMulEquivProd [Π i, Monoid (R i)] [∀ i, SubmonoidClass (T i) (R i)] :
    Πʳ i, [R i, A i]_[𝓟 S] ≃* (Π i : S, A i) × (Π i : (Sᶜ : Set ι), R i) where
  __ := principalEquivProd R S _
  map_mul' _ _ := rfl


-- @@ L634-634 verbatim
end monoid


-- @@ L636-636 verbatim
variable {ι : Type*} (R : ι → Type*) {ℱ : Filter ι} (A : Type*) [CommRing A]


-- @@ L638-638 verbatim
open scoped RestrictedProduct


-- @@ L640-640 verbatim
open Filter


-- @@ L642-642 verbatim
section module


-- @@ L644-651 verbatim
/-- Module equivalence version of `principalEquivProd`. -/
noncomputable def principalLinearEquivProd [Π i, AddCommGroup (R i)]
    [∀ i, Module A (R i)] {C : ∀ i, Submodule A (R i)}
    (S : Set ι) [∀ i, Decidable (i ∈ S)] :
    (Πʳ i, [R i, C i]_[𝓟 S]) ≃ₗ[A] ((Π i : S, C i) ×
      (Π i : (Sᶜ : Set ι), R i)) where
  __ := principalAddEquivSum R S (A := C)
  map_smul' _ _ := rfl


-- @@ L653-653 verbatim
end module


-- @@ L655-655 verbatim
end principal


-- @@ L657-657 verbatim
end RestrictedProduct
