import DG.Homotopy.ConeCochain


-- @@ L3-22 verbatim
/-!
# The mapping cone of a composition

Let `f : X₁ →ᵈᵍ[A] X₂` and `g : X₂ →ᵈᵍ[A] X₃` be morphisms of dg modules. This file ports the
cochain-level part of Mathlib's `Mathlib/Algebra/Homology/HomotopyCategory/Triangulated.lean`,
which is the input of the octahedron axiom for the homotopy category:

* the three morphisms `DG.Cone.compMor₁ f g : Cone f →ᵈᵍ[A] Cone (g ∘ f)`,
  `DG.Cone.compMor₂ f g : Cone (g ∘ f) →ᵈᵍ[A] Cone g` and
  `DG.Cone.compMor₃ f g : Cone g →ᵈᵍ[A] Shift 1 (Cone f)` of Mathlib's triangle
  `mappingConeCompTriangle f g`;
* the homotopy equivalence `DG.Cone.mappingConeCompHomotopyEquiv f g` between `Cone g` and the
  cone of `compMor₁ f g`, built from `DG.Cone.MappingConeCompHomotopyEquiv.hom` and
  `DG.Cone.MappingConeCompHomotopyEquiv.inv` with `inv ∘ hom = id` and an explicit homotopy
  `hom ∘ inv ≃ id`, together with its compatibilities `mappingConeCompHomotopyEquiv_comm₁` and
  `mappingConeCompHomotopyEquiv_comm₂` with the triangles.

All definitions and signs are those of Mathlib. The third morphism of the standard triangle of
a morphism `φ` is `-fstHom φ` (Mathlib's `(mappingCone.triangle φ).mor₃`).
-/


-- @@ L24-24 verbatim
namespace DG


-- @@ L26-26 verbatim
namespace Cone


-- @@ L28-28 verbatim
open Cochain Shift


-- @@ L30-34 expanded
variable {A : Type*} {X₁ X₂ X₃ : Type*} [Ring A] [DGAddCommGroup A] [DGRing A] [AddCommGroup X₁]
  [DGAddCommGroup X₁] [Module A X₁] [DGModule A X₁] [AddCommGroup X₂] [DGAddCommGroup X₂]
  [Module A X₂] [DGModule A X₂] [AddCommGroup X₃] [DGAddCommGroup X₃] [Module A X₃] [DGModule A X₃]
  (f : DGModuleHom A X₁ X₂) (g : DGModuleHom A X₂ X₃)


-- @@ L36-38 expanded
/-- The first morphism `Cone f → Cone (g ∘ f)` of Mathlib's `mappingConeCompTriangle`. -/
def compMor₁ : DGModuleHom A (Cone f) (Cone (g.comp f)) :=
  map DGModuleHom.id g rfl


-- @@ L40-42 expanded
/-- The second morphism `Cone (g ∘ f) → Cone g` of Mathlib's `mappingConeCompTriangle`. -/
def compMor₂ : DGModuleHom A (Cone (g.comp f)) (Cone g) :=
  map f DGModuleHom.id rfl


-- @@ L44-47 expanded
/-- The third morphism `Cone g → (Cone f)⟦1⟧` of Mathlib's `mappingConeCompTriangle`: the
third morphism `-fstHom g` of the standard triangle of `g`, followed by `(inr f)⟦1⟧`. -/
def compMor₃ : DGModuleHom A (Cone g) (Shift 1 (Cone f)) :=
  ((inr f).shift 1).comp (-fstHom g)


-- @@ L49-49 verbatim
variable {f g}


-- @@ L51-53 verbatim
@[simp]
theorem compMor₁_fst_apply (p : Cone f) : (fst (g.comp f)).1 (compMor₁ f g p) = (fst f).1 p :=
  rfl


-- @@ L55-57 verbatim
omit [DGModule A X₁] [DGModule A X₂] [DGModule A X₃] in
@[simp]
theorem compMor₁_snd_apply (p : Cone f) : snd (g.comp f) (compMor₁ f g p) = g (snd f p) := rfl


-- @@ L59-61 verbatim
@[simp]
theorem compMor₂_fst_apply (p : Cone (g.comp f)) :
    (fst g).1 (compMor₂ f g p) = f ((fst (g.comp f)).1 p) := rfl


-- @@ L63-66 verbatim
omit [DGModule A X₁] [DGModule A X₂] [DGModule A X₃] in
@[simp]
theorem compMor₂_snd_apply (p : Cone (g.comp f)) : snd g (compMor₂ f g p) = snd (g.comp f) p :=
  rfl


-- @@ L68-68 verbatim
variable (f g)


-- @@ L70-70 verbatim
namespace MappingConeCompHomotopyEquiv


-- @@ L72-79 expanded
/-- The morphism `Cone g → Cone (compMor₁ f g)` of Mathlib's `MappingConeCompHomotopyEquiv.hom`;
it is a homotopy equivalence (`DG.Cone.mappingConeCompHomotopyEquiv`). -/
def hom : DGModuleHom A (Cone g) (Cone (compMor₁ f g)) :=
  lift _ (descCocycle g (ofHom (inr f)) 0 (zero_add 1) (by simp))
    (descCochain _ 0 (ofHom (inr (g.comp f))) (neg_add_cancel 1))
    (by
      refine Cochain.ext fun p => ext_to ?_ ?_
      · simp [descCochain_apply, d_snd_apply]
      · simp [descCochain_apply, d_snd_apply])


-- @@ L81-89 expanded
/-- The morphism `Cone (compMor₁ f g) → Cone g` of Mathlib's `MappingConeCompHomotopyEquiv.inv`.
-/
def inv : DGModuleHom A (Cone (compMor₁ f g)) (Cone g) :=
  desc _ ((inl g).comp (snd f) (zero_add (-1)))
    (desc _ ((inl g).comp (ofHom f) (zero_add (-1))) (inr g) (by rw [δ_ofHom_comp, δ_inl]; rfl))
    (by
      refine Cochain.ext fun p => ext_to ?_ ?_
      · simp [descCochain_apply, δ_neg_one_apply, inl_d_apply, d_snd_apply]
      · simp [descCochain_apply, δ_neg_one_apply, inl_d_apply, d_snd_apply])


-- @@ L91-95 verbatim
@[simp]
theorem inv_comp_hom : (inv f g).comp (hom f g) = DGModuleHom.id := by
  refine DGModuleHom.ext fun p => ext_to ?_ ?_
  · simp [hom, inv, lift_apply, desc_apply, descCochain_apply]
  · simp [hom, inv, lift_apply, desc_apply, descCochain_apply]


-- @@ L97-110 verbatim
/-- The homotopy `hom ∘ inv ≃ id` of Mathlib's `MappingConeCompHomotopyEquiv.homotopyInvHomId`,
given by the cochain `-inl ∘ inl ∘ fst ∘ snd` of degree `-1`. -/
def homotopyInvHomId : DGHomotopy ((hom f g).comp (inv f g)) DGModuleHom.id :=
  DGHomotopy.mk' (-(((inl (compMor₁ f g)).comp (inl f) (show -1 + -1 = -2 by norm_num)).comp
    (fst (g.comp f)).1 (show 1 + -2 = -1 by norm_num)).comp (snd (compMor₁ f g)) (zero_add (-1)))
    (fun p => by
      refine ext_to ?_ ?_
      · refine ext_to ?_ ?_
        · simp [hom, inv, lift_apply, desc_apply, descCochain_apply, d_fst_apply, d_snd_apply]
        · simp [hom, inv, lift_apply, desc_apply, descCochain_apply, d_fst_apply, d_snd_apply]
          abel
      · refine ext_to ?_ ?_
        · simp [hom, inv, lift_apply, desc_apply, descCochain_apply, d_fst_apply, d_snd_apply]
        · simp [hom, inv, lift_apply, desc_apply, descCochain_apply, d_fst_apply, d_snd_apply])


-- @@ L112-112 verbatim
end MappingConeCompHomotopyEquiv


-- @@ L114-120 verbatim
/-- The homotopy equivalence between `Cone g` and the cone of `compMor₁ f g : Cone f → Cone (g ∘
f)` (Mathlib's `mappingConeCompHomotopyEquiv`). -/
def mappingConeCompHomotopyEquiv : DGHomotopyEquiv A (Cone g) (Cone (compMor₁ f g)) where
  hom := MappingConeCompHomotopyEquiv.hom f g
  inv := MappingConeCompHomotopyEquiv.inv f g
  homotopyHomInvId := DGHomotopy.ofEq (MappingConeCompHomotopyEquiv.inv_comp_hom f g)
  homotopyInvHomId := MappingConeCompHomotopyEquiv.homotopyInvHomId f g


-- @@ L122-126 verbatim
@[simp]
theorem mappingConeCompHomotopyEquiv_inv_comp_hom :
    (mappingConeCompHomotopyEquiv f g).inv.comp (mappingConeCompHomotopyEquiv f g).hom =
      DGModuleHom.id :=
  MappingConeCompHomotopyEquiv.inv_comp_hom f g


-- @@ L128-134 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- Mathlib's `mappingConeCompHomotopyEquiv_comm₁`. -/
theorem mappingConeCompHomotopyEquiv_comm₁ :
    (mappingConeCompHomotopyEquiv f g).inv.comp (inr (compMor₁ f g)) = compMor₂ f g := by
  refine DGModuleHom.ext fun p => ext_to ?_ ?_
  · simp [mappingConeCompHomotopyEquiv, MappingConeCompHomotopyEquiv.inv, compMor₂, desc_apply]
  · simp [mappingConeCompHomotopyEquiv, MappingConeCompHomotopyEquiv.inv, compMor₂, desc_apply]


-- @@ L136-143 verbatim
/-- Mathlib's `mappingConeCompHomotopyEquiv_comm₂`. -/
theorem mappingConeCompHomotopyEquiv_comm₂ :
    (-fstHom (compMor₁ f g)).comp (mappingConeCompHomotopyEquiv f g).hom = compMor₃ f g := by
  refine DGModuleHom.ext fun p => (unmk 1).injective ?_
  simp only [compMor₃, DGModuleHom.comp_apply, DGModuleHom.neg_apply, unmk_neg,
    DGModuleHom.unmk_shift_apply, ← fst_apply]
  simp [mappingConeCompHomotopyEquiv, MappingConeCompHomotopyEquiv.hom, lift_apply,
    descCochain_apply]


-- @@ L145-145 verbatim
end Cone


-- @@ L147-147 verbatim
end DG
