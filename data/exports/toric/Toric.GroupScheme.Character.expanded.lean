/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
-/
module

public import Mathlib.Algebra.FreeAbelianGroup.Finsupp
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Toric.GroupScheme.Torus


-- @@ L12-14 verbatim
/-!
# The lattices of characters and cocharacters
-/


-- @@ L16-16 verbatim
@[expose] public noncomputable section


-- @@ L18-18 verbatim
open AddMonoidAlgebra CategoryTheory

-- @@ L19-19 verbatim
open scoped Hom


-- @@ L21-21 verbatim
namespace AlgebraicGeometry.Scheme

-- @@ L22-22 verbatim
universe u


-- @@ L24-24 verbatim
section general_base

-- @@ L25-25 verbatim
variable {σ : Type u} {S G H : Scheme.{u}} [G.Over S] [H.Over S]


-- @@ L27-27 verbatim
section GrpObj

-- @@ L28-28 verbatim
variable [GrpObj (G.asOver S)] [GrpObj (H.asOver S)]


-- @@ L30-32 expanded
variable (S G) in
/-- The characters of the group scheme `G` over `S` are the group morphisms `G ⟶/S 𝔾ₘ[S]`. -/
abbrev Char :=
  HomGrp G (SplitTorus S PUnit) S


-- @@ L34-36 expanded
variable (S G) in
/-- The cocharacters of the group scheme `G` over `S` are the group morphisms `𝔾ₘ[S] ⟶/S G`. -/
abbrev Cochar :=
  HomGrp (SplitTorus S PUnit) G S


-- @@ L38-38 verbatim
@[inherit_doc] notation "X("S", "G")" => Char S G

-- @@ L39-39 verbatim
@[inherit_doc] notation "X*("S", "G")" => Cochar S G


-- @@ L41-45 expanded
set_option backward.isDefEq.respectTransparency false in
variable (S) in
/-- Characters of isomorphic group schemes are isomorphic. -/
def charCongr (e : G ≅ H) [e.hom.IsOver S] [IsMonHom <| e.hom.asOver S] : Char S G ≃+ Char S H :=
  HomGrp.congr e (.refl _)


-- @@ L47-50 verbatim
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma charCongr_symm (e : G ≅ H) [e.hom.IsOver S] [IsMonHom <| e.hom.asOver S] :
  (charCongr S e).symm = charCongr S e.symm := rfl


-- @@ L52-56 expanded
variable (S) in
/-- Cocharacters of isomorphic commutative group schemes are isomorphic. -/
def cocharCongr [IsCommMonObj <| G.asOver S] [IsCommMonObj <| H.asOver S] (e : G ≅ H)
    [e.hom.IsOver S] [IsMonHom <| e.hom.asOver S] : Cochar S G ≃+ Cochar S H :=
  HomGrp.congr (.refl _) e


-- @@ L58-61 verbatim
@[simp]
lemma cocharCongr_symm (e : G ≅ H) [IsCommMonObj <| G.asOver S] [IsCommMonObj <| H.asOver S]
    [e.hom.IsOver S] [IsMonHom <| e.hom.asOver S] :
  (cocharCongr S e).symm = cocharCongr S e.symm := rfl


-- @@ L63-68 verbatim
@[simp]
lemma cocharCongr_comp_charCongr [IsCommMonObj <| G.asOver S] [IsCommMonObj <| H.asOver S]
    (e : G ≅ H) [e.hom.IsOver S] [IsMonHom <| e.hom.asOver S] (a b) :
    (cocharCongr S e a).comp (charCongr S e b) = a.comp b := by
  ext
  simp [charCongr, cocharCongr, HomGrp.congr]


-- @@ L70-70 verbatim
end GrpObj


-- @@ L72-72 verbatim
section CommGrpObj

-- @@ L73-73 verbatim
variable [CommGrpObj (G.asOver S)]


-- @@ L75-83 expanded
set_option backward.isDefEq.respectTransparency false in
/-- The perfect pairing between characters and cocharacters, valued in the characters of the
algebraic torus. -/
@[simps]
noncomputable def charPairingAux : Cochar S G →+ Char S G →+ Char S (SplitTorus S PUnit)
    where
  toFun χ := { toFun χ' := χ.comp χ', map_zero' := by simp, map_add' := by simp [HomGrp.add_comp] }
  map_zero' := by ext f; simp
  map_add' χ χ' := by ext; simp [HomGrp.comp_add]


-- @@ L85-85 verbatim
end CommGrpObj

-- @@ L86-86 verbatim
end general_base


-- @@ L88-88 verbatim
section IsDomain

-- @@ L89-90 verbatim
variable {R : CommRingCat.{u}} [IsDomain R] {σ : Type u} {G T : Scheme.{u}} [G.Over (Spec R)]
  [T.Over (Spec R)]


-- @@ L92-92 verbatim
section AddCommGroup

-- @@ L93-93 verbatim
variable {G : Type u} [AddCommGroup G]


-- @@ L95-101 expanded
set_option backward.isDefEq.respectTransparency false in
variable (R G) in
/-- Characters of a diagonal group scheme over a domain are exactly the input group.

Note: This is true over a general base using Cartier duality, but we do not prove that. -/
def charDiag : Char (Spec R) (Diag (Spec R) G) ≃+ G :=
  diagHomEquiv.symm.trans <| FreeAbelianGroup.liftAddEquiv.symm.trans <| .piUnique fun _ ↦ G


-- @@ L103-105 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma charDiag_symm_apply (g : G) :
    (charDiag R G).symm g = diagHomGrp _ (FreeAbelianGroup.lift fun _ ↦ g) := rfl


-- @@ L107-113 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma charDiag_diagHomGrp (f : _ →+ G) : charDiag R G (diagHomGrp _ f) = f (.of 0) := by
  apply (charDiag R G).symm.injective
  simp only [AddEquiv.symm_apply_apply, PUnit.zero_eq, charDiag_symm_apply]
  congr 1
  ext
  simp only [FreeAbelianGroup.lift_apply_of]


-- @@ L115-121 expanded
set_option backward.isDefEq.respectTransparency false in
variable (R G) in
/-- Cocharacters of a diagonal group scheme over a domain are exactly the dual of the input group.

Note: This is true over a general base using Cartier duality, but we do not prove that. -/
def cocharDiag : Cochar (Spec R) (Diag (Spec R) G) ≃+ (G →+ ℤ) :=
  diagHomEquiv.symm.trans <| .addMonoidHomCongrRight <| FreeAbelianGroup.uniqueEquiv _


-- @@ L123-126 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma cocharDiag_symm_apply (g : G →+ ℤ) :
    (cocharDiag R G).symm g =
      diagHomGrp _ ((FreeAbelianGroup.uniqueEquiv _).symm.toAddMonoidHom.comp g) := rfl


-- @@ L128-128 verbatim
end AddCommGroup


-- @@ L130-136 expanded
set_option backward.isDefEq.respectTransparency false in
variable (R σ) in
/-- Characters of the algebraic torus with dimensions `σ`over a domain `R` are exactly `ℤ^σ`.

Note: This is true over a general base using Cartier duality, but we do not prove that. -/
def charTorus : Char (Spec R) (SplitTorus (Spec R) σ) ≃+ (σ →₀ ℤ) :=
  (charDiag R _).trans (FreeAbelianGroup.equivFinsupp _)


-- @@ L138-141 expanded
set_option backward.isDefEq.respectTransparency false in
variable (R) in
def charTorusUnit : Char (Spec R) (SplitTorus (Spec R) PUnit) ≃+ ℤ :=
  (charDiag R _).trans (FreeAbelianGroup.uniqueEquiv _)


-- @@ L143-149 expanded
set_option backward.isDefEq.respectTransparency false in
variable (R σ) in
/-- Cocharacters of the algebraic torus with dimensions `σ`over a domain `R` are exactly `ℤ^σ`.

Note: This is true over a general base using Cartier duality, but we do not prove that. -/
def cocharTorus : Cochar (Spec R) (SplitTorus (Spec R) σ) ≃+ (σ → ℤ) :=
  (cocharDiag R _).trans ⟨FreeAbelianGroup.lift.symm, fun _ _ ↦ rfl⟩


-- @@ L151-151 verbatim
section CommGrpObj

-- @@ L152-152 verbatim
variable [CommGrpObj (G.asOver (Spec R))] [CommGrpObj (T.asOver (Spec R))]


-- @@ L154-171 expanded
set_option backward.isDefEq.respectTransparency false in
variable (R G) in
attribute [local instance 1000000] AddEquivClass.instAddHomClass AddMonoidHomClass.toAddHomClass
    AddEquivClass.instAddMonoidHomClass in
attribute [-simp] charPairingAux_apply_apply in
/-- The `ℤ`-valued perfect pairing between characters and cocharacters of group schemes over a
domain.

Note: This exists over a general base using Cartier duality, but we do not prove that. -/
noncomputable def charPairing : Cochar (Spec R) G →ₗ[ℤ] Char (Spec R) G →ₗ[ℤ] ℤ
    where
  toFun
    x :=
    { toFun y := charTorusUnit (R := R) (charPairingAux (S := Spec R) (G := G) x y)
      map_add' _ _ := by simp only [map_add]
      map_smul' _ _ := by simp only [map_zsmul, smul_eq_mul, eq_intCast, Int.cast_eq] }
  map_add' _
    _ := by ext;
    simp only [map_add, AddMonoidHom.add_apply, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.add_apply]
  map_smul' _
    _ := by ext;
    simp only [map_zsmul, AddMonoidHom.coe_smul, Pi.smul_apply, smul_eq_mul, LinearMap.coe_mk,
      AddHom.coe_mk, eq_intCast, Int.cast_eq, LinearMap.smul_apply]


-- @@ L173-194 verbatim
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance isPerfPair_charPairing [T.IsSplitTorusOver <| Spec ↧R]
    [LocallyOfFiniteType (T ↘ Spec ↧R)] :
    (charPairing R T).IsPerfPair := by
  obtain ⟨σ, _, e, _, _⟩ :=
    exists_iso_diag_finite_of_isSplitTorusOver_locallyOfFiniteType T <| Spec ↧R
  refine .congr (.id (R := ℤ) (M := Module.Dual ℤ (σ →₀ ℤ)))
    ((cocharCongr _ e).trans ((cocharDiag ↧R ℤ[σ]).trans <|
      AddMonoidAlgebra.coeffAddEquiv.addMonoidHomCongrLeft.trans
        (addMonoidHomLequivInt ℤ).toAddEquiv)).toIntLinearEquiv
    ((charCongr _ e).trans <| (charDiag ↧R ℤ[σ]).trans
      AddMonoidAlgebra.coeffAddEquiv).toIntLinearEquiv _ ?_
  ext f x
  apply (charTorusUnit (R := R)).symm.injective
  apply Additive.ofMul.symm.injective
  dsimp [charDiag_symm_apply, charPairing, charTorusUnit, charTorus,
    cocharDiag_symm_apply, AddMonoidAlgebra, CommRingCat.of_carrier]
  simp only [Char, cocharCongr_comp_charCongr, diagHomGrp_comp, charDiag_diagHomGrp, PUnit.zero_eq,
    AddMonoidHom.coe_comp, AddMonoidHom.coe_coe, Function.comp_apply,
    FreeAbelianGroup.lift_apply_of, AddEquiv.symm_apply_apply, EmbeddingLike.apply_eq_iff_eq]
  simp


-- @@ L196-196 verbatim
end CommGrpObj

-- @@ L197-197 verbatim
end IsDomain

-- @@ L198-198 verbatim
end AlgebraicGeometry.Scheme
