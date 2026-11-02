import DG.Derived.ExternalTensorCompact
import DG.Algebra.TensorProductComparison
import DG.Category.Derived.TensorInduction
import DG.Category.Derived.Perfect


-- @@ L6-27 verbatim
/-!
# The derived external tensor product over a commutative ring

Let `R` be a commutative ring and `A`, `B` dg `R`-algebras. The derived external tensor product
over `R`,

`- ⊠ᴸ_R - : D(A) ⥤ D(B) ⥤ D(A ᵍ⊗[R] B)` (`DG.DerivedCategory.externalTensorOver R A B`),

is the derived external tensor product over `ℤ` (`DG.DerivedCategory.externalTensor`) followed by
derived induction along the comparison morphism of dg rings
`A ᵍ⊗[ℤ] B → A ᵍ⊗[R] B`, `a ⊗ b ↦ a ⊗ b` (`DG.GradedTensorProduct.intComparison`). On dg modules
this is the identification `(A ⊗_R B) ⊗_{A ⊗_ℤ B} (M ⊗_ℤ N) = M ⊗_R N` (both are the quotient of
`M ⊗_ℤ N` by the relations `r m ⊗ n = m ⊗ r n`); the dg module structure on `M ⊗_R N` itself is
not formalized here. For `R = ℤ` the comparison morphism is the identity.

* Derived induction along a morphism of dg rings is a triangulated functor
  (`DG.DGRingHom.derivedInduction_isTriangulated`) and preserves compact objects
  (`DG.DGRingHom.isCompact_derivedInduction_obj`).
* Hence `X ⊠ᴸ_R -` and `- ⊠ᴸ_R Y` are triangulated (instances for
  `(externalTensorOver R A B).obj X` and `(externalTensorOver R A B).flip.obj Y`), and
  `X ⊠ᴸ_R Y` is compact for compact `X`, `Y` (`DG.DerivedCategory.isCompact_externalTensorOver`).
-/


-- @@ L29-29 verbatim
open CategoryTheory Limits Pretriangulated

-- @@ L30-30 verbatim
open scoped TensorProduct


-- @@ L32-32 verbatim
universe w w₁ w₂ w₃ w₄ u


-- @@ L34-34 verbatim
noncomputable section


-- @@ L36-36 verbatim
namespace DG


-- @@ L38-38 verbatim
/-! ### Derived induction along a morphism of dg rings -/


-- @@ L40-40 verbatim
namespace CatModule.DerivedCategory


-- @@ L42-43 verbatim
variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]
  [CatModule.HasDerivedCategory.{w₁, u} (SingleObj A)] [DG.HasDerivedCategory.{w, u} A]


-- @@ L45-48 verbatim
/-- The inverse of `D(SingleObj A) ≌ D(A)` commutes with the shifts. -/
noncomputable instance singleObjEquivalence_inverse_commShift :
    (singleObjEquivalence A).inverse.CommShift ℤ :=
  (singleObjEquivalence A).commShiftInverse ℤ


-- @@ L50-51 verbatim
instance singleObjEquivalence_commShift : (singleObjEquivalence A).CommShift ℤ :=
  (singleObjEquivalence A).commShift_of_functor ℤ


-- @@ L53-55 verbatim
/-- `D(SingleObj A) ≌ D(A)` is a triangulated equivalence. -/
instance singleObjEquivalence_isTriangulated : (singleObjEquivalence A).IsTriangulated :=
  Equivalence.IsTriangulated.mk' _ inferInstance


-- @@ L57-57 verbatim
end CatModule.DerivedCategory


-- @@ L59-59 verbatim
namespace DGRingHom


-- @@ L61-62 expanded
variable {A B : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B]
  [DGRing B] (φ : DGRingHom B A)


-- @@ L64-64 verbatim
section Triangulated


-- @@ L66-68 verbatim
variable [CatModule.HasDerivedCategory.{w₁, u} (SingleObj B)]
  [CatModule.HasDerivedCategory.{w₂, u} (SingleObj A)]
  [HasDerivedCategory.{w₃, u} B] [HasDerivedCategory.{w₄, u} A]


-- @@ L70-75 verbatim
/-- Derived induction along a morphism of dg rings commutes with the shifts. -/
noncomputable instance derivedInduction_commShift :
    (φ.derivedInduction.{w₁, w₂, w₃, w₄}).CommShift ℤ :=
  inferInstanceAs (((CatModule.DerivedCategory.singleObjEquivalence B).inverse ⋙
    CatModule.DerivedCategory.induction.{w₁, w₂, u} φ.singleObjFunctor ⋙
      (CatModule.DerivedCategory.singleObjEquivalence A).functor).CommShift ℤ)


-- @@ L77-82 verbatim
/-- **Derived induction along a morphism of dg rings is a triangulated functor.** -/
instance derivedInduction_isTriangulated :
    (φ.derivedInduction.{w₁, w₂, w₃, w₄}).IsTriangulated :=
  inferInstanceAs ((CatModule.DerivedCategory.singleObjEquivalence B).inverse ⋙
    CatModule.DerivedCategory.induction.{w₁, w₂, u} φ.singleObjFunctor ⋙
      (CatModule.DerivedCategory.singleObjEquivalence A).functor).IsTriangulated


-- @@ L84-84 verbatim
end Triangulated


-- @@ L86-86 verbatim
section Compact


-- @@ L88-90 verbatim
variable [CatModule.HasDerivedCategory.{u, u} (SingleObj B)]
  [CatModule.HasDerivedCategory.{u, u} (SingleObj A)]
  [HasDerivedCategory.{u, u} B] [HasDerivedCategory.{u, u} A]


-- @@ L92-97 verbatim
/-- **Derived induction along a morphism of dg rings preserves compact objects.** -/
theorem isCompact_derivedInduction_obj {X : DerivedCategory.{u, u} B} (hX : IsCompact.{u} X) :
    IsCompact.{u} (φ.derivedInduction.{u, u, u, u}.obj X) :=
  IsCompact.map_of_equivalence (CatModule.DerivedCategory.singleObjEquivalence A)
    (CatModule.DerivedCategory.isCompact_induction_obj φ.singleObjFunctor
      (hX.map_of_equivalence (CatModule.DerivedCategory.singleObjEquivalence B).symm))


-- @@ L99-99 verbatim
end Compact


-- @@ L101-101 verbatim
end DGRingHom


-- @@ L103-103 verbatim
/-! ### The derived external tensor product over `R` -/


-- @@ L105-105 verbatim
namespace DerivedCategory


-- @@ L107-109 verbatim
variable (R : Type*) [CommRing R]
  {A B : Type u} [Ring A] [Algebra R A] [DGAddCommGroup A] [DGRing A] [DGAlgebra R A]
  [Ring B] [Algebra R B] [DGAddCommGroup B] [DGRing B] [DGAlgebra R B]


-- @@ L111-111 verbatim
local notation "𝒜" => DGAlgebra.gradingSubmodule ℤ A

-- @@ L112-112 verbatim
local notation "ℬ" => DGAlgebra.gradingSubmodule ℤ B

-- @@ L113-113 verbatim
local notation "𝒜ᵣ" => DGAlgebra.gradingSubmodule R A

-- @@ L114-114 verbatim
local notation "ℬᵣ" => DGAlgebra.gradingSubmodule R B


-- @@ L116-116 verbatim
section Triangulated


-- @@ L118-124 verbatim
variable [HasDerivedCategory.{w, u} A] [HasDerivedCategory.{w, u} B]
  [HasDerivedCategory.{w, u} (DGAlgebra.gradingSubmodule ℤ A ᵍ⊗[ℤ] DGAlgebra.gradingSubmodule ℤ B)]
  [HasDerivedCategory.{w, u} (DGAlgebra.gradingSubmodule R A ᵍ⊗[R] DGAlgebra.gradingSubmodule R B)]
  [CatModule.HasDerivedCategory.{w₁, u}
    (SingleObj (DGAlgebra.gradingSubmodule ℤ A ᵍ⊗[ℤ] DGAlgebra.gradingSubmodule ℤ B))]
  [CatModule.HasDerivedCategory.{w₂, u}
    (SingleObj (DGAlgebra.gradingSubmodule R A ᵍ⊗[R] DGAlgebra.gradingSubmodule R B))]


-- @@ L126-133 verbatim
variable (A B) in
/-- **The derived external tensor product over `R`**, `D(A) ⥤ D(B) ⥤ D(A ᵍ⊗[R] B)`: the derived
external tensor product over `ℤ` followed by derived induction along
`A ᵍ⊗[ℤ] B → A ᵍ⊗[R] B`. -/
def externalTensorOver : DerivedCategory.{w, u} A ⥤ DerivedCategory.{w, u} B ⥤
    DerivedCategory.{w, u} (𝒜ᵣ ᵍ⊗[R] ℬᵣ) :=
  externalTensor A B ⋙ (Functor.whiskeringRight _ _ _).obj
    (GradedTensorProduct.intComparison R A B).derivedInduction.{w₁, w₂, w, w}


-- @@ L135-139 verbatim
theorem externalTensorOver_obj_obj (X : DerivedCategory.{w, u} A)
    (Y : DerivedCategory.{w, u} B) :
    ((externalTensorOver R A B).obj X).obj Y =
      (GradedTensorProduct.intComparison R A B).derivedInduction.{w₁, w₂, w, w}.obj
        (((externalTensor A B).obj X).obj Y) := rfl


-- @@ L141-145 verbatim
/-- `X ⊠ᴸ_R -` commutes with the shifts. -/
noncomputable instance externalTensorOver_obj_commShift (X : DerivedCategory.{w, u} A) :
    ((externalTensorOver R A B).obj X).CommShift ℤ :=
  inferInstanceAs (((externalTensor A B).obj X ⋙
    (GradedTensorProduct.intComparison R A B).derivedInduction.{w₁, w₂, w, w}).CommShift ℤ)


-- @@ L147-151 verbatim
/-- **`X ⊠ᴸ_R -` is a triangulated functor**, for every `X ∈ D(A)`. -/
instance externalTensorOver_obj_isTriangulated (X : DerivedCategory.{w, u} A) :
    ((externalTensorOver R A B).obj X).IsTriangulated :=
  inferInstanceAs ((externalTensor A B).obj X ⋙
    (GradedTensorProduct.intComparison R A B).derivedInduction.{w₁, w₂, w, w}).IsTriangulated


-- @@ L153-160 verbatim
variable (A) in
/-- `- ⊠ᴸ_R Y` is `- ⊠ᴸ Y` followed by derived induction. -/
def externalTensorOverFlipObjIso (Y : DerivedCategory.{w, u} B) :
    (externalTensorOver R A B).flip.obj Y ≅
      (externalTensor A B).flip.obj Y ⋙
        (GradedTensorProduct.intComparison R A B).derivedInduction.{w₁, w₂, w, w} :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun _ =>
    (Category.comp_id _).trans (Category.id_comp _).symm


-- @@ L162-165 verbatim
/-- `- ⊠ᴸ_R Y` commutes with the shifts. -/
noncomputable instance externalTensorOver_flip_obj_commShift (Y : DerivedCategory.{w, u} B) :
    ((externalTensorOver R A B).flip.obj Y).CommShift ℤ :=
  Functor.CommShift.ofIso (externalTensorOverFlipObjIso R A Y).symm ℤ


-- @@ L167-169 verbatim
instance (Y : DerivedCategory.{w, u} B) :
    NatTrans.CommShift (externalTensorOverFlipObjIso R A Y).symm.hom ℤ :=
  Functor.CommShift.ofIso_compatibility _ ℤ


-- @@ L171-174 verbatim
/-- **`- ⊠ᴸ_R Y` is a triangulated functor**, for every `Y ∈ D(B)`. -/
instance externalTensorOver_flip_obj_isTriangulated (Y : DerivedCategory.{w, u} B) :
    ((externalTensorOver R A B).flip.obj Y).IsTriangulated :=
  Functor.isTriangulated_of_iso (externalTensorOverFlipObjIso R A Y).symm


-- @@ L176-176 verbatim
end Triangulated


-- @@ L178-178 verbatim
section Compact


-- @@ L180-186 verbatim
variable [HasDerivedCategory.{u, u} A] [HasDerivedCategory.{u, u} B]
  [HasDerivedCategory.{u, u} (DGAlgebra.gradingSubmodule ℤ A ᵍ⊗[ℤ] DGAlgebra.gradingSubmodule ℤ B)]
  [HasDerivedCategory.{u, u} (DGAlgebra.gradingSubmodule R A ᵍ⊗[R] DGAlgebra.gradingSubmodule R B)]
  [CatModule.HasDerivedCategory.{u, u}
    (SingleObj (DGAlgebra.gradingSubmodule ℤ A ᵍ⊗[ℤ] DGAlgebra.gradingSubmodule ℤ B))]
  [CatModule.HasDerivedCategory.{u, u}
    (SingleObj (DGAlgebra.gradingSubmodule R A ᵍ⊗[R] DGAlgebra.gradingSubmodule R B))]


-- @@ L188-193 verbatim
/-- **The derived external tensor product over `R` of compact objects is compact.** -/
theorem isCompact_externalTensorOver {X : DerivedCategory.{u, u} A}
    {Y : DerivedCategory.{u, u} B} (hX : IsCompact.{u} X) (hY : IsCompact.{u} Y) :
    IsCompact.{u} (((externalTensorOver R A B).obj X).obj Y) :=
  (GradedTensorProduct.intComparison R A B).isCompact_derivedInduction_obj
    (isCompact_externalTensor hX hY)


-- @@ L195-195 verbatim
end Compact


-- @@ L197-197 verbatim
end DerivedCategory


-- @@ L199-199 verbatim
end DG
