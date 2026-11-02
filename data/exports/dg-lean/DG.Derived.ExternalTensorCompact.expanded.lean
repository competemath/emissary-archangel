import DG.Derived.ExternalTensorTriangulated
import DG.Derived.Perfect


-- @@ L4-18 verbatim
/-!
# The derived external tensor product preserves compact objects

For dg rings `A`, `B` and `A ⊗ B = A ᵍ⊗[ℤ] B`, if `X ∈ D(A)` and `Y ∈ D(B)` are compact, then
`X ⊠ᴸ Y` is compact in `D(A ⊗ B)` (`DG.DerivedCategory.isCompact_externalTensor`).

The compact objects of `D(A)` are the thick closure of `A`
(`DG.DerivedCategory.thickClosure_self_eq_isCompact`), and the preimage of a thick subcategory
under a triangulated functor is thick (`DG.IsThick.comap`). Since `- ⊠ᴸ B` is triangulated and
`A ⊠ᴸ B ≅ A ⊗ B` is compact, `X ⊠ᴸ B` is compact for compact `X`; since `X ⊠ᴸ -` is
triangulated, `X ⊠ᴸ Y` is compact for compact `Y`.

Compactness refers to coproducts indexed by types in the universe `u` of the rings, so the
derived categories are the models with morphisms in `Type u` (`[HasDerivedCategory.{u, u} A]`).
-/


-- @@ L20-20 verbatim
open CategoryTheory Limits Pretriangulated

-- @@ L21-21 verbatim
open scoped TensorProduct


-- @@ L23-23 verbatim
universe u


-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-27 verbatim
namespace DG


-- @@ L29-29 verbatim
section Comap


-- @@ L31-35 verbatim
variable {C D : Type*} [Category C] [Category D]
  [HasZeroObject C] [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]
  [HasZeroObject D] [HasShift D ℤ] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D]


-- @@ L37-43 verbatim
/-- The preimage of a thick property under a triangulated functor is thick. -/
theorem IsThick.comap (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] {P : ObjectProperty D}
    (hP : IsThick P) : IsThick fun X => P (F.obj X) where
  zero := hP.of_isZero (F.map_isZero (isZero_zero C))
  shift X n h := hP.of_iso ((F.commShiftIso n).app X) (hP.shift _ n h)
  ext₂ T hT h₁ h₃ := hP.ext₂ _ (F.map_distinguished T hT) h₁ h₃
  retract e h := hP.retract (e.map F) h


-- @@ L45-45 verbatim
end Comap


-- @@ L47-47 verbatim
namespace DerivedCategory


-- @@ L49-50 verbatim
variable {A B : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B]
  [DGRing B]


-- @@ L52-52 verbatim
local notation "𝒜" => DGAlgebra.gradingSubmodule ℤ A

-- @@ L53-53 verbatim
local notation "ℬ" => DGAlgebra.gradingSubmodule ℤ B

-- @@ L54-54 verbatim
local notation "AB" => 𝒜 ᵍ⊗[ℤ] ℬ


-- @@ L56-57 verbatim
variable [HasDerivedCategory.{u, u} A] [HasDerivedCategory.{u, u} B]
  [HasDerivedCategory.{u, u} (DGAlgebra.gradingSubmodule ℤ A ᵍ⊗[ℤ] DGAlgebra.gradingSubmodule ℤ B)]


-- @@ L59-71 verbatim
theorem isCompact_externalTensor_obj_Q_self {X : DerivedCategory.{u, u} A}
    (hX : IsCompact.{u} X) :
    IsCompact.{u} (((externalTensor A B).obj X).obj (Q.obj (DGModuleCat.of B B))) := by
  have hP : IsThick fun X : DerivedCategory.{u, u} A =>
      IsCompact.{u} (((externalTensor A B).flip.obj (Q.obj (DGModuleCat.of B B))).obj X) :=
    (isThick_isCompact _).comap _
  have hX' : ThickClosure
      (fun Y : DerivedCategory.{u, u} A => ∃ _ : Unit, Q.obj (DGModuleCat.of A A) = Y) X := by
    rw [thickClosure_self_eq_isCompact]
    exact hX
  refine thickClosure_le hP ?_ X hX'
  rintro _ ⟨-, rfl⟩
  exact isCompact_Q_self.of_iso externalTensorRegularIso


-- @@ L73-86 verbatim
/-- **The derived external tensor product of compact objects is compact.** -/
theorem isCompact_externalTensor {X : DerivedCategory.{u, u} A} {Y : DerivedCategory.{u, u} B}
    (hX : IsCompact.{u} X) (hY : IsCompact.{u} Y) :
    IsCompact.{u} (((externalTensor A B).obj X).obj Y) := by
  have hP : IsThick fun Y : DerivedCategory.{u, u} B =>
      IsCompact.{u} (((externalTensor A B).obj X).obj Y) :=
    (isThick_isCompact _).comap _
  have hY' : ThickClosure
      (fun Y : DerivedCategory.{u, u} B => ∃ _ : Unit, Q.obj (DGModuleCat.of B B) = Y) Y := by
    rw [thickClosure_self_eq_isCompact]
    exact hY
  refine thickClosure_le hP ?_ Y hY'
  rintro _ ⟨-, rfl⟩
  exact isCompact_externalTensor_obj_Q_self hX


-- @@ L88-88 verbatim
end DerivedCategory


-- @@ L90-90 verbatim
end DG
