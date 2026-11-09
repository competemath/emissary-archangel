import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.Biproducts
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import ModularCurves.ForMathlib.AcyclicAffineOpenCover


-- @@ L7-13 verbatim
/-!
# Concrete Cech cochains on topological spaces

This file gives an elementwise description of mathlib's Cech complex for presheaves of
abelian groups and connects its intersection opens to affine quasicoherent vanishing.
The construction follows mathlib PR #35073, specialized to the API needed here.
-/


-- @@ L15-15 verbatim
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite


-- @@ L17-17 verbatim
universe v u


-- @@ L19-19 verbatim
namespace AddCommGrpCat


-- @@ L21-25 verbatim
/-- The categorical product of additive commutative groups is isomorphic to the
corresponding dependent function group. -/
noncomputable def productIsoPi {ι : Type u} (X : ι → AddCommGrpCat.{u}) :
    ∏ᶜ X ≅ .of (∀ i, X i) :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _) (HasLimit.productLimitCone X).isLimit


-- @@ L27-33 verbatim
/-- The forward product isomorphism is componentwise projection. -/
@[simp]
theorem productIsoPi_hom_apply {ι : Type u} (X : ι → AddCommGrpCat.{u})
    (x : (∏ᶜ X :)) (i : ι) : (productIsoPi X).hom x i = Pi.π X i x :=
  ConcreteCategory.congr_hom
    (IsLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit _)
      (HasLimit.productLimitCone X).isLimit ⟨i⟩) x


-- @@ L35-41 verbatim
/-- Every component of the inverse product isomorphism is evaluation. -/
@[simp]
theorem productIsoPi_inv_apply {ι : Type u} (X : ι → AddCommGrpCat.{u})
    (x : ∀ i, X i) (i : ι) : Pi.π X i ((productIsoPi X).inv x) = x i :=
  ConcreteCategory.congr_hom
    (IsLimit.conePointUniqueUpToIso_inv_comp (limit.isLimit _)
      (HasLimit.productLimitCone X).isLimit ⟨i⟩) x


-- @@ L43-43 verbatim
end AddCommGrpCat


-- @@ L45-45 verbatim
namespace TopologicalSpace


-- @@ L47-47 verbatim
variable {T : Type u} [TopologicalSpace T]

-- @@ L48-48 verbatim
variable (F : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{u}) {ι : Type u}

-- @@ L49-49 verbatim
variable (U : ι → Opens T) (n : ℕ)


-- @@ L51-58 verbatim
/-- Degree `n` of the Cech complex consists of families of sections indexed by
`(n + 1)`-tuples of cover indices. -/
noncomputable def cechCochainAddEquiv :
    ((cechComplexFunctor U).obj F).X n ≃+
      ∀ i : Fin (n + 1) → ι,
        F.obj (op (∏ᶜ fun k : Fin (n + 1) => U (i k))) :=
  (AddCommGrpCat.productIsoPi fun i : Fin (n + 1) → ι =>
    F.obj (op (∏ᶜ fun k : Fin (n + 1) => U (i k)))).addCommGroupIsoToAddEquiv


-- @@ L60-66 verbatim
@[simp]
theorem cechCochainAddEquiv_apply
    (x : ((cechComplexFunctor U).obj F).X n) (i : Fin (n + 1) → ι) :
    cechCochainAddEquiv F U n x i =
      Pi.π (fun i : Fin (n + 1) → ι =>
        F.obj (op (∏ᶜ fun k : Fin (n + 1) => U (i k)))) i x :=
  AddCommGrpCat.productIsoPi_hom_apply _ _ _


-- @@ L68-76 verbatim
@[simp]
theorem cechCochainAddEquiv_symm_apply_component
    (x : ∀ i : Fin (n + 1) → ι,
      F.obj (op (∏ᶜ fun k : Fin (n + 1) => U (i k))))
    (i : Fin (n + 1) → ι) :
    Pi.π (fun i : Fin (n + 1) → ι =>
      F.obj (op (∏ᶜ fun k : Fin (n + 1) => U (i k)))) i
        ((cechCochainAddEquiv F U n).symm x) = x i :=
  AddCommGrpCat.productIsoPi_inv_apply _ _ _


-- @@ L78-80 verbatim
private noncomputable def Opens.piObjIsoIInf {κ : Type v} (V : κ → Opens T) :
    ∏ᶜ V ≅ ⨅ k, V k :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _) (Preorder.isLimitIInf V)


-- @@ L82-84 verbatim
theorem Opens.piObj_eq_iInf {κ : Type v} (V : κ → Opens T) :
    (∏ᶜ V) = ⨅ k, V k :=
  (Opens.piObjIsoIInf V).to_eq


-- @@ L86-86 verbatim
end TopologicalSpace


-- @@ L88-88 verbatim
namespace AlgebraicGeometry


-- @@ L90-99 verbatim
/-- In a separated scheme, the product open attached to a Cech tuple of affine opens is
affine. -/
theorem IsAffineOpen.cechIntersection {X : Scheme.{u}} [X.IsSeparated] {ι : Type u}
    (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (n : ℕ)
    (i : Fin (n + 1) → ι) :
    IsAffineOpen (∏ᶜ fun k : Fin (n + 1) => U (i k)) := by
  rw [show (∏ᶜ fun k : Fin (n + 1) => U (i k)) =
      ⨅ k : Fin (n + 1), U (i k) from
    TopologicalSpace.Opens.piObj_eq_iInf _]
  exact IsAffineOpen.iInf (fun k ↦ hU (i k))


-- @@ L101-101 verbatim
namespace Scheme.Modules


-- @@ L103-111 verbatim
/-- Every Cech intersection of an affine cover is acyclic for a quasicoherent module. -/
theorem cechIntersection_subsingleton_H {X : Scheme.{u}} [X.IsSeparated]
    (M : X.Modules) [M.IsQuasicoherent] {ι : Type u}
    (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (n : ℕ)
    (i : Fin (n + 1) → ι) (r : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H
      ((TopCat.Sheaf.restrict AddCommGrpCat
        (∏ᶜ fun k : Fin (n + 1) => U (i k)).isOpenEmbedding).obj M.sheaf) (r + 1)) :=
  restrict_subsingleton_H_of_isAffineOpen M _ (IsAffineOpen.cechIntersection U hU n i) r


-- @@ L113-113 verbatim
end Scheme.Modules


-- @@ L115-115 verbatim
end AlgebraicGeometry
