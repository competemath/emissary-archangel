/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AlgebraicGeometry.ProjectiveSpace.Basic
import Oka.Analytification.SchemeAffine


-- @@ L9-17 verbatim
/-!
# Projective space over `ℂ` as a scheme locally of finite type

`ComplexAnalytic.projectiveSpace n` is `ℙ(n; ℂ) = Proj ℂ[X₀, …, Xₙ]` (with `ℂ` lifted to
universe `u`), as an object of `ComplexAnalytic.SchemeLFTℂ.{u}`; its structure morphism is proper
(`ComplexAnalytic.isProper_projectiveSpace_hom`). The standard charts are morphisms
`ComplexAnalytic.projectiveSpaceChart i : affineSpace n ⟶ projectiveSpace n` over `ℂ` from affine
space `affineSpace n = Spec ℂ[Y₀, …, Yₙ₋₁]`.
-/


-- @@ L19-19 verbatim
open CategoryTheory AlgebraicGeometry


-- @@ L21-21 verbatim
universe u


-- @@ L23-23 verbatim
namespace ComplexAnalytic


-- @@ L25-28 verbatim
/-- **Affine `n`-space over `ℂ`**, `Spec ℂ[Y₀, …, Yₙ₋₁]`, as a scheme locally of finite type. -/
noncomputable def affineSpace (n : ℕ) : SchemeLFTℂ.{u} :=
  SchemeLFTℂ.spec (CommRingCat.ofHom (MvPolynomial.C (σ := Fin n) (R := ULift.{u} ℂ)))
    (RingHom.finiteType_algebraMap.mpr inferInstance)


-- @@ L30-33 verbatim
@[simp]
lemma affineSpace_obj_hom (n : ℕ) :
    (affineSpace.{u} n).obj.hom = Spec.map (CommRingCat.ofHom MvPolynomial.C) :=
  rfl


-- @@ L35-38 verbatim
/-- **Projective `n`-space over `ℂ`**, `Proj ℂ[X₀, …, Xₙ]`, as a scheme locally of finite type. -/
noncomputable def projectiveSpace (n : ℕ) : SchemeLFTℂ.{u} :=
  ⟨Over.mk (ProjectiveSpace.toSpec n (ULift.{u} ℂ)),
    show LocallyOfFiniteType (ProjectiveSpace.toSpec n _) from inferInstance⟩


-- @@ L40-43 expanded
@[simp]
lemma projectiveSpace_obj_left (n : ℕ) :
    (projectiveSpace.{u} n).obj.left = ProjectiveSpace n (ULift.{u} ℂ) :=
  rfl


-- @@ L45-48 verbatim
@[simp]
lemma projectiveSpace_obj_hom (n : ℕ) :
    (projectiveSpace.{u} n).obj.hom = ProjectiveSpace.toSpec n (ULift.{u} ℂ) :=
  rfl


-- @@ L50-51 verbatim
instance isProper_projectiveSpace_hom (n : ℕ) : IsProper (projectiveSpace.{u} n).obj.hom :=
  inferInstanceAs (IsProper (ProjectiveSpace.toSpec n _))


-- @@ L53-57 verbatim
/-- The **standard chart** `i` of `ℙⁿ`, `𝔸ⁿ ⟶ ℙⁿ` over `ℂ`, an open immersion onto
`ProjectiveSpace.U n _ i = D₊(Xᵢ)`. -/
noncomputable def projectiveSpaceChart {n : ℕ} (i : Fin (n + 1)) :
    affineSpace.{u} n ⟶ projectiveSpace.{u} n :=
  ObjectProperty.homMk (Over.homMk (ProjectiveSpace.chart i) (ProjectiveSpace.chart_toSpec i))


-- @@ L59-62 verbatim
@[simp]
lemma projectiveSpaceChart_hom_left {n : ℕ} (i : Fin (n + 1)) :
    (projectiveSpaceChart.{u} i).hom.left = ProjectiveSpace.chart i :=
  rfl


-- @@ L64-65 verbatim
instance {n : ℕ} (i : Fin (n + 1)) : IsOpenImmersion (projectiveSpaceChart.{u} i).hom.left :=
  inferInstanceAs (IsOpenImmersion (ProjectiveSpace.chart i))


-- @@ L67-67 verbatim
end ComplexAnalytic
