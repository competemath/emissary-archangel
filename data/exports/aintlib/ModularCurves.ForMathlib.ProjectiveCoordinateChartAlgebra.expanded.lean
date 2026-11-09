/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex, AINTLIB ModularCurves project

Adapted from Clawristotle's
`CoherentCohomologyFinite.ProjectiveCoordinateChartAlgebra`.
-/
import ModularCurves.ForMathlib.ProjectiveStandardIntersectionRing


-- @@ L11-17 verbatim
/-!
# Algebra on a standard projective coordinate chart

The standard coordinate ratios define a dehomogenization map to the degree-zero
homogeneous localization. AINTLIB's existing projective chart equivalence gives
a short proof that this map is surjective.
-/


-- @@ L19-19 verbatim
open HomogeneousLocalization


-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
universe u v


-- @@ L25-25 verbatim
namespace MvPolynomial


-- @@ L27-27 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra


-- @@ L29-32 verbatim
/-- The coordinate ring of the standard chart `D₊(Xᵢ)`. -/
abbrev ProjectiveCoordinateAway
    (R : Type u) [CommRing R] {σ : Type v} (i : σ) :=
  Away (homogeneousSubmodule σ R) (X i)


-- @@ L34-44 verbatim
/-- The regular function `Xⱼ / Xᵢ` on the standard chart `D₊(Xᵢ)`. -/
@[reducible]
def projectiveCoordinateRatio
    (R : Type u) [CommRing R] {σ : Type v} (i j : σ) :
    ProjectiveCoordinateAway R i :=
  Away.mk
    (homogeneousSubmodule σ R)
    (X_mem_homogeneousSubmodule_one R i)
    1
    (X j)
    (by simpa using X_mem_homogeneousSubmodule_one R j)


-- @@ L46-51 verbatim
@[simp]
lemma projectiveCoordinateRatio_self
    (R : Type u) [CommRing R] {σ : Type v} (i : σ) :
    projectiveCoordinateRatio R i i = 1 := by
  apply HomogeneousLocalization.val_injective
  simp [projectiveCoordinateRatio, HomogeneousLocalization.Away.val_mk]


-- @@ L53-57 verbatim
/-- Dehomogenize by sending every variable `Xⱼ` to the ratio `Xⱼ / Xᵢ`. -/
noncomputable def projectiveCoordinateDehomogenization
    (R : Type u) [CommRing R] {σ : Type v} (i : σ) :
    MvPolynomial σ R →ₐ[R] ProjectiveCoordinateAway R i :=
  MvPolynomial.aeval (projectiveCoordinateRatio R i)


-- @@ L59-64 verbatim
@[simp]
lemma projectiveCoordinateDehomogenization_X
    (R : Type u) [CommRing R] {σ : Type v} (i j : σ) :
    projectiveCoordinateDehomogenization R i (X j) =
      projectiveCoordinateRatio R i j := by
  simp [projectiveCoordinateDehomogenization]


-- @@ L66-73 verbatim
/-- A nonanchor ratio is AINTLIB's affine projective-chart variable. -/
lemma projectiveCoordinateRatio_ne
    (R : Type u) [CommRing R] {σ : Type v} (i : σ)
    (j : {j : σ // j ≠ i}) :
    projectiveCoordinateRatio R i j = awayVar R i j := by
  apply HomogeneousLocalization.val_injective
  simp [projectiveCoordinateRatio, awayVar,
    HomogeneousLocalization.Away.val_mk]


-- @@ L75-91 verbatim
/-- Dehomogenization after including the nonanchor variables is the landed homogenization map. -/
lemma projectiveCoordinateDehomogenization_comp_rename
    (R : Type u) [CommRing R] {σ : Type v} (i : σ) :
    (projectiveCoordinateDehomogenization R i).toRingHom.comp
        (rename (Subtype.val : {j : σ // j ≠ i} → σ)).toRingHom =
      homogenizeAt R i := by
  letI : DecidableEq σ := Classical.decEq σ
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [projectiveCoordinateDehomogenization, homogenizeAt,
      algebraMap_homogeneousAway_X_eq_awayConst]
    rfl
  · intro j
    apply HomogeneousLocalization.val_injective
    simp [projectiveCoordinateDehomogenization,
      projectiveCoordinateRatio, homogenizeAt, awayVar,
      HomogeneousLocalization.Away.val_mk]


-- @@ L93-107 verbatim
/-- Dehomogenization onto a standard projective coordinate chart is surjective. -/
lemma projectiveCoordinateDehomogenization_surjective
    (R : Type u) [CommRing R] {σ : Type v} (i : σ) :
    Function.Surjective (projectiveCoordinateDehomogenization R i) := by
  letI : DecidableEq σ := Classical.decEq σ
  intro x
  let p := chartRingEquiv R i x
  refine ⟨rename (Subtype.val : {j : σ // j ≠ i} → σ) p, ?_⟩
  change (projectiveCoordinateDehomogenization R i).toRingHom
    ((rename (Subtype.val : {j : σ // j ≠ i} → σ)).toRingHom p) = x
  calc
    _ = homogenizeAt R i p :=
      RingHom.congr_fun
        (projectiveCoordinateDehomogenization_comp_rename R i) p
    _ = x := (chartRingEquiv R i).symm_apply_apply x


-- @@ L109-109 verbatim
end MvPolynomial
