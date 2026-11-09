/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PointsDictionary


-- @@ L8-27 verbatim
/-!
# Galois naturality of the field-points dictionary (DS4 M1c, node A)

The field-points dictionary `projModelPointsEquiv W K` identifies the `K`-points of the
projective Weierstrass model with mathlib's affine points `(W ⊗ K).toAffine.Point`. This
file proves it is **natural in `K`** for a base-algebra automorphism `σ : K ≃ₐ[R] K`,
where the two actions are

* on `K`-points of the model: `g ↦ Spec σ ≫ g` (precomposition — contravariance of `Spec`);
* on affine points: `WeierstrassCurve.Affine.Point.map σ` (coordinatewise).

The dictionary is pinned by exactly two value lemmas
(`projModelPointsEquiv_infinity` / `_some`), so the proof is a two-case argument. The
only substantive step is that the chart hom conjugates (`chartHomEquiv_specMap_comp`);
the coordinate readout is then definitional, because the `Z`-chart solution at index `j`
is literally `φ` applied to a **fixed** element of the away-algebra.

Everything is split into one-step lemmas: this region of the development is
elaboration-fragile and heartbeat bumps are not permitted.
-/


-- @@ L29-29 verbatim
universe u


-- @@ L31-31 verbatim
open CategoryTheory AlgebraicGeometry Limits HomogeneousLocalization HomogeneousIdeal


-- @@ L33-33 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra


-- @@ L35-35 verbatim
namespace ModularCurves


-- @@ L37-37 verbatim
variable {R : Type u} [CommRing R]


-- @@ L39-39 verbatim
/-! ## A1 — `Spec` of a ring isomorphism is an isomorphism -/


-- @@ L41-48 verbatim
/-- `Spec.map` of the underlying hom of a ring equivalence has `Spec.map` of the inverse
as a two-sided inverse. -/
theorem specMap_ofHom_ringEquiv_comp {K : Type u} [CommRing K] (σ : K ≃+* K) :
    Spec.map (CommRingCat.ofHom (σ.symm : K →+* K)) ≫
        Spec.map (CommRingCat.ofHom (σ : K →+* K)) = 𝟙 _ := by
  rw [← Spec.map_comp, show (CommRingCat.ofHom (σ : K →+* K) ≫
      CommRingCat.ofHom (σ.symm : K →+* K)) = 𝟙 (CommRingCat.of K) from
    CommRingCat.hom_ext (RingHom.ext fun x => σ.symm_apply_apply x), Spec.map_id]


-- @@ L50-53 verbatim
theorem specMap_ofHom_ringEquiv_comp' {K : Type u} [CommRing K] (σ : K ≃+* K) :
    Spec.map (CommRingCat.ofHom (σ : K →+* K)) ≫
        Spec.map (CommRingCat.ofHom (σ.symm : K →+* K)) = 𝟙 _ := by
  simpa using specMap_ofHom_ringEquiv_comp σ.symm


-- @@ L55-59 verbatim
/-- **(A1)** `Spec` of a ring isomorphism is an isomorphism of schemes. -/
instance isIso_specMap_ofHom_ringEquiv {K : Type u} [CommRing K] (σ : K ≃+* K) :
    IsIso (Spec.map (CommRingCat.ofHom (σ : K →+* K))) :=
  ⟨Spec.map (CommRingCat.ofHom (σ.symm : K →+* K)),
    specMap_ofHom_ringEquiv_comp' σ, specMap_ofHom_ringEquiv_comp σ⟩


-- @@ L61-61 verbatim
/-! ## The `σ`-translate of a `K`-point of the model -/


-- @@ L63-63 verbatim
variable (W : WeierstrassCurve R)


-- @@ L65-73 verbatim
/-- The `σ`-translate of a `K`-point of the projective model: precomposition with
`Spec σ`. The structure condition survives because `σ` is `R`-linear. -/
noncomputable def specMapCompPoint {K : Type u} [CommRing K] [Algebra R K]
    (σ : K ≃ₐ[R] K) (g : SpecPoints (projModel W) (projModelπ W) K) :
    SpecPoints (projModel W) (projModelπ W) K :=
  ⟨Spec.map (CommRingCat.ofHom (σ : K →+* K)) ≫ g.1, by
    rw [Category.assoc, g.2, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun c => σ.commutes c)⟩


-- @@ L75-78 verbatim
@[simp] theorem specMapCompPoint_coe {K : Type u} [CommRing K] [Algebra R K]
    (σ : K ≃ₐ[R] K) (g : SpecPoints (projModel W) (projModelπ W) K) :
    (specMapCompPoint W σ g).1 =
      Spec.map (CommRingCat.ofHom (σ : K →+* K)) ≫ g.1 := rfl


-- @@ L80-80 verbatim
/-! ## A2 — the `Z`-chart condition is invariant -/


-- @@ L82-88 verbatim
/-- **(A2, →)** If `g` factors through the `Z`-chart then so does its `σ`-translate. -/
theorem inZChart_specMapCompPoint {K : Type u} [CommRing K] [Algebra R K]
    (σ : K ≃ₐ[R] K) {g : SpecPoints (projModel W) (projModelπ W) K} (hZ : InZChart W g) :
    InZChart W (specMapCompPoint W σ g) := by
  obtain ⟨h, hfac⟩ := hZ
  exact ⟨Spec.map (CommRingCat.ofHom (σ : K →+* K)) ≫ h, by
    rw [Category.assoc, hfac, specMapCompPoint_coe]⟩


-- @@ L90-100 verbatim
/-- **(A2, ←)** and conversely, since `Spec σ` is an isomorphism (A1). -/
theorem inZChart_of_inZChart_specMapCompPoint {K : Type u} [CommRing K] [Algebra R K]
    (σ : K ≃ₐ[R] K) {g : SpecPoints (projModel W) (projModelπ W) K}
    (hZ : InZChart W (specMapCompPoint W σ g)) : InZChart W g := by
  obtain ⟨h, hfac⟩ := hZ
  refine ⟨Spec.map (CommRingCat.ofHom ((σ.symm : K ≃+* K) : K →+* K)) ≫ h, ?_⟩
  rw [Category.assoc, hfac, specMapCompPoint_coe, ← Category.assoc,
    show Spec.map (CommRingCat.ofHom ((σ.symm : K ≃+* K) : K →+* K)) ≫
        Spec.map (CommRingCat.ofHom (σ : K →+* K)) = 𝟙 _ from
      specMap_ofHom_ringEquiv_comp (σ : K ≃+* K),
    Category.id_comp]


-- @@ L102-106 verbatim
/-- **(A2)** The `Z`-chart condition is invariant under the `σ`-action. -/
theorem inZChart_specMapCompPoint_iff {K : Type u} [CommRing K] [Algebra R K]
    (σ : K ≃ₐ[R] K) (g : SpecPoints (projModel W) (projModelπ W) K) :
    InZChart W (specMapCompPoint W σ g) ↔ InZChart W g :=
  ⟨inZChart_of_inZChart_specMapCompPoint W σ, inZChart_specMapCompPoint W σ⟩


-- @@ L108-108 verbatim
/-! ## A3 — the chart hom conjugates -/


-- @@ L110-125 verbatim
/-- **(A3)** The `Z`-chart hom of the `σ`-translate is `σ ∘ φ`. -/
theorem chartHomEquiv_specMapCompPoint {K : Type u} [CommRing K] [Algebra R K]
    (σ : K ≃ₐ[R] K) (g : SpecPoints (projModel W) (projModelπ W) K) (hZ : InZChart W g) :
    (chartHomEquiv W 2 K ⟨specMapCompPoint W σ g,
        inZChart_specMapCompPoint W σ hZ⟩).1 =
      (σ : K →+* K).comp (chartHomEquiv W 2 K ⟨g, hZ⟩).1 := by
  refine congrArg Subtype.val (chartHomEquiv_eq_of_specMap W 2
    ⟨specMapCompPoint W σ g, inZChart_specMapCompPoint W σ hZ⟩
    ⟨(σ : K →+* K).comp (chartHomEquiv W 2 K ⟨g, hZ⟩).1, ?_⟩ ?_)
  · rw [RingHom.comp_assoc, (chartHomEquiv W 2 K ⟨g, hZ⟩).2]
    exact RingHom.ext fun c => σ.commutes c
  · rw [show CommRingCat.ofHom ((σ : K →+* K).comp (chartHomEquiv W 2 K ⟨g, hZ⟩).1) =
        CommRingCat.ofHom (chartHomEquiv W 2 K ⟨g, hZ⟩).1 ≫
          CommRingCat.ofHom (σ : K →+* K) from rfl,
      Spec.map_comp, Category.assoc, chartHomEquiv_specMap_factors W 2 ⟨g, hZ⟩]
    rfl


-- @@ L127-127 verbatim
/-! ## A4 — the coordinate readout transforms by `σ` -/


-- @@ L129-140 verbatim
/-- The `Z`-chart solution at index `j` is the chart hom applied to a **fixed** element
of the away-algebra — the readout is definitional. -/
theorem chartSolutionsEquiv_apply_eq {K : Type u} [CommRing K] [Algebra R K]
    (gZ : { g : SpecPoints (projModel W) (projModelπ W) K //
      ∃ h : Spec (.of K) ⟶ Spec (.of (Away (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))),
        h ≫ Proj.awayι (quotientGrading (projIdeal W)) _
          (mk_X_mem_quotientGrading_one W 2) one_pos = g.1 })
    (j : {j : Fin 3 // j ≠ 2}) :
    (chartSolutionsEquiv W 2 K (chartHomEquiv W 2 K gZ)).1 j =
      (chartHomEquiv W 2 K gZ).1
        (chartCoordEquiv W 2 (Ideal.Quotient.mk _ (MvPolynomial.X j))) := rfl


-- @@ L142-151 verbatim
/-- **(A4)** Hence the `Z`-chart coordinates of the `σ`-translate are the `σ`-images. -/
theorem chartSolution_specMapCompPoint {K : Type u} [CommRing K] [Algebra R K]
    (σ : K ≃ₐ[R] K) (g : SpecPoints (projModel W) (projModelπ W) K) (hZ : InZChart W g)
    (j : {j : Fin 3 // j ≠ 2}) :
    (chartSolutionsEquiv W 2 K (chartHomEquiv W 2 K
        ⟨specMapCompPoint W σ g, inZChart_specMapCompPoint W σ hZ⟩)).1 j =
      σ ((chartSolutionsEquiv W 2 K (chartHomEquiv W 2 K ⟨g, hZ⟩)).1 j) := by
  rw [chartSolutionsEquiv_apply_eq W _ j, chartSolutionsEquiv_apply_eq W ⟨g, hZ⟩ j,
    chartHomEquiv_specMapCompPoint W σ g hZ]
  rfl


-- @@ L153-153 verbatim
/-! ## A5 — the dictionary is `σ`-natural -/


-- @@ L155-163 verbatim
/-- Affine points with equal coordinates are equal (`Nonsingular` is a `Prop`). Stated as a
standalone lemma so that no `simp` ever has to unify two `Point.some` terms whose
coordinate expressions are large. -/
theorem affinePoint_some_congr {F : Type*} [Field F] {V : WeierstrassCurve.Affine F}
    {x y x' y' : F} (hx : x = x') (hy : y = y')
    (h : V.Nonsingular x y) (h' : V.Nonsingular x' y') :
    WeierstrassCurve.Affine.Point.some x y h =
      WeierstrassCurve.Affine.Point.some x' y' h' := by
  subst hx; subst hy; rfl


-- @@ L165-173 verbatim
/-- The value of the dictionary at a chart-factoring point, with the canonical
nonsingularity witness. One `rw`-free step, isolated from A5's case split. -/
theorem projModelPointsEquiv_eq_some_chartSolution [W.IsElliptic] {K : Type u} [Field K]
    [DecidableEq K] [Algebra R K] (g : SpecPoints (projModel W) (projModelπ W) K)
    (hZ : InZChart W g) :
    projModelPointsEquiv W K g =
      WeierstrassCurve.Affine.Point.some _ _
        (nonsingular_chartSolution W ‹W.IsElliptic› g hZ) :=
  projModelPointsEquiv_some W K g hZ _ _ _ rfl rfl


-- @@ L175-179 verbatim
/-- The value of the dictionary at a point off the `Z`-chart. -/
theorem projModelPointsEquiv_eq_zero_of_notInZChart [W.IsElliptic] {K : Type u} [Field K]
    [DecidableEq K] [Algebra R K] (g : SpecPoints (projModel W) (projModelπ W) K)
    (hZ : ¬ InZChart W g) : projModelPointsEquiv W K g = 0 :=
  projModelPointsEquivEll_infinity W ‹W.IsElliptic› K g hZ


-- @@ L181-203 verbatim
/-- **(A5 ★)** The field-points dictionary intertwines precomposition with `Spec σ` and
mathlib's coordinatewise `Affine.Point.map σ`. -/
theorem projModelPointsEquiv_specMapCompPoint [W.IsElliptic] {K : Type u} [Field K]
    [DecidableEq K] [Algebra R K] (σ : K ≃ₐ[R] K)
    (g : SpecPoints (projModel W) (projModelπ W) K) :
    projModelPointsEquiv W K (specMapCompPoint W σ g) =
      WeierstrassCurve.Affine.Point.map (W' := W) (F := K) (K := K)
        (σ : K →ₐ[R] K) (projModelPointsEquiv W K g) := by
  classical
  by_cases hZ : InZChart W g
  · have hZ' : InZChart W (specMapCompPoint W σ g) := inZChart_specMapCompPoint W σ hZ
    rw [projModelPointsEquiv_eq_some_chartSolution W (specMapCompPoint W σ g) hZ',
      projModelPointsEquiv_eq_some_chartSolution W g hZ]
    refine Eq.trans ?_ (WeierstrassCurve.Affine.Point.map_some (f := (σ : K →ₐ[R] K))
      (nonsingular_chartSolution W ‹W.IsElliptic› g hZ)).symm
    exact affinePoint_some_congr
      (chartSolution_specMapCompPoint W σ g hZ ⟨0, by decide⟩)
      (chartSolution_specMapCompPoint W σ g hZ ⟨1, by decide⟩) _ _
  · have hZ' : ¬ InZChart W (specMapCompPoint W σ g) := fun h =>
      hZ (inZChart_of_inZChart_specMapCompPoint W σ h)
    rw [projModelPointsEquiv_eq_zero_of_notInZChart W (specMapCompPoint W σ g) hZ',
      projModelPointsEquiv_eq_zero_of_notInZChart W g hZ]
    exact (WeierstrassCurve.Affine.Point.map_zero (f := (σ : K →ₐ[R] K))).symm


-- @@ L205-205 verbatim
/-! ## B — extension of scalars on `SpecPoints` (the embedding analogue of the σ-action) -/


-- @@ L207-207 verbatim
section Extension


-- @@ L209-211 verbatim
variable {K : Type u} [Field K] [DecidableEq K] [Algebra R K]
  {K' : Type u} [Field K'] [DecidableEq K'] [Algebra R K']
  [Algebra K K'] [IsScalarTower R K K']


-- @@ L213-221 verbatim
/-- **(B1)** Extension of a `K`-valued SpecPoint along a field embedding `K → K'`
(precomposition with `Spec.map`). The embedding analogue of `specMapCompPoint`. -/
noncomputable def extendSpecPoint (g : SpecPoints (projModel W) (projModelπ W) K) :
    SpecPoints (projModel W) (projModelπ W) K' :=
  ⟨Spec.map (CommRingCat.ofHom (algebraMap K K')) ≫ g.1, by
    rw [Category.assoc, g.2, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun c =>
      (IsScalarTower.algebraMap_apply R K K' c).symm)⟩


-- @@ L223-228 verbatim
/-- **(B2 forward)** The `Z`-chart condition ascends along the extension. -/
theorem inZChart_extendSpecPoint (g : SpecPoints (projModel W) (projModelπ W) K)
    (hZ : InZChart W g) : InZChart W (extendSpecPoint W g : SpecPoints _ _ K') := by
  obtain ⟨h, hfac⟩ := hZ
  exact ⟨Spec.map (CommRingCat.ofHom (algebraMap K K')) ≫ h, by
    rw [Category.assoc, hfac]; rfl⟩


-- @@ L230-242 verbatim
/-- **(B2 reverse, via the zero characterisation)** Off-chart points stay off-chart. -/
theorem not_inZChart_extendSpecPoint (g : SpecPoints (projModel W) (projModelπ W) K)
    (hZ : ¬ InZChart W g) : ¬ InZChart W (extendSpecPoint W g : SpecPoints _ _ K') := by
  have h0 := specPoint_eq_zero_of_not_inZ W K g hZ
  intro hcon
  refine projModelZero_not_inZ W K' ?_
  obtain ⟨h, hfac⟩ := hcon
  refine ⟨h, hfac.trans ?_⟩
  show Spec.map (CommRingCat.ofHom (algebraMap K K')) ≫ g.1 = _
  rw [h0, ← Category.assoc, ← Spec.map_comp]
  congr 2
  exact CommRingCat.hom_ext (RingHom.ext fun c =>
    (IsScalarTower.algebraMap_apply R K K' c).symm)


-- @@ L244-261 verbatim
/-- **(B3)** The chart hom of the extension is the embedding composed with the chart
hom (mirror of `chartHomEquiv_specMapCompPoint`). -/
theorem chartHomEquiv_extendSpecPoint (g : SpecPoints (projModel W) (projModelπ W) K)
    (hZ : InZChart W g) :
    (chartHomEquiv W 2 K' ⟨extendSpecPoint W g,
        inZChart_extendSpecPoint W g hZ⟩).1 =
      ((algebraMap K K')).comp (chartHomEquiv W 2 K ⟨g, hZ⟩).1 := by
  refine congrArg Subtype.val (chartHomEquiv_eq_of_specMap W 2
    ⟨extendSpecPoint W g, inZChart_extendSpecPoint W g hZ⟩
    ⟨((algebraMap K K')).comp (chartHomEquiv W 2 K ⟨g, hZ⟩).1, ?_⟩ ?_)
  · rw [RingHom.comp_assoc, (chartHomEquiv W 2 K ⟨g, hZ⟩).2]
    exact RingHom.ext fun c => (IsScalarTower.algebraMap_apply R K K' c).symm
  · rw [show CommRingCat.ofHom (((algebraMap K K')).comp
        (chartHomEquiv W 2 K ⟨g, hZ⟩).1) =
        CommRingCat.ofHom (chartHomEquiv W 2 K ⟨g, hZ⟩).1 ≫
          CommRingCat.ofHom (algebraMap K K') from rfl,
      Spec.map_comp, Category.assoc, chartHomEquiv_specMap_factors W 2 ⟨g, hZ⟩]
    rfl


-- @@ L263-297 verbatim
/-- **(B4 — the field-extension dictionary naturality)** The dictionary of the extended
point is `Point.map` along the embedding (mirror of
`projModelPointsEquiv_specMapCompPoint`). -/
theorem projModelPointsEquiv_extendSpecPoint [W.IsElliptic]
    (g : SpecPoints (projModel W) (projModelπ W) K) :
    projModelPointsEquiv W K' (extendSpecPoint W g)
      = WeierstrassCurve.Affine.Point.map
          (IsScalarTower.toAlgHom R K K')
          (projModelPointsEquiv W K g) := by
  classical
  by_cases hZ : InZChart W g
  · have hZ' := inZChart_extendSpecPoint (K' := K') W g hZ
    have hcoord : ∀ j : {j : Fin 3 // j ≠ 2},
        (chartSolutionsEquiv W 2 K' (chartHomEquiv W 2 K'
            ⟨extendSpecPoint W g, hZ'⟩)).1 j
          = algebraMap K K' ((chartSolutionsEquiv W 2 K
              (chartHomEquiv W 2 K ⟨g, hZ⟩)).1 j) := by
      intro j
      have h1 := chartSolutionsEquiv_apply_eq W ⟨extendSpecPoint W g, hZ'⟩ j
      have h2 := chartSolutionsEquiv_apply_eq W ⟨g, hZ⟩ j
      refine h1.trans (Eq.trans ?_ (congrArg (algebraMap K K') h2).symm)
      exact congrArg (fun (φ : _ →+* K') => φ (chartCoordEquiv W 2
        (Ideal.Quotient.mk _ (MvPolynomial.X j))))
        (chartHomEquiv_extendSpecPoint W g hZ)
    refine ((projModelPointsEquiv_eq_some_chartSolution W (extendSpecPoint W g)
      hZ').trans ?_).trans (congrArg (WeierstrassCurve.Affine.Point.map
        (IsScalarTower.toAlgHom R K K'))
        (projModelPointsEquiv_eq_some_chartSolution W g hZ)).symm
    rw [WeierstrassCurve.Affine.Point.map_some]
    exact affinePoint_some_congr (hcoord ⟨0, by decide⟩) (hcoord ⟨1, by decide⟩) _ _
  · have hZ' := not_inZChart_extendSpecPoint (K' := K') W g hZ
    rw [projModelPointsEquiv_eq_zero_of_notInZChart W (extendSpecPoint W g) hZ',
      projModelPointsEquiv_eq_zero_of_notInZChart W g hZ]
    exact (WeierstrassCurve.Affine.Point.map_zero
      (f := IsScalarTower.toAlgHom R K K')).symm


-- @@ L299-299 verbatim
end Extension


-- @@ L301-301 verbatim
end ModularCurves
