/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import ModularCurves.ForMathlib.ProjMapClosedImmersion
import ModularCurves.ForMathlib.SegreProductStandardCover
import Mathlib.RingTheory.TensorProduct.MvPolynomial


-- @@ L12-18 verbatim
/-!
# Coefficient base change for polynomial projective space

Polynomial projective space commutes with extension of its coefficient ring. The proof identifies
each standard projective chart with a polynomial ring and uses the scalar-extension equivalence for
multivariate polynomial rings.
-/


-- @@ L20-20 verbatim
open CategoryTheory Limits AlgebraicGeometry

-- @@ L21-21 verbatim
open HomogeneousIdeal HomogeneousLocalization

-- @@ L22-22 verbatim
open scoped TensorProduct


-- @@ L24-24 verbatim
noncomputable section


-- @@ L26-26 verbatim
universe u


-- @@ L28-28 verbatim
namespace MvPolynomial


-- @@ L30-30 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra

-- @@ L31-32 verbatim
local instance (priority := 10000) {n : ℕ} : DecidableEq (Fin n) :=
  Classical.decEq _


-- @@ L34-41 verbatim
/-- Coefficient extension on homogeneous polynomial rings, preserving the standard grading. -/
noncomputable abbrev coefficientGradedHom
    {k R : Type u} [CommRing k] [CommRing R]
    (φ : k →+* R) (d : ℕ) :
    homogeneousSubmodule (Fin (d + 1)) k →+*ᵍ
      homogeneousSubmodule (Fin (d + 1)) R where
  toRingHom := MvPolynomial.map φ
  map_mem := fun hp => MvPolynomial.IsHomogeneous.map hp φ


-- @@ L43-49 verbatim
@[simp]
lemma coefficientGradedHom_X
    {k R : Type u} [CommRing k] [CommRing R]
    (φ : k →+* R) {d : ℕ} (i : Fin (d + 1)) :
    coefficientGradedHom φ d (X i) = X i := by
  change MvPolynomial.map φ (X i) = X i
  exact MvPolynomial.map_X φ i


-- @@ L51-78 verbatim
/-- Coefficient extension satisfies the irrelevant-ideal hypothesis required by `Proj.map`. -/
lemma coefficientIrrelevantLE
    {k R : Type u} [CommRing k] [CommRing R]
    (φ : k →+* R) (d : ℕ) :
    (homogeneousSubmodule (Fin (d + 1)) R)₊ ≤
      (homogeneousSubmodule (Fin (d + 1)) k)₊.map
        (coefficientGradedHom φ d) := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro n hn p hp
  have hpIrrelevant :
      p ∈ (homogeneousSubmodule (Fin (d + 1)) R)₊.toIdeal :=
    HomogeneousIdeal.mem_irrelevant_of_mem
      (homogeneousSubmodule (Fin (d + 1)) R) hn hp
  have hpSpan :
      p ∈ Ideal.span
        (Set.range
          (X : Fin (d + 1) → MvPolynomial (Fin (d + 1)) R)) :=
    irrelevant_toIdeal_le_span_range_X hpIrrelevant
  refine (Ideal.span_le.2 ?_) hpSpan
  intro x hx
  obtain ⟨i, rfl⟩ := hx
  rw [← coefficientGradedHom_X φ i]
  exact Ideal.mem_map_of_mem
    (coefficientGradedHom φ d)
    (HomogeneousIdeal.mem_irrelevant_of_mem
      (homogeneousSubmodule (Fin (d + 1)) k)
      Nat.zero_lt_one
      (X_mem_homogeneousSubmodule_one k i))


-- @@ L80-87 verbatim
/-- The morphism from projective space after coefficient extension to the original projective
space. -/
def coefficientMap
    {k R : Type u} [CommRing k] [CommRing R]
    (φ : k →+* R) (d : ℕ) :
    Proj (homogeneousSubmodule (Fin (d + 1)) R) ⟶
      Proj (homogeneousSubmodule (Fin (d + 1)) k) :=
  Proj.map (coefficientGradedHom φ d) (coefficientIrrelevantLE φ d)


-- @@ L89-100 verbatim
/-- The standard coordinate chart is preserved by coefficient extension. -/
@[simp]
lemma coefficientMap_preimage_coordinateOpen
    {k R : Type u} [CommRing k] [CommRing R]
    (φ : k →+* R) (d : ℕ) (i : Fin (d + 1)) :
    coefficientMap φ d ⁻¹ᵁ coordinateOpen (R := k) i =
      coordinateOpen (R := R) i := by
  simpa only [coefficientMap, coordinateOpen, coefficientGradedHom_X] using
    (Proj.map_preimage_basicOpen
      (coefficientGradedHom φ d)
      (coefficientIrrelevantLE φ d)
      (X i))


-- @@ L102-110 verbatim
/-- Coefficient extension on a standard projective chart. -/
noncomputable abbrev coefficientChartRingHom
    {k R : Type u} [CommRing k] [CommRing R]
    (φ : k →+* R) {d : ℕ} (i : Fin (d + 1)) :
    ProjectiveCoordinateAway k i →+* ProjectiveCoordinateAway R i :=
  (ModularCurves.awayCongr
      (𝒜 := homogeneousSubmodule (Fin (d + 1)) R)
      (MvPolynomial.map_X φ i)).toRingHom.comp
    (Away.map (coefficientGradedHom φ d) (X i))


-- @@ L112-119 verbatim
/-- Coefficient extension on a standard chart commutes with homogenization. -/
lemma coefficientChartRingHom_homogenizeAt
    {k R : Type u} [CommRing k] [CommRing R]
    (φ : k →+* R) {d : ℕ} (i : Fin (d + 1))
    (p : MvPolynomial {j : Fin (d + 1) // j ≠ i} k) :
    coefficientChartRingHom φ i (homogenizeAt k i p) =
      homogenizeAt R i (MvPolynomial.map φ p) :=
  (homogenizeAt_map k φ i p).symm


-- @@ L121-127 verbatim
private lemma dehomogenizeAt_homogenizeAt
    (A : Type u) [CommRing A] {d : ℕ} (i : Fin (d + 1))
    (p : MvPolynomial {j : Fin (d + 1) // j ≠ i} A) :
    dehomogenizeAt A i (homogenizeAt A i p) = p := by
  change ((dehomogenizeAt A i).comp (homogenizeAt A i)) p = p
  rw [dehomogenizeAt_comp_homogenizeAt]
  rfl


-- @@ L129-141 verbatim
/-- Coefficient extension on a standard chart commutes with dehomogenization. -/
lemma coefficientChartRingHom_dehomogenizeAt
    {k R : Type u} [CommRing k] [CommRing R]
    (φ : k →+* R) {d : ℕ} (i : Fin (d + 1))
    (x : ProjectiveCoordinateAway k i) :
    dehomogenizeAt R i (coefficientChartRingHom φ i x) =
      MvPolynomial.map φ (dehomogenizeAt k i x) := by
  obtain ⟨p, rfl⟩ := (chartRingEquiv k i).symm.surjective x
  change dehomogenizeAt R i
      (coefficientChartRingHom φ i (homogenizeAt k i p)) =
    MvPolynomial.map φ (dehomogenizeAt k i (homogenizeAt k i p))
  rw [coefficientChartRingHom_homogenizeAt]
  rw [dehomogenizeAt_homogenizeAt, dehomogenizeAt_homogenizeAt]


-- @@ L143-147 verbatim
private lemma chartRingEquiv_apply
    (A : Type u) [CommRing A] {d : ℕ} (i : Fin (d + 1))
    (x : ProjectiveCoordinateAway A i) :
    chartRingEquiv A i x = dehomogenizeAt A i x :=
  rfl


-- @@ L149-164 verbatim
/-- The standard projective chart equivalence as an algebra homomorphism. -/
noncomputable def coordinateChartAlgHom
    (R : Type u) [CommRing R] {d : ℕ} (i : Fin (d + 1)) :
    ProjectiveCoordinateAway R i →ₐ[R]
      MvPolynomial {j : Fin (d + 1) // j ≠ i} R where
  toRingHom := (chartRingEquiv R i).toRingHom
  commutes' := by
    intro r
    calc
      chartRingEquiv R i
          (algebraMap R (ProjectiveCoordinateAway R i) r) = C r :=
        chartRingEquiv_algebraMap (R := R) i r
      _ = algebraMap R
          (MvPolynomial {j : Fin (d + 1) // j ≠ i} R) r := by
        rw [MvPolynomial.algebraMap_apply]
        simp


-- @@ L166-169 verbatim
private lemma coordinateChartAlgHom_bijective
    (R : Type u) [CommRing R] {d : ℕ} (i : Fin (d + 1)) :
    Function.Bijective (coordinateChartAlgHom R i) :=
  (chartRingEquiv R i).bijective


-- @@ L171-178 verbatim
/-- The standard projective chart equivalence as an algebra equivalence. -/
noncomputable def coordinateChartAlgEquiv
    (R : Type u) [CommRing R] {d : ℕ} (i : Fin (d + 1)) :
    ProjectiveCoordinateAway R i ≃ₐ[R]
      MvPolynomial {j : Fin (d + 1) // j ≠ i} R :=
  AlgEquiv.ofBijective
    (coordinateChartAlgHom R i)
    (coordinateChartAlgHom_bijective R i)


-- @@ L180-185 verbatim
@[simp]
lemma coordinateChartAlgEquiv_apply
    (R : Type u) [CommRing R] {d : ℕ} (i : Fin (d + 1))
    (x : ProjectiveCoordinateAway R i) :
    coordinateChartAlgEquiv R i x = chartRingEquiv R i x :=
  rfl


-- @@ L187-198 verbatim
/-- The scalar extension of a standard projective chart ring is the corresponding chart ring over
the new coefficient ring. -/
noncomputable def coefficientChartTensorAlgEquiv
    (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]
    {d : ℕ} (i : Fin (d + 1)) :
    R ⊗[k] ProjectiveCoordinateAway k i ≃ₐ[R]
      ProjectiveCoordinateAway R i :=
  (Algebra.TensorProduct.congr
      (AlgEquiv.refl)
      (coordinateChartAlgEquiv k i)).trans
    ((MvPolynomial.algebraTensorAlgEquiv k R).trans
      (coordinateChartAlgEquiv R i).symm)


-- @@ L200-218 verbatim
/-- The chart scalar-extension equivalence agrees with the coefficient map on its left factor. -/
lemma coefficientChartTensorAlgEquiv_comp_includeLeft
    (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]
    {d : ℕ} (i : Fin (d + 1)) :
    (coefficientChartTensorAlgEquiv k R i).toRingHom.comp
        (Algebra.TensorProduct.includeLeftRingHom :
          R →+* R ⊗[k] ProjectiveCoordinateAway k i) =
      algebraMap R (ProjectiveCoordinateAway R i) := by
  apply RingHom.ext
  intro r
  change coefficientChartTensorAlgEquiv k R i (r ⊗ₜ[k] 1) =
    algebraMap R (ProjectiveCoordinateAway R i) r
  simp only [coefficientChartTensorAlgEquiv, AlgEquiv.trans_apply,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
    AlgEquiv.refl_toAlgHom, AlgHom.id_apply, map_one,
    MvPolynomial.algebraTensorAlgEquiv_tmul]
  rw [show r • (1 : MvPolynomial {j : Fin (d + 1) // j ≠ i} R) =
      algebraMap R _ r by rw [Algebra.smul_def, mul_one]]
  exact (coordinateChartAlgEquiv R i).symm.commutes r


-- @@ L220-241 verbatim
/-- The chart scalar-extension equivalence agrees with coefficient extension on its right factor. -/
lemma coefficientChartTensorAlgEquiv_comp_includeRight
    (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]
    {d : ℕ} (i : Fin (d + 1)) :
    (coefficientChartTensorAlgEquiv k R i).toRingHom.comp
        (Algebra.TensorProduct.includeRight :
          ProjectiveCoordinateAway k i →ₐ[k]
            R ⊗[k] ProjectiveCoordinateAway k i).toRingHom =
      coefficientChartRingHom (algebraMap k R) i := by
  apply RingHom.ext
  intro x
  apply (coordinateChartAlgEquiv R i).injective
  change coordinateChartAlgEquiv R i
      (coefficientChartTensorAlgEquiv k R i (1 ⊗ₜ[k] x)) =
    coordinateChartAlgEquiv R i
      (coefficientChartRingHom (algebraMap k R) i x)
  rw [coordinateChartAlgEquiv_apply R i
    (coefficientChartRingHom (algebraMap k R) i x)]
  rw [chartRingEquiv_apply]
  rw [coefficientChartRingHom_dehomogenizeAt]
  simp [coefficientChartTensorAlgEquiv]
  rw [chartRingEquiv_apply]


-- @@ L243-259 verbatim
/-- Coefficient extension on a projective chart respects the coefficient embeddings. -/
lemma coefficientChartRingHom_algebraMap
    (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]
    {d : ℕ} (i : Fin (d + 1)) (r : k) :
    coefficientChartRingHom (algebraMap k R) i
        (algebraMap k (ProjectiveCoordinateAway k i) r) =
      algebraMap R (ProjectiveCoordinateAway R i) (algebraMap k R r) := by
  apply (chartRingEquiv R i).injective
  rw [chartRingEquiv_apply]
  rw [coefficientChartRingHom_dehomogenizeAt]
  have hk :
      dehomogenizeAt k i
          (algebraMap k (ProjectiveCoordinateAway k i) r) = C r := by
    rw [← chartRingEquiv_apply]
    exact chartRingEquiv_algebraMap (R := k) i r
  rw [hk, MvPolynomial.map_C]
  exact (chartRingEquiv_algebraMap (R := R) i (algebraMap k R r)).symm


-- @@ L261-313 verbatim
/-- The affine square on a standard projective chart is cartesian. -/
lemma isPullback_coefficientChart
    (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]
    {d : ℕ} (i : Fin (d + 1)) :
    IsPullback
      (Spec.map
        (CommRingCat.ofHom
          (algebraMap R (ProjectiveCoordinateAway R i))))
      (Spec.map
        (CommRingCat.ofHom
          (coefficientChartRingHom (algebraMap k R) i)))
      (Spec.map (CommRingCat.ofHom (algebraMap k R)))
      (Spec.map
        (CommRingCat.ofHom
          (algebraMap k (ProjectiveCoordinateAway k i)))) := by
  let tensorMap :=
    (coefficientChartTensorAlgEquiv k R i).toRingHom
  letI : IsIso (CommRingCat.ofHom tensorMap) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (coefficientChartTensorAlgEquiv k R i).bijective
  let e :
      Spec (CommRingCat.of (ProjectiveCoordinateAway R i)) ≅
        pullback
          (Spec.map (CommRingCat.ofHom (algebraMap k R)))
          (Spec.map
            (CommRingCat.ofHom
              (algebraMap k (ProjectiveCoordinateAway k i)))) :=
    asIso (Spec.map (CommRingCat.ofHom tensorMap)) ≪≫
      (pullbackSpecIso k R (ProjectiveCoordinateAway k i)).symm
  apply IsPullback.of_iso_pullback _ e
  · dsimp only [e]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
      pullbackSpecIso_inv_fst, asIso_hom, ← Spec.map_comp]
    dsimp only [tensorMap]
    rw [← CommRingCat.ofHom_comp]
    exact congrArg
      (fun f => Spec.map (CommRingCat.ofHom f))
      (coefficientChartTensorAlgEquiv_comp_includeLeft k R i)
  · dsimp only [e]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
      pullbackSpecIso_inv_snd, asIso_hom, ← Spec.map_comp]
    dsimp only [tensorMap]
    rw [← CommRingCat.ofHom_comp]
    exact congrArg
      (fun f => Spec.map (CommRingCat.ofHom f))
      (coefficientChartTensorAlgEquiv_comp_includeRight k R i)
  · constructor
    simp only [← Spec.map_comp]
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    apply congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    apply RingHom.ext
    intro r
    exact (coefficientChartRingHom_algebraMap k R i r).symm


-- @@ L315-331 verbatim
/-- The coefficient-extension map restricts on each standard chart to
`coefficientChartRingHom`. -/
private lemma Spec_map_awayCongr_awayι
    {R₀ B : Type u} [CommRing R₀] [CommRing B] [Algebra R₀ B]
    (𝒜 : ℕ → Submodule R₀ B) [GradedAlgebra 𝒜]
    {s t : B} (h : s = t) {m : ℕ} (hs : s ∈ 𝒜 m) (hm : 0 < m) :
    Spec.map
          (CommRingCat.ofHom
            (ModularCurves.awayCongr (𝒜 := 𝒜) h).toRingHom) ≫
        Proj.awayι 𝒜 s hs hm =
      Proj.awayι 𝒜 t (h ▸ hs) hm := by
  subst h
  rw [show
    (ModularCurves.awayCongr (𝒜 := 𝒜) (rfl : s = s)).toRingHom =
        RingHom.id _ by
      rw [ModularCurves.awayCongr_rfl, RingEquiv.toRingHom_refl]]
  rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]


-- @@ L333-401 verbatim
lemma isPullback_coefficientChart_coefficientMap
    (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]
    (d : ℕ) (i : Fin (d + 1)) :
    IsPullback
      (Spec.map
        (CommRingCat.ofHom
          (coefficientChartRingHom (algebraMap k R) i)))
      (coordinateChartMap R (Fin (d + 1)) i)
      (coordinateChartMap k (Fin (d + 1)) i)
      (coefficientMap (algebraMap k R) d) := by
  apply IsOpenImmersion.isPullback
  · let f := coefficientGradedHom (algebraMap k R) d
    let hX : f (X i) = X i :=
      coefficientGradedHom_X (algebraMap k R) i
    calc
      coordinateChartMap R (Fin (d + 1)) i ≫
          coefficientMap (algebraMap k R) d =
        (Spec.map
              (CommRingCat.ofHom
                (ModularCurves.awayCongr
                  (𝒜 := homogeneousSubmodule (Fin (d + 1)) R)
                  hX).toRingHom) ≫
            Proj.awayι
              (homogeneousSubmodule (Fin (d + 1)) R)
              (f (X i))
              (GradedRingHom.map_mem f
                (X_mem_homogeneousSubmodule_one k i))
              Nat.zero_lt_one) ≫
          coefficientMap (algebraMap k R) d := by
            rw [Spec_map_awayCongr_awayι]
      _ =
        Spec.map
              (CommRingCat.ofHom
                (ModularCurves.awayCongr
                  (𝒜 := homogeneousSubmodule (Fin (d + 1)) R)
                  hX).toRingHom) ≫
            (Proj.awayι
                (homogeneousSubmodule (Fin (d + 1)) R)
                (f (X i))
                (GradedRingHom.map_mem f
                  (X_mem_homogeneousSubmodule_one k i))
                Nat.zero_lt_one ≫
              coefficientMap (algebraMap k R) d) := by
                rw [Category.assoc]
      _ =
        Spec.map
              (CommRingCat.ofHom
                (ModularCurves.awayCongr
                  (𝒜 := homogeneousSubmodule (Fin (d + 1)) R)
                  hX).toRingHom) ≫
            (Spec.map (CommRingCat.ofHom (Away.map f (X i))) ≫
              coordinateChartMap k (Fin (d + 1)) i) := by
                change _ ≫
                    (Proj.awayι _ (f (X i)) _ _ ≫
                      Proj.map f
                        (coefficientIrrelevantLE (algebraMap k R) d)) =
                  _
                rw [Proj.awayι_comp_map]
      _ =
        Spec.map
              (CommRingCat.ofHom
                (coefficientChartRingHom (algebraMap k R) i)) ≫
            coordinateChartMap k (Fin (d + 1)) i := by
              rw [← Category.assoc, ← Spec.map_comp,
                ← CommRingCat.ofHom_comp]
  · rw [coordinateAffineOpenCover_opensRange,
      coordinateAffineOpenCover_opensRange]
    exact coefficientMap_preimage_coordinateOpen
      (algebraMap k R) d i


-- @@ L403-521 verbatim
/-- Polynomial projective space commutes with extension of its coefficient ring. -/
theorem isPullback_coefficientMap
    (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]
    (d : ℕ) :
    IsPullback
      (coefficientMap (algebraMap k R) d)
      (homogeneousProjπ (R := R) (σ := Fin (d + 1)))
      (homogeneousProjπ (R := k) (σ := Fin (d + 1)))
      (Spec.map (CommRingCat.ofHom (algebraMap k R))) := by
  apply Scheme.isPullback_of_openCover
    (coefficientMap (algebraMap k R) d)
    (homogeneousProjπ (R := R) (σ := Fin (d + 1)))
    (homogeneousProjπ (R := k) (σ := Fin (d + 1)))
    (Spec.map (CommRingCat.ofHom (algebraMap k R)))
    (coordinateSchemeOpenCover k (Fin (d + 1)))
  rintro (i : Fin (d + 1))
  let global := coefficientMap (algebraMap k R) d
  let toBaseR := homogeneousProjπ (R := R) (σ := Fin (d + 1))
  let toBaseK := homogeneousProjπ (R := k) (σ := Fin (d + 1))
  let base := Spec.map (CommRingCat.ofHom (algebraMap k R))
  let chartMap :=
    Spec.map
      (CommRingCat.ofHom
        (coefficientChartRingHom (algebraMap k R) i))
  have hChart :
      IsPullback chartMap
        (coordinateChartMap R (Fin (d + 1)) i)
        (coordinateChartMap k (Fin (d + 1)) i)
        global :=
    isPullback_coefficientChart_coefficientMap k R d i
  have hLocal :
      IsPullback
        chartMap
        (Spec.map
          (CommRingCat.ofHom
            (algebraMap R (ProjectiveCoordinateAway R i))))
        (Spec.map
          (CommRingCat.ofHom
            (algebraMap k (ProjectiveCoordinateAway k i))))
        base :=
    (isPullback_coefficientChart k R i).flip
  let e :
      Spec (CommRingCat.of (ProjectiveCoordinateAway R i)) ≅
        ((coordinateSchemeOpenCover k (Fin (d + 1))).pullback₁ global).X i :=
    hChart.isoPullback ≪≫
      pullbackSymmetry
        (coordinateChartMap k (Fin (d + 1)) i) global
  have e_snd :
      e.hom ≫
          pullback.snd global
            (coordinateChartMap k (Fin (d + 1)) i) =
        chartMap := by
    change
      (hChart.isoPullback.hom ≫
          (pullbackSymmetry
            (coordinateChartMap k (Fin (d + 1)) i) global).hom) ≫
        pullback.snd global
          (coordinateChartMap k (Fin (d + 1)) i) =
      chartMap
    rw [Category.assoc, pullbackSymmetry_hom_comp_snd,
      hChart.isoPullback_hom_fst]
  have e_fst :
      e.hom ≫
          pullback.fst global
            (coordinateChartMap k (Fin (d + 1)) i) =
        coordinateChartMap R (Fin (d + 1)) i := by
    change
      (hChart.isoPullback.hom ≫
          (pullbackSymmetry
            (coordinateChartMap k (Fin (d + 1)) i) global).hom) ≫
        pullback.fst global
          (coordinateChartMap k (Fin (d + 1)) i) =
      coordinateChartMap R (Fin (d + 1)) i
    rw [Category.assoc, pullbackSymmetry_hom_comp_fst,
      hChart.isoPullback_hom_snd]
  refine hLocal.of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · change chartMap =
      e.hom ≫
        pullback.snd global
          (coordinateChartMap k (Fin (d + 1)) i)
    exact e_snd.symm
  · change
      Spec.map
          (CommRingCat.ofHom
            (algebraMap R (ProjectiveCoordinateAway R i))) =
        e.hom ≫
          pullback.fst global
              (coordinateChartMap k (Fin (d + 1)) i) ≫
            toBaseR
    calc
      Spec.map
          (CommRingCat.ofHom
            (algebraMap R (ProjectiveCoordinateAway R i))) =
          coordinateChartMap R (Fin (d + 1)) i ≫ toBaseR :=
        (coordinateAffineOpenCover_comp_homogeneousProjπ
          R (Fin (d + 1)) i).symm
      _ =
          (e.hom ≫
              pullback.fst global
                (coordinateChartMap k (Fin (d + 1)) i)) ≫
            toBaseR :=
        congrArg (fun q => q ≫ toBaseR) e_fst.symm
      _ =
          e.hom ≫
            pullback.fst global
                (coordinateChartMap k (Fin (d + 1)) i) ≫
              toBaseR :=
        Category.assoc _ _ _
  · change
      Spec.map
          (CommRingCat.ofHom
            (algebraMap k (ProjectiveCoordinateAway k i))) =
        coordinateChartMap k (Fin (d + 1)) i ≫ toBaseK
    exact
      (coordinateAffineOpenCover_comp_homogeneousProjπ
        k (Fin (d + 1)) i).symm
  · change base = base
    rfl


-- @@ L523-523 verbatim
end MvPolynomial
