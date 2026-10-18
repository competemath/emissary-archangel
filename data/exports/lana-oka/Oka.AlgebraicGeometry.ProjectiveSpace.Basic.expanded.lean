/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Oka.RingTheory.MvPolynomial.HomogeneousLocalization


-- @@ L9-51 verbatim
/-!
# Projective space

`ℙ(n; R) = Proj R[X₀, …, Xₙ]` for the grading by total degree (`MvPolynomial.gradedAlgebra`,
made a scoped instance in `AlgebraicGeometry.ProjectiveSpace`). It is proper over `Spec R`, and it
is covered by the `n + 1` standard charts

  `chart i : 𝔸ⁿ_R = Spec R[Y₀, …, Yₙ₋₁] ⟶ ℙ(n; R)`,

open immersions with image `U i = D₊(Xᵢ)`, where `Yⱼ` is the fraction `X_{i.succAbove j} / Xᵢ`
(`MvPolynomial.awayXEquiv`). For a finite set `I` of indices, `UI I = D₊(∏_{j ∈ I} Xⱼ)` is
`⨅_{j ∈ I} U j`, and for `i ∈ I` it is `Spec` of `R[Y][1 / dehomogenize i (∏_{j ∈ I} Xⱼ)]`
(`UIIsoSpec`), compatibly with `chart i` (`UIIsoSpec_inv_ι`).

## Main definitions

- `AlgebraicGeometry.ProjectiveSpace n R`, notation `ℙ(n; R)`.
- `ProjectiveSpace.toSpec : ℙ(n; R) ⟶ Spec R`, which is proper.
- `ProjectiveSpace.chart i : Spec R[Y₀, …, Yₙ₋₁] ⟶ ℙ(n; R)`, an open immersion.
- `ProjectiveSpace.U i : ℙ(n; R).Opens`, the affine open `D₊(Xᵢ)`, with `⨆ i, U i = ⊤`.
- `ProjectiveSpace.affineOpenCover`: the standard affine open cover indexed by `Fin (n + 1)`.
- `ProjectiveSpace.UI I`: the intersection `⨅_{j ∈ I} U j` (`UI_eq_iInf`).
- `ProjectiveSpace.UIIsoSpec i I hi : UI I ≅ Spec R[Y][1 / dehomogenize i (∏_{j ∈ I} Xⱼ)]`.

## Design note: twisting sheaves `O(k)`

Sections of `O(k)` over `UI I` are the degree-`k` part of `A[1 / ∏_{j ∈ I} Xⱼ]`, and over
`U i` this is the free module of rank one over `A_(Xᵢ)` on `Xᵢᵏ`, with transition functions
`(Xⱼ / Xᵢ)ᵏ`. Mathlib has no graded-module `Proj`-tilde construction yet, so the recommended
construction on top of this file is:

1. For a `ℤ`-graded (or `ℕ`-graded) `A`-module `M` and homogeneous `f` of degree `d > 0`, the
   degree-zero part `M_(f)` of `M_f` is an `A_(f)`-module; on the charts `U i` take the tilde of
   `M_(Xᵢ)` and glue along `HomogeneousLocalization.awayMap`-compatible isomorphisms
   `M_(Xᵢ) ⊗ A_(XᵢXⱼ) ≅ M_(XᵢXⱼ)`. With `M = A(k)` this gives `O(k)`, with `M_(Xᵢ) = A_(Xᵢ) · Xᵢᵏ`.
2. For `O(k)` alone it suffices to glue the free rank-one modules `O_{U i}` along the cocycle
   `gᵢⱼ = (Xⱼ / Xᵢ)ᵏ ∈ Γ(UI {i, j}, O)ˣ` (a line bundle from a Čech 1-cocycle), which only
   needs `UIIsoSpec` and the units `awayXDiv`; `F(k) := F ⊗ O(k)`.

Option 1 is what makes Serre's theorem A and graded resolutions (`M ↦ M~` exact, `A(k)~ = O(k)`)
available; option 2 is the cheapest route to the Čech computation of `H^q(ℙⁿ, O(k))`, whose
Čech complex on the standard cover is, in chart-free form, `⊕_{|I| = q+1} (A_{∏_{I} Xⱼ})_k`.
-/


-- @@ L53-53 verbatim
open CategoryTheory MvPolynomial HomogeneousLocalization


-- @@ L55-55 verbatim
universe u


-- @@ L57-57 verbatim
namespace AlgebraicGeometry


-- @@ L59-59 verbatim
namespace ProjectiveSpace


-- @@ L61-61 verbatim
attribute [scoped instance] MvPolynomial.gradedAlgebra


-- @@ L63-63 verbatim
end ProjectiveSpace


-- @@ L65-65 verbatim
open scoped ProjectiveSpace


-- @@ L67-67 verbatim
variable (n : ℕ) (R : Type u) [CommRing R]


-- @@ L69-70 verbatim
/-- **Projective `n`-space** over `R`: `Proj R[X₀, …, Xₙ]` for the grading by total degree. -/
noncomputable abbrev ProjectiveSpace : Scheme.{u} := Proj (homogeneousSubmodule (Fin (n + 1)) R)


-- @@ L72-72 verbatim
@[inherit_doc] scoped[AlgebraicGeometry] notation "ℙ(" n "; " R ")" => ProjectiveSpace n R


-- @@ L74-74 verbatim
namespace ProjectiveSpace


-- @@ L76-76 verbatim
local notation "𝒜" => homogeneousSubmodule (Fin (n + 1)) R


-- @@ L78-84 verbatim
/-- The degree-zero part of `R[X₀, …, Xₙ]` is `R`. -/
noncomputable def gradeZeroEquiv : R ≃+* 𝒜 0 :=
  RingEquiv.ofBijective (algebraMap R (𝒜 0))
    ⟨fun a b h ↦ C_injective _ _ congr(($h : MvPolynomial (Fin (n + 1)) R)), fun ⟨p, hp⟩ ↦ by
      rw [homogeneousSubmodule_zero, Submodule.mem_one] at hp
      obtain ⟨r, rfl⟩ := hp
      exact ⟨r, rfl⟩⟩


-- @@ L86-88 verbatim
instance : Algebra.FiniteType (𝒜 0) (MvPolynomial (Fin (n + 1)) R) :=
  by classical exact
    ⟨⟨Finset.univ.image X, by simpa using adjoin_range_X_gradeZero_eq_top R (Fin (n + 1))⟩⟩


-- @@ L90-92 verbatim
/-- The structure morphism `ℙ(n; R) ⟶ Spec R`. -/
noncomputable def toSpec : ℙ(n; R) ⟶ Spec (.of R) :=
  Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 0)))


-- @@ L94-95 verbatim
instance : IsIso (Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 0)))) :=
  inferInstanceAs (IsIso (Scheme.Spec.mapIso (gradeZeroEquiv n R).toCommRingCatIso.op).hom)


-- @@ L97-99 verbatim
/-- **Projective space is proper.** -/
instance : IsProper (toSpec n R) := by
  rw [toSpec]; infer_instance


-- @@ L101-101 verbatim
variable {n R}


-- @@ L103-107 verbatim
/-- The **standard chart** `𝔸ⁿ_R ⟶ ℙ(n; R)` with image `D₊(Xᵢ)`, where the coordinate `Yⱼ` is
`X_{i.succAbove j} / Xᵢ`. -/
noncomputable def chart (i : Fin (n + 1)) : Spec (.of (MvPolynomial (Fin n) R)) ⟶ ℙ(n; R) :=
  Spec.map (CommRingCat.ofHom (awayXEquiv R i).symm.toRingHom) ≫
    Proj.awayι 𝒜 (X i) (X_mem_homogeneousSubmodule_one i) Nat.one_pos


-- @@ L109-111 verbatim
instance (i : Fin (n + 1)) :
    IsIso (Spec.map (CommRingCat.ofHom (awayXEquiv R i).symm.toRingHom)) :=
  inferInstanceAs (IsIso (Scheme.Spec.mapIso (awayXEquiv R i).toCommRingCatIso.op).inv)


-- @@ L113-114 verbatim
instance (i : Fin (n + 1)) : IsOpenImmersion (chart (R := R) i) := by
  rw [chart]; infer_instance


-- @@ L116-127 verbatim
@[reassoc]
lemma chart_toSpec (i : Fin (n + 1)) :
    chart i ≫ toSpec n R = Spec.map (CommRingCat.ofHom C) := by
  rw [chart, toSpec, Category.assoc, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp,
    ← Spec.map_comp]
  congr 1
  ext r : 2
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
    Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    awayXEquiv_symm_apply]
  rw [← fromAwayX_toAwayX (R := R) i (C r), toAwayX_C]
  rfl


-- @@ L129-132 verbatim
variable (n R) in
/-- The standard affine open `D₊(Xᵢ) ⊆ ℙ(n; R)`. -/
noncomputable def U (i : Fin (n + 1)) : ℙ(n; R).Opens :=
  Proj.basicOpen 𝒜 (X i)


-- @@ L134-136 verbatim
lemma opensRange_chart (i : Fin (n + 1)) : (chart (R := R) i).opensRange = U n R i := by
  unfold chart
  rw [Scheme.Hom.opensRange_comp_of_isIso, Proj.opensRange_awayι, U]


-- @@ L138-139 verbatim
lemma isAffineOpen_U (i : Fin (n + 1)) : IsAffineOpen (U n R i) :=
  Proj.isAffineOpen_basicOpen _ _ (X_mem_homogeneousSubmodule_one i) Nat.one_pos


-- @@ L141-144 verbatim
variable (n R) in
lemma iSup_U : ⨆ i, U n R i = ⊤ :=
  Proj.iSup_basicOpen_eq_top' _ _ (fun i ↦ ⟨1, X_mem_homogeneousSubmodule_one i⟩)
    (adjoin_range_X_gradeZero_eq_top R _)


-- @@ L146-156 verbatim
variable (n R) in
/-- The **standard affine open cover** of `ℙ(n; R)` by the `n + 1` charts `𝔸ⁿ_R`. -/
noncomputable def affineOpenCover : ℙ(n; R).AffineOpenCover where
  I₀ := Fin (n + 1)
  X _ := .of (MvPolynomial (Fin n) R)
  f := chart
  idx x := (TopologicalSpace.Opens.mem_iSup.mp ((iSup_U n R).ge (Set.mem_univ x))).choose
  covers x := by
    change x ∈ (chart _).opensRange
    rw [opensRange_chart]
    exact (TopologicalSpace.Opens.mem_iSup.mp ((iSup_U n R).ge (Set.mem_univ x))).choose_spec


-- @@ L158-159 verbatim
@[simp]
lemma affineOpenCover_f (i : Fin (n + 1)) : (affineOpenCover n R).f i = chart i := rfl


-- @@ L161-169 verbatim
/-- The chart `i` meets `U j` in the basic open of the coordinate `Xⱼ / Xᵢ`. -/
lemma chart_preimage_U (i j : Fin (n + 1)) :
    chart i ⁻¹ᵁ U n R j = PrimeSpectrum.basicOpen (dehomogenize R i (X j)) := by
  rw [chart, Scheme.Hom.comp_preimage, U,
    Proj.awayι_preimage_basicOpen _ _ _ (X_mem_homogeneousSubmodule_one j) Nat.one_pos,
    SpecMap_preimage_basicOpen]
  simp only [CommRingCat.hom_ofHom, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    awayXEquiv_symm_apply]
  rw [fromAwayX_mk, pow_one]


-- @@ L171-171 verbatim
section intersections


-- @@ L173-176 verbatim
variable (n R) in
/-- The intersection `⨅_{j ∈ I} U j = D₊(∏_{j ∈ I} Xⱼ)` of standard opens. -/
noncomputable abbrev UI (I : Finset (Fin (n + 1))) : ℙ(n; R).Opens :=
  Proj.basicOpen 𝒜 (∏ j ∈ I, X j)


-- @@ L178-184 verbatim
lemma UI_eq_iInf (I : Finset (Fin (n + 1))) : UI n R I = ⨅ j ∈ I, U n R j := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [UI, Proj.basicOpen_one]
  | insert a s ha ih =>
    simp only [UI] at ih ⊢
    rw [Finset.prod_insert ha, Proj.basicOpen_mul, ih, Finset.iInf_insert, U]


-- @@ L186-188 verbatim
@[simp]
lemma UI_singleton (i : Fin (n + 1)) : UI n R {i} = U n R i := by
  simp [UI, U]


-- @@ L190-192 verbatim
lemma UI_le_U {I : Finset (Fin (n + 1))} {i : Fin (n + 1)} (hi : i ∈ I) : UI n R I ≤ U n R i := by
  rw [UI_eq_iInf]
  exact iInf₂_le i hi


-- @@ L194-195 verbatim
lemma card_pos_of_mem {I : Finset (Fin (n + 1))} {i : Fin (n + 1)} (hi : i ∈ I) : 0 < I.card :=
  Finset.card_pos.mpr ⟨i, hi⟩


-- @@ L197-199 verbatim
lemma isAffineOpen_UI {I : Finset (Fin (n + 1))} {i : Fin (n + 1)} (hi : i ∈ I) :
    IsAffineOpen (UI n R I) :=
  Proj.isAffineOpen_basicOpen _ _ (prod_X_mem_homogeneousSubmodule I) (card_pos_of_mem hi)


-- @@ L201-214 verbatim
/-- **The intersection `UI I` in the chart `i ∈ I`**: it is the spectrum of the chart ring
`R[Y₀, …, Yₙ₋₁]` localised away from `dehomogenize i (∏_{j ∈ I} Xⱼ) = ∏_{j ∈ I, j ≠ i} Y_j`. -/
noncomputable def UIIsoSpec (i : Fin (n + 1)) (I : Finset (Fin (n + 1))) (hi : i ∈ I) :
    (UI n R I).toScheme ≅
      Spec (.of (Localization.Away (dehomogenize R i (∏ j ∈ I, X j)))) :=
  Proj.basicOpenIsoSpec 𝒜 _ (prod_X_mem_homogeneousSubmodule I) (card_pos_of_mem hi) ≪≫
    { hom := Spec.map (CommRingCat.ofHom (awayProdXEquiv R i I hi).toRingHom)
      inv := Spec.map (CommRingCat.ofHom (awayProdXEquiv R i I hi).symm.toRingHom)
      hom_inv_id := by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← RingEquiv.toRingHom_trans,
          RingEquiv.symm_trans_self, RingEquiv.toRingHom_refl, CommRingCat.ofHom_id, Spec.map_id]
      inv_hom_id := by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← RingEquiv.toRingHom_trans,
          RingEquiv.self_trans_symm, RingEquiv.toRingHom_refl, CommRingCat.ofHom_id, Spec.map_id] }


-- @@ L216-239 verbatim
/-- `UIIsoSpec` is compatible with the chart: the inclusion `UI I ⊆ ℙ(n; R)` is
`Spec R[Y][1/f] ⟶ Spec R[Y] ⟶ ℙ(n; R)`. -/
@[reassoc]
lemma UIIsoSpec_inv_ι (i : Fin (n + 1)) (I : Finset (Fin (n + 1))) (hi : i ∈ I) :
    (UIIsoSpec i I hi).inv ≫ (UI n R I).ι =
      Spec.map (CommRingCat.ofHom (algebraMap _ _)) ≫ chart i := by
  have hx := (Finset.mul_prod_erase I (fun j ↦ (X j : MvPolynomial (Fin (n + 1)) R)) hi).symm
  have hg := prod_X_mem_homogeneousSubmodule (R := R) (I.erase i)
  have h₁ : (Proj.basicOpenIsoSpec 𝒜 _ (prod_X_mem_homogeneousSubmodule I)
      (card_pos_of_mem hi)).inv ≫ (UI n R I).ι =
      Spec.map (CommRingCat.ofHom (awayMap 𝒜 hg hx)) ≫
        Proj.awayι 𝒜 (X i) (X_mem_homogeneousSubmodule_one i) Nat.one_pos := by
    rw [Proj.SpecMap_awayMap_awayι]
    rfl
  rw [UIIsoSpec, Iso.trans_inv, Category.assoc, h₁, chart, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext p : 2
  apply (awayProdXEquiv R i I hi).injective
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom,
    RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, RingEquiv.apply_symm_apply,
    RingEquiv.toRingHom_eq_coe, awayXEquiv_symm_apply, awayProdXEquiv_algebraMap,
    toAwayProdX, toAwayX_fromAwayX]


-- @@ L241-241 verbatim
end intersections


-- @@ L243-243 verbatim
end ProjectiveSpace


-- @@ L245-245 verbatim
end AlgebraicGeometry
