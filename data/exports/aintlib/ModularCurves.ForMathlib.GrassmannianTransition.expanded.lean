/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse


-- @@ L11-35 verbatim
/-!
# The Grassmannian chart-transition ring layer ([NISOG-GRASS], [GR-E3] generic half)

The gluing data for the chart atlas of `Grass(k, n)`, at the level of generic matrix
rings — deliberately **Grassmannian-free** (no import of `GrassmannianChart`): the
pointwise spec tying these to `Module.Grassmannian.chartMatrix` is a separate increment
(artifact, [GR-E] design, single-writer discipline).

For two coordinate charts `ι ι' : Fin k ↪ Fin n` of the Grassmannian of rank-`k`
quotients of `R^n`:

* `Grassmannian.ChartRing R k n ι` — the ι-chart coordinate ring
  `R[X_{j,i} : j ∉ range ι, i : Fin k]` (the chart is `𝔸^{k(n−k)}`, Stacks 089T (3));
* `Grassmannian.Transition.matrix ι ι'` — the generic transition matrix `T`: column
  `i₂` is the ι'-tuple's `i₂`-th coordinate vector expressed through the generic
  ι-retraction (Kronecker column when `ι' i₂ ∈ range ι`, variable column otherwise);
* `Grassmannian.Transition.det ι ι'` — its determinant, the gluing denominator: the
  ι∩ι'-overlap is the basic open `D(det)` of the ι-chart ([GR-E2] criterion);
* `Grassmannian.Transition.ringHom ι ι'` — the transition
  `ChartRing ι' → (ChartRing ι)[1/det]`, sending the generic ι'-variable `X_{j',i'}` to
  the `i'`-entry of `T⁻¹ · (ι-coordinate column of j')` — the [GR-F] glue datum.

Decomposition artifact: `.mathlib-quality/decomposition-nisog-grass.md` ([STREAM-FP],
fable-FP, [GR-E] design 2026-07-09).
-/


-- @@ L37-37 verbatim
universe u


-- @@ L39-39 verbatim
namespace Module.Grassmannian


-- @@ L41-41 verbatim
open MvPolynomial


-- @@ L43-43 verbatim
variable (R : Type u) [CommRing R] {k n : ℕ}


-- @@ L45-48 verbatim
/-- The coordinate ring of the ι-chart of `Grass(k, R^n)`: polynomials in one variable
per matrix entry `(j, i)`, `j` a complementary coordinate, `i : Fin k`. -/
abbrev ChartRing (ι : Fin k ↪ Fin n) : Type u :=
  MvPolynomial ({j : Fin n // j ∉ Set.range ι} × Fin k) R


-- @@ L50-50 verbatim
namespace Transition


-- @@ L52-52 verbatim
open Matrix


-- @@ L54-54 verbatim
variable {R} (ι ι' : Fin k ↪ Fin n)


-- @@ L56-62 verbatim
/-- The generic ι-coordinate column of an arbitrary index `j : Fin n`: the `ι`-indexed
Kronecker vector when `j = ι i₀`, the generic variable column when `j ∉ range ι`. This
is "the generic retraction evaluated at the `j`-th basis vector". -/
noncomputable def column (j : Fin n) : Fin k → ChartRing R ι :=
  if h : j ∈ Set.range ι then
    Pi.single ((Equiv.ofInjective ι ι.injective).symm ⟨j, h⟩) 1
  else fun i => X (⟨j, h⟩, i)


-- @@ L64-68 verbatim
@[simp] lemma column_mem (i₀ : Fin k) :
    column ι (ι i₀) = (Pi.single i₀ 1 : Fin k → ChartRing R ι) := by
  rw [column, dif_pos ⟨i₀, rfl⟩]
  congr 1
  exact Equiv.ofInjective_symm_apply ι.injective i₀


-- @@ L70-72 verbatim
lemma column_notMem {j : Fin n} (h : j ∉ Set.range ι) :
    column ι j = fun i => (X (⟨j, h⟩, i) : ChartRing R ι) := by
  rw [column, dif_neg h]


-- @@ L74-78 verbatim
/-- The generic transition matrix from the ι-chart to the ι'-chart: `T i₁ i₂` is the
`i₁`-entry of the generic ι-coordinate column of `ι' i₂`. On the locus where its
determinant is invertible, the ι'-tuple is also a quotient basis ([GR-E2]). -/
noncomputable def matrix : Matrix (Fin k) (Fin k) (ChartRing R ι) :=
  Matrix.of fun i₁ i₂ => column ι (ι' i₂) i₁


-- @@ L80-82 verbatim
/-- The transition determinant — the denominator of the chart transition, cutting the
overlap `D(det)` out of the ι-chart. -/
noncomputable def det : ChartRing R ι := (matrix ι ι').det


-- @@ L84-87 verbatim
/-- The localized transition matrix over the overlap ring `(ChartRing ι)[1/det]`. -/
noncomputable def matrixAway :
    Matrix (Fin k) (Fin k) (Localization.Away (det (R := R) ι ι')) :=
  (matrix ι ι').map (algebraMap (ChartRing R ι) (Localization.Away (det (R := R) ι ι')))


-- @@ L89-92 verbatim
/-- The image of the transition determinant is a unit on the overlap. -/
lemma isUnit_det_matrixAway : IsUnit (matrixAway ι ι' (R := R)).det := by
  rw [matrixAway, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact IsLocalization.Away.algebraMap_isUnit (det (R := R) ι ι')


-- @@ L94-105 verbatim
/-- **[GR-E3]** The chart-transition ring map `ChartRing ι' → (ChartRing ι)[1/det]`:
the generic ι'-variable `X_{j', i'}` goes to the `i'`-entry of `T⁻¹` applied to the
generic ι-column of `j'` — "express the ι'-retraction through the ι-retraction and the
inverted transition matrix". The [GR-F] glue datum. -/
noncomputable def ringHom :
    ChartRing R ι' →+* Localization.Away (det (R := R) ι ι') :=
  MvPolynomial.eval₂Hom
    ((algebraMap (ChartRing R ι) (Localization.Away (det (R := R) ι ι'))).comp
      (MvPolynomial.C : R →+* ChartRing R ι))
    (fun p => ((matrixAway (R := R) ι ι')⁻¹ *ᵥ
      fun i₁ => algebraMap (ChartRing R ι) (Localization.Away (det (R := R) ι ι'))
        (column ι p.1.1 i₁)) p.2)


-- @@ L107-108 verbatim
@[simp] lemma matrix_apply (i₁ i₂ : Fin k) :
    matrix (R := R) ι ι' i₁ i₂ = column ι (ι' i₂) i₁ := rfl


-- @@ L110-115 verbatim
private lemma mulVec_single_one {S : Type u} [CommRing S]
    (M : Matrix (Fin k) (Fin k) S) (j : Fin k) :
    M *ᵥ Pi.single j 1 = fun i => M i j := by
  funext i
  rw [Matrix.mulVec_single]
  simp


-- @@ L117-120 verbatim
@[simp] lemma matrixAway_apply (i₁ i₂ : Fin k) :
    matrixAway (R := R) ι ι' i₁ i₂
      = algebraMap (ChartRing R ι) (Localization.Away (det (R := R) ι ι'))
          (column ι (ι' i₂) i₁) := rfl


-- @@ L122-130 verbatim
/-- The image of a delta column under the coefficient embedding is a delta column. -/
private lemma algebraMap_comp_single (i₂ : Fin k) :
    (fun i₁ => algebraMap (ChartRing R ι) (Localization.Away (det (R := R) ι ι'))
        (column ι (ι i₂) i₁))
      = Pi.single i₂ 1 := by
  funext l
  rw [congrFun (column_mem ι i₂) l, Pi.single_apply, Pi.single_apply,
    apply_ite (algebraMap (ChartRing R ι) (Localization.Away (det (R := R) ι ι'))),
    map_one, map_zero]


-- @@ L132-138 verbatim
/-- The localized forward transition matrix has delta columns at indices hit by `ι`. -/
private lemma matrixAway_mulVec_single {i₀ i₂ : Fin k} (hcol : ι' i₀ = ι i₂) :
    matrixAway (R := R) ι ι' *ᵥ Pi.single i₀ 1 = Pi.single i₂ 1 := by
  rw [mulVec_single_one]
  funext i₁
  rw [matrixAway_apply, hcol]
  exact congrFun (algebraMap_comp_single ι ι' i₂) i₁


-- @@ L140-143 verbatim
private lemma nonsing_inv_matrixAway_mulVec_single {i₀ i₂ : Fin k} (hcol : ι' i₀ = ι i₂) :
    (matrixAway (R := R) ι ι')⁻¹ *ᵥ Pi.single i₂ 1 = Pi.single i₀ 1 := by
  rw [← matrixAway_mulVec_single ι ι' hcol, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_det_matrixAway ι ι'), Matrix.one_mulVec]


-- @@ L145-165 verbatim
/-- **[GR-F1]** The transition ring map carries the *reverse* transition matrix to the
inverse of the (localized) forward one — the generic content of "the coordinate changes
are mutually inverse on the overlap". -/
lemma map_ringHom_matrix :
    (matrix ι' ι).map ⇑(ringHom (R := R) ι ι') = (matrixAway (R := R) ι ι')⁻¹ := by
  classical
  funext i₁ i₂
  rw [Matrix.map_apply, matrix_apply]
  have hR : (matrixAway (R := R) ι ι')⁻¹ i₁ i₂
      = ((matrixAway (R := R) ι ι')⁻¹ *ᵥ Pi.single i₂ 1) i₁ := by
    rw [mulVec_single_one]
  by_cases hj : ι i₂ ∈ Set.range ι'
  · obtain ⟨i₀, hi₀⟩ := hj
    rw [← hi₀, congrFun (column_mem ι' i₀) i₁, hR,
      nonsing_inv_matrixAway_mulVec_single ι ι' hi₀, Pi.single_apply, Pi.single_apply]
    split <;> simp
  · rw [congrFun (column_notMem ι' hj) i₁, ringHom, eval₂Hom_X']
    rw [show (fun l => algebraMap (ChartRing R ι)
          (Localization.Away (det (R := R) ι ι')) (column ι (ι i₂) l))
        = Pi.single i₂ 1 from algebraMap_comp_single ι ι' i₂,
      hR]


-- @@ L167-174 verbatim
/-- **[GR-F1]** The transition map sends the reverse transition determinant to a unit —
so it extends over the reverse overlap localization. -/
lemma isUnit_ringHom_det :
    IsUnit (ringHom (R := R) ι ι' (det (R := R) ι' ι)) := by
  have hd : det (R := R) ι' ι = (matrix ι' ι).det := rfl
  rw [hd, RingHom.map_det, RingHom.mapMatrix_apply, map_ringHom_matrix]
  exact Matrix.isUnit_det_of_left_inverse
    (Matrix.mul_nonsing_inv _ (isUnit_det_matrixAway ι ι'))


-- @@ L176-180 verbatim
/-- **[GR-F2]** The chart transition on overlap rings — the `Scheme.GlueData` gluing map
at ring level: `(ChartRing ι')[1/det ι'ι] → (ChartRing ι)[1/det ιι']`. -/
noncomputable def ringHomAway :
    Localization.Away (det (R := R) ι' ι) →+* Localization.Away (det (R := R) ι ι') :=
  IsLocalization.Away.lift (det (R := R) ι' ι) (isUnit_ringHom_det ι ι')


-- @@ L182-186 verbatim
lemma ringHomAway_algebraMap (q : ChartRing R ι') :
    ringHomAway ι ι' (algebraMap (ChartRing R ι')
        (Localization.Away (det (R := R) ι' ι)) q)
      = ringHom (R := R) ι ι' q :=
  IsLocalization.Away.lift_eq _ (isUnit_ringHom_det ι ι') q


-- @@ L188-211 verbatim
/-- The transition image of ANY reverse-chart column, uniformly: `ringHom` sends the
ι'-column of `j` to `(matrixAway ι ι')⁻¹` applied to the embedded ι-column of `j`. The
variable case is definitional; the delta case is the inverse-column identity. -/
lemma ringHom_comp_column (j : Fin n) :
    (fun i₁ => ringHom (R := R) ι ι' (column ι' j i₁))
      = (matrixAway (R := R) ι ι')⁻¹ *ᵥ
        (fun i₁ => algebraMap (ChartRing R ι) (Localization.Away (det (R := R) ι ι'))
          (column ι j i₁)) := by
  classical
  by_cases hj : j ∈ Set.range ι'
  · obtain ⟨i₀, rfl⟩ := hj
    have hcol : (fun i₁ => algebraMap (ChartRing R ι)
        (Localization.Away (det (R := R) ι ι')) (column ι (ι' i₀) i₁))
        = matrixAway (R := R) ι ι' *ᵥ Pi.single i₀ 1 := by
      rw [mulVec_single_one]
      funext l
      rw [matrixAway_apply]
    rw [hcol, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_det_matrixAway ι ι'),
      Matrix.one_mulVec]
    funext i₁
    rw [congrFun (column_mem ι' i₀) i₁, Pi.single_apply, Pi.single_apply,
      apply_ite (ringHom (R := R) ι ι'), map_one, map_zero]
  · funext i₁
    rw [congrFun (column_notMem ι' hj) i₁, ringHom, eval₂Hom_X']


-- @@ L213-259 verbatim
/-- Cancellation transport: the `ringHomAway`-image of the ι'-side solution vector is
the embedded ι-column — the pointwise heart of the inverse-pair identity. -/
private lemma ringHomAway_solution_column (j : Fin n) :
    (fun i => ringHomAway (R := R) ι ι'
      (((matrixAway (R := R) ι' ι)⁻¹ *ᵥ
        fun l => algebraMap (ChartRing R ι') (Localization.Away (det (R := R) ι' ι))
          (column ι' j l)) i))
      = fun i => algebraMap (ChartRing R ι) (Localization.Away (det (R := R) ι ι'))
          (column ι j i) := by
  have hdet := isUnit_det_matrixAway (R := R) ι ι'
  have hinj : ∀ v w : Fin k → Localization.Away (det (R := R) ι ι'),
      (matrixAway (R := R) ι ι')⁻¹ *ᵥ v = (matrixAway (R := R) ι ι')⁻¹ *ᵥ w → v = w := by
    intro v w hvw
    have h2 := congrArg (fun u => matrixAway (R := R) ι ι' *ᵥ u) hvw
    simpa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet,
      Matrix.one_mulVec] using h2
  have hmapF : (matrixAway (R := R) ι' ι).map ⇑(ringHomAway (R := R) ι ι')
      = (matrixAway (R := R) ι ι')⁻¹ := by
    have hAM : ⇑(ringHomAway (R := R) ι ι') ∘
        ⇑(algebraMap (ChartRing R ι') (Localization.Away (det (R := R) ι' ι)))
        = ⇑(ringHom (R := R) ι ι') :=
      funext fun q => ringHomAway_algebraMap ι ι' q
    rw [matrixAway, Matrix.map_map, hAM]
    exact map_ringHom_matrix ι ι'
  set z : Fin k → Localization.Away (det (R := R) ι' ι) :=
    (matrixAway (R := R) ι' ι)⁻¹ *ᵥ
      fun l => algebraMap (ChartRing R ι') (Localization.Away (det (R := R) ι' ι))
        (column ι' j l) with hz
  have hMz : matrixAway (R := R) ι' ι *ᵥ z
      = fun l => algebraMap (ChartRing R ι') (Localization.Away (det (R := R) ι' ι))
          (column ι' j l) := by
    rw [hz, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_det_matrixAway ι' ι),
      Matrix.one_mulVec]
  refine hinj _ _ ?_
  conv_lhs => rw [← hmapF]
  funext i
  calc ((matrixAway (R := R) ι' ι).map ⇑(ringHomAway (R := R) ι ι') *ᵥ
        fun l => ringHomAway (R := R) ι ι' (z l)) i
      = ringHomAway (R := R) ι ι' ((matrixAway (R := R) ι' ι *ᵥ z) i) :=
        (RingHom.map_mulVec _ _ _ i).symm
    _ = ringHomAway (R := R) ι ι'
          (algebraMap (ChartRing R ι') (Localization.Away (det (R := R) ι' ι))
            (column ι' j i)) := by rw [hMz]
    _ = ringHom (R := R) ι ι' (column ι' j i) := ringHomAway_algebraMap ι ι' _
    _ = ((matrixAway (R := R) ι ι')⁻¹ *ᵥ
          fun i₁ => algebraMap (ChartRing R ι) (Localization.Away (det (R := R) ι ι'))
            (column ι j i₁)) i := congrFun (ringHom_comp_column ι ι' j) i


-- @@ L261-287 verbatim
/-- **[GR-E4]** The two chart transitions are mutually inverse on the overlap rings —
the `Scheme.GlueData` inverse-pair condition at ring level. -/
theorem ringHomAway_comp_ringHomAway :
    (ringHomAway (R := R) ι ι').comp (ringHomAway ι' ι)
      = RingHom.id (Localization.Away (det (R := R) ι ι')) := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (det (R := R) ι ι')) ?_
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun p => ?_)
  · rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply,
      ringHomAway_algebraMap]
    rw [show ringHom (R := R) ι' ι (C a)
        = algebraMap (ChartRing R ι') (Localization.Away (det (R := R) ι' ι)) (C a) from
      eval₂Hom_C _ _ a]
    rw [ringHomAway_algebraMap]
    rw [show ringHom (R := R) ι ι' (C a)
        = algebraMap (ChartRing R ι) (Localization.Away (det (R := R) ι ι')) (C a) from
      eval₂Hom_C _ _ a]
    rfl
  · obtain ⟨⟨j, hj⟩, i⟩ := p
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply,
      ringHomAway_algebraMap]
    rw [show ringHom (R := R) ι' ι (X (⟨j, hj⟩, i))
        = ((matrixAway (R := R) ι' ι)⁻¹ *ᵥ
            fun l => algebraMap (ChartRing R ι') (Localization.Away (det (R := R) ι' ι))
              (column ι' j l)) i from by rw [ringHom, eval₂Hom_X']]
    rw [congrFun (ringHomAway_solution_column ι ι' j) i,
      congrFun (column_notMem ι hj) i]
    rfl


-- @@ L289-293 verbatim
/-- The self-transition matrix is the identity: every ι-column at an ι-index is a delta
column. -/
lemma matrix_self : matrix (R := R) ι ι = 1 := by
  funext i₁ i₂
  rw [matrix_apply, congrFun (column_mem ι i₂) i₁, Matrix.one_apply, Pi.single_apply]


-- @@ L295-297 verbatim
lemma det_self : det (R := R) ι ι = 1 := by
  have hd : det (R := R) ι ι = (matrix (R := R) ι ι).det := rfl
  rw [hd, matrix_self, Matrix.det_one]


-- @@ L299-312 verbatim
/-- **[GR-F-tid]** The self-transition ring map is the localization embedding. -/
lemma ringHom_self :
    ringHom (R := R) ι ι
      = algebraMap (ChartRing R ι) (Localization.Away (det (R := R) ι ι)) := by
  refine MvPolynomial.ringHom_ext (fun a => eval₂Hom_C _ _ a) (fun p => ?_)
  obtain ⟨⟨j, hj⟩, i⟩ := p
  rw [ringHom, eval₂Hom_X']
  have h1 : matrixAway (R := R) ι ι = 1 := by
    have hm : matrixAway (R := R) ι ι
        = (matrix (R := R) ι ι).map
            (algebraMap (ChartRing R ι) (Localization.Away (det (R := R) ι ι))) := rfl
    rw [hm, matrix_self]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  rw [h1, inv_one, Matrix.one_mulVec, congrFun (column_notMem ι hj) i]


-- @@ L314-322 verbatim
/-- **[GR-F-tid]** The self-transition on the overlap ring is the identity — the
`Scheme.GlueData` `t_id` condition at ring level. -/
theorem ringHomAway_self :
    ringHomAway (R := R) ι ι
      = RingHom.id (Localization.Away (det (R := R) ι ι)) := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (det (R := R) ι ι)) ?_
  refine RingHom.ext fun q => ?_
  rw [RingHom.comp_apply, RingHom.comp_apply, ringHomAway_algebraMap, ringHom_self,
    RingHom.id_apply]


-- @@ L324-344 verbatim
/-- Pure matrix transport: a ring hom pushes through `M⁻¹ *ᵥ ·` when both determinants
are units — the reusable core of every transition-composite computation. -/
lemma map_inv_mulVec {S S' : Type u} [CommRing S] [CommRing S'] (F : S →+* S')
    (M : Matrix (Fin k) (Fin k) S) (hM : IsUnit M.det) (hM' : IsUnit (M.map ⇑F).det)
    (w : Fin k → S) :
    (fun i => F ((M⁻¹ *ᵥ w) i)) = (M.map ⇑F)⁻¹ *ᵥ (fun i => F (w i)) := by
  have hinj : ∀ v v' : Fin k → S',
      (M.map ⇑F) *ᵥ v = (M.map ⇑F) *ᵥ v' → v = v' := by
    intro v v' hvv
    have h2 := congrArg (fun u => (M.map ⇑F)⁻¹ *ᵥ u) hvv
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hM',
      Matrix.one_mulVec] using h2
  refine hinj _ _ ?_
  have hMw : M *ᵥ (M⁻¹ *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hM, Matrix.one_mulVec]
  have hleft : (M.map ⇑F) *ᵥ (fun i => F ((M⁻¹ *ᵥ w) i)) = fun i => F (w i) := by
    funext i
    calc ((M.map ⇑F) *ᵥ fun l => F ((M⁻¹ *ᵥ w) l)) i
        = F ((M *ᵥ (M⁻¹ *ᵥ w)) i) := (RingHom.map_mulVec _ _ _ i).symm
      _ = F (w i) := by rw [hMw]
  rw [hleft, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hM', Matrix.one_mulVec]


-- @@ L346-370 verbatim
/-- The transition rule: composing any ring hom out of the overlap with the transition
map sends the reverse-chart columns to the mapped-inverse-matrix solution of the
forward columns — the uniform engine for transition composites (generalizes
`ringHomAway_solution_column`). -/
lemma comp_ringHom_column {S : Type u} [CommRing S]
    (F : Localization.Away (det (R := R) ι ι') →+* S)
    (hdet : IsUnit ((matrix (R := R) ι ι').map (⇑F ∘ ⇑(algebraMap (ChartRing R ι)
      (Localization.Away (det (R := R) ι ι'))))).det)
    (j : Fin n) :
    (fun i => F (ringHom (R := R) ι ι' (column ι' j i)))
      = ((matrix (R := R) ι ι').map (⇑F ∘ ⇑(algebraMap (ChartRing R ι)
          (Localization.Away (det (R := R) ι ι')))))⁻¹ *ᵥ
        (fun i => F (algebraMap (ChartRing R ι)
          (Localization.Away (det (R := R) ι ι')) (column ι j i))) := by
  have hmm : (matrixAway (R := R) ι ι').map ⇑F
      = (matrix (R := R) ι ι').map (⇑F ∘ ⇑(algebraMap (ChartRing R ι)
          (Localization.Away (det (R := R) ι ι')))) := by
    rw [matrixAway, Matrix.map_map]
  have hstep : (fun i => F (ringHom (R := R) ι ι' (column ι' j i)))
      = fun i => F (((matrixAway (R := R) ι ι')⁻¹ *ᵥ
          fun l => algebraMap (ChartRing R ι)
            (Localization.Away (det (R := R) ι ι')) (column ι j l)) i) := by
    funext i
    rw [congrFun (ringHom_comp_column (R := R) ι ι' j) i]
  rw [hstep, map_inv_mulVec F _ (isUnit_det_matrixAway ι ι') (hmm ▸ hdet), hmm]


-- @@ L372-381 verbatim
/-- Ring homs commute with nonsingular inversion (unit determinant). -/
lemma map_nonsing_inv {S S' : Type u} [CommRing S] [CommRing S'] (F : S →+* S')
    (M : Matrix (Fin k) (Fin k) S) (hM : IsUnit M.det) :
    (M.map ⇑F)⁻¹ = M⁻¹.map ⇑F := by
  refine Matrix.inv_eq_left_inv ?_
  have hmul : (M⁻¹.map ⇑F) * (M.map ⇑F) = (M⁻¹ * M).map ⇑F := by
    funext i₁ i₂
    simp [Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul]
  rw [hmul, Matrix.nonsing_inv_mul _ hM]
  exact Matrix.map_one _ (map_zero _) (map_one _)


-- @@ L383-383 verbatim
section Triple


-- @@ L385-385 verbatim
variable (ι'' : Fin k ↪ Fin n)


-- @@ L387-399 verbatim
/-- **[GR-F3]** The composite-transition matrix identity: the `ringHom ι ι'`-image of
the ι'→ι'' transition matrix factors as `(matrixAway ι ι')⁻¹ *` (embedded ι→ι''
matrix) — column-by-column, two applications of the master column identity. -/
lemma map_ringHom_matrix_triple :
    (matrix (R := R) ι' ι'').map ⇑(ringHom (R := R) ι ι')
      = (matrixAway (R := R) ι ι')⁻¹ *
        (matrix (R := R) ι ι'').map
          (algebraMap (ChartRing R ι) (Localization.Away (det (R := R) ι ι'))) := by
  funext i₁ i₂
  rw [Matrix.map_apply, matrix_apply, Matrix.mul_apply]
  have hcol := congrFun (ringHom_comp_column (R := R) ι ι' (ι'' i₂)) i₁
  rw [hcol]
  simp [Matrix.mulVec, dotProduct, Matrix.map_apply, matrix_apply]


-- @@ L401-412 verbatim
/-- **[GR-F3]** Determinant factorization of the composite transition: the
`ringHom ι ι'`-image of `det ι' ι''` is (a unit) × (the embedded `det ι ι''`) — so it
becomes a unit exactly where `det ι ι''` does, i.e. on the triple overlap. -/
lemma ringHom_det_triple :
    ringHom (R := R) ι ι' (det (R := R) ι' ι'')
      = ((matrixAway (R := R) ι ι')⁻¹).det *
        algebraMap (ChartRing R ι) (Localization.Away (det (R := R) ι ι'))
          (det (R := R) ι ι'') := by
  have hd : det (R := R) ι' ι'' = (matrix (R := R) ι' ι'').det := rfl
  have hd' : det (R := R) ι ι'' = (matrix (R := R) ι ι'').det := rfl
  rw [hd, hd', RingHom.map_det, RingHom.mapMatrix_apply, map_ringHom_matrix_triple,
    Matrix.det_mul, RingHom.map_det, RingHom.mapMatrix_apply]


-- @@ L414-424 verbatim
/-- **[GR-F3]** The unit form: on any ring where the embedded `det ι ι''` becomes a
unit, so does the `ringHom ι ι'`-image of `det ι' ι''` — the existence condition for
the GlueData `t'`-legs on the triple overlap. -/
lemma isUnit_map_ringHom_det_triple {S : Type u} [CommRing S]
    (g : Localization.Away (det (R := R) ι ι') →+* S)
    (hg : IsUnit (g (algebraMap (ChartRing R ι)
      (Localization.Away (det (R := R) ι ι')) (det (R := R) ι ι'')))) :
    IsUnit (g (ringHom (R := R) ι ι' (det (R := R) ι' ι''))) := by
  rw [ringHom_det_triple, map_mul]
  exact ((Matrix.isUnit_det_of_left_inverse
    (Matrix.mul_nonsing_inv _ (isUnit_det_matrixAway ι ι'))).map g).mul hg


-- @@ L426-426 verbatim
end Triple


-- @@ L428-428 verbatim
end Transition


-- @@ L430-430 verbatim
end Module.Grassmannian
