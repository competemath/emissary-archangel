/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.GAGA.HoledRect
import Oka.Analytification.GAGA.ProjectiveSpaceAn
import Oka.Geometry.RingedSpace.LocallyRingedSpace.OpenImmersionCohomology
import Oka.Topology.Sheaves.Cohomology.Dimension


-- @@ L11-32 verbatim
/-!
# Acyclicity of `𝒪` on the chart intersections of `ℙⁿ_an`

For `I : Finset (Fin (n + 1))` let `W_I = π⁻¹(UI I) ⊆ ℙⁿ_an`
(`ComplexAnalytic.projectiveSpaceAn.opensUI I`), the intersection of the images of the charts
`j ∈ I` (`ComplexAnalytic.projectiveSpaceAn.chartOpens j`). For `i ∈ I`, the chart `i` maps the
open `(ℂ^×)^P × ℂ^{n - P} ⊆ ℂⁿ` (`ComplexAnalytic.projectiveSpaceAn.puncturedOpens P`, with
`P = {m | i.succAbove m ∈ I}`) isomorphically onto `W_I`. Since the charts are open immersions,
the cohomology of the structure sheaf is transported
(`AlgebraicGeometry.LocallyRingedSpace.subsingleton_H_structureSheafAb_of_image_eq`).

## Main results

* `ComplexAnalytic.projectiveSpaceAn.subsingleton_H_opensUI`: if `𝒪` is acyclic on every
  `(ℂ^×)^P × ℂ^{n - P} ⊆ ℂⁿ` (Theorem B, taken as hypothesis `hD`), then `𝒪` is acyclic on every
  `W_I`, `I ≠ ∅`.
* `ComplexAnalytic.projectiveSpaceAn.subsingleton_H_iInf_chartOpens`: the same for
  `⨅ i ∈ I, chartOpens i`, in the shape required by `TopCat.Sheaf.subsingleton_H_of_iSup_eq_top`
  (the chart images cover, `iSup_chartOpens`).
* `ComplexAnalytic.projectiveSpaceAn.subsingleton_H_structureSheafAb`: under `hD`,
  `Hᵠ(ℙⁿ_an, 𝒪) = 0` for `q ≥ n + 1`.
-/


-- @@ L34-34 verbatim
universe u


-- @@ L36-36 verbatim
open CategoryTheory TopologicalSpace Topology AlgebraicGeometry


-- @@ L38-38 verbatim
namespace ComplexAnalytic.projectiveSpaceAn


-- @@ L40-40 verbatim
open AnalyticSpace


-- @@ L42-42 verbatim
variable {n : ℕ}


-- @@ L44-44 verbatim
noncomputable section


-- @@ L46-53 verbatim
lemma isOpen_puncturedSet (P : Set (ULift.{u} (Fin n))) :
    IsOpen (Complex.HoledRect.puncturedSet P) := by
  have : Complex.HoledRect.puncturedSet P = ⋂ k ∈ P, {x : ULift.{u} (Fin n) → ℂ | x k ≠ 0} := by
    ext x
    simp [Complex.HoledRect.puncturedSet]
  rw [this]
  exact (Set.toFinite P).isOpen_biInter fun k _ =>
    isOpen_ne_fun (continuous_apply k) continuous_const


-- @@ L55-59 verbatim
/-- The open `(ℂ^×)^P × ℂ^{n - P} = {z | zₖ ≠ 0 for k ∈ P}` of `ℂⁿ`
(`Complex.HoledRect.puncturedSet P`). -/
def puncturedOpens (P : Set (ULift.{u} (Fin n))) :
    Opens (AnalyticSpace.complexAffineSpace.{u} n).toLocallyRingedSpace.toPresheafedSpace :=
  ⟨Complex.HoledRect.puncturedSet P, isOpen_puncturedSet P⟩


-- @@ L61-64 verbatim
@[simp]
lemma coe_puncturedOpens (P : Set (ULift.{u} (Fin n))) :
    SetLike.coe (puncturedOpens P) = Complex.HoledRect.puncturedSet P :=
  rfl


-- @@ L66-70 verbatim
/-- The open `π⁻¹(UI I) = ⋂_{j ∈ I} (image of the chart j)` of `ℙⁿ_an`. -/
def opensUI (I : Finset (Fin (n + 1))) :
    Opens (projectiveSpaceAn.{u} n).toLocallyRingedSpace.toPresheafedSpace :=
  (Opens.map (analytificationπ (projectiveSpace.{u} n)).left.base).obj
    (ProjectiveSpace.UI n (ULift.{u} ℂ) I)


-- @@ L72-76 expanded
@[simp]
lemma coe_opensUI (I : Finset (Fin (n + 1))) :
    (opensUI.{u} I : Set (projectiveSpaceAn.{u} n)) =
      π n ⁻¹' (ProjectiveSpace.UI n (ULift.{u} ℂ) I : Set (ProjectiveSpace n (ULift.{u} ℂ))) :=
  rfl


-- @@ L78-81 verbatim
/-- The image of the chart `i` of `ℙⁿ_an`, an open. -/
def chartOpens (i : Fin (n + 1)) :
    Opens (projectiveSpaceAn.{u} n).toLocallyRingedSpace.toPresheafedSpace :=
  ⟨Set.range (projectiveSpaceAnChart.{u} i).toLRSHom.base, (isOpenEmbedding_chart i).isOpen_range⟩


-- @@ L83-87 verbatim
@[simp]
lemma coe_chartOpens (i : Fin (n + 1)) :
    (chartOpens.{u} i : Set (projectiveSpaceAn.{u} n)) =
      Set.range (projectiveSpaceAnChart.{u} i).toLRSHom.base :=
  rfl


-- @@ L89-92 verbatim
/-- The chart images cover `ℙⁿ_an`. -/
lemma iSup_chartOpens : ⨆ i, chartOpens.{u} (n := n) i = ⊤ := by
  ext x
  simp only [Opens.coe_iSup, coe_chartOpens, Opens.coe_top, iUnion_range_chart]


-- @@ L94-104 verbatim
/-- `π⁻¹(UI I)` is the intersection of the chart images `j ∈ I`. -/
lemma iInf_chartOpens (I : Finset (Fin (n + 1))) :
    ⨅ i ∈ I, chartOpens.{u} (n := n) i = opensUI I := by
  apply SetLike.coe_injective
  rw [coe_opensUI, preimage_UI]
  ext x
  simp only [Opens.coe_iInf, Set.mem_iInter]
  refine forall_congr' fun j => ?_
  by_cases hj : j ∈ I
  · simp [hj]
  · simp [hj]


-- @@ L106-120 verbatim
/-- In the chart `i ∈ I`, the locus where the homogeneous coordinates `j ∈ I` do not vanish is
`(ℂ^×)^P × ℂ^{n - P}` with `P = {m | i.succAbove m ∈ I}`. -/
lemma setOf_homogCoord_ne_zero {I : Finset (Fin (n + 1))} {i : Fin (n + 1)} (hi : i ∈ I) :
    {z : AnalyticSpace.complexAffineSpace.{u} n | ∀ j ∈ I, homogCoord i z j ≠ 0} =
      Complex.HoledRect.puncturedSet {k : ULift.{u} (Fin n) | i.succAbove k.down ∈ I} := by
  ext z
  simp only [Set.mem_setOf_eq, Complex.HoledRect.puncturedSet]
  constructor
  · intro h k hk
    have := h _ hk
    simpa [homogCoord, toFin] using this
  · intro h j hj
    obtain rfl | ⟨m, rfl⟩ := Fin.eq_self_or_eq_succAbove i j
    · simp
    · simpa [homogCoord, toFin] using h ⟨m⟩ hj


-- @@ L122-130 verbatim
/-- The chart `i ∈ I` maps `(ℂ^×)^P × ℂ^{n - P}`, `P = {m | i.succAbove m ∈ I}`, onto
`π⁻¹(UI I)`. -/
lemma image_chart_puncturedOpens {I : Finset (Fin (n + 1))} {i : Fin (n + 1)} (hi : i ∈ I) :
    (projectiveSpaceAnChart.{u} i).toLRSHom.base ''
        (puncturedOpens {k : ULift.{u} (Fin n) | i.succAbove k.down ∈ I} :
          Set (AnalyticSpace.complexAffineSpace.{u} n)) =
      (opensUI.{u} I : Set (projectiveSpaceAn.{u} n)) := by
  rw [coe_opensUI, preimage_UI_eq_image hi, setOf_homogCoord_ne_zero hi]
  rfl


-- @@ L132-135 verbatim
variable
  (hD : ∀ (P : Set (ULift.{u} (Fin n))) (q : ℕ), 0 < q →
    Subsingleton (TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen (puncturedOpens P)).obj
      (AnalyticSpace.complexAffineSpace.{u} n).toLocallyRingedSpace.structureSheafAb) q))


-- @@ L137-146 verbatim
include hD in
/-- **`𝒪` is acyclic on `π⁻¹(UI I) ⊆ ℙⁿ_an`**, given that it is acyclic on the opens
`(ℂ^×)^P × ℂ^{n - P}` of `ℂⁿ` (Theorem B, hypothesis `hD`). -/
theorem subsingleton_H_opensUI {I : Finset (Fin (n + 1))} (hI : I.Nonempty) (q : ℕ)
    (hq : 0 < q) :
    Subsingleton (TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen (opensUI.{u} I)).obj
      (projectiveSpaceAn.{u} n).toLocallyRingedSpace.structureSheafAb) q) := by
  obtain ⟨i, hi⟩ := hI
  exact LocallyRingedSpace.subsingleton_H_structureSheafAb_of_image_eq
    (projectiveSpaceAnChart.{u} i).toLRSHom _ (image_chart_puncturedOpens hi) q (hD _ q hq)


-- @@ L148-156 verbatim
include hD in
/-- **`𝒪` is acyclic on the nonempty finite intersections of the chart images of `ℙⁿ_an`**,
given Theorem B on the opens `(ℂ^×)^P × ℂ^{n - P}` of `ℂⁿ` (hypothesis `hD`). -/
theorem subsingleton_H_iInf_chartOpens (I : Finset (Fin (n + 1))) (hI : I.Nonempty) (q : ℕ)
    (hq : 0 < q) :
    Subsingleton (TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen (⨅ i ∈ I, chartOpens.{u} i)).obj
      (projectiveSpaceAn.{u} n).toLocallyRingedSpace.structureSheafAb) q) := by
  rw [iInf_chartOpens]
  exact subsingleton_H_opensUI hD hI q hq


-- @@ L158-165 verbatim
include hD in
/-- **`Hᵠ(ℙⁿ_an, 𝒪) = 0` for `q > n`**, given Theorem B on the opens `(ℂ^×)^P × ℂ^{n - P}` of
`ℂⁿ` (hypothesis `hD`). -/
theorem subsingleton_H_structureSheafAb (q : ℕ) (hq : n + 1 ≤ q) :
    Subsingleton (TopCat.Sheaf.H
      (projectiveSpaceAn.{u} n).toLocallyRingedSpace.structureSheafAb q) :=
  TopCat.Sheaf.subsingleton_H_of_iSup_eq_top _ chartOpens iSup_chartOpens
    (subsingleton_H_iInf_chartOpens hD) q (by simpa using hq)


-- @@ L167-167 verbatim
end


-- @@ L169-169 verbatim
end ComplexAnalytic.projectiveSpaceAn
