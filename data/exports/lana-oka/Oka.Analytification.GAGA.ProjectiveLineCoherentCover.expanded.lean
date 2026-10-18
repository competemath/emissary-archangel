/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.GAGA.Proper.RelativeTwistCechAn
import Oka.Topology.Sheaves.Cohomology.MayerVietorisNatural


-- @@ L9-33 verbatim
/-!
# Chart boxes on `U × ℙ¹` and Theorem B for the structure sheaf

Let `P = ℙ(1; ℂ[y₀, …, y_{m-1}])` and `P^an = ℂᵐ × ℙ¹`. A point with base coordinates `y` and
fibre coordinate `z` in the chart `i` is `chartPt i (y, z)`; the chart `0` has homogeneous
coordinates `[1 : z]`, the chart `1` has `[z : 1]`, and `chartPt 0 (y, z) = chartPt 1 (y, z⁻¹)`
for `z ≠ 0` (`chartPt_zero_eq_chartPt_one`). For an open `S ⊆ ℂᵐ × ℂ`, `chartBox i S` is its
image in the chart `i`.

For an open box `B ⊆ ℂᵐ` and open rectangles `Q₀`, `Q₁ ⊆ ℂ` with `chartBox 0 (B × Q₀)` and
`chartBox 1 (B × Q₁)` covering `B × ℙ¹`, we show that the structure sheaf is acyclic on both
chart boxes (they are open boxes in `ℂ^{1+m}`) and on their intersection, which is not a box.
The latter follows from the Mayer–Vietoris sequence, since `Hᵠ(B × ℙ¹, 𝒪) = 0` for `q ≥ 2`
(again by Mayer–Vietoris, for the cover by `B × ℂ`, `B × ℂ` with intersection `B × ℂ^×`).

## Main results

- `TopCat.Sheaf.H_sup_eq_zero`, `TopCat.Sheaf.H_one_sup_eq_zero`, `TopCat.Sheaf.H_inf_eq_zero`:
  vanishing statements from the Mayer–Vietoris sequence of two opens.
- `ComplexAnalytic.relProjectiveLine.subsingleton_H_chartBox`: Theorem B on chart boxes.
- `ComplexAnalytic.relProjectiveLine.subsingleton_H_tube_structureSheafAb`:
  `Hᵠ(B × ℙ¹, 𝒪) = 0` for `q ≥ 2`.
- `ComplexAnalytic.relProjectiveLine.subsingleton_H_chartBox_inf`: Theorem B on the intersection
  of two chart boxes covering `B × ℙ¹`.
-/


-- @@ L35-35 verbatim
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry


-- @@ L37-37 verbatim
universe u


-- @@ L39-39 verbatim
namespace TopCat.Sheaf


-- @@ L41-41 verbatim
open MayerVietoris


-- @@ L43-43 verbatim
variable {X : TopCat.{u}} {A B W W' : Opens X} (F : AbSheaf X)


-- @@ L45-60 verbatim
/-- **Mayer–Vietoris, vanishing on the union**: `Hᵠ⁺¹(A ∪ B, F) = 0` if `Hᵠ(A ∩ B, F) = 0` and
`Hᵠ⁺¹(A, F) = Hᵠ⁺¹(B, F) = 0`. -/
lemma H_sup_eq_zero (hW : A ⊔ B = W) (hW' : A ⊓ B = W') {q : ℕ}
    (hAB : ∀ x : H ((restrictOpen W').obj F) q, x = 0)
    (hA : ∀ x : H ((restrictOpen A).obj F) (q + 1), x = 0)
    (hB : ∀ x : H ((restrictOpen B).obj F) (q + 1), x = 0)
    (x : H ((restrictOpen W).obj F) (q + 1)) : x = 0 := by
  subst hW hW'
  obtain ⟨x, rfl⟩ := (H'AddEquiv (A ⊔ B) F (q + 1)).surjective x
  suffices hx : x = 0 by rw [hx, map_zero]
  have h0 : toProd A B F (q + 1) x = 0 :=
    Prod.ext ((H'AddEquiv A F (q + 1)).injective ((hA _).trans (map_zero _).symm))
      ((H'AddEquiv B F (q + 1)).injective ((hB _).trans (map_zero _).symm))
  obtain ⟨y, rfl⟩ := (exact_δ_toProd A B F q x).1 h0
  have hy : y = 0 := (H'AddEquiv (A ⊓ B) F q).injective (by rw [map_zero]; exact hAB _)
  rw [hy, map_zero]


-- @@ L62-82 verbatim
/-- **Mayer–Vietoris in degree one**: `H¹(A ∪ B, F) = 0` if `H¹(A, F) = H¹(B, F) = 0` and every
section of `F` over `A ∩ B` is a difference of sections over `A` and over `B`. -/
lemma H_one_sup_eq_zero (hW : A ⊔ B = W)
    (hsplit : ∀ s : F.obj.obj (op (A ⊓ B)), ∃ (a : F.obj.obj (op A)) (b : F.obj.obj (op B)),
      F.obj.map (homOfLE inf_le_left).op a - F.obj.map (homOfLE inf_le_right).op b = s)
    (hA : ∀ x : H ((restrictOpen A).obj F) 1, x = 0)
    (hB : ∀ x : H ((restrictOpen B).obj F) 1, x = 0)
    (x : H ((restrictOpen W).obj F) 1) : x = 0 := by
  subst hW
  obtain ⟨x, rfl⟩ := (H'AddEquiv (A ⊔ B) F 1).surjective x
  suffices hx : x = 0 by rw [hx, map_zero]
  have h0 : toProd A B F 1 x = 0 :=
    Prod.ext ((H'AddEquiv A F 1).injective ((hA _).trans (map_zero _).symm))
      ((H'AddEquiv B F 1).injective ((hB _).trans (map_zero _).symm))
  obtain ⟨y, rfl⟩ := (exact_δ_toProd A B F 0 x).1 h0
  obtain ⟨a, b, hab⟩ := hsplit (zeroAddEquiv F (A ⊓ B) y)
  have hy : y = (zeroAddEquiv F (A ⊓ B)).symm
      (F.obj.map (homOfLE inf_le_left).op a - F.obj.map (homOfLE inf_le_right).op b) := by
    rw [hab, AddEquiv.symm_apply_apply]
  rw [hy]
  exact δ_zeroAddEquiv_symm_sub a b


-- @@ L84-99 verbatim
/-- **Mayer–Vietoris, vanishing on the intersection**: `Hᵠ(A ∩ B, F) = 0` if
`Hᵠ(A, F) = Hᵠ(B, F) = 0` and `Hᵠ⁺¹(A ∪ B, F) = 0`. -/
lemma H_inf_eq_zero (hW : A ⊓ B = W) (hW' : A ⊔ B = W') {q : ℕ}
    (hA : ∀ x : H ((restrictOpen A).obj F) q, x = 0)
    (hB : ∀ x : H ((restrictOpen B).obj F) q, x = 0)
    (hAB : ∀ x : H ((restrictOpen W').obj F) (q + 1), x = 0)
    (x : H ((restrictOpen W).obj F) q) : x = 0 := by
  subst hW hW'
  obtain ⟨x, rfl⟩ := (H'AddEquiv (A ⊓ B) F q).surjective x
  suffices hx : x = 0 by rw [hx, map_zero]
  have hδ : δ A B F q x = 0 :=
    (H'AddEquiv (A ⊔ B) F (q + 1)).injective (by rw [map_zero]; exact hAB _)
  obtain ⟨p, rfl⟩ := (exact_fromProd_δ A B F q x).1 hδ
  have h1 : p.1 = 0 := (H'AddEquiv A F q).injective (by rw [map_zero]; exact hA _)
  have h2 : p.2 = 0 := (H'AddEquiv B F q).injective (by rw [map_zero]; exact hB _)
  rw [fromProd_apply, h1, h2, map_zero, map_zero, sub_zero]


-- @@ L101-101 verbatim
end TopCat.Sheaf


-- @@ L103-103 verbatim
noncomputable section


-- @@ L105-105 verbatim
namespace ComplexAnalytic.relProjectiveLine


-- @@ L107-107 verbatim
open relProjectiveSpaceAn


-- @@ L109-109 verbatim
variable {m : ℕ}


-- @@ L111-111 verbatim
/-! ### Chart coordinates -/


-- @@ L113-115 verbatim
/-- The point of `ℂ^{1+m}` with base coordinates `p.1` and fibre coordinate `p.2`. -/
def cpt (p : (Fin m → ℂ) × ℂ) : AnalyticSpace.complexAffineSpace.{u} (1 + m) :=
  joinPt ![p.2] p.1


-- @@ L117-119 verbatim
@[simp]
lemma yPart_cpt (p : (Fin m → ℂ) × ℂ) : yPart.{u} (N := 1) (cpt.{u} p) = p.1 :=
  yPart_joinPt _ _


-- @@ L121-123 verbatim
@[simp]
lemma zPart_cpt (p : (Fin m → ℂ) × ℂ) : zPart.{u} (m := m) (cpt.{u} p) = ![p.2] :=
  zPart_joinPt _ _


-- @@ L125-131 verbatim
lemma cpt_yPart_zPart (w : AnalyticSpace.complexAffineSpace.{u} (1 + m)) :
    cpt.{u} (yPart w, zPart w 0) = w := by
  rw [← joinPt_zPart_yPart w, cpt, yPart_joinPt, zPart_joinPt]
  congr 1
  funext k
  fin_cases k
  rfl


-- @@ L133-138 verbatim
lemma cpt_injective : Function.Injective (cpt.{u} (m := m)) := by
  intro p q h
  have h1 := congrArg yPart h
  have h2 := congrFun (congrArg zPart h) 0
  simp only [yPart_cpt, zPart_cpt, Matrix.cons_val_zero] at h1 h2
  exact Prod.ext h1 h2


-- @@ L140-147 verbatim
lemma continuous_cpt : Continuous (cpt.{u} (m := m)) := by
  refine continuous_pi fun k ↦ ?_
  change Continuous fun p : (Fin m → ℂ) × ℂ ↦ Fin.append ![p.2] p.1 k.down
  induction k.down using Fin.addCases with
  | left l => simpa [Fin.append_left, Subsingleton.elim l 0] using continuous_snd
  | right j =>
    simp only [Fin.append_right]
    exact (continuous_apply j).comp continuous_fst


-- @@ L149-151 verbatim
lemma continuous_zPart_zero :
    Continuous fun w : AnalyticSpace.complexAffineSpace.{u} (1 + m) ↦ zPart w 0 :=
  continuous_apply _


-- @@ L153-156 verbatim
/-- The point with base coordinates `p.1` and fibre coordinate `p.2` in the chart `i` of
`P^an = ℂᵐ × ℙ¹`. -/
def chartPt (i : Fin 2) (p : (Fin m → ℂ) × ℂ) : relProjectiveSpaceAn.{u} m 1 :=
  (chartLRS.{u} i).base (cpt p)


-- @@ L158-168 verbatim
lemma isOpenEmbedding_chartPt (i : Fin 2) : Topology.IsOpenEmbedding (chartPt.{u} (m := m) i) := by
  have hc : Topology.IsOpenEmbedding (cpt.{u} (m := m)) := by
    let e : (Fin m → ℂ) × ℂ ≃ₜ (ULift.{u} (Fin (1 + m)) → ℂ) :=
      { toFun := cpt
        invFun := fun w ↦ (yPart w, zPart w 0)
        left_inv := fun p ↦ by simp
        right_inv := fun w ↦ cpt_yPart_zPart w
        continuous_toFun := continuous_cpt
        continuous_invFun := continuous_yPart.prodMk continuous_zPart_zero }
    exact e.isOpenEmbedding
  exact (isOpenEmbedding_chart i).comp hc


-- @@ L170-171 verbatim
lemma chartPt_injective (i : Fin 2) : Function.Injective (chartPt.{u} (m := m) i) :=
  (isOpenEmbedding_chartPt i).injective


-- @@ L173-175 verbatim
lemma homogCoord_zero_cpt (p : (Fin m → ℂ) × ℂ) : homogCoord 0 (cpt.{u} p) = ![1, p.2] := by
  funext k
  fin_cases k <;> simp [homogCoord]


-- @@ L177-181 verbatim
lemma homogCoord_one_cpt (p : (Fin m → ℂ) × ℂ) : homogCoord 1 (cpt.{u} p) = ![p.2, 1] := by
  funext k
  fin_cases k
  · rfl
  · simp [homogCoord]


-- @@ L183-186 verbatim
lemma chartPt_zero_eq (p : (Fin m → ℂ) × ℂ) :
    chartPt.{u} 0 p = pointOfVec.{u} ![1, p.2] (Function.ne_iff.2 ⟨0, by simp⟩) p.1 := by
  rw [chartPt, chart_eq_pointOfVec]
  simp_rw [homogCoord_zero_cpt, yPart_cpt]


-- @@ L188-191 verbatim
lemma chartPt_one_eq (p : (Fin m → ℂ) × ℂ) :
    chartPt.{u} 1 p = pointOfVec.{u} ![p.2, 1] (Function.ne_iff.2 ⟨1, by simp⟩) p.1 := by
  rw [chartPt, chart_eq_pointOfVec]
  simp_rw [homogCoord_one_cpt, yPart_cpt]


-- @@ L193-200 verbatim
/-- A point with `v₀ ≠ 0` is the point of the chart `0` with fibre coordinate `v₁ / v₀`. -/
lemma pointOfVec_eq_chartPt_zero (v : Fin 2 → ℂ) (hv : v ≠ 0) (y : Fin m → ℂ) (h : v 0 ≠ 0) :
    pointOfVec.{u} v hv y = chartPt.{u} 0 (y, v 1 / v 0) := by
  rw [pointOfVec_eq _ _ _ 0 h, chartPt, cpt]
  congr 2
  funext k
  fin_cases k
  rfl


-- @@ L202-209 verbatim
/-- A point with `v₁ ≠ 0` is the point of the chart `1` with fibre coordinate `v₀ / v₁`. -/
lemma pointOfVec_eq_chartPt_one (v : Fin 2 → ℂ) (hv : v ≠ 0) (y : Fin m → ℂ) (h : v 1 ≠ 0) :
    pointOfVec.{u} v hv y = chartPt.{u} 1 (y, v 0 / v 1) := by
  rw [pointOfVec_eq _ _ _ 1 h, chartPt, cpt]
  congr 2
  funext k
  fin_cases k
  rfl


-- @@ L211-215 verbatim
/-- **The chart transition**: `chartPt 0 (y, z) = chartPt 1 (y, z⁻¹)` for `z ≠ 0`. -/
lemma chartPt_zero_eq_chartPt_one {p : (Fin m → ℂ) × ℂ} (hp : p.2 ≠ 0) :
    chartPt.{u} 0 p = chartPt.{u} 1 (p.1, p.2⁻¹) := by
  rw [chartPt_zero_eq, pointOfVec_eq_chartPt_one _ _ _ (by simpa using hp)]
  simp


-- @@ L217-219 verbatim
@[simp]
lemma baseY_chartPt (i : Fin 2) (p : (Fin m → ℂ) × ℂ) : baseY.{u} (chartPt.{u} i p) = p.1 := by
  rw [chartPt, baseY_chart, yPart_cpt]


-- @@ L221-224 verbatim
lemma chartPt_zero_mem_range_chart_one_iff (p : (Fin m → ℂ) × ℂ) :
    chartPt.{u} 0 p ∈ Set.range (chartLRS.{u} (m := m) 1).base ↔ p.2 ≠ 0 := by
  rw [chartPt_zero_eq, mem_range_chart_pointOfVec_iff]
  simp


-- @@ L226-233 verbatim
/-- Every point of `P^an` lies in the chart `0` or in the chart `1`. -/
lemma exists_chartPt (x : relProjectiveSpaceAn.{u} m 1) :
    (∃ p, chartPt.{u} 0 p = x) ∨ ∃ p, chartPt.{u} 1 p = x := by
  obtain ⟨v, hv, y, rfl⟩ := pointOfVec_surjective x
  by_cases h : v 0 = 0
  · have h1 : v 1 ≠ 0 := fun h1 ↦ hv (funext fun k ↦ by fin_cases k <;> simp [h, h1])
    exact Or.inr ⟨_, (pointOfVec_eq_chartPt_one v hv y h1).symm⟩
  · exact Or.inl ⟨_, (pointOfVec_eq_chartPt_zero v hv y h).symm⟩


-- @@ L235-235 verbatim
/-! ### Chart boxes -/


-- @@ L237-239 verbatim
/-- The image in the chart `i` of an open `S ⊆ ℂᵐ × ℂ` (base and fibre coordinates). -/
def chartBox (i : Fin 2) (S : Opens ((Fin m → ℂ) × ℂ)) : (relProjectiveSpaceAn.{u} m 1).Opens :=
  ⟨chartPt.{u} i '' S, (isOpenEmbedding_chartPt i).isOpenMap _ S.isOpen⟩


-- @@ L241-243 verbatim
lemma mem_chartBox_iff {i : Fin 2} {S : Opens ((Fin m → ℂ) × ℂ)}
    {x : relProjectiveSpaceAn.{u} m 1} : x ∈ chartBox.{u} i S ↔ ∃ p ∈ S, chartPt.{u} i p = x :=
  Iff.rfl


-- @@ L245-247 verbatim
lemma chartPt_mem_chartBox_iff {i : Fin 2} {S : Opens ((Fin m → ℂ) × ℂ)}
    {p : (Fin m → ℂ) × ℂ} : chartPt.{u} i p ∈ chartBox.{u} i S ↔ p ∈ S :=
  (chartPt_injective i).mem_set_image


-- @@ L249-251 verbatim
lemma chartBox_mono {i : Fin 2} {S S' : Opens ((Fin m → ℂ) × ℂ)} (h : S ≤ S') :
    chartBox.{u} i S ≤ chartBox.{u} i S' :=
  Set.image_mono h


-- @@ L253-255 verbatim
/-- The open `B × O ⊆ ℂᵐ × ℂ`. -/
def prodOpens (B : Opens (Fin m → ℂ)) (O : Opens ℂ) : Opens ((Fin m → ℂ) × ℂ) :=
  ⟨(B : Set (Fin m → ℂ)) ×ˢ (O : Set ℂ), B.isOpen.prod O.isOpen⟩


-- @@ L257-260 verbatim
@[simp]
lemma mem_prodOpens {B : Opens (Fin m → ℂ)} {O : Opens ℂ} {p : (Fin m → ℂ) × ℂ} :
    p ∈ prodOpens B O ↔ p.1 ∈ B ∧ p.2 ∈ O :=
  Iff.rfl


-- @@ L262-267 verbatim
lemma chartBox_prodOpens_le_tube (i : Fin 2) (B : Opens (Fin m → ℂ)) (O : Opens ℂ) :
    chartBox.{u} i (prodOpens B O) ≤ tube.{u} (N := 1) B := by
  rintro _ ⟨p, hp, rfl⟩
  change chartPt i p ∈ tube B
  rw [mem_tube, baseY_chartPt]
  exact hp.1


-- @@ L269-272 verbatim
lemma chartBox_le_chartOpens (i : Fin 2) (S : Opens ((Fin m → ℂ) × ℂ)) :
    chartBox.{u} i S ≤ chartOpens.{u} i := by
  rintro _ ⟨p, -, rfl⟩
  exact ⟨cpt p, rfl⟩


-- @@ L274-283 verbatim
/-- The open `{(y, z) | z ≠ 0, (y, z) ∈ S₀, (y, z⁻¹) ∈ S₁}`: the intersection of `chartBox 0 S₀`
and `chartBox 1 S₁` in the coordinates of the chart `0`. -/
def overlapOpens (S₀ S₁ : Opens ((Fin m → ℂ) × ℂ)) : Opens ((Fin m → ℂ) × ℂ) :=
  ⟨{p | p.2 ≠ 0 ∧ p ∈ S₀ ∧ (p.1, p.2⁻¹) ∈ S₁}, by
    have h : IsOpen {p : (Fin m → ℂ) × ℂ | p.2 ≠ 0} := isOpen_ne_fun continuous_snd continuous_const
    refine isOpen_iff_mem_nhds.2 fun p hp ↦ ?_
    have hc : ContinuousAt (fun p : (Fin m → ℂ) × ℂ ↦ (p.1, p.2⁻¹)) p :=
      continuousAt_fst.prodMk (continuous_snd.continuousAt.inv₀ hp.1)
    exact Filter.inter_mem (h.mem_nhds hp.1) (Filter.inter_mem (S₀.isOpen.mem_nhds hp.2.1)
      (hc.preimage_mem_nhds (S₁.isOpen.mem_nhds hp.2.2)))⟩


-- @@ L285-288 verbatim
@[simp]
lemma mem_overlapOpens {S₀ S₁ : Opens ((Fin m → ℂ) × ℂ)} {p : (Fin m → ℂ) × ℂ} :
    p ∈ overlapOpens S₀ S₁ ↔ p.2 ≠ 0 ∧ p ∈ S₀ ∧ (p.1, p.2⁻¹) ∈ S₁ :=
  Iff.rfl


-- @@ L290-303 verbatim
/-- **The intersection of two chart boxes**, in the coordinates of the chart `0`. -/
lemma chartBox_inf (S₀ S₁ : Opens ((Fin m → ℂ) × ℂ)) :
    chartBox.{u} 0 S₀ ⊓ chartBox.{u} 1 S₁ = chartBox.{u} 0 (overlapOpens S₀ S₁) := by
  ext x
  simp only [Opens.coe_inf, Set.mem_inter_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨⟨p, hp, rfl⟩, ⟨q, hq, hpq⟩⟩
    have h2 : p.2 ≠ 0 := by
      exact (chartPt_zero_mem_range_chart_one_iff p).1 (hpq ▸ ⟨cpt q, rfl⟩)
    rw [chartPt_zero_eq_chartPt_one h2] at hpq
    rw [chartPt_injective 1 hpq] at hq
    exact ⟨p, ⟨h2, hp, hq⟩, rfl⟩
  · rintro ⟨p, ⟨h2, hp, hq⟩, rfl⟩
    exact ⟨⟨p, hp, rfl⟩, ⟨_, hq, (chartPt_zero_eq_chartPt_one h2).symm⟩⟩


-- @@ L305-327 verbatim
/-- **Two chart boxes cover `B × ℙ¹`** if the fibre opens cover `ℙ¹`. -/
lemma chartBox_sup (B : Opens (Fin m → ℂ)) (O₀ O₁ : Opens ℂ) (h₀ : (0 : ℂ) ∈ O₀)
    (h₁ : (0 : ℂ) ∈ O₁) (h : ∀ z : ℂ, z ≠ 0 → z ∈ O₀ ∨ z⁻¹ ∈ O₁) :
    chartBox.{u} 0 (prodOpens B O₀) ⊔ chartBox.{u} 1 (prodOpens B O₁) = tube.{u} (N := 1) B := by
  refine le_antisymm (sup_le (chartBox_prodOpens_le_tube 0 B O₀)
    (chartBox_prodOpens_le_tube 1 B O₁)) fun x hx ↦ ?_
  rw [mem_tube] at hx
  rw [Opens.mem_sup]
  obtain ⟨p, rfl⟩ | ⟨p, rfl⟩ := exists_chartPt x
  · rw [baseY_chartPt] at hx
    by_cases hp : p.2 = 0
    · exact Or.inl ⟨p, ⟨hx, hp ▸ h₀⟩, rfl⟩
    · rcases h p.2 hp with h' | h'
      · exact Or.inl ⟨p, ⟨hx, h'⟩, rfl⟩
      · exact Or.inr ⟨(p.1, p.2⁻¹), ⟨hx, h'⟩, (chartPt_zero_eq_chartPt_one hp).symm⟩
  · rw [baseY_chartPt] at hx
    by_cases hp : p.2 = 0
    · exact Or.inr ⟨p, ⟨hx, hp ▸ h₁⟩, rfl⟩
    · rcases h p.2⁻¹ (inv_ne_zero hp) with h' | h'
      · refine Or.inl ⟨(p.1, p.2⁻¹), ⟨hx, h'⟩, ?_⟩
        rw [chartPt_zero_eq_chartPt_one (inv_ne_zero hp), inv_inv]
      · rw [inv_inv] at h'
        exact Or.inr ⟨p, ⟨hx, h'⟩, rfl⟩


-- @@ L329-329 verbatim
/-! ### Theorem B for the structure sheaf -/


-- @@ L331-333 verbatim
/-- The open rectangle `(c.re, d.re) × (c.im, d.im) ⊆ ℂ`. -/
def rectOpens (c d : ℂ) : Opens ℂ :=
  ⟨Set.Ioo c.re d.re ×ℂ Set.Ioo c.im d.im, isOpen_Ioo.reProdIm isOpen_Ioo⟩


-- @@ L335-338 verbatim
@[simp]
lemma mem_rectOpens {c d z : ℂ} :
    z ∈ rectOpens c d ↔ z ∈ Set.Ioo c.re d.re ×ℂ Set.Ioo c.im d.im :=
  Iff.rfl


-- @@ L340-345 verbatim
/-- The chart preimage `{w | (yPart w, zPart w 0) ∈ S}` of `chartBox i S`, an open of
`ℂ^{1+m}`. -/
def chartPreimg (S : Opens ((Fin m → ℂ) × ℂ)) :
    Opens (AnalyticSpace.complexAffineSpace.{u} (1 + m)).toPresheafedSpace :=
  ⟨{w | (yPart w, zPart w 0) ∈ S},
    S.isOpen.preimage (continuous_yPart.prodMk continuous_zPart_zero)⟩


-- @@ L347-355 verbatim
lemma image_chartPreimg (i : Fin 2) (S : Opens ((Fin m → ℂ) × ℂ)) :
    (chartLRS.{u} (m := m) i).base '' (chartPreimg.{u} S : Set _) =
      (chartBox.{u} i S : Set (relProjectiveSpaceAn.{u} m 1)) := by
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨_, hw, by rw [chartPt, cpt_yPart_zPart]⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨cpt p, by simpa [chartPreimg] using hp, rfl⟩


-- @@ L357-374 verbatim
lemma coe_chartPreimg_prodOpens (a b : Fin m → ℂ) (c d : ℂ) :
    ((chartPreimg.{u} (prodOpens (boxOpens a b) (rectOpens c d)) :
        Set (AnalyticSpace.complexAffineSpace.{u} (1 + m))) :
        Set (ULift.{u} (Fin (1 + m)) → ℂ)) =
      Complex.openBox (fun k ↦ Fin.append ![c] a k.down) (fun k ↦ Fin.append ![d] b k.down) := by
  ext w
  change (yPart w ∈ Complex.openBox a b ∧ zPart w 0 ∈ _) ↔ _
  simp only [Complex.openBox, Set.mem_pi, Set.mem_univ, true_implies]
  constructor
  · rintro ⟨hy, hz⟩ ⟨k⟩
    induction k using Fin.addCases with
    | left l =>
      rw [Subsingleton.elim l 0]
      simpa [zPart] using hz
    | right j => simpa [yPart] using hy j
  · intro h
    exact ⟨fun j ↦ by simpa [yPart] using h ⟨Fin.natAdd 1 j⟩,
      by simpa [zPart] using h ⟨Fin.castAdd m 0⟩⟩


-- @@ L376-385 verbatim
/-- **Theorem B on chart boxes**: `Hᵠ(chartBox i (B × Q), 𝒪) = 0` for `q ≥ 1`, `B` an open box
in `ℂᵐ` and `Q` an open rectangle in `ℂ`. -/
theorem subsingleton_H_chartBox (i : Fin 2) (a b : Fin m → ℂ) (c d : ℂ) {q : ℕ} (hq : 0 < q) :
    Subsingleton (TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen
      (chartBox.{u} i (prodOpens (boxOpens a b) (rectOpens c d)))).obj
        (relProjectiveSpaceAn.{u} m 1).toLocallyRingedSpace.structureSheafAb) q) :=
  LocallyRingedSpace.subsingleton_H_structureSheafAb_of_image_eq (chartLRS.{u} i) _
    (image_chartPreimg i _) q
    (Complex.TheoremB.subsingleton_H_restrictOpen_structureSheafAb_openBox _ _
      (coe_chartPreimg_prodOpens a b c d) hq)


-- @@ L387-392 verbatim
lemma mem_range_chart_zero_or_one (x : relProjectiveSpaceAn.{u} m 1) :
    x ∈ Set.range (chartLRS.{u} (m := m) 0).base ∨
      x ∈ Set.range (chartLRS.{u} (m := m) 1).base := by
  obtain ⟨p, rfl⟩ | ⟨p, rfl⟩ := exists_chartPt x
  · exact Or.inl ⟨cpt p, rfl⟩
  · exact Or.inr ⟨cpt p, rfl⟩


-- @@ L394-422 verbatim
/-- **`Hᵠ(B × ℙ¹, 𝒪) = 0` for `q ≥ 2`** and `B` an open box, by Mayer–Vietoris for the cover by
`B × ℂ` and `B × ℂ` with intersection `B × ℂ^×`. -/
theorem H_tube_structureSheafAb_eq_zero (a b : Fin m → ℂ) {B : Opens (Fin m → ℂ)}
    (hB : (B : Set (Fin m → ℂ)) = Complex.openBox a b) (q : ℕ)
    (x : TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen (tube.{u} (N := 1) B)).obj
      (relProjectiveSpaceAn.{u} m 1).toLocallyRingedSpace.structureSheafAb) (q + 2)) : x = 0 := by
  refine TopCat.Sheaf.H_sup_eq_zero _ (A := tube B ⊓ opensUI {0}) (B := tube B ⊓ opensUI {1})
    (W' := tube B ⊓ opensUI {0, 1}) ?_ ?_ (q := q + 1) (fun y ↦ ?_) (fun y ↦ ?_) (fun y ↦ ?_) x
  · ext x
    simp only [Opens.coe_sup, Opens.coe_inf, Set.mem_union, Set.mem_inter_iff, SetLike.mem_coe,
      mem_opensUI_iff, Finset.mem_singleton, forall_eq]
    rcases mem_range_chart_zero_or_one x with h | h <;> tauto
  · ext x
    simp only [Opens.coe_inf, Set.mem_inter_iff, SetLike.mem_coe, mem_opensUI_iff,
      Finset.mem_singleton, forall_eq, Finset.mem_insert]
    constructor
    · rintro ⟨⟨h1, h2⟩, -, h3⟩
      exact ⟨h1, fun j hj ↦ by rcases hj with rfl | rfl <;> assumption⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, h2 0 (Or.inl rfl)⟩, h1, h2 1 (Or.inr rfl)⟩
  · haveI := subsingleton_H_tube_inf_opensUI (N := 1) a b hB (I := {0, 1}) ⟨0, by simp⟩ (q + 1)
      (by omega)
    exact Subsingleton.elim _ _
  · haveI := subsingleton_H_tube_inf_opensUI (N := 1) a b hB (I := {0}) ⟨0, by simp⟩ (q + 2)
      (by omega)
    exact Subsingleton.elim _ _
  · haveI := subsingleton_H_tube_inf_opensUI (N := 1) a b hB (I := {1}) ⟨1, by simp⟩ (q + 2)
      (by omega)
    exact Subsingleton.elim _ _


-- @@ L424-447 verbatim
/-- **Theorem B on the intersection of two chart boxes covering `B × ℙ¹`**: if the rectangles
`Q₀`, `Q₁` contain `0` and every `z ≠ 0` satisfies `z ∈ Q₀` or `z⁻¹ ∈ Q₁`, then
`Hᵠ(chartBox 0 (B × Q₀) ∩ chartBox 1 (B × Q₁), 𝒪) = 0` for `q ≥ 1`. -/
theorem subsingleton_H_chartBox_inf (a b : Fin m → ℂ) (c₀ d₀ c₁ d₁ : ℂ)
    (h₀ : (0 : ℂ) ∈ rectOpens c₀ d₀) (h₁ : (0 : ℂ) ∈ rectOpens c₁ d₁)
    (h : ∀ z : ℂ, z ≠ 0 → z ∈ rectOpens c₀ d₀ ∨ z⁻¹ ∈ rectOpens c₁ d₁) {q : ℕ} (hq : 0 < q) :
    Subsingleton (TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen
      (chartBox.{u} 0 (prodOpens (boxOpens a b) (rectOpens c₀ d₀)) ⊓
        chartBox.{u} 1 (prodOpens (boxOpens a b) (rectOpens c₁ d₁)))).obj
          (relProjectiveSpaceAn.{u} m 1).toLocallyRingedSpace.structureSheafAb) q) := by
  obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  refine ⟨fun x y ↦ ?_⟩
  suffices H : ∀ z : TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen
      (chartBox.{u} 0 (prodOpens (boxOpens a b) (rectOpens c₀ d₀)) ⊓
        chartBox.{u} 1 (prodOpens (boxOpens a b) (rectOpens c₁ d₁)))).obj
          (relProjectiveSpaceAn.{u} m 1).toLocallyRingedSpace.structureSheafAb) (q + 1),
      z = 0 by rw [H x, H y]
  refine TopCat.Sheaf.H_inf_eq_zero _ rfl (chartBox_sup _ _ _ h₀ h₁ h) (fun z ↦ ?_)
    (fun z ↦ ?_) (fun z ↦ ?_)
  · haveI := subsingleton_H_chartBox.{u} 0 a b c₀ d₀ (q := q + 1) (by omega)
    exact Subsingleton.elim _ _
  · haveI := subsingleton_H_chartBox.{u} 1 a b c₁ d₁ (q := q + 1) (by omega)
    exact Subsingleton.elim _ _
  · exact H_tube_structureSheafAb_eq_zero a b (coe_boxOpens a b) q z


-- @@ L449-451 verbatim
/-- The open square `(-S, S)²` in `ℂ`. -/
def squareOpens (S : ℝ) : Opens ℂ :=
  rectOpens ⟨-S, -S⟩ ⟨S, S⟩


-- @@ L453-454 verbatim
lemma mem_squareOpens_iff {S : ℝ} {z : ℂ} : z ∈ squareOpens S ↔ |z.re| < S ∧ |z.im| < S := by
  simp only [squareOpens, mem_rectOpens, Complex.mem_reProdIm, Set.mem_Ioo, abs_lt]


-- @@ L456-458 verbatim
lemma zero_mem_squareOpens {S : ℝ} (hS : 0 < S) : (0 : ℂ) ∈ squareOpens S := by
  rw [mem_squareOpens_iff]
  simpa using hS


-- @@ L460-464 verbatim
lemma ball_subset_squareOpens (S : ℝ) : Metric.ball (0 : ℂ) S ⊆ (squareOpens S : Set ℂ) := by
  intro z hz
  rw [Metric.mem_ball, dist_zero_right] at hz
  exact mem_squareOpens_iff.2 ⟨(Complex.abs_re_le_norm z).trans_lt hz,
    (Complex.abs_im_le_norm z).trans_lt hz⟩


-- @@ L466-475 verbatim
lemma squareOpens_or_inv {S : ℝ} (hS : 1 < S) (z : ℂ) (hz : z ≠ 0) :
    z ∈ squareOpens S ∨ z⁻¹ ∈ squareOpens S := by
  by_cases h : ‖z‖ < S
  · exact Or.inl (ball_subset_squareOpens S (by simpa using h))
  · refine Or.inr (ball_subset_squareOpens S ?_)
    rw [Metric.mem_ball, dist_zero_right, norm_inv]
    push Not at h
    have h0 : 0 < ‖z‖ := norm_pos_iff.2 hz
    calc ‖z‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (hS.le.trans h)
      _ < S := hS


-- @@ L477-482 verbatim
/-- **The chart boxes over `B × (-S, S)²` in both charts cover `B × ℙ¹`**, for `S > 1`. -/
lemma chartBox_square_sup (B : Opens (Fin m → ℂ)) {S : ℝ} (hS : 1 < S) :
    chartBox.{u} 0 (prodOpens B (squareOpens S)) ⊔ chartBox.{u} 1 (prodOpens B (squareOpens S)) =
      tube.{u} (N := 1) B :=
  chartBox_sup B _ _ (zero_mem_squareOpens (by linarith)) (zero_mem_squareOpens (by linarith))
    (squareOpens_or_inv hS)


-- @@ L484-492 verbatim
/-- **Theorem B on the intersection of the chart boxes over `B × (-S, S)²`**, `S > 1`. -/
theorem subsingleton_H_chartBox_square_inf (a b : Fin m → ℂ) {S : ℝ} (hS : 1 < S) {q : ℕ}
    (hq : 0 < q) :
    Subsingleton (TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen
      (chartBox.{u} 0 (prodOpens (boxOpens a b) (squareOpens S)) ⊓
        chartBox.{u} 1 (prodOpens (boxOpens a b) (squareOpens S)))).obj
          (relProjectiveSpaceAn.{u} m 1).toLocallyRingedSpace.structureSheafAb) q) :=
  subsingleton_H_chartBox_inf a b _ _ _ _ (zero_mem_squareOpens (by linarith))
    (zero_mem_squareOpens (by linarith)) (squareOpens_or_inv hS) hq


-- @@ L494-494 verbatim
end ComplexAnalytic.relProjectiveLine


-- @@ L496-496 verbatim
end
