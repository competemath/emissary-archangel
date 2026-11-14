import TDA.Reeb.GeometricThickeningAddition
import TDA.Reeb.RGraphSmoothing


-- @@ L4-55 verbatim
/-!
# The Reeb quotient of the thickening addition map

The addition map `μ_(ε,δ) : T_ε T_δ X → T_(ε+δ) X`, `((x, s), t) ↦ (x, s + t)`, is not a
homeomorphism, and on the one-point space no slice isomorphism `T_1 T_1 P ≅ T_2 P` exists. After the
Reeb quotient it becomes one, with no hypothesis on `X` or on the height function:

```
ℛ μ_(ε,δ) : ReebQuotient (height (height f δ) ε) ≃ₜ ReebQuotient (height f (ε + δ)).
```

## The section and the fibre paths

`addSection X ε δ : T_(ε+δ) X → T_ε T_δ X` sends `(x, u)` to `((x, c), u - c)` with `c` the
projection of `u` onto `[-δ, δ]`. It is continuous, height-preserving (`height_addSection`) and
natural (`addSection_natural`), and it is a section of the addition map
(`addMap_comp_addSection`). For every `z = ((x, s), t)`, the straight segment from `(s, t)` to
`(c, s + t - c)` keeps `x` and `s + t` and stays in `Band δ × Band ε`, by convexity of the bands
(`addFiberPath`). It lies in one height fibre (`height_addFiberPath`), so `z` and `σ (μ z)` are
Reeb-equivalent (`reebRel_addSection_addMap`).

## The homeomorphism

`quotientAddHomeomorph f ε δ` has forward map `ℛ μ` and inverse `ℛ σ`. The identity `μ ∘ σ = id`
gives one composite, the fibre paths give the other, and continuity of both directions is the
functoriality of `ℛ` on the continuous maps `μ` and `σ`. No compactness, Hausdorff or
constructibility argument is used, and the carrier universe is arbitrary. In particular two points
of `T_ε T_δ X` have the same class after `ℛ μ` exactly when they are Reeb-equivalent
(`mk_addMap_eq_mk_addMap_iff`).

## The real slice and coherence

`reebAddIso ε δ : (T_δ ⋙ T_ε) ⋙ ℛ ≅ T_(ε+δ) ⋙ ℛ` has hom `whiskerRight (addNatTrans ε δ) ℛ`
(`reebAddIso_hom`) and inverse `ℛ σ` (`reebAddIso_inv_app_left_hom`). Parameter equalities are
bridged by `bandEqIso`, a pair of band inclusions. The merged lax laws of `addNatTrans` pass
through `ℛ`: associativity (`reebAddIso_assoc`, and in iso form `reebAddIso_assoc_iso`), both unit
laws against `zeroIso` (`reebAddIso_zero_left`, `reebAddIso_zero_right`), both zero-section laws and
band enlargement. As a consequence `ℛ (T_ε μ_(δ,γ))` is an isomorphism
(`isIso_whiskerRight_whiskerRight_addNatTrans`).

## Graph objects

The Reeb quotient of `T_ε T_δ A` is a graph object for every graph object `A`
(`RGraph.isRGraph_quotient_thickening_thickening`), through the isomorphism with the Reeb quotient
of `T_(ε+δ) A`; the double thickening itself is not claimed to be constructible. The functor
`RGraph.doubleThickeningQuotient ε δ : A ↦ ℛ T_ε T_δ A` on graph objects is naturally isomorphic to
the merged `geometricSmoothing (ε + δ)` (`RGraph.geometricSmoothingAddIso`).

The slice and graph packaging is in universe `0`.

See `docs/math/reeb-quotient-thickening-addition.md`.
-/


-- @@ L57-57 verbatim
open Set Topology CategoryTheory

-- @@ L58-58 verbatim
open scoped NNReal


-- @@ L60-60 verbatim
universe u v


-- @@ L62-62 verbatim
namespace TDA.Reeb


-- @@ L64-64 verbatim
namespace GeometricThickening


-- @@ L66-66 verbatim
noncomputable section


-- @@ L68-68 verbatim
/-! ### The section of the addition map -/


-- @@ L70-70 verbatim
section AddSection


-- @@ L72-72 verbatim
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]


-- @@ L74-90 verbatim
/-- For `u ∈ [-(ε + δ), ε + δ]` and `c` its projection onto `[-δ, δ]`, `u - c ∈ [-ε, ε]`. -/
theorem sub_projIcc_mem_band {ε δ : ℝ≥0} (u : Band (ε + δ)) :
    (u : ℝ) - projIcc (-(δ : ℝ)) δ (neg_le_band δ) u ∈ Band ε := by
  have hs : (projIcc (-(δ : ℝ)) δ (neg_le_band δ) u : ℝ) =
      max (-(δ : ℝ)) (min (δ : ℝ) u) := coe_projIcc _ _ _ _
  have h₁ : -((ε : ℝ) + δ) ≤ u := by have := u.2.1; rwa [NNReal.coe_add] at this
  have h₂ : (u : ℝ) ≤ ε + δ := by have := u.2.2; rwa [NNReal.coe_add] at this
  have hε := ε.coe_nonneg
  have hδ := δ.coe_nonneg
  rw [hs]
  have hm1 : min (δ : ℝ) u ≤ δ := min_le_left _ _
  have hm2 : min (δ : ℝ) u ≤ u := min_le_right _ _
  have hv1 : -(δ : ℝ) ≤ max (-(δ : ℝ)) (min (δ : ℝ) u) := le_max_left _ _
  have hv2 : min (δ : ℝ) u ≤ max (-(δ : ℝ)) (min (δ : ℝ) u) := le_max_right _ _
  rcases min_choice (δ : ℝ) u with hm | hm <;>
    rcases max_choice (-(δ : ℝ)) (min (δ : ℝ) u) with hv | hv <;>
    exact ⟨by linarith, by linarith⟩


-- @@ L92-104 verbatim
/-- The section `σ_(ε,δ) : T_(ε+δ) X → T_ε T_δ X`, `(x, u) ↦ ((x, c), u - c)` with `c` the
projection of `u` onto `[-δ, δ]`. -/
def addSection (X : Type u) [TopologicalSpace X] (ε δ : ℝ≥0) :
    C(X × Band (ε + δ), (X × Band δ) × Band ε) where
  toFun w := ((w.1, projIcc (-(δ : ℝ)) δ (neg_le_band δ) w.2),
    ⟨w.2 - projIcc (-(δ : ℝ)) δ (neg_le_band δ) w.2, sub_projIcc_mem_band w.2⟩)
  continuous_toFun := by
    have hc : Continuous fun w : X × Band (ε + δ) =>
        projIcc (-(δ : ℝ)) δ (neg_le_band δ) (w.2 : ℝ) :=
      continuous_projIcc.comp (continuous_subtype_val.comp continuous_snd)
    exact (continuous_fst.prodMk hc).prodMk
      (((continuous_subtype_val.comp continuous_snd).sub
        (continuous_subtype_val.comp hc)).subtype_mk _)


-- @@ L106-108 verbatim
@[simp] theorem addSection_apply (ε δ : ℝ≥0) (x : X) (u : Band (ε + δ)) :
    addSection X ε δ (x, u) = ((x, projIcc (-(δ : ℝ)) δ (neg_le_band δ) u),
      ⟨u - projIcc (-(δ : ℝ)) δ (neg_le_band δ) u, sub_projIcc_mem_band u⟩) := rfl


-- @@ L110-115 verbatim
/-- The section preserves height: `f x + c + (u - c) = f x + u`. -/
theorem height_addSection (f : C(X, ℝ)) (ε δ : ℝ≥0) (w : X × Band (ε + δ)) :
    height (height f δ) ε (addSection X ε δ w) = height f (ε + δ) w := by
  show f w.1 + (projIcc (-(δ : ℝ)) δ (neg_le_band δ) w.2 : ℝ) +
      ((w.2 : ℝ) - projIcc (-(δ : ℝ)) δ (neg_le_band δ) w.2) = f w.1 + w.2
  ring


-- @@ L117-120 verbatim
/-- `σ` is a section of the addition map: `μ ∘ σ = id`. -/
theorem addMap_comp_addSection (ε δ : ℝ≥0) :
    (addMap X ε δ).comp (addSection X ε δ) = ContinuousMap.id _ :=
  ContinuousMap.ext fun _ => Prod.ext rfl (Subtype.ext (add_sub_cancel _ _))


-- @@ L122-125 verbatim
/-- Naturality of the section in every continuous map. -/
theorem addSection_natural (g : C(X, Y)) (ε δ : ℝ≥0) :
    (addSection Y ε δ).comp (map g (ε + δ)) = (map (map g δ) ε).comp (addSection X ε δ) :=
  rfl


-- @@ L127-127 verbatim
end AddSection


-- @@ L129-129 verbatim
/-! ### The fibre paths -/


-- @@ L131-131 verbatim
section FiberPath


-- @@ L133-133 verbatim
variable {X : Type u} [TopologicalSpace X] {ε δ : ℝ≥0}


-- @@ L135-148 verbatim
/-- The straight segment from `z = ((x, s), t)` to `σ (μ z) = ((x, c), s + t - c)`, in the band
coordinates of `T_ε T_δ X`. It keeps `x` and stays in `Band δ × Band ε` by convexity. -/
def addFiberPath (z : (X × Band δ) × Band ε) : Path z (addSection X ε δ (addMap X ε δ z)) where
  toFun r := ((z.1.1, ⟨(1 - (r : ℝ)) * z.1.2 + r * (addSection X ε δ (addMap X ε δ z)).1.2,
      interp_mem_band _ _ r⟩),
    ⟨(1 - (r : ℝ)) * z.2 + r * (addSection X ε δ (addMap X ε δ z)).2, interp_mem_band _ _ r⟩)
  continuous_toFun := by
    have h₁ : Continuous fun r : unitInterval =>
        (1 - (r : ℝ)) * z.1.2 + r * (addSection X ε δ (addMap X ε δ z)).1.2 := by fun_prop
    have h₂ : Continuous fun r : unitInterval =>
        (1 - (r : ℝ)) * z.2 + r * (addSection X ε δ (addMap X ε δ z)).2 := by fun_prop
    exact (continuous_const.prodMk (h₁.subtype_mk _)).prodMk (h₂.subtype_mk _)
  source' := Prod.ext (Prod.ext rfl (Subtype.ext (by simp))) (Subtype.ext (by simp))
  target' := Prod.ext (Prod.ext rfl (Subtype.ext (by simp))) (Subtype.ext (by simp))


-- @@ L150-158 verbatim
/-- The fibre path keeps the thickened height `f x + s + t`. -/
theorem height_addFiberPath (f : C(X, ℝ)) (z : (X × Band δ) × Band ε) (r : unitInterval) :
    height (height f δ) ε (addFiberPath z r) = height (height f δ) ε z := by
  show f z.1.1 + ((1 - (r : ℝ)) * z.1.2 + r * (addSection X ε δ (addMap X ε δ z)).1.2) +
      ((1 - (r : ℝ)) * z.2 + r * (addSection X ε δ (addMap X ε δ z)).2) = f z.1.1 + z.1.2 + z.2
  have h : ((addSection X ε δ (addMap X ε δ z)).2 : ℝ) =
      z.1.2 + z.2 - (addSection X ε δ (addMap X ε δ z)).1.2 := rfl
  rw [h]
  ring


-- @@ L160-163 verbatim
/-- `z` and `σ (μ z)` are Reeb-equivalent for the thickened height of `T_ε T_δ`. -/
theorem reebRel_addSection_addMap (f : C(X, ℝ)) (z : (X × Band δ) × Band ε) :
    ReebRel (height (height f δ) ε) z (addSection X ε δ (addMap X ε δ z)) :=
  ⟨addFiberPath z, height_addFiberPath f z⟩


-- @@ L165-165 verbatim
end FiberPath


-- @@ L167-167 verbatim
/-! ### The Reeb-quotient homeomorphism -/


-- @@ L169-169 verbatim
section Homeomorph


-- @@ L171-171 verbatim
variable {X : Type u} [TopologicalSpace X]


-- @@ L173-186 verbatim
/-- **The Reeb quotient of the addition map is a homeomorphism**, for every `f : C(X, ℝ)` and
every `ε, δ`: the forward map is `ℛ μ` and the inverse is `ℛ σ`. -/
def quotientAddHomeomorph (f : C(X, ℝ)) (ε δ : ℝ≥0) :
    ReebQuotient (height (height f δ) ε) ≃ₜ ReebQuotient (height f (ε + δ)) where
  toFun := ReebQuotient.map (addMap X ε δ) (height_addMap f ε δ)
  invFun := ReebQuotient.map (addSection X ε δ) (height_addSection f ε δ)
  left_inv q := by
    induction q using ReebQuotient.ind with
    | h z => exact ((ReebQuotient.mk_eq_mk_iff _).2 (reebRel_addSection_addMap f z)).symm
  right_inv q := by
    induction q using ReebQuotient.ind with
    | h w => exact congrArg (ReebQuotient.mk _) (DFunLike.congr_fun (addMap_comp_addSection ε δ) w)
  continuous_toFun := (ReebQuotient.map _ _).continuous
  continuous_invFun := (ReebQuotient.map _ _).continuous


-- @@ L188-190 verbatim
theorem coe_quotientAddHomeomorph (f : C(X, ℝ)) (ε δ : ℝ≥0) :
    ⇑(quotientAddHomeomorph f ε δ) = ReebQuotient.map (addMap X ε δ) (height_addMap f ε δ) :=
  rfl


-- @@ L192-195 verbatim
theorem coe_quotientAddHomeomorph_symm (f : C(X, ℝ)) (ε δ : ℝ≥0) :
    ⇑(quotientAddHomeomorph f ε δ).symm =
      ReebQuotient.map (addSection X ε δ) (height_addSection f ε δ) :=
  rfl


-- @@ L197-199 verbatim
@[simp] theorem quotientAddHomeomorph_mk (f : C(X, ℝ)) (ε δ : ℝ≥0) (z : (X × Band δ) × Band ε) :
    quotientAddHomeomorph f ε δ (ReebQuotient.mk _ z) = ReebQuotient.mk _ (addMap X ε δ z) :=
  rfl


-- @@ L201-204 verbatim
@[simp] theorem quotientAddHomeomorph_symm_mk (f : C(X, ℝ)) (ε δ : ℝ≥0) (w : X × Band (ε + δ)) :
    (quotientAddHomeomorph f ε δ).symm (ReebQuotient.mk _ w) =
      ReebQuotient.mk _ (addSection X ε δ w) :=
  rfl


-- @@ L206-210 verbatim
/-- The homeomorphism preserves height. -/
theorem height_quotientAddHomeomorph (f : C(X, ℝ)) (ε δ : ℝ≥0)
    (q : ReebQuotient (height (height f δ) ε)) :
    ReebQuotient.height _ (quotientAddHomeomorph f ε δ q) = ReebQuotient.height _ q :=
  ReebQuotient.height_map_apply (addMap X ε δ) (height_addMap f ε δ) q


-- @@ L212-215 verbatim
/-- `ℛ μ` is bijective. -/
theorem bijective_quotientMap_addMap (f : C(X, ℝ)) (ε δ : ℝ≥0) :
    Function.Bijective (ReebQuotient.map (addMap X ε δ) (height_addMap f ε δ)) :=
  (quotientAddHomeomorph f ε δ).bijective


-- @@ L217-225 verbatim
/-- **Fibre comparison.** Two points of `T_ε T_δ X` have the same class after `ℛ μ` exactly when
they are Reeb-equivalent in `T_ε T_δ X`. -/
theorem mk_addMap_eq_mk_addMap_iff (f : C(X, ℝ)) {ε δ : ℝ≥0} (z z' : (X × Band δ) × Band ε) :
    ReebQuotient.mk (height f (ε + δ)) (addMap X ε δ z) =
        ReebQuotient.mk (height f (ε + δ)) (addMap X ε δ z') ↔
      ReebRel (height (height f δ) ε) z z' :=
  ⟨fun h => (ReebQuotient.mk_eq_mk_iff _).1 ((quotientAddHomeomorph f ε δ).injective
      (a₁ := ReebQuotient.mk _ z) (a₂ := ReebQuotient.mk _ z') h),
    fun h => (ReebQuotient.mk_eq_mk_iff _).2 (h.map (addMap X ε δ) (height_addMap f ε δ))⟩


-- @@ L227-227 verbatim
end Homeomorph


-- @@ L229-229 verbatim
/-! ### The real slice (universe `0`) -/


-- @@ L231-231 verbatim
section Over


-- @@ L233-233 verbatim
local notation "ℛ" => ReebQuotient.quotientFunctor ℝ


-- @@ L235-249 verbatim
/-- `ℛ μ_(ε,δ)` is an isomorphism at every object of the real slice. -/
instance isIso_quotientFunctor_map_addNatTrans_app (ε δ : ℝ≥0) (A : Over (TopCat.of ℝ)) :
    IsIso ((ℛ).map ((addNatTrans ε δ).app A)) := by
  let e : (ℛ).obj ((functor ε).obj ((functor δ).obj A)) ≅ (ℛ).obj ((functor (ε + δ)).obj A) :=
    Over.isoMk (TopCat.isoOfHomeo
        (X := ((ℛ).obj ((functor ε).obj ((functor δ).obj A))).left)
        (Y := ((ℛ).obj ((functor (ε + δ)).obj A)).left)
        (quotientAddHomeomorph (overBaseMap A) ε δ)) (by
      ext q
      exact height_quotientAddHomeomorph (overBaseMap A) ε δ q)
  have h : (ℛ).map ((addNatTrans ε δ).app A) = e.hom := by
    ext q
    rfl
  rw [h]
  infer_instance


-- @@ L251-255 verbatim
instance isIso_whiskerRight_addNatTrans (ε δ : ℝ≥0) :
    IsIso (Functor.whiskerRight (addNatTrans ε δ) ℛ) := by
  have : ∀ A, IsIso ((Functor.whiskerRight (addNatTrans ε δ) ℛ).app A) := fun A =>
    isIso_quotientFunctor_map_addNatTrans_app ε δ A
  exact NatIso.isIso_of_isIso_app _


-- @@ L257-259 verbatim
/-- **`ℛ T_ε T_δ ≅ ℛ T_(ε+δ)`** on the real slice, with hom `ℛ μ`. -/
def reebAddIso (ε δ : ℝ≥0) : (functor δ ⋙ functor ε) ⋙ ℛ ≅ functor (ε + δ) ⋙ ℛ :=
  asIso (Functor.whiskerRight (addNatTrans ε δ) ℛ)


-- @@ L261-263 verbatim
theorem reebAddIso_hom (ε δ : ℝ≥0) :
    (reebAddIso ε δ).hom = Functor.whiskerRight (addNatTrans ε δ) ℛ :=
  rfl


-- @@ L265-274 verbatim
/-- The inverse of `reebAddIso` is `ℛ σ`. -/
theorem reebAddIso_inv_app_left_hom (ε δ : ℝ≥0) (A : Over (TopCat.of ℝ)) :
    ((reebAddIso ε δ).inv.app A).left.hom =
      ReebQuotient.map (addSection A.left ε δ) (height_addSection (overBaseMap A) ε δ) := by
  ext q
  have h : quotientAddHomeomorph (overBaseMap A) ε δ (((reebAddIso ε δ).inv.app A).left.hom q) =
      q :=
    congrArg (fun φ => φ.left.hom q) ((reebAddIso ε δ).inv_hom_id_app A)
  exact ((quotientAddHomeomorph (overBaseMap A) ε δ).symm_apply_apply _).symm.trans
    (congrArg (quotientAddHomeomorph (overBaseMap A) ε δ).symm h)


-- @@ L276-286 verbatim
/-- A parameter equality `ε = δ` as an isomorphism `T_ε ≅ T_δ`, by band inclusions in both
directions; not `eqToIso`. -/
def bandEqIso {ε δ : ℝ≥0} (h : ε = δ) : functor ε ≅ functor δ where
  hom := bandInclusionNatTrans h.le
  inv := bandInclusionNatTrans h.ge
  hom_inv_id := by
    ext A z
    rfl
  inv_hom_id := by
    ext A z
    rfl


-- @@ L288-290 verbatim
theorem bandEqIso_hom {ε δ : ℝ≥0} (h : ε = δ) :
    (bandEqIso h).hom = bandInclusionNatTrans h.le :=
  rfl


-- @@ L292-294 verbatim
theorem bandEqIso_inv {ε δ : ℝ≥0} (h : ε = δ) :
    (bandEqIso h).inv = bandInclusionNatTrans h.ge :=
  rfl


-- @@ L296-306 verbatim
/-- **Associativity**, the `ℛ`-image of `addNatTrans_assoc`, with `(ε + δ) + γ = ε + (δ + γ)`
bridged by `bandEqIso`. -/
theorem reebAddIso_assoc (ε δ γ : ℝ≥0) :
    Functor.whiskerLeft (functor γ) (reebAddIso ε δ).hom ≫ (reebAddIso (ε + δ) γ).hom ≫
        Functor.whiskerRight (bandEqIso (add_assoc ε δ γ)).hom ℛ =
      Functor.whiskerRight (Functor.whiskerRight (addNatTrans δ γ) (functor ε)) ℛ ≫
        (reebAddIso ε (δ + γ)).hom := by
  ext A q
  induction q using ReebQuotient.ind with
  | h z =>
    exact congrArg (ReebQuotient.mk _) (DFunLike.congr_fun (addMap_assoc (X := A.left) ε δ γ) z)


-- @@ L308-315 verbatim
/-- `ℛ (T_ε μ_(δ,γ))` is an isomorphism, from associativity. -/
instance isIso_whiskerRight_whiskerRight_addNatTrans (ε δ γ : ℝ≥0) :
    IsIso (Functor.whiskerRight (Functor.whiskerRight (addNatTrans δ γ) (functor ε)) ℛ) := by
  have : IsIso (Functor.whiskerRight (Functor.whiskerRight (addNatTrans δ γ) (functor ε)) ℛ ≫
      (reebAddIso ε (δ + γ)).hom) := by
    rw [← reebAddIso_assoc]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (reebAddIso ε (δ + γ)).hom


-- @@ L317-320 verbatim
/-- `ℛ (T_ε μ_(δ,γ)) : ℛ T_ε T_δ T_γ ≅ ℛ T_ε T_(δ+γ)`. -/
def reebAddInnerIso (ε δ γ : ℝ≥0) :
    ((functor γ ⋙ functor δ) ⋙ functor ε) ⋙ ℛ ≅ (functor (δ + γ) ⋙ functor ε) ⋙ ℛ :=
  asIso (Functor.whiskerRight (Functor.whiskerRight (addNatTrans δ γ) (functor ε)) ℛ)


-- @@ L322-325 verbatim
theorem reebAddInnerIso_hom (ε δ γ : ℝ≥0) :
    (reebAddInnerIso ε δ γ).hom =
      Functor.whiskerRight (Functor.whiskerRight (addNatTrans δ γ) (functor ε)) ℛ :=
  rfl


-- @@ L327-332 verbatim
/-- **Associativity in iso form.** -/
theorem reebAddIso_assoc_iso (ε δ γ : ℝ≥0) :
    Functor.isoWhiskerLeft (functor γ) (reebAddIso ε δ) ≪≫ reebAddIso (ε + δ) γ ≪≫
        Functor.isoWhiskerRight (bandEqIso (add_assoc ε δ γ)) ℛ =
      reebAddInnerIso ε δ γ ≪≫ reebAddIso ε (δ + γ) :=
  Iso.ext (reebAddIso_assoc ε δ γ)


-- @@ L334-341 verbatim
/-- **Left unit law** against `zeroIso`, the `ℛ`-image of `addNatTrans_zero_left`. -/
theorem reebAddIso_zero_left (δ : ℝ≥0) :
    reebAddIso 0 δ ≪≫ Functor.isoWhiskerRight (bandEqIso (zero_add δ)) ℛ =
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft (functor δ) zeroIso) ℛ := by
  ext A q
  induction q using ReebQuotient.ind with
  | h z =>
    exact congrArg (ReebQuotient.mk _) (DFunLike.congr_fun (addMap_zero_left (X := A.left) δ) z)


-- @@ L343-350 verbatim
/-- **Right unit law** against `zeroIso`, the `ℛ`-image of `addNatTrans_zero_right`. -/
theorem reebAddIso_zero_right (δ : ℝ≥0) :
    reebAddIso δ 0 ≪≫ Functor.isoWhiskerRight (bandEqIso (add_zero δ)) ℛ =
      Functor.isoWhiskerRight (Functor.isoWhiskerRight zeroIso (functor δ)) ℛ := by
  ext A q
  induction q using ReebQuotient.ind with
  | h z =>
    exact congrArg (ReebQuotient.mk _) (DFunLike.congr_fun (addMap_zero_right (X := A.left) δ) z)


-- @@ L352-361 verbatim
/-- The outer zero section followed by `ℛ μ` is `ℛ` of the enlargement `δ ≤ ε + δ`. -/
theorem whiskerLeft_zeroSectionNatTrans_comp_reebAddIso (ε δ : ℝ≥0) :
    Functor.whiskerRight (Functor.whiskerLeft (functor δ) (zeroSectionNatTrans ε)) ℛ ≫
        (reebAddIso ε δ).hom =
      Functor.whiskerRight (bandInclusionNatTrans (le_add_self : δ ≤ ε + δ)) ℛ := by
  ext A q
  induction q using ReebQuotient.ind with
  | h z =>
    exact congrArg (ReebQuotient.mk _)
      (DFunLike.congr_fun (addMap_comp_zeroSection (X := A.left) ε δ) z)


-- @@ L363-372 verbatim
/-- `T_ε` of the inner zero section followed by `ℛ μ` is `ℛ` of the enlargement `ε ≤ ε + δ`. -/
theorem whiskerRight_zeroSectionNatTrans_comp_reebAddIso (ε δ : ℝ≥0) :
    Functor.whiskerRight (Functor.whiskerRight (zeroSectionNatTrans δ) (functor ε)) ℛ ≫
        (reebAddIso ε δ).hom =
      Functor.whiskerRight (bandInclusionNatTrans (le_self_add : ε ≤ ε + δ)) ℛ := by
  ext A q
  induction q using ReebQuotient.ind with
  | h z =>
    exact congrArg (ReebQuotient.mk _)
      (DFunLike.congr_fun (addMap_comp_map_zeroSection (X := A.left) ε δ) z)


-- @@ L374-382 verbatim
/-- **Band enlargement**, the `ℛ`-image of `addNatTrans_comp_bandInclusionNatTrans`. -/
theorem reebAddIso_comp_bandInclusionNatTrans {ε ε' δ δ' : ℝ≥0} (hε : ε ≤ ε') (hδ : δ ≤ δ') :
    Functor.whiskerRight (Functor.whiskerRight (bandInclusionNatTrans hδ) (functor ε)) ℛ ≫
        Functor.whiskerRight (Functor.whiskerLeft (functor δ') (bandInclusionNatTrans hε)) ℛ ≫
          (reebAddIso ε' δ').hom =
      (reebAddIso ε δ).hom ≫ Functor.whiskerRight (bandInclusionNatTrans (add_le_add hε hδ)) ℛ := by
  ext A q
  induction q using ReebQuotient.ind with
  | h z => rfl


-- @@ L384-384 verbatim
end Over


-- @@ L386-386 verbatim
end


-- @@ L388-388 verbatim
end GeometricThickening


-- @@ L390-390 verbatim
/-! ### Graph objects -/


-- @@ L392-392 verbatim
noncomputable section


-- @@ L394-394 verbatim
namespace RGraph


-- @@ L396-396 verbatim
local notation "ℛ" => ReebQuotient.quotientFunctor ℝ


-- @@ L398-406 verbatim
/-- The Reeb quotient of `T_ε T_δ A` is a graph object for every graph object `A`, through its
isomorphism with the Reeb quotient of `T_(ε+δ) A`. -/
theorem isRGraph_quotient_thickening_thickening {A : Over (TopCat.of ℝ)} (hA : IsRGraph A)
    (ε δ : ℝ≥0) :
    IsRGraph ((ℛ).obj ((GeometricThickening.functor ε).obj
      ((GeometricThickening.functor δ).obj A))) := by
  obtain ⟨m, T, D, ⟨i⟩⟩ :=
    isRGraph_quotient_of_isConstructibleSpace (isConstructibleSpace_thickening hA (ε + δ))
  exact ⟨m, T, D, ⟨(GeometricThickening.reebAddIso ε δ).app A ≪≫ i⟩⟩


-- @@ L408-411 verbatim
/-- `A ↦ ℛ T_ε T_δ A` on graph objects. -/
def doubleThickeningQuotient (ε δ : ℝ≥0) : RGraphCat ⥤ RGraphCat :=
  IsRGraph.lift (IsRGraph.ι ⋙ GeometricThickening.functor δ ⋙ GeometricThickening.functor ε ⋙ ℛ)
    fun A => isRGraph_quotient_thickening_thickening A.property ε δ


-- @@ L413-416 verbatim
theorem doubleThickeningQuotient_comp_ι (ε δ : ℝ≥0) :
    doubleThickeningQuotient ε δ ⋙ IsRGraph.ι =
      IsRGraph.ι ⋙ GeometricThickening.functor δ ⋙ GeometricThickening.functor ε ⋙ ℛ :=
  rfl


-- @@ L418-426 verbatim
/-- **`ℛ T_ε T_δ ≅ U_(ε+δ)`** on graph objects, with target the merged
`geometricSmoothing (ε + δ)`. Its components are those of `GeometricThickening.reebAddIso`. -/
def geometricSmoothingAddIso (ε δ : ℝ≥0) :
    doubleThickeningQuotient ε δ ≅ geometricSmoothing (ε + δ) :=
  NatIso.ofComponents
    (fun A => ObjectProperty.isoMk _ ((GeometricThickening.reebAddIso ε δ).app A.obj))
    (fun φ => by
      ext1
      exact (GeometricThickening.reebAddIso ε δ).hom.naturality φ.hom)


-- @@ L428-431 verbatim
theorem geometricSmoothingAddIso_hom_app_hom (ε δ : ℝ≥0) (A : RGraphCat) :
    ((geometricSmoothingAddIso ε δ).hom.app A).hom =
      (ℛ).map ((GeometricThickening.addNatTrans ε δ).app A.obj) :=
  rfl


-- @@ L433-436 verbatim
theorem geometricSmoothingAddIso_inv_app_hom (ε δ : ℝ≥0) (A : RGraphCat) :
    ((geometricSmoothingAddIso ε δ).inv.app A).hom =
      (GeometricThickening.reebAddIso ε δ).inv.app A.obj :=
  rfl


-- @@ L438-438 verbatim
end RGraph


-- @@ L440-440 verbatim
end


-- @@ L442-442 verbatim
end TDA.Reeb
