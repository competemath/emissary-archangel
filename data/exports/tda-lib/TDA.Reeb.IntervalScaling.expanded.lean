import TDA.Reeb.IntervalTranslation
import Mathlib.Analysis.Normed.Field.Basic


-- @@ L4-17 verbatim
/-!
# Scaling interval precosheaves

`OpenInterval.scale s I` is the inverse image of `I` under multiplication by `s`, including
negative and zero multipliers. The thickening law is
`thicken ε (scale s I) = scale s (thicken (‖s‖₊ * ε) I)`. Thus an `ε`-interleaving transports to a
`‖s‖₊ * ε`-interleaving of `scalePre s F` and `scalePre s G` in any target category.
For `s ≠ 0`, inverse scaling gives exact homogeneity of the extended interleaving distance;
reflection is an isometry. Interval components of `s • f` are definitionally `scalePre s`
of the interval components of `f`, also when the two heights have different domains.

These are library statements in the setting of de Silva–Munch–Patel, Definition 4.4.
No scaling functor on graph objects or compatibility with geometric smoothing is constructed.
-/


-- @@ L19-19 verbatim
open Set CategoryTheory

-- @@ L20-20 verbatim
open scoped NNReal ENNReal


-- @@ L22-22 verbatim
universe v u w


-- @@ L24-24 verbatim
namespace TDA.Reeb


-- @@ L26-26 verbatim
noncomputable section

-- @@ L27-27 verbatim
open scoped Classical

-- @@ L28-28 verbatim
namespace OpenInterval


-- @@ L30-36 verbatim
/-- Inverse image of an interval under multiplication by `s`. -/
def scale (s : ℝ) (I : OpenInterval) : OpenInterval :=
  ⟨(s * ·) ⁻¹' (I : Set ℝ), I.isOpen.preimage (continuous_const.mul continuous_id),
    by
      rcases le_total 0 s with h | h
      · exact I.ordConnected.preimage_mono (fun _ _ hxy => mul_le_mul_of_nonneg_left hxy h)
      · exact I.ordConnected.preimage_anti (fun _ _ hxy => mul_le_mul_of_nonpos_left hxy h)⟩


-- @@ L38-39 verbatim
@[simp] theorem mem_scale {s x : ℝ} {I : OpenInterval} :
    x ∈ scale s I ↔ s * x ∈ I := Iff.rfl


-- @@ L41-42 verbatim
@[simp] theorem coe_scale (s : ℝ) (I : OpenInterval) :
    (scale s I : Set ℝ) = (s * ·) ⁻¹' (I : Set ℝ) := rfl


-- @@ L44-48 verbatim
theorem scale_ioo_of_pos {s : ℝ} (hs : 0 < s) (p q : ℝ) :
    scale s (ioo p q) = ioo (p / s) (q / s) := by
  ext x
  change p < s * x ∧ s * x < q ↔ p / s < x ∧ x < q / s
  simp only [div_lt_iff₀ hs, lt_div_iff₀ hs, mul_comm s]


-- @@ L50-54 verbatim
theorem scale_ioo_of_neg {s : ℝ} (hs : s < 0) (p q : ℝ) :
    scale s (ioo p q) = ioo (q / s) (p / s) := by
  ext x
  change p < s * x ∧ s * x < q ↔ q / s < x ∧ x < p / s
  simp only [div_lt_iff_of_neg hs, lt_div_iff_of_neg hs, mul_comm s, and_comm]


-- @@ L56-56 verbatim
@[simp] theorem scale_one (I : OpenInterval) : scale 1 I = I := by ext; simp


-- @@ L58-58 verbatim
@[simp] theorem scale_top (s : ℝ) : scale s ⊤ = ⊤ := rfl


-- @@ L60-60 verbatim
@[simp] theorem scale_bot (s : ℝ) : scale s ⊥ = ⊥ := rfl


-- @@ L62-69 verbatim
theorem scale_zero (I : OpenInterval) : scale 0 I = if 0 ∈ I then ⊤ else ⊥ := by
  split_ifs with h
  · ext x
    change (0 * x ∈ I ↔ True)
    simp [h]
  · ext x
    change (0 * x ∈ I ↔ False)
    simp [h]


-- @@ L71-72 verbatim
theorem scale_scale (s μ : ℝ) (I : OpenInterval) :
    scale s (scale μ I) = scale (μ * s) I := by ext; simp [mul_assoc]


-- @@ L74-74 verbatim
theorem scale_monotone (s : ℝ) : Monotone (scale s) := fun _ _ h _ hx => h hx


-- @@ L76-94 verbatim
/-- Thickening and inverse scaling agree after multiplying the radius by `|s|`. -/
theorem thicken_scale (s : ℝ) (ε : ℝ≥0) (I : OpenInterval) :
    thicken ε (scale s I) = scale s (thicken (‖s‖₊ * ε) I) := by
  by_cases hs : s = 0
  · subst s
    simp only [nnnorm_zero, zero_mul, thicken_zero, scale_zero]
    split_ifs <;> simp
  ext x
  simp only [mem_thicken, mem_scale, NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs]
  constructor
  · rintro ⟨y, hy, hxy⟩
    refine ⟨s * y, hy, ?_⟩
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left hxy (abs_nonneg s)
  · rintro ⟨y, hy, hxy⟩
    refine ⟨y / s, by simpa only [mul_div_cancel₀ _ hs] using hy, ?_⟩
    apply (mul_le_mul_iff_right₀ (abs_pos.2 hs)).1
    rw [← abs_mul, mul_sub, mul_div_cancel₀ _ hs]
    exact hxy


-- @@ L96-97 verbatim
/-- Inverse scaling as an endofunctor of the interval category. -/
def scaleFunctor (s : ℝ) : OpenInterval ⥤ OpenInterval := (scale_monotone s).functor


-- @@ L99-100 verbatim
@[simp] theorem scaleFunctor_obj (s : ℝ) (I : OpenInterval) :
    (scaleFunctor s).obj I = scale s I := rfl


-- @@ L102-102 verbatim
end OpenInterval

-- @@ L103-103 verbatim
open OpenInterval


-- @@ L105-105 verbatim
section Precosheaf

-- @@ L106-106 verbatim
variable {C : Type u} [Category.{v} C]


-- @@ L108-109 verbatim
/-- Reindex a precosheaf by inverse scaling of intervals. -/
def scalePre (s : ℝ) (F : OpenInterval ⥤ C) : OpenInterval ⥤ C := scaleFunctor s ⋙ F


-- @@ L111-112 verbatim
@[simp] theorem scalePre_obj (s : ℝ) (F : OpenInterval ⥤ C) (I : OpenInterval) :
    (scalePre s F).obj I = F.obj (scale s I) := rfl


-- @@ L114-115 verbatim
@[simp] theorem scalePre_map (s : ℝ) (F : OpenInterval ⥤ C) {I J : OpenInterval}
    (f : I ⟶ J) : (scalePre s F).map f = F.map ((scaleFunctor s).map f) := rfl


-- @@ L117-121 expanded
/-- Scaling by one gives the original precosheaf. -/
def scalePreOneIso (F : OpenInterval ⥤ C) : scalePre 1 F ≅ F :=
  NatIso.ofComponents (fun I => F.mapIso (eqToIso (scale_one I))) fun _ =>
    by
    dsimp
    first
    | exact map_eq_map_of_interval _ _ _
    | exact map_comp2_eq_comp2_of_interval _ _ _ _ _
    | exact map_comp3_eq_comp2_of_interval _ _ _ _ _ _
    | exact map_comp_map_of_interval _ _ _ _
    | exact map_comp_map_comp_map_of_interval _ _ _ _ _
    | exact map_comp4_of_interval _ _ _ _ _ _
    | exact map_comp5_of_interval _ _ _ _ _ _ _
    | exact map_comp6_of_interval _ _ _ _ _ _ _ _
    | exact (map_eq_map_of_interval _ _ (𝟙 _)).trans (CategoryTheory.Functor.map_id _ _)
    | exact (map_comp_map_of_interval _ _ _ (𝟙 _)).trans (CategoryTheory.Functor.map_id _ _)
    |
      exact
        (map_comp_map_comp_map_of_interval _ _ _ _ (𝟙 _)).trans (CategoryTheory.Functor.map_id _ _)
    | exact (map_comp6_of_interval _ _ _ _ _ _ _ (𝟙 _)).trans (CategoryTheory.Functor.map_id _ _)


-- @@ L123-128 expanded
/-- Composition of scaling operations on precosheaves. -/
def scalePreScalePreIso (s μ : ℝ) (F : OpenInterval ⥤ C) :
    scalePre s (scalePre μ F) ≅ scalePre (s * μ) F :=
  NatIso.ofComponents (fun I => F.mapIso (eqToIso (scale_scale μ s I))) fun _ =>
    by
    simp only [scalePre_map, Functor.mapIso_hom]
    first
    | exact map_eq_map_of_interval _ _ _
    | exact map_comp2_eq_comp2_of_interval _ _ _ _ _
    | exact map_comp3_eq_comp2_of_interval _ _ _ _ _ _
    | exact map_comp_map_of_interval _ _ _ _
    | exact map_comp_map_comp_map_of_interval _ _ _ _ _
    | exact map_comp4_of_interval _ _ _ _ _ _
    | exact map_comp5_of_interval _ _ _ _ _ _ _
    | exact map_comp6_of_interval _ _ _ _ _ _ _ _
    | exact (map_eq_map_of_interval _ _ (𝟙 _)).trans (CategoryTheory.Functor.map_id _ _)
    | exact (map_comp_map_of_interval _ _ _ (𝟙 _)).trans (CategoryTheory.Functor.map_id _ _)
    |
      exact
        (map_comp_map_comp_map_of_interval _ _ _ _ (𝟙 _)).trans (CategoryTheory.Functor.map_id _ _)
    | exact (map_comp6_of_interval _ _ _ _ _ _ _ (𝟙 _)).trans (CategoryTheory.Functor.map_id _ _)


-- @@ L130-156 expanded
/-- Scale the interval argument of both interleaving maps and multiply the radius by `|s|`. -/
def Interleaving.scalePre {ε : ℝ≥0} {F G : OpenInterval ⥤ C} (s : ℝ) (i : Interleaving ε F G) :
    Interleaving (‖s‖₊ * ε) (TDA.Reeb.scalePre s F) (TDA.Reeb.scalePre s G) :=
  Interleaving.ofApp
    { app := fun I => i.φ.app (scale s I) ≫ G.map (homOfLE (thicken_scale s ε I).le)
      naturality := fun I J f => by
        dsimp
        erw [reassoc_of% (i.φ.naturality ((scaleFunctor s).map f))]
        refine Eq.trans ?_ (Category.assoc _ _ _).symm
        congr 1
        first
        | exact map_eq_map_of_interval _ _ _
        | exact map_comp2_eq_comp2_of_interval _ _ _ _ _
        | exact map_comp3_eq_comp2_of_interval _ _ _ _ _ _
        | exact map_comp_map_of_interval _ _ _ _
        | exact map_comp_map_comp_map_of_interval _ _ _ _ _
        | exact map_comp4_of_interval _ _ _ _ _ _
        | exact map_comp5_of_interval _ _ _ _ _ _ _
        | exact map_comp6_of_interval _ _ _ _ _ _ _ _
        | exact (map_eq_map_of_interval _ _ (𝟙 _)).trans (CategoryTheory.Functor.map_id _ _)
        | exact (map_comp_map_of_interval _ _ _ (𝟙 _)).trans (CategoryTheory.Functor.map_id _ _)
        |
          exact
            (map_comp_map_comp_map_of_interval _ _ _ _ (𝟙 _)).trans
              (CategoryTheory.Functor.map_id _ _)
        |
          exact
            (map_comp6_of_interval _ _ _ _ _ _ _ (𝟙 _)).trans (CategoryTheory.Functor.map_id _ _) }
    { app := fun I => i.ψ.app (scale s I) ≫ F.map (homOfLE (thicken_scale s ε I).le)
      naturality := fun I J f => by
        dsimp
        erw [reassoc_of% (i.ψ.naturality ((scaleFunctor s).map f))]
        refine Eq.trans ?_ (Category.assoc _ _ _).symm
        congr 1
        first
        | exact map_eq_map_of_interval _ _ _
        | exact map_comp2_eq_comp2_of_interval _ _ _ _ _
        | exact map_comp3_eq_comp2_of_interval _ _ _ _ _ _
        | exact map_comp_map_of_interval _ _ _ _
        | exact map_comp_map_comp_map_of_interval _ _ _ _ _
        | exact map_comp4_of_interval _ _ _ _ _ _
        | exact map_comp5_of_interval _ _ _ _ _ _ _
        | exact map_comp6_of_interval _ _ _ _ _ _ _ _
        | exact (map_eq_map_of_interval _ _ (𝟙 _)).trans (CategoryTheory.Functor.map_id _ _)
        | exact (map_comp_map_of_interval _ _ _ (𝟙 _)).trans (CategoryTheory.Functor.map_id _ _)
        |
          exact
            (map_comp_map_comp_map_of_interval _ _ _ _ (𝟙 _)).trans
              (CategoryTheory.Functor.map_id _ _)
        |
          exact
            (map_comp6_of_interval _ _ _ _ _ _ _ (𝟙 _)).trans (CategoryTheory.Functor.map_id _ _) }
    (fun I => by
      dsimp
      rw [Category.assoc, i.φ_map_ψ_assoc]
      first
      | exact map_eq_map_of_interval _ _ _
      | exact map_comp2_eq_comp2_of_interval _ _ _ _ _
      | exact map_comp3_eq_comp2_of_interval _ _ _ _ _ _
      | exact map_comp_map_of_interval _ _ _ _
      | exact map_comp_map_comp_map_of_interval _ _ _ _ _
      | exact map_comp4_of_interval _ _ _ _ _ _
      | exact map_comp5_of_interval _ _ _ _ _ _ _
      | exact map_comp6_of_interval _ _ _ _ _ _ _ _
      | exact (map_eq_map_of_interval _ _ (𝟙 _)).trans (CategoryTheory.Functor.map_id _ _)
      | exact (map_comp_map_of_interval _ _ _ (𝟙 _)).trans (CategoryTheory.Functor.map_id _ _)
      |
        exact
          (map_comp_map_comp_map_of_interval _ _ _ _ (𝟙 _)).trans
            (CategoryTheory.Functor.map_id _ _)
      | exact (map_comp6_of_interval _ _ _ _ _ _ _ (𝟙 _)).trans (CategoryTheory.Functor.map_id _ _))
    (fun I => by
      dsimp
      rw [Category.assoc, i.ψ_map_φ_assoc]
      first
      | exact map_eq_map_of_interval _ _ _
      | exact map_comp2_eq_comp2_of_interval _ _ _ _ _
      | exact map_comp3_eq_comp2_of_interval _ _ _ _ _ _
      | exact map_comp_map_of_interval _ _ _ _
      | exact map_comp_map_comp_map_of_interval _ _ _ _ _
      | exact map_comp4_of_interval _ _ _ _ _ _
      | exact map_comp5_of_interval _ _ _ _ _ _ _
      | exact map_comp6_of_interval _ _ _ _ _ _ _ _
      | exact (map_eq_map_of_interval _ _ (𝟙 _)).trans (CategoryTheory.Functor.map_id _ _)
      | exact (map_comp_map_of_interval _ _ _ (𝟙 _)).trans (CategoryTheory.Functor.map_id _ _)
      |
        exact
          (map_comp_map_comp_map_of_interval _ _ _ _ (𝟙 _)).trans
            (CategoryTheory.Functor.map_id _ _)
      | exact (map_comp6_of_interval _ _ _ _ _ _ _ (𝟙 _)).trans (CategoryTheory.Functor.map_id _ _))


-- @@ L158-165 verbatim
private theorem distance_scalePre_le {s : ℝ} (hs : s ≠ 0) (F G : OpenInterval ⥤ C) :
    interleavingDistance (scalePre s F) (scalePre s G) ≤
      (‖s‖₊ : ℝ≥0∞) * interleavingDistance F G := by
  have hn : (‖s‖₊ : ℝ≥0∞) ≠ 0 := by simpa using hs
  conv_rhs => unfold interleavingDistance
  simp only [ENNReal.mul_iInf_of_ne hn ENNReal.coe_ne_top]
  exact le_iInf₂ fun ε ⟨i⟩ => by
    simpa only [ENNReal.coe_mul] using (i.scalePre s).interleavingDistance_le


-- @@ L167-179 verbatim
/-- Nonzero height scaling multiplies the extended interleaving distance by `|s|`. -/
theorem interleavingDistance_scalePre {s : ℝ} (hs : s ≠ 0) (F G : OpenInterval ⥤ C) :
    interleavingDistance (scalePre s F) (scalePre s G) =
      (‖s‖₊ : ℝ≥0∞) * interleavingDistance F G := by
  refine le_antisymm (distance_scalePre_le hs F G) ?_
  have e (H : OpenInterval ⥤ C) : scalePre s⁻¹ (scalePre s H) ≅ H :=
    scalePreScalePreIso s⁻¹ s H ≪≫ eqToIso (by rw [inv_mul_cancel₀ hs]) ≪≫ scalePreOneIso H
  have h := distance_scalePre_le (inv_ne_zero hs) (scalePre s F) (scalePre s G)
  rw [interleavingDistance_congr (e F) (e G)] at h
  have hn : ‖s‖₊ ≠ 0 := nnnorm_ne_zero_iff.2 hs
  have hprod : (‖s‖₊ : ℝ≥0∞) * (‖s⁻¹‖₊ : ℝ≥0∞) = 1 := by
    rw [nnnorm_inv, ← ENNReal.coe_mul, mul_inv_cancel₀ hn, ENNReal.coe_one]
  simpa only [← mul_assoc, hprod, one_mul] using mul_le_mul_right h (‖s‖₊ : ℝ≥0∞)


-- @@ L181-184 verbatim
/-- Reflection of the interval argument preserves distance. -/
theorem interleavingDistance_scalePre_neg_one (F G : OpenInterval ⥤ C) :
    interleavingDistance (scalePre (-1) F) (scalePre (-1) G) = interleavingDistance F G := by
  simpa using interleavingDistance_scalePre (by norm_num : (-1 : ℝ) ≠ 0) F G


-- @@ L186-186 verbatim
end Precosheaf


-- @@ L188-190 verbatim
/-- The component precosheaf of a scaled height is reindexed by inverse scaling. -/
theorem intervalComponents_smul {X : Type u} [TopologicalSpace X] (s : ℝ) (f : C(X, ℝ)) :
    intervalComponents (s • f) = scalePre s (intervalComponents f) := rfl


-- @@ L192-198 verbatim
/-- Exact homogeneity for heights on possibly different spaces in the same universe. -/
theorem interleavingDistance_intervalComponents_smul {X X' : Type u}
    [TopologicalSpace X] [TopologicalSpace X'] {s : ℝ} (hs : s ≠ 0)
    (f : C(X, ℝ)) (g : C(X', ℝ)) :
    interleavingDistance (intervalComponents (s • f)) (intervalComponents (s • g)) =
      (‖s‖₊ : ℝ≥0∞) * interleavingDistance (intervalComponents f) (intervalComponents g) := by
  rw [intervalComponents_smul, intervalComponents_smul, interleavingDistance_scalePre hs]


-- @@ L200-200 verbatim
end


-- @@ L202-202 verbatim
end TDA.Reeb
