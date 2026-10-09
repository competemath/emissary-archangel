import OAI.Geometry.DoublingHilbert.SelectedSheets
import OAI.Geometry.DoublingHilbert.Extremal


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
/-! Anisotropic energy bounds and arbitrarily small-energy period grids. -/


-- @@ L8-8 verbatim
open MeasureTheory Set Filter

-- @@ L9-9 verbatim
open scoped BigOperators Topology


-- @@ L11-11 verbatim
namespace DoublingHilbert

-- @@ L12-12 verbatim
open MeasureTheory Set Filter

-- @@ L13-13 verbatim
noncomputable section


-- @@ L15-21 verbatim
/-- A squared triangle inequality with the same reference vector. -/
theorem norm_sub_sq_le_two {E : Type*} [NormedAddCommGroup E] (a b c : E) :
    ‖a - b‖ ^ 2 ≤ 2 * ‖a - c‖ ^ 2 + 2 * ‖b - c‖ ^ 2 := by
  have h := norm_sub_le_norm_sub_add_norm_sub a c b
  rw [norm_sub_rev c b] at h
  have hs := pow_le_pow_left₀ (norm_nonneg (a - b)) h 2
  nlinarith [sq_nonneg (‖a - c‖ - ‖b - c‖)]


-- @@ L23-23 verbatim
section ProbabilityEnergy

-- @@ L24-25 verbatim
variable {X E : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]


-- @@ L27-35 verbatim
theorem norm_mean_sub_le_of_energy {F : X → E} (hF : IsBoundedField F)
    (a : E) {t : ℝ} (ht : 0 ≤ t)
    (he : (∫ x, ‖F x - a‖ ^ 2 ∂μ) ≤ t ^ 2) :
    ‖(∫ x, F x ∂μ) - a‖ ≤ t := by
  have hf := hF.sub (IsBoundedField.const a)
  have hb := norm_integral_sq_le_mass_mul (hf.integrable μ) (hf.norm_sq.integrable μ)
  rw [probReal_univ, one_mul, integral_sub (hF.integrable μ) (integrable_const a),
    integral_const, probReal_univ, one_smul] at hb
  exact (sq_le_sq₀ (norm_nonneg _) ht).mp (hb.trans he)


-- @@ L37-48 verbatim
omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem energy_sub_le_two {F G : X → E} (hF : IsBoundedField F)
    (hG : IsBoundedField G) (a : E) :
    (∫ x, ‖G x - F x‖ ^ 2 ∂μ) ≤
      2 * (∫ x, ‖G x - a‖ ^ 2 ∂μ) + 2 * (∫ x, ‖F x - a‖ ^ 2 ∂μ) := by
  have hGa := (hG.sub (IsBoundedField.const a)).norm_sq
  have hFa := (hF.sub (IsBoundedField.const a)).norm_sq
  have hb := integral_mono ((hG.sub hF).norm_sq.integrable μ)
    (((hGa.const_mul 2).add (hFa.const_mul 2)).integrable μ)
    (fun x => norm_sub_sq_le_two (G x) (F x) a)
  simpa only [integral_add ((hGa.const_mul 2).integrable μ) ((hFa.const_mul 2).integrable μ),
    integral_const_mul] using hb


-- @@ L50-50 verbatim
end ProbabilityEnergy


-- @@ L52-52 verbatim
section Energies

-- @@ L53-54 verbatim
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]


-- @@ L56-58 verbatim
def horizontalEnergy {f : constructedSet → E} {D : NNReal} (hf : LipschitzWith D f)
    (w : Tuple) (j : ℕ) (p : Base) : ℝ :=
  ‖horizontalColumn hf w j (1, 0) p - column (globalSheet hf w) (1, 0) p‖ ^ 2


-- @@ L60-62 verbatim
def verticalEnergy {f : constructedSet → E} {D : NNReal} (hf : LipschitzWith D f)
    (w : Tuple) (j : ℕ) (p : Base) : ℝ :=
  ‖verticalColumn hf w j (0, 1) p - column (globalSheet hf w) (0, 1) p‖ ^ 2


-- @@ L64-66 verbatim
def combinedEnergy {f : constructedSet → E} {D : NNReal} (hf : LipschitzWith D f)
    (w : Tuple) (j : ℕ) (p : Base) : ℝ :=
  (widthFactor j : ℝ) ^ 2 * horizontalEnergy hf w j p + verticalEnergy hf w j p


-- @@ L68-73 verbatim
omit [CompleteSpace E] in
theorem bounded_baseColumn {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) (v : Base) :
    IsBoundedField (column (globalSheet hf w) v) := by
  obtain ⟨C, hC⟩ := globalSheet_lipschitz hf w
  exact boundedField_column hC v


-- @@ L75-79 verbatim
omit [CompleteSpace E] in
theorem bounded_horizontalEnergy {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) (j : ℕ) :
    IsBoundedField (horizontalEnergy hf w j) :=
  ((bounded_horizontalColumn hf w j _).sub (bounded_baseColumn hf w _)).norm_sq


-- @@ L81-85 verbatim
omit [CompleteSpace E] in
theorem bounded_verticalEnergy {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) (j : ℕ) :
    IsBoundedField (verticalEnergy hf w j) :=
  ((bounded_verticalColumn hf w j _).sub (bounded_baseColumn hf w _)).norm_sq


-- @@ L87-91 verbatim
omit [CompleteSpace E] in
theorem bounded_combinedEnergy {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) (j : ℕ) :
    IsBoundedField (combinedEnergy hf w j) :=
  ((bounded_horizontalEnergy hf w j).const_mul _).add (bounded_verticalEnergy hf w j)


-- @@ L93-98 verbatim
omit [CompleteSpace E] in
theorem combinedEnergy_nonneg {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) (j : ℕ) (p : Base) :
    0 ≤ combinedEnergy hf w j p := by
  unfold combinedEnergy horizontalEnergy verticalEnergy
  positivity


-- @@ L100-100 verbatim
end Energies


-- @@ L102-102 verbatim
end

-- @@ L103-103 verbatim
end DoublingHilbert


-- @@ L105-105 verbatim
namespace DoublingHilbert

-- @@ L106-106 verbatim
open MeasureTheory Set Filter

-- @@ L107-107 verbatim
noncomputable section


-- @@ L109-109 verbatim
def horizontalCoefficient (D : ℝ) : ℝ := 4 + 8 * D * (2 * D + 1)

-- @@ L110-110 verbatim
def verticalCoefficient (D C : ℝ) : ℝ := 4 + 2 * C + 8 * C * D + 8 * D * (2 * D + 1)


-- @@ L112-114 verbatim
theorem horizontalCoefficient_pos {D : ℝ} (hD : 0 ≤ D) : 0 < horizontalCoefficient D := by
  unfold horizontalCoefficient
  positivity


-- @@ L116-119 verbatim
theorem verticalCoefficient_pos {D C : ℝ} (hD : 0 ≤ D) (hC : 0 ≤ C) :
    0 < verticalCoefficient D C := by
  unfold verticalCoefficient
  positivity


-- @@ L121-121 verbatim
section AnisotropicEnergy

-- @@ L122-123 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]


-- @@ L125-205 verbatim
/-- Finite-epsilon anisotropic energy estimates. -/
theorem anisotropic_energy_bound {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) (j : ℕ) (hj : w j = 0)
    (G : PeriodGrid j) (hQ : G.rectangle.closed ⊆ sheetDomain w)
    {A B C ε t : ℝ} (hC : 0 ≤ C) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hfirst : ∀ z ∈ derivativeCompact f, z.1 ≤ A)
    (hbarrier : ∀ z ∈ derivativeCompact f, z.2 ≤ B + ε + C * (A - z.1))
    (u v : E) (hu : ‖u‖ ≤ 2 * D) (hv : ‖v‖ ≤ 2 * D)
    (hnearu : A - ‖u‖ ^ 2 ≤ t) (hnearv : B - ‖v‖ ^ 2 ≤ t)
    (hbaseu : (∫ p, ‖column (globalSheet hf w) (1, 0) p - u‖ ^ 2 ∂G.rectangle.law) ≤ t ^ 2)
    (hbasev : (∫ p, ‖column (globalSheet hf w) (0, 1) p - v‖ ^ 2 ∂G.rectangle.law) ≤ t ^ 2)
    (hrx : scale j / G.rectangle.x.length ≤ t)
    (hry : scale j / G.rectangle.y.length ≤ t) :
    (∫ p, horizontalEnergy hf w j p ∂G.rectangle.law) ≤ horizontalCoefficient D * t ∧
    (∫ p, verticalEnergy hf w j p ∂G.rectangle.law) ≤
      2 * ε + 16 * C * (D : ℝ) ^ 2 / (widthFactor j : ℝ) + verticalCoefficient D C * t := by
  let Q := G.rectangle
  let H := horizontalColumn hf w j (1, 0)
  let X := verticalColumn hf w j (1, 0)
  let Y := verticalColumn hf w j (0, 1)
  let F₁ := column (globalSheet hf w) (1, 0)
  let F₂ := column (globalSheet hf w) (0, 1)
  have bH : IsBoundedField H := bounded_horizontalColumn hf w j _
  have bX : IsBoundedField X := bounded_verticalColumn hf w j _
  have bY : IsBoundedField Y := bounded_verticalColumn hf w j _
  have bF₁ : IsBoundedField F₁ := bounded_baseColumn hf w _
  have bF₂ : IsBoundedField F₂ := bounded_baseColumn hf w _
  have hmu : ‖(∫ p, F₁ p ∂Q.law) - u‖ ≤ t :=
    norm_mean_sub_le_of_energy bF₁ u ht hbaseu
  have hmv : ‖(∫ p, F₂ p ∂Q.law) - v‖ ≤ t :=
    norm_mean_sub_le_of_energy bF₂ v ht hbasev
  have hrx' : 2 * (D : ℝ) * scale j / Q.x.length ≤ 2 * D * t := by
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hrx (by positivity : 0 ≤ 2 * (D : ℝ))
  have hry' : 2 * (D : ℝ) * scale j / Q.y.length ≤ 2 * D * t := by
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hry (by positivity : 0 ≤ 2 * (D : ℝ))
  have hmH : ‖(∫ p, H p ∂Q.law) - u‖ ≤ (2 * D + 1) * t := by
    have h := horizontalColumn_mean hf w j hj Q hQ
    have htri := norm_sub_le_norm_sub_add_norm_sub (∫ p, H p ∂Q.law) (∫ p, F₁ p ∂Q.law) u
    change ‖(∫ p, H p ∂Q.law) - (∫ p, F₁ p ∂Q.law)‖ ≤ _ at h
    linarith
  have hmX : ‖(∫ p, X p ∂Q.law) - u‖ ≤ 2 * D / (widthFactor j : ℝ) + t := by
    have h := verticalColumn_x_mean hf w j hj G hQ
    have htri := norm_sub_le_norm_sub_add_norm_sub (∫ p, X p ∂Q.law) (∫ p, F₁ p ∂Q.law) u
    change ‖(∫ p, X p ∂Q.law) - (∫ p, F₁ p ∂Q.law)‖ ≤ _ at h
    linarith
  have hmY : ‖(∫ p, Y p ∂Q.law) - v‖ ≤ (2 * D + 1) * t := by
    have h := verticalColumn_y_mean hf w j hj Q hQ
    have htri := norm_sub_le_norm_sub_add_norm_sub (∫ p, Y p ∂Q.law) (∫ p, F₂ p ∂Q.law) v
    change ‖(∫ p, Y p ∂Q.law) - (∫ p, F₂ p ∂Q.law)‖ ≤ _ at h
    linarith
  have ht2 : t ^ 2 ≤ t := by nlinarith
  constructor
  · have hsecond : (∫ p, ‖H p‖ ^ 2 ∂Q.law) ≤ A := by
      have hb := integral_mono_ae (bH.norm_sq.integrable Q.law) (integrable_const A)
        ((ae_horizontal_pair hf w j hj Q hQ).mono fun p hp => hfirst _ hp)
      simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using hb
    have hvar := variance_le_of_moments (bH.integrable Q.law) (bH.norm_sq.integrable Q.law) u hsecond
    have hmprod : 2 * ‖u‖ * ‖(∫ p, H p ∂Q.law) - u‖ ≤
        2 * (2 * D) * ((2 * D + 1) * t) := by gcongr
    have hcompare := energy_sub_le_two (μ := Q.law) bF₁ bH u
    change (∫ p, ‖H p - F₁ p‖ ^ 2 ∂Q.law) ≤ horizontalCoefficient D * t
    unfold horizontalCoefficient
    nlinarith
  · have hvar := vertical_variance_bound (bX.integrable Q.law) (bX.norm_sq.integrable Q.law)
      (bY.integrable Q.law) (bY.norm_sq.integrable Q.law) (ae_vertical_pair hf w j hj Q hQ)
      hC hbarrier u v hu hv
    have hvar' : (∫ p, ‖Y p - v‖ ^ 2 ∂Q.law) ≤
        t + ε + C * (t + 4 * D * (2 * D / (widthFactor j : ℝ) + t)) +
          4 * D * ((2 * D + 1) * t) := by
      refine hvar.trans ?_
      change B - ‖v‖ ^ 2 + ε + C * (A - ‖u‖ ^ 2 + 2 * (2 * D) * ‖(∫ p, X p ∂Q.law) - u‖) +
        2 * (2 * D) * ‖(∫ p, Y p ∂Q.law) - v‖ ≤ _
      have hfour : (2 : ℝ) * (2 * D) = 4 * D := by ring
      rw [hfour]
      gcongr
    have hcompare := energy_sub_le_two (μ := Q.law) bF₂ bY v
    change (∫ p, ‖Y p - F₂ p‖ ^ 2 ∂Q.law) ≤ _
    calc
      _ ≤ 2 * (t + ε + C * (t + 4 * D * (2 * D / (widthFactor j : ℝ) + t)) +
          4 * D * ((2 * D + 1) * t)) + 2 * t := by nlinarith
      _ = _ := by unfold verticalCoefficient; ring


-- @@ L207-207 verbatim
end AnisotropicEnergy

-- @@ L208-208 verbatim
end

-- @@ L209-209 verbatim
end DoublingHilbert


-- @@ L211-211 verbatim
namespace DoublingHilbert

-- @@ L212-212 verbatim
open MeasureTheory Set Filter

-- @@ L213-213 verbatim
noncomputable section

-- @@ L214-214 verbatim
section NearMaxGrid

-- @@ L215-216 verbatim
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]


-- @@ L218-285 verbatim
omit [CompleteSpace E] in
/-- Good points near the lexicographic pair and recurrence give actual fine grid rectangles. -/
theorem exists_nearmax_grid {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (N W : ℕ) (hN : 0 < N) (hW : 0 < W)
    {A B : ℝ} (hAB : (A, B) ∈ derivativeCompact f) {t : ℝ} (ht : 0 < t) :
    ∃ (w : Tuple) (j : ℕ) (G : PeriodGrid j) (u v : E),
      colors j = N ∧ widthFactor j = W ∧ w j = 0 ∧
      G.rectangle.closed ⊆ sheetDomain w ∧
      ‖u‖ ≤ 2 * D ∧ ‖v‖ ≤ 2 * D ∧
      A - ‖u‖ ^ 2 ≤ t ∧ B - ‖v‖ ^ 2 ≤ t ∧
      (∫ p, ‖column (globalSheet hf w) (1, 0) p - u‖ ^ 2 ∂G.rectangle.law) ≤ t ^ 2 ∧
      (∫ p, ‖column (globalSheet hf w) (0, 1) p - v‖ ^ 2 ∂G.rectangle.law) ≤ t ^ 2 ∧
      scale j / G.rectangle.x.length ≤ t ∧ scale j / G.rectangle.y.length ≤ t := by
  obtain ⟨z, ⟨w, p, hp, hpz⟩, hz⟩ := Metric.mem_closure_iff.mp hAB t ht
  subst z
  let u := sheetColumn (embeddingSheet f w) (sheetDomain w) (1, 0) p
  let v := sheetColumn (embeddingSheet f w) (sheetDomain w) (0, 1) p
  have hz' : |A - ‖u‖ ^ 2| < t ∧ |B - ‖v‖ ^ 2| < t := by
    simpa only [Prod.dist_eq, Real.dist_eq, max_lt_iff, derivativePair] using hz
  have hb := derivativePair_bounds hf w p
  have hu : ‖u‖ ≤ 2 * D :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hb.2.1
  have hv : ‖v‖ ≤ 2 * D :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hb.2.2
  obtain ⟨Q, hQ, hQu, hQv⟩ := goodSheetPoint_exists_rectangle hf hp
    (show 0 < t ^ 2 / 4 by positivity)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hWR : (0 : ℝ) < W := by exact_mod_cast hW
  let δ := min (Q.x.length / (4 * N * W))
    (min (Q.y.length / (4 * N)) (min (t * Q.x.length / 2) (t * Q.y.length / 2)))
  have hxpos := Q.x.length_pos
  have hypos := Q.y.length_pos
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨j, hjN, hjW, hjw, hjδ⟩ := exists_fine_level N W hN hW w hδ
  have hr₁ : scale j < Q.x.length / (4 * N * W) := hjδ.trans_le (min_le_left _ _)
  have hr₂ : scale j < Q.y.length / (4 * N) :=
    hjδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hr₃ : scale j < t * Q.x.length / 2 :=
    hjδ.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hr₄ : scale j < t * Q.y.length / 2 :=
    hjδ.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hxperiod : xPeriod j < Q.x.length / 4 := by
    have hh := (lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * N * W)).mp hr₁
    dsimp [xPeriod, stripWidth]
    rw [hjN, hjW]
    nlinarith
  have hyperiod : yPeriod j < Q.y.length / 4 := by
    have hh := (lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * N)).mp hr₂
    dsimp [yPeriod]
    rw [hjN]
    nlinarith
  obtain ⟨G, hGQ, hGx, hGy⟩ := PeriodGrid.exists_inside Q hxperiod hyperiod
  have bu := ((bounded_baseColumn hf w (1, 0)).sub (IsBoundedField.const u)).norm_sq
  have bv := ((bounded_baseColumn hf w (0, 1)).sub (IsBoundedField.const v)).norm_sq
  have hGu := Rectangle.integral_le_four_of_subset Q G.rectangle bu
    (fun _ => sq_nonneg _) hGQ hGx hGy
  have hGv := Rectangle.integral_le_four_of_subset Q G.rectangle bv
    (fun _ => sq_nonneg _) hGQ hGx hGy
  refine ⟨w, j, G, u, v, hjN, hjW, hjw, hGQ.trans hQ, hu, hv,
    (le_abs_self _).trans hz'.1.le, (le_abs_self _).trans hz'.2.le, ?_, ?_, ?_, ?_⟩
  · change (∫ p, ‖column (globalSheet hf w) (1, 0) p - u‖ ^ 2 ∂Q.law) < t ^ 2 / 4 at hQu
    linarith
  · change (∫ p, ‖column (globalSheet hf w) (0, 1) p - v‖ ^ 2 ∂Q.law) < t ^ 2 / 4 at hQv
    linarith
  · apply (div_le_iff₀ G.rectangle.x.length_pos).mpr
    nlinarith
  · apply (div_le_iff₀ G.rectangle.y.length_pos).mpr
    nlinarith


-- @@ L287-287 verbatim
end NearMaxGrid

-- @@ L288-288 verbatim
end

-- @@ L289-289 verbatim
end DoublingHilbert


-- @@ L291-291 verbatim
namespace DoublingHilbert

-- @@ L292-292 verbatim
open MeasureTheory Set Filter

-- @@ L293-293 verbatim
noncomputable section


-- @@ L295-322 verbatim
/-- The order of choices is essential: the strip width follows the compact barrier,
then the base error and the unused radius are made small. -/
theorem exists_energy_parameters {D C η : ℝ} (hD : 0 ≤ D) (hC : 0 ≤ C) (hη : 0 < η) :
    ∃ W : ℕ, 0 < W ∧ ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      2 * (η / 8) + 16 * C * D ^ 2 / (W : ℝ) +
        ((W : ℝ) ^ 2 * horizontalCoefficient D + verticalCoefficient D C) * t < η := by
  obtain ⟨W, hW⟩ := exists_nat_gt (max 1 (64 * C * D ^ 2 / η))
  have hW1 : (1 : ℝ) < W := (le_max_left _ _).trans_lt hW
  have hWpos : 0 < W := by exact_mod_cast (lt_trans zero_lt_one hW1)
  have hWR : (0 : ℝ) < W := by exact_mod_cast hWpos
  have hbig : 64 * C * D ^ 2 / η < W := (le_max_right _ _).trans_lt hW
  have hterm : 16 * C * D ^ 2 / (W : ℝ) < η / 4 := by
    apply (div_lt_iff₀ hWR).mpr
    have hh := (div_lt_iff₀ hη).mp hbig
    nlinarith
  let K := (W : ℝ) ^ 2 * horizontalCoefficient D + verticalCoefficient D C
  have hK : 0 < K := by
    dsimp [K]
    exact add_pos_of_nonneg_of_pos (mul_nonneg (sq_nonneg _) (horizontalCoefficient_pos hD).le)
      (verticalCoefficient_pos hD hC)
  let t := min 1 (η / (4 * K))
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := min_le_left _ _
  have htK : K * t ≤ η / 4 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4 * K)).mp (min_le_right 1 (η / (4 * K)))
    change t * (4 * K) ≤ η at hh
    linarith
  exact ⟨W, hWpos, t, ht, ht1, by change 2 * (η / 8) + _ + K * t < η; linarith⟩


-- @@ L324-324 verbatim
section SmallEnergy

-- @@ L325-326 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]


-- @@ L328-362 verbatim
/-- The full analytic output: arbitrarily small combined energy on actual sheets
of the single fixed Hilbert set, at a level with any prescribed number of colors. -/
theorem exists_small_energy_grid {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (N : ℕ) (hN : 0 < N) {η : ℝ} (hη : 0 < η) :
    ∃ (w : Tuple) (j : ℕ) (G : PeriodGrid j), colors j = N ∧ w j = 0 ∧
      G.rectangle.closed ⊆ sheetDomain w ∧
      (∫ p, combinedEnergy hf w j p ∂G.rectangle.law) < η := by
  obtain ⟨A, B, hAB, hfirst, hsecond⟩ := exists_lexicographic_maximum
    (isCompact_derivativeCompact hf) (derivativeCompact_nonempty hf)
  have hb := derivativeCompact_subset hf hAB
  obtain ⟨C, hC, hbarrier⟩ := lexicographic_affine_barrier (isCompact_derivativeCompact hf)
    hfirst hsecond (fun z hz => (derivativeCompact_subset hf hz).2.2) hb.1.2
    (sq_nonneg (2 * (D : ℝ))) (show 0 < η / 8 by positivity)
  obtain ⟨W, hW, t, ht, ht1, hparam⟩ := exists_energy_parameters D.coe_nonneg hC hη
  obtain ⟨w, j, G, u, v, hjN, hjW, hjw, hQ, hu, hv, hnu, hnv, hbu, hbv, hrx, hry⟩ :=
    exists_nearmax_grid hf N W hN hW hAB ht
  obtain ⟨hH, hV⟩ := anisotropic_energy_bound hf w j hjw G hQ hC ht.le ht1
    hfirst hbarrier u v hu hv hnu hnv hbu hbv hrx hry
  rw [hjW] at hV
  have hH' := mul_le_mul_of_nonneg_left hH (sq_nonneg (W : ℝ))
  have bH := bounded_horizontalEnergy hf w j
  have bV := bounded_verticalEnergy hf w j
  refine ⟨w, j, G, hjN, hjw, hQ, ?_⟩
  calc
    (∫ p, combinedEnergy hf w j p ∂G.rectangle.law) =
        (W : ℝ) ^ 2 * (∫ p, horizontalEnergy hf w j p ∂G.rectangle.law) +
          (∫ p, verticalEnergy hf w j p ∂G.rectangle.law) := by
      unfold combinedEnergy
      rw [integral_add ((bH.const_mul _).integrable _) (bV.integrable _), integral_const_mul, hjW]
    _ ≤ (W : ℝ) ^ 2 * (horizontalCoefficient D * t) +
        (2 * (η / 8) + 16 * C * (D : ℝ) ^ 2 / (W : ℝ) + verticalCoefficient D C * t) :=
      add_le_add hH' hV
    _ = 2 * (η / 8) + 16 * C * (D : ℝ) ^ 2 / (W : ℝ) +
        ((W : ℝ) ^ 2 * horizontalCoefficient D + verticalCoefficient D C) * t := by ring
    _ < η := hparam


-- @@ L364-364 verbatim
end SmallEnergy

-- @@ L365-365 verbatim
end

-- @@ L366-366 verbatim
end DoublingHilbert


-- @@ L368-368 verbatim
end OAI
