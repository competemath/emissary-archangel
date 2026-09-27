/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.Scaling
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import LeanPool.NavierStokesAndEuler.NavierStokes.SlotGeometry
public import Mathlib.Analysis.SpecialFunctions.Pow.Real


-- @@ L13-20 verbatim
/-!
# The actual native chart scales

The floor index is the one defined from the manuscript's logarithmic formula
in `SlotColoring`. This module derives the coefficient comparisons in (25),
their reciprocal bounds, the rounded carrier scale, and polynomial/exponential
decay along the actual dyadic sequence.
-/


-- @@ L22-22 verbatim
section


-- @@ L24-32 verbatim
/-!
# Physical grid labels, bounded degree, and an explicit finite coloring

Labels consist of a dyadic level, three integer grid coordinates, and a sign.
The physical mesh at exponent `a` is `2^(-n*a)/n^6`, namely the mesh
`S_n^-3` with `S_n=n²`, rescaled by `Q_n^a` with `Q_n=2^-n`.
Closed boxes of two mesh widths include the fixed small enlargement of the
one-mesh supports in the manuscript.
-/


-- @@ L34-34 verbatim
@[expose] public section


-- @@ L36-36 verbatim
noncomputable section


-- @@ L38-38 verbatim
namespace NavierStokes.SlotColoring


-- @@ L40-40 verbatim
open Set

-- @@ L41-41 verbatim
open scoped BigOperators


-- @@ L43-44 verbatim
/-- Grid: an abbreviation for `Fin 3 → ℤ`. -/
abbrev Grid := Fin 3 → ℤ

-- @@ L45-46 verbatim
/-- Position: an abbreviation for `Fin 3 → ℝ`. -/
abbrev Position := Fin 3 → ℝ

-- @@ L47-48 verbatim
/-- Label: an abbreviation for `ℕ × (Grid × Bool)`. -/
abbrev Label := ℕ × (Grid × Bool)


-- @@ L50-51 verbatim
/-- Dyadic Q, given by `(2 : ℝ) ^ (-(n : ℝ))`. -/
def dyadicQ (n : ℕ) : ℝ := (2 : ℝ) ^ (-(n : ℝ))


-- @@ L53-54 verbatim
/-- Spacing, given by `(2 : ℝ) ^ (-(n : ℝ) * a) / (n : ℝ) ^ 6`. -/
def spacing (a : ℝ) (n : ℕ) : ℝ := (2 : ℝ) ^ (-(n : ℝ) * a) / (n : ℝ) ^ 6


-- @@ L56-62 verbatim
theorem spacing_eq_scaled_mesh (a : ℝ) (n : ℕ) :
    spacing a n = dyadicQ n ^ a * (1 / (((n : ℝ) ^ 2) ^ 3)) := by
  unfold spacing dyadicQ
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [← pow_mul]
  norm_num
  ring


-- @@ L64-66 verbatim
theorem spacing_pos (a : ℝ) {n : ℕ} (hn : 1 ≤ n) : 0 < spacing a n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  exact div_pos (Real.rpow_pos_of_pos (by norm_num) _) (pow_pos hn' _)


-- @@ L68-82 verbatim
theorem spacing_ratio (a : ℝ) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    spacing a n / spacing a m =
      ((m : ℝ) / (n : ℝ)) ^ 6 * (2 : ℝ) ^ (((m : ℝ) - (n : ℝ)) * a) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have he : (2 : ℝ) ^ (-(m : ℝ) * a) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  have hp : (2 : ℝ) ^ (((m : ℝ) - (n : ℝ)) * a) =
      (2 : ℝ) ^ (-(n : ℝ) * a) / (2 : ℝ) ^ (-(m : ℝ) * a) := by
    rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [hp]
  unfold spacing
  rw [div_pow]
  field_simp


-- @@ L84-108 verbatim
/-- The mesh ratio is uniform across levels at distance at most four. -/
theorem spacing_ratio_le (a A : ℝ) {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n ≤ m + 4) (hmn : m ≤ n + 4)
    (ha : |a| ≤ A) :
    spacing a n / spacing a m ≤ (5 : ℝ) ^ 6 * (2 : ℝ) ^ (4 * A) := by
  rw [spacing_ratio a hn hm]
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hm5 : (m : ℝ) ≤ 5 * (n : ℝ) := by exact_mod_cast (by omega : m ≤ 5 * n)
  have hquot : (m : ℝ) / (n : ℝ) ≤ 5 := (div_le_iff₀ hn').mpr hm5
  have hpow : ((m : ℝ) / (n : ℝ)) ^ 6 ≤ (5 : ℝ) ^ 6 :=
    pow_le_pow_left₀ (div_nonneg hm0 hn'.le) hquot 6
  have hdiff : |(m : ℝ) - (n : ℝ)| ≤ 4 := by
    have h1 : (n : ℝ) ≤ (m : ℝ) + 4 := by exact_mod_cast hnm
    have h2 : (m : ℝ) ≤ (n : ℝ) + 4 := by exact_mod_cast hmn
    rw [abs_le]
    constructor <;> linarith
  have hexp : ((m : ℝ) - (n : ℝ)) * a ≤ 4 * A := by
    calc
      ((m : ℝ) - (n : ℝ)) * a ≤ |((m : ℝ) - (n : ℝ)) * a| := le_abs_self _
      _ = |(m : ℝ) - (n : ℝ)| * |a| := abs_mul _ _
      _ ≤ 4 * |a| := mul_le_mul_of_nonneg_right hdiff (abs_nonneg a)
      _ ≤ 4 * A := mul_le_mul_of_nonneg_left ha (by norm_num)
  exact mul_le_mul hpow (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)
    (Real.rpow_nonneg (by norm_num) _) (by positivity)


-- @@ L110-111 verbatim
/-- Axis exponent, given by `![1 / 2, D, 1]`. -/
def axisExponent (D : ℝ) : Fin 3 → ℝ := ![1 / 2, D, 1]

-- @@ L112-113 verbatim
/-- Width, given by `spacing (axisExponent D j) n`. -/
def width (D : ℝ) (j : Fin 3) (n : ℕ) : ℝ := spacing (axisExponent D j) n

-- @@ L114-115 verbatim
/-- Ratio bound, given by `(5 : ℝ) ^ 6 * (2 : ℝ) ^ (4 * (1 + |D|))`. -/
def ratioBound (D : ℝ) : ℝ := (5 : ℝ) ^ 6 * (2 : ℝ) ^ (4 * (1 + |D|))


-- @@ L117-118 verbatim
theorem width_pos (D : ℝ) (j : Fin 3) {n : ℕ} (hn : 1 ≤ n) : 0 < width D j n :=
  spacing_pos _ hn


-- @@ L120-132 verbatim
theorem width_ratio_le (D : ℝ) (j : Fin 3) {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n ≤ m + 4) (hmn : m ≤ n + 4) :
    width D j n / width D j m ≤ ratioBound D := by
  apply spacing_ratio_le _ _ hn hm hnm hmn
  fin_cases j
  · change |(1 / 2 : ℝ)| ≤ 1 + |D|
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    linarith [abs_nonneg D]
  · change |D| ≤ 1 + |D|
    linarith
  · change |(1 : ℝ)| ≤ 1 + |D|
    rw [abs_one]
    linarith [abs_nonneg D]


-- @@ L134-137 verbatim
/-- Physical box, given by `{x | ∀ j, |x j - width D j L.1 * (L.2.1 j : ℝ)| ≤ 2 * width D j
L.1}`. -/
def physicalBox (D : ℝ) (L : Label) : Set Position :=
  {x | ∀ j, |x j - width D j L.1 * (L.2.1 j : ℝ)| ≤ 2 * width D j L.1}


-- @@ L139-146 verbatim
/-- The exact enlarged-box interaction relation used for coloring. -/
structure Adj (D : ℝ) (L M : Label) : Prop where
  left_positive : 1 ≤ L.1
  right_positive : 1 ≤ M.1
  distinct : L ≠ M
  left_level_le : L.1 ≤ M.1 + 4
  right_level_le : M.1 ≤ L.1 + 4
  overlap : (physicalBox D L ∩ physicalBox D M).Nonempty


-- @@ L148-156 verbatim
theorem overlapping_centers (D : ℝ) (L M : Label)
    (hov : (physicalBox D L ∩ physicalBox D M).Nonempty) (j : Fin 3) :
    |width D j L.1 * (L.2.1 j : ℝ) - width D j M.1 * (M.2.1 j : ℝ)| ≤
      2 * (width D j L.1 + width D j M.1) := by
  obtain ⟨x, hx, hy⟩ := hov
  have htriangle := abs_sub_le (width D j L.1 * (L.2.1 j : ℝ)) (x j)
    (width D j M.1 * (M.2.1 j : ℝ))
  rw [abs_sub_comm (width D j L.1 * (L.2.1 j : ℝ)) (x j)] at htriangle
  linarith [hx j, hy j]


-- @@ L158-165 verbatim
theorem same_level_grid_gap (D : ℝ) (L M : Label) (hn : 1 ≤ L.1)
    (hl : L.1 = M.1) (hov : (physicalBox D L ∩ physicalBox D M).Nonempty) (j : Fin 3) :
    |L.2.1 j - M.2.1 j| ≤ (4 : ℤ) := by
  have h := overlapping_centers D L M hov j
  rw [← hl, ← mul_sub, abs_mul, abs_of_pos (width_pos D j hn)] at h
  have hr : |(L.2.1 j : ℝ) - (M.2.1 j : ℝ)| ≤ 4 := by
    nlinarith [width_pos D j hn]
  exact_mod_cast hr


-- @@ L167-172 verbatim
/-- Int color as an element of `Fin 5`. -/
def intColor (z : ℤ) : Fin 5 :=
  ⟨(z % 5).toNat, by
    have h0 := Int.emod_nonneg z (by norm_num : (5 : ℤ) ≠ 0)
    have h1 := Int.emod_lt_of_pos z (by norm_num : (0 : ℤ) < 5)
    omega⟩


-- @@ L174-181 verbatim
theorem intColor_eq_of_close {z w : ℤ} (hc : intColor z = intColor w)
    (hd : |z - w| ≤ 4) : z = w := by
  have hv := congrArg Fin.val hc
  dsimp [intColor] at hv
  have hz0 := Int.emod_nonneg z (by norm_num : (5 : ℤ) ≠ 0)
  have hw0 := Int.emod_nonneg w (by norm_num : (5 : ℤ) ≠ 0)
  have hdiff := abs_le.mp hd
  omega


-- @@ L183-184 verbatim
/-- Palette: an abbreviation for `Fin 9 × ((Fin 3 → Fin 5) × Bool)`. -/
abbrev Palette := Fin 9 × ((Fin 3 → Fin 5) × Bool)


-- @@ L186-189 verbatim
/-- Color data, given by `(⟨L.1 % 9, Nat.mod_lt _ (by norm_num)⟩, (fun j => intColor (L.2.1 j),
L.2.2))`. -/
def colorData (L : Label) : Palette :=
  (⟨L.1 % 9, Nat.mod_lt _ (by norm_num)⟩, (fun j => intColor (L.2.1 j), L.2.2))


-- @@ L191-192 verbatim
theorem palette_card : Fintype.card Palette = 2250 := by
  norm_num [Palette, Fintype.card_prod, Fintype.card_fun]


-- @@ L194-209 verbatim
/-- This is a constructed coloring, not a coloring hypothesis. -/
theorem colorData_proper (D : ℝ) {L M : Label} (h : Adj D L M) : colorData L ≠ colorData M := by
  intro hc
  have hlevel := congrArg (fun c : Palette => c.1.val) hc
  change L.1 % 9 = M.1 % 9 at hlevel
  have hl : L.1 = M.1 := by
    have h1 := h.left_level_le
    have h2 := h.right_level_le
    omega
  have hg : L.2.1 = M.2.1 := by
    funext j
    apply intColor_eq_of_close
    · exact congrArg (fun c : Palette => c.2.1 j) hc
    · exact same_level_grid_gap D L M h.left_positive hl h.overlap j
  have hs : L.2.2 = M.2.2 := congrArg (fun c : Palette => c.2.2) hc
  exact h.distinct (Prod.ext hl (Prod.ext hg hs))


-- @@ L211-212 verbatim
/-- Color, given by `(Fintype.equivFin Palette) (colorData L)`. -/
def color (L : Label) : Fin (Fintype.card Palette) := (Fintype.equivFin Palette) (colorData L)


-- @@ L214-216 verbatim
theorem color_proper (D : ℝ) {L M : Label} (h : Adj D L M) : color L ≠ color M := by
  intro hc
  exact colorData_proper D h ((Fintype.equivFin Palette).injective hc)


-- @@ L218-231 verbatim
/-- A reusable one-dimensional bound: overlapping intervals force the finer
grid index to lie within a fixed distance of the rescaled reference index. -/
theorem normalized_index_gap (h h' B : ℝ) (i j : ℤ) (hh' : 0 < h')
    (hratio : h / h' ≤ B)
    (hgap : |h * (i : ℝ) - h' * (j : ℝ)| ≤ 2 * (h + h')) :
    |h / h' * (i : ℝ) - (j : ℝ)| ≤ 2 * (B + 1) := by
  calc
    |h / h' * (i : ℝ) - (j : ℝ)| = |(h * (i : ℝ) - h' * (j : ℝ)) / h'| := by
      congr 1
      field_simp
    _ = |h * (i : ℝ) - h' * (j : ℝ)| / h' := by rw [abs_div, abs_of_pos hh']
    _ ≤ (2 * (h + h')) / h' := div_le_div_of_nonneg_right hgap hh'.le
    _ = 2 * (h / h' + 1) := by field_simp
    _ ≤ 2 * (B + 1) := by linarith


-- @@ L233-242 verbatim
theorem index_near_floor (c A : ℝ) (j : ℤ) (K : ℕ)
    (hgap : |c - (j : ℝ)| ≤ A) (hK : A + 1 ≤ (K : ℝ)) :
    |j - ⌊c⌋| ≤ (K : ℤ) := by
  have hfloor : |c - (⌊c⌋ : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (Int.floor_le c))]
    linarith [Int.lt_floor_add_one c]
  have ht := abs_sub_le (j : ℝ) c (⌊c⌋ : ℝ)
  rw [abs_sub_comm (j : ℝ) c] at ht
  have hreal : |(j : ℝ) - (⌊c⌋ : ℝ)| ≤ (K : ℝ) := by linarith
  exact_mod_cast hreal


-- @@ L244-245 verbatim
/-- Index radius, given by `⌈2 * (ratioBound D + 1) + 1⌉₊`. -/
def indexRadius (D : ℝ) : ℕ := ⌈2 * (ratioBound D + 1) + 1⌉₊


-- @@ L247-249 verbatim
/-- Index center, given by `⌊width D j L.1 / width D j m * (L.2.1 j : ℝ)⌋`. -/
def indexCenter (D : ℝ) (L : Label) (m : ℕ) (j : Fin 3) : ℤ :=
  ⌊width D j L.1 / width D j m * (L.2.1 j : ℝ)⌋


-- @@ L251-255 verbatim
/-- Candidate grids, given by `Fintype.piFinset (fun j => Finset.Icc (indexCenter D L m j -
(indexRadius D : ℤ)) (indexCenter D L m j + (indexRadius D : ℤ)))`. -/
def candidateGrids (D : ℝ) (L : Label) (m : ℕ) : Finset Grid :=
  Fintype.piFinset (fun j => Finset.Icc (indexCenter D L m j - (indexRadius D : ℤ))
    (indexCenter D L m j + (indexRadius D : ℤ)))


-- @@ L257-260 verbatim
/-- Candidates at level, given by `((candidateGrids D L m).product (Finset.univ : Finset
Bool)).image (fun gs => (m, gs))`. -/
def candidatesAtLevel (D : ℝ) (L : Label) (m : ℕ) : Finset Label :=
  ((candidateGrids D L m).product (Finset.univ : Finset Bool)).image (fun gs => (m, gs))


-- @@ L262-264 verbatim
/-- Candidates, given by `(Finset.Icc (L.1 - 4) (L.1 + 4)).biUnion (candidatesAtLevel D L)`. -/
def candidates (D : ℝ) (L : Label) : Finset Label :=
  (Finset.Icc (L.1 - 4) (L.1 + 4)).biUnion (candidatesAtLevel D L)


-- @@ L266-272 verbatim
theorem adj_index_bound (D : ℝ) {L M : Label} (h : Adj D L M) (j : Fin 3) :
    |M.2.1 j - indexCenter D L M.1 j| ≤ (indexRadius D : ℤ) := by
  apply index_near_floor
  · exact normalized_index_gap _ _ _ _ _ (width_pos D j h.right_positive)
      (width_ratio_le D j h.left_positive h.right_positive h.left_level_le h.right_level_le)
      (overlapping_centers D L M h.overlap j)
  · exact Nat.le_ceil _


-- @@ L274-289 verbatim
theorem adj_mem_candidates (D : ℝ) {L M : Label} (h : Adj D L M) : M ∈ candidates D L := by
  apply Finset.mem_biUnion.mpr
  refine ⟨M.1, ?_, ?_⟩
  · simp only [Finset.mem_Icc]
    have h1 := h.left_level_le
    have h2 := h.right_level_le
    omega
  · apply Finset.mem_image.mpr
    refine ⟨M.2, ?_, rfl⟩
    apply Finset.mem_product.mpr
    refine ⟨?_, Finset.mem_univ _⟩
    apply Fintype.mem_piFinset.mpr
    intro j
    have hj := abs_le.mp (adj_index_bound D h j)
    simp only [Finset.mem_Icc]
    omega


-- @@ L291-294 verbatim
theorem integer_interval_card (c : ℤ) (K : ℕ) :
    (Finset.Icc (c - (K : ℤ)) (c + (K : ℤ))).card = 2 * K + 1 := by
  rw [Int.card_Icc]
  omega


-- @@ L296-300 verbatim
theorem candidateGrids_card (D : ℝ) (L : Label) (m : ℕ) :
    (candidateGrids D L m).card = (2 * indexRadius D + 1) ^ 3 := by
  unfold candidateGrids
  rw [Fintype.card_piFinset]
  simp only [integer_interval_card, Finset.prod_const, Finset.card_univ, Fintype.card_fin]


-- @@ L302-310 verbatim
theorem candidatesAtLevel_card_le (D : ℝ) (L : Label) (m : ℕ) :
    (candidatesAtLevel D L m).card ≤ (2 * indexRadius D + 1) ^ 3 * 2 := by
  calc
    (candidatesAtLevel D L m).card ≤
        ((candidateGrids D L m).product (Finset.univ : Finset Bool)).card := Finset.card_image_le
    _ = (2 * indexRadius D + 1) ^ 3 * 2 := by
      change ((candidateGrids D L m) ×ˢ (Finset.univ : Finset Bool)).card = _
      simpa only [candidateGrids_card, Finset.card_univ, Fintype.card_bool] using
        Finset.card_product (candidateGrids D L m) (Finset.univ : Finset Bool)


-- @@ L312-313 verbatim
/-- Degree bound, given by `18 * (2 * indexRadius D + 1) ^ 3`. -/
def degreeBound (D : ℝ) : ℕ := 18 * (2 * indexRadius D + 1) ^ 3


-- @@ L315-328 verbatim
theorem candidates_card_le (D : ℝ) (L : Label) :
    (candidates D L).card ≤ degreeBound D := by
  have hlevels : (Finset.Icc (L.1 - 4) (L.1 + 4)).card ≤ 9 := by
    rw [Nat.card_Icc]
    omega
  calc
    (candidates D L).card ≤
        ∑ m ∈ Finset.Icc (L.1 - 4) (L.1 + 4), (candidatesAtLevel D L m).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _m ∈ Finset.Icc (L.1 - 4) (L.1 + 4), (2 * indexRadius D + 1) ^ 3 * 2 :=
      Finset.sum_le_sum (fun m _ => candidatesAtLevel_card_le D L m)
    _ = (Finset.Icc (L.1 - 4) (L.1 + 4)).card * ((2 * indexRadius D + 1) ^ 3 * 2) := by simp
    _ ≤ 9 * ((2 * indexRadius D + 1) ^ 3 * 2) := Nat.mul_le_mul_right _ hlevels
    _ = degreeBound D := by unfold degreeBound; ring


-- @@ L330-333 verbatim
/-- The actual finite neighbor set, obtained by filtering an explicit finite box. -/
def neighbors (D : ℝ) (L : Label) : Finset Label := by
  classical
  exact (candidates D L).filter (Adj D L)


-- @@ L335-338 verbatim
theorem mem_neighbors_iff (D : ℝ) (L M : Label) : M ∈ neighbors D L ↔ Adj D L M := by
  classical
  simp only [neighbors, Finset.mem_filter]
  exact ⟨And.right, fun h => ⟨adj_mem_candidates D h, h⟩⟩


-- @@ L340-343 verbatim
/-- Uniform degree control for every dyadic level, grid point, and sign. -/
theorem neighbors_card_le (D : ℝ) (L : Label) : (neighbors D L).card ≤ degreeBound D := by
  classical
  exact (Finset.card_filter_le _ _).trans (candidates_card_le D L)


-- @@ L345-345 verbatim
theorem label_type_countable : Countable Label := by infer_instance


-- @@ L347-348 verbatim
/-- The expanding eigenvalue of the actual covering matrix. -/
def coverGrowth : ℝ := 4 + Real.sqrt 2


-- @@ L350-353 verbatim
theorem log_coverGrowth_pos : 0 < Real.log coverGrowth := by
  apply Real.log_pos
  unfold coverGrowth
  linarith [Real.sqrt_nonneg (2 : ℝ)]


-- @@ L355-357 verbatim
/-- The real expression whose floor defines the manuscript's native index. -/
def nativeArgument (h : ℝ) (n : ℕ) : ℝ :=
  Real.log (dyadicQ n ^ (-1 - h) / (n : ℝ) ^ 2) / Real.log coverGrowth


-- @@ L359-360 verbatim
/-- Native index, given by `⌊nativeArgument h n⌋₊`. -/
def nativeIndex (h : ℝ) (n : ℕ) : ℕ := ⌊nativeArgument h n⌋₊


-- @@ L362-373 verbatim
theorem nativeArgument_expanded (h : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    nativeArgument h n =
      ((n : ℝ) * (1 + h) * Real.log 2 - 2 * Real.log (n : ℝ)) / Real.log coverGrowth := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hq : 0 < dyadicQ n := Real.rpow_pos_of_pos (by norm_num) _
  unfold nativeArgument
  rw [Real.log_div (ne_of_gt (Real.rpow_pos_of_pos hq _)) (pow_ne_zero 2 hn'),
    Real.log_rpow hq, Real.log_pow]
  unfold dyadicQ
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  norm_num
  ring


-- @@ L375-378 verbatim
/-- Native gap budget, given by `(4 * (1 + h) * Real.log 2 + 2 * Real.log 5) / Real.log
coverGrowth`. -/
def nativeGapBudget (h : ℝ) : ℝ :=
  (4 * (1 + h) * Real.log 2 + 2 * Real.log 5) / Real.log coverGrowth


-- @@ L380-381 verbatim
/-- Native gap, given by `⌈nativeGapBudget h⌉₊ + 1`. -/
def nativeGap (h : ℝ) : ℕ := ⌈nativeGapBudget h⌉₊ + 1


-- @@ L383-395 verbatim
theorem log_level_gap {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hnm : n ≤ m + 4) (hmn : m ≤ n + 4) :
    |Real.log (n : ℝ) - Real.log (m : ℝ)| ≤ Real.log 5 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hm' : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hn5 : (n : ℝ) ≤ 5 * (m : ℝ) := by exact_mod_cast (by omega : n ≤ 5 * m)
  have hm5 : (m : ℝ) ≤ 5 * (n : ℝ) := by exact_mod_cast (by omega : m ≤ 5 * n)
  have h1 := Real.log_le_log hn' hn5
  have h2 := Real.log_le_log hm' hm5
  rw [Real.log_mul (by norm_num : (5 : ℝ) ≠ 0) (ne_of_gt hm')] at h1
  rw [Real.log_mul (by norm_num : (5 : ℝ) ≠ 0) (ne_of_gt hn')] at h2
  rw [abs_le]
  constructor <;> linarith


-- @@ L397-432 verbatim
theorem nativeArgument_gap (h : ℝ) (hh : 0 ≤ h) {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n ≤ m + 4) (hmn : m ≤ n + 4) :
    |nativeArgument h n - nativeArgument h m| ≤ nativeGapBudget h := by
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := (Real.log_pos (by norm_num)).le
  have h1h : 0 ≤ 1 + h := by linarith
  have hdiff : |(n : ℝ) - (m : ℝ)| ≤ 4 := by
    have hn' : (n : ℝ) ≤ (m : ℝ) + 4 := by exact_mod_cast hnm
    have hm' : (m : ℝ) ≤ (n : ℝ) + 4 := by exact_mod_cast hmn
    rw [abs_le]
    constructor <;> linarith
  have hlogs := log_level_gap hn hm hnm hmn
  have hnum :
      |((n : ℝ) - (m : ℝ)) * (1 + h) * Real.log 2 -
        2 * (Real.log (n : ℝ) - Real.log (m : ℝ))| ≤
      4 * (1 + h) * Real.log 2 + 2 * Real.log 5 := by
    calc
      _ ≤ |((n : ℝ) - (m : ℝ)) * (1 + h) * Real.log 2| +
          |2 * (Real.log (n : ℝ) - Real.log (m : ℝ))| := abs_sub _ _
      _ = |(n : ℝ) - (m : ℝ)| * (1 + h) * Real.log 2 +
          2 * |Real.log (n : ℝ) - Real.log (m : ℝ)| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hlog2, abs_of_nonneg h1h,
              abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdiff h1h) hlog2)
        (mul_le_mul_of_nonneg_left hlogs (by norm_num))
  calc
    |nativeArgument h n - nativeArgument h m| =
        |(((n : ℝ) - (m : ℝ)) * (1 + h) * Real.log 2 -
          2 * (Real.log (n : ℝ) - Real.log (m : ℝ))) / Real.log coverGrowth| := by
            rw [nativeArgument_expanded h hn, nativeArgument_expanded h hm]
            congr 1
            ring
    _ = |((n : ℝ) - (m : ℝ)) * (1 + h) * Real.log 2 -
        2 * (Real.log (n : ℝ) - Real.log (m : ℝ))| / Real.log coverGrowth := by
          rw [abs_div, abs_of_pos log_coverGrowth_pos]
    _ ≤ nativeGapBudget h := div_le_div_of_nonneg_right hnum log_coverGrowth_pos.le


-- @@ L434-438 verbatim
theorem natFloor_gap_le (u v C : ℝ) (h : u - v ≤ C) :
    ⌊u⌋₊ ≤ ⌊v⌋₊ + (⌈C⌉₊ + 1) := by
  apply Nat.floor_le_of_le
  push_cast
  linarith [Nat.lt_floor_add_one v, Nat.le_ceil C]


-- @@ L440-448 verbatim
/-- The actual adjacent native indices have an explicit uniform gap. -/
theorem nativeIndex_gap (h : ℝ) (hh : 0 ≤ h) {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n ≤ m + 4) (hmn : m ≤ n + 4) :
    nativeIndex h n ≤ nativeIndex h m + nativeGap h ∧
      nativeIndex h m ≤ nativeIndex h n + nativeGap h := by
  have hg := abs_le.mp (nativeArgument_gap h hh hn hm hnm hmn)
  constructor
  · exact natFloor_gap_le _ _ _ hg.2
  · exact natFloor_gap_le _ _ _ (by linarith [hg.1])


-- @@ L450-458 verbatim
theorem nat_square_le_two_pow {n : ℕ} (hn : 4 ≤ n) : n ^ 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have hmul := Nat.mul_le_mul_right n hn
      calc
        (n + 1) ^ 2 ≤ 2 * n ^ 2 := by nlinarith
        _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 1) := by rw [pow_succ]; ring


-- @@ L460-477 verbatim
/-- `n=4` is already a valid uniform threshold for nonnegative native indices
when `h≥0`; the manuscript subsequently retains still larger bands. -/
theorem nativeArgument_nonneg (h : ℝ) (hh : 0 ≤ h) {n : ℕ} (hn : 4 ≤ n) :
    0 ≤ nativeArgument h n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hsquare : (n : ℝ) ^ 2 ≤ (2 : ℝ) ^ n := by exact_mod_cast nat_square_le_two_pow hn
  have hq : (n : ℝ) ^ 2 ≤ dyadicQ n ^ (-1 - h) := by
    unfold dyadicQ
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      (n : ℝ) ^ 2 ≤ (2 : ℝ) ^ n := hsquare
      _ = (2 : ℝ) ^ (n : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ (2 : ℝ) ^ (-(n : ℝ) * (-1 - h)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
  have hratio : 1 ≤ dyadicQ n ^ (-1 - h) / (n : ℝ) ^ 2 := by
    apply (le_div_iff₀ (pow_pos hn' 2)).mpr
    simpa using hq
  exact div_nonneg (Real.log_nonneg hratio) log_coverGrowth_pos.le


-- @@ L479-482 verbatim
theorem nativeIndex_eq_integer_floor (h : ℝ) (hh : 0 ≤ h) {n : ℕ} (hn : 4 ≤ n) :
    (nativeIndex h n : ℤ) = ⌊nativeArgument h n⌋ := by
  unfold nativeIndex
  rw [← Int.floor_toNat, Int.toNat_of_nonneg (Int.floor_nonneg.mpr (nativeArgument_nonneg h hh hn))]


-- @@ L484-503 verbatim
/-- The constructed finite coloring feeds the proved rational-slot geometry
using the manuscript's actual native covering index, with no coloring or
native-index-gap assumption. -/
theorem physical_labels_have_auxiliary_slots (D h : ℝ) (hh : 0 ≤ h)
    (a b : SlotGeometry.Plane) :
    ∃ r : ℝ, 0 < r ∧ ∀ L M : Label, Adj D L M →
      Disjoint
        (SlotGeometry.liftedSupport (nativeIndex h L.1)
          (SlotGeometry.orientedRectangle
            (SlotGeometry.center (Fintype.card Palette) (nativeGap h) (color L)) a b (2 * r)))
        (SlotGeometry.liftedSupport (nativeIndex h M.1)
          (SlotGeometry.orientedRectangle
            (SlotGeometry.center (Fintype.card Palette) (nativeGap h) (color M)) a b (2 * r))) := by
  apply SlotGeometry.colored_labels_have_slots
    (Fintype.card Palette) (nativeGap h) a b (Adj D) color (fun L => nativeIndex h L.1)
  · intro L M hLM
    exact color_proper D hLM
  · intro L M hLM
    exact nativeIndex_gap h hh hLM.left_positive hLM.right_positive
      hLM.left_level_le hLM.right_level_le


-- @@ L505-505 verbatim
end NavierStokes.SlotColoring


-- @@ L507-507 verbatim
end

-- @@ L508-508 verbatim
end


-- @@ L510-510 verbatim
end


-- @@ L512-512 verbatim
@[expose] public section


-- @@ L514-514 verbatim
noncomputable section


-- @@ L516-516 verbatim
namespace NavierStokes.ChartScales


-- @@ L518-518 verbatim
open Filter

-- @@ L519-519 verbatim
open scoped Topology


-- @@ L521-522 verbatim
/-- Tg: an abbreviation for `SlotColoring.coverGrowth`. -/
abbrev Tg : ℝ := SlotColoring.coverGrowth

-- @@ L523-524 verbatim
/-- Lambda, given by `4 - Real.sqrt 2`. -/
def Lambda : ℝ := 4 - Real.sqrt 2

-- @@ L525-526 verbatim
/-- Rho, given by `Real.log Lambda / Real.log Tg`. -/
def rho : ℝ := Real.log Lambda / Real.log Tg

-- @@ L527-528 verbatim
/-- Kappa, given by `1 / 100000`. -/
def kappa : ℝ := 1 / 100000

-- @@ L529-530 verbatim
/-- Radial exponent, given by `2 * ((1 + h) * rho - h * kappa)`. -/
def radialExponent (h : ℝ) : ℝ := 2 * ((1 + h) * rho - h * kappa)


-- @@ L532-533 verbatim
/-- Q: an abbreviation for `SlotColoring.dyadicQ n`. -/
abbrev Q (n : ℕ) : ℝ := SlotColoring.dyadicQ n

-- @@ L534-535 verbatim
/-- S, given by `(n : ℝ) ^ 2`. -/
def S (n : ℕ) : ℝ := (n : ℝ) ^ 2

-- @@ L536-537 verbatim
/-- Epsilon, given by `Q n ^ h`. -/
def epsilon (h : ℝ) (n : ℕ) : ℝ := Q n ^ h

-- @@ L538-539 verbatim
/-- Native index: an abbreviation for `SlotColoring.nativeIndex h n`. -/
abbrev nativeIndex (h : ℝ) (n : ℕ) : ℕ := SlotColoring.nativeIndex h n


-- @@ L541-542 verbatim
/-- Time coefficient, given by `Tg ^ nativeIndex h n * Q n ^ (1 + h)`. -/
def timeCoefficient (h : ℝ) (n : ℕ) : ℝ := Tg ^ nativeIndex h n * Q n ^ (1 + h)

-- @@ L543-545 verbatim
/-- Radial coefficient, given by `Lambda ^ nativeIndex h n * Q n ^ (radialExponent h / 2)`. -/
def radialCoefficient (h : ℝ) (n : ℕ) : ℝ :=
  Lambda ^ nativeIndex h n * Q n ^ (radialExponent h / 2)


-- @@ L547-548 verbatim
theorem sqrt_two_lt_two : Real.sqrt (2 : ℝ) < 2 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]


-- @@ L550-552 verbatim
theorem Tg_one_lt : 1 < Tg := by
  unfold Tg SlotColoring.coverGrowth
  linarith [Real.sqrt_nonneg (2 : ℝ)]


-- @@ L554-554 verbatim
theorem Tg_pos : 0 < Tg := lt_trans zero_lt_one Tg_one_lt

-- @@ L555-555 verbatim
theorem log_Tg_pos : 0 < Real.log Tg := SlotColoring.log_coverGrowth_pos


-- @@ L557-559 verbatim
theorem Lambda_two_lt : 2 < Lambda := by
  unfold Lambda
  linarith [sqrt_two_lt_two]


-- @@ L561-561 verbatim
theorem Lambda_pos : 0 < Lambda := lt_trans (by norm_num) Lambda_two_lt

-- @@ L562-562 verbatim
theorem log_Lambda_pos : 0 < Real.log Lambda := Real.log_pos (by linarith [Lambda_two_lt])


-- @@ L564-576 verbatim
/-- A coarse explicit bound suffices to show that the radial power is positive. -/
theorem rho_lower : (1 / 3 : ℝ) ≤ rho := by
  have hl : Real.log (2 : ℝ) ≤ Real.log Lambda := Real.log_le_log (by norm_num) Lambda_two_lt.le
  have ht : Tg ≤ (2 : ℝ) ^ 3 := by
    unfold Tg SlotColoring.coverGrowth
    norm_num
    linarith [sqrt_two_lt_two]
  have htlog := Real.log_le_log Tg_pos ht
  rw [Real.log_pow] at htlog
  norm_num at htlog
  unfold rho
  apply (le_div_iff₀ log_Tg_pos).mpr
  linarith


-- @@ L578-578 verbatim
theorem rho_pos : 0 < rho := lt_of_lt_of_le (by norm_num) rho_lower


-- @@ L580-585 verbatim
/-- This includes the manuscript's range `0<h<1/2`, and in fact every `h≥0`. -/
theorem radialExponent_pos (h : ℝ) (hh : 0 ≤ h) : 0 < radialExponent h := by
  have hk : kappa < rho := by unfold kappa; linarith [rho_lower]
  have hm := mul_nonneg hh (sub_nonneg.mpr hk.le)
  unfold radialExponent
  nlinarith [rho_pos]


-- @@ L587-587 verbatim
theorem Q_pos (n : ℕ) : 0 < Q n := Real.rpow_pos_of_pos (by norm_num) _


-- @@ L589-593 verbatim
theorem Q_le_one (n : ℕ) : Q n ≤ 1 := by
  calc
    Q n ≤ (2 : ℝ) ^ (0 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (neg_nonpos.mpr (Nat.cast_nonneg n))
    _ = 1 := Real.rpow_zero _


-- @@ L595-597 verbatim
theorem S_pos {n : ℕ} (hn : 1 ≤ n) : 0 < S n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  exact pow_pos hn' _


-- @@ L599-599 verbatim
theorem epsilon_pos (h : ℝ) (n : ℕ) : 0 < epsilon h n := Real.rpow_pos_of_pos (Q_pos n) _


-- @@ L601-602 verbatim
theorem epsilon_le_one (h : ℝ) (hh : 0 ≤ h) (n : ℕ) : epsilon h n ≤ 1 :=
  Real.rpow_le_one (Q_pos n).le (Q_le_one n) hh


-- @@ L604-605 verbatim
theorem timeCoefficient_pos (h : ℝ) (n : ℕ) : 0 < timeCoefficient h n :=
  mul_pos (pow_pos Tg_pos _) (Real.rpow_pos_of_pos (Q_pos n) _)


-- @@ L607-608 verbatim
theorem radialCoefficient_pos (h : ℝ) (n : ℕ) : 0 < radialCoefficient h n :=
  mul_pos (pow_pos Lambda_pos _) (Real.rpow_pos_of_pos (Q_pos n) _)


-- @@ L610-615 verbatim
theorem Tg_rpow_rho : Tg ^ rho = Lambda := by
  rw [Real.rpow_def_of_pos Tg_pos]
  have he : Real.log Tg * rho = Real.log Lambda := by
    unfold rho
    field_simp [ne_of_gt log_Tg_pos]
  rw [he, Real.exp_log Lambda_pos]


-- @@ L617-622 verbatim
theorem Lambda_pow_eq (n : ℕ) : Lambda ^ n = ((Tg ^ n : ℝ) ^ rho) := by
  calc
    Lambda ^ n = (Tg ^ rho) ^ n := by rw [Tg_rpow_rho]
    _ = Tg ^ (rho * (n : ℝ)) := (Real.rpow_mul_natCast Tg_pos.le rho n).symm
    _ = Tg ^ ((n : ℝ) * rho) := by rw [mul_comm]
    _ = (Tg ^ n : ℝ) ^ rho := Real.rpow_natCast_mul Tg_pos.le n rho


-- @@ L624-631 verbatim
private theorem growth_at_nativeArgument (h : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    Tg ^ SlotColoring.nativeArgument h n = Q n ^ (-1 - h) / S n := by
  have ha : 0 < Q n ^ (-1 - h) / S n := div_pos (Real.rpow_pos_of_pos (Q_pos n) _) (S_pos hn)
  change Tg ^ (Real.log (Q n ^ (-1 - h) / S n) / Real.log Tg) = _
  rw [Real.rpow_def_of_pos Tg_pos]
  have he : Real.log Tg * (Real.log (Q n ^ (-1 - h) / S n) / Real.log Tg) =
      Real.log (Q n ^ (-1 - h) / S n) := by field_simp [ne_of_gt log_Tg_pos]
  rw [he, Real.exp_log ha]


-- @@ L633-643 verbatim
theorem native_power_bounds (h : ℝ) (hh : 0 ≤ h) {n : ℕ} (hn : 4 ≤ n) :
    Tg ^ nativeIndex h n ≤ Q n ^ (-1 - h) / S n ∧
      Q n ^ (-1 - h) / S n ≤ Tg * Tg ^ nativeIndex h n := by
  have hlo := Nat.floor_le (SlotColoring.nativeArgument_nonneg h hh hn)
  have hhi := (Nat.lt_floor_add_one (SlotColoring.nativeArgument h n)).le
  have lo := Real.rpow_le_rpow_of_exponent_le Tg_one_lt.le hlo
  have hi := Real.rpow_le_rpow_of_exponent_le Tg_one_lt.le hhi
  rw [growth_at_nativeArgument h (by omega), Real.rpow_natCast] at lo
  rw [growth_at_nativeArgument h (by omega), Real.rpow_add Tg_pos,
    Real.rpow_natCast, Real.rpow_one] at hi
  exact ⟨lo, by simpa only [nativeIndex, SlotColoring.nativeIndex, mul_comm] using hi⟩


-- @@ L645-653 verbatim
private theorem target_times_Q (h : ℝ) {n : ℕ} :
    (Q n ^ (-1 - h) / S n) * Q n ^ (1 + h) = 1 / S n := by
  calc
    (Q n ^ (-1 - h) / S n) * Q n ^ (1 + h) =
        (Q n ^ (-1 - h) * Q n ^ (1 + h)) / S n := by ring
    _ = 1 / S n := by
      rw [← Real.rpow_add (Q_pos n)]
      have he : (-1 - h) + (1 + h) = 0 := by ring
      rw [he, Real.rpow_zero]


-- @@ L655-668 verbatim
/-- The actual floor index gives the complete `c_i` comparison in (25). -/
theorem timeCoefficient_bounds (h : ℝ) (hh : 0 ≤ h) {n : ℕ} (hn : 4 ≤ n) :
    1 / (Tg * S n) ≤ timeCoefficient h n ∧ timeCoefficient h n ≤ 1 / S n := by
  obtain ⟨hl, hu⟩ := native_power_bounds h hh hn
  have hQ := (Real.rpow_pos_of_pos (Q_pos n) (1 + h)).le
  constructor
  · have hu' := mul_le_mul_of_nonneg_right hu hQ
    rw [target_times_Q] at hu'
    have hdiv : (1 / S n) / Tg ≤ timeCoefficient h n := by
      apply (div_le_iff₀ Tg_pos).mpr
      simpa [timeCoefficient, mul_assoc, mul_comm, mul_left_comm] using hu'
    simpa only [div_div, mul_comm] using hdiv
  · have hl' := mul_le_mul_of_nonneg_right hl hQ
    simpa only [target_times_Q, timeCoefficient] using hl'


-- @@ L670-691 verbatim
/-- The radial coefficient is an exact power of the time coefficient,
with the explicit small-viscosity loss. -/
theorem radialCoefficient_eq (h : ℝ) (n : ℕ) :
    radialCoefficient h n = epsilon h n ^ (-kappa) * timeCoefficient h n ^ rho := by
  have he : epsilon h n ^ (-kappa) = Q n ^ (-h * kappa) := by
    unfold epsilon
    rw [← Real.rpow_mul (Q_pos n).le]
    congr 1
    ring
  have hc : timeCoefficient h n ^ rho =
      (Tg ^ nativeIndex h n : ℝ) ^ rho * Q n ^ ((1 + h) * rho) := by
    unfold timeCoefficient
    rw [Real.mul_rpow (pow_nonneg Tg_pos.le _) (Real.rpow_nonneg (Q_pos n).le _),
      ← Real.rpow_mul (Q_pos n).le]
  rw [he, hc]
  unfold radialCoefficient
  rw [Lambda_pow_eq]
  have hd : radialExponent h / 2 = (-h * kappa) + (1 + h) * rho := by
    unfold radialExponent
    ring
  rw [hd, Real.rpow_add (Q_pos n)]
  ring


-- @@ L693-697 verbatim
private theorem one_div_S_rpow {n : ℕ} (hn : 1 ≤ n) :
    (1 / S n) ^ rho = S n ^ (-rho) := by
  rw [Real.div_rpow zero_le_one (S_pos hn).le, Real.one_rpow,
    Real.rpow_neg (S_pos hn).le]
  exact one_div _


-- @@ L699-703 verbatim
private theorem one_div_TS_rpow {n : ℕ} (hn : 1 ≤ n) :
    (1 / (Tg * S n)) ^ rho = S n ^ (-rho) / Lambda := by
  rw [Real.div_rpow zero_le_one (mul_pos Tg_pos (S_pos hn)).le, Real.one_rpow,
    Real.mul_rpow Tg_pos.le (S_pos hn).le, Tg_rpow_rho, Real.rpow_neg (S_pos hn).le]
  simp [div_eq_mul_inv, mul_comm]


-- @@ L705-719 verbatim
/-- The full `M_i` comparison in (25), obtained from the actual native index. -/
theorem radialCoefficient_bounds (h : ℝ) (hh : 0 ≤ h) {n : ℕ} (hn : 4 ≤ n) :
    epsilon h n ^ (-kappa) * S n ^ (-rho) / Lambda ≤ radialCoefficient h n ∧
      radialCoefficient h n ≤ epsilon h n ^ (-kappa) * S n ^ (-rho) := by
  obtain ⟨hcL, hcU⟩ := timeCoefficient_bounds h hh hn
  have hp := (Real.rpow_pos_of_pos (epsilon_pos h n) (-kappa)).le
  have hl := Real.rpow_le_rpow (one_div_nonneg.mpr (mul_pos Tg_pos (S_pos (by omega))).le)
    hcL rho_pos.le
  have hu := Real.rpow_le_rpow (timeCoefficient_pos h n).le hcU rho_pos.le
  rw [one_div_TS_rpow (by omega)] at hl
  rw [one_div_S_rpow (by omega)] at hu
  rw [radialCoefficient_eq]
  constructor
  · simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hl hp
  · exact mul_le_mul_of_nonneg_left hu hp


-- @@ L721-725 verbatim
theorem timeCoefficient_inv_upper (h : ℝ) (hh : 0 ≤ h) {n : ℕ} (hn : 4 ≤ n) :
    (timeCoefficient h n)⁻¹ ≤ Tg * S n := by
  have hl := (timeCoefficient_bounds h hh hn).1
  have hi := one_div_le_one_div_of_le (one_div_pos.mpr (mul_pos Tg_pos (S_pos (by omega)))) hl
  simpa only [one_div, inv_inv] using hi


-- @@ L727-736 verbatim
theorem radialCoefficient_inv_upper (h : ℝ) (hh : 0 ≤ h) {n : ℕ} (hn : 4 ≤ n) :
    (radialCoefficient h n)⁻¹ ≤ Lambda * epsilon h n ^ kappa * S n ^ rho := by
  have hl := (radialCoefficient_bounds h hh hn).1
  have hpos : 0 < epsilon h n ^ (-kappa) * S n ^ (-rho) / Lambda :=
    div_pos (mul_pos (Real.rpow_pos_of_pos (epsilon_pos h n) _)
      (Real.rpow_pos_of_pos (S_pos (by omega)) _)) Lambda_pos
  have hi := one_div_le_one_div_of_le hpos hl
  have hS : 0 < S n := S_pos (by omega)
  simpa [Real.rpow_neg (epsilon_pos h n).le, Real.rpow_neg hS.le,
    div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hi


-- @@ L738-741 verbatim
theorem timeCoefficient_inv_lower (h : ℝ) (hh : 0 ≤ h) {n : ℕ} (hn : 4 ≤ n) :
    S n ≤ (timeCoefficient h n)⁻¹ := by
  have hi := one_div_le_one_div_of_le (timeCoefficient_pos h n) (timeCoefficient_bounds h hh hn).2
  simpa only [one_div, inv_inv] using hi


-- @@ L743-744 verbatim
/-- Slot length, given by `2 * r0 / timeCoefficient h n`. -/
def slotLength (r0 h : ℝ) (n : ℕ) : ℝ := 2 * r0 / timeCoefficient h n


-- @@ L746-753 verbatim
/-- The native slot has length comparable to the actual slow scale `n²`. -/
theorem slotLength_bounds (r0 h : ℝ) (hr : 0 ≤ r0) (hh : 0 ≤ h) {n : ℕ} (hn : 4 ≤ n) :
    2 * r0 * S n ≤ slotLength r0 h n ∧ slotLength r0 h n ≤ 2 * r0 * Tg * S n := by
  have hm : 0 ≤ 2 * r0 := by positivity
  have hl := mul_le_mul_of_nonneg_left (timeCoefficient_inv_lower h hh hn) hm
  have hu := mul_le_mul_of_nonneg_left (timeCoefficient_inv_upper h hh hn) hm
  exact ⟨by simpa only [slotLength, div_eq_mul_inv] using hl,
    by simpa only [slotLength, div_eq_mul_inv, mul_assoc] using hu⟩


-- @@ L755-756 verbatim
/-- The carrier is the genuine rounded integer frequency used in the manuscript. -/
def carrier (h : ℝ) (n : ℕ) : ℕ := Scaling.carrierFrequency (epsilon h n)


-- @@ L758-762 verbatim
theorem carrier_viscosity_bounds (h : ℝ) (hh : 0 ≤ h) (n : ℕ) :
    1 ≤ epsilon h n * (carrier h n : ℝ) ^ 2 ∧
      epsilon h n * (carrier h n : ℝ) ^ 2 ≤ 4 := by
  obtain ⟨hl, hu, h4⟩ := Scaling.order_one_viscosity (epsilon_pos h n) (epsilon_le_one h hh n)
  exact ⟨hl, hu.trans h4⟩


-- @@ L764-767 verbatim
theorem carrier_inv_bounds (h : ℝ) (hh : 0 ≤ h) (n : ℕ) :
    Real.sqrt (epsilon h n) / 2 ≤ 1 / (carrier h n : ℝ) ∧
      1 / (carrier h n : ℝ) ≤ Real.sqrt (epsilon h n) :=
  Scaling.reciprocal_frequency_bounds (epsilon_pos h n) (epsilon_le_one h hh n)


-- @@ L769-783 verbatim
theorem slow_power_epsilon_identity (h a b : ℝ) (n : ℕ) :
    S n ^ a * epsilon h n ^ b =
      (n : ℝ) ^ (2 * a) * Real.exp (-(h * b * Real.log 2) * (n : ℝ)) := by
  have hS : S n ^ a = (n : ℝ) ^ (2 * a) := by
    simpa only [S, Nat.cast_ofNat] using
      (Real.rpow_natCast_mul (Nat.cast_nonneg n) 2 a).symm
  have he : epsilon h n ^ b = Real.exp (-(h * b * Real.log 2) * (n : ℝ)) := by
    unfold epsilon
    rw [← Real.rpow_mul (Q_pos n).le]
    unfold Q SlotColoring.dyadicQ
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [hS, he]


-- @@ L785-793 verbatim
/-- Every fixed real power of the slow scale is dominated by every positive
power of the actual small-viscosity scale, provided `h>0`. -/
theorem slow_power_epsilon_tendsto_zero (h : ℝ) (hh : 0 < h) (a b : ℝ) (hb : 0 < b) :
    Tendsto (fun n : ℕ => S n ^ a * epsilon h n ^ b) atTop (𝓝 0) := by
  have hc : 0 < h * b * Real.log 2 :=
    mul_pos (mul_pos hh hb) (Real.log_pos (by norm_num))
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (2 * a) (h * b * Real.log 2) hc).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [slow_power_epsilon_identity, Function.comp_def] using ht


-- @@ L795-798 verbatim
theorem eventually_slow_power_epsilon_lt (h : ℝ) (hh : 0 < h) (a b δ : ℝ)
    (hb : 0 < b) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, S n ^ a * epsilon h n ^ b < δ :=
  (tendsto_order.1 (slow_power_epsilon_tendsto_zero h hh a b hb)).2 δ hδ


-- @@ L800-803 verbatim
theorem exists_slow_power_epsilon_cutoff (h : ℝ) (hh : 0 < h) (a b δ : ℝ)
    (hb : 0 < b) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, S n ^ a * epsilon h n ^ b < δ :=
  eventually_atTop.1 (eventually_slow_power_epsilon_lt h hh a b δ hb hδ)


-- @@ L805-819 verbatim
/-- The rounding error `1/k`, multiplied by any fixed slow power, also
vanishes along the actual dyadic sequence. -/
theorem slow_power_div_carrier_tendsto_zero (h : ℝ) (hh : 0 < h) (a : ℝ) :
    Tendsto (fun n : ℕ => S n ^ a / (carrier h n : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero
    (fun n => div_nonneg (Real.rpow_nonneg (sq_nonneg (n : ℝ)) a) (Nat.cast_nonneg _))
    (g := fun n : ℕ => S n ^ a * epsilon h n ^ (1 / 2 : ℝ))
  · intro n
    calc
      S n ^ a / (carrier h n : ℝ) = S n ^ a * (1 / (carrier h n : ℝ)) := by ring
      _ ≤ S n ^ a * Real.sqrt (epsilon h n) :=
        mul_le_mul_of_nonneg_left (carrier_inv_bounds h hh.le n).2
          (Real.rpow_nonneg (sq_nonneg (n : ℝ)) a)
      _ = S n ^ a * epsilon h n ^ (1 / 2 : ℝ) := by rw [Real.sqrt_eq_rpow]
  · exact slow_power_epsilon_tendsto_zero h hh a (1 / 2) (by norm_num)


-- @@ L821-821 verbatim
end NavierStokes.ChartScales
