/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.CenteredMaximal.Statement


-- @@ L10-27 verbatim
/-!
# The constants of the weighted lattice

The chosen configuration is the periodic measure with columns at `x = i * hgap`, carrying mass
`1` for even `i` and mass `heavy` for odd `i`, and rows at `y = j * vgap` of unit weight. Its
parameters are determined by three edge collisions of witness rectangles; they reduce to the single
quadratic `3 u² - 4 u - 6 = 0` for `u = root = (2 + √22)/3`:

* `heavy = u² - 1 = (17 + 4√22)/9`, so a light and a heavy atom together weigh `u²`;
* `hgap = (1 + u)/2 = (5 + √22)/6` and `vgap = hgap + 1 = (11 + √22)/6`.

The witness squares use the sides `1`, `u`, `sideH1 = √heavy`, `sideLH2 = √2 · u`,
`sideLHL2 = √(2 (2 + heavy))` and `2 hgap + 1`. The witnesses cover the period cell outside
four open slots, each of width `slotW` and height `slotH`, and
`phi = (2 hgap vgap - 4 slotW slotH) / (1 + heavy)`.

All numerical facts are proved from rational enclosures of `√2` and `√22`.
-/


-- @@ L29-29 verbatim
@[expose] public section


-- @@ L31-31 verbatim
noncomputable section


-- @@ L33-33 verbatim
namespace LeanPool.CenteredMaximal.Lattice


-- @@ L35-36 verbatim
/-- `u = (2 + √22)/3`, the positive root of `3u² - 4u - 6 = 0`. -/
def root : ℝ := (2 + √22) / 3


-- @@ L38-39 verbatim
/-- The heavy mass `w = u² - 1 = (17 + 4√22)/9`. -/
def heavy : ℝ := root ^ 2 - 1


-- @@ L41-42 verbatim
/-- The column spacing `h = (1 + u)/2 = (5 + √22)/6`. -/
def hgap : ℝ := (1 + root) / 2


-- @@ L44-45 verbatim
/-- The row spacing `V = h + 1 = (11 + √22)/6`. -/
def vgap : ℝ := hgap + 1


-- @@ L47-48 verbatim
/-- Side of the witness made of one heavy atom: `√w`. -/
def sideH1 : ℝ := √heavy


-- @@ L50-51 verbatim
/-- Side of the witness made of a light and a heavy atom in two rows: `√(2(1 + w)) = √2 · u`. -/
def sideLH2 : ℝ := √2 * root


-- @@ L53-54 verbatim
/-- Side of the witness made of light, heavy, light atoms in two rows: `√(2(2 + w))`. -/
def sideLHL2 : ℝ := √(2 * (2 + heavy))


-- @@ L56-57 verbatim
/-- Width of a slot excluded from the witnessed region: `2h - √(2(2 + w))/2 - u/2`. -/
def slotW : ℝ := 2 * hgap - sideLHL2 / 2 - root / 2


-- @@ L59-60 verbatim
/-- Height of a slot excluded from the witnessed region: `V - √(2(1 + w))/2 - √w/2`. -/
def slotH : ℝ := vgap - sideLH2 / 2 - sideH1 / 2


-- @@ L62-62 verbatim
/-! ### Square roots -/


-- @@ L64-64 verbatim
theorem sqrt22_sq : √22 ^ 2 = 22 := Real.sq_sqrt (by norm_num)


-- @@ L66-67 verbatim
/-- Lower rational enclosure of `√22`. -/
theorem sqrt22_gt : (4.69 : ℝ) < √22 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)


-- @@ L69-70 verbatim
/-- Upper rational enclosure of `√22`. -/
theorem sqrt22_lt : √22 < (4.691 : ℝ) := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)


-- @@ L72-73 verbatim
/-- Lower rational enclosure of `√2`. -/
theorem sqrt2_gt : (1.414 : ℝ) < √2 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)


-- @@ L75-76 verbatim
/-- Upper rational enclosure of `√2`. -/
theorem sqrt2_lt : √2 < (1.4143 : ℝ) := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)


-- @@ L78-78 verbatim
/-! ### Exact identities -/


-- @@ L80-83 verbatim
/-- `3u² - 4u - 6 = 0`. -/
theorem root_quadratic : 3 * root ^ 2 - 4 * root - 6 = 0 := by
  unfold root
  linear_combination (1 / 3 : ℝ) * sqrt22_sq


-- @@ L85-88 verbatim
/-- `u = 2h - 1`: the light–heavy one-row witness starts where the light atom's square ends. -/
theorem two_mul_hgap_sub_one : 2 * hgap - 1 = root := by
  unfold hgap
  ring


-- @@ L90-93 verbatim
/-- A light and a heavy atom together weigh `u²`. -/
theorem one_add_heavy : 1 + heavy = root ^ 2 := by
  unfold heavy
  ring


-- @@ L95-96 verbatim
/-- `V = h + 1`. -/
theorem vgap_eq : vgap = hgap + 1 := rfl


-- @@ L98-101 verbatim
/-- `w = (17 + 4√22)/9`. -/
theorem heavy_eq : heavy = (17 + 4 * √22) / 9 := by
  unfold heavy root
  linear_combination (1 / 9 : ℝ) * sqrt22_sq


-- @@ L103-106 verbatim
/-- The side `2h + 1` of the heavy–light–heavy two-row witness squares to its mass. -/
theorem two_mul_hgap_add_one_sq : (2 * hgap + 1) ^ 2 = 2 * (heavy + 1 + heavy) := by
  unfold hgap heavy
  linear_combination (-1 : ℝ) * root_quadratic


-- @@ L108-108 verbatim
/-! ### Numerical facts -/


-- @@ L110-112 verbatim
theorem root_gt : (2.23 : ℝ) < root := by
  unfold root
  linarith [sqrt22_gt]


-- @@ L114-117 verbatim
/-- Upper enclosure of `u`. -/
theorem root_lt : root < (2.2304 : ℝ) := by
  unfold root
  linarith [sqrt22_lt]


-- @@ L119-121 verbatim
/-- `1 ≤ u`, so the light–heavy one-row witness has side at least `1`. -/
theorem one_le_root : 1 ≤ root := by
  linarith [root_gt]


-- @@ L123-126 verbatim
/-- Lower enclosure of `w`. -/
theorem heavy_gt : (3.9729 : ℝ) < heavy := by
  unfold heavy
  nlinarith [root_gt]


-- @@ L128-131 verbatim
/-- Upper enclosure of `w`. -/
theorem heavy_lt : heavy < (3.9747 : ℝ) := by
  unfold heavy
  nlinarith [root_gt, root_lt]


-- @@ L133-135 verbatim
/-- The heavy mass is positive. -/
theorem heavy_pos : 0 < heavy := by
  linarith [heavy_gt]


-- @@ L137-140 verbatim
/-- Lower enclosure of `h`. -/
theorem hgap_gt : (1.615 : ℝ) < hgap := by
  unfold hgap
  linarith [root_gt]


-- @@ L142-145 verbatim
/-- Upper enclosure of `h`. -/
theorem hgap_lt : hgap < (1.6152 : ℝ) := by
  unfold hgap
  linarith [root_lt]


-- @@ L147-149 verbatim
/-- The column spacing is positive. -/
theorem hgap_pos : 0 < hgap := by
  linarith [hgap_gt]


-- @@ L151-154 verbatim
/-- Lower enclosure of `V`. -/
theorem vgap_gt : (2.615 : ℝ) < vgap := by
  unfold vgap
  linarith [hgap_gt]


-- @@ L156-159 verbatim
/-- Upper enclosure of `V`. -/
theorem vgap_lt : vgap < (2.6152 : ℝ) := by
  unfold vgap
  linarith [hgap_lt]


-- @@ L161-163 verbatim
/-- The light–heavy two-row witness squares to its mass `2(1 + w)`. -/
theorem sideLH2_sq : sideLH2 ^ 2 = 2 * (1 + heavy) := by
  rw [sideLH2, mul_pow, Real.sq_sqrt (by norm_num), one_add_heavy]


-- @@ L165-167 verbatim
/-- The one-heavy-atom witness squares to its mass `w`. -/
theorem sideH1_sq : sideH1 ^ 2 = heavy :=
  Real.sq_sqrt heavy_pos.le


-- @@ L169-172 verbatim
/-- The light–heavy–light two-row witness squares to its mass `2(2 + w)`. -/
theorem sideLHL2_sq : sideLHL2 ^ 2 = 2 * (1 + heavy + 1) := by
  rw [sideLHL2, Real.sq_sqrt (by linarith [heavy_pos])]
  ring


-- @@ L174-177 verbatim
/-- Lower enclosure of `√2 u`. -/
theorem sideLH2_gt : (3.153 : ℝ) < sideLH2 := by
  unfold sideLH2
  nlinarith [sqrt2_gt, root_gt]


-- @@ L179-182 verbatim
/-- Upper enclosure of `√2 u`. -/
theorem sideLH2_lt : sideLH2 < (3.1545 : ℝ) := by
  unfold sideLH2
  nlinarith [sqrt2_lt, sqrt2_gt, root_lt, root_gt]


-- @@ L184-186 verbatim
/-- Lower enclosure of `√w`. -/
theorem sideH1_gt : (1.99 : ℝ) < sideH1 :=
  (Real.lt_sqrt (by norm_num)).2 (by linarith [heavy_gt])


-- @@ L188-190 verbatim
/-- Upper enclosure of `√w`. -/
theorem sideH1_lt : sideH1 < (1.994 : ℝ) :=
  (Real.sqrt_lt' (by norm_num)).2 (by linarith [heavy_lt])


-- @@ L192-194 verbatim
/-- Lower enclosure of `√(2(2 + w))`. -/
theorem sideLHL2_gt : (3.45 : ℝ) < sideLHL2 :=
  (Real.lt_sqrt (by norm_num)).2 (by linarith [heavy_gt])


-- @@ L196-198 verbatim
/-- Upper enclosure of `√(2(2 + w))`. -/
theorem sideLHL2_lt : sideLHL2 < (3.457 : ℝ) :=
  (Real.sqrt_lt' (by norm_num)).2 (by linarith [heavy_lt])


-- @@ L200-202 verbatim
/-- `1 ≤ √w`: the heavy atom's square reaches back to the light–heavy one-row region. -/
theorem one_le_sideH1 : 1 ≤ sideH1 := by
  linarith [sideH1_gt]


-- @@ L204-207 verbatim
/-- `u ≤ √2 u`: the light–heavy two-row witness is wider than the one-row one. -/
theorem root_le_sideLH2 : root ≤ sideLH2 := by
  unfold sideLH2
  nlinarith [sqrt2_gt, root_gt]


-- @@ L209-211 verbatim
/-- `V ≤ √2 u`: the light–heavy two-row witness reaches the middle line `y = V/2`. -/
theorem vgap_le_sideLH2 : vgap ≤ sideLH2 := by
  linarith [vgap_lt, sideLH2_gt]


-- @@ L213-215 verbatim
/-- `2V ≤ u + √2 u`: above the one-row witness the two-row witness takes over. -/
theorem two_mul_vgap_le_root_add_sideLH2 : 2 * vgap ≤ root + sideLH2 := by
  linarith [vgap_lt, sideLH2_gt, root_gt]


-- @@ L217-219 verbatim
/-- `2h ≤ √(2(2 + w))`: the light–heavy–light witness reaches the heavy column. -/
theorem two_mul_hgap_le_sideLHL2 : 2 * hgap ≤ sideLHL2 := by
  linarith [hgap_lt, sideLHL2_gt]


-- @@ L221-223 verbatim
/-- `V ≤ √(2(2 + w))`: the light–heavy–light witness reaches the middle line `y = V/2`. -/
theorem vgap_le_sideLHL2 : vgap ≤ sideLHL2 := by
  linarith [vgap_lt, sideLHL2_gt]


-- @@ L225-227 verbatim
/-- `2V - √(2(2 + w)) ≤ √w`: next to the heavy column the two witnesses overlap. -/
theorem vgap_sub_le_sideH1 : 2 * vgap - sideLHL2 ≤ sideH1 := by
  linarith [vgap_lt, sideLHL2_gt, sideH1_gt]


-- @@ L229-231 verbatim
/-- `4h - √(2(2 + w)) ≤ √2 u`: left of the heavy column the two-row witnesses overlap. -/
theorem four_mul_hgap_sub_le_sideLH2 : 4 * hgap - sideLHL2 ≤ sideLH2 := by
  linarith [hgap_lt, sideLHL2_gt, sideLH2_gt]


-- @@ L233-236 verbatim
/-- The slot has positive width. -/
theorem slotW_pos : 0 < slotW := by
  unfold slotW
  linarith [hgap_gt, sideLHL2_lt, root_lt]


-- @@ L238-241 verbatim
/-- The slot has positive height. -/
theorem slotH_pos : 0 < slotH := by
  unfold slotH
  linarith [vgap_gt, sideLH2_lt, sideH1_lt]


-- @@ L243-243 verbatim
/-! ### The closed form of `Φ` -/


-- @@ L245-247 verbatim
theorem sqrt2_mul_sqrt22 : √2 * √22 = 2 * √11 := by
  rw [← Real.sqrt_mul (by norm_num), show (2 : ℝ) * 22 = 2 ^ 2 * 11 by norm_num,
    Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]


-- @@ L249-251 verbatim
/-- `√(x/9) = √x / 3`. -/
theorem sqrt_div_nine {x : ℝ} (hx : 0 ≤ x) : √(x / 9) = √x / 3 := by
  rw [Real.sqrt_div hx, show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]


-- @@ L253-256 verbatim
/-- `√2 u = (2√2 + 2√11)/3`. -/
theorem sideLH2_eq : sideLH2 = (2 * √2 + 2 * √11) / 3 := by
  rw [sideLH2, root, ← sqrt2_mul_sqrt22]
  ring


-- @@ L258-260 verbatim
/-- `√w = √(17 + 4√22)/3`. -/
theorem sideH1_eq : sideH1 = √(17 + 4 * √22) / 3 := by
  rw [sideH1, heavy_eq, sqrt_div_nine (by positivity)]


-- @@ L262-265 verbatim
/-- `√(2(2 + w)) = √(70 + 8√22)/3`. -/
theorem sideLHL2_eq : sideLHL2 = √(70 + 8 * √22) / 3 := by
  rw [sideLHL2, heavy_eq, ← sqrt_div_nine (by positivity)]
  ring_nf


-- @@ L267-270 verbatim
/-- The slot width in radicals. -/
theorem slotW_eq : slotW = (8 + √22 - √(70 + 8 * √22)) / 6 := by
  rw [slotW, sideLHL2_eq, hgap, root]
  ring


-- @@ L272-275 verbatim
/-- The slot height in radicals. -/
theorem slotH_eq : slotH = (11 + √22 - 2 * √2 - 2 * √11 - √(17 + 4 * √22)) / 6 := by
  rw [slotH, sideLH2_eq, sideH1_eq, vgap, hgap, root]
  ring


-- @@ L277-280 verbatim
/-- The mass per period cell in radicals. -/
theorem one_add_heavy_eq : 1 + heavy = (26 + 4 * √22) / 9 := by
  rw [heavy_eq]
  ring


-- @@ L282-285 verbatim
/-- The area of the period cell in radicals. -/
theorem two_mul_hgap_mul_vgap : 2 * hgap * vgap = (77 + 16 * √22) / 18 := by
  unfold vgap hgap root
  linear_combination (1 / 18 : ℝ) * sqrt22_sq


-- @@ L287-293 verbatim
/-- The expression for `Φ` used in the area lower bound: subtract the four slot areas
`slotW · slotH` from the cell area `2 h V`, then divide by the cell mass `1 + w`. -/
theorem phi_eq : phi = (2 * hgap * vgap - 4 * slotW * slotH) / (1 + heavy) := by
  rw [phi, mul_assoc 4, slotW_eq, slotH_eq, one_add_heavy_eq, two_mul_hgap_mul_vgap]
  have h₁ : (0 : ℝ) < 26 + 4 * √22 := by positivity
  field_simp
  ring


-- @@ L295-295 verbatim
end LeanPool.CenteredMaximal.Lattice
