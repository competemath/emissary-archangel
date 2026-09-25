/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module


public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic


-- @@ L15-19 verbatim
/-!
# Integral Parametrisations

Parametrisations of the contours used to define the magic-function integrals.
-/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
open Set Complex Real


-- @@ L25-25 verbatim
local notation "V" => EuclideanSpace ℝ (Fin 8)


-- @@ L27-27 verbatim
local notation "ℍ₀" => UpperHalfPlane.upperHalfPlaneSet


-- @@ L29-29 verbatim
namespace MagicFunction.Parametrisations


-- @@ L31-31 verbatim
noncomputable section Parametrisations


-- @@ L33-33 verbatim
def z₁ (t : Icc (0 : ℝ) 1) : ℂ := -1 + I * t


-- @@ L35-35 verbatim
def z₁' (t : ℝ) : ℂ := IccExtend (zero_le_one) z₁ t -- `by norm_num` also works


-- @@ L37-37 verbatim
def z₂ (t : Icc (0 : ℝ) 1) : ℂ := -1 + t + I


-- @@ L39-39 verbatim
def z₂' (t : ℝ) : ℂ := IccExtend (zero_le_one) z₂ t -- `by norm_num` also works


-- @@ L41-41 verbatim
def z₃ (t : Icc (0 : ℝ) 1) : ℂ := 1 + I * t


-- @@ L43-43 verbatim
def z₃' (t : ℝ) : ℂ := IccExtend (zero_le_one) z₃ t -- `by norm_num` also works


-- @@ L45-45 verbatim
def z₄ (t : Icc (0 : ℝ) 1) : ℂ := 1 - t + I


-- @@ L47-47 verbatim
def z₄' (t : ℝ) : ℂ := IccExtend (zero_le_one) z₄ t -- `by norm_num` also works


-- @@ L49-49 verbatim
def z₅ (t : Icc (0 : ℝ) 1) : ℂ := I * t


-- @@ L51-51 verbatim
def z₅' (t : ℝ) : ℂ := IccExtend (zero_le_one) z₅ t -- `by norm_num` also works


-- @@ L53-53 verbatim
def z₆ (t : Ici (1 : ℝ)) : ℂ := I * t


-- @@ L55-55 verbatim
def z₆' (t : ℝ) : ℂ := IciExtend z₆ t -- `by norm_num` also works


-- @@ L57-57 verbatim
end Parametrisations


-- @@ L59-59 verbatim
section UpperHalfPlane


-- @@ L61-61 verbatim
open scoped UpperHalfPlane


-- @@ L63-67 verbatim
lemma im_z₁'_pos {t : ℝ} (ht : t ∈ Ioc 0 1) : 0 < (z₁' t).im := by
  have ht' : t ∈ Icc 0 1 := mem_Icc_of_Ioc ht
  simp only [z₁', IccExtend_of_mem zero_le_one z₁ ht', z₁, add_im, neg_im, one_im, neg_zero, mul_im,
    I_re, ofReal_im, mul_zero, I_im, ofReal_re, one_mul, zero_add]
  exact ht.1


-- @@ L69-70 verbatim
lemma im_z₂'_pos {t : ℝ} (ht : t ∈ Icc 0 1) : 0 < (z₂' t).im := by
  simp [z₂', IccExtend_of_mem zero_le_one z₂ ht, z₂]


-- @@ L72-76 verbatim
lemma im_z₃'_pos {t : ℝ} (ht : t ∈ Ioc 0 1) : 0 < (z₃' t).im := by
  have ht' : t ∈ Icc 0 1 := mem_Icc_of_Ioc ht
  simp only [z₃', IccExtend_of_mem zero_le_one z₃ ht', z₃, add_im, one_im, mul_im, I_re, ofReal_im,
    mul_zero, I_im, ofReal_re, one_mul, zero_add]
  exact ht.1


-- @@ L78-79 verbatim
lemma im_z₄'_pos {t : ℝ} (ht : t ∈ Icc 0 1) : 0 < (z₄' t).im := by
  simp [z₄', IccExtend_of_mem zero_le_one z₄ ht, z₄]


-- @@ L81-85 verbatim
lemma im_z₅'_pos {t : ℝ} (ht : t ∈ Ioc 0 1) : 0 < (z₅' t).im := by
  have ht' : t ∈ Icc 0 1 := mem_Icc_of_Ioc ht
  simp only [z₅', IccExtend_of_mem zero_le_one z₅ ht', z₅, mul_im, I_re, ofReal_im, mul_zero, I_im,
    ofReal_re, one_mul, zero_add]
  exact ht.1


-- @@ L87-91 verbatim
lemma im_z₆'_pos {t : ℝ} (ht : t ∈ Ici (1 : ℝ)) : 0 < (z₆' t).im := by
  simp only [z₆', IciExtend_of_mem z₆ ht, z₆, mul_im, I_re, ofReal_im, mul_zero, I_im, ofReal_re,
    one_mul, zero_add]
  rw [mem_Ici] at ht
  linarith


-- @@ L93-93 expanded
lemma z₁'_mem_upperHalfPlane_set {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    z₁' t ∈ UpperHalfPlane.upperHalfPlaneSet :=
  im_z₁'_pos ht


-- @@ L95-95 expanded
lemma z₂'_mem_upperHalfPlane_set {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    z₂' t ∈ UpperHalfPlane.upperHalfPlaneSet :=
  im_z₂'_pos ht


-- @@ L97-97 expanded
lemma z₃'_mem_upperHalfPlane_set {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    z₃' t ∈ UpperHalfPlane.upperHalfPlaneSet :=
  im_z₃'_pos ht


-- @@ L99-99 expanded
lemma z₄'_mem_upperHalfPlane_set {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    z₄' t ∈ UpperHalfPlane.upperHalfPlaneSet :=
  im_z₄'_pos ht


-- @@ L101-101 expanded
lemma z₅'_mem_upperHalfPlane_set {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    z₅' t ∈ UpperHalfPlane.upperHalfPlaneSet :=
  im_z₅'_pos ht


-- @@ L103-103 expanded
lemma z₆'_mem_upperHalfPlane_set {t : ℝ} (ht : t ∈ Ici (1 : ℝ)) :
    z₆' t ∈ UpperHalfPlane.upperHalfPlaneSet :=
  im_z₆'_pos ht


-- @@ L105-105 expanded
lemma z₁'_mapsto : MapsTo z₁' (Ioc 0 1) UpperHalfPlane.upperHalfPlaneSet := fun _ ht ↦
  z₁'_mem_upperHalfPlane_set ht


-- @@ L107-107 expanded
lemma z₂'_mapsto : MapsTo z₂' (Icc 0 1) UpperHalfPlane.upperHalfPlaneSet := fun _ ht ↦
  z₂'_mem_upperHalfPlane_set ht


-- @@ L109-109 expanded
lemma z₃'_mapsto : MapsTo z₃' (Ioc 0 1) UpperHalfPlane.upperHalfPlaneSet := fun _ ht ↦
  z₃'_mem_upperHalfPlane_set ht


-- @@ L111-111 expanded
lemma z₄'_mapsto : MapsTo z₄' (Icc 0 1) UpperHalfPlane.upperHalfPlaneSet := fun _ ht ↦
  z₄'_mem_upperHalfPlane_set ht


-- @@ L113-113 expanded
lemma z₅'_mapsto : MapsTo z₅' (Ioc 0 1) UpperHalfPlane.upperHalfPlaneSet := fun _ ht ↦
  z₅'_mem_upperHalfPlane_set ht


-- @@ L115-115 expanded
lemma z₆'_mapsto : MapsTo z₆' (Ici 1) UpperHalfPlane.upperHalfPlaneSet := fun _ ht ↦
  z₆'_mem_upperHalfPlane_set ht


-- @@ L117-117 verbatim
end UpperHalfPlane


-- @@ L119-119 verbatim
section eq_of_mem


-- @@ L121-122 verbatim
lemma z₁'_eq_z₁_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) : z₁' t = z₁ ⟨t, ht⟩ := by
  rw [z₁', IccExtend_of_mem zero_le_one z₁ ht]


-- @@ L124-125 verbatim
lemma z₂'_eq_z₂_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) : z₂' t = z₂ ⟨t, ht⟩ := by
  rw [z₂', IccExtend_of_mem zero_le_one z₂ ht]


-- @@ L127-128 verbatim
lemma z₃'_eq_z₃_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) : z₃' t = z₃ ⟨t, ht⟩ := by
  rw [z₃', IccExtend_of_mem zero_le_one z₃ ht]


-- @@ L130-131 verbatim
lemma z₄'_eq_z₄_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) : z₄' t = z₄ ⟨t, ht⟩ := by
  rw [z₄', IccExtend_of_mem zero_le_one z₄ ht]


-- @@ L133-134 verbatim
lemma z₅'_eq_z₅_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) : z₅' t = z₅ ⟨t, ht⟩ := by
  rw [z₅', IccExtend_of_mem zero_le_one z₅ ht]


-- @@ L136-137 verbatim
lemma z₆'_eq_z₆_of_mem {t : ℝ} (ht : t ∈ Ici 1) : z₆' t = z₆ ⟨t, ht⟩ := by
  rw [z₆', IciExtend_of_mem z₆ ht]


-- @@ L139-140 verbatim
lemma z₁'_eq_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) : z₁' t = -1 + I * t := by
  rw [z₁'_eq_z₁_of_mem ht, z₁]


-- @@ L142-143 verbatim
lemma z₂'_eq_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) : z₂' t = -1 + t + I := by
  rw [z₂'_eq_z₂_of_mem ht, z₂]


-- @@ L145-146 verbatim
lemma z₃'_eq_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) : z₃' t = 1 + I * t := by
  rw [z₃'_eq_z₃_of_mem ht, z₃]


-- @@ L148-149 verbatim
lemma z₄'_eq_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) : z₄' t = 1 - t + I := by
  rw [z₄'_eq_z₄_of_mem ht, z₄]


-- @@ L151-152 verbatim
lemma z₅'_eq_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) : z₅' t = I * t := by
  rw [z₅'_eq_z₅_of_mem ht, z₅]


-- @@ L154-155 verbatim
lemma z₆'_eq_of_mem {t : ℝ} (ht : t ∈ Ici 1) : z₆' t = I * t := by
  rw [z₆'_eq_z₆_of_mem ht, z₆]


-- @@ L157-157 verbatim
end eq_of_mem


-- @@ L159-159 verbatim
section transforms_mem


-- @@ L161-161 verbatim
open Matrix Matrix.SpecialLinearGroup UpperHalfPlane ModularGroup

-- @@ L162-162 verbatim
open scoped MatrixGroups ComplexConjugate


-- @@ L164-164 verbatim
lemma _root_.ModularGroup.ST_eq : S * T = !![(0 : ℤ), -1; 1, 1] := by decide


-- @@ L166-166 verbatim
lemma _root_.ModularGroup.S_eq : S = !![(0 : ℤ), -1; 1, 0] := by rfl


-- @@ L168-168 verbatim
lemma det_aux : !![(0 : ℤ), -1; 1, 1].det = 1 := by decide


-- @@ L170-171 verbatim
lemma _root_.ModularGroup.ST_eq' : S * T = ⟨!![(0 : ℤ), -1; 1, 1], det_aux⟩ := by
  simp only [← ModularGroup.ST_eq]; norm_cast


-- @@ L173-174 verbatim
lemma _root_.ModularGroup.S_eq' : S = ⟨!![(0 : ℤ), -1; 1, 0], det_aux⟩ := by
  simp only [← ModularGroup.S_eq]; norm_cast


-- @@ L176-179 verbatim
lemma neg_inv_one_add_eq_ST_coe (z : ℍ) :
    -1 / ((z : ℂ) + 1) = UpperHalfPlane.coe ((S * T) • z) := by
  rw [specialLinearGroup_apply]
  simp_all [ST_eq]


-- @@ L181-183 verbatim
lemma neg_inv_one_add_mem (z : ℍ) : 0 < (-1 / ((z : ℂ) + 1)).im := by
  rw [neg_inv_one_add_eq_ST_coe, coe_im]
  exact ((S * T) • z).2


-- @@ L185-188 verbatim
lemma neg_inv_one_add_eq_ST (z : ℍ) :
    ⟨-1 / ((z : ℂ) + 1), neg_inv_one_add_mem z⟩ = (S * T) • z := by
  apply UpperHalfPlane.ext
  rw [← neg_inv_one_add_eq_ST_coe]


-- @@ L190-193 verbatim
lemma neg_inv_eq_S_coe (z : ℍ) :
    -1 / z = UpperHalfPlane.coe (S • z) := by
  rw [specialLinearGroup_apply]
  simp_all [S_eq]


-- @@ L195-197 verbatim
lemma neg_inv_mem (z : ℍ) : 0 < (-1 / (z : ℂ)).im := by
  rw [neg_inv_eq_S_coe, coe_im]
  exact (S • z).2


-- @@ L199-202 verbatim
lemma neg_inv_eq_S (z : ℍ) :
    ⟨-1 / (z : ℂ), neg_inv_mem z⟩ = S • z := by
  apply UpperHalfPlane.ext
  rw [← neg_inv_eq_S_coe]


-- @@ L204-207 expanded
/-- The Möbius map `w ↦ -1/w` sends the upper-half-plane set `ℍ₀ ⊆ ℂ` to itself.
    (Set-level analogue of `neg_inv_mem`, which is stated for the subtype `ℍ`.) -/
theorem neg_inv_mem_of_mem {w : ℂ} (hw : w ∈ UpperHalfPlane.upperHalfPlaneSet) :
    -1 / w ∈ UpperHalfPlane.upperHalfPlaneSet := by
  simpa [neg_div, one_div] using UpperHalfPlane.im_inv_neg_coe_pos ⟨w, hw⟩


-- @@ L209-210 expanded
/-- `w ↦ -1/w` maps `ℍ₀` into `ℍ₀`. -/
theorem neg_inv_mapsto :
    MapsTo (fun w : ℂ ↦ -1 / w) UpperHalfPlane.upperHalfPlaneSet UpperHalfPlane.upperHalfPlaneSet :=
  fun _ hw ↦ neg_inv_mem_of_mem hw


-- @@ L212-215 expanded
/-- For a real shift `c` (`c.im = 0`), `z ↦ -1/(z + c)` maps `ℍ₀` into `ℍ₀`. -/
theorem neg_inv_add_mapsto {c : ℂ} (hc : c.im = 0) :
    MapsTo (fun z : ℂ ↦ -1 / (z + c)) UpperHalfPlane.upperHalfPlaneSet
      UpperHalfPlane.upperHalfPlaneSet :=
  fun z hz ↦
  neg_inv_mem_of_mem
    (show z + c ∈ UpperHalfPlane.upperHalfPlaneSet by rw [mem_setOf_eq, add_im, hc, add_zero];
      exact hz)


-- @@ L217-217 verbatim
end transforms_mem


-- @@ L219-219 verbatim
end MagicFunction.Parametrisations
