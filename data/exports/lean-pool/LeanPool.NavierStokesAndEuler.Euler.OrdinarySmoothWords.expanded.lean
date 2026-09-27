/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpSmoothFieldAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.ParameterWordGevrey
import LeanPool.NavierStokesAndEuler.Euler.SmoothL2Gevrey
import Mathlib.Algebra.Order.Star.Real


-- @@ L14-16 verbatim
/-! Actual finite coordinate derivatives of ordinary smooth L² fields.
The word fields retain all genuine L² derivatives; no Sobolev regularity
or distributional derivative is postulated. -/


-- @@ L18-18 verbatim
@[expose] public section



-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
namespace EulerOrdinarySobolev


-- @@ L25-26 verbatim
open MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerParameterWordGevrey Finset

-- @@ L27-27 verbatim
open scoped ContDiff ENNReal


-- @@ L29-30 verbatim
/-- Axis, given by `EuclideanSpace.single i 1`. -/
def axis (i : Fin 3) : Space := EuclideanSpace.single i 1


-- @@ L32-33 verbatim
@[simp] theorem axis_norm (i : Fin 3) : ‖axis i‖ = 1 := by
  simp [axis]


-- @@ L35-36 verbatim
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]


-- @@ L38-42 verbatim
theorem field_ext {A B : SmoothL2Field V} (h : A.field = B.field) : A = B := by
  cases A
  cases B
  cases h
  rfl


-- @@ L44-48 verbatim
/-- Word field as an element of `{n : ℕ} → (Fin n → Fin 3) → SmoothL2Field V | 0, _ => A | _+1,
w => (wordField A (Fin.tail w)).directionalField (axis (w 0))`. -/
def wordField (A : SmoothL2Field V) : {n : ℕ} → (Fin n → Fin 3) → SmoothL2Field V
  | 0, _ => A
  | _+1, w => (wordField A (Fin.tail w)).directionalField (axis (w 0))


-- @@ L50-51 verbatim
@[simp] theorem wordField_zero (A : SmoothL2Field V) (w : Fin 0 → Fin 3) :
    wordField A w = A := rfl


-- @@ L53-56 verbatim
@[simp] theorem wordField_cons (A : SmoothL2Field V) {n : ℕ}
    (w : Fin n → Fin 3) (i : Fin 3) :
    wordField A (Fin.cons i w) = (wordField A w).directionalField (axis i) := by
  simp only [wordField,Fin.tail_cons,Fin.cons_zero]


-- @@ L58-72 verbatim
theorem wordField_field (A : SmoothL2Field V) {n : ℕ} (w : Fin n → Fin 3) :
    (wordField A w).field = wordDerivative axis A.field w := by
  induction n with
  | zero => exact (funext (wordDerivative_zero axis A.field w)).symm
  | succ n ih =>
    funext x
    change fderiv ℝ (wordField A (Fin.tail w)).field x (axis (w 0)) = _
    rw [ih]
    have h := (A.smooth.differentiable_iteratedFDeriv
      (show (n : ℕ∞ω) < (∞ : ℕ∞ω) by
          exact_mod_cast ENat.natCast_lt_top n) x).iteratedFDeriv_succ_apply_left' (m := axis ∘ w)
    change fderiv ℝ (fun y => iteratedFDeriv ℝ n A.field y
      (fun j => axis (w j.succ))) x (axis (w 0)) =
        iteratedFDeriv ℝ (n+1) A.field x (fun j => axis (w j))
    exact h.symm


-- @@ L74-79 verbatim
theorem wordField_snoc (A : SmoothL2Field V) {n : ℕ}
    (w : Fin n → Fin 3) (i : Fin 3) :
    wordField A (Fin.snoc w i) = wordField (A.directionalField (axis i)) w := by
  apply field_ext
  rw [wordField_field,wordField_field]
  exact funext (wordDerivative_snoc axis A.field A.smooth w i)


-- @@ L81-87 verbatim
theorem wordField_map (L : V →L[ℝ] W) (A : SmoothL2Field V)
    {n : ℕ} (w : Fin n → Fin 3) :
    wordField (mapField L A) w = mapField L (wordField A w) := by
  apply field_ext
  funext x
  rw [wordField_field,mapField_field,wordField_field]
  exact wordDerivative_comp_clm axis L A.field A.smooth w x


-- @@ L89-94 verbatim
theorem wordField_add (A B : SmoothL2Field V) {n : ℕ} (w : Fin n → Fin 3) :
    wordField (addField A B) w = addField (wordField A w) (wordField B w) := by
  apply field_ext
  funext x
  rw [wordField_field,addField_field,wordField_field,wordField_field]
  exact wordDerivative_add axis A.field B.field A.smooth B.smooth w x


-- @@ L96-105 verbatim
theorem wordField_toLp_norm_le (A : SmoothL2Field V) {n : ℕ} (w : Fin n → Fin 3) :
    ‖(wordField A w).toLp‖ ≤ ‖A.jetLp n‖ := by
  rw [Lp.norm_def,eLpNorm_congr_ae (wordField A w).toLp_ae,
    norm_jetLp]
  apply ENNReal.toReal_mono (A.integrable n).eLpNorm_ne_top
  apply eLpNorm_mono (wordField A w).memLp.aestronglyMeasurable
  intro x
  rw [wordField_field]
  have h := (iteratedFDeriv ℝ n A.field x).le_opNorm (fun i => axis (w i))
  simpa only [wordDerivative,axis_norm,prod_const_one,mul_one] using h


-- @@ L107-109 verbatim
/-- Word size, given by `∑ n ∈ range (s+1), ∑ w : Fin n → Fin 3, ‖(wordField A w).toLp‖`. -/
def wordSize (s : ℕ) (A : SmoothL2Field V) : ℝ :=
  ∑ n ∈ range (s+1), ∑ w : Fin n → Fin 3, ‖(wordField A w).toLp‖


-- @@ L111-113 verbatim
/-- Word energy, given by `∑ n ∈ range (s+1), ∑ w : Fin n → Fin 3, ‖(wordField A w).toLp‖^2`. -/
def wordEnergy (s : ℕ) (A : SmoothL2Field V) : ℝ :=
  ∑ n ∈ range (s+1), ∑ w : Fin n → Fin 3, ‖(wordField A w).toLp‖^2


-- @@ L115-117 verbatim
/-- Word bound, given by `∀ n ≤ s, ∀ w : Fin n → Fin 3, ‖(wordField A w).toLp‖ ≤ M`. -/
def WordBound (s : ℕ) (M : ℝ) (A : SmoothL2Field V) : Prop :=
  ∀ n ≤ s, ∀ w : Fin n → Fin 3, ‖(wordField A w).toLp‖ ≤ M


-- @@ L119-120 verbatim
theorem wordEnergy_nonneg (s : ℕ) (A : SmoothL2Field V) : 0 ≤ wordEnergy s A :=
  sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => sq_nonneg _))


-- @@ L122-126 verbatim
theorem word_norm_sq_le_energy (A : SmoothL2Field V) {n s : ℕ} (hn : n ≤ s)
    (w : Fin n → Fin 3) : ‖(wordField A w).toLp‖^2 ≤ wordEnergy s A := by
  apply (single_le_sum (fun _ _ => sq_nonneg _) (mem_univ w)).trans
  exact single_le_sum (f := fun n => ∑ w : Fin n → Fin 3, ‖(wordField A w).toLp‖^2)
    (fun _ _ => sum_nonneg (fun _ _ => sq_nonneg _)) (mem_range.mpr (by omega))


-- @@ L128-132 verbatim
theorem wordBound_sqrt_energy (s : ℕ) (A : SmoothL2Field V) :
    WordBound s (Real.sqrt (wordEnergy s A)) A := by
  intro n hn w
  exact (Real.le_sqrt (norm_nonneg _) (wordEnergy_nonneg s A)).mpr
    (word_norm_sq_le_energy A hn w)


-- @@ L134-147 verbatim
theorem wordBound_wordField {s k : ℕ} {M : ℝ} {A : SmoothL2Field V}
    (h : WordBound (k + s) M A) (w : Fin k → Fin 3) : WordBound s M (wordField A w) := by
  induction k generalizing A with
  | zero => simpa only [wordField_zero,Nat.zero_add] using h
  | succ k ih =>
    have hd : WordBound (k+s) M (A.directionalField (axis (w (Fin.last k)))) := by
      intro n hn v
      rw [← wordField_snoc]
      exact h (n+1) (by omega) (Fin.snoc v (w (Fin.last k)))
    have he : wordField A w = wordField (A.directionalField (axis (w (Fin.last k)))) (Fin.init w)
        := by
      simpa only [Fin.snoc_init_self] using wordField_snoc A (Fin.init w) (w (Fin.last k))
    rw [he]
    exact ih hd (Fin.init w)


-- @@ L149-151 verbatim
theorem field_norm (A : SmoothL2Field V) :
    ‖A.toLp‖ = (eLpNorm A.field 2 (volume : Measure Space)).toReal := by
  rw [Lp.norm_def,eLpNorm_congr_ae A.toLp_ae]


-- @@ L153-157 verbatim
theorem mapField_norm_le (L : V →L[ℝ] W) (A : SmoothL2Field V) :
    ‖(mapField L A).toLp‖ ≤ ‖L‖*‖A.toLp‖ := by
  rw [toLp_mapField]
  exact ((L.compLpL 2 volume).le_opNorm A.toLp).trans
    (mul_le_mul_of_nonneg_right (L.norm_compLpL_le (p := 2) (μ := volume)) (norm_nonneg _))


-- @@ L159-159 verbatim
end EulerOrdinarySobolev
