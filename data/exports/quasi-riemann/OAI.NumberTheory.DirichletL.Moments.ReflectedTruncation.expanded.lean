import OAI.NumberTheory.DirichletL.Moments.ReflectedSeries


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical BigOperators SchwartzMap

-- @@ L7-7 verbatim
namespace SevenEighths.CenteredMomentReflectedTruncation

-- @@ L8-8 verbatim
open HeckeFamily CenteredMomentSectorLocalization CenteredMomentReflectedAnnuli

-- @@ L9-9 verbatim
open CenteredMomentComparisonReflection CenteredMomentReflectionDeletion

-- @@ L10-10 verbatim
open CenteredMomentReflectedSeries EisensteinSchwartzPoisson

-- @@ L11-11 verbatim
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal


-- @@ L13-49 verbatim
theorem normalized_subseries (η : Character) (F : ℝ→ℂ) (hF : DecayTwo F)
    (Y : ℝ) (hY : 0<Y) (A : Set ℤ) :
    Summable (fun n : ℤ=>if n∈A then (Real.sqrt (dyadicScale n):ℂ)*
      HeckeDyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0 else 0) ∧
    HeckeDyadic.polynomial η false
      (fun x=>(∑'n : ℤ,if n∈A then dyadicWeight n x else 0:ℝ)*F x) Y 0 0=
      ∑'n : ℤ,if n∈A then (Real.sqrt (dyadicScale n):ℂ)*
        HeckeDyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0 else 0 := by
  have hs := (dyadic_ideal_absolute η F hF Y hY).of_norm
  have hi : Summable (fun p : NI×ℤ=>if p.2∈A then dyadicIdealTerm η F Y p.1 p.2 else 0) :=
    hs.indicator {p : NI×ℤ | p.2∈A}
  have he (n : ℤ) : (if n∈A then (Real.sqrt (dyadicScale n):ℂ)*
      HeckeDyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0 else 0)=
      (Real.sqrt Y:ℂ)⁻¹*∑'I : NI,if n∈A then dyadicIdealTerm η F Y I n else 0 := by
    split_ifs with hn
    · rw [←normalized_annular_term η F (dyadicScale n) Y (dyadicScale_pos n) hY,
        polynomial_plain _ _ _ hY]
      congr 1
      apply tsum_congr
      intro I
      simp only [dyadicIdealTerm,dyadicWeight]
      ring
    · simp
  simp_rw [he]
  refine ⟨hi.prod_symm.prod.mul_left _,?_⟩
  rw [tsum_mul_left,polynomial_plain η _ Y hY]
  congr 1
  rw [hi.tsum_comm]
  apply tsum_congr
  intro I
  have ht (n : ℤ) : (if n∈A then dyadicIdealTerm η F Y I n else 0)=
      ((if n∈A then dyadicWeight n ((I.val.absNorm:ℝ)/Y) else 0:ℝ):ℂ)*
        (idealCoeff η I.val*F ((I.val.absNorm:ℝ)/Y)) := by
    split_ifs <;> simp only [dyadicIdealTerm,Complex.ofReal_zero,zero_mul] ; ring
  simp_rw [ht]
  rw [tsum_mul_right,←Complex.ofReal_tsum]
  ring


-- @@ L51-52 verbatim
def retainedAnnuli (R Y : ℝ) (hY : 0<Y) : Finset ℤ :=
  (finite_retained_above R (Y⁻¹) (inv_pos.mpr hY)).toFinset


-- @@ L54-56 verbatim
lemma retainedAnnuli_mem (R Y : ℝ) (hY : 0<Y) (n : ℤ) :
    n∈retainedAnnuli R Y hY ↔ Retained R n ∧ ∃q : ℝ,Y⁻¹≤q ∧ dyadicWeight n q≠0 := by
  exact (finite_retained_above R (Y⁻¹) (inv_pos.mpr hY)).mem_toFinset


-- @@ L58-62 verbatim
lemma original_norm_lower (I : NI) (Y : ℝ) (hY : 0<Y) :
    Y⁻¹≤(I.val.absNorm:ℝ)/Y := by
  have hn : (1:ℝ)≤I.val.absNorm := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property))
  simpa only [one_div] using div_le_div_of_nonneg_right hn hY.le


-- @@ L64-87 verbatim
theorem retained_finite_series (η : Character) (F : ℝ→ℂ) (hF : DecayTwo F)
    (R Y : ℝ) (hY : 0<Y) :
    HeckeDyadic.polynomial η false (fun x=>(retainedWeight R x:ℂ)*F x) Y 0 0=
      ∑n∈retainedAnnuli R Y hY,(Real.sqrt (dyadicScale n):ℂ)*
        HeckeDyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0 := by
  have hh := (normalized_subseries η F hF Y hY {n | Retained R n}).2
  change HeckeDyadic.polynomial η false (fun x=>(retainedWeight R x:ℂ)*F x) Y 0 0=_ at hh
  rw [hh,tsum_eq_sum (s:=retainedAnnuli R Y hY)]
  · apply Finset.sum_congr rfl
    intro n hn
    simp only [Set.mem_ofPred_eq,ite_eq_left ((retainedAnnuli_mem R Y hY n).mp hn).1]
  · intro n hn
    split_ifs with hr
    · rw [←normalized_annular_term η F (dyadicScale n) Y (dyadicScale_pos n) hY,
        polynomial_plain _ _ _ hY]
      have hz (I : NI) : dyadicWeight n ((I.val.absNorm:ℝ)/Y)=0 := by
        by_contra hne
        exact hn ((retainedAnnuli_mem R Y hY n).mpr ⟨hr,_,original_norm_lower I Y hY,hne⟩)
      have he (I : NI) : idealCoeff η I.val*
          ((annulus (((I.val.absNorm:ℝ)/Y)/dyadicScale n):ℂ)*F ((I.val.absNorm:ℝ)/Y))=0 := by
        change idealCoeff η I.val*((dyadicWeight n ((I.val.absNorm:ℝ)/Y):ℂ)*F _)=0
        rw [hz,Complex.ofReal_zero,zero_mul,mul_zero]
      simp_rw [he,tsum_zero,mul_zero]
    · rfl


-- @@ L89-89 verbatim
end SevenEighths.CenteredMomentReflectedTruncation


-- @@ L91-91 verbatim
end


-- @@ L93-93 verbatim
end OAI
