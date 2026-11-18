import OAI.NumberTheory.DirichletL.Detector.Phase


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
namespace SevenEighths.ProbePhase

-- @@ L7-7 verbatim
open ActualEisensteinCubic ActualEisensteinCoordinates QuadraticGaussRay ConcreteTraceCRT

-- @@ L8-8 verbatim
open QuadraticAllOddCRT CanonicalRowCompletion CanonicalQuadraticSieve

-- @@ L9-9 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L11-14 verbatim
theorem quadraticRayValue_norm_one (r : EisensteinEPrimaryPhase.Coord)
    (hr : EisensteinEPrimaryPhase.odd r) : ‖quadraticRayValue r‖ = 1 := by
  rw [quadraticRayValue_eq_fourthRoot r hr]
  simp [fourthRoot]


-- @@ L16-28 verbatim
theorem G_norm_one (a : O) (ha : EisensteinEPrimaryPhase.odd (residue a))
    (hu : IsUnit (Ideal.Quotient.mk cubicTwoIdeal a)) : ‖G a‖ = 1 := by
  have hχ := congrArg
    (fun η : MulChar (O ⧸ cubicTwoIdeal) O => η (Ideal.Quotient.mk cubicTwoIdeal a))
    (cubicChar_pow_three cubicTwoIdeal cubicTwoIdeal_good)
  simp only [MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), MulChar.one_apply hu] at hχ
  have hc := congrArg eisEmbedding hχ
  simp only [map_pow, map_one] at hc
  have hn := Complex.norm_eq_one_of_pow_eq_one hc (by decide : (3 : ℕ) ≠ 0)
  change ‖fixedGValue (residue a)‖ = 1
  simp only [fixedGValue, ← fixed_two_mk_eq_residue_lift, norm_mul, norm_inv,
    hn, inv_one, one_mul]
  exact quadraticRayValue_norm_one _ ha


-- @@ L30-39 verbatim
theorem cubicTwo_isUnit_of_odd (a : O)
    (ha : EisensteinEPrimaryPhase.odd (residue a)) :
    IsUnit (Ideal.Quotient.mk cubicTwoIdeal a) := by
  let : Field (O ⧸ cubicTwoIdeal) := Ideal.Quotient.field _
  apply isUnit_iff_ne_zero.mpr
  intro hz
  have hm := Ideal.Quotient.eq_zero_iff_mem.mp hz
  have hd : (2 : O) ∣ a := by
    simpa only [cubicTwoIdeal, Ideal.mem_span_singleton, neg_dvd] using hm
  exact ((odd_residue_iff_not_two_dvd a).mp ha) hd


-- @@ L41-43 verbatim
theorem G_norm_one_of_odd (a : O)
    (ha : EisensteinEPrimaryPhase.odd (residue a)) : ‖G a‖ = 1 :=
  G_norm_one a ha (cubicTwo_isUnit_of_odd a ha)


-- @@ L45-50 verbatim
theorem G_conjugate_cancel (a : O) (ha : EisensteinEPrimaryPhase.odd (residue a))
    (hu : IsUnit (Ideal.Quotient.mk cubicTwoIdeal a)) : star (G a) * G a = 1 := by
  have hn := G_norm_one a ha hu
  have hs : star (G a) = (G a)⁻¹ := (Complex.inv_eq_conj hn).symm
  rw [hs]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mp (by rw [hn]; norm_num))


-- @@ L52-61 verbatim
theorem completed_phase_cancel (c n : O)
    (hc : EisensteinEPrimaryPhase.odd (residue c))
    (hn : EisensteinEPrimaryPhase.odd (residue n))
    (hu : IsUnit (Ideal.Quotient.mk cubicTwoIdeal (c * n ^ 3))) :
    star (G (c * n ^ 3)) * (G c * reciprocitySign c n * G (n ^ 3)) = 1 := by
  rw [← G_completed_index c n hc hn]
  apply G_conjugate_cancel _ _ hu
  rw [show c * n ^ 3 = c * ((n * n) * n) by ring]
  simp only [residue_mul]
  exact odd_mul _ _ hc (odd_mul _ _ (odd_mul _ _ hn hn) hn)


-- @@ L63-63 verbatim
end SevenEighths.ProbePhase

-- @@ L64-64 verbatim
end


-- @@ L66-66 verbatim
end OAI
