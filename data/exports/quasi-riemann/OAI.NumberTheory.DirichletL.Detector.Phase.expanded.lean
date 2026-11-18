import OAI.NumberTheory.DirichletL.Foundation


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
namespace SevenEighths.ProbePhase

-- @@ L7-7 verbatim
open ActualEisensteinCubic ActualEisensteinCoordinates QuadraticGaussRay ConcreteTraceCRT

-- @@ L8-8 verbatim
open QuadraticAllOddCRT

-- @@ L9-9 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L11-11 verbatim
def G (a : O) : ℂ := fixedGQuotientValue (Ideal.Quotient.mk (Ideal.span {(4 : O)}) a)


-- @@ L13-14 verbatim
def reciprocitySign (a b : O) : ℂ :=
  (quadraticRaySign (residue a) (residue b) : ℂ)


-- @@ L16-25 verbatim
theorem G_mul (a b : O)
    (ha : EisensteinEPrimaryPhase.odd (residue a))
    (hb : EisensteinEPrimaryPhase.odd (residue b)) :
    G (a * b) = G a * G b * reciprocitySign a b := by
  change fixedGValue (residue (a * b)) = fixedGValue (residue a) * fixedGValue (residue b) * reciprocitySign a b
  simp only [fixedGValue, ← fixed_two_mk_eq_residue_lift]
  simp only [map_mul, mul_inv_rev, residue_mul]
  rw [quadraticRayValue_mul _ _ ha hb]
  unfold reciprocitySign
  ring


-- @@ L27-29 verbatim
theorem reciprocitySign_mul_right (a b c : O) :
    reciprocitySign a (b * c) = reciprocitySign a b * reciprocitySign a c := by
  simp only [reciprocitySign, residue_mul, quadraticRaySign_mul_right, Int.cast_mul]


-- @@ L31-36 verbatim
theorem reciprocitySign_sq (a b : O)
    (ha : EisensteinEPrimaryPhase.odd (residue a))
    (hb : EisensteinEPrimaryPhase.odd (residue b)) :
    reciprocitySign a b ^ 2 = 1 := by
  unfold reciprocitySign
  exact_mod_cast quadraticRaySign_sq (residue a) (residue b) ha hb


-- @@ L38-47 verbatim
theorem reciprocitySign_cube_right (a b : O)
    (ha : EisensteinEPrimaryPhase.odd (residue a))
    (hb : EisensteinEPrimaryPhase.odd (residue b)) :
    reciprocitySign a (b ^ 3) = reciprocitySign a b := by
  rw [show b ^ 3 = b ^ 2 * b by ring, reciprocitySign_mul_right,
    pow_two, reciprocitySign_mul_right]
  have hs := reciprocitySign_sq a b ha hb
  calc
    _ = reciprocitySign a b ^ 2 * reciprocitySign a b := by ring
    _ = reciprocitySign a b := by rw [hs, one_mul]


-- @@ L49-57 verbatim
theorem G_completed_index (c n : O)
    (hc : EisensteinEPrimaryPhase.odd (residue c))
    (hn : EisensteinEPrimaryPhase.odd (residue n)) :
    G (c * n ^ 3) = G c * reciprocitySign c n * G (n ^ 3) := by
  have hn3 : EisensteinEPrimaryPhase.odd (residue (n ^ 3)) := by
    rw [show n ^ 3 = (n * n) * n by ring, residue_mul, residue_mul]
    exact QuadraticAllOddCRT.odd_mul _ _ (QuadraticAllOddCRT.odd_mul _ _ hn hn) hn
  rw [G_mul c (n ^ 3) hc hn3, reciprocitySign_cube_right c n hc hn]
  ring


-- @@ L59-67 verbatim
theorem quadraticRayValue_cube (r : EisensteinEPrimaryPhase.Coord)
    (hr : EisensteinEPrimaryPhase.odd r) :
    quadraticRayValue (EisensteinEPrimaryPhase.mul
      (EisensteinEPrimaryPhase.mul r r) r) = quadraticRayValue r := by
  have he : ∀ r : EisensteinEPrimaryPhase.Coord, EisensteinEPrimaryPhase.odd r →
      quadraticRayExponent (EisensteinEPrimaryPhase.mul
        (EisensteinEPrimaryPhase.mul r r) r) = quadraticRayExponent r := by decide
  rw [quadraticRayValue_eq_fourthRoot _ (odd_mul _ _ (odd_mul _ _ hr hr) hr),
    he r hr, ← quadraticRayValue_eq_fourthRoot r hr]


-- @@ L69-82 verbatim
theorem G_cube (a : O) (ha : EisensteinEPrimaryPhase.odd (residue a))
    (hu : IsUnit (Ideal.Quotient.mk cubicTwoIdeal a)) :
    G (a ^ 3) = quadraticRayValue (residue a) := by
  have hχ := congrArg
    (fun η : MulChar (O ⧸ cubicTwoIdeal) O => η (Ideal.Quotient.mk cubicTwoIdeal a))
    (cubicChar_pow_three cubicTwoIdeal cubicTwoIdeal_good)
  simp only [MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), MulChar.one_apply hu] at hχ
  have hc := congrArg eisEmbedding hχ
  simp only [map_pow, map_one] at hc
  change fixedGValue (residue (a ^ 3)) = quadraticRayValue (residue a)
  simp only [fixedGValue, ← fixed_two_mk_eq_residue_lift]
  simp only [map_pow, hc, inv_one, one_mul]
  rw [show a ^ 3 = (a * a) * a by ring, residue_mul, residue_mul]
  exact quadraticRayValue_cube (residue a) ha


-- @@ L84-84 verbatim
end SevenEighths.ProbePhase

-- @@ L85-85 verbatim
end


-- @@ L87-87 verbatim
end OAI
