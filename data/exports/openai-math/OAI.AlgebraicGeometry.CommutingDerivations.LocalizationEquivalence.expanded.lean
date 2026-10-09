import OAI.AlgebraicGeometry.CommutingDerivations.LocalizationSetup
import OAI.AlgebraicGeometry.CommutingDerivations.ParameterBridge


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-9 verbatim
/-!
Explicit maps between the ambient localization and the polynomial algebra
over Laurent coefficients, using the unrestricted reconstruction formulas.
-/

-- @@ L10-10 verbatim
noncomputable section

-- @@ L11-11 verbatim
namespace AbhyankarSathaye.CommutingDerivations

-- @@ L12-12 verbatim
open MvPolynomial


-- @@ L14-16 verbatim
def ambientToFree : R →+* RelativePlane :=
  eval₂Hom (C.comp (algebraMap ℂ LaurentCoefficients))
    (ParameterBridge.values LaurentCoefficients coefficientC coefficientD)


-- @@ L18-20 verbatim
@[simp] theorem ambientToFree_constant (a : ℂ) :
    ambientToFree (C a) = C (algebraMap ℂ LaurentCoefficients a) := by
  simp [ambientToFree]


-- @@ L22-24 verbatim
@[simp] theorem ambientToFree_h :
    ambientToFree h = ParameterBridge.freeH LaurentCoefficients coefficientC coefficientD := by
  simp [ambientToFree, h, ParameterBridge.values]

-- @@ L25-27 verbatim
@[simp] theorem ambientToFree_u :
    ambientToFree u = ParameterBridge.freeU LaurentCoefficients coefficientC coefficientD := by
  simp [ambientToFree, u, ParameterBridge.values]

-- @@ L28-30 verbatim
@[simp] theorem ambientToFree_v :
    ambientToFree v = ParameterBridge.freeV LaurentCoefficients coefficientC coefficientD := by
  simp [ambientToFree, v, ParameterBridge.values]

-- @@ L31-33 verbatim
@[simp] theorem ambientToFree_w :
    ambientToFree w = ParameterBridge.freeW LaurentCoefficients coefficientC coefficientD := by
  simp [ambientToFree, w, ParameterBridge.values]

-- @@ L34-35 verbatim
@[simp] theorem ambientToFree_x : ambientToFree x = ParameterBridge.freeX LaurentCoefficients coefficientD := by
  simpa [x] using (ParameterBridge.free_relations _ _ _ coefficient_unit).1

-- @@ L36-37 verbatim
@[simp] theorem ambientToFree_y : ambientToFree y = ParameterBridge.freeY LaurentCoefficients coefficientD := by
  simpa [y] using (ParameterBridge.free_relations _ _ _ coefficient_unit).2.1

-- @@ L38-39 verbatim
@[simp] theorem ambientToFree_s : ambientToFree s = ParameterBridge.freeS LaurentCoefficients coefficientD := by
  simpa [s] using (ParameterBridge.free_relations _ _ _ coefficient_unit).2.2


-- @@ L41-42 verbatim
@[simp] theorem ambientToFree_c : ambientToFree ambientC = C coefficientC := by
  simp [ambientC, F, p, ParameterBridge.freeH]


-- @@ L44-45 verbatim
@[simp] theorem ambientToFree_shiftX : ambientToFree shiftX = X 0 := by
  simp [shiftX, ParameterBridge.freeX]

-- @@ L46-47 verbatim
@[simp] theorem ambientToFree_shiftY : ambientToFree shiftY = X 1 := by
  simp [shiftY, ParameterBridge.freeY]


-- @@ L49-54 verbatim
@[simp] theorem coefficientMap_complex (a : ℂ) :
    coefficientMap (algebraMap ℂ LaurentCoefficients a) = loc (C a) := by
  rw [IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) LaurentCoefficients]
  change coefficientMap (algebraMap (Polynomial ℂ) LaurentCoefficients (Polynomial.C a)) = _
  simp [coefficientMap, polynomialCoefficientMap, loc,
    IsScalarTower.algebraMap_apply ℂ R LocalizedAmbient]


-- @@ L56-60 verbatim
def relativeForward : LocalizedAmbient →+* RelativePlane :=
  IsLocalization.Away.lift ambientC
    (show IsUnit (ambientToFree ambientC) by
      rw [ambientToFree_c]
      exact (IsUnit.of_mul_eq_one coefficientD coefficient_unit).map C)


-- @@ L62-63 verbatim
@[simp] theorem relativeForward_loc (f : R) : relativeForward (loc f) = ambientToFree f := by
  simp [relativeForward, loc]


-- @@ L65-73 verbatim
theorem relativeForward_coefficientMap :
    relativeForward.comp coefficientMap = (C : LaurentCoefficients →+* RelativePlane) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial ℂ))
  apply Polynomial.ringHom_ext
  · intro a
    simp [coefficientMap, polynomialCoefficientMap, relativeForward, ambientToFree,
      IsScalarTower.algebraMap_apply ℂ R LocalizedAmbient,
      IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) LaurentCoefficients]
  · simp [coefficientMap, polynomialCoefficientMap, coefficientC]


-- @@ L75-77 verbatim
@[simp] theorem relativeForward_coefficient (a : LaurentCoefficients) :
    relativeForward (coefficientMap a) = C a :=
  RingHom.congr_fun relativeForward_coefficientMap a


-- @@ L79-80 verbatim
@[simp] theorem relativeForward_d : relativeForward localD = C coefficientD := by
  rw [← coefficientMap_D, relativeForward_coefficient]


-- @@ L82-84 verbatim
@[simp] theorem relativeForward_alpha :
    relativeForward localAlpha = ParameterBridge.freeAlpha LaurentCoefficients coefficientC coefficientD := by
  simp [localAlpha, ParameterBridge.freeAlpha]

-- @@ L85-87 verbatim
@[simp] theorem relativeForward_beta :
    relativeForward localBeta = ParameterBridge.freeBeta LaurentCoefficients coefficientC coefficientD := by
  simp [localBeta, ParameterBridge.freeBeta]


-- @@ L89-90 verbatim
@[simp] theorem relativeForward_shiftX : relativeForward (loc shiftX) = X 0 := by
  simp [shiftX, ParameterBridge.freeX]

-- @@ L91-92 verbatim
@[simp] theorem relativeForward_shiftY : relativeForward (loc shiftY) = X 1 := by
  simp [shiftY, ParameterBridge.freeY]

-- @@ L93-102 verbatim
@[simp] theorem relativeForward_T : relativeForward localT = X 2 := by
  simpa [localT, ParameterBridge.freeU, ParameterBridge.freeV, ParameterBridge.freeW, ParameterBridge.freeG] using
    (inverse_parameter
      (ParameterBridge.freeH LaurentCoefficients coefficientC coefficientD)
      (ParameterBridge.freeX LaurentCoefficients coefficientD)
      (ParameterBridge.freeY LaurentCoefficients coefficientD)
      (ParameterBridge.freeS LaurentCoefficients coefficientD)
      (ParameterBridge.freeAlpha LaurentCoefficients coefficientC coefficientD)
      (ParameterBridge.freeBeta LaurentCoefficients coefficientC coefficientD) (X 2 : RelativePlane)
      (ParameterBridge.free_bezout LaurentCoefficients coefficientC coefficientD coefficient_unit))


-- @@ L104-110 verbatim
theorem relativeForward_backward :
    relativeForward.comp relativeBackward = RingHom.id RelativePlane := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · intro i
    fin_cases i <;> simp [localCoordinates]


-- @@ L112-114 verbatim
@[simp] theorem relativeBackward_freeS :
    relativeBackward (ParameterBridge.freeS LaurentCoefficients coefficientD) = loc s := by
  simpa [ParameterBridge.freeS, localCoordinates] using local_recover_s

-- @@ L115-117 verbatim
@[simp] theorem relativeBackward_freeX :
    relativeBackward (ParameterBridge.freeX LaurentCoefficients coefficientD) = loc x := by
  simp [ParameterBridge.freeX, localCoordinates, shiftX]

-- @@ L118-120 verbatim
@[simp] theorem relativeBackward_freeY :
    relativeBackward (ParameterBridge.freeY LaurentCoefficients coefficientD) = loc y := by
  simp [ParameterBridge.freeY, localCoordinates, shiftY]

-- @@ L121-123 verbatim
@[simp] theorem relativeBackward_freeH :
    relativeBackward (ParameterBridge.freeH LaurentCoefficients coefficientC coefficientD) = loc h := by
  simpa [ParameterBridge.freeH] using local_section.symm

-- @@ L124-126 verbatim
@[simp] theorem relativeBackward_freeAlpha :
    relativeBackward (ParameterBridge.freeAlpha LaurentCoefficients coefficientC coefficientD) = localAlpha := by
  simp [ParameterBridge.freeAlpha, localAlpha]

-- @@ L127-129 verbatim
@[simp] theorem relativeBackward_freeBeta :
    relativeBackward (ParameterBridge.freeBeta LaurentCoefficients coefficientC coefficientD) = localBeta := by
  simp [ParameterBridge.freeBeta, localBeta]


-- @@ L131-140 verbatim
theorem relativeBackward_free_original :
    relativeBackward (ParameterBridge.freeU LaurentCoefficients coefficientC coefficientD) = loc u ∧
    relativeBackward (ParameterBridge.freeV LaurentCoefficients coefficientC coefficientD) = loc v ∧
    relativeBackward (ParameterBridge.freeW LaurentCoefficients coefficientC coefficientD) = loc w := by
  have hx : (loc u)^3 + loc h * loc v = loc x := by simp [x]
  have hy : -(loc u)^2 + loc h * loc w = loc y := by simp [y]
  have hs : S (loc h) (loc u) (loc v) (loc w) = loc s := by simp [s]
  simpa [ParameterBridge.freeU, ParameterBridge.freeV, ParameterBridge.freeW, ParameterBridge.freeG, localCoordinates, localT] using
    original_reconstruction (loc h) (loc x) (loc y) (loc s) localAlpha localBeta
      (loc u) (loc v) (loc w) local_bezout hx hy hs


-- @@ L142-164 verbatim
theorem relativeBackward_forward :
    relativeBackward.comp relativeForward = RingHom.id LocalizedAmbient := by
  apply IsLocalization.ringHom_ext (Submonoid.powers ambientC)
  apply MvPolynomial.ringHom_ext
  · intro a
    change relativeBackward (relativeForward (loc (C a))) = loc (C a)
    rw [relativeForward_loc, ambientToFree_constant, relativeBackward_C, coefficientMap_complex]
  · intro i
    obtain ⟨hu, hv, hw⟩ := relativeBackward_free_original
    change relativeBackward (relativeForward (loc (X i))) = loc (X i)
    fin_cases i
    · change relativeBackward (relativeForward (loc h)) = loc h
      rw [relativeForward_loc, ambientToFree_h]
      exact relativeBackward_freeH
    · change relativeBackward (relativeForward (loc u)) = loc u
      rw [relativeForward_loc, ambientToFree_u]
      exact hu
    · change relativeBackward (relativeForward (loc v)) = loc v
      rw [relativeForward_loc, ambientToFree_v]
      exact hv
    · change relativeBackward (relativeForward (loc w)) = loc w
      rw [relativeForward_loc, ambientToFree_w]
      exact hw


-- @@ L166-169 verbatim
/-- Actual localized ring equivalence, with explicit maps and both composites. -/
def localizationRingEquiv : LocalizedAmbient ≃+* RelativePlane :=
  RingEquiv.ofRingHom relativeForward relativeBackward
    relativeForward_backward relativeBackward_forward


-- @@ L171-173 verbatim
/-- The algebra structure is exactly the specified map c ↦ F+1. -/
@[instance_reducible]
def relativeAlgebra : Algebra LaurentCoefficients LocalizedAmbient := coefficientMap.toAlgebra


-- @@ L175-181 verbatim
/-- Actual equivalence over the Laurent coefficient ring. -/
def localizationEquiv :
    letI := relativeAlgebra
    LocalizedAmbient ≃ₐ[LaurentCoefficients] RelativePlane :=
  letI := relativeAlgebra
  { localizationRingEquiv with
    commutes' := relativeForward_coefficient }


-- @@ L183-192 verbatim
/-- The same explicit equivalence also preserves the original complex scalars. -/
def localizationComplexEquiv : LocalizedAmbient ≃ₐ[ℂ] RelativePlane :=
  { localizationRingEquiv with
    commutes' := by
      intro a
      change relativeForward (algebraMap ℂ LocalizedAmbient a) =
        algebraMap ℂ RelativePlane a
      rw [IsScalarTower.algebraMap_apply ℂ R LocalizedAmbient]
      change relativeForward (loc (C a)) = C (algebraMap ℂ LaurentCoefficients a)
      rw [relativeForward_loc, ambientToFree_constant] }


-- @@ L194-197 verbatim
theorem relativeLocalizationContract_proved : RelativeLocalizationContract := by
  refine ⟨localizationRingEquiv, relativeForward_coefficient,
    relativeForward_shiftX, relativeForward_shiftY, relativeForward_T, ?_⟩
  rfl


-- @@ L199-199 verbatim
end AbhyankarSathaye.CommutingDerivations


-- @@ L201-201 verbatim
end


-- @@ L203-203 verbatim
end OAI
