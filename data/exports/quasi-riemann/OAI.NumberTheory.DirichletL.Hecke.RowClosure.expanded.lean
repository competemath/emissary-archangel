import OAI.NumberTheory.DirichletL.Hecke.IdealOperations


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical

-- @@ L7-7 verbatim
namespace SevenEighths.HeckeRowClosure

-- @@ L8-8 verbatim
open HeckeFamily

-- @@ L9-9 verbatim
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda


-- @@ L11-36 verbatim
theorem periodic_of_primary (M : Ideal O)
    (hM : M ≤ Ideal.span {λ₀ ^ 2}) (G F : O →* ℂ)
    (hF : CanonicalCoefficientClass.FactorsModulo M F)
    (hu : ∀ (u : Oˣ) x, G ((u : O) * x) = G x)
    (hz : ∀ x, λ₀ ∣ x → G x = 0)
    (hagree : ∀ x, λ₀ ^ 2 ∣ x - 1 → G x = F x) :
    CanonicalCoefficientClass.FactorsModulo M G := by
  intro x y hxy
  have hdiff : λ₀ ^ 2 ∣ x - y := Ideal.mem_span_singleton.mp (hM hxy)
  have hdiff' : λ₀ ∣ x - y := (dvd_pow_self λ₀ (by decide : 2 ≠ 0)).trans hdiff
  by_cases hx : λ₀ ∣ x
  · have hy : λ₀ ∣ y := by
      convert dvd_sub hx hdiff' using 1 ; ring
    rw [hz x hx, hz y hy]
  · have hg := PrimaryIdealUnitReindex.primaryGenerator_span_ne_zero_iff x |>.mpr hx
    have hspec := CompletedGauss.primaryGenerator_spec (Ideal.span {x}) hg
    obtain ⟨u, hu'⟩ := Ideal.span_singleton_eq_span_singleton.mp hspec.1.symm
    have hp : λ₀ ^ 2 ∣ (u : O) * x - 1 := by
      have hp' : λ₀ ^ 2 ∣ CompletedGauss.primaryGenerator (Ideal.span {x}) - 1 := hspec.2
      rwa [mul_comm, hu']
    have hq : λ₀ ^ 2 ∣ (u : O) * y - 1 := by
      have hd := hdiff.trans (dvd_mul_left (x-y) (u : O))
      convert dvd_sub hp hd using 1 ; ring
    rw [← hu u x, ← hu u y, hagree _ hp, hagree _ hq]
    apply hF
    simpa only [mul_sub] using M.mul_mem_left (u : O) hxy


-- @@ L38-44 verbatim
def quotientRow (M : Ideal O) (G : O →* ℂ)
    (hG : CanonicalCoefficientClass.FactorsModulo M G) : (O ⧸ M) →* ℂ where
  toFun x := Quotient.liftOn' x G (fun a b hab => hG a b (M.quotientRel_def.mp hab))
  map_one' := G.map_one
  map_mul' x y := by
    refine Quotient.inductionOn₂' x y ?_
    exact G.map_mul


-- @@ L46-48 verbatim
@[simp] theorem quotientRow_mk (M : Ideal O) (G : O →* ℂ)
    (hG : CanonicalCoefficientClass.FactorsModulo M G) (z : O) :
    quotientRow M G hG (Ideal.Quotient.mk M z) = G z := rfl


-- @@ L50-52 verbatim
def residueRow (M : Ideal O) (G : O →* ℂ)
    (hG : CanonicalCoefficientClass.FactorsModulo M G) : MulChar (O ⧸ M) ℂ :=
  MulChar.ofUnitHom (Units.map (quotientRow M G hG))


-- @@ L54-66 verbatim
theorem residueRow_mk (M : Ideal O) (G : O →* ℂ)
    (hG : CanonicalCoefficientClass.FactorsModulo M G) (z : O) :
    residueRow M G hG (Ideal.Quotient.mk M z) =
      if IsUnit (Ideal.Quotient.mk M z) then G z else 0 := by
  by_cases hz : IsUnit (Ideal.Quotient.mk M z)
  · obtain ⟨u, hu⟩ := hz
    rw [ite_eq_left (hu ▸ u.isUnit), ← hu]
    change MulChar.ofUnitHom (Units.map (quotientRow M G hG)) (u : O ⧸ M) = G z
    rw [MulChar.ofUnitHom_coe]
    change quotientRow M G hG (u : O ⧸ M) = G z
    rw [hu, quotientRow_mk]
  · rw [ite_eq_right hz]
    exact MulChar.map_nonunit _ hz


-- @@ L68-73 verbatim
def rowCharacter (M : Ideal O) (hM : M ≠ ⊥) (G : O →* ℂ)
    (hG : CanonicalCoefficientClass.FactorsModulo M G)
    (hu : ∀ u : Oˣ, G (u : O) = 1) : Character :=
  Character.ofResidue M hM (residueRow M G hG) (by
    intro u
    rw [residueRow_mk, ite_eq_left (u.isUnit.map (Ideal.Quotient.mk M)), hu])


-- @@ L75-79 verbatim
theorem elementCoeff_rowCharacter (M : Ideal O) (hM : M ≠ ⊥) (G : O →* ℂ)
    (hG : CanonicalCoefficientClass.FactorsModulo M G)
    (hu : ∀ u : Oˣ, G (u : O) = 1) (z : O) :
    elementCoeff (rowCharacter M hM G hG hu) z =
      if IsUnit (Ideal.Quotient.mk M z) then G z else 0 := residueRow_mk M G hG z


-- @@ L81-84 verbatim
def elementHom (η : Character) : O →* ℂ where
  toFun := elementCoeff η
  map_one' := elementCoeff_one η
  map_mul' := elementCoeff_mul η


-- @@ L86-90 verbatim
theorem elementHom_periodic (η : Character) :
    CanonicalCoefficientClass.FactorsModulo η.modulus (elementHom η) := by
  intro x y hxy
  apply congrArg η.residue
  exact Ideal.Quotient.eq.mpr hxy


-- @@ L92-95 verbatim
theorem elementHom_norm (η : Character) (x : O) : ‖elementHom η x‖ ≤ 1 := by
  let : Finite (O ⧸ η.modulus) := Ring.HasFiniteQuotients.finiteQuotient η.modulus_ne_bot
  let : Fintype (O ⧸ η.modulus) := Fintype.ofFinite _
  exact FiniteRayExpansion.norm_char_le_one η.residue _


-- @@ L97-101 verbatim
theorem rowTwist_unit_mul (η : Character) (m f z : O) (u : Oˣ) (n : O) :
    CanonicalRowCompletion.rowTwist (elementHom η) m f z ((u : O)*n) =
      CanonicalRowCompletion.rowTwist (elementHom η) m f z n := by
  change elementCoeff η ((u : O)*n) * CanonicalRowCompletion.idealRowHom (m^6*f^4*z) (Ideal.span {(u : O)*n}) = elementCoeff η n * CanonicalRowCompletion.idealRowHom (m^6*f^4*z) (Ideal.span {n})
  rw [elementCoeff_unit_mul, Ideal.span_singleton_mul_left_unit u.isUnit]


-- @@ L103-105 verbatim
theorem rowTwist_unit (η : Character) (m f z : O) (u : Oˣ) :
    CanonicalRowCompletion.rowTwist (elementHom η) m f z (u : O) = 1 := by
  simpa using rowTwist_unit_mul η m f z u 1


-- @@ L107-128 verbatim
theorem rowTwist_periodic (η : Character) (m f z : O)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hr : CanonicalQuadraticSieve.Supported (Ideal.span {r}))
    (hpr : λ₀ ^ 2 ∣ r-1) (hx : f^4*z = (u : O)*λ₀^a*(2 : O)^b*r) :
    CanonicalCoefficientClass.FactorsModulo
      (η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * Ideal.span {r})
      (CanonicalRowCompletion.rowTwist (elementHom η) m f z) := by
  refine periodic_of_primary _ ?_ _
    (CanonicalRowCompletion.actualPeriodicRow (elementHom η) m u a b r hr)
    (CanonicalRowCompletion.actualPeriodicRow_periodic _ _ (elementHom_periodic η) _ _ _ _ _ hr)
    (rowTwist_unit_mul η m f z) ?_ ?_
  · have hd3 : λ₀ ^ 2 ∣ (3 : O) := ActualEisensteinCubic.lambda_sq_dvd_three
    have hd72 : λ₀ ^ 2 ∣ (72 : O) := hd3.trans ⟨24, by norm_num⟩
    exact (Ideal.mul_le_left.trans Ideal.mul_le_right).trans
      ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_span_singleton.mpr hd72))
  · intro n hn
    apply CanonicalRowCompletion.rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2
    intro hs
    exact ((CanonicalQuadraticSieve.supported_span_iff n).mp hs).1 hn
  · exact CanonicalRowCompletion.rowTwist_eq_actualPeriodicRow_primary
      _ _ _ _ hmLam hm2 u a b r hr hpr hx


-- @@ L130-145 verbatim
theorem rowTwist_nonzero_coprime (η : Character) (m f z n : O)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (hn : CanonicalRowCompletion.rowTwist (elementHom η) m f z n ≠ 0) :
    CanonicalQuadraticSieve.Supported (Ideal.span {n}) ∧ IsCoprime n (m^6*f^4*z) := by
  have hs : CanonicalQuadraticSieve.Supported (Ideal.span {n}) := by
    by_contra h
    exact hn (CanonicalRowCompletion.rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 h)
  refine ⟨hs, ?_⟩
  have hrow : CanonicalRowCompletion.idealRowHom (m^6*f^4*z) (Ideal.span {n}) ≠ 0 :=
    right_ne_zero_of_mul hn
  have hp := pow_ne_zero 6 hrow
  rw [← CanonicalRowCompletion.idealRowHom_argument_pow _ _ _ hs,
    CanonicalRowCompletion.idealRowHom_sixth_mask _ _ hs] at hp
  by_cases hc : IsCoprime (Ideal.span {n}) (Ideal.span {m^6*f^4*z})
  · exact (Ideal.isCoprime_span_singleton_iff _ _).mp hc
  · simp [hc] at hp


-- @@ L147-172 verbatim
theorem rowTwist_nonzero_unit (η : Character) (m f z n : O)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hx : f^4*z = (u : O)*λ₀^a*(2 : O)^b*r)
    (hn : CanonicalRowCompletion.rowTwist (elementHom η) m f z n ≠ 0) :
    IsUnit (Ideal.Quotient.mk
      (η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * Ideal.span {r}) n) := by
  obtain ⟨hs, hc⟩ := rowTwist_nonzero_coprime η m f z n hmLam hm2 hn
  have hm : IsCoprime n m := hc.of_isCoprime_of_dvd_right ⟨m^5*f^4*z, by ring⟩
  have hr : IsCoprime n r := hc.of_isCoprime_of_dvd_right
    ⟨m^6*((u : O)*λ₀^a*(2 : O)^b), by
      rw [show m^6*f^4*z = m^6*(f^4*z) by ring, hx]; ring⟩
  have h2 := hm.of_isCoprime_of_dvd_right hm2
  have h9 := (ShortDraftCRT.nine_coprime_of_not_lambda_dvd n
    ((CanonicalQuadraticSieve.supported_span_iff n).mp hs).1).symm
  have h72 : IsCoprime n (72 : O) := by
    convert (h2.pow_right : IsCoprime n ((2 : O)^3)).mul_right h9 using 1 ; norm_num
  have he : elementCoeff η n ≠ 0 := left_ne_zero_of_mul hn
  have hη : IsCoprime (Ideal.span {n}) η.modulus := by
    apply (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp
    exact MulChar.apply_ne_zero_iff.mp he
  rw [IdealCharacter.isUnit_mk_iff_isCoprime, IsCoprime.mul_right_iff,
    IsCoprime.mul_right_iff, IsCoprime.mul_right_iff]
  exact ⟨⟨⟨hη, (Ideal.isCoprime_span_singleton_iff _ _).mpr hm⟩,
    (Ideal.isCoprime_span_singleton_iff _ _).mpr h72⟩,
    (Ideal.isCoprime_span_singleton_iff _ _).mpr hr⟩


-- @@ L174-190 verbatim
theorem exists_row_character (η : Character) (m f z : O)
    (hm : m ≠ 0) (hf : f ≠ 0) (hz : z ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m) :
    ∃ χ : Character, ∀ n : O, elementCoeff χ n =
      CanonicalRowCompletion.rowTwist (elementHom η) m f z n := by
  obtain ⟨u, a, b, r, hr, hpr, hx, hM, _, _, _⟩ :=
    CanonicalRowCompletion.exists_actual_periodic_row (elementHom η) η.modulus
      η.modulus_ne_bot (elementHom_periodic η) (elementHom_norm η) m f z hm hf hz hmLam hm2
  let M := η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * Ideal.span {r}
  let G := CanonicalRowCompletion.rowTwist (elementHom η) m f z
  have hG := rowTwist_periodic η m f z hmLam hm2 u a b r hr hpr hx
  refine ⟨rowCharacter M hM G hG (rowTwist_unit η m f z), ?_⟩
  intro n
  rw [elementCoeff_rowCharacter]
  split_ifs with hn
  · rfl
  · exact Eq.symm (not_not.mp (fun h => hn (rowTwist_nonzero_unit η m f z n hmLam hm2 u a b r hx h)))


-- @@ L192-194 verbatim
def rowConductorBound (η : Character) (m f z : O) : ℕ :=
  η.modulus.absNorm * (Ideal.span {m}).absNorm * (Ideal.span {(72 : O)}).absNorm *
    ((Ideal.span {f}).absNorm ^ 4 * (Ideal.span {z}).absNorm)


-- @@ L196-214 verbatim
theorem row_modulus_norm_le (η : Character) (m f z : O)
    (hf : f ≠ 0) (hz : z ≠ 0) (u : Oˣ) (a b : ℕ) (r : O)
    (hx : f^4*z = (u : O)*λ₀^a*(2 : O)^b*r) :
    (η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * Ideal.span {r}).absNorm ≤
      rowConductorBound η m f z := by
  have hprod : (Ideal.span {f^4*z} : Ideal O) ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero (pow_ne_zero _ hf) hz)
  let : Finite (O ⧸ Ideal.span {f^4*z}) := Ring.HasFiniteQuotients.finiteQuotient hprod
  have hle : (Ideal.span {f^4*z} : Ideal O) ≤ Ideal.span {r} := by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    apply Ideal.mem_span_singleton.mpr
    exact ⟨(u : O)*λ₀^a*(2 : O)^b, by rw [hx]; ring⟩
  have hn := FiniteConductor.absNorm_le_of_le hle
  have heq : (Ideal.span {f^4*z} : Ideal O) = (Ideal.span {f})^4 * Ideal.span {z} := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton]
  rw [heq, map_mul, map_pow] at hn
  simpa only [rowConductorBound, map_mul] using
    Nat.mul_le_mul_left
      (η.modulus.absNorm * (Ideal.span {m}).absNorm * (Ideal.span {(72 : O)}).absNorm) hn


-- @@ L216-234 verbatim
theorem exists_row_character_with_conductor (η : Character) (m f z : O)
    (hm : m ≠ 0) (hf : f ≠ 0) (hz : z ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m) :
    ∃ χ : Character, χ.modulus.absNorm ≤ rowConductorBound η m f z ∧
      ∀ n : O, elementCoeff χ n =
        CanonicalRowCompletion.rowTwist (elementHom η) m f z n := by
  obtain ⟨u, a, b, r, hr, hpr, hx, hM, _, _, _⟩ :=
    CanonicalRowCompletion.exists_actual_periodic_row (elementHom η) η.modulus
      η.modulus_ne_bot (elementHom_periodic η) (elementHom_norm η) m f z hm hf hz hmLam hm2
  let M := η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * Ideal.span {r}
  let G := CanonicalRowCompletion.rowTwist (elementHom η) m f z
  have hG := rowTwist_periodic η m f z hmLam hm2 u a b r hr hpr hx
  refine ⟨rowCharacter M hM G hG (rowTwist_unit η m f z),
    row_modulus_norm_le η m f z hf hz u a b r hx, ?_⟩
  intro n
  rw [elementCoeff_rowCharacter]
  split_ifs with hn
  · rfl
  · exact Eq.symm (not_not.mp (fun h => hn (rowTwist_nonzero_unit η m f z n hmLam hm2 u a b r hx h)))


-- @@ L236-249 verbatim
theorem idealCoeff_eq_row (η χ : Character) (m f z : O)
    (heq : ∀ n : O, elementCoeff χ n =
      CanonicalRowCompletion.rowTwist (elementHom η) m f z n) (I : Ideal O) :
    idealCoeff χ I = idealCoeff η I * CanonicalRowCompletion.idealRowHom (m^6*f^4*z) I := by
  by_cases hI : I = 0
  · subst I
    rw [map_zero, map_zero, zero_mul]
  let n := ConcretePrimeRowBridge.idealGenerator I
  have hn : n ≠ 0 := ConcretePrimeRowBridge.idealGenerator_ne_zero I hI
  have hs : Ideal.span {n} = I := ConcretePrimeRowBridge.span_idealGenerator I
  rw [← hs, idealCoeff_span χ hn, heq]
  change elementCoeff η n * _ = idealCoeff η (Ideal.span {n}) * _
  rw [idealCoeff_span η hn]
  rfl


-- @@ L251-262 verbatim
theorem exists_primitive_row (η : Character) (m f z : O)
    (hm : m ≠ 0) (hf : f ≠ 0) (hz : z ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m) :
    ∃ χ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      ψ.modulus.absNorm ≤ rowConductorBound η m f z ∧
      (∀ I : Ideal O, idealCoeff χ I =
        idealCoeff η I * CanonicalRowCompletion.idealRowHom (m^6*f^4*z) I) ∧
      (∀ I : Ideal O, idealCoeff χ I =
        if IsCoprime I χ.modulus then idealCoeff ψ I else 0) := by
  obtain ⟨χ, hnorm, heq⟩ := exists_row_character_with_conductor η m f z hm hf hz hmLam hm2
  obtain ⟨ψ, _, hp, hn, hmask⟩ := exists_primitive_character χ
  exact ⟨χ, ψ, hp, hn.trans hnorm, idealCoeff_eq_row η χ m f z heq, hmask⟩


-- @@ L264-264 verbatim
end SevenEighths.HeckeRowClosure


-- @@ L266-266 verbatim
end


-- @@ L268-268 verbatim
end OAI
