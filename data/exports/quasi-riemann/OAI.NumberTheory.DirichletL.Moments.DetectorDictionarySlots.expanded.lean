import OAI.NumberTheory.DirichletL.Moments.DetectorDictionary
import OAI.NumberTheory.DirichletL.Hecke.DetectorRelativePrime


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators ComplexConjugate


-- @@ L9-9 verbatim
namespace SevenEighths.CenteredMomentDetectorDictionary

-- @@ L10-10 verbatim
open HeckeFamily HeckeDyadic HeckeRowClosure CanonicalRowCompletion

-- @@ L11-11 verbatim
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot

-- @@ L12-12 verbatim
open HeckeDetectorRelativePrime

-- @@ L13-13 verbatim
local notation "O" => HeckeFamily.O


-- @@ L15-16 verbatim
def physicalSlotCoefficient (η : Character) (W : ℝ→ℂ) (D : ℝ) (z : ℂ) (P : Ideal O) : ℂ :=
  idealCoeff η.inverse P*conj (W ((P.absNorm:ℝ)/D)*(((P.absNorm:ℝ)/D:ℝ):ℂ)^(z-1))


-- @@ L18-21 verbatim
lemma physicalSlotCoefficient_norm (η : Character) (W : ℝ→ℂ) (D : ℝ) (z : ℂ) (P : Ideal O) :
    ‖physicalSlotCoefficient η W D z P‖≤‖W ((P.absNorm:ℝ)/D)*(((P.absNorm:ℝ)/D:ℝ):ℂ)^(z-1)‖ := by
  rw [physicalSlotCoefficient,norm_mul,RCLike.norm_conj]
  exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one η.inverse P)


-- @@ L23-33 verbatim
lemma physicalSlotCoefficient_annular (η : Character) (W : ℝ→ℂ) (D : ℝ) (z : ℂ)
    (P : Ideal O) (hP : P≠0) (hD : 0<D) :
    physicalSlotCoefficient η W D z P=idealCoeff η.inverse P*
      HeckePrimeAnnular.annularWeight (fun y=>conj (W y)) D (1-z.re) (-z.im) P := by
  have hn : 0<(P.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hP)
  unfold physicalSlotCoefficient HeckePrimeAnnular.annularWeight
  rw [map_mul,HeckeInverseAmplification.conj_positive_cpow _ (div_pos hn hD)]
  have he : conj (z-1)= -HeckeDyadic.shift (1-z.re) (-z.im) := by
    apply Complex.ext <;> simp [HeckeDyadic.shift]
  rw [he]


-- @@ L35-57 verbatim
theorem physical_slot_conj (M : Ideal O) (H : Subgroup (O⧸M)ˣ)
    (η : Character) (m u : O) (hmLam : ConcretePrimeRowBridge.goodLambda∣m)
    (hMm : M≤Ideal.span {m}) (W : ℝ→ℂ) (b D : ℝ) (z : ℂ) (hD : 0<D)
    (hη : ∀P∈primePool M H b D,W ((P.absNorm:ℝ)/D)≠0→IsCoprime P η.modulus) :
    normalizedSlot η m 1 u (primePool M H b D) (physicalSlotCoefficient η W D z) 0 D=
      conj (HeckePrimeRow.canonicalPrimeAmplitude M H u W b D z) := by
  unfold normalizedSlot rowSlot HeckePrimeRow.canonicalPrimeAmplitude
  rw [←sqrt_inverse_cpow D hD,map_mul]
  simp only [map_inv₀,Complex.conj_ofReal,Complex.ofReal_zero,one_mul,mul_zero,Complex.cpow_zero,mul_one,map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro P hP
  have hP' : P∈primePool M H b D := hP
  obtain ⟨_,hp,hclass⟩ := Finset.mem_filter.mp hP
  let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  have hg := HeckePrimeRow.identityClass_prime_good M H m hmLam hMm P hclass
  have hcop := HeckePrimeRow.identityClass_coprime_larger M H hclass hMm
  rw [idealRowHom_argument_mul,idealRowHom_prime_sixth_mask m P hg,ite_eq_left hcop,one_mul]
  by_cases hw : W ((P.absNorm:ℝ)/D)=0
  · simp only [physicalSlotCoefficient,hw,zero_mul,map_zero,mul_zero,zero_mul]
  · have hn := idealCoeff_ne_zero_of_coprime η P hp.ne_zero (hη P hP' hw)
    simp only [physicalSlotCoefficient,HeckeDetectorRelativePrime.idealCoeff_inverse,map_mul,starRingEnd_self_apply]
    field_simp


-- @@ L59-59 verbatim
end SevenEighths.CenteredMomentDetectorDictionary


-- @@ L61-61 verbatim
end


-- @@ L63-63 verbatim
end OAI
