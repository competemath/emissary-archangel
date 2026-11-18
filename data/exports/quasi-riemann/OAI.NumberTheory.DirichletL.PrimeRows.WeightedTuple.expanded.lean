import OAI.NumberTheory.DirichletL.PrimeRows.TupleFactor


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical BigOperators

-- @@ L7-7 verbatim
namespace SevenEighths.ProbeHighRowFamily

-- @@ L8-8 verbatim
open HeckeFamily HeckeInverseAmplification ProbePhysical

-- @@ L9-9 verbatim
local notation "O" => HeckeFamily.O


-- @@ L11-15 verbatim
theorem tupleOutside {K : ℕ} (S : Finset (Ideal O)) (P : Fin K→PrimeIdeal)
    (hPS : ∀i,(P i).val∉S) : ∀Q∈Finset.univ.image P,Q.val∉S := by
  intro Q hQ
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hQ
  exact hPS i


-- @@ L17-23 verbatim
def calibratedTupleValue {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (u : FreeRow)
    (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (x w z : ℂ) : ℂ :=
  star ((calibrationForSet S hmax).residueMonoid u.val)*
  (∏i,W i (((P i).val.absNorm:ℝ)/Y i)*((P i).val.absNorm:ℂ)^(z-1))*
  physicalCompensatedRow S hS (Finset.univ.image P) (tupleOutside S P hPS) η u x w z


-- @@ L25-43 verbatim
theorem calibratedTupleValue_factor {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (u : FreeRow)
    (P : Fin K→PrimeIdeal) (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (x w z : ℂ) :
    calibratedTupleValue S hS hmax η u P hPS W Y x w z=
      (star ((calibrationForSet S hmax).residueMonoid u.val)*
        (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
          HeckeOrigin.continued (rowCharacter S hS.prime u) w*
          HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x))*
      (continuedCorrection (markExclusions S (Finset.univ.image P))
        (markedSourceExclusions S hS (Finset.univ.image P)) η u x w z*
        ∏i,W i (((P i).val.absNorm:ℝ)/Y i)*((P i).val.absNorm:ℂ)^(z-1)*
          continuedCompensatedLocal η u (P i) (outside_prime_supported S hS.bad (P i) (hPS i)) x w z
            (star (idealCoeff η (P i).val)*((P i).val.absNorm:ℂ)^x)
            (((P i).val.absNorm:ℂ)^(-w))) := by
  unfold calibratedTupleValue
  rw [physicalCompensatedRow_indexed S hS P hP hPS]
  simp only [Finset.prod_mul_distrib]
  ring


-- @@ L45-45 verbatim
end SevenEighths.ProbeHighRowFamily

-- @@ L46-46 verbatim
end


-- @@ L48-48 verbatim
end OAI
