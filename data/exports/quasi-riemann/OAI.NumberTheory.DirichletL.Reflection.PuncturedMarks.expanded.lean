import OAI.NumberTheory.DirichletL.Reflection.PunctureAbsorption


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace SevenEighths.InverseReflectedPhase

-- @@ L6-6 verbatim
open scoped Classical BigOperators

-- @@ L7-7 verbatim
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment

-- @@ L8-8 verbatim
noncomputable section

-- @@ L9-9 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L11-23 verbatim
lemma markedCompletedT_zero_punctured (Ψ : Eis→*ℂ) (m f z : Eis)
    (P : Ideal Eis) (hP : Prime P) (hm : m∈P)
    (W : ℝ→ℂ) (X : ℝ) (d : Ideal Eis→ℂ) (hd : ∀ A,¬P∣A → d A=0) :
    markedCompletedT (rowTwist Ψ m f z) W X d=0 := by
  have hz (I J : Ideal Eis) : summand (rowTwist Ψ m f z) W X I J*d (I*J^3)=0 := by
    by_cases hdiv : P∣I*J^3
    · rcases hP.dvd_mul.mp hdiv with hI|hJ
      · have hz := CanonicalRowCompletion.columnWeight_zero_of_mask Ψ m f z hP hI hm
        simp only [summand,hz,zero_div,zero_mul]
      · have hz := cubeWeight_zero_of_prime_mask Ψ m f z hP (hP.dvd_of_dvd_pow hJ) hm
        simp only [summand,hz,mul_zero,zero_mul]
    · rw [hd _ hdiv,mul_zero]
  simp only [markedCompletedT,hz,tsum_zero]


-- @@ L25-33 verbatim
lemma markedCompletedT_zero_punctured_slot {σ : Type*} [Fintype σ]
    (S : PrimeFamily σ) (i : σ) (Ψ : Eis→*ℂ) (m f z : Eis) (hm : m∈S.ideal i)
    (W : ℝ→ℂ) (X : ℝ) :
    markedCompletedT (rowTwist Ψ m f z) W X
      (fun A => ∏ j,if S.ideal j∣A then (1:ℂ) else 0)=0 := by
  apply markedCompletedT_zero_punctured Ψ m f z (S.ideal i)
    (Ideal.prime_of_isPrime (NeZero.ne (S.ideal i)) inferInstance) hm W X
  intro A hA
  exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hA)

-- @@ L34-34 verbatim
end

-- @@ L35-35 verbatim
end SevenEighths.InverseReflectedPhase


-- @@ L37-37 verbatim
end OAI
