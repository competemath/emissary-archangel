import OAI.NumberTheory.DirichletL.Detector.HighExcludedEuler
import OAI.NumberTheory.DirichletL.Detector.HighEulerLocal


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators

-- @@ L8-8 verbatim
namespace SevenEighths.ProbePhysical

-- @@ L9-9 verbatim
open ActualEisensteinCubic

-- @@ L10-10 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L11-11 verbatim
local notation "Id" => Ideal O


-- @@ L13-24 verbatim
lemma highExclusion_prime (S : Finset Id) (hS : ∀P∈S,Prime P) (P : PrimeIdeal) :
    highExclusion S hS P.val=if P.val∈S then 0 else 1 := by
  change (if ∀Q∈S,¬Q∣P.val then (1:ℂ) else 0)=_
  by_cases hP : P.val∈S
  · rw [ite_eq_right (fun h=>h P.val hP (dvd_refl _)),ite_eq_left hP]
  · have houtside : ∀Q∈S,¬Q∣P.val := by
      intro Q hQ hd
      have hn : (⟨Q,hS Q hQ⟩ : PrimeIdeal)≠P := by
        intro hh
        exact hP ((congrArg Subtype.val hh) ▸ hQ)
      exact (hS Q hQ).not_isUnit ((primeIdeal_coprime ⟨Q,hS Q hQ⟩ P hn).isUnit_of_dvd hd)
    rw [ite_eq_left houtside,ite_eq_right hP]


-- @@ L26-30 verbatim
lemma highIdealMask_prime_outside (S : Finset Id) (hS : ∀P∈S,Prime P)
    (P : PrimeIdeal) (hP : P.val∉S) (b : HighValuation) :
    highIdealMask S 1 (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)=1 := by
  simp only [highIdealMask_unmarked S hS,map_pow,highExclusion_prime S hS P,
    ite_eq_right hP,one_pow,one_mul]


-- @@ L32-39 verbatim
lemma highIdealMask_prime_inside (S : Finset Id) (hS : ∀P∈S,Prime P)
    (P : PrimeIdeal) (hP : P.val∈S) (b : HighValuation) :
    highIdealMask S 1 (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)=
      if b=0 then 1 else 0 := by
  rcases b with ⟨⟨e,l⟩,k,m⟩
  simp only [highIdealMask_unmarked S hS,map_pow,highExclusion_prime S hS P,ite_eq_left hP]
  by_cases he : e=0 <;> by_cases hl : l=0 <;> by_cases hk : k=0 <;> by_cases hm : m=0 <;>
    simp [he,hl,hk,hm,Prod.mk_eq_zero]


-- @@ L41-59 verbatim
theorem excludedHighLocalFactor (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) (P : PrimeIdeal) :
    (∑' b : HighValuation,markedIdealHighSummand S 1 η 1 x w z
      (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)) =
      if P.val∈S then 1 else idealHighLocalFactor η P.val x w z := by
  by_cases hP : P.val∈S
  · rw [ite_eq_left hP]
    have he (b : HighValuation) : markedIdealHighSummand S 1 η 1 x w z
        (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)=if b=0 then 1 else 0 := by
      rw [markedIdealHighSummand,highIdealMask_prime_inside S hS P hP b]
      by_cases hb : b=0
      · subst b
        simp only [Prod.fst_zero,Prod.snd_zero,pow_zero,bareIdealHighSummand_one,mul_one]
      · simp only [ite_eq_right hb,zero_mul]
    simp only [he,tsum_ite_eq]
  · rw [ite_eq_right hP]
    simp only [markedIdealHighSummand,highIdealMask_prime_outside S hS P hP,one_mul]
    exact highPrimeTerm_tsum_eq_localFactor η x w z hx hw hz P


-- @@ L61-74 verbatim
theorem excludedIdealHighSeries_hasProd_outside (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : {P : PrimeIdeal // P.val∉S}=>idealHighLocalFactor η P.val.val x w z)
      (markedIdealHighSeries S 1 η 1 x w z) := by
  have h := excludedIdealHighSeries_hasProd S hS η x w z hx hw hz
  simp only [excludedHighLocalFactor S hS η x w z hx hw hz] at h
  apply (hasProd_subtype_iff_mulIndicator
    (s:={P : PrimeIdeal | P.val∉S})
    (f:=fun P : PrimeIdeal=>idealHighLocalFactor η P.val x w z)).mpr
  convert h using 1
  funext P
  simp only [Set.mulIndicator,Set.mem_ofPred_eq]
  split_ifs <;> simp_all


-- @@ L76-76 verbatim
end SevenEighths.ProbePhysical

-- @@ L77-77 verbatim
end


-- @@ L79-79 verbatim
end OAI
