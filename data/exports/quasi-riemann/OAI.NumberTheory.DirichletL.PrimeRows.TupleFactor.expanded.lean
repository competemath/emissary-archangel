import OAI.NumberTheory.DirichletL.PrimeRows.MarkedHolomorphic


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


-- @@ L11-39 verbatim
theorem physicalCompensatedRow_indexed {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (P : Fin K→PrimeIdeal) (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (x w z : ℂ) :
    let hT : ∀Q∈Finset.univ.image P,Q.val∉S := by
      intro Q hQ
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hQ
      exact hPS i
    physicalCompensatedRow S hS (Finset.univ.image P) hT η u x w z=
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        HeckeOrigin.continued (rowCharacter S hS.prime u) w*
        HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)*
      (continuedCorrection (markExclusions S (Finset.univ.image P))
        (markedSourceExclusions S hS (Finset.univ.image P)) η u x w z*
        ∏i,continuedCompensatedLocal η u (P i)
          (outside_prime_supported S hS.bad (P i) (hPS i)) x w z
          (star (idealCoeff η (P i).val)*((P i).val.absNorm:ℂ)^x)
          (((P i).val.absNorm:ℂ)^(-w))) := by
  dsimp only
  unfold physicalCompensatedRow continuedCompensatedRow
  congr 2
  symm
  apply Finset.prod_bij (fun i _=>⟨P i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩)
  · intro i _; exact Finset.mem_attach _ _
  · intro i _ j _ h; exact hP (congrArg Subtype.val h)
  · intro Q _
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp Q.property
    exact ⟨i,hi,Subtype.ext he⟩
  · intro i _; rfl


-- @@ L41-41 verbatim
end SevenEighths.ProbeHighRowFamily

-- @@ L42-42 verbatim
end


-- @@ L44-44 verbatim
end OAI
