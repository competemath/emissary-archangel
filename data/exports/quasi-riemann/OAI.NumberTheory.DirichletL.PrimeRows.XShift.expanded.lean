import OAI.NumberTheory.DirichletL.PrimeRows.XBoundary


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical BigOperators

-- @@ L7-7 verbatim
open MeasureTheory Set Complex

-- @@ L8-8 verbatim
namespace SevenEighths.ProbeHighRowFamily

-- @@ L9-9 verbatim
open HeckeFamily HeckeInverseAmplification ProbePhysical

-- @@ L10-10 verbatim
local notation "O" => HeckeFamily.O


-- @@ L12-31 verbatim
theorem first_x_integral_eq {K : ℕ}
    (e eps : ℝ) (he : 0<e) (he' : e<1/1000) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hZ : 0<Z) (w z : ℂ) (l r : ℝ) (hlr : l≤r)
    (hl : (51/100:ℝ)≤l) (hlβ : HeckeZeroSupremum.beta+8*e≤l)
    (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hlw : 1+eps≤l+w.re) :
    (∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z ((l:ℂ)+t*I) w z)=
      ∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z ((r:ℂ)+t*I) w z := by
  obtain ⟨B,hB,hbound⟩ := continuedPhysicalRowKernel_x_gaussian e (eps/2) he he' S hS hfirst hmax P hPS
    η u W0 W1 X Y Z hZ w z l r hl hlβ hw hz (by linarith)
  apply Continuation.vertical_integral_eq_of_shifted_polynomial_gaussian_bound
    (fun x=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z) z.im 2 hlr _ hbound
  intro x hx
  apply (continuedPhysicalRowKernel_buffered_differentiableAt_x eps heps S hS hfirst hmax P hPS η u
    W0 W1 X Y Z hZ x w z (hl.trans hx.1) hw hz (by linarith [hx.1]) ?_).differentiableWithinAt
  intro hpole
  exact HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt _ (by linarith [hx.1]) (by tauto)


-- @@ L33-33 verbatim
end SevenEighths.ProbeHighRowFamily


-- @@ L35-35 verbatim
end


-- @@ L37-37 verbatim
end OAI
