import OAI.NumberTheory.DirichletL.PrimeRows.Series
import OAI.NumberTheory.DirichletL.PrimeRows.FirstContinuation
import OAI.NumberTheory.DirichletL.Hecke.Origin


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
namespace SevenEighths.ProbeHighRowFamily

-- @@ L9-9 verbatim
open HeckeFamily HeckeInverseAmplification ProbePhysical

-- @@ L10-10 verbatim
local notation "O" => HeckeFamily.O


-- @@ L12-17 verbatim
def continuedHighSeries (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
    HeckeOrigin.continued (rowCharacter S hS.prime u) w*
    HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x*
    continuedCorrection S hS η u x w z


-- @@ L19-22 verbatim
theorem continuedHighSeries_eq_series (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ) (hw0 : w≠0) (hw1 : w≠1) :
    continuedHighSeries S hS η u x w z=continuedSeries S hS η u x w z := by
  rw [continuedHighSeries,HeckeOrigin.continued_eq _ hw0 hw1,continuedSeries]


-- @@ L24-31 verbatim
theorem continuedHighSeries_eq_initial (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    continuedHighSeries S hS η u x w z=markedIdealHighSeries S 1 η u.val x w z := by
  have hw0 : w≠0 := by intro h; simp only [h,Complex.zero_re] at hw; linarith
  have hw1 : w≠1 := by intro h; simp only [h,Complex.one_re] at hw; linarith
  rw [continuedHighSeries_eq_series S hS η u x w z hw0 hw1,
    continuedSeries_eq_initial S hS η u x w z hx hw hz]


-- @@ L33-41 verbatim
theorem continuedHighSeries_first_differentiableAt_w (eps : ℝ) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hw : max (-(1/100:ℝ)) (1+eps-x.re)<w.re)
    (hpole : w≠1 ∨ (rowCharacter S hS.prime u).residue≠1) :
    DifferentiableAt ℂ (fun w=>continuedHighSeries S hS η u x w z) w := by
  exact (((HeckeOrigin.continued_differentiableAt _ hpole).const_mul _).mul_const _).mul
    ((continuedCorrection_first_analytic_w eps S hS hfirst η u x z hx hz) w hw).differentiableAt


-- @@ L43-51 verbatim
theorem continuedHighSeries_first_differentiableAt_x (eps : ℝ) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hx : max (51/100:ℝ) (1+eps-w.re)<x.re)
    (hbeta : HeckeZeroSupremum.beta<x.re) :
    DifferentiableAt ℂ (fun x=>continuedHighSeries S hS η u x w z) x := by
  exact ((HeckeReciprocal.reciprocal_differentiableAt _ hbeta).const_mul _).mul
    ((continuedCorrection_first_analytic_x eps S hS hfirst η u w z hw hz) x hx).differentiableAt


-- @@ L53-53 verbatim
end SevenEighths.ProbeHighRowFamily


-- @@ L55-55 verbatim
end


-- @@ L57-57 verbatim
end OAI
