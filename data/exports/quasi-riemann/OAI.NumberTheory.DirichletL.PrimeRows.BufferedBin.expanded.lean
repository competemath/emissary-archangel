import OAI.NumberTheory.DirichletL.PrimeRows.DetectorBins


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

-- @@ L11-11 verbatim
variable {ι : Type*} [Fintype ι]


-- @@ L13-15 verbatim
def sourceDetectorFamily (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (u : FreeRow) (ψ : ι→Character) : Sum Bool ι→Character :=
  Sum.elim (fun b=>if b then rowCharacter S hS u else (targetRow η u).excludePrimes S hS) ψ


-- @@ L17-20 verbatim
omit [Fintype ι] in
@[simp] lemma sourceDetectorFamily_denominator (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (u : FreeRow) (ψ : ι→Character) :
    sourceDetectorFamily S hS η u ψ (Sum.inl false)=(targetRow η u).excludePrimes S hS := rfl


-- @@ L22-25 verbatim
omit [Fintype ι] in
@[simp] lemma sourceDetectorFamily_numerator (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (u : FreeRow) (ψ : ι→Character) :
    sourceDetectorFamily S hS η u ψ (Sum.inl true)=rowCharacter S hS u := rfl


-- @@ L27-34 verbatim
lemma source_bin_denominator_nonzero (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (u : FreeRow) (ψ : ι→Character) (T a e : ℝ) (i : ℕ) (he : 0<e)
    (hmax : detectorMaximum (sourceDetectorFamily S hS η u ψ) (3*(i+1:ℕ)*T)<a+2*e)
    (x : ℂ) (hx : a+16*e≤x.re) (ht : |x.im|≤3*(i+1:ℕ)*T)
    (hpole : ¬(((targetRow η u).excludePrimes S hS).residue=1 ∧ x=1)) :
    LFunction ((targetRow η u).excludePrimes S hS) x≠0 :=
  detector_nonzero_above_maximum (sourceDetectorFamily S hS η u ψ) _ (Sum.inl false)
    (by linarith) ht hpole


-- @@ L36-58 verbatim
theorem source_buffered_x_rectangle {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmaxS : ∀P∈S,P.IsMaximal)
    (P : Fin K→PrimeIdeal) (hPS : ∀j,(P j).val∉S) (η : Character) (u : FreeRow) (ψ : ι→Character)
    (T a e : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (hfirst : FirstTail (4*e) S)
    (hmax : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*T)<a+2*e)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0<Z)
    (w z : ℂ) (hw : w.re=1-a-6*e) (hz : (17/50:ℝ)≤z.re)
    (r H : ℝ) (hr : a+16*e≤r) (hH : 0≤H) (hHT : H≤3*(i+1:ℕ)*T) :
    let F := fun x=>continuedPhysicalRowKernel S hS hmaxS P hPS η u W0 W1 X Y Z x w z
    (∫t : ℝ in -H..H,F ((r:ℂ)+t*I))=
      (∫t : ℝ in -H..H,F ((((a+16*e):ℝ):ℂ)+t*I))+
        I*((∫v : ℝ in (a+16*e)..r,F ((v:ℂ)+(-H)*I))-
          (∫v : ℝ in (a+16*e)..r,F ((v:ℂ)+H*I))) := by
  apply buffered_x_rectangle (8*e) (by positivity) S hS
    (by convert hfirst using 1 ; ring) hmaxS P hPS η u W0 W1 X Y Z hZ w z (a+16*e) r H
    (by linarith) (by linarith) (by rw [hw];linarith) hz (by rw [hw];linarith) (by rw [hw];linarith)
  intro x hx hpole
  have hxr : a+16*e≤x.re := by simpa only [min_eq_left hr] using hx.1.1
  have hxi : |x.im|≤H := by
    apply abs_le.mpr
    simpa only [uIcc_of_le (by linarith : -H≤H),Set.mem_preimage,Set.mem_Icc] using hx.2
  exact source_bin_denominator_nonzero S hS.prime η u ψ T a e i he hmax x hxr (hxi.trans hHT) hpole


-- @@ L60-60 verbatim
end SevenEighths.ProbeHighRowFamily


-- @@ L62-62 verbatim
end


-- @@ L64-64 verbatim
end OAI
