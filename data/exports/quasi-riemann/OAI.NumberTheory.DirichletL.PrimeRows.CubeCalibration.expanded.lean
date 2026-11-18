import OAI.NumberTheory.DirichletL.PrimeRows.CanonicalRayCube


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical BigOperators

-- @@ L7-7 verbatim
open MeasureTheory Set

-- @@ L8-8 verbatim
namespace SevenEighths.ProbeHighRowFamily

-- @@ L9-9 verbatim
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary

-- @@ L10-10 verbatim
local notation "O" => HeckeFamily.O


-- @@ L12-18 verbatim
lemma centralCubeIntegral_calibration_zero {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (hc : (calibrationForSet S hmax).residueMonoid u.val=0)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e H : ℝ) :
    centralCubeIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H=0 := by
  simp [centralCubeIntegral,continuedRowOnLines,continuedPhysicalRowKernel,hc]


-- @@ L20-28 verbatim
lemma cubeWeightedRow_calibration_zero {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (hc : (calibrationForSet S hmax).residueMonoid u.val=0)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z a e H : ℝ) :
    cubeWeightedRow S hS hmax P hPS η u W Yp W0 W1 X Y Z a e H=0 := by
  funext t
  simp [cubeWeightedRow,weightedRowOnLines,calibratedTupleValue,hc]


-- @@ L30-44 verbatim
theorem finiteCentralCubeRows_filter_calibration {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z e : ℝ) (a H : FreeRow→ℝ) :
    finiteCentralCubeRows S hS hmax η (R.filter (fun u=>(calibrationForSet S hmax).residueMonoid u.val≠0))
      T hT W Yp W0 W1 X Y Z e a H=
    finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e a H := by
  unfold finiteCentralCubeRows
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hc : (calibrationForSet S hmax).residueMonoid u.val=0
  · simp [hc,centralCubeIntegral_calibration_zero S hS hmax _ _ η u hc]
  · simp [hc]


-- @@ L46-46 verbatim
end SevenEighths.ProbeHighRowFamily


-- @@ L48-48 verbatim
end


-- @@ L50-50 verbatim
end OAI
