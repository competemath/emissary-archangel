import OAI.NumberTheory.DirichletL.Detector.RawSourceIntegral
import OAI.NumberTheory.DirichletL.Detector.SixthSeries


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical

-- @@ L8-8 verbatim
open MeasureTheory

-- @@ L9-9 verbatim
namespace SevenEighths.ProbePhysical

-- @@ L10-10 verbatim
open ProbeMellinBoundary ProbeCompleted HeckeInverseAmplification CanonicalQuadraticSieve

-- @@ L11-11 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L13-16 verbatim
def sourceRowSeries (η : HeckeFamily.Character) (S : Finset (Ideal O))
    (C : CalibrationData) (D : Ideal O) (x w z : ℂ) : ℂ :=
  ∑'u : FreeRow,star (C.residueMonoid u.val)*frequencyWeight z ⟨u.val,u.property.1⟩*
    markedIdealHighSeries S D η u.val x w z


-- @@ L18-24 verbatim
def sourceTripleIntegral (η : HeckeFamily.Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,P.IsMaximal) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*∫p : HeightSpace,
    sourceMellinWeight W0 W1 X Y Z ((3:ℂ)+p.1.1*Complex.I)
      ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I)*
    sourceRowSeries η S (calibrationForSet S hS) D ((3:ℂ)+p.1.1*Complex.I)
      ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I) ∂heightMeasure


-- @@ L26-43 verbatim
lemma rawSourceTripleIntegral_eq_source (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) :
    rawSourceTripleIntegral η S hS D W0 W1 X Y Z=
      sourceTripleIntegral η S hS D W0 W1 X Y Z := by
  unfold rawSourceTripleIntegral sourceTripleIntegral
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro p
  dsimp only
  congr 1
  unfold sourceRowSeries
  exact rawArithmeticSeries_eq_sixth_high S hS hpS hbad D η
    ((3:ℂ)+p.1.1*Complex.I) ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I)
    (by norm_num [Complex.add_re,Complex.mul_re])
    (by norm_num [Complex.add_re,Complex.mul_re])
    (by norm_num [Complex.add_re,Complex.mul_re])


-- @@ L45-55 verbatim
theorem markedPhysicalProbe_eq_source_triple (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (hSne : S.Nonempty) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    markedPhysicalProbe η (calibrationForSet S hS) D W0 W1 X Y Z=
      sourceTripleIntegral η S hS D W0 W1 X Y Z := by
  rw [markedPhysicalProbe_eq_raw_triple η S hS hpS hbad hSne D W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z hX hY hZ]
  exact rawSourceTripleIntegral_eq_source η S hS hpS hbad D W0 W1 X Y Z


-- @@ L57-57 verbatim
end SevenEighths.ProbePhysical

-- @@ L58-58 verbatim
end


-- @@ L60-60 verbatim
end OAI
