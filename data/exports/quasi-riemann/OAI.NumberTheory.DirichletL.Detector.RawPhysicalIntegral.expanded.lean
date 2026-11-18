import OAI.NumberTheory.DirichletL.Detector.InitialProduct
import OAI.NumberTheory.DirichletL.Detector.RawMellinTerm


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
open ProbeMellinBoundary CanonicalQuadraticSieve

-- @@ L11-11 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L12-12 verbatim
local instance : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable

-- @@ L13-13 verbatim
local instance : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable


-- @@ L15-16 verbatim
def SourceRawIndex (S : Finset (Ideal O)) :=
  {p : RawHighIndex // Supported p.2.2 ∧ ∀P∈S,¬P∣p.2.2}


-- @@ L18-18 verbatim
instance (S : Finset (Ideal O)) : Countable (SourceRawIndex S) := inferInstanceAs (Countable {_p : RawHighIndex // _})


-- @@ L20-21 verbatim
def sourceRawEmbedding (S : Finset (Ideal O)) (i : SourceRawIndex S) : FullHighIndex :=
  rawHighEmbedding i.val


-- @@ L23-24 verbatim
lemma sourceRawEmbedding_injective (S : Finset (Ideal O)) : Function.Injective (sourceRawEmbedding S) :=
  rawHighEmbedding_injective.comp Subtype.val_injective


-- @@ L26-31 verbatim
def originalRawOnLines (η : HeckeFamily.Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,P.IsMaximal) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ)
    (i : SourceRawIndex S) (p : HeightSpace) : ℂ :=
  rawPhysicalMellinTerm η (calibrationForSet S hS) S D i.val.2.1.1 i.val.2.1.2 i.val.2.2 i.property.1
    W0 W1 X Y Z i.val.1.val ((4:ℂ)+p.1.1*Complex.I)
      ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I)


-- @@ L33-66 verbatim
theorem originalRaw_counting_product_integrable (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) [MeasurableSpace (SourceRawIndex S)] [MeasurableSingletonClass (SourceRawIndex S)]
    (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Integrable (fun p : SourceRawIndex S×HeightSpace=>originalRawOnLines η S hS D W0 W1 X Y Z p.1 p.2)
      ((Measure.count:Measure (SourceRawIndex S)).prod heightMeasure) := by
  let mask := fun H : NonzeroFrequency=>star ((calibrationForSet S hS).residueMonoid H.val)
  have hm (H : NonzeroFrequency) : ‖mask H‖≤1 := by
    simpa only [mask,norm_star] using (calibrationForSet S hS).residueMonoid_norm_le_one H.val
  let T := fun p : HeightSpace=>sourceMellinWeight W0 W1 X Y Z
    ((3:ℂ)+p.1.1*Complex.I) ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I)
  have hT : Integrable T heightMeasure := sourceMellinWeight_initial_integrable W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 X Y Z hX hY hZ 3 2 3 (by norm_num)
  have hcT : Continuous T := sourceMellinWeight_initial_continuous W0 W1 a1 b1 ha1 hW1
    X Y Z hX hY hZ 3 2 3 (by norm_num)
  have hi := initialHigh_counting_product_integrable (sourceRawEmbedding S) (sourceRawEmbedding_injective S)
    S D η mask hm 3 3 2 (by norm_num) (by norm_num) (by norm_num) T hT hcT
  have hp := (MeasurePreserving.id (Measure.count:Measure (SourceRawIndex S))).prod
    (sourceHeightShear_preserving.symm sourceHeightShear)
  have hh := hp.integrable_comp_of_integrable hi
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro p
  dsimp only [Function.comp_def,Prod.map]
  rw [originalRawOnLines,rawPhysicalMellinTerm_eq_source η S hS hpS hbad D _ _ _ p.1.property.1
    p.1.property.2 W0 W1 X Y Z hX p.1.val.1]
  have he : (4:ℂ)+p.2.1.1*Complex.I+1-((2:ℂ)+p.2.1.2*Complex.I)=
      3+((p.2.1.1-p.2.1.2:ℝ):ℂ)*Complex.I := by push_cast;ring
  have hsh : sourceHeightShear.symm p.2=((p.2.1.1-p.2.1.2,p.2.1.2),p.2.2) := rfl
  simp only [he,initialHighOnLines,T,hsh,sourceRawEmbedding,mask,id_eq,Complex.ofReal_ofNat]
  ring


-- @@ L68-68 verbatim
end SevenEighths.ProbePhysical

-- @@ L69-69 verbatim
end


-- @@ L71-71 verbatim
end OAI
