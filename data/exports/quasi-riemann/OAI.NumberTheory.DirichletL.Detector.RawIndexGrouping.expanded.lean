import OAI.NumberTheory.DirichletL.Detector.MixedFubini


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open MeasureTheory

-- @@ L7-7 verbatim
namespace SevenEighths.ProbePhysical

-- @@ L8-8 verbatim
open CanonicalQuadraticSieve

-- @@ L9-9 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L10-10 verbatim
local instance : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable

-- @@ L11-11 verbatim
local instance : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable


-- @@ L13-13 verbatim
abbrev SourceOuter (S : Finset (Ideal O)) := {K : Ideal O // Supported K ∧ ∀P∈S,¬P∣K}

-- @@ L14-14 verbatim
abbrev CompletedPair := Ideal O×Ideal O


-- @@ L16-21 verbatim
def sourceRawGrouping (S : Finset (Ideal O)) :
    SourceRawIndex S ≃ SourceOuter S×(CompletedPair×NonzeroFrequency) where
  toFun i := (⟨i.val.2.2,i.property⟩,(i.val.2.1,i.val.1))
  invFun i := ⟨(i.2.2,(i.2.1,i.1.val)),i.1.property⟩
  left_inv _i := rfl
  right_inv _i := rfl


-- @@ L23-31 verbatim
def sourceRawGroupingMeasurable (S : Finset (Ideal O))
    [MeasurableSpace (SourceRawIndex S)] [MeasurableSingletonClass (SourceRawIndex S)]
    [MeasurableSpace (SourceOuter S)] [MeasurableSingletonClass (SourceOuter S)]
    [MeasurableSpace CompletedPair] [MeasurableSingletonClass CompletedPair]
    [MeasurableSpace NonzeroFrequency] [MeasurableSingletonClass NonzeroFrequency] :
    SourceRawIndex S ≃ᵐ SourceOuter S×(CompletedPair×NonzeroFrequency) where
  toEquiv := sourceRawGrouping S
  measurable_toFun := measurable_of_countable _
  measurable_invFun := measurable_of_countable _


-- @@ L33-42 verbatim
lemma sourceRawGrouping_preserving (S : Finset (Ideal O))
    [MeasurableSpace (SourceRawIndex S)] [MeasurableSingletonClass (SourceRawIndex S)]
    [MeasurableSpace (SourceOuter S)] [MeasurableSingletonClass (SourceOuter S)]
    [MeasurableSpace CompletedPair] [MeasurableSingletonClass CompletedPair]
    [MeasurableSpace NonzeroFrequency] [MeasurableSingletonClass NonzeroFrequency] :
    MeasurePreserving (sourceRawGroupingMeasurable S) Measure.count
      ((Measure.count:Measure (SourceOuter S)).prod
        ((Measure.count:Measure CompletedPair).prod (Measure.count:Measure NonzeroFrequency))) := by
  rw [count_product,count_product]
  exact count_equiv_preserving _


-- @@ L44-44 verbatim
end SevenEighths.ProbePhysical

-- @@ L45-45 verbatim
end


-- @@ L47-47 verbatim
end OAI
