import OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedPadding


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
open scoped Classical BigOperators SchwartzMap

-- @@ L8-8 verbatim
namespace SevenEighths.DetectorDictionaryInverseMarkedReference

-- @@ L9-9 verbatim
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber

-- @@ L10-10 verbatim
open InverseInitialRawDictionary InverseInitialDetectorSource InverseInitialPhysicalSlots

-- @@ L11-11 verbatim
open DetectorDictionaryInverseMarkedPadding

-- @@ L12-12 verbatim
local notation "O"=>HeckeFamily.O


-- @@ L14-15 verbatim
def slotCoefficient (data:RowData)(V:ℝ→ℂ)(Y:ℝ)(ζ:ℂ)(P:Ideal O) : ℂ :=
  star (primeProfile V Y ζ P)/fixedBase data.η data.m data.f P


-- @@ L17-21 verbatim
theorem slotCoefficient_character (data:RowData)(V:ℝ→ℂ)(Y:ℝ)(ζ:ℂ)(P:Ideal O) :
    slotCoefficient data V Y ζ P=
      idealCoeff (baseCharacter data).inverse P*star (primeProfile V Y ζ P) := by
  rw [slotCoefficient,HeckeDetectorRelativePrime.idealCoeff_inverse,baseCharacter_coeff,
    div_eq_mul_inv,mul_comm]


-- @@ L23-28 verbatim
theorem tuple_coefficient {ι:Type*}[Fintype ι](data:RowData)
    (V:ι→ℝ→ℂ)(Y:ι→ℝ)(ζ:ι→ℂ)(P:ι→Ideal O) :
    star (∏i,primeProfile (V i) (Y i) (ζ i) (P i))/
      fixedBase data.η data.m data.f (∏i,P i)=
      ∏i,slotCoefficient data (V i) (Y i) (ζ i) (P i) := by
  simp only [slotCoefficient,star_prod,map_prod,Finset.prod_div_distrib]


-- @@ L30-31 verbatim
def normalizedSlotCoefficient (data:RowData)(V:ℝ→ℂ)(Y:ℝ)(ζ:ℂ)(C:ℝ)(P:Ideal O) : ℂ :=
  slotCoefficient data V Y ζ P/(C:ℂ)


-- @@ L33-42 verbatim
theorem tuple_coefficient_normalized {ι:Type*}[Fintype ι](data:RowData)
    (V:ι→ℝ→ℂ)(Y:ι→ℝ)(ζ:ι→ℂ)(C:ι→ℝ)(hC:∀i,C i≠0)(P:ι→Ideal O) :
    star (∏i,primeProfile (V i) (Y i) (ζ i) (P i))/
      fixedBase data.η data.m data.f (∏i,P i)=
      (∏i,(C i:ℂ))*∏i,normalizedSlotCoefficient data (V i) (Y i) (ζ i) (C i) (P i) := by
  rw [tuple_coefficient,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [normalizedSlotCoefficient]
  field_simp [hC i]


-- @@ L44-45 verbatim
variable {M:Ideal O}[NeZero M]{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
  {U a ε tstar T allowance:ℝ}{i:ℕ}


-- @@ L47-69 verbatim
omit [NeZero M] in
theorem selectedSource_normalized (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (selected:Finset Slot)(W:ℝ→ℂ)(σ t bW:ℝ)(C:Slot→ℝ)(hC:∀s∈selected,C s≠0)(u:O) :
    selectedSource F selected W σ t bW u=
      (∏s∈selected,(C s:ℂ))*
      ∑p∈Fintype.piFinset (fun s:selected=>livePrimes M H (F.profile s) (F.upper s) (U^(F.widths s))),
        (∏s:selected,normalizedSlotCoefficient F.rowData (F.profile s) (U^(F.widths s))
          (F.external s) (C s) (p s))*
        InverseInitialConjugateEnergy.originalTotalPolynomial
          ((ConcretePrimeRowBridge.idealsUpTo ⌈U^F.r*bW⌉₊).filter CanonicalQuadraticSieve.Supported)
          (∏s:selected,p s) (fixedBase F.rowData.η F.rowData.m F.rowData.f) (fun _=>1)
          (twistedProfile (HeckeDetectorCoefficientTransfer.orientedProfile F.reverse W) σ
            (HeckeDetectorCoefficientTransfer.orientedFrequency F.reverse t))
          U F.r (∑s:selected,F.widths s) u := by
  unfold selectedSource
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [tuple_coefficient_normalized F.rowData (fun s:selected=>F.profile s)
    (fun s:selected=>U^(F.widths s)) (fun s:selected=>F.external s)
    (fun s:selected=>C s) (fun s=>hC s s.property) p]
  rw [Finset.prod_coe_sort selected (fun s=>(C s:ℂ))]
  ring


-- @@ L71-71 verbatim
end SevenEighths.DetectorDictionaryInverseMarkedReference


-- @@ L73-73 verbatim
end


-- @@ L75-75 verbatim
end OAI
