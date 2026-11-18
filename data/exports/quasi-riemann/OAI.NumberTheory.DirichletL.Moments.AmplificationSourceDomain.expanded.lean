import OAI.NumberTheory.DirichletL.Moments.AmplificationSource


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped BigOperators Classical


-- @@ L8-8 verbatim
namespace SevenEighths.CenteredMomentAmplificationSourceDomain

-- @@ L9-9 verbatim
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge CompletedGauss

-- @@ L10-10 verbatim
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationShortening

-- @@ L11-11 verbatim
open CenteredMomentAmplificationAllocation CenteredMomentGaussEnergy

-- @@ L12-12 verbatim
open CenteredMomentSupportedCorrelation CenteredMomentSourceRow CenteredMomentLiveDomain

-- @@ L13-13 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L15-17 verbatim
def residualIdeal (p : O) (hp : Prime p) (I : Ideal O) : Ideal O :=
  if hI : Supported I then Ideal.span {primeRemainder p hp (primaryGenerator I)
    (supported_primaryGenerator_ne_zero I hI)} else 0


-- @@ L19-23 verbatim
theorem residualIdeal_supported (p : O) (hp : Prime p) (I : Ideal O) (hI : Supported I) :
    Supported (residualIdeal p hp I) := by
  rw [residualIdeal,dite_eq_left hI]
  exact primeRemainder_supported p hp (primaryGenerator I)
    (by rw [primary_span_supported I hI];exact hI)


-- @@ L25-35 verbatim
theorem residualIdeal_generator (p : O) (hp : Prime p) (hpp : goodLambda^2 ∣ p-1)
    (I : Ideal O) (hI : Supported I) :
    primaryGenerator (residualIdeal p hp I) =
      primeRemainder p hp (primaryGenerator I) (supported_primaryGenerator_ne_zero I hI) := by
  rw [residualIdeal,dite_eq_left hI]
  apply primaryGenerator_span
  · apply supported_element_ne_zero
    simpa only [residualIdeal,dite_eq_left hI] using residualIdeal_supported p hp I hI
  · exact primeRemainder_primary p hp hpp (primaryGenerator I)
      (by rw [primary_span_supported I hI];exact hI)
      (primaryGenerator_spec I (supported_primaryGenerator_ne_zero I hI)).2


-- @@ L37-42 verbatim
theorem residualIdeal_reconstruct (p : O) (hp : Prime p) (I : Ideal O) (hI : Supported I) :
    (Ideal.span {p})^(multiplicity p (primaryGenerator I))*residualIdeal p hp I=I := by
  rw [residualIdeal,dite_eq_left hI,Ideal.span_singleton_pow,
    Ideal.span_singleton_mul_span_singleton,
    ← (primeRemainder_spec p hp (primaryGenerator I) (supported_primaryGenerator_ne_zero I hI)).1]
  exact primary_span_supported I hI


-- @@ L44-45 verbatim
def valuationColumns (S : Finset (Ideal O)) (p : O) (k : ℕ) : Finset (Ideal O) :=
  (supportedColumns S).filter (fun I => multiplicity p (primaryGenerator I)=k)


-- @@ L47-48 verbatim
def residualColumns (S : Finset (Ideal O)) (p : O) (hp : Prime p) (k : ℕ) : Finset (Ideal O) :=
  (valuationColumns S p k).image (residualIdeal p hp)


-- @@ L50-52 verbatim
theorem valuationColumns_supported (S : Finset (Ideal O)) (p : O) (k : ℕ)
    (I : Ideal O) (hI : I∈valuationColumns S p k) : Supported I :=
  (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2


-- @@ L54-61 verbatim
theorem residualIdeal_injOn (S : Finset (Ideal O)) (p : O) (hp : Prime p) (k : ℕ) :
    Set.InjOn (residualIdeal p hp) (valuationColumns S p k) := by
  intro I hI J hJ he
  have hi := residualIdeal_reconstruct p hp I (valuationColumns_supported S p k I hI)
  have hj := residualIdeal_reconstruct p hp J (valuationColumns_supported S p k J hJ)
  rw [(Finset.mem_filter.mp hI).2] at hi
  rw [(Finset.mem_filter.mp hJ).2] at hj
  exact hi.symm.trans ((congrArg (fun x => (Ideal.span {p})^k*x) he).trans hj)


-- @@ L63-66 verbatim
theorem residualColumns_supported (S : Finset (Ideal O)) (p : O) (hp : Prime p) (k : ℕ)
    (I : Ideal O) (hI : I∈residualColumns S p hp k) : Supported I := by
  obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hI
  exact residualIdeal_supported p hp J (valuationColumns_supported S p k J hJ)


-- @@ L68-77 verbatim
theorem residual_column_sum (S : Finset (Ideal O)) (p : O) (hp : Prime p) (k : ℕ)
    (c f : Ideal O → ℂ) :
    (∑ I∈valuationColumns S p k,c I*f (residualIdeal p hp I))=
      ∑ I∈residualColumns S p hp k,c ((Ideal.span {p})^k*I)*f I := by
  rw [residualColumns,Finset.sum_image (residualIdeal_injOn S p hp k)]
  apply Finset.sum_congr rfl
  intro I hI
  have hi := residualIdeal_reconstruct p hp I (valuationColumns_supported S p k I hI)
  rw [(Finset.mem_filter.mp hI).2] at hi
  rw [hi]


-- @@ L79-79 verbatim
end SevenEighths.CenteredMomentAmplificationSourceDomain


-- @@ L81-81 verbatim
end


-- @@ L83-83 verbatim
end OAI
