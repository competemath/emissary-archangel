import OAI.NumberTheory.DirichletL.Moments.ExceptionalAsymmetricSource
import OAI.NumberTheory.DirichletL.Moments.ExceptionalCanonicalShell


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators

-- @@ L8-8 verbatim
open Filter


-- @@ L10-10 verbatim
namespace SevenEighths.CenteredMomentExceptionalAsymmetricCanonical

-- @@ L11-11 verbatim
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge

-- @@ L12-12 verbatim
open CenteredMomentEligibleEnergy CenteredMomentAllocatedDetectorAmplitude

-- @@ L13-13 verbatim
open CenteredMomentExceptionalAmplitudePair CenteredMomentExceptionalSourceShell

-- @@ L14-14 verbatim
open CenteredMomentExceptionalMaskedSource CenteredMomentExceptionalAsymmetricSource CenteredMomentSecondExceptionalCount

-- @@ L15-15 verbatim
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical

-- @@ L16-16 verbatim
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit

-- @@ L17-17 verbatim
open CenteredMomentForcing CenteredMomentChildRows UniqueFactorizationMonoid

-- @@ L18-18 verbatim
local notation "O" => HeckeFamily.O

-- @@ L19-19 verbatim
universe u

-- @@ L20-20 verbatim
variable {ι:Type u} [Fintype ι] [DecidableEq ι]


-- @@ L22-73 verbatim
theorem actual_asymmetric_canonical_source (lo hi:ι→ℝ)(ε δ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(I L:Finset ι)(s:Data I)(v:Data L)(p q:Tests),
      (∀i:L,v.lo i=lo i) → (∀i:L,v.hi i=hi i) →
      ∀r rRight:ℝ,∀(η:Character)(χ:RayFourExpansion.RayCharacter)(C₀ D₀:Ideal O)(_hC₀:Supported C₀)
        (U:Finset (CommonIndex C₀ D₀)),IsCoprime Q C₀ → idealCoeff η C₀≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      ∀rows:Finset O,(∀z∈rows,z≠0) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter η χ) Q m
        (commonFrequencyGenerator C₀ D₀*nonunitFrequencyGenerator C₀ D₀ U) z) →
      (∀z∈rows,Admissible s p Q Z B r z) →
      (∀z∈rows,Admissible v q Q Z B rRight z) →
      ∀Cr M:ℝ,0≤Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) →
      ∀Ds:Finset (Ideal O),
      (∀D∈Ds,(moebius D:ℂ)≠0 → (D.absNorm:ℝ)≤Z^Lbound) →
      (∑D∈Ds,‖(moebius D:ℂ)‖*∑z∈rows,
        ‖maskedAmplitude s D z‖*‖maskedAmplitude v D z‖)≤
        C*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
          Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C₀ D₀=>P.val)
            (leftExponent C₀ D₀) (rightExponent C₀ D₀) (nonunitPartitionSet C₀ D₀ U)):ℝ))/6+
            2*ε+δ-max r 0)*profileMass s v p q J:=by
  obtain ⟨J,hJ⟩:=actual_masked_asymmetric lo hi ε δ B Lbound hε hδ hB hL
  refine ⟨J,?_⟩
  intro Q hQ0 hQ hQ72
  obtain ⟨C,hC,hbound⟩:=hJ Q hQ0
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro I L s v p q hlo hhi r rRight η χ C₀ D₀ hC₀ U hcop hη m hm hml hm2 rows hn hex hs hv
    Cr M hCr hN Ds hDs
  have hc:=actual_canonical_exceptional_count η χ C₀ D₀ hC₀ U Q hQ0 hQ hQ72 hcop hη
    m hm hml hm2 rows hn hex Z Cr M hZ.1 hCr hN
  apply (hZ.2 I L s v p q hlo hhi r rRight rows hs hv Ds hDs).trans
  have hz:=zero_lt_one.trans hZ.1
  calc
    _≤C*((768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
        Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C₀ D₀=>P.val)
          (leftExponent C₀ D₀) (rightExponent C₀ D₀) (nonunitPartitionSet C₀ D₀ U)):ℝ))/6))*
        Z^(2*ε+δ-max r 0)*profileMass s v p q J:=by
      apply mul_le_mul_of_nonneg_right _ (profileMass_nonneg s v p q J)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hz.le _)
      exact mul_le_mul_of_nonneg_left hc hC.le
    _=_:=by
      rw [show (M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C₀ D₀=>P.val)
          (leftExponent C₀ D₀) (rightExponent C₀ D₀) (nonunitPartitionSet C₀ D₀ U)):ℝ))/6+
          2*ε+δ-max r 0=
          (M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C₀ D₀=>P.val)
          (leftExponent C₀ D₀) (rightExponent C₀ D₀) (nonunitPartitionSet C₀ D₀ U)):ℝ))/6+
          (2*ε+δ-max r 0) by ring,Real.rpow_add hz]
      ring


-- @@ L75-75 verbatim
end SevenEighths.CenteredMomentExceptionalAsymmetricCanonical


-- @@ L77-77 verbatim
end


-- @@ L79-79 verbatim
end OAI
