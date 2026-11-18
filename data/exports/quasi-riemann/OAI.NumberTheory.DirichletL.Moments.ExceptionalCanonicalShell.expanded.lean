import OAI.NumberTheory.DirichletL.Moments.ExceptionalSourceShell
import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalCount


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators


-- @@ L9-9 verbatim
namespace SevenEighths.CenteredMomentExceptionalCanonicalShell

-- @@ L10-10 verbatim
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge

-- @@ L11-11 verbatim
open CenteredMomentEligibleEnergy CenteredMomentAllocatedDetectorAmplitude

-- @@ L12-12 verbatim
open CenteredMomentExceptionalAmplitudePair CenteredMomentExceptionalSourceShell

-- @@ L13-13 verbatim
open CenteredMomentSecondExceptionalCount CenteredMomentCanonicalFirst CenteredMomentSecondCanonical

-- @@ L14-14 verbatim
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit

-- @@ L15-15 verbatim
open CenteredMomentForcing CenteredMomentChildRows UniqueFactorizationMonoid

-- @@ L16-16 verbatim
local notation "O" => HeckeFamily.O

-- @@ L17-17 verbatim
universe u

-- @@ L18-18 verbatim
variable {ι:Type u} [Fintype ι] [DecidableEq ι]


-- @@ L20-66 verbatim
theorem actual_canonical_source_shell (ε δ B:ℝ) (hε:0<ε) (hδ:0<δ) (hB:0≤B):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} → ∃C:ℝ,0<C ∧
      ∀(I L:Finset ι)(s:Data I)(v:Data L)(p q:Tests)(Z r:ℝ),1<Z →
      ∀(η:Character)(χ:RayFourExpansion.RayCharacter)(C₀ D₀:Ideal O)(_hC₀:Supported C₀)
        (U:Finset (CommonIndex C₀ D₀)),IsCoprime Q C₀ → idealCoeff η C₀≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      ∀rows:Finset O,(∀z∈rows,z≠0) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter η χ) Q m
        (commonFrequencyGenerator C₀ D₀*nonunitFrequencyGenerator C₀ D₀ U) z) →
      (∀z∈rows,Admissible s p Q Z B r z) → (∀z∈rows,Admissible v q Q Z B r z) →
      ∀Cr M:ℝ,0≤Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) →
      ∀Ds:Finset (Ideal O),(∀D∈Ds,Squarefree D) → ∀T:ℝ,1≤T →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∑D∈Ds,∑a∈s.toSource.active D,∑b∈v.toSource.active D,
        ∑z∈rows,‖amplitude s D a z‖*‖amplitude v D b z‖)≤
        C*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*(2*T)^(2*δ)*
          Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C₀ D₀=>P.val)
            (leftExponent C₀ D₀) (rightExponent C₀ D₀) (nonunitPartitionSet C₀ D₀ U)):ℝ))/6+
            2*ε+v.toSource.allowance Z-r)*profileMass s v p q J:=by
  obtain ⟨J,hJ⟩:=actual_paired_source_shell (ι:=ι) ε δ B hε hδ hB
  refine ⟨J,?_⟩
  intro Q hQ0 hQ hQ72
  obtain ⟨C,hC,hbound⟩:=hJ Q hQ0
  refine ⟨C,hC,?_⟩
  intro I L s v p q Z r hZ η χ C₀ D₀ hC₀ U hcop hη m hm hml hm2 rows hn hex hs hv
    Cr M hCr hN Ds hD T hT hlo hhi
  have hc:=actual_canonical_exceptional_count η χ C₀ D₀ hC₀ U Q hQ0 hQ hQ72 hcop hη
    m hm hml hm2 rows hn hex Z Cr M hZ hCr hN
  apply (hbound I L s v p q Z r hZ rows hs hv Ds hD T hT hlo hhi).trans
  have hz:=zero_lt_one.trans hZ
  calc
    _≤C*((768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
        Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C₀ D₀=>P.val)
          (leftExponent C₀ D₀) (rightExponent C₀ D₀) (nonunitPartitionSet C₀ D₀ U)):ℝ))/6))*
        (2*T)^(2*δ)*Z^(2*ε+v.toSource.allowance Z-r)*profileMass s v p q J:=by
      apply mul_le_mul_of_nonneg_right _ (profileMass_nonneg s v p q J)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hz.le _)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
      exact mul_le_mul_of_nonneg_left hc hC.le
    _=_:=by
      rw [show (M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C₀ D₀=>P.val)
          (leftExponent C₀ D₀) (rightExponent C₀ D₀) (nonunitPartitionSet C₀ D₀ U)):ℝ))/6+
          2*ε+v.toSource.allowance Z-r=
          (M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C₀ D₀=>P.val)
          (leftExponent C₀ D₀) (rightExponent C₀ D₀) (nonunitPartitionSet C₀ D₀ U)):ℝ))/6+
          (2*ε+v.toSource.allowance Z-r) by ring,Real.rpow_add hz]
      ring


-- @@ L68-68 verbatim
end SevenEighths.CenteredMomentExceptionalCanonicalShell


-- @@ L70-70 verbatim
end


-- @@ L72-72 verbatim
end OAI
