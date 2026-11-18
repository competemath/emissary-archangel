import OAI.NumberTheory.DirichletL.Moments.SecondBlockRadicalHarmonicMass
import OAI.NumberTheory.DirichletL.Moments.FirstDiscardedEnergy


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators


-- @@ L9-9 verbatim
namespace SevenEighths.CenteredMomentFirstInactiveRadicalMass

-- @@ L10-10 verbatim
open ActualEisensteinCubic CanonicalQuadraticSieve CompletedGauss

-- @@ L11-11 verbatim
open CenteredMomentCanonicalFirst CenteredMomentFirstDiscardedEnergy

-- @@ L12-12 verbatim
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondBlockRadicalHarmonicMass

-- @@ L13-13 verbatim
open CenteredMomentSourceMass CenteredMomentSourceRow CenteredMomentOriginalCommonHarmonic

-- @@ L14-14 verbatim
open CenteredMomentCommonRadialData CenteredMomentRankinRadical

-- @@ L15-15 verbatim
open CenteredMomentSecondBlockAggregate CenteredMomentSupportedCorrelation

-- @@ L16-16 verbatim
open ConcretePrimeRowBridge

-- @@ L17-17 verbatim
local notation "O"=>ActualEisensteinCubic.O


-- @@ L19-21 verbatim
def inactiveWeight (C D:Ideal O)(E:Finset (CommonIndex C D))(a:ℝ):ℝ:=
  ‖(UniqueFactorizationMonoid.moebius (∏P∈E,P.val):ℂ)‖/
    ((Ideal.absNorm (∏P∈E,P.val):ℝ)^a)


-- @@ L23-26 verbatim
lemma inactiveWeight_nonneg (C D:Ideal O)(E:Finset (CommonIndex C D))(a:ℝ):
    0 ≤ inactiveWeight C D E a:=by
  unfold inactiveWeight
  exact div_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)


-- @@ L28-39 verbatim
lemma inactiveWeight_le_one (C D:Ideal O)(E:Finset (CommonIndex C D))(a:ℝ)(ha:0≤a):
    inactiveWeight C D E a≤1:=by
  have hE:(∏P∈E,P.val)≠(0:Ideal O):=by
    have he:=primeSubsetGenerator_ne_zero (fun P:CommonIndex C D=>P.val) E
    have hh:=Ideal.span_singleton_eq_bot.not.mpr he
    simpa only [primeSubsetGenerator,ConcretePrimeRowBridge.span_idealGenerator,
      Ideal.zero_eq_bot] using hh
  have hn:1≤(Ideal.absNorm (∏P∈E,P.val):ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hE)
  have hp:1≤(Ideal.absNorm (∏P∈E,P.val):ℝ)^a:=Real.one_le_rpow hn ha
  unfold inactiveWeight
  exact (div_le_self (norm_nonneg _) hp).trans (QuadraticInitialBound.norm_ideal_moebius_le_one _)


-- @@ L41-62 verbatim
theorem actual_inactive_radical_mass (B ε:ℝ)(hB:0≤B)(hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀Z:ℝ,2≤Z→∀seed:Ideal O,Squarefree seed→seed≠0→
      ∀(S:Finset (Ideal O))(β:Ideal O→ℂ),
      (∀I∈S,β I≠0→seed∣I)→(∀I∈S,β I≠0→(I.absNorm:ℝ)≤Z^B)→
      ∀a:ℝ,0≤a→
      (∑p:ActiveLabel S β,∑E∈inactiveSubsets p.val.1 p.val.2,
        inactiveWeight p.val.1 p.val.2 E a/
          (Ideal.absNorm (commonRadical p.val.1 p.val.2):ℝ))≤C*Z^ε/(seed.absNorm:ℝ):=by
  obtain ⟨C,hC,hb⟩:=actual_active_radical_mass B ε hB hε
  refine ⟨C,hC,?_⟩
  intro Z hZ seed hs hs0 S β hm hn a ha
  apply le_trans _ (hb Z hZ seed hs hs0 S β hm hn)
  apply Finset.sum_le_sum
  intro p hp
  calc
    _≤∑_E∈inactiveSubsets p.val.1 p.val.2,radicalWeight p.val.1 p.val.2:=by
      apply Finset.sum_le_sum
      intro E hE
      exact div_le_div_of_nonneg_right (inactiveWeight_le_one _ _ E a ha) (Nat.cast_nonneg _)
    _≤∑_E:Finset (CommonIndex p.val.1 p.val.2),radicalWeight p.val.1 p.val.2:=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _=>radicalWeight_nonneg _ _)


-- @@ L64-77 verbatim
theorem original_input_inactive_radical_mass (B ε:ℝ)(hB:0≤B)(hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀Z:ℝ,2≤Z→∀(ι:Type*)[Fintype ι][DecidableEq ι](s:Input ι),
      s.W₁ 0=0→s.W₂ 0=0→sourceRadius s≤Z^B→
      ∀puncture seed:Ideal O,Squarefree seed→seed≠0→∀a:ℝ,0≤a→
      (∑p:ActiveLabel (finiteColumns (Fintype.piFinset s.pools)) (coefficient s puncture seed),
        ∑E∈inactiveSubsets p.val.1 p.val.2,
          inactiveWeight p.val.1 p.val.2 E a/
            (Ideal.absNorm (commonRadical p.val.1 p.val.2):ℝ))≤C*Z^ε/(seed.absNorm:ℝ):=by
  obtain ⟨C,hC,hb⟩:=actual_inactive_radical_mass B ε hB hε
  refine ⟨C,hC,?_⟩
  intro Z hZ ι _ _ s hz₁ hz₂ hcap puncture seed hs hs0 a ha
  exact hb Z hZ seed hs hs0 _ _
    (fun I _ hI=>original_column_mask s puncture seed I hI)
    (fun I _ hI=>(original_column_norm s puncture seed I hz₁ hz₂ hI).2.trans hcap) a ha


-- @@ L79-79 verbatim
end SevenEighths.CenteredMomentFirstInactiveRadicalMass


-- @@ L81-81 verbatim
end


-- @@ L83-83 verbatim
end OAI
