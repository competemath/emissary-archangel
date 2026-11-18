import OAI.NumberTheory.DirichletL.Reflection.MarkedFiber


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace SevenEighths.InverseReflectedPhase

-- @@ L6-6 verbatim
open scoped Classical BigOperators

-- @@ L7-7 verbatim
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment

-- @@ L8-8 verbatim
noncomputable section

-- @@ L9-9 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L10-10 verbatim
variable {σ : Type*} [Fintype σ] {m f z : Eis} (D : GoodMaskRowData m f z)

-- @@ L11-16 verbatim
variable (R I F Q₀ : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime Q₀ (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))

-- @@ L17-17 verbatim
local notation "E" => D.primeFiberEquiv R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask


-- @@ L19-57 verbatim
theorem original_fiber_inactive_sum (S : PrimeFamily σ)
    (hS : ∀ i, ringChar (Eis⧸S.ideal i)≠2)
    (H : Finset (FreePrimeIndex D.movingIdeal Q₀⊕σ)→ℂ) :
    (∑ A : Finset (FreePrimeIndex D.movingIdeal Q₀⊕σ),
      localInactiveWeight ((freePrimeFamily D.movingIdeal Q₀ D.movingSupported).sum S).generator
        ((freePrimeFamily D.movingIdeal Q₀ D.movingSupported).sum S).generator_ne_zero
        (mixedPrimeFunction ((freePrimeFamily D.movingIdeal Q₀ D.movingSupported).sum S).generator
          ((freePrimeFamily D.movingIdeal Q₀ D.movingSupported).sum S).generator_good
          (Sum.elim (fun P => (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val%6)
            (fun _ => 0)) markedSumSlots) A * H A)=
    ∑ B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀), ∑ T : Finset σ,
      ((∏ b∈(Finset.univ:Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀))\B,
        if completedLocalExponent R F b.val=0 then 1-(Ideal.absNorm b.val:ℂ)⁻¹ else 0)*
        ∏ t∈(Finset.univ:Finset σ)\T,(Ideal.absNorm (S.ideal t):ℂ)⁻¹)*H (markedActiveSet E B T) := by
  have hodd : ∀ P : FreePrimeIndex D.movingIdeal Q₀,
      ringChar (Eis⧸(freePrimeFamily D.movingIdeal Q₀ D.movingSupported).ideal P)≠2 := by
    intro P
    exact (supported_factors_good D.movingIdeal D.movingSupported P.val.val
      (Multiset.mem_toFinset.mp P.val.property)).2.2
  have hres : ∀ a, (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count
      (E (Sum.inl a)).val.val%6=1 := by
    intro a
    exact D.primeFiberEquiv_exponent R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inl a)
  have he := joined_inactive_three_blocks (freePrimeFamily D.movingIdeal Q₀ D.movingSupported)
    S hodd hS (fun P => (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val%6)
    (fun _ => Nat.mod_lt _ (by norm_num)) E hres H
  refine he.trans ?_
  apply Finset.sum_congr (by ext B; simp only [Finset.mem_univ])
  intro B hB
  apply Finset.sum_congr (by ext T; simp only [Finset.mem_univ])
  intro T hT
  congr 2
  apply Finset.prod_congr (by ext b; simp only [Finset.mem_sdiff,Finset.mem_univ])
  intro b hb
  rw [D.primeFiberEquiv_exponent R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inr b)]
  change (if completedLocalExponent R F b.val=0 then
    1-(Ideal.absNorm (E (Sum.inr b)).val.val:ℂ)⁻¹ else 0)=_
  rw [D.primeFiberEquiv_val R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inr b)]
  rfl

-- @@ L58-58 verbatim
end

-- @@ L59-59 verbatim
end SevenEighths.InverseReflectedPhase


-- @@ L61-61 verbatim
end OAI
