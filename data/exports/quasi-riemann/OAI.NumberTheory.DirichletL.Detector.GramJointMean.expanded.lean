import OAI.NumberTheory.DirichletL.Detector.GramJointSource
import OAI.NumberTheory.DirichletL.Detector.GramMeanLift


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical

-- @@ L8-8 verbatim
namespace SevenEighths.ProbeGramCommon

-- @@ L9-9 verbatim
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion

-- @@ L10-10 verbatim
open ConcretePrimeRowBridge CenteredMomentCorrelation

-- @@ L11-11 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L12-12 verbatim
local notation "Id" => Ideal O

-- @@ L13-13 verbatim
variable {ι : Type*} [Fintype ι]


-- @@ L15-20 verbatim
def jointRemainder (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,goodLambda∉P i) (c : ι→ℕ)
    (J : Id) (n₁ n₂ : O) : ℂ :=
  jointFixed S hS σ C u a b r hr n₁ n₂*
    (idealRowHom n₁ J*star (idealRowHom n₂ (Ideal.span {r})))*globalExtension P hg c n₁ n₂ k


-- @@ L22-34 verbatim
theorem jointExtension_local_factor (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,goodLambda∉P i) (c : ι→ℕ)
    (J p : Id) [p.IsMaximal] (hgp : goodLambda∉p) (e : ℕ) (he : e≠0)
    (hfactor : Ideal.span {r}=J*p^e) (n₁ n₂ : O) :
    jointExtension S hS σ C k u a b r hr P hg c n₁ n₂=
      (actualSextic p hgp^e) (Ideal.Quotient.mk p n₁)*
        jointRemainder S hS σ C k u a b r hr P hg c J n₁ n₂ := by
  have hf : idealRowHom n₁ (Ideal.span {r})=
      idealRowHom n₁ J*(actualSextic p hgp^e) (Ideal.Quotient.mk p n₁) := by
    rw [hfactor,map_mul,map_pow,idealRowHom_prime n₁ p hgp,MulChar.pow_apply' _ he]
  rw [jointExtension,hf,jointRemainder]
  ring


-- @@ L36-47 verbatim
lemma jointRemainder_periodic_first (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,goodLambda∉P i) (c : ι→ℕ)
    (J : Id) (n m y : O) (h : n-m∈jointFixedModulus S hS*(∏i,P i)*J) :
    jointRemainder S hS σ C k u a b r hr P hg c J n y=
      jointRemainder S hS σ C k u a b r hr P hg c J m y := by
  have hf := jointFixed_periodic S hS σ C u a b r hr n y m y
    (Ideal.mul_le_left (Ideal.mul_le_left h)) (by simp)
  have hm := idealRowHom_congr_mod J n m (Ideal.mul_le_right h)
  have hg' := globalExtension_periodic P hg c n y m y k k
    (Ideal.mul_le_right (Ideal.mul_le_left h)) (by simp) (by simp)
  simp only [jointRemainder,hf,hm,hg']


-- @@ L49-68 verbatim
theorem jointExtension_mean_zero (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,goodLambda∉P i) (c : ι→ℕ)
    (J p : Id) [p.IsMaximal] (hgp : goodLambda∉p) (hchar : ringChar (O⧸p)≠2)
    (e : ℕ) (he : ¬6∣e) (hfactor : Ideal.span {r}=J*p^e)
    (hcop : IsCoprime (jointFixedModulus S hS*(∏i,P i)*J) (p^e))
    [Fintype (O⧸jointFixedModulus S hS*(∏i,P i)*J)] [Fintype (O⧸p^e)]
    [Fintype (O⧸(jointFixedModulus S hS*(∏i,P i)*J)*p^e)] (d : O) :
    (∑x : O⧸(jointFixedModulus S hS*(∏i,P i)*J)*p^e,
      ∑y : O⧸(jointFixedModulus S hS*(∏i,P i)*J)*p^e,
        jointExtension S hS σ C k u a b r hr P hg c (d*x.out) (d*y.out))=0 := by
  have he0 : e≠0 := by intro h;exact he (h ▸ dvd_zero 6)
  have he1 : 1≤e := Nat.one_le_iff_ne_zero.mpr he0
  simp_rw [jointExtension_local_factor S hS σ C k u a b r hr P hg c J p hgp e he0 hfactor]
  apply joint_mean_of_local_factor _ p hgp hchar e e he1 he hcop
    (fun x y=>jointRemainder S hS σ C k u a b r hr P hg c J (d*x) (d*y)) _ d
  intro x z y hxz
  apply jointRemainder_periodic_first
  rw [←mul_sub]
  exact (jointFixedModulus S hS*(∏i,P i)*J).mul_mem_left d hxz


-- @@ L70-70 verbatim
end SevenEighths.ProbeGramCommon

-- @@ L71-71 verbatim
end


-- @@ L73-73 verbatim
end OAI
