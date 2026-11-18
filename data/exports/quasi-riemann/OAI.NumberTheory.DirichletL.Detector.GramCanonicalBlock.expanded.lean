import OAI.NumberTheory.DirichletL.Detector.GramClassification
import OAI.NumberTheory.DirichletL.Detector.GramLatticeWindow


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical SchwartzMap ContDiff

-- @@ L8-8 verbatim
namespace SevenEighths.ProbeGramCommon

-- @@ L9-9 verbatim
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion

-- @@ L10-10 verbatim
open ConcreteTraceCRT UniqueFactorizationMonoid

-- @@ L11-11 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L12-12 verbatim
local notation "Id" => Ideal O


-- @@ L14-18 verbatim
def canonicalLatticeBlock (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (C : SupportedIdeal) (k : GramFrequency) (d : O) (W : ℝ→ℂ) (U : SchwartzMap ℝ ℂ)
    (v T N : ℝ) : ℂ :=
  ∑'m : O×O,canonicalJoint S hS σ C k (d*m.1) (d*m.2)*
    shellProfile W v U T (‖eisEmbedding m.1‖^2/N) (‖eisEmbedding m.2‖^2/N)


-- @@ L20-50 verbatim
theorem canonical_nonexceptional_block (A B : ℕ) (hA : 2<A) (a₀ b₀ : ℝ)
    (ha₀ : 0<a₀) (hab : a₀<b₀) :
    ∃(J : ℕ)(H : Finset (ℕ×ℕ)),
      ∀(W : ℝ→ℂ)(_hs : Function.support W⊆Set.Icc a₀ b₀)(_hW : ContDiff ℝ ∞ W),
      ∃K : ℝ,0<K ∧ ∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (C : SupportedIdeal)(k : GramFrequency),¬ExceptionalFrequency S hS C k→
      ∀(d : O)(U : SchwartzMap ℝ ℂ)(v T N : ℝ),0≤T→0<N→
        ‖canonicalLatticeBlock S hS σ C k d W U v T N‖≤
        K*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J/(1+T)^B*
          (Ideal.absNorm C.val:ℝ)*N^2*
          min 1 (((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm C.val*
            Ideal.absNorm (Ideal.span {k.val})/N)^A) := by
  obtain ⟨J,H,hsource⟩ := literal_nonexceptional_source A B hA a₀ b₀ ha₀ hab
  refine ⟨J,H,?_⟩
  intro W hs hW
  obtain ⟨K,hK,hsource⟩ := hsource W hs hW
  refine ⟨K,hK,?_⟩
  intro S hS σ C k hk d U v T N hT hN
  obtain ⟨p,hp,hout,he⟩ := nonexceptional_prime S hS C k hk
  let : p.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  have hg := outside_exceptional_good S hS C p hp hout
  have hd := outside_exceptional_not_dvd S hS C p hp hout
  have hcspan := (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ C.property)).1
  have hf : Ideal.span {primaryGenerator C.val}=∏i : GramPrime C,gramPrime C i^gramExponent C i := hcspan.trans (gramPrime_product C)
  have hh := hsource S hS σ (primaryGenerator C.val) k.val
    (supported_primaryGenerator_ne_zero _ C.property) k.property
    (gramNumeratorData k).unit (gramNumeratorData k).lambdaExponent (gramNumeratorData k).twoExponent
    (gramNumeratorData k).good (gramNumeratorData k).supported (gramNumeratorData k).factor
    (gramPrime C) (gramPrime_good C) (gramExponent C) (gramExponent_pos C) hf
    p hp.ne_zero hg.1 hg.2 hd.1 hd.2 he U v T hT d N hN
  simpa only [canonicalLatticeBlock,canonicalJoint,hcspan] using hh.2


-- @@ L52-52 verbatim
end SevenEighths.ProbeGramCommon

-- @@ L53-53 verbatim
end


-- @@ L55-55 verbatim
end OAI
