import OAI.NumberTheory.DirichletL.Reflection.ActiveProducts
import OAI.NumberTheory.DirichletL.Reflection.SlotCoefficients
import OAI.NumberTheory.DirichletL.Reflection.OriginalTransport


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
namespace SevenEighths.InverseReflectedPhase

-- @@ L8-8 verbatim
open scoped Classical BigOperators

-- @@ L9-9 verbatim
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment

-- @@ L10-10 verbatim
noncomputable section

-- @@ L11-11 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L12-12 verbatim
variable {φ σ : Type*} [Fintype φ] [Fintype σ]

-- @@ L13-15 verbatim
variable (tuples : Finset (σ→Ideal Eis))
    (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
    (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i)


-- @@ L17-20 verbatim
def memberTupleFamily (p : tuples) : PrimeFamily σ where
  ideal := p.val
  maximal := hmax p.val p.property
  good := hgood p.val p.property


-- @@ L22-26 verbatim
lemma tuplePrimeFamily_at_member (hne : tuples.Nonempty)
    (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis))) (p : tuples) :
    tuplePrimeFamily tuples hne hmax hgood (slotTupleProduct p.val)=memberTupleFamily tuples hmax hgood p := by
  apply PrimeFamily.eq_of_ideal_eq
  exact tuplePrimeFamily_at_product tuples hne hmax hgood hinj p.val p.property


-- @@ L28-32 verbatim
variable {N a c : Eis} {mode : Bool}
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (hne : tuples.Nonempty)
    (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis)))
    (D : ∀ P : tuples.image slotTupleProduct,IsCoprime K P.val→
      ControlledStratumArithmetic (F.reflected K hK (tuplePrimeFamily tuples hne hmax hgood P.val)).generator N a c mode)


-- @@ L34-38 verbatim
def memberTupleControlled (p : tuples) (hp : IsCoprime K (slotTupleProduct p.val)) :
    ControlledStratumArithmetic (F.reflected K hK (memberTupleFamily tuples hmax hgood p)).generator N a c mode :=
  castControlled (congrArg (fun S => (F.reflected K hK S).generator)
    (tuplePrimeFamily_at_member tuples hmax hgood hne hinj p))
    (D ⟨slotTupleProduct p.val,Finset.mem_image.mpr ⟨p.val,p.property,rfl⟩⟩ hp)


-- @@ L40-51 verbatim
lemma memberTupleControlled_value (p : tuples) (hp : IsCoprime K (slotTupleProduct p.val))
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : φ→ℕ) (W : ℝ→ℂ) (X : ℝ) :
    mixedReflectedValue (memberTupleControlled tuples hmax hgood F K hK hne hinj D p hp) s
      (F.reflected K hK (memberTupleFamily tuples hmax hgood p)).generator_ne_zero hc
      (F.reflected K hK (memberTupleFamily tuples hmax hgood p)).generator_good
      (reflectedExponent j) (slotIndices φ (PrimeIndex K) σ) W X=
    mixedReflectedValue (D ⟨slotTupleProduct p.val,Finset.mem_image.mpr ⟨p.val,p.property,rfl⟩⟩ hp) s
      (F.reflected K hK (tuplePrimeFamily tuples hne hmax hgood (slotTupleProduct p.val))).generator_ne_zero hc
      (F.reflected K hK (tuplePrimeFamily tuples hne hmax hgood (slotTupleProduct p.val))).generator_good
      (reflectedExponent j) (slotIndices φ (PrimeIndex K) σ) W X :=
  mixedReflectedValue_cast _ _ s _ _ hc _ _ _ _ W X


-- @@ L53-60 verbatim
def memberTupleRow
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : φ→ℕ) (W : ℝ→ℂ) (θ X : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ) : ℂ :=
    ∑ p : tuples,if hp:IsCoprime K (slotTupleProduct p.val) then
      r K*aw p.val*mixedReflectedValue (memberTupleControlled tuples hmax hgood F K hK hne hinj D p hp) s
        (F.reflected K hK (memberTupleFamily tuples hmax hgood p)).generator_ne_zero hc
        (F.reflected K hK (memberTupleFamily tuples hmax hgood p)).generator_good
        (reflectedExponent j) (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X else 0


-- @@ L62-89 verbatim
theorem literalWholeRow_eq_member_tuples
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : φ→ℕ) (W : ℝ→ℂ) (θ X : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ) :
    literalWholeRow F K hK (tuplePrimeFamily tuples hne hmax hgood) j
      (tuples.image slotTupleProduct) D s hc W θ X r (slotProductCoefficient tuples aw)=
    ∑ p : tuples,if hp:IsCoprime K (slotTupleProduct p.val) then
      r K*aw p.val*mixedReflectedValue (memberTupleControlled tuples hmax hgood F K hK hne hinj D p hp) s
        (F.reflected K hK (memberTupleFamily tuples hmax hgood p)).generator_ne_zero hc
        (F.reflected K hK (memberTupleFamily tuples hmax hgood p)).generator_good
        (reflectedExponent j) (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X else 0 := by
  let hr : ∀ k∈({K}:Finset (Ideal Eis)),Admissible k := fun k hk => (Finset.mem_singleton.mp hk).symm ▸ hK
  let Ds : ∀ k : ({K}:Finset (Ideal Eis)),∀ P : tuples.image slotTupleProduct,IsCoprime k.val P.val→
      ControlledStratumArithmetic (F.reflected k.val (hr k.val k.property)
        (tuplePrimeFamily tuples hne hmax hgood P.val)).generator N a c mode := by
    intro k
    rcases k with ⟨k,hk⟩
    have hh := Finset.mem_singleton.mp hk
    subst k
    exact D
  have he := literalWholeRow_eq_active_tuples F {K} tuples hne hmax hgood hinj
    hr j Ds s hc W θ X r aw ⟨K,Finset.mem_singleton_self K⟩
  convert he using 1
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hk : IsCoprime K (slotTupleProduct p.val)
  · simp only [dite_eq_left hk]
    rw [memberTupleControlled_value]
  · simp only [dite_eq_right hk]

-- @@ L90-90 verbatim
end

-- @@ L91-91 verbatim
end SevenEighths.InverseReflectedPhase


-- @@ L93-93 verbatim
end OAI
