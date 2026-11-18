import OAI.NumberTheory.DirichletL.Reflection.WholePair
import OAI.NumberTheory.DirichletL.Reflection.TupleFamily


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
namespace SevenEighths.InverseReflectedPhase

-- @@ L7-7 verbatim
open scoped Classical BigOperators

-- @@ L8-8 verbatim
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment

-- @@ L9-9 verbatim
noncomputable section

-- @@ L10-10 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L11-11 verbatim
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}


-- @@ L13-20 verbatim
lemma slotProductCoefficient_norm (tuples : Finset (σ→Ideal Eis))
    (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis)))
    (aw : (σ→Ideal Eis)→ℂ) (haw : ∀ p∈tuples,‖aw p‖≤1)
    (P : Ideal Eis) (hP : P∈tuples.image slotTupleProduct) :
    ‖slotProductCoefficient tuples aw P‖≤1 := by
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hP
  rw [slotProductCoefficient_at_product tuples hinj aw p hp]
  exact haw p hp


-- @@ L22-39 verbatim
def activeTupleReflectedRow
    (F : PrimeFamily φ) (rows : Finset (Ideal Eis))
    (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
    (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
    (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i)
    (hrows : ∀ K∈rows,Admissible K) (jF : φ→ℕ)
    (D : ∀ K : rows,∀ P : tuples.image slotTupleProduct,IsCoprime K.val P.val→
      ControlledStratumArithmetic (F.reflected K.val (hrows K.val K.property)
        (tuplePrimeFamily tuples hne hmax hgood P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (W : ℝ→ℂ) (θ X : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ) (K : rows) : ℂ :=
    ∑ p : tuples,if hp:IsCoprime K.val (slotTupleProduct p.val) then
      r K.val*aw p.val*mixedReflectedValue
        (D K ⟨slotTupleProduct p.val,Finset.mem_image.mpr ⟨p.val,p.property,rfl⟩⟩ hp) s
        (F.reflected K.val (hrows K.val K.property) (tuplePrimeFamily tuples hne hmax hgood (slotTupleProduct p.val))).generator_ne_zero hc
        (F.reflected K.val (hrows K.val K.property) (tuplePrimeFamily tuples hne hmax hgood (slotTupleProduct p.val))).generator_good
        (reflectedExponent jF) (slotIndices φ (PrimeIndex K.val) σ)
        (CompletedHeight.normTwistedSource W θ) X else 0


-- @@ L41-68 verbatim
theorem literalWholeRow_eq_active_tuples
    (F : PrimeFamily φ) (rows : Finset (Ideal Eis))
    (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
    (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
    (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i)
    (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis)))
    (hrows : ∀ K∈rows,Admissible K) (jF : φ→ℕ)
    (D : ∀ K : rows,∀ P : tuples.image slotTupleProduct,IsCoprime K.val P.val→
      ControlledStratumArithmetic (F.reflected K.val (hrows K.val K.property)
        (tuplePrimeFamily tuples hne hmax hgood P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (W : ℝ→ℂ) (θ X : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ) (K : rows) :
    literalWholeRow F K.val (hrows K.val K.property) (tuplePrimeFamily tuples hne hmax hgood)
      jF (tuples.image slotTupleProduct) (D K) s hc W θ X r (slotProductCoefficient tuples aw)=
    ∑ p : tuples,if hp:IsCoprime K.val (slotTupleProduct p.val) then
      r K.val*aw p.val*mixedReflectedValue
        (D K ⟨slotTupleProduct p.val,Finset.mem_image.mpr ⟨p.val,p.property,rfl⟩⟩ hp) s
        (F.reflected K.val (hrows K.val K.property) (tuplePrimeFamily tuples hne hmax hgood (slotTupleProduct p.val))).generator_ne_zero hc
        (F.reflected K.val (hrows K.val K.property) (tuplePrimeFamily tuples hne hmax hgood (slotTupleProduct p.val))).generator_good
        (reflectedExponent jF) (slotIndices φ (PrimeIndex K.val) σ)
        (CompletedHeight.normTwistedSource W θ) X else 0 := by
  rw [literalWholeRow_eq_pairs F rows _ _ hrows jF D s hc W θ X r _ K,Finset.sum_image hinj]
  rw [←Finset.sum_coe_sort tuples]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [literalPairEntry,dite_eq_left K.property,
    dite_eq_left (Finset.mem_image.mpr ⟨p.val,p.property,rfl⟩),
    slotProductCoefficient_at_product tuples hinj aw p.val p.property]

-- @@ L69-69 verbatim
end

-- @@ L70-70 verbatim
end SevenEighths.InverseReflectedPhase


-- @@ L72-72 verbatim
end OAI
