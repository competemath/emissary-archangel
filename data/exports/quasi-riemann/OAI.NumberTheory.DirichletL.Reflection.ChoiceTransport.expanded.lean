import OAI.NumberTheory.DirichletL.Reflection.FixedTuples
import OAI.NumberTheory.DirichletL.Reflection.OriginalTransport


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
variable {σ φ τ : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ]


-- @@ L13-19 verbatim
def fixedTupleFamily (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis)
    (hne : (fixedSlotTupleSet L F).Nonempty)
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P) (P : Ideal Eis) : PrimeFamily σ :=
  tuplePrimeFamily (fixedSlotTupleSet L F) hne
    (fun p hp i => hmax i _ (((mem_fixedSlotTupleSet L F p).mp hp).1 i))
    (fun p hp i => hgood i _ (((mem_fixedSlotTupleSet L F p).mp hp).1 i)) P


-- @@ L21-31 verbatim
lemma fixedTupleFamily_at_choice (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis)
    (hne : (fixedSlotTupleSet L F).Nonempty)
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)
    (hL : Pairwise (fun i j => Disjoint (L i) (L j))) (hprime : ∀ i,∀ P∈L i,Prime P)
    (p : ∀ i,L i) (hp : ∀ j i,(p i).val≠F j) :
    fixedTupleFamily L F hne hmax hgood (∏ i,(p i).val)=slotChoiceFamily L hmax hgood p := by
  apply PrimeFamily.eq_of_ideal_eq
  exact tuplePrimeFamily_at_product (fixedSlotTupleSet L F) hne _ _
    (fixedSlotTupleSet_product_injective L F hL hprime) (fun i => (p i).val)
    ((mem_fixedSlotTupleSet L F _).mpr ⟨fun i => (p i).property,hp⟩)


-- @@ L33-34 verbatim
def fixedTupleCoefficient (L : σ→Finset (Ideal Eis)) (w : ∀ i,L i→ℂ) (p : σ→Ideal Eis) : ℂ :=
  if hp:∀ i,p i∈L i then ∏ i,w i ⟨p i,hp i⟩ else 0


-- @@ L36-39 verbatim
omit [DecidableEq σ] in
lemma fixedTupleCoefficient_at (L : σ→Finset (Ideal Eis)) (w : ∀ i,L i→ℂ) (p : ∀ i,L i) :
    fixedTupleCoefficient L w (fun i => (p i).val)=∏ i,w i (p i) := by
  simp only [fixedTupleCoefficient,dite_eq_left (show ∀ i,(p i).val∈L i from fun i => (p i).property)]


-- @@ L41-47 verbatim
omit [DecidableEq σ] in
lemma fixedTupleCoefficient_norm (L : σ→Finset (Ideal Eis)) (w : ∀ i,L i→ℂ)
    (hw : ∀ i P,‖w i P‖≤1) (p : σ→Ideal Eis) : ‖fixedTupleCoefficient L w p‖≤1 := by
  unfold fixedTupleCoefficient
  split
  · exact slot_coefficient_norm L w hw _
  · simp


-- @@ L49-49 verbatim
variable {N a c : Eis} {mode : Bool}

-- @@ L50-58 verbatim
variable (G : PrimeFamily τ) (K : Ideal Eis) (hK : Admissible K)
    (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis)
    (hne : (fixedSlotTupleSet L F).Nonempty)
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)
    (hL : Pairwise (fun i j => Disjoint (L i) (L j))) (hprime : ∀ i,∀ P∈L i,Prime P)
    (D : ∀ P : (fixedSlotTupleSet L F).image slotTupleProduct,IsCoprime K P.val→
      ControlledStratumArithmetic (G.reflected K hK (fixedTupleFamily L F hne hmax hgood P.val)).generator N a c mode)
    (p : supportedSlotChoices L F K)


-- @@ L60-65 verbatim
def activeChoiceControlled :
      ControlledStratumArithmetic (G.reflected K hK (slotChoiceFamily L hmax hgood p.val)).generator N a c mode :=
  castControlled (congrArg (fun S => (G.reflected K hK S).generator)
    (fixedTupleFamily_at_choice L F hne hmax hgood hL hprime p.val p.property.2))
    (D ⟨∏ i,(p.val i).val,Finset.mem_image.mpr
      ⟨fun i => (p.val i).val,(mem_fixedSlotTupleSet L F _).mpr ⟨fun i => (p.val i).property,p.property.2⟩,rfl⟩⟩ p.property.1)


-- @@ L67-79 verbatim
lemma activeChoiceControlled_value
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : τ→ℕ) (W : ℝ→ℂ) (X : ℝ) :
    mixedReflectedValue (activeChoiceControlled G K hK L F hne hmax hgood hL hprime D p) s
      (G.reflected K hK (slotChoiceFamily L hmax hgood p.val)).generator_ne_zero hc
      (G.reflected K hK (slotChoiceFamily L hmax hgood p.val)).generator_good
      (reflectedExponent j) (slotIndices τ (PrimeIndex K) σ) W X=
    mixedReflectedValue (D ⟨∏ i,(p.val i).val,Finset.mem_image.mpr
      ⟨fun i => (p.val i).val,(mem_fixedSlotTupleSet L F _).mpr ⟨fun i => (p.val i).property,p.property.2⟩,rfl⟩⟩ p.property.1) s
      (G.reflected K hK (fixedTupleFamily L F hne hmax hgood (∏ i,(p.val i).val))).generator_ne_zero hc
      (G.reflected K hK (fixedTupleFamily L F hne hmax hgood (∏ i,(p.val i).val))).generator_good
      (reflectedExponent j) (slotIndices τ (PrimeIndex K) σ) W X := by
  exact mixedReflectedValue_cast _ _ s _ _ hc _ _ _ _ W X


-- @@ L81-107 verbatim
theorem literalWholeRow_eq_original_choices
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : τ→ℕ) (W : ℝ→ℂ) (θ X : ℝ) (r : Ideal Eis→ℂ) (w : ∀ i,L i→ℂ) :
    literalWholeRow G K hK (fixedTupleFamily L F hne hmax hgood) j
      ((fixedSlotTupleSet L F).image slotTupleProduct) D s hc W θ X r
      (slotProductCoefficient (fixedSlotTupleSet L F) (fixedTupleCoefficient L w))=
    ∑ p : supportedSlotChoices L F K,r K*(∏ i,w i (p.val i))*
      mixedReflectedValue (activeChoiceControlled G K hK L F hne hmax hgood hL hprime D p) s
        (G.reflected K hK (slotChoiceFamily L hmax hgood p.val)).generator_ne_zero hc
        (G.reflected K hK (slotChoiceFamily L hmax hgood p.val)).generator_good
        (reflectedExponent j) (slotIndices τ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X := by
  let e := supportedSlotProductEquiv L F hL hprime K
  unfold literalWholeRow
  rw [←e.sum_comp]
  apply Finset.sum_congr rfl
  intro p hp
  rw [activeChoiceControlled_value G K hK L F hne hmax hgood hL hprime D p s hc j]
  have hcft : slotProductCoefficient (fixedSlotTupleSet L F) (fixedTupleCoefficient L w)
      (e p).val.val=∏ i,w i (p.val i) := by
    change slotProductCoefficient (fixedSlotTupleSet L F) (fixedTupleCoefficient L w)
      (slotTupleProduct (fun i => (p.val i).val))=_
    rw [slotProductCoefficient_at_product (fixedSlotTupleSet L F)
      (fixedSlotTupleSet_product_injective L F hL hprime) (fixedTupleCoefficient L w)
      (fun i => (p.val i).val) ((mem_fixedSlotTupleSet L F _).mpr ⟨fun i => (p.val i).property,p.property.2⟩)]
    exact fixedTupleCoefficient_at L w p.val
  rw [hcft]
  rfl


-- @@ L109-109 verbatim
end

-- @@ L110-110 verbatim
end SevenEighths.InverseReflectedPhase


-- @@ L112-112 verbatim
end OAI
