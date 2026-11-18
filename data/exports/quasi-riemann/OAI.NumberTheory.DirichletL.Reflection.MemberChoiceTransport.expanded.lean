import OAI.NumberTheory.DirichletL.Reflection.TupleMembers
import OAI.NumberTheory.DirichletL.Reflection.ChoiceTransport
import OAI.NumberTheory.DirichletL.Reflection.MarkedTuples


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
variable {σ φ τ : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ]

-- @@ L13-15 verbatim
variable (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis)
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)


-- @@ L17-18 verbatim
abbrev originalTupleMax : ∀ p∈fixedSlotTupleSet L F,∀ i,(p i).IsMaximal :=
  fun p hp i => hmax i _ (((mem_fixedSlotTupleSet L F p).mp hp).1 i)

-- @@ L19-20 verbatim
abbrev originalTupleGood : ∀ p∈fixedSlotTupleSet L F,∀ i,ConcretePrimeRowBridge.goodLambda∉p i :=
  fun p hp i => hgood i _ (((mem_fixedSlotTupleSet L F p).mp hp).1 i)


-- @@ L22-22 verbatim
variable {N a c : Eis} {mode : Bool} (G : PrimeFamily τ) (K : Ideal Eis) (hK : Admissible K)

-- @@ L23-25 verbatim
variable (D : ∀ p : fixedSlotTupleSet L F,IsCoprime K (slotTupleProduct p.val)→
    ControlledStratumArithmetic (G.reflected K hK
      (memberTupleFamily (fixedSlotTupleSet L F) (originalTupleMax L F hmax) (originalTupleGood L F hgood) p)).generator N a c mode)


-- @@ L27-29 verbatim
def memberChoiceControlled (p : supportedSlotChoices L F K) :
    ControlledStratumArithmetic (G.reflected K hK (slotChoiceFamily L hmax hgood p.val)).generator N a c mode :=
  D ((supportedSlotTupleEquiv L F K) p).val ((supportedSlotTupleEquiv L F K) p).property


-- @@ L31-59 verbatim
theorem member_source_eq_original_choices
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (jF : τ→ℕ) (W : ℝ→ℂ) (X : ℝ) (r : ℂ) (w : ∀ i,L i→ℂ) :
    (∑ p : fixedSlotTupleSet L F,if hp:IsCoprime K (slotTupleProduct p.val) then
      r*fixedTupleCoefficient L w p.val*mixedReflectedValue (D p hp) s
        (G.reflected K hK (memberTupleFamily (fixedSlotTupleSet L F)
          (originalTupleMax L F hmax) (originalTupleGood L F hgood) p)).generator_ne_zero hc
        (G.reflected K hK (memberTupleFamily (fixedSlotTupleSet L F)
          (originalTupleMax L F hmax) (originalTupleGood L F hgood) p)).generator_good
        (reflectedExponent jF) (slotIndices τ (PrimeIndex K) σ) W X else 0)=
    ∑ p : supportedSlotChoices L F K,r*(∏ i,w i (p.val i))*
      mixedReflectedValue (memberChoiceControlled L F hmax hgood G K hK D p) s
        (G.reflected K hK (slotChoiceFamily L hmax hgood p.val)).generator_ne_zero hc
        (G.reflected K hK (slotChoiceFamily L hmax hgood p.val)).generator_good
        (reflectedExponent jF) (slotIndices τ (PrimeIndex K) σ) W X := by
  let e := supportedSlotTupleEquiv L F K
  have he := sum_subtype_dite_decidable (fun p : fixedSlotTupleSet L F => IsCoprime K (slotTupleProduct p.val))
    (fun p hp => r*fixedTupleCoefficient L w p.val*mixedReflectedValue (D p hp) s
      (G.reflected K hK (memberTupleFamily (fixedSlotTupleSet L F)
        (originalTupleMax L F hmax) (originalTupleGood L F hgood) p)).generator_ne_zero hc
      (G.reflected K hK (memberTupleFamily (fixedSlotTupleSet L F)
        (originalTupleMax L F hmax) (originalTupleGood L F hgood) p)).generator_good
      (reflectedExponent jF) (slotIndices τ (PrimeIndex K) σ) W X)
  rw [←he,←e.sum_comp]
  apply Finset.sum_congr rfl
  intro p hp
  change r*fixedTupleCoefficient L w (fun i => (p.val i).val)*_=_
  rw [fixedTupleCoefficient_at]
  rfl

-- @@ L60-60 verbatim
end

-- @@ L61-61 verbatim
end SevenEighths.InverseReflectedPhase


-- @@ L63-63 verbatim
end OAI
