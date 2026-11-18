import OAI.NumberTheory.DirichletL.Reflection.OriginalSlotSupport
import OAI.NumberTheory.DirichletL.Reflection.OriginalTransport


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
namespace SevenEighths.InverseReflectedPhase

-- @@ L7-7 verbatim
open scoped Classical BigOperators

-- @@ L8-8 verbatim
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment

-- @@ L9-9 verbatim
noncomputable section

-- @@ L10-10 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L11-11 verbatim
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {m f z : Eis} (D : GoodMaskRowData m f z)

-- @@ L12-17 verbatim
variable (R I F Q₀ : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime Q₀ (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))


-- @@ L19-21 verbatim
variable (L : σ→Finset (Ideal Eis))
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)


-- @@ L23-32 verbatim
lemma originalSplit_active_family (T : Finset σ) (p : originalSlotChoices D Q₀ L) :
    (slotChoiceFamily L hmax hgood p.val).restrict T=
      slotChoiceFamily (fun i : T => L i.val) (fun i => hmax i.val) (fun i => hgood i.val)
        ((originalSlotSplit D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T p).2.val) := by
  let e := originalSlotSplit D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T
  calc
    _ = (slotChoiceFamily L hmax hgood (e.symm (e p)).val).restrict T :=
      congrArg (fun q : originalSlotChoices D Q₀ L => (slotChoiceFamily L hmax hgood q.val).restrict T) (e.symm_apply_apply p).symm
    _ = _ := by
      rw [originalSlotSplit_symm_val,slotChoiceFamily_active]


-- @@ L34-34 verbatim
variable {τ : Type*} [Fintype τ] (Frozen : PrimeFamily τ) {N a c : Eis} {mode : Bool}

-- @@ L35-42 verbatim
variable (T : Finset σ)
    (C : ∀ _b : supportedSlotChoices (fun i : {i // i∉T} => L i.val)
        ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)),
      ∀ p : supportedSlotChoices (fun i : T => L i.val)
        ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)),
      ControlledStratumArithmetic (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F))
        (rowResidualPart_admissible I (Ideal.span {m}*F) hbad)
        (slotChoiceFamily (fun i : T => L i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator N a c mode)


-- @@ L44-52 verbatim
def originalSplitControlled (p : originalSlotChoices D Q₀ L) :
    ControlledStratumArithmetic (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F))
      (rowResidualPart_admissible I (Ideal.span {m}*F) hbad)
      ((slotChoiceFamily L hmax hgood p.val).restrict T)).generator N a c mode :=
  castControlled (congrArg (fun S => (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F))
    (rowResidualPart_admissible I (Ideal.span {m}*F) hbad) S).generator)
    (originalSplit_active_family D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T p).symm)
    (C (originalSlotSplit D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T p).1
      (originalSlotSplit D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T p).2)


-- @@ L54-71 verbatim
lemma originalSplitControlled_value (p : originalSlotChoices D Q₀ L)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (jF : τ→ℕ) (W : ℝ→ℂ) (X : ℝ) :
    mixedReflectedValue
      (originalSplitControlled D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood Frozen T C p) s
      (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad)
        ((slotChoiceFamily L hmax hgood p.val).restrict T)).generator_ne_zero hc
      (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad)
        ((slotChoiceFamily L hmax hgood p.val).restrict T)).generator_good
      (reflectedExponent jF) (slotIndices τ (PrimeIndex (rowResidualPart I (Ideal.span {m}*F))) T) W X=
    let q := originalSlotSplit D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T p
    mixedReflectedValue (C q.1 q.2) s
      (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad)
        (slotChoiceFamily (fun i : T => L i.val) (fun i => hmax i.val) (fun i => hgood i.val) q.2.val)).generator_ne_zero hc
      (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad)
        (slotChoiceFamily (fun i : T => L i.val) (fun i => hmax i.val) (fun i => hgood i.val) q.2.val)).generator_good
      (reflectedExponent jF) (slotIndices τ (PrimeIndex (rowResidualPart I (Ideal.span {m}*F))) T) W X := by
  exact mixedReflectedValue_cast _ _ s _ _ hc _ _ _ _ W X


-- @@ L73-73 verbatim
end

-- @@ L74-74 verbatim
end SevenEighths.InverseReflectedPhase


-- @@ L76-76 verbatim
end OAI
