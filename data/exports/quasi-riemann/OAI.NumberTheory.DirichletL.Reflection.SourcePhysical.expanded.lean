import OAI.NumberTheory.DirichletL.Reflection.CanonicalInactiveEnergy


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace SevenEighths.InverseReflectedPhase

-- @@ L6-6 verbatim
open scoped Classical BigOperators

-- @@ L7-7 verbatim
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment

-- @@ L8-8 verbatim
noncomputable section

-- @@ L9-9 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L10-10 verbatim
variable {σ φ τ : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ]

-- @@ L11-11 verbatim
variable {N a c : Eis} {mode : Bool}

-- @@ L12-14 verbatim
variable (G : PrimeFamily τ) (FF : φ→Ideal Eis) (rows : Finset (Ideal Eis)) (hrows : ∀ K∈rows,Admissible K)
    (lists : σ→Finset (Ideal Eis)) (hmax : ∀ i,∀ P∈lists i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P) (T : Finset σ)


-- @@ L16-20 verbatim
abbrev OriginalSplitCompletion :=
    ∀ K : rows,∀ _b : supportedSlotChoices (fun i : {i // i∉T} => lists i.val) FF K.val,
      ∀ p : supportedSlotChoices (fun i : T => lists i.val) FF K.val,
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property)
        (slotChoiceFamily (fun i : T => lists i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator N a c mode


-- @@ L22-34 verbatim
def originalInactivePhysical
    (D : OriginalSplitCompletion (N:=N) (a:=a) (c:=c) (mode:=mode) G FF rows hrows lists hmax hgood T)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (jF : τ→ℕ) (W : ℝ→ℂ) (X : ℝ) (w : ∀ i,lists i→ℂ) (K : rows) : ℂ :=
    ∑ b : supportedSlotChoices (fun i : {i // i∉T} => lists i.val) FF K.val,
      ((∏ i : {i // i∉T},(Ideal.absNorm (b.val i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b.val i)))*
      ∑ p : supportedSlotChoices (fun i : T => lists i.val) FF K.val,
        (∏ i : T,w i.val (p.val i))*mixedReflectedValue (D K b p) s
        (G.reflected K.val (hrows K.val K.property)
          (slotChoiceFamily (fun i : T => lists i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator_ne_zero hc
        (G.reflected K.val (hrows K.val K.property)
          (slotChoiceFamily (fun i : T => lists i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator_good
        (reflectedExponent jF) (slotIndices τ (PrimeIndex K.val) T) W X

-- @@ L35-35 verbatim
end

-- @@ L36-36 verbatim
end SevenEighths.InverseReflectedPhase


-- @@ L38-38 verbatim
end OAI
