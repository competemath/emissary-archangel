import OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileCellEnergy
import OAI.NumberTheory.DirichletL.Inversion.FirstGlobalCaps


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators

-- @@ L8-8 verbatim
namespace SevenEighths.InverseMomentFirstOriginalProfile

-- @@ L9-9 verbatim
open InverseMoment InverseMomentFirstChildWindows ActualEisensteinCubic

-- @@ L10-10 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L11-11 verbatim
variable {ι : Type*} [DecidableEq ι] (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]


-- @@ L13-16 verbatim
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma originalNorms_eq_caps : originalNorms p=InverseFirstGlobalCaps.originalNorms p := by
  funext x i
  fin_cases i <;> rfl


-- @@ L18-23 verbatim
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma originalOuterCell_eq_caps (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) :
    originalOuterCell p pool Q k=InverseFirstGlobalCaps.outerCell p pool Q k := by
  unfold originalOuterCell InverseFirstGlobalCaps.outerCell InverseFirstGlobalCaps.outerGate
  ext x
  simp only [Finset.mem_filter,originalNorms_eq_caps,InverseFirstGlobalCaps.originalNorms_outer]


-- @@ L25-36 verbatim
lemma originalChildEnergy_eq_caps (hp : ∀i,p i≠0)
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l : ℕ)
    (negative : Bool) (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ)
    (omega : ℝ→ℂ) (T t Y : ℝ) :
    originalChildEnergy p hp hg hinj pool Q k l negative Ψ m mark omega T t Y=
      ∑x∈InverseFirstGlobalCaps.outerCell p pool Q k,
        firstCanonicalSecondEnergy p hp hg hinj pool x.1 x.2.1 negative Ψ m (divisorElement p x)
          (mark (if negative then x.1.rightExponent else x.1.leftExponent))
          (commonSelector p (fun _=>1) l) omega T t Y := by
  rw [originalChildEnergy,originalOuterCell_eq_caps]


-- @@ L38-38 verbatim
end SevenEighths.InverseMomentFirstOriginalProfile

-- @@ L39-39 verbatim
end


-- @@ L41-41 verbatim
end OAI
