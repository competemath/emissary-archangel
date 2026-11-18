import OAI.NumberTheory.DirichletL.Descent.ActualChildStateSupport


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical

-- @@ L7-7 verbatim
namespace SevenEighths.InverseMoment

-- @@ L8-8 verbatim
open ActualEisensteinCubic InverseSecondFibers CompletedGauss

-- @@ L9-9 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L11-16 verbatim
lemma actual_inherited_puncture_dvd (m : O) (γ : OuterTriple) :
    m∣actualSecondInheritedPuncture m γ := by
  refine ⟨ConcretePrimeRowBridge.idealGenerator γ.quotient*primaryGenerator γ.q0*
    primaryGenerator γ.residual,?_⟩
  unfold actualSecondInheritedPuncture actualSecondPuncture
  ring


-- @@ L18-21 verbatim
lemma actual_inherited_radical_puncture_span (m : O) (γ : OuterTriple) :
    Ideal.span {actualSecondInheritedRadicalPuncture m γ}=
      (Ideal.span {actualSecondInheritedPuncture m γ}:Ideal O).radical :=
  ConcretePrimeRowBridge.span_idealGenerator _


-- @@ L23-28 verbatim
lemma actual_inherited_radical_preserves_support (m : O) (γ : OuterTriple) :
    (Ideal.span {m}:Ideal O).radical∣Ideal.span {actualSecondInheritedRadicalPuncture m γ} := by
  rw [actual_inherited_radical_puncture_span,Ideal.dvd_iff_le]
  apply Ideal.radical_mono
  apply Ideal.span_singleton_le_span_singleton.mpr
  exact actual_inherited_puncture_dvd m γ


-- @@ L30-35 verbatim
lemma actual_inherited_radical_preserves_fixed (m : O) (γ : OuterTriple) (Q : Ideal O)
    (hQ : Q.radical=Q) (hparent : Q∣Ideal.span {m}) :
    Q∣Ideal.span {actualSecondInheritedRadicalPuncture m γ} := by
  apply dvd_trans _ (actual_inherited_radical_preserves_support m γ)
  rw [Ideal.dvd_iff_le,←hQ]
  exact Ideal.radical_mono (Ideal.dvd_iff_le.mp hparent)


-- @@ L37-40 verbatim
lemma actual_inherited_radical_is_radical (m : O) (γ : OuterTriple) :
    (Ideal.span {actualSecondInheritedRadicalPuncture m γ}:Ideal O).radical=
      Ideal.span {actualSecondInheritedRadicalPuncture m γ} := by
  rw [actual_inherited_radical_puncture_span,Ideal.radical_idem]


-- @@ L42-42 verbatim
end SevenEighths.InverseMoment

-- @@ L43-43 verbatim
end


-- @@ L45-45 verbatim
end OAI
