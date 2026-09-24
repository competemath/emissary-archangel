module

public import Foundation.FirstOrder.Incompleteness.StandardProvability
public import Foundation.FirstOrder.Arithmetic.R0.Representation
public import Foundation.FirstOrder.Bootstrapping.Syntax.CraigTrick


-- @@ L7-7 verbatim
@[expose] public section

-- @@ L8-10 verbatim
/-!
# Gödel's first incompleteness theorem for arithmetic theories stronger than $\mathsf{R_0}$
-/


-- @@ L12-12 verbatim
namespace FFL.FirstOrder.Arithmetic


-- @@ L14-14 verbatim
open FFL.Entailment Bootstrapping Bootstrapping.Arithmetic


-- @@ L16-45 verbatim
/-- Gödel's first incompleteness theorem-/
theorem incomplete (T : ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1] :
    Incomplete T := by
  have con : Consistent T := inferInstance
  let D : ℕ → Prop := fun φ : ℕ ↦
    IsSemiformula ℒₒᵣ 1 φ ∧ Provable T (neg ℒₒᵣ <| subst ℒₒᵣ ?[numeral φ] φ)
  have D_re : REPred D := by
    have : 𝚺₁-Predicate fun φ : ℕ ↦
        IsSemiformula ℒₒᵣ 1 φ ∧ Provable T (neg ℒₒᵣ <| subst ℒₒᵣ ?[numeral φ] φ) := by
      definability
    exact rePred_iff_sigma1.mpr this
  have D_spec (φ : ArithmeticSemisentence 1) : D ⌜φ⌝ ↔ T ⊢ ∼φ/[⌜φ⌝] := by
    simp [D, ←provable_iff_provable, Sentence.quote_def,
      Rewriting.emb_subst_eq_subst_coe₁, Semiformula.quote_def]
  let δ : ArithmeticSemisentence 1 := codeOfREPred D
  have (n : ℕ) : D n ↔ T ⊢ δ/[↑n] := by
    simpa [Semiformula.coe_subst_eq_subst_coe₁] using rePred_weak_representation D_re
  let π : ArithmeticSentence := δ/[⌜δ⌝]
  have : T ⊢ π ↔ T ⊢ ∼π := calc
    T ⊢ π ↔ T ⊢ δ/[⌜δ⌝]  := by rfl
    _     ↔ D ⌜δ⌝        := by simpa using (this ⌜δ⌝).symm
    _     ↔ T ⊢ ∼δ/[⌜δ⌝] := D_spec δ
    _     ↔ T ⊢ ∼π       := by rfl
  refine incomplete_def.mpr ⟨π, ?_, ?_⟩
  · intro h
    exact not_consistent_iff_inconsistent.mpr
      (inconsistent_of_provable_of_unprovable h (this.mp h)) inferInstance
  · intro h
    exact not_consistent_iff_inconsistent.mpr
      (inconsistent_of_provable_of_unprovable (this.mpr h) h) inferInstance


-- @@ L47-50 verbatim
theorem exists_true_but_unprovable_sentence_of_sigma1sound
    (T : ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1] :
    ∃ δ : ArithmeticSentence, ℕ↓[ℒₒᵣ] ⊧ δ ∧ T ⊬ δ :=
  exists_true_but_unprovable_sentence_of_incomplete (Arithmetic.incomplete T)


-- @@ L52-53 verbatim
instance {T : ArithmeticTheory} [T.RE] [𝗥₀ ⪯ T] : 𝗥₀ ⪯ T.craig :=
  WeakerThan.trans (𝓣 := T) inferInstance (inferInstance : T ⪯ T.craig)


-- @@ L55-56 verbatim
instance {T : ArithmeticTheory} [T.RE] [T.SoundOnHierarchy 𝚺 1] : ArithmeticTheory.SoundOnHierarchy (T.craig) 𝚺 1 :=
  ArithmeticTheory.SoundOn.of_weakerThan _ T T.craig


-- @@ L58-60 verbatim
/-- Gödel's first incompleteness theorem for r.e. theories -/
theorem incomplete_of_RE (T : ArithmeticTheory) [T.RE] [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1] : Incomplete T :=
  (Equiv.incomplete_iff (inferInstance : T ≊ T.craig)).mpr (incomplete T.craig)


-- @@ L62-65 verbatim
theorem exists_true_but_unprovable_sentence_of_RE_of_sigma1sound
    (T : ArithmeticTheory) [T.RE] [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1] :
    ∃ δ : ArithmeticSentence, ℕ↓[ℒₒᵣ] ⊧ δ ∧ T ⊬ δ :=
  exists_true_but_unprovable_sentence_of_incomplete (incomplete_of_RE T)


-- @@ L67-71 verbatim
instance {T : ArithmeticTheory} [ℕ↓[ℒₒᵣ] ⊧* T] [T.Δ₁] [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1] : T ⪱ 𝗧𝗔 := by
  constructor;
  . infer_instance
  . obtain ⟨δ, δTrue, δUnprov⟩ := exists_true_but_unprovable_sentence_of_sigma1sound T;
    exact not_weakerThan_iff.mpr ⟨δ, TA.provable_iff.mpr δTrue, δUnprov⟩


-- @@ L73-73 verbatim
end FFL.FirstOrder.Arithmetic
