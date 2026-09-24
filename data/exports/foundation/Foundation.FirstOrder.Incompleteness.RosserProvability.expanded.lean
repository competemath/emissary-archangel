module

public import Foundation.FirstOrder.Incompleteness.WitnessComparison
public import Foundation.FirstOrder.Bootstrapping.Syntax.CraigTrick


-- @@ L6-6 verbatim
@[expose] public section

-- @@ L7-9 verbatim
/-!
# Rosser's provability predicate
-/


-- @@ L11-11 verbatim
namespace FFL.FirstOrder.Arithmetic.Bootstrapping


-- @@ L13-13 verbatim
open FFL.Entailment


-- @@ L15-15 verbatim
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]


-- @@ L17-17 verbatim
variable {L : Language} [L.Encodable] [L.LORDefinable]


-- @@ L19-19 verbatim
variable (T : Theory L) [T.Δ₁]


-- @@ L21-21 verbatim
def _root_.FFL.FirstOrder.Theory.RosserProvable (φ : V) : Prop := T.ProvabilityComparisonLE φ (neg L φ)


-- @@ L23-23 verbatim
section


-- @@ L25-26 verbatim
noncomputable def _root_.FFL.FirstOrder.Theory.rosserProvable : 𝚺₁.Semisentence 1 := .mkSigma
  “φ. ∃ nφ, !(negGraph L) nφ φ ∧ !T.provabilityComparisonLE φ nφ”


-- @@ L28-30 verbatim
instance _root_.FFL.FirstOrder.Theory.RosserProvable_defined :
    𝚺₁-Predicate (T.RosserProvable : V → Prop) via T.rosserProvable := .mk fun v ↦ by
  simp [Theory.rosserProvable, Theory.RosserProvable]


-- @@ L32-33 verbatim
instance _root_.FFL.FirstOrder.Theory.rosserProvable_definable :
    𝚺₁-Predicate (T.RosserProvable : V → Prop) := T.RosserProvable_defined.to_definable


-- @@ L35-35 verbatim
noncomputable abbrev _root_.FFL.FirstOrder.Theory.rosserPred (σ : Sentence L) : ArithmeticSentence := T.rosserProvable.val/[⌜σ⌝]


-- @@ L37-37 verbatim
end


-- @@ L39-51 verbatim
variable {T}

lemma rosser_quote {φ : Proposition L} : T.RosserProvable (V := V) ⌜φ⌝ ↔ T.ProvabilityComparisonLE (V := V) ⌜φ⌝ ⌜∼φ⌝ := by
  simp [Theory.RosserProvable, Semiformula.quote_def]

lemma rosser_quote₀ {φ : Sentence L} : T.RosserProvable (V := V) ⌜φ⌝ ↔ T.ProvabilityComparisonLE (V := V) ⌜φ⌝ ⌜∼φ⌝ := by
  simpa [Sentence.quote_def] using rosser_quote

lemma rosser_quote_def {φ : Proposition L} :
    T.RosserProvable (V := V) ⌜φ⌝ ↔ ∃ b : V, Proof T b ⌜φ⌝ ∧ ∀ b' < b, ¬Proof T b' ⌜∼φ⌝ := rosser_quote

lemma rosser_quote_def₀ {φ : Sentence L} :
    T.RosserProvable (V := V) ⌜φ⌝ ↔ ∃ b : V, Proof T b ⌜φ⌝ ∧ ∀ b' < b, ¬Proof T b' ⌜∼φ⌝ := by simpa [Sentence.quote_def] using! rosser_quote


-- @@ L53-62 verbatim
theorem RosserProvable.to_provable {φ : V} : T.RosserProvable φ → Provable T φ := ProvabilityComparison.le_to_provable

lemma provable_of_standard_proof {n : ℕ} {φ : Sentence L} : Proof T (n : V) ⌜φ⌝ → T ⊢ φ := fun h ↦ by
  have : Proof T n ⌜φ⌝ ↔ Proof T (↑n : V) ⌜φ⌝ := by
    simpa [Sentence.coe_quote_eq_quote] using
      Defined.shigmaOne_absolute V (φ := proof T)
        (R := fun v ↦ Proof T (v 0) (v 1)) (R' := fun v ↦ Proof T (v 0) (v 1))
        Proof.defined Proof.defined ![n, ⌜φ⌝]
  have : Provable T (⌜φ⌝ : ℕ) := ⟨n, this.mpr h⟩
  exact provable_iff_provable.mp this


-- @@ L64-64 verbatim
open Classical


-- @@ L66-74 verbatim
theorem rosser_internalize [Consistent T] {φ : Sentence L} : T ⊢ φ → T.RosserProvable (⌜φ⌝ : V) := by
  intro h
  let n : ℕ := ⌜h.get⌝
  have hn : Proof T (↑n : V) ⌜φ⌝ := by simp [n, coe_quote_proof_eq]
  refine rosser_quote_def₀.mpr ⟨n, hn, ?_⟩
  intro b hb Hb
  rcases eq_nat_of_lt_nat hb with ⟨b, rfl⟩
  have : T ⊢ ∼φ := provable_of_standard_proof (V := V) Hb
  exact Consistent.not_inc inferInstance (inconsistent_of_provable_of_unprovable h this)


-- @@ L76-77 verbatim
theorem rosser_internalize_sentence [Consistent T] {σ : Sentence L} : T ⊢ σ → T.RosserProvable (⌜σ⌝ : V) := fun h ↦ by
  simpa [Sentence.quote_def] using! rosser_internalize h


-- @@ L79-88 verbatim
open Classical in
theorem not_rosserProvable [Consistent T] {φ : Sentence L} : T ⊢ ∼φ → ¬T.RosserProvable (⌜φ⌝ : V) := by
  rintro h r
  let n : ℕ := ⌜h.get⌝
  have hn : Proof T (↑n : V) ⌜∼φ⌝ := by simp [n, coe_quote_proof_eq]
  rcases rosser_quote₀.mp r with ⟨b, hb, Hb⟩
  have : b ≤ n := by grind;
  rcases eq_nat_of_le_nat this with ⟨b, rfl⟩
  have : T ⊢ φ := provable_of_standard_proof hb
  exact Consistent.not_inc inferInstance (inconsistent_of_provable_of_unprovable this h)


-- @@ L90-91 verbatim
theorem not_rosserProvable_sentence [Consistent T] {σ : Sentence L} : T ⊢ ∼σ → ¬T.RosserProvable (⌜σ⌝ : V) := fun h ↦ by
  simpa [Sentence.quote_def] using! not_rosserProvable h


-- @@ L93-93 verbatim
end FFL.FirstOrder.Arithmetic.Bootstrapping


-- @@ L95-95 verbatim
namespace FFL.FirstOrder.Arithmetic


-- @@ L97-97 verbatim
open Bootstrapping

-- @@ L98-98 verbatim
open FFL.Entailment


-- @@ L100-100 verbatim
section


-- @@ L102-102 verbatim
variable {L : Language} [L.Encodable] [L.LORDefinable]


-- @@ L104-104 verbatim
variable {T : Theory L} [T.Δ₁] [Consistent T]


-- @@ L106-106 verbatim
local prefix:90 "𝗥" => T.rosserPred


-- @@ L108-110 verbatim
theorem rosserProvable_D1 {σ} : T ⊢ σ → 𝗜𝚺₁ ⊢ 𝗥σ := fun h ↦
  complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
    simpa [models_iff] using rosser_internalize_sentence h


-- @@ L112-114 verbatim
theorem rosserProvable_rosser {σ} : T ⊢ ∼σ → 𝗜𝚺₁ ⊢ ∼𝗥σ := fun h ↦
  complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
    simpa [models_iff] using not_rosserProvable_sentence h


-- @@ L116-116 verbatim
end


-- @@ L118-118 verbatim
section rosserProvability


-- @@ L120-120 verbatim
open ProvabilityAbstraction


-- @@ L122-122 verbatim
variable {L : Language} [L.Encodable] [L.LORDefinable]


-- @@ L124-124 verbatim
variable {T : Theory L} [T.Δ₁] [Consistent T]


-- @@ L126-126 verbatim
variable (T)


-- @@ L128-130 verbatim
noncomputable abbrev _root_.FFL.FirstOrder.Theory.rosserProvability : Provability 𝗜𝚺₁ T where
  prov := T.rosserProvable
  bew_def := rosserProvable_D1


-- @@ L132-134 verbatim
instance : T.rosserProvability.Rosser := ⟨rosserProvable_rosser⟩

lemma rosserProvability_def (σ : Sentence L) : T.rosserProvability σ = T.rosserPred σ := rfl


-- @@ L136-141 verbatim
instance : T.rosserProvability.SoundOn ℕ := by
  constructor;
  intro σ h;
  apply Bootstrapping.provable_iff_provable.mp
    $ Bootstrapping.ProvabilityComparison.le_to_provable
    $ by simpa [models_iff, Provability.pr, Theory.RosserProvable] using h;


-- @@ L143-143 verbatim
end rosserProvability


-- @@ L145-147 verbatim
/-- Gödel-Rosser incompleteness theorem -/
theorem incomplete_GR (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [Consistent T] : Incomplete T :=
  ProvabilityAbstraction.rosser_first_incompleteness T.rosserProvability


-- @@ L149-149 verbatim
instance {T : ArithmeticTheory} [T.RE] [𝗜𝚺₁ ⪯ T] : 𝗜𝚺₁ ⪯ T.craig := WeakerThan.trans inferInstance (inferInstance : T ⪯ T.craig)


-- @@ L151-153 verbatim
/-- Gödel-Rosser incompleteness theorem for r.e. theories -/
theorem incomplete_GR_of_RE (T : ArithmeticTheory) [T.RE] [𝗜𝚺₁ ⪯ T] [Consistent T] : Incomplete T :=
  (Equiv.incomplete_iff (inferInstance : T ≊ T.craig)).mpr (incomplete_GR T.craig)


-- @@ L155-158 verbatim
theorem exists_true_but_unprovable_sentence_of_RE_of_consistent
    (T : ArithmeticTheory) [T.RE] [𝗜𝚺₁ ⪯ T] [Consistent T] :
    ∃ δ : ArithmeticSentence, ℕ↓[ℒₒᵣ] ⊧ δ ∧ T ⊬ δ :=
  exists_true_but_unprovable_sentence_of_incomplete (incomplete_GR_of_RE T)


-- @@ L160-160 verbatim
end FFL.FirstOrder.Arithmetic
