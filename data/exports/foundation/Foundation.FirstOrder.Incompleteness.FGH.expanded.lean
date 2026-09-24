module

public import Foundation.FirstOrder.Incompleteness.Consistency
public import Foundation.FirstOrder.Arithmetic.ISigma1.Prenex


-- @@ L6-8 verbatim
/-!
# The Friedman–Goldfarb–Harrington theorem
-/


-- @@ L10-10 verbatim
@[expose] public section


-- @@ L12-12 verbatim
open Classical


-- @@ L14-14 verbatim
namespace FFL.FirstOrder.Arithmetic.Bootstrapping


-- @@ L16-16 verbatim
open FFL.Entailment


-- @@ L18-18 verbatim
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {x : V}


-- @@ L20-20 verbatim
variable (T : ArithmeticTheory) [T.Δ₁] (θ : 𝚺₀.Semisentence 1)



-- @@ L23-23 verbatim
def _root_.FFL.FirstOrder.Theory.WitnessedBefore (φ : V) := ∃ b, V ⊧/![b] θ.val ∧ ∀ b' < b, ¬Proof T b' φ


-- @@ L25-26 verbatim
noncomputable def _root_.FFL.FirstOrder.Theory.witnessedBefore : 𝚺₁.Semisentence 1 := .mkSigma
  “x. ∃ w, !θ w ∧ ∀ p < w, ¬!(proof T).pi p x”


-- @@ L28-30 verbatim
instance _root_.FFL.FirstOrder.Theory.WitnessedBefore.defined :
    𝚺₁-Predicate[V] T.WitnessedBefore θ via T.witnessedBefore θ := .mk fun v ↦ by
  simp [Theory.witnessedBefore, Theory.WitnessedBefore];


-- @@ L32-33 verbatim
instance _root_.FFL.FirstOrder.Theory.WitnessedBefore.definable :
    𝚺₁-Predicate[V] T.WitnessedBefore θ := (Theory.WitnessedBefore.defined T θ).to_definable



-- @@ L36-36 verbatim
def _root_.FFL.FirstOrder.Theory.ProvedBefore (φ : V) := ∃ b, Proof T b φ ∧ ∀ b' ≤ b, ¬V ⊧/![b'] θ.val


-- @@ L38-39 verbatim
noncomputable def _root_.FFL.FirstOrder.Theory.provedBefore : 𝚺₁.Semisentence 1 := .mkSigma
  “x. ∃ p, !(proof T).sigma p x ∧ ∀ w <⁺ p, ¬!θ w”


-- @@ L41-43 verbatim
instance _root_.FFL.FirstOrder.Theory.ProvedBefore.defined :
    𝚺₁-Predicate[V] T.ProvedBefore θ via T.provedBefore θ := .mk fun v ↦ by
  simp [Theory.provedBefore, Theory.ProvedBefore];


-- @@ L45-46 verbatim
instance _root_.FFL.FirstOrder.Theory.ProvedBefore.definable :
    𝚺₁-Predicate[V] T.ProvedBefore θ := (Theory.ProvedBefore.defined T θ).to_definable



-- @@ L49-50 verbatim
noncomputable def _root_.FFL.FirstOrder.Theory.fghSentence : ArithmeticSentence :=
  fixedpoint (T.witnessedBefore θ).val


-- @@ L52-53 verbatim
noncomputable def _root_.FFL.FirstOrder.Theory.fghSentence' : 𝚺₁.Sentence :=
  (T.witnessedBefore θ).rew (Rew.subst ![⌜T.fghSentence θ⌝])



-- @@ L56-63 verbatim
variable {T : ArithmeticTheory} [T.Δ₁] {θ : 𝚺₀.Semisentence 1} {σ : ArithmeticSentence}

lemma not_witnessedBefore_of_provedBefore : T.ProvedBefore θ x → ¬T.WitnessedBefore θ x := by
  rintro ⟨p, hp, hbound⟩ ⟨w, hw, hbound'⟩;
  rcases lt_or_ge p w with h | h <;> grind;


-- Avoids a v4.33.1 kernel defeq blow-up when unfolding `.rew`/`.val` against `witnessedBefore`.

-- @@ L64-79 verbatim
private lemma fghSentence'_val_eq :
    (T.fghSentence' θ).val = (T.witnessedBefore θ).val/[⌜T.fghSentence θ⌝] := by
  unfold Theory.fghSentence'
  rw [HierarchySymbol.Semiformula.val_rew]

lemma diagonal_fghSentence :
    𝗜𝚺₁ ⊢ T.fghSentence θ 🡘 (T.fghSentence' θ).val := by
  rw [fghSentence'_val_eq]
  exact diagonal (T.witnessedBefore θ).val

lemma refutable_fghSentence_of_provedBefore :
    𝗜𝚺₁ ⊢ (T.provedBefore θ).val/[⌜T.fghSentence θ⌝] 🡒 ∼T.fghSentence θ := by
  apply C_trans ?_ $ contra $ K_left diagonal_fghSentence;
  apply complete.{0};
  intro V _ _;
  simpa [models_iff, Sentence.coe_quote_eq_quote, Theory.fghSentence'] using not_witnessedBefore_of_provedBefore;



-- @@ L82-88 verbatim
local notation:max "□" σ:max => Provable T (⌜σ⌝ : V)

lemma provable_of_provable_bot : □(⊥ : ArithmeticSentence) → □σ :=
  modus_ponens_sentence T $ internalize_provability efq

lemma provable_bot_of_provable_of_provable_neg : □σ → □(∼σ) → □(⊥ : ArithmeticSentence) := fun hσ hnσ ↦
  modus_ponens_sentence T (modus_ponens_sentence T (internalize_provability (by cl_prover)) hσ) hnσ


-- @@ L90-122 verbatim
variable [𝗜𝚺₁ ⪯ T]

lemma witness_or_provable_bot_of_provable_fghSentence :
  □(T.fghSentence θ) → (∃ w, V ⊧/![w] θ.val) ∨ □(⊥ : ArithmeticSentence) := by
  intro hprov;
  by_cases hw : ∃ w, V ⊧/![w] θ.val;
  . tauto;
  . push Not at hw;
    obtain ⟨p₀, hp₀⟩ := hprov;
    right;
    apply provable_bot_of_provable_of_provable_neg (σ := T.fghSentence θ);
    . use p₀;
    . apply modus_ponens_sentence T (internalize_provability (WeakerThan.pbl refutable_fghSentence_of_provedBefore));
      apply Bootstrapping.Arithmetic.sigma_one_complete T (by simp);
      apply models_iff.mpr;
      simpa using ⟨p₀, hp₀, fun w _ ↦ hw w⟩;

lemma provable_fghSentence_of_witness_or_provable_bot :
  (∃ w, V ⊧/![w] θ.val) ∨ □(⊥ : ArithmeticSentence) → □(T.fghSentence θ) := by
  rintro (⟨w₀, hw₀⟩ | hbot);
  . by_cases hp : ∃ p < w₀, Proof T p (⌜T.fghSentence θ⌝ : V);
    . obtain ⟨p, -, hp⟩ := hp;
      use p;
    . push Not at hp;
      apply modus_ponens_sentence T (internalize_provability (WeakerThan.pbl (K_right diagonal_fghSentence)));
      apply Bootstrapping.Arithmetic.sigma_one_complete T (by simp);
      simpa [models_iff, Theory.fghSentence'] using ⟨w₀, hw₀, hp⟩;
  . exact provable_of_provable_bot hbot;

lemma provable_fghSentence_iff : □(T.fghSentence θ) ↔ (∃ w, V ⊧/![w] θ.val) ∨ □(⊥ : ArithmeticSentence) := ⟨
  witness_or_provable_bot_of_provable_fghSentence,
  provable_fghSentence_of_witness_or_provable_bot
⟩


-- @@ L124-133 verbatim
/-- The constructive form of the FGH theorem: `T.fghSentence θ` is an explicit witness. -/
lemma provable_fixedpoint_iff_exs_or_provable_bot :
  𝗜𝚺₁ ⊢ provabilityPred T (T.fghSentence θ) 🡘 (∃¹ θ.val) ⋎ provabilityPred T ⊥ := by
  apply complete.{0};
  intro V _ _;
  simpa [models_iff] using provable_fghSentence_iff;

lemma provable_fixedpoint'_iff_exs_or_provable_bot :
  𝗜𝚺₁ ⊢ provabilityPred T (T.fghSentence' θ).val 🡘 (∃¹ θ.val) ⋎ provabilityPred T ⊥ :=
  E_trans (E_symm $ T.standardProvability.ext' diagonal_fghSentence) provable_fixedpoint_iff_exs_or_provable_bot


-- @@ L135-135 verbatim
end FFL.FirstOrder.Arithmetic.Bootstrapping


-- @@ L137-137 verbatim
namespace FFL.FirstOrder.Arithmetic


-- @@ L139-139 verbatim
open Bootstrapping

-- @@ L140-140 verbatim
open FFL.Entailment


-- @@ L142-142 verbatim
variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] {σ : ArithmeticSentence}


-- @@ L144-152 verbatim
theorem fgh_theorem (hσ : Hierarchy 𝚺 1 σ) :
  ∃ π : 𝚺₁.Sentence, 𝗜𝚺₁ ⊢ provabilityPred T π.val 🡘 σ ⋎ provabilityPred T ⊥ := by
  obtain ⟨θ, hwit⟩ := ISigma1.exists_matrix_provable_of_sentence hσ;
  use T.fghSentence' θ;
  apply E_trans provable_fixedpoint'_iff_exs_or_provable_bot;
  apply complete.{0};
  intro V _ _;
  simp [models_iff, show V ⊧/![] σ ↔ ∃ w, V ⊧/![w] θ.val from
    by simpa [Semiformula.eval_ex] using models_iff_of_provable_iff hwit V ![]];


-- @@ L154-160 verbatim
theorem fgh_theorem_con (hσ : Hierarchy 𝚺 1 σ) :
  ∃ π : 𝚺₁.Sentence, 𝗜𝚺₁ ∪ T.Con ⊢ σ 🡘 provabilityPred T π.val := by
  obtain ⟨π, heq⟩ := fgh_theorem T hσ;
  use π;
  have heq' : 𝗜𝚺₁ ∪ T.Con ⊢ provabilityPred T π.val 🡘 σ ⋎ provabilityPred T ⊥ := WeakerThan.pbl heq;
  have hcon : 𝗜𝚺₁ ∪ T.Con ⊢ ∼provabilityPred T ⊥ := by_axm (by simp [Theory.consistent]);
  cl_prover [heq', hcon];


-- @@ L162-162 verbatim
end FFL.FirstOrder.Arithmetic
