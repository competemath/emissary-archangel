module

public import Foundation.FirstOrder.Basic.PrimrecCoding
public import Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.D1
public import Foundation.FirstOrder.Incompleteness.Church
public import Mathlib.Computability.Reduce
public import Mathlib.Data.Nat.Log


-- @@ L9-14 verbatim
/-!
# Ehrenfeucht–Mycielski speedup theorem

`Theory.minProof T σ` is the least Gödel code of a proof `T ⊢₂! ↑σ`, and `0` when `σ` is not
`T`-provable.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
namespace FFL.FirstOrder.Arithmetic.Bootstrapping


-- @@ L20-20 verbatim
section Provability


-- @@ L22-25 verbatim
variable {L : Language} [L.DecidableEq] {T : Theory L} {σ π : Sentence L}

lemma provable_insert_neg_iff_or : insert (∼σ) T ⊢ π ↔ T ⊢ σ ⋎ π :=
  Entailment.deduction_iff.trans ⟨λ h ↦ by cl_prover [h], λ h ↦ by cl_prover [h]⟩


-- @@ L27-27 verbatim
end Provability


-- @@ L29-31 verbatim
variable
  {L : Language} [L.DecidableEq] [L.Encodable] [L.LORDefinable]
  {T : Theory L} [T.Δ₁] {σ : Sentence L}


-- @@ L33-34 verbatim
noncomputable def _root_.FFL.FirstOrder.Theory.minProof (T : Theory L) [T.Δ₁] (σ : Sentence L) : ℕ :=
  sInf (Set.range λ d : T ⊢₂! (σ : Proposition L) ↦ (⌜d⌝ : ℕ))


-- @@ L36-40 verbatim
@[grind →]
lemma proof_minProof (h : T ⊢ σ) : Proof T (T.minProof σ) ⌜σ⌝ := by
  obtain ⟨d, hd⟩ : T.minProof σ ∈ Set.range (λ d : T ⊢₂! (σ : Proposition L) ↦ (⌜d⌝ : ℕ)) :=
    Nat.sInf_mem ⟨_, Set.mem_range_self (provable_iff_derivable2.mp h).some⟩
  exact hd ▸ proof_of_quote_proof2 d


-- @@ L42-46 verbatim
@[grind →]
lemma minProof_eq_zero_of_unprovable (h : T ⊬ σ) : T.minProof σ = 0 := by
  have : IsEmpty (T ⊢₂! (σ : Proposition L)) :=
    not_nonempty_iff.mp λ hd ↦ h (provable_iff_derivable2.mpr hd)
  simp [Theory.minProof, Set.range_eq_empty_iff.mpr this]


-- @@ L48-50 verbatim
@[grind ←]
lemma minProof_le (d : T ⊢₂! (σ : Proposition L)) : T.minProof σ ≤ ⌜d⌝ :=
  Nat.sInf_le (Set.mem_range_self d)


-- @@ L52-52 verbatim
open Encodable


-- @@ L54-54 verbatim
variable {α : Type*} [Primcodable α] {F : α → Sentence L}


-- @@ L56-64 verbatim
omit [L.DecidableEq] in
lemma computablePred_proof : ComputablePred λ p : ℕ × ℕ ↦ Proof T p.1 p.2 := by
  apply ComputablePred.computable_of_manyOneReducible (q := λ n : ℕ => Proof T (π₁ n) (π₂ n));
  . use (λ p => Nat.pair p.1 p.2);
    and_intros;
    . exact Primrec₂.natPair.to_comp;
    . simp [←nat_pair_eq];
  . apply computablePred_iff_delta1.mpr;
    definability;



-- @@ L67-71 verbatim
omit [L.DecidableEq] in
private lemma definable_bddExists_proof : 𝚫₁-Predicate λ n : ℕ ↦ ∃ d ≤ π₁ n, Proof T d (π₂ n) :=
  (HierarchySymbol.Definable.bexs_ble (ℌ := 𝚫₁) (f := λ v : Fin 1 → ℕ ↦ π₁ (v 0))
    (P := λ v x ↦ Proof T x (π₂ (v 0))) (by simp) (by definability)).of_iff <| λ v ↦
      exists_congr λ d ↦ and_congr_left' (by simp only [Arithmetic.le_def]; omega)


-- @@ L73-91 verbatim
omit [L.DecidableEq] in
lemma computablePred_bddExists_proof [L.Primcodable] (hF : Computable F) {bd : α → ℕ}
    (hbd : Computable bd) :
  ComputablePred λ a ↦ ∃ d ≤ bd a, Proof T d ⌜F a⌝ := by
  apply ComputablePred.computable_of_manyOneReducible (q := λ n : ℕ ↦ ∃ d ≤ π₁ n, Proof T d (π₂ n));
  . use λ a => Nat.pair (bd a) (encode (F a));
    and_intros;
    . exact Computable₂.comp Primrec₂.natPair.to_comp hbd (Computable.encode.comp hF);
    . simp [←nat_pair_eq, Sentence.quote_eq_encode_nat];
  . apply computablePred_iff_delta1.mpr;
    exact definable_bddExists_proof;

lemma computablePred_provable_of_minProof_le [L.Primcodable] (hF : Computable F) {bd : α → ℕ}
  (hbd : Computable bd) (hb : ∀ a, T ⊢ F a → T.minProof (F a) ≤ bd a) :
  ComputablePred λ a ↦ T ⊢ F a := by
  apply ComputablePred.of_eq (computablePred_bddExists_proof (T := T) hF hbd);
  intro a;
  have hp : ∀ d, Proof T d ⌜F a⌝ → T ⊢ F a := λ d hd ↦ provable_iff_provable.mp ⟨d, hd⟩;
  grind;


-- @@ L93-96 verbatim
private def speedupProof (T : Theory L) (σ π : Sentence L) :
    insert σ T ⊢₂! ((σ ⋎ π : Sentence L)) :=
  Derivation2.or (φ := σ) (ψ := π) (by simp) $
    Derivation2.axm σ (by simp) (by simp)


-- @@ L98-104 verbatim
private lemma computable_quote_speedupProof [L.Primcodable] :
    Computable λ π ↦ (⌜speedupProof T σ π⌝ : ℕ) :=
  have hc : Computable₂ λ s p : ℕ ↦
      orIntro (insert (s ^⋎ p) ∅) s p (axm (insert s (insert p (insert (s ^⋎ p) ∅))) s) :=
    computable₂_iff_sigma1.mpr (by definability);
  (hc.comp (Computable.const ⌜σ⌝) Sentence.primrec_quote_natCast.to_comp).of_eq λ π ↦ by
    simp [speedupProof, Derivation2.quote_or, Derivation2.quote_axm, Sentence.quote_def];


-- @@ L106-107 verbatim
private lemma minProof_or_le_speedupProof (π : Sentence L) :
  (insert σ T).minProof (σ ⋎ π) ≤ ⌜speedupProof T σ π⌝ := minProof_le (speedupProof T σ π)


-- @@ L109-120 verbatim
/-- The Ehrenfeucht–Mycielski speedup theorem.

- [EM71] -/
theorem ehrenfeucht_mycielski_speedup [L.Primcodable]
    (hU : ¬ComputablePred (insert (∼σ) T).theory) (f : ℕ → ℕ) (hf : Computable f) :
    ∃ π : Sentence L, T ⊢ π ∧ f ((insert σ T).minProof π) < T.minProof π := by
  contrapose! hU;
  apply ComputablePred.of_eq ?_ (λ π ↦ provable_insert_neg_iff_or.symm);
  exact computablePred_provable_of_minProof_le
    (Semiformula.primrec₂_or.comp (Primrec.const σ) Primrec.id).to_comp
    ((Nat.computable_boundedMax hf).comp computable_quote_speedupProof)
    λ π hπ ↦ (hU (σ ⋎ π) hπ).trans (Nat.le_boundedMax (minProof_or_le_speedupProof π));


-- @@ L122-122 verbatim
section Arithmetic


-- @@ L124-124 verbatim
variable {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] {σ : ArithmeticSentence}


-- @@ L126-132 verbatim
open FFL.Entailment in
theorem ehrenfeucht_mycielski_speedup_arithmetic (hσ : T ⊬ σ) (f : ℕ → ℕ) (hf : Computable f) :
  ∃ π : ArithmeticSentence, T ⊢ π ∧ f ((insert σ T).minProof π) < T.minProof π :=
  have : 𝗜𝚺₁ ⪯ (insert (∼σ) T) :=
    WeakerThan.trans ‹𝗜𝚺₁ ⪯ T› (Axiomatized.le_of_subset (Set.subset_insert _ T));
  have : Consistent (insert (∼σ) T) := unprovable_iff_consistent_adjoin.mp hσ;
  ehrenfeucht_mycielski_speedup uncomputable_theory_of_consistent f hf


-- @@ L134-142 verbatim
example (hσ : T ⊬ σ) :
  ∃ π : ArithmeticSentence, T ⊢ π ∧ (insert σ T).minProof π < Nat.log 2 (T.minProof π) := by
  obtain ⟨π, hπ, hlt⟩ := ehrenfeucht_mycielski_speedup_arithmetic hσ (λ x ↦ 2 ^ (x + 1)) $
    Primrec₂.unpaired'.1 Nat.Primrec.pow |>.comp (Primrec.const 2) Primrec.succ |>.to_comp;
  use π;
  and_intros;
  . exact hπ;
  . apply Nat.le_log_iff_pow_le (by grind) (by grind) |>.mpr;
    omega;


-- @@ L144-144 verbatim
end Arithmetic


-- @@ L146-146 verbatim
end FFL.FirstOrder.Arithmetic.Bootstrapping
