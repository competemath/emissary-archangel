module

public import Foundation.FirstOrder.Basic.Coding
public import Foundation.FirstOrder.Basic.PrimrecCoding
public import Foundation.FirstOrder.Incompleteness.RosserProvability
public import Foundation.FirstOrder.Arithmetic.R0.Representation
public import Foundation.FirstOrder.Incompleteness.Halting
public import Foundation.Meta.ClProver
public import Mathlib.Computability.Reduce


-- @@ L11-18 verbatim
/-!
# Church's undecidability theorem

The set of sentences provable in an arithmetic theory `T ⊇ 𝗥₀` is not computable, whether `T` is
sound on `𝚺₁` sentences (`uncomputable_theory_of_sigma1Sound`) or merely consistent and extends
`𝗜𝚺₁` (`uncomputable_theory_of_consistent`). Provability in pure first-order logic is likewise
undecidable (`undecidability_first_order_logic`).
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
namespace FFL.FirstOrder.Arithmetic


-- @@ L24-24 verbatim
open Bootstrapping Bootstrapping.Arithmetic


-- @@ L26-26 verbatim
section Diagonalization


-- @@ L28-36 expanded
lemma computable_iff_sigma1_simulate {α β : Type*} [Primcodable α] [Primcodable β] {f : ℕ → ℕ}
    (hf : DefinableFunction₁ HierarchySymbol.sigmaOne f) {F : α → β}
    (h : ∀ a, f (Encodable.encode a) = Encodable.encode (F a)) : Computable F :=
  by
  have hCode : Computable fun a : α ↦ f (Encodable.encode a) :=
    (computable_iff_sigma1.mpr hf).comp Computable.encode
  have hDecode := Computable.ofOption ((Computable.decode (α := β)).comp hCode)
  exact hDecode.of_eq_tot fun a ↦ by simp [h a]


-- @@ L38-47 expanded
lemma computable₂_iff_sigma1_simulate {α β γ : Type*} [Primcodable α] [Primcodable β]
    [Primcodable γ] {f : ℕ → ℕ → ℕ} (hf : DefinableFunction₂ HierarchySymbol.sigmaOne f)
    {F : α → β → γ}
    (h : ∀ a b, f (Encodable.encode a) (Encodable.encode b) = Encodable.encode (F a b)) :
    Computable₂ F :=
  by
  have hCode : Computable fun p : α × β ↦ f (Encodable.encode p.1) (Encodable.encode p.2) :=
    (computable₂_iff_sigma1.mpr hf).comp (Computable.encode.comp Computable.fst)
      (Computable.encode.comp Computable.snd)
  have hDecode := Computable.ofOption ((Computable.decode (α := γ)).comp hCode)
  exact Computable₂.mk <| hDecode.of_eq_tot fun p ↦ by simp [h p.1 p.2]


-- @@ L49-49 expanded
variable {T : ArithmeticTheory} [WeakerThan R0 T] [T.SoundOnHierarchy SigmaSymbol.sigma 1]


-- @@ L51-71 expanded
theorem uncomputable_theory_of_sigma1Sound : ¬ComputablePred T.theory :=
  by
  by_contra hC
  have hQuoteSubst :
    Computable₂ fun σ π : ArithmeticSemisentence 1 ↦
      (FFL.FirstOrder.Rewriting.subst σ ![GödelQuote.quote π] : ArithmeticSentence) :=
    computable₂_iff_sigma1_simulate (f := substNumeral (V := ℕ))
      (by aesop  (config := { terminal := true })  (rule_sets := [Definability])) fun σ τ ↦ by
      simp [← Sentence.quote_eq_encode_nat, substNumeral_app_quote]
  have hSubst :
    Computable fun σ : ArithmeticSemisentence 1 ↦
      (FFL.FirstOrder.Rewriting.subst σ ![GödelQuote.quote σ] : ArithmeticSentence) :=
    hQuoteSubst.comp Computable.id Computable.id
  have hD :
    ComputablePred
      (fun σ : ArithmeticSemisentence 1 ↦
        Unprovable T (FFL.FirstOrder.Rewriting.subst σ ![GödelQuote.quote σ])) :=
    ComputablePred.computable_of_manyOneReducible
      (ManyOneReducible.mk (fun σ ↦ Unprovable T σ) hSubst) hC.not
  let D : ℕ → Prop := fun n ↦
    (Encodable.decode (α := ArithmeticSemisentence 1) n).elim False
      (fun σ ↦ Unprovable T (FFL.FirstOrder.Rewriting.subst σ ![GödelQuote.quote σ]))
  have hRe : REPred D := by simpa [D] using REPred.iff_decoded_pred.mp hD.to_re
  have hδ :
    Unprovable T
        (FFL.FirstOrder.Rewriting.subst (codeOfREPred D) ![GödelQuote.quote (codeOfREPred D)]) ↔
      Provable T
        (FFL.FirstOrder.Rewriting.subst (codeOfREPred D) ![GödelQuote.quote (codeOfREPred D)]) :=
    by
    simpa [D, Encodable.encodek, Arithmetic.gödelNumber'_eq_coe_encode] using
      rePred_weak_representation (T := T) hRe (x := Encodable.encode (codeOfREPred D))
  tauto


-- @@ L73-73 verbatim
end Diagonalization


-- @@ L75-75 verbatim
section ConsistencyOnly


-- @@ L77-77 expanded
variable {T : ArithmeticTheory} [WeakerThan (ISigma 1) T] [Entailment.Consistent T]


-- @@ L79-96 expanded
theorem uncomputable_theory_of_consistent : ¬ComputablePred T.theory :=
  by
  by_contra hC
  let p : ℕ → Prop := fun n ↦
    (Encodable.decode (α := ArithmeticSentence) n).elim False (fun σ ↦ Provable T σ)
  have hp : ComputablePred p := ComputablePred.iff_decoded_pred.mp hC
  let ψ : ArithmeticSemisentence 1 := codeOfComputablePred p
  let δ : ArithmeticSentence := fixedpoint (unop% HTilde.hTilde ψ)
  have hδ :
    Provable T
      (LogicalConnective.iff δ
        unop% HTilde.hTilde (FFL.FirstOrder.Rewriting.subst ψ ![GödelQuote.quote δ])) :=
    by simpa using diagonal (T := T) (unop% HTilde.hTilde ψ)
  have hp_iff : p (Encodable.encode δ) ↔ Provable T δ := by simp [p, Encodable.encodek]
  by_cases h : Provable T δ
  · have hψ : Provable T (FFL.FirstOrder.Rewriting.subst ψ ![GödelQuote.quote δ]) := by
      simpa [Arithmetic.gödelNumber'_eq_coe_encode] using
        codeOfComputablePred_provable hp (hp_iff.mpr h)
    apply Entailment.Consistent.not_bot (𝓢 := T)
    cl_prover[hδ, h, hψ]
  · have hnψ :
      Provable T unop% HTilde.hTilde (FFL.FirstOrder.Rewriting.subst ψ ![GödelQuote.quote δ]) := by
      simpa [Arithmetic.gödelNumber'_eq_coe_encode] using
        codeOfComputablePred_provable_neg hp (hp_iff.not.mpr h)
    exact h (by cl_prover[hδ, hnψ])


-- @@ L98-98 verbatim
end ConsistencyOnly


-- @@ L100-100 verbatim
section PeanoMinusReduction


-- @@ L102-120 expanded
/-- Provability in pure first-order logic, i.e. provability from the empty theory, is
undecidable. -/
theorem undecidability_first_order_logic : ¬ComputablePred ((∅ : ArithmeticTheory).theory) :=
  by
  have hDeduction (σ : ArithmeticSentence) :
    Provable PeanoMinus σ ↔
      Provable (∅ : ArithmeticTheory) binop% HArrow.hArrow PeanoMinus.finite.toFinset.conj σ :=
    by
    rw [Entailment.Equiv.iff.mp PeanoMinus.equiv_singleton_finiteConj σ, ← insert_empty_eq]
    exact Entailment.deduction_iff
  by_contra hC
  have hImpIntro :
    Computable fun σ : ArithmeticSentence ↦
      binop% HArrow.hArrow PeanoMinus.finite.toFinset.conj σ :=
    let c :=
      Encodable.encode (unop% HTilde.hTilde PeanoMinus.finite.toFinset.conj : ArithmeticSentence)
    computable_iff_sigma1_simulate (f := fun e ↦ pair 5 (pair c e) + 1)
      (by aesop  (config := { terminal := true })  (rule_sets := [Definability])) fun σ ↦ by
      simp [nat_pair_eq, c, Semiformula.imp_eq, Semiformula.encode_or,
        ← Semiformula.encode_eq_toNat, ← Semiformula.encode_eq_toNat]
  apply
    uncomputable_theory_of_sigma1Sound (T := PeanoMinus)
      (ComputablePred.computable_of_manyOneReducible ?_ hC)
  refine ⟨fun σ ↦ binop% HArrow.hArrow PeanoMinus.finite.toFinset.conj σ, ?_, ?_⟩
  · exact hImpIntro
  · exact hDeduction


-- @@ L122-122 verbatim
end PeanoMinusReduction


-- @@ L124-124 verbatim
end FFL.FirstOrder.Arithmetic


-- @@ L126-126 verbatim
end
