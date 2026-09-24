module

public import Foundation.FirstOrder.Incompleteness.RosserProvability
public import Foundation.FirstOrder.Incompleteness.ProvabilityAbstraction.Refutability


-- @@ L6-16 verbatim
/-!
# Jeroslow's Second Incompleteness Theorem

Jeroslow's formulation of the second incompleteness theorem
states that the sentence represents _formalized law of noncontradiction_ of `T`
(i.e. no statement can be both formally proved in `T` and formally refuted in `T`)
is not provable in `T` itself.

## References
- [Jeroslow, R. G., *Redundancies in the Hilbert-Bernays Derivability Conditions for Gödel's Second Incompleteness Theorem*][Jer73]
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
namespace FFL.FirstOrder


-- @@ L22-22 verbatim
open _root_.FFL.FirstOrder.Entailment

-- @@ L23-23 verbatim
open Arithmetic Bootstrapping

-- @@ L24-24 verbatim
open Derivation ProvabilityAbstraction


-- @@ L26-26 verbatim
namespace Theory


-- @@ L28-28 verbatim
variable {L : Language}



-- @@ L31-31 verbatim
section


-- @@ L33-34 verbatim
variable [L.Encodable] [L.LORDefinable]
         {T : Theory L} [T.Δ₁]


-- @@ L36-37 verbatim
def Refutable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (T : Theory L) [T.Δ₁] (φ : V) : Prop
  := Provable T (neg L φ)


-- @@ L39-40 verbatim
noncomputable def refutable (T : Theory L) [T.Δ₁] : 𝚺₁.Semisentence 1
  := .mkSigma “φ. ∃ nφ, !(negGraph L) nφ φ ∧ !(provable T) nφ”


-- @@ L42-42 verbatim
section


-- @@ L44-47 verbatim
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma Refutable.quote_iff {σ : Sentence L} : T.Refutable (⌜σ⌝ : V) ↔ Provable T (⌜∼σ⌝ : V) := by
  simp [Theory.Refutable, Sentence.quote_def, Semiformula.quote_def]


-- @@ L49-50 verbatim
instance refutable_defined : 𝚺₁-Predicate[V] T.Refutable via T.refutable := .mk fun v ↦ by
  simp [Theory.refutable, Theory.Refutable]


-- @@ L52-52 verbatim
instance refutable_definable : 𝚺₁-Predicate[V] T.Refutable := refutable_defined.to_definable


-- @@ L54-54 verbatim
end


-- @@ L56-56 verbatim
end



-- @@ L59-59 verbatim
section


-- @@ L61-61 verbatim
variable {T U : ArithmeticTheory} [T.Δ₁]


-- @@ L63-66 verbatim
noncomputable abbrev standardRefutability (T : ArithmeticTheory) [T.Δ₁] : Refutability 𝗜𝚺₁ T where
  refu := T.refutable.val
  refu_def {σ} h := complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
    simpa [models_iff, Refutable.quote_iff] using internalize_provability h (V := V)


-- @@ L68-68 verbatim
noncomputable abbrev jeroslow (T : ArithmeticTheory) [T.Δ₁] : ArithmeticSentence := fixedpoint T.refutable


-- @@ L70-70 verbatim
private noncomputable abbrev jeroslow' (T : ArithmeticTheory) [T.Δ₁] : ArithmeticSentence := (T.refutable)/[⌜T.jeroslow⌝]


-- @@ L72-74 verbatim
private lemma jeroslow'_sigmaOne : Hierarchy 𝚺 1 (T.jeroslow') := by definability;

lemma def_jeroslow [𝗜𝚺₁ ⪯ U] : U ⊢ T.jeroslow 🡘 (T.refutable)/[⌜T.jeroslow⌝] := diagonal _


-- @@ L76-76 verbatim
private lemma def_jeroslow' [𝗜𝚺₁ ⪯ U] : U ⊢ T.jeroslow' 🡘 (T.refutable)/[⌜T.jeroslow⌝] := by simp;


-- @@ L78-78 verbatim
private lemma provable_E_jeroslow_jeroslow' [𝗜𝚺₁ ⪯ U] : U ⊢ T.jeroslow 🡘 T.jeroslow' := Entailment.E_trans def_jeroslow def_jeroslow'


-- @@ L80-81 verbatim
private lemma iff_provable_jeroslow_provable_jeroslow' [𝗜𝚺₁ ⪯ U] : U ⊢ (T.jeroslow) ↔ U ⊢ (T.jeroslow') := by
  apply Entailment.iff_of_E provable_E_jeroslow_jeroslow';


-- @@ L83-90 verbatim
open FFL.Entailment in
instance [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] : T.standardRefutability.SoundOn (ProvabilityAbstraction.jeroslow T.standardRefutability) := by
  constructor;
  intro h;
  have := ArithmeticTheory.SoundOn.sound (F := Arithmetic.Hierarchy 𝚺 1) h $ by simp [standardRefutability, Refutability.rf];
  exact provable_iff_provable (L := ℒₒᵣ) |>.mp $ by simpa [models_iff, standardRefutability, Refutability.rf, Refutable.quote_iff] using this;

-- Proving this by a plain `rfl` overflows memory on Lean v4.33.1.

-- @@ L91-95 verbatim
private lemma jeroslow_eq_standard :
    ProvabilityAbstraction.jeroslow (T.standardRefutability) = T.jeroslow := by
  unfold ProvabilityAbstraction.jeroslow
  rw [show (T.standardRefutability).refu = T.refutable.val from rfl,
      show (Diagonalization.fixedpoint (T := 𝗜𝚺₁)) = Arithmetic.fixedpoint from rfl]


-- @@ L97-100 verbatim
instance [𝗜𝚺₁ ⪯ T] : T.standardProvability.FormalizedCompleteOn (ProvabilityAbstraction.jeroslow T.standardRefutability) := by
  constructor;
  rw [jeroslow_eq_standard];
  exact provable_sigma_one_complete_of_E jeroslow'_sigmaOne (Entailment.E_symm provable_E_jeroslow_jeroslow');


-- @@ L102-102 verbatim
end


-- @@ L104-104 verbatim
end Theory



-- @@ L107-107 verbatim
namespace Arithmetic


-- @@ L109-109 verbatim
variable {L : Language} [L.Encodable] [L.LORDefinable]

-- @@ L110-110 verbatim
variable {T : ArithmeticTheory} [T.Δ₁]


-- @@ L112-118 verbatim
/--
  Jeroslow sentence of `T` is not provable in `T` itself.
-/
theorem unprovable_jeroslow [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
  : T ⊬ T.jeroslow := by
  rw [← Theory.jeroslow_eq_standard];
  exact ProvabilityAbstraction.unprovable_jeroslow (𝔚 := T.standardRefutability)


-- @@ L120-130 verbatim
/--
  Jeroslow's formulation of the second incompleteness theorem.

  The sentence represents _formalized law of noncontradiction_ of `T`
  (i.e. no statement can be both formally proved in `T` and formally refuted in `T`)
  is not provable in `T` itself.
-/
theorem unprovable_formalized_law_of_noncontradiction [𝗜𝚺₁ ⪯ T] [Entailment.Consistent T]
  : T ⊬ (∀¹ ∼(provable T ⋏ T.refutable) : ArithmeticSentence) := by
    simpa [flon, safe, -LogicalConnective.DeMorgan.and] using ProvabilityAbstraction.unprovable_flon
      (𝔅 := T.standardProvability) (𝔚 := T.standardRefutability)


-- @@ L132-132 verbatim
end Arithmetic



-- @@ L135-135 verbatim
end FFL.FirstOrder


-- @@ L137-137 verbatim
end
