module

public import Foundation.FirstOrder.Incompleteness.StandardProvability


-- @@ L5-5 verbatim
@[expose] public section

-- @@ L6-8 verbatim
/-!
# Consistency predicate
-/


-- @@ L10-10 verbatim
open Classical


-- @@ L12-12 verbatim
namespace FFL.FirstOrder.Arithmetic.Bootstrapping


-- @@ L14-14 verbatim
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]


-- @@ L16-16 verbatim
section WitnessComparisons


-- @@ L18-18 verbatim
variable {L : Language} [L.Encodable] [L.LORDefinable]


-- @@ L20-20 verbatim
section


-- @@ L22-22 verbatim
variable (T : Theory L) [T.Δ₁] (V)


-- @@ L24-24 verbatim
def _root_.FFL.FirstOrder.Theory.Consistent : Prop := ¬Provable T (⌜(⊥ : Sentence L)⌝ : V)


-- @@ L26-26 verbatim
variable {V}


-- @@ L28-32 verbatim
def _root_.FFL.FirstOrder.Theory.ConsistentWith (φ : V) : Prop := ¬Provable T (neg L φ)

lemma _root_.FFL.FirstOrder.Theory.ConsistentWith.quote_iff {σ : Sentence L} :
    T.ConsistentWith (⌜σ⌝ : V) ↔ ¬Provable T (⌜∼σ⌝ : V) := by
  simp [Theory.ConsistentWith, Sentence.quote_def, Semiformula.quote_def]


-- @@ L34-34 verbatim
section


-- @@ L36-37 verbatim
noncomputable def _root_.FFL.FirstOrder.Theory.consistent : 𝚷₁.Sentence :=
  .mkPi (∼provabilityPred T ⊥)


-- @@ L39-40 verbatim
@[simp] lemma consistent.defined : (T.consistent : ArithmeticSentence).Evalb (M := V) ![] ↔ T.Consistent V := by
  simp [Theory.consistent, Theory.Consistent]


-- @@ L42-43 verbatim
noncomputable def _root_.FFL.FirstOrder.Theory.consistentWith : 𝚷₁.Semisentence 1 := .mkPi
  “φ. ∀ nφ, !(negGraph L) nφ φ → ¬!(provable T) nφ”


-- @@ L45-46 verbatim
instance consistentWith.defined : 𝚷₁-Predicate (T.ConsistentWith : V → Prop) via T.consistentWith := .mk fun v ↦ by
  simp [Theory.ConsistentWith, Theory.consistentWith]


-- @@ L48-48 verbatim
instance consistentWith.definable : 𝚷₁-Predicate (T.ConsistentWith : V → Prop) := (consistentWith.defined T).to_definable


-- @@ L50-50 verbatim
noncomputable abbrev _root_.FFL.FirstOrder.Theory.consistentWithPred (σ : Sentence L) : ArithmeticSentence := T.consistentWith.val/[⌜σ⌝]


-- @@ L52-53 verbatim
noncomputable def _root_.FFL.FirstOrder.Theory.consistentWithPred' (σ : Sentence L) : 𝚷₁.Sentence := .mkPi
  “!T.consistentWith !!(⌜σ⌝)”


-- @@ L55-55 verbatim
@[simp] lemma consistentWithPred'_val (σ : Sentence L) : (T.consistentWithPred' σ).val = T.consistentWithPred' σ := by rfl


-- @@ L57-57 verbatim
variable {T}


-- @@ L59-59 verbatim
end


-- @@ L61-61 verbatim
abbrev _root_.FFL.FirstOrder.Theory.Con : ArithmeticTheory := {T.consistent.val}


-- @@ L63-63 verbatim
abbrev _root_.FFL.FirstOrder.Theory.Incon : ArithmeticTheory := {∼T.consistent.val}


-- @@ L65-65 verbatim
noncomputable instance : T.Con.Δ₁ := Theory.Δ₁.singleton _


-- @@ L67-67 verbatim
noncomputable instance : T.Incon.Δ₁ := Theory.Δ₁.singleton _


-- @@ L69-69 verbatim
end


-- @@ L71-71 verbatim
variable (T : ArithmeticTheory) [T.Δ₁] (V)


-- @@ L73-73 verbatim
theorem consistent_eq : T.consistent = T.standardProvability.con := rfl


-- @@ L75-76 verbatim
@[simp] lemma standard_consistent [𝗥₀ ⪯ T] : T.Consistent ℕ ↔ Entailment.Consistent T := by
  simp [Theory.Consistent, Entailment.consistent_iff_unprovable_bot]


-- @@ L78-78 verbatim
end WitnessComparisons


-- @@ L80-80 verbatim
end FFL.FirstOrder.Arithmetic.Bootstrapping


-- @@ L82-82 verbatim
namespace FFL.FirstOrder.Arithmetic


-- @@ L84-84 verbatim
open _root_.FFL.FirstOrder.Entailment


-- @@ L86-86 verbatim
variable (T : ArithmeticTheory) [𝗜𝚺₁ ⪯ T] [T.Δ₁]


-- @@ L88-92 verbatim
instance [ℕ↓[ℒₒᵣ] ⊧* T] : ℕ↓[ℒₒᵣ] ⊧* T ∪ T.Con := by
  have : 𝗥₀ ⪯ 𝗜𝚺₁ := inferInstance
  have : 𝗥₀ ⪯ T := Entailment.WeakerThan.trans this inferInstance
  have : Entailment.Consistent T := ArithmeticTheory.consistent_of_sound T (Eq ⊥) rfl
  simp [models_iff, *]


-- @@ L94-94 verbatim
end FFL.FirstOrder.Arithmetic
