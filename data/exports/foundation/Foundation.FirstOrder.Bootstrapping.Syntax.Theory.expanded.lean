module

public import Foundation.FirstOrder.Bootstrapping.Syntax.Formula.Coding
public import Foundation.FirstOrder.Basic.PrimrecCoding
public import Foundation.Vorspiel.Computability


-- @@ L7-7 verbatim
@[expose] public section

-- @@ L8-8 verbatim
namespace FFL.FirstOrder.Theory


-- @@ L10-10 verbatim
variable {L : Language} [L.Encodable] [L.LORDefinable]


-- @@ L12-16 verbatim
/-- TODO: define predicate `VariableFree` and make `mem_iff` `∀ φ : Sentence, ℕ ⊧/![⌜φ⌝] ch.val ↔ φ ∈ T` -/
class Δ₁ (T : Theory L) where
  ch : 𝚫₁.Semisentence 1
  mem_iff : ∀ φ : Proposition L, ℕ ⊧/![⌜φ⌝] ch.val ↔ ∃ σ ∈ T, φ = σ
  isDelta1 : ch.ProvablyProperOn 𝗜𝚺₁


-- @@ L18-18 verbatim
abbrev Δ₁ch (T : Theory L) [T.Δ₁] : 𝚫₁.Semisentence 1 := Δ₁.ch T


-- @@ L20-20 verbatim
variable [L.Primcodable]


-- @@ L22-23 verbatim
class RE (T : Theory L) : Prop where
  re : REPred (· ∈ T)


-- @@ L25-26 verbatim
protected class Primrec (T : Theory L) : Prop where
  primrec : PrimrecPred (· ∈ T)


-- @@ L28-29 verbatim
instance {T : Theory L} [T.Primrec] : T.RE :=
  ⟨Theory.Primrec.primrec.computablePred.to_re⟩


-- @@ L31-31 verbatim
namespace RE


-- @@ L33-33 verbatim
variable {T U : Theory L}


-- @@ L35-37 verbatim
omit [L.LORDefinable] in
lemma add (hT : T.RE) (hU : U.RE) : (T ∪ U).RE :=
  ⟨(REPred.or hT.re hU.re).of_eq fun _ ↦ Iff.rfl⟩


-- @@ L39-39 verbatim
variable [L.DecidableEq]


-- @@ L41-49 verbatim
omit [L.LORDefinable] in
lemma ofFinite (hT : Set.Finite T) : T.RE := by
  constructor;
  simpa using show REPred (· ∈ hT.toFinset) by
    induction hT.toFinset using Finset.induction_on with
    | empty => exact (REPred.const False).of_eq fun _ ↦ by simp
    | @insert σ s _ ih =>
      exact ((PrimrecPred.computablePred
        (Primrec.eq.comp Primrec.id (Primrec.const σ))).to_re.or ih).of_eq fun _ ↦ by simp


-- @@ L51-51 verbatim
end RE


-- @@ L53-53 verbatim
end FFL.FirstOrder.Theory


-- @@ L55-55 verbatim
namespace FFL.FirstOrder.Arithmetic.Bootstrapping


-- @@ L57-57 verbatim
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]


-- @@ L59-59 verbatim
variable {L : Language} [L.Encodable] [L.LORDefinable]


-- @@ L61-61 verbatim
def _root_.FFL.FirstOrder.Theory.Δ₁Class (T : Theory L) [T.Δ₁] : Set V := { φ : V | V ⊧/![φ] T.Δ₁ch.val }


-- @@ L63-63 verbatim
variable {T : Theory L} [T.Δ₁]


-- @@ L65-73 verbatim
instance Δ₁Class.defined : 𝚫₁-Predicate[V] (· ∈ T.Δ₁Class) via T.Δ₁ch := .mk <| by
  constructor
  · intro v
    have : V ⊧/![v 0] (Theory.Δ₁.ch T).sigma.val ↔ V ⊧/![v 0] (Theory.Δ₁.ch T).pi.val := by
      have := (consequence_iff (T := 𝗜𝚺₁)).mp (Theory.Proof.sound <| FirstOrder.Theory.Δ₁.isDelta1 (T := T)) V inferInstance
      simp [models_iff] at this ⊢
      simpa [Matrix.constant_eq_singleton] using this ![v 0]
    rwa [Matrix.fun_eq_vec_one v]
  · intro v; simp [←Matrix.fun_eq_vec_one, Theory.Δ₁Class]


-- @@ L75-75 verbatim
instance Δ₁Class.definable : 𝚫₁-Predicate[V] (· ∈ T.Δ₁Class) := Δ₁Class.defined.to_definable


-- @@ L77-77 verbatim
@[simp] lemma Δ₁Class.proper : T.Δ₁ch.ProperOn V := (Theory.Δ₁.isDelta1 (T := T)).properOn V


-- @@ L79-83 verbatim
@[simp] lemma Δ₁Class.mem_iff_s {φ : Proposition L} : (⌜φ⌝ : V) ∈ T.Δ₁Class ↔ ∃ σ ∈ T, φ = σ :=
  have : V ⊧/![⌜φ⌝] T.Δ₁ch.val ↔ ℕ ⊧/![⌜φ⌝] T.Δ₁ch.val := by
    simpa [Semiformula.coe_quote_eq_quote, Matrix.constant_eq_singleton]
      using FirstOrder.Arithmetic.models_iff_of_Delta1 (V := V) (σ := T.Δ₁ch) (by simp) (by simp) (e := ![⌜φ⌝])
  Iff.trans this (Theory.Δ₁.mem_iff _)


-- @@ L85-86 verbatim
@[simp] lemma Δ₁Class.mem_iff {φ : Sentence L} : (⌜φ⌝ : V) ∈ T.Δ₁Class ↔ φ ∈ T := by
  simp [Sentence.quote_def, Δ₁Class.mem_iff_s]


-- @@ L88-88 verbatim
@[simp] lemma Δ₁Class.mem_iff' {φ : Sentence L} : V ⊧/![⌜φ⌝] T.Δ₁ch.val ↔ φ ∈ T := Δ₁Class.mem_iff


-- @@ L90-90 verbatim
@[simp] lemma Δ₁Class.mem_iff'_s {φ : Proposition L} : V ⊧/![⌜φ⌝] T.Δ₁ch.val ↔ ∃ σ ∈ T, φ = σ := Δ₁Class.mem_iff_s


-- @@ L92-93 verbatim
@[simp] lemma Δ₁Class.mem_iff'' {φ : Sentence L} : ((⌜φ⌝ : Bootstrapping.Formula V L).val : V) ∈ T.Δ₁Class ↔ φ ∈ T :=
  Δ₁Class.mem_iff


-- @@ L95-95 verbatim
end FFL.FirstOrder.Arithmetic.Bootstrapping


-- @@ L97-97 verbatim
namespace FFL.FirstOrder.Theory


-- @@ L99-99 verbatim
variable {L : Language} [L.Encodable] [L.LORDefinable]


-- @@ L101-101 verbatim
variable {T U : Theory L}


-- @@ L103-103 verbatim
namespace Δ₁


-- @@ L105-105 verbatim
open Arithmetic.HierarchySymbol.Semiformula FFL.FirstOrder.Theory


-- @@ L107-113 verbatim
abbrev add (dT : T.Δ₁) (dU : U.Δ₁) : (T ∪ U).Δ₁ where
  ch := T.Δ₁ch ⋎ U.Δ₁ch
  mem_iff {φ} := by
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, val_or, LogicalConnective.HomClass.map_or,
      FirstOrder.Arithmetic.Bootstrapping.Δ₁Class.mem_iff'_s, LogicalConnective.Prop.or_eq, Set.mem_union]
    grind
  isDelta1 := ProvablyProperOn.ofProperOn.{0} _ fun V _ _ ↦ ProperOn.or (by simp) (by simp)


-- @@ L115-118 verbatim
abbrev ofEq (dT : T.Δ₁) (h : T = U) : U.Δ₁ where
  ch := dT.ch
  mem_iff := by rcases h; exact dT.mem_iff
  isDelta1 := by rcases h; exact dT.isDelta1


-- @@ L120-123 verbatim
instance empty : Theory.Δ₁ (∅ : Theory L) where
  ch := ⊥
  mem_iff {ψ} := by simp
  isDelta1 := ProvablyProperOn.ofProperOn.{0} _ fun V _ _ ↦ by simp


-- @@ L125-128 verbatim
abbrev singleton (φ : Sentence L) : Theory.Δ₁ {φ} where
  ch := .ofZero (.mkSigma “x. x = ↑(Encodable.encode φ)”) _
  mem_iff {ψ} := by simp [Semiformula.quote_eq_encode]
  isDelta1 := ProvablyProperOn.ofProperOn.{0} _ fun V _ _ ↦ by simp


-- @@ L130-132 verbatim
@[simp] lemma singleton_toTDef_ch_val (φ : Sentence L) :
    letI := Δ₁.singleton φ
    ({φ} : Theory L).Δ₁ch.val = “x. x = ↑(Encodable.encode φ)” := by rfl


-- @@ L134-137 verbatim
abbrev ofList (l : List (Sentence L)) : Δ₁ {φ | φ ∈ l} :=
  match l with
  |     [] => empty.ofEq (by ext; simp)
  | φ :: l => ((singleton φ).add (ofList l)).ofEq (by ext; simp)


-- @@ L139-139 verbatim
noncomputable abbrev ofFinite (T : Theory L) (h : Set.Finite T) : T.Δ₁ := (ofList h.toFinset.toList).ofEq (by ext; simp)


-- @@ L141-141 verbatim
instance [T.Δ₁] [U.Δ₁] : (T ∪ U).Δ₁ := add inferInstance inferInstance


-- @@ L143-143 verbatim
instance (φ : Sentence L) : Theory.Δ₁ {φ} := singleton φ


-- @@ L145-145 verbatim
instance insert [d : T.Δ₁] : (insert φ T).Δ₁ := (d.add (singleton φ)).ofEq (by ext; simp)


-- @@ L147-147 verbatim
end Δ₁


-- @@ L149-149 verbatim
end FFL.FirstOrder.Theory
