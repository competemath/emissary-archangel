/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Logic.LogicSymbol
import Mathlib.Tactic.Bound.Init


-- @@ L11-11 verbatim
/-! # Quantifier -/


-- @@ L13-13 verbatim
@[expose] public section




-- @@ L17-17 verbatim
namespace LO


-- @@ L19-22 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
@[notation_class] class SigmaSymbol (α : Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  sigma : α


-- @@ L24-27 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
@[notation_class] class PiSymbol (α : Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  pi : α


-- @@ L29-32 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
@[notation_class] class DeltaSymbol (α : Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  delta : α


-- @@ L34-35 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation "Sg" => SigmaSymbol.sigma


-- @@ L37-38 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation "Pg" => PiSymbol.pi


-- @@ L40-41 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation "Dlt" => DeltaSymbol.delta


-- @@ L43-43 verbatim
attribute [match_pattern] SigmaSymbol.sigma PiSymbol.pi DeltaSymbol.delta


-- @@ L45-48 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
inductive Polarity where
  | sigma
  | pi


-- @@ L50-50 verbatim
namespace Polarity


-- @@ L52-52 verbatim
instance : SigmaSymbol Polarity := ⟨sigma⟩


-- @@ L54-54 verbatim
instance : PiSymbol Polarity := ⟨pi⟩


-- @@ L56-59 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def alt : Polarity → Polarity
  | SigmaSymbol.sigma => PiSymbol.pi
  | PiSymbol.pi => SigmaSymbol.sigma


-- @@ L61-61 expanded
lemma eq_sigma : sigma = SigmaSymbol.sigma :=
  rfl


-- @@ L63-63 expanded
lemma eq_pi : pi = PiSymbol.pi :=
  rfl


-- @@ L65-65 expanded
@[simp]
lemma alt_sigma : alt SigmaSymbol.sigma = PiSymbol.pi :=
  rfl


-- @@ L67-67 expanded
@[simp]
lemma alt_pi : alt PiSymbol.pi = SigmaSymbol.sigma :=
  rfl


-- @@ L69-69 verbatim
@[simp] lemma alt_alt (Γ : Polarity) : Γ.alt.alt = Γ := by rcases Γ <;> rfl


-- @@ L71-71 verbatim
end Polarity


-- @@ L73-74 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
inductive SigmaPiDelta where | sigma | pi | delta


-- @@ L76-76 verbatim
namespace SigmaPiDelta


-- @@ L78-78 verbatim
instance : SigmaSymbol SigmaPiDelta := ⟨sigma⟩


-- @@ L80-80 verbatim
instance : PiSymbol SigmaPiDelta := ⟨pi⟩


-- @@ L82-82 verbatim
instance : DeltaSymbol SigmaPiDelta := ⟨delta⟩


-- @@ L84-88 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def alt : SigmaPiDelta → SigmaPiDelta
  | SigmaSymbol.sigma => PiSymbol.pi
  | PiSymbol.pi => SigmaSymbol.sigma
  | DeltaSymbol.delta => DeltaSymbol.delta


-- @@ L90-90 expanded
lemma eq_sigma : sigma = SigmaSymbol.sigma :=
  rfl


-- @@ L92-92 expanded
lemma eq_pi : pi = PiSymbol.pi :=
  rfl


-- @@ L94-94 expanded
lemma eq_delta : delta = DeltaSymbol.delta :=
  rfl


-- @@ L96-96 expanded
@[simp]
lemma alt_sigma : alt SigmaSymbol.sigma = PiSymbol.pi :=
  rfl


-- @@ L98-98 expanded
@[simp]
lemma alt_pi : alt PiSymbol.pi = SigmaSymbol.sigma :=
  rfl


-- @@ L100-100 expanded
@[simp]
lemma alt_delta : alt DeltaSymbol.delta = DeltaSymbol.delta :=
  rfl


-- @@ L102-102 verbatim
@[simp] lemma alt_alt (Γ : SigmaPiDelta) : Γ.alt.alt = Γ := by rcases Γ <;> rfl


-- @@ L104-104 verbatim
end SigmaPiDelta


-- @@ L106-109 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
@[notation_class] class UnivQuantifier (α : ℕ → Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  univ : ∀ {n}, α (n + 1) → α n


-- @@ L111-114 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
@[notation_class] class ExQuantifier (α : ℕ → Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  ex : ∀ {n}, α (n + 1) → α n


-- @@ L116-117 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
prefix:64 "∀' " => UnivQuantifier.univ


-- @@ L119-120 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
prefix:64 "∃' " => ExQuantifier.ex


-- @@ L122-124 verbatim
attribute [match_pattern]
  UnivQuantifier.univ
  ExQuantifier.ex


-- @@ L126-127 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class Quantifier (α : ℕ → Type*) extends UnivQuantifier α, ExQuantifier α


-- @@ L129-132 verbatim
/-- Logical Connectives with Quantifiers. -/
class LCWQ (α : ℕ → Type*) extends Quantifier α where
  /-- Imported declaration from the Incompleteness formalization. -/
  connectives : (n : ℕ) → LogicalConnective (α n)


-- @@ L134-134 verbatim
instance (α : ℕ → Type*) [LCWQ α] (n : ℕ) : LogicalConnective (α n) := LCWQ.connectives n


-- @@ L136-137 verbatim
instance (α : ℕ → Type*) [Quantifier α] [(n : ℕ) → LogicalConnective (α n)] : LCWQ α where
  connectives := inferInstance


-- @@ L139-139 verbatim
section «lp_section_1»


-- @@ L141-141 verbatim
variable {α : ℕ → Type*} [UnivQuantifier α] [ExQuantifier α]


-- @@ L143-146 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def quant : Polarity → α (n + 1) → α n
  | SigmaSymbol.sigma, φ => ExQuantifier.ex φ
  | PiSymbol.pi, φ => UnivQuantifier.univ φ


-- @@ L148-148 expanded
@[simp]
lemma quant_sigma (φ : α (n + 1)) : quant SigmaSymbol.sigma φ = ExQuantifier.ex φ :=
  rfl


-- @@ L150-150 expanded
@[simp]
lemma quant_pi (φ : α (n + 1)) : quant PiSymbol.pi φ = UnivQuantifier.univ φ :=
  rfl


-- @@ L152-152 verbatim
end «lp_section_1»


-- @@ L154-154 verbatim
section «lp_section_2»


-- @@ L156-156 verbatim
variable {α : ℕ → Type*} [UnivQuantifier α]


-- @@ L158-161 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def univClosure : {n : ℕ} → α n → α 0
  | 0, a => a
  | _ + 1, a => univClosure (UnivQuantifier.univ a)


-- @@ L163-164 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
prefix:64 "∀* " => univClosure


-- @@ L166-166 expanded
@[simp]
lemma univClosure_zero (a : α 0) : univClosure a = a :=
  rfl


-- @@ L168-168 expanded
lemma univClosure_succ {n} (a : α (n + 1)) : univClosure a = univClosure (UnivQuantifier.univ a) :=
  rfl


-- @@ L170-173 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def univItr : (k : ℕ) → α (n + k) → α n
  | 0, a => a
  | k + 1, a => univItr k (UnivQuantifier.univ a)


-- @@ L175-176 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation "∀^[" k "] " φ:64 => univItr k φ


-- @@ L178-178 expanded
@[simp]
lemma univItr_zero (a : α n) : univItr 0 a = a :=
  rfl


-- @@ L180-180 expanded
@[simp]
lemma univItr_one (a : α (n + 1)) : univItr 1 a = UnivQuantifier.univ a :=
  rfl


-- @@ L182-182 expanded
lemma univItr_succ {k} (a : α (n + (k + 1))) :
    univItr (k + 1) a = univItr k (UnivQuantifier.univ a) :=
  rfl


-- @@ L184-184 verbatim
end «lp_section_2»


-- @@ L186-186 verbatim
section «lp_section_3»


-- @@ L188-188 verbatim
variable {α : ℕ → Type*} [ExQuantifier α]


-- @@ L190-193 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def exClosure : {n : ℕ} → α n → α 0
  | 0, a => a
  | _ + 1, a => exClosure (ExQuantifier.ex a)


-- @@ L195-196 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
prefix:64 "∃* " => exClosure


-- @@ L198-198 expanded
@[simp]
lemma exClosure_zero (a : α 0) : exClosure a = a :=
  rfl


-- @@ L200-200 expanded
lemma exClosure_succ {n} (a : α (n + 1)) : exClosure a = exClosure (ExQuantifier.ex a) :=
  rfl


-- @@ L202-205 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def exItr : (k : ℕ) → α (n + k) → α n
  | 0, a => a
  | k + 1, a => exItr k (ExQuantifier.ex a)


-- @@ L207-208 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation "∃^[" k "] " φ:64 => exItr k φ


-- @@ L210-210 expanded
@[simp]
lemma exItr_zero (a : α n) : exItr 0 a = a :=
  rfl


-- @@ L212-212 expanded
@[simp]
lemma exItr_one (a : α (n + 1)) : exItr 1 a = ExQuantifier.ex a :=
  rfl


-- @@ L214-214 expanded
lemma exItr_succ {k} (a : α (n + (k + 1))) : exItr (k + 1) a = exItr k (ExQuantifier.ex a) :=
  rfl


-- @@ L216-216 verbatim
end «lp_section_3»


-- @@ L218-218 verbatim
section «lp_section_4»


-- @@ L220-220 verbatim
variable {α : ℕ → Type*}


-- @@ L222-224 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def ball [UnivQuantifier α] [Arrow (α (n + 1))] (φ : α (n + 1)) (ψ : α (n + 1)) : α n :=
  UnivQuantifier.univ (Arrow.arrow φ ψ)


-- @@ L226-227 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def bex [ExQuantifier α] [Wedge (α (n + 1))] (φ : α (n + 1)) (ψ : α (n + 1)) : α n :=
  ExQuantifier.ex (Wedge.wedge φ ψ)


-- @@ L229-230 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation:64 "∀[" φ "] " ψ => ball φ ψ


-- @@ L232-233 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation:64 "∃[" φ "] " ψ => bex φ ψ


-- @@ L235-235 verbatim
end «lp_section_4»


-- @@ L237-237 verbatim
end LO
