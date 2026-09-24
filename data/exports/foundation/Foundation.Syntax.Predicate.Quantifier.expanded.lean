module

public import Foundation.Logic.LogicSymbol


-- @@ L5-5 verbatim
@[expose] public section


-- @@ L7-7 verbatim
namespace FFL


-- @@ L9-9 verbatim
inductive Polarity where | sigma | pi


-- @@ L11-11 verbatim
namespace Polarity


-- @@ L13-13 verbatim
instance : SigmaSymbol Polarity := ⟨sigma⟩


-- @@ L15-15 verbatim
instance : PiSymbol Polarity := ⟨pi⟩


-- @@ L17-19 verbatim
def alt : Polarity → Polarity
  | 𝚺 => 𝚷
  | 𝚷 => 𝚺


-- @@ L21-21 verbatim
@[simp] lemma eq_sigma : sigma = 𝚺 := rfl


-- @@ L23-23 verbatim
@[simp] lemma eq_pi : pi = 𝚷 := rfl


-- @@ L25-25 verbatim
@[simp] lemma alt_sigma : alt 𝚺 = 𝚷 := rfl


-- @@ L27-27 verbatim
@[simp] lemma alt_pi : alt 𝚷 = 𝚺 := rfl


-- @@ L29-29 verbatim
@[simp] lemma alt_alt (Γ : Polarity) : Γ.alt.alt = Γ := by rcases Γ <;> simp


-- @@ L31-32 verbatim
/-- `Γ` with its polarity flipped `k` times. -/
abbrev altItr (Γ : Polarity) (k : ℕ) : Polarity := Polarity.alt^[k] Γ


-- @@ L34-40 verbatim
@[simp] lemma altItr_zero (Γ : Polarity) : Γ.altItr 0 = Γ := rfl

lemma altItr_succ (Γ : Polarity) (k : ℕ) : Γ.altItr (k + 1) = (Γ.altItr k).alt :=
  Function.iterate_succ_apply' _ _ _

lemma altItr_succ' (Γ : Polarity) (k : ℕ) : Γ.altItr (k + 1) = Γ.alt.altItr k :=
  Function.iterate_succ_apply _ _ _


-- @@ L42-42 verbatim
section symbol


-- @@ L44-44 verbatim
variable {α : Type*} [SigmaSymbol α] [PiSymbol α]


-- @@ L46-48 verbatim
protected def coe : Polarity → α
 | 𝚺 => 𝚺
 | 𝚷 => 𝚷


-- @@ L50-50 verbatim
instance : Coe Polarity α := ⟨Polarity.coe⟩


-- @@ L52-52 verbatim
@[simp] lemma coe_sigma : ((𝚺 : Polarity) : α) = 𝚺 := rfl


-- @@ L54-54 verbatim
@[simp] lemma coe_pi : ((𝚷 : Polarity) : α) = 𝚷 := rfl


-- @@ L56-56 verbatim
end symbol


-- @@ L58-58 verbatim
end Polarity


-- @@ L60-60 verbatim
inductive SigmaPiDelta where | sigma | pi | delta


-- @@ L62-62 verbatim
namespace SigmaPiDelta


-- @@ L64-64 verbatim
instance : SigmaSymbol SigmaPiDelta := ⟨sigma⟩


-- @@ L66-66 verbatim
instance : PiSymbol SigmaPiDelta := ⟨pi⟩


-- @@ L68-68 verbatim
instance : DeltaSymbol SigmaPiDelta := ⟨delta⟩


-- @@ L70-73 verbatim
def alt : SigmaPiDelta → SigmaPiDelta
  | 𝚺 => 𝚷
  | 𝚷 => 𝚺
  | 𝚫 => 𝚫


-- @@ L75-75 verbatim
@[simp] lemma eq_sigma : sigma = 𝚺 := rfl


-- @@ L77-77 verbatim
@[simp] lemma eq_pi : pi = 𝚷 := rfl


-- @@ L79-79 verbatim
@[simp] lemma eq_delta : delta = 𝚫 := rfl


-- @@ L81-81 verbatim
@[simp] lemma alt_sigma : alt 𝚺 = 𝚷 := rfl


-- @@ L83-83 verbatim
@[simp] lemma alt_pi : alt 𝚷 = 𝚺 := rfl


-- @@ L85-85 verbatim
@[simp] lemma alt_delta : alt 𝚫 = 𝚫 := rfl


-- @@ L87-87 verbatim
@[simp] lemma alt_alt (Γ : SigmaPiDelta) : Γ.alt.alt = Γ := by rcases Γ <;> simp


-- @@ L89-89 verbatim
@[simp] lemma alt_coe (Γ : Polarity) : SigmaPiDelta.alt Γ = (Γ.alt : SigmaPiDelta) := by cases Γ <;> simp


-- @@ L91-91 verbatim
end SigmaPiDelta


-- @@ L93-93 verbatim
/-! ## First-order quantifiers -/


-- @@ L95-95 verbatim
namespace FirstOrder


-- @@ L97-98 verbatim
class UnivQuantifier (α : ℕ → Type*) where
  all : α (n + 1) → α n


-- @@ L100-100 verbatim
prefix:64 "∀¹ " => UnivQuantifier.all


-- @@ L102-103 verbatim
class ExsQuantifier (α : ℕ → Type*) where
  exs : α (n + 1) → α n


-- @@ L105-105 verbatim
prefix:64 "∃¹ " => ExsQuantifier.exs


-- @@ L107-107 verbatim
attribute [match_pattern] UnivQuantifier.all ExsQuantifier.exs


-- @@ L109-109 verbatim
class Quantifier (α : ℕ → Type*) extends UnivQuantifier α, ExsQuantifier α


-- @@ L111-114 verbatim
/-- Logical Connectives with Quantifiers. -/
class LCWQ (α : ℕ → Type*) extends Quantifier α where
  connectives : (n : ℕ) → LogicalConnective (α n)
  neutrals : (n : ℕ) → LogicalNeutral (α n)


-- @@ L116-116 verbatim
instance (α : ℕ → Type*) [LCWQ α] (n : ℕ) : LogicalConnective (α n) := LCWQ.connectives n


-- @@ L118-118 verbatim
instance (α : ℕ → Type*) [LCWQ α] (n : ℕ) : LogicalNeutral (α n) := LCWQ.neutrals n


-- @@ L120-123 verbatim
instance (α : ℕ → Type*) [Quantifier α] [(n : ℕ) → LogicalConnective (α n)]
    [(n : ℕ) → LogicalNeutral (α n)] : LCWQ α where
  connectives := inferInstance
  neutrals := inferInstance


-- @@ L125-125 verbatim
section UnivQuantifier


-- @@ L127-127 verbatim
variable {α : ℕ → Type*} [UnivQuantifier α]


-- @@ L129-131 verbatim
def allClosure : {n : ℕ} → α n → α 0
  |     0, a => a
  | _ + 1, a => allClosure (∀¹ a)


-- @@ L133-136 verbatim
/--
The universal closure of a formula.
-/
prefix:64 "∀¹* " => allClosure


-- @@ L138-140 verbatim
@[simp] lemma allClosure_zero (a : α 0) : ∀¹* a = a := rfl

lemma allClosure_succ {n} (a : α (n + 1)) : ∀¹* a = ∀¹* ∀¹ a := rfl


-- @@ L142-144 verbatim
def allItr : (k : ℕ) → α (n + k) → α n
  |     0, a => a
  | k + 1, a => allItr k (∀¹ a)


-- @@ L146-146 verbatim
notation "∀¹^[" k "] " φ:64 => allItr k φ


-- @@ L148-148 verbatim
@[simp] lemma allItr_zero (a : α n) : ∀¹^[0] a = a := rfl


-- @@ L150-152 verbatim
@[simp] lemma allItr_one (a : α (n + 1)) : ∀¹^[1] a = ∀¹ a := rfl

lemma allItr_succ {k} (a : α (n + (k + 1))) : ∀¹^[k + 1] a = ∀¹^[k] (∀¹ a) := rfl


-- @@ L154-154 verbatim
end UnivQuantifier


-- @@ L156-156 verbatim
section ExsQuantifier


-- @@ L158-158 verbatim
variable {α : ℕ → Type*} [ExsQuantifier α]


-- @@ L160-162 verbatim
def exsClosure : {n : ℕ} → α n → α 0
  |     0, a => a
  | _ + 1, a => exsClosure (∃¹ a)


-- @@ L164-167 verbatim
/--
The existential closure of a formula.
-/
prefix:64 "∃¹* " => exsClosure


-- @@ L169-171 verbatim
@[simp] lemma exsClosure_zero (a : α 0) : ∃¹* a = a := rfl

lemma exsClosure_succ {n} (a : α (n + 1)) : ∃¹* a = ∃¹* ∃¹ a := rfl


-- @@ L173-175 verbatim
def exsItr : (k : ℕ) → α (n + k) → α n
  |     0, a => a
  | k + 1, a => exsItr k (∃¹ a)


-- @@ L177-178 verbatim
/-- Iterated application of `k` existential quantifiers. -/
notation "∃¹^[" k "] " φ:64 => exsItr k φ


-- @@ L180-180 verbatim
@[simp] lemma exsItr_zero (a : α n) : ∃¹^[0] a = a := rfl


-- @@ L182-184 verbatim
@[simp] lemma exsItr_one (a : α (n + 1)) : ∃¹^[1] a = ∃¹ a := rfl

lemma exsItr_succ {k} (a : α (n + (k + 1))) : ∃¹^[k + 1] a = ∃¹^[k] (∃¹ a) := rfl


-- @@ L186-186 verbatim
end ExsQuantifier


-- @@ L188-188 verbatim
section quantifier


-- @@ L190-190 verbatim
variable {α : ℕ → Type*}


-- @@ L192-192 verbatim
def ball [UnivQuantifier α] [Arrow (α (n + 1))] (φ : α (n + 1)) (ψ : α (n + 1)) : α n := ∀¹ (φ 🡒 ψ)


-- @@ L194-194 verbatim
def bexs [ExsQuantifier α] [Wedge (α (n + 1))] (φ : α (n + 1)) (ψ : α (n + 1)) : α n := ∃¹ (φ ⋏ ψ)


-- @@ L196-197 verbatim
/-- A bounded universal quantifier. `∀¹[φ] ψ` is defined as `∀¹ (φ 🡒 ψ)`. -/
notation:64 "∀¹[" φ "] " ψ => ball φ ψ


-- @@ L199-200 verbatim
/-- A bounded existential quantifier. `∃¹[φ] ψ` is defined as `∃¹ (φ ⋏ ψ)`. -/
notation:64 "∃¹[" φ "] " ψ => bexs φ ψ


-- @@ L202-202 verbatim
end quantifier


-- @@ L204-204 verbatim
end FirstOrder


-- @@ L206-206 verbatim
namespace Polarity


-- @@ L208-208 verbatim
variable {α : ℕ → Type*} [FirstOrder.UnivQuantifier α] [FirstOrder.ExsQuantifier α] {n : ℕ} {Γ : Polarity}


-- @@ L210-212 verbatim
def quant : Polarity → α (n + 1) → α n
  | 𝚺 => FirstOrder.ExsQuantifier.exs
  | 𝚷 => FirstOrder.UnivQuantifier.all


-- @@ L214-214 verbatim
@[simp] lemma quant_sigma (φ : α (n + 1)) : (𝚺 : Polarity).quant φ = ∃¹ φ := rfl


-- @@ L216-216 verbatim
@[simp] lemma quant_pi (φ : α (n + 1)) : (𝚷 : Polarity).quant φ = ∀¹ φ := rfl


-- @@ L218-221 verbatim
/-- Prefixes `k` alternating quantifiers starting with `Γ`. -/
def quantItr (Γ : Polarity) : (k : ℕ) → {n : ℕ} → α (n + k) → α n
  | 0,     n, φ => φ
  | k + 1, n, φ => Γ.quant $ quantItr Γ.alt k (cast (by grind) φ)


-- @@ L223-224 verbatim
@[simp]
lemma quantItr_zero (φ : α n) : quantItr Γ 0 φ = φ := rfl


-- @@ L226-242 verbatim
@[simp] lemma quantItr_one (φ : α (n + 1)) : quantItr Γ 1 φ = Γ.quant φ := rfl

lemma quantItr_succ {k} (φ : α (n + (k + 1))) :
    quantItr Γ (k + 1) φ = Γ.quant (quantItr Γ.alt k (cast (by grind) φ)) := rfl

lemma cast_quant {m₁ m₂ : ℕ} (h : m₁ = m₂) (Γ : Polarity) (φ : α (m₁ + 1)) :
  cast (congrArg α h) (Γ.quant φ) = Γ.quant (cast (by grind) φ) := by
  subst h; rfl

lemma quantItr_succ' {k} (φ : α (n + (k + 1))) :
    quantItr Γ (k + 1) φ = quantItr Γ k ((Γ.altItr k).quant φ) := by
  induction k generalizing n Γ with
  | zero => simp [quantItr_one];
  | succ k ih =>
    rw [quantItr_succ, ih, quantItr_succ, altItr_succ']
    congr 2;
    grind;


-- @@ L244-244 verbatim
end Polarity


-- @@ L246-246 verbatim
/-! ## Second-order quantifiers -/


-- @@ L248-248 verbatim
namespace SecondOrder


-- @@ L250-251 verbatim
class UnivQuantifier (α : ℕ → ℕ → Type*) where
  all₁ : α (m + 1) n → α m n


-- @@ L253-253 verbatim
prefix:64 "∀² " => UnivQuantifier.all₁


-- @@ L255-256 verbatim
class ExsQuantifier (α : ℕ → ℕ → Type*) where
  exs₁ : α (m + 1) n → α m n


-- @@ L258-258 verbatim
prefix:64 "∃² " => ExsQuantifier.exs₁


-- @@ L260-260 verbatim
attribute [match_pattern] UnivQuantifier.all₁ ExsQuantifier.exs₁


-- @@ L262-262 verbatim
class Quantifier (α : ℕ → ℕ → Type*) extends UnivQuantifier α, ExsQuantifier α


-- @@ L264-266 verbatim
/-- Logical Connectives with Quantifiers. -/
class LCWQ (α : ℕ → ℕ → Type*) extends Quantifier α where
  firstOrder : (m : ℕ) → FirstOrder.LCWQ (α m)


-- @@ L268-268 verbatim
instance (α : ℕ → ℕ → Type*) [LCWQ α] (m : ℕ) : FirstOrder.LCWQ (α m) := LCWQ.firstOrder m


-- @@ L270-271 verbatim
instance (α : ℕ → ℕ → Type*) [Quantifier α] [(m : ℕ) → FirstOrder.LCWQ (α m)] : LCWQ α where
  firstOrder := inferInstance


-- @@ L273-273 verbatim
section UnivQuantifier


-- @@ L275-275 verbatim
variable {α : ℕ → ℕ → Type*} [UnivQuantifier α]


-- @@ L277-279 verbatim
def allClosure : {m : ℕ} → α m n → α 0 n
  |     0, a => a
  | _ + 1, a => allClosure (∀² a)


-- @@ L281-281 verbatim
prefix:64 "∀²* " => allClosure


-- @@ L283-285 verbatim
@[simp] lemma allClosure_zero (a : α 0 n) : ∀²* a = a := rfl

lemma allClosure_succ {n} (a : α (n + 1) n) : ∀²* a = ∀²* ∀² a := rfl


-- @@ L287-289 verbatim
def allItr : (k : ℕ) → α (m + k) n → α m n
  |     0, a => a
  | k + 1, a => allItr k (∀² a)


-- @@ L291-291 verbatim
notation "∀²^[" k "] " φ:64 => allItr k φ


-- @@ L293-293 verbatim
@[simp] lemma allItr_zero (a : α m n) : ∀²^[0] a = a := rfl


-- @@ L295-297 verbatim
@[simp] lemma allItr_one (a : α (m + 1) n) : ∀²^[1] a = ∀² a := rfl

lemma allItr_succ {k} (a : α (m + (k + 1)) n) : ∀²^[k + 1] a = ∀²^[k] (∀² a) := rfl


-- @@ L299-299 verbatim
end UnivQuantifier


-- @@ L301-301 verbatim
section ExsQuantifier


-- @@ L303-303 verbatim
variable {α : ℕ → ℕ → Type*} [ExsQuantifier α]


-- @@ L305-307 verbatim
def exsClosure : {m : ℕ} → α m n → α 0 n
  |     0, a => a
  | _ + 1, a => exsClosure (∃² a)


-- @@ L309-309 verbatim
prefix:64 "∃²* " => exsClosure


-- @@ L311-313 verbatim
@[simp] lemma exsClosure_zero (a : α 0 n) : ∃²* a = a := rfl

lemma exsClosure_succ {n} (a : α (m + 1) n) : ∃²* a = ∃²* ∃² a := rfl


-- @@ L315-317 verbatim
def exsItr : (k : ℕ) → α (m + k) n → α m n
  |     0, a => a
  | k + 1, a => exsItr k (∃² a)


-- @@ L319-319 verbatim
notation "∃²^[" k "] " φ:64 => exsItr k φ


-- @@ L321-321 verbatim
@[simp] lemma exsItr_zero (a : α m n) : ∃²^[0] a = a := rfl


-- @@ L323-325 verbatim
@[simp] lemma exsItr_one (a : α (m + 1) n) : ∃²^[1] a = ∃² a := rfl

lemma exsItr_succ {k} (a : α (m + (k + 1)) n) : ∃²^[k + 1] a = ∃²^[k] (∃² a) := rfl


-- @@ L327-327 verbatim
end ExsQuantifier


-- @@ L329-329 verbatim
section quantifier


-- @@ L331-331 verbatim
variable {α : ℕ → ℕ → Type*}


-- @@ L333-333 verbatim
def ball [UnivQuantifier α] [Arrow (α (m + 1) n)] (φ : α (m + 1) n) (ψ : α (m + 1) n) : α m n := ∀² (φ 🡒 ψ)


-- @@ L335-335 verbatim
def bexs [ExsQuantifier α] [Wedge (α (m + 1) n)] (φ : α (m + 1) n) (ψ : α (m + 1) n) : α m n := ∃² (φ ⋏ ψ)


-- @@ L337-337 verbatim
notation:64 "∀²[" φ "] " ψ => ball φ ψ


-- @@ L339-339 verbatim
notation:64 "∃²[" φ "] " ψ => bexs φ ψ


-- @@ L341-341 verbatim
end quantifier


-- @@ L343-343 verbatim
end SecondOrder


-- @@ L345-345 verbatim
end FFL


-- @@ L347-347 verbatim
end
