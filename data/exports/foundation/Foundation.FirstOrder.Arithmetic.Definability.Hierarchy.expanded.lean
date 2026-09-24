module

public import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic


-- @@ L5-5 verbatim
@[expose] public section

-- @@ L6-17 verbatim
/-!

# Arithmetical Formula Sorted by Arithmetical Hierarchy

This file defines the $\Sigma_n / \Pi_n / \Delta_n$ formulas of arithmetic of first-order logic.

- `𝚺-[m].Semiformula ξ n` is a `ArithmeticSemiformula ξ n` which is `𝚺-[m]`.
- `𝚷-[m].Semiformula ξ n` is a `ArithmeticSemiformula ξ n` which is `𝚷-[m]`.
- `𝚫-[m].Semiformula ξ n` is a pair of `𝚺-[m].Semiformula ξ n` and `𝚷-[m].Semiformula ξ n`.
- `ProperOn` : `φ.ProperOn M` iff `φ`'s two element `φ.sigma` and `φ.pi` are equivalent on model `M`.

-/


-- @@ L19-19 verbatim
namespace FFL.FirstOrder.Arithmetic


-- @@ L21-23 verbatim
structure HierarchySymbol where
  Γ : SigmaPiDelta
  rank : ℕ


-- @@ L25-25 verbatim
scoped notation:max Γ:max "-[" n "]" => HierarchySymbol.mk Γ n


-- @@ L27-27 expanded
abbrev HierarchySymbol.sigmaZero : HierarchySymbol :=
  SigmaSymbol.sigma-[0]


-- @@ L29-29 expanded
abbrev HierarchySymbol.piZero : HierarchySymbol :=
  PiSymbol.pi-[0]


-- @@ L31-31 expanded
abbrev HierarchySymbol.deltaZero : HierarchySymbol :=
  DeltaSymbol.delta-[0]


-- @@ L33-33 expanded
abbrev HierarchySymbol.sigmaOne : HierarchySymbol :=
  SigmaSymbol.sigma-[1]


-- @@ L35-35 expanded
abbrev HierarchySymbol.piOne : HierarchySymbol :=
  PiSymbol.pi-[1]


-- @@ L37-37 expanded
abbrev HierarchySymbol.deltaOne : HierarchySymbol :=
  DeltaSymbol.delta-[1]


-- @@ L39-39 verbatim
notation "𝚺₀" => HierarchySymbol.sigmaZero


-- @@ L41-41 verbatim
notation "𝚷₀" => HierarchySymbol.piZero


-- @@ L43-43 verbatim
notation "𝚫₀" => HierarchySymbol.deltaZero


-- @@ L45-45 verbatim
notation "𝚺₁" => HierarchySymbol.sigmaOne


-- @@ L47-47 verbatim
notation "𝚷₁" => HierarchySymbol.piOne


-- @@ L49-49 verbatim
notation "𝚫₁" => HierarchySymbol.deltaOne


-- @@ L51-51 verbatim
namespace HierarchySymbol


-- @@ L53-53 verbatim
variable (ξ : Type*) (n : ℕ)


-- @@ L55-58 expanded
protected inductive Semiformula : HierarchySymbol → Type _ where
  |
  mkSigma {m} (φ : ArithmeticSemiformula ξ n) (hφ : Hierarchy SigmaSymbol.sigma m φ := by simp) :
    SigmaSymbol.sigma-[m].Semiformula
  |
  mkPi {m} (φ : ArithmeticSemiformula ξ n) (hφ : Hierarchy PiSymbol.pi m φ := by simp) :
    PiSymbol.pi-[m].Semiformula
  |
  mkDelta {m} :
    SigmaSymbol.sigma-[m].Semiformula →
      PiSymbol.pi-[m].Semiformula → DeltaSymbol.delta-[m].Semiformula


-- @@ L60-60 verbatim
protected abbrev Semisentence (Γ : HierarchySymbol) (n : ℕ) := Γ.Semiformula Empty n


-- @@ L62-62 verbatim
protected abbrev Sentence (Γ : HierarchySymbol) := Γ.Semiformula Empty 0


-- @@ L64-64 verbatim
variable {Γ : HierarchySymbol}


-- @@ L66-66 verbatim
variable {ξ n}


-- @@ L68-68 verbatim
namespace Semiformula


-- @@ L70-73 verbatim
@[coe] def val {Γ : HierarchySymbol} : Γ.Semiformula ξ n → ArithmeticSemiformula ξ n
  | mkSigma φ _ => φ
  | mkPi    φ _ => φ
  | mkDelta φ _ => φ.val


-- @@ L75-75 expanded
@[simp]
lemma val_mkSigma (φ : ArithmeticSemiformula ξ n) (hp : Hierarchy SigmaSymbol.sigma m φ) :
    (mkSigma φ hp).val = φ :=
  rfl


-- @@ L77-77 expanded
@[simp]
lemma val_mkPi (φ : ArithmeticSemiformula ξ n) (hp : Hierarchy PiSymbol.pi m φ) :
    (mkPi φ hp).val = φ :=
  rfl


-- @@ L79-79 expanded
@[simp]
lemma val_mkDelta (φ : SigmaSymbol.sigma-[m].Semiformula ξ n)
    (ψ : PiSymbol.pi-[m].Semiformula ξ n) : (mkDelta φ ψ).val = φ.val :=
  rfl


-- @@ L81-81 expanded
instance : Coe (HierarchySymbol.sigmaZero.Semisentence n) (ArithmeticSemisentence n) :=
  ⟨Semiformula.val⟩


-- @@ L82-82 expanded
instance : Coe (HierarchySymbol.piZero.Semisentence n) (ArithmeticSemisentence n) :=
  ⟨Semiformula.val⟩


-- @@ L83-83 expanded
instance : Coe (HierarchySymbol.deltaZero.Semisentence n) (ArithmeticSemisentence n) :=
  ⟨Semiformula.val⟩


-- @@ L85-85 expanded
instance : Coe (HierarchySymbol.sigmaOne.Semisentence n) (ArithmeticSemisentence n) :=
  ⟨Semiformula.val⟩


-- @@ L86-86 expanded
instance : Coe (HierarchySymbol.piOne.Semisentence n) (ArithmeticSemisentence n) :=
  ⟨Semiformula.val⟩


-- @@ L87-87 expanded
instance : Coe (HierarchySymbol.deltaOne.Semisentence n) (ArithmeticSemisentence n) :=
  ⟨Semiformula.val⟩


-- @@ L89-90 expanded
@[simp]
lemma sigma_prop : (φ : SigmaSymbol.sigma-[m].Semiformula ξ n) → Hierarchy SigmaSymbol.sigma m φ.val
  | mkSigma _ h => h


-- @@ L92-93 expanded
@[simp]
lemma pi_prop : (φ : PiSymbol.pi-[m].Semiformula ξ n) → Hierarchy PiSymbol.pi m φ.val
  | mkPi _ h => h


-- @@ L95-97 expanded
@[simp]
lemma polarity_prop : {Γ : Polarity} → (φ : Γ-[m].Semiformula ξ n) → Hierarchy Γ m φ.val
  | SigmaSymbol.sigma, φ => φ.sigma_prop
  | PiSymbol.pi, φ => φ.pi_prop


-- @@ L99-100 expanded
def sigma : DeltaSymbol.delta-[m].Semiformula ξ n → SigmaSymbol.sigma-[m].Semiformula ξ n
  | mkDelta φ _ => φ


-- @@ L102-102 expanded
@[simp]
lemma sigma_mkDelta (φ : SigmaSymbol.sigma-[m].Semiformula ξ n)
    (ψ : PiSymbol.pi-[m].Semiformula ξ n) : (mkDelta φ ψ).sigma = φ :=
  rfl


-- @@ L104-105 expanded
def pi : DeltaSymbol.delta-[m].Semiformula ξ n → PiSymbol.pi-[m].Semiformula ξ n
  | mkDelta _ φ => φ


-- @@ L107-107 expanded
@[simp]
lemma pi_mkDelta (φ : SigmaSymbol.sigma-[m].Semiformula ξ n) (ψ : PiSymbol.pi-[m].Semiformula ξ n) :
    (mkDelta φ ψ).pi = ψ :=
  rfl


-- @@ L109-109 expanded
lemma val_sigma (φ : DeltaSymbol.delta-[m].Semiformula ξ n) : φ.sigma.val = φ.val := by rcases φ;
  simp


-- @@ L111-113 expanded
def mkPolarity (φ : ArithmeticSemiformula ξ n) :
    (Γ : Polarity) → Hierarchy Γ m φ → Γ-[m].Semiformula ξ n
  | SigmaSymbol.sigma, h => mkSigma φ h
  | PiSymbol.pi, h => mkPi φ h


-- @@ L115-115 verbatim
@[simp] lemma val_mkPolarity (φ : ArithmeticSemiformula ξ n) {Γ} (h : Hierarchy Γ m φ) : (mkPolarity φ Γ h).val = φ := by cases Γ <;> rfl


-- @@ L117-117 expanded
@[simp]
lemma hierarchy_sigma (φ : SigmaSymbol.sigma-[m].Semiformula ξ n) :
    Hierarchy SigmaSymbol.sigma m φ.val :=
  φ.sigma_prop


-- @@ L119-119 expanded
@[simp]
lemma hierarchy_pi (φ : PiSymbol.pi-[m].Semiformula ξ n) : Hierarchy PiSymbol.pi m φ.val :=
  φ.pi_prop


-- @@ L121-126 verbatim
@[simp] lemma hierarchy_zero {Γ Γ' m} (φ : Γ-[0].Semiformula ξ n) : Hierarchy Γ' m φ.val := by
  cases Γ
  · exact Hierarchy.of_zero φ.sigma_prop
  · exact Hierarchy.of_zero φ.pi_prop
  · cases φ
    simpa using Hierarchy.of_zero (sigma_prop _)


-- @@ L128-128 verbatim
variable {M : Type*} [ORingStructure M]


-- @@ L130-130 verbatim
variable (M)


-- @@ L132-133 expanded
def ProperOn (φ : DeltaSymbol.delta-[m].Semisentence n) : Prop :=
  ∀ (e : Fin n → M), φ.sigma.val.Evalb e ↔ φ.pi.val.Evalb e


-- @@ L135-136 expanded
def ProperWithParamOn (φ : DeltaSymbol.delta-[m].Semiformula M n) : Prop :=
  ∀ (e : Fin n → M), φ.sigma.val.Eval e id ↔ φ.pi.val.Eval e id


-- @@ L138-139 expanded
def ProvablyProperOn (φ : DeltaSymbol.delta-[m].Semisentence n) (T : ArithmeticTheory) : Prop :=
  Provable T
    (allClosure
      (LogicalConnective.iff (FFL.FirstOrder.Rewriting.subst φ.sigma.val fun x ↦ #(finSuccItr x 0))
        (FFL.FirstOrder.Rewriting.subst φ.pi.val fun x ↦ #(finSuccItr x 0))))


-- @@ L141-141 verbatim
variable {M}


-- @@ L143-145 expanded
lemma ProperOn.iff {φ : DeltaSymbol.delta-[m].Semisentence n} (h : φ.ProperOn M) (e : Fin n → M) :
    φ.sigma.val.Evalb e ↔ φ.pi.val.Evalb e :=
  h e


-- @@ L147-149 expanded
lemma ProperWithParamOn.iff {φ : DeltaSymbol.delta-[m].Semiformula M n} (h : φ.ProperWithParamOn M)
    (e : Fin n → M) : φ.sigma.val.Eval e id ↔ φ.pi.val.Eval e id :=
  h e


-- @@ L151-153 expanded
lemma ProperOn.iff' {φ : DeltaSymbol.delta-[m].Semisentence n} (h : φ.ProperOn M) (e : Fin n → M) :
    φ.pi.val.Evalb e ↔ φ.val.Evalb e := by simp [← h.iff, val_sigma]


-- @@ L155-157 expanded
lemma ProperWithParamOn.iff' {φ : DeltaSymbol.delta-[m].Semiformula M n} (h : φ.ProperWithParamOn M)
    (e : Fin n → M) : φ.pi.val.Eval e id ↔ φ.val.Eval e id := by simp [← h.iff, val_sigma]


-- @@ L159-162 expanded
inductive ProvablyProperOn' (T : ArithmeticTheory) :
    {Γ : HierarchySymbol} → {n : ℕ} → (φ : Γ.Semisentence n) → Prop
  | sigma (φ : SigmaSymbol.sigma-[m].Semisentence n) : φ.ProvablyProperOn' T
  | pi (φ : PiSymbol.pi-[m].Semisentence n) : φ.ProvablyProperOn' T
  | delta (φ : DeltaSymbol.delta-[m].Semisentence n) : φ.ProvablyProperOn T → φ.ProvablyProperOn' T


-- @@ L164-164 verbatim
section ProvablyProperOn


-- @@ L166-166 verbatim
variable (T : ArithmeticTheory)


-- @@ L168-172 expanded
lemma ProvablyProperOn.ofProperOn [WeakerThan (eqAxiom oRing) T]
    {φ : DeltaSymbol.delta-[m].Semisentence n}
    (h : ∀ (M : Type w) [ORingStructure M] [ModelsSet (Language.str M oRing) T], φ.ProperOn M) :
    φ.ProvablyProperOn T :=
  by
  apply FirstOrder.Arithmetic.complete.{w} T _ ?_
  intro M _ _
  simpa [models_iff] using! (h M).iff


-- @@ L174-174 verbatim
variable {T}


-- @@ L176-181 expanded
lemma ProvablyProperOn.properOn {φ : DeltaSymbol.delta-[m].Semisentence n}
    (h : φ.ProvablyProperOn T) (M : Type w) [ORingStructure M]
    [ModelsSet (Language.str M oRing) T] : φ.ProperOn M :=
  by
  intro v
  have := by simpa [models_iff] using consequence_iff.mp (Theory.Proof.sound h) M inferInstance
  exact this v


-- @@ L183-183 verbatim
end ProvablyProperOn


-- @@ L185-188 expanded
def rew (ω : Rew oRing ξ₁ n₁ ξ₂ n₂) :
    {Γ : HierarchySymbol} → Γ.Semiformula ξ₁ n₁ → Γ.Semiformula ξ₂ n₂
  | SigmaSymbol.sigma-[_], mkSigma φ hp => mkSigma (app ω φ) (by simpa using hp)
  | PiSymbol.pi-[_], mkPi φ hp => mkPi (app ω φ) (by simpa using hp)
  | DeltaSymbol.delta-[_], mkDelta φ ψ => mkDelta (φ.rew ω) (ψ.rew ω)


-- @@ L190-191 expanded
@[simp]
lemma val_rew (ω : Rew oRing ξ₁ n₁ ξ₂ n₂) {Γ : HierarchySymbol} (φ : Γ.Semiformula ξ₁ n₁) :
    (φ.rew ω).val = app ω φ.val := by rcases Γ with ⟨Γ, m⟩;
  rcases φ with (_ | _ | ⟨⟨p, _⟩, ⟨q, _⟩⟩) <;> simp [rew]


-- @@ L193-195 expanded
@[simp]
lemma ProperOn.rew {φ : DeltaSymbol.delta-[m].Semisentence n₁} (h : φ.ProperOn M)
    (ω : Rew oRing Empty n₁ Empty n₂) : (φ.rew ω).ProperOn M :=
  by
  rcases φ;
  simp only [ProperOn, Semiformula.rew, sigma_mkDelta, val_rew, Semiformula.eval_rew, Empty.eq_elim,
    pi_mkDelta]
  intro e; exact h.iff _


-- @@ L197-199 expanded
@[simp]
lemma ProperOn.rew' {φ : DeltaSymbol.delta-[m].Semisentence n₁} (h : φ.ProperOn M)
    (ω : Rew oRing Empty n₁ M n₂) : (φ.rew ω).ProperWithParamOn M :=
  by
  rcases φ; intro e; simp [Semiformula.rew, Semiformula.eval_rew, Empty.eq_elim]
  simpa using h.iff _


-- @@ L201-205 expanded
@[simp]
lemma ProperWithParamOn.rew {φ : DeltaSymbol.delta-[m].Semiformula M n₁} (h : φ.ProperWithParamOn M)
    (f : Fin n₁ → ArithmeticSemiterm M n₂) : (φ.rew (Rew.subst f)).ProperWithParamOn M :=
  by
  rcases φ; intro e;
  simp only [Semiformula.rew, sigma_mkDelta, val_rew, Semiformula.eval_rew, pi_mkDelta]
  exact h.iff _


-- @@ L207-211 expanded
lemma sigmaZero {Γ} (φ : Γ-[0].Semiformula ξ k) : Hierarchy SigmaSymbol.sigma 0 φ.val :=
  match Γ with
  | SigmaSymbol.sigma => φ.sigma_prop
  | PiSymbol.pi => φ.pi_prop.of_zero
  | DeltaSymbol.delta => by simp


-- @@ L213-216 expanded
def ofZero {Γ'} (φ : Γ'-[0].Semiformula ξ k) : (Γ : HierarchySymbol) → Γ.Semiformula ξ k
  | SigmaSymbol.sigma-[_] => mkSigma φ.val φ.sigmaZero.of_zero
  | PiSymbol.pi-[_] => mkPi φ.val φ.sigmaZero.of_zero
  | DeltaSymbol.delta-[_] =>
    mkDelta (mkSigma φ.val φ.sigmaZero.of_zero) (mkPi φ.val φ.sigmaZero.of_zero)


-- @@ L218-221 expanded
def ofDeltaOne (φ : HierarchySymbol.deltaOne.Semiformula ξ k) :
    (Γ : SigmaPiDelta) → (m : ℕ) → Γ-[m + 1].Semiformula ξ k
  | SigmaSymbol.sigma, m => mkSigma φ.sigma.val (φ.sigma.sigma_prop.mono (by simp))
  | PiSymbol.pi, m => mkPi φ.pi.val (φ.pi.pi_prop.mono (by simp))
  | DeltaSymbol.delta, m =>
    mkDelta (mkSigma φ.sigma.val (φ.sigma.sigma_prop.mono (by simp)))
      (mkPi φ.pi.val (φ.pi.pi_prop.mono (by simp)))


-- @@ L223-227 expanded
@[simp]
lemma ofZero_val {Γ'} (φ : Γ'-[0].Semiformula ξ n) (Γ) : (ofZero φ Γ).val = φ.val := by
  match Γ with
  | SigmaSymbol.sigma-[_] => simp [ofZero]
  | PiSymbol.pi-[_] => simp [ofZero]
  | DeltaSymbol.delta-[_] => simp [ofZero]


-- @@ L229-230 expanded
@[simp]
lemma ProperOn.of_zero (φ : Γ'-[0].Semisentence k) (m) :
    (ofZero φ DeltaSymbol.delta-[m]).ProperOn M := by simp [ProperOn, ofZero]


-- @@ L232-233 expanded
@[simp]
lemma ProperWithParamOn.of_zero (φ : Γ'-[0].Semiformula M k) (m) :
    (ofZero φ DeltaSymbol.delta-[m]).ProperWithParamOn M := by simp [ProperWithParamOn, ofZero]


-- @@ L235-238 expanded
def verum : {Γ : HierarchySymbol} → Γ.Semiformula ξ n
  | SigmaSymbol.sigma-[m] => mkSigma ⊤ (by simp)
  | PiSymbol.pi-[m] => mkPi ⊤ (by simp)
  | DeltaSymbol.delta-[m] => mkDelta (mkSigma ⊤ (by simp)) (mkPi ⊤ (by simp))


-- @@ L240-243 expanded
def falsum : {Γ : HierarchySymbol} → Γ.Semiformula ξ n
  | SigmaSymbol.sigma-[m] => mkSigma ⊥ (by simp)
  | PiSymbol.pi-[m] => mkPi ⊥ (by simp)
  | DeltaSymbol.delta-[m] => mkDelta (mkSigma ⊥ (by simp)) (mkPi ⊥ (by simp))


-- @@ L245-248 expanded
def and : {Γ : HierarchySymbol} → Γ.Semiformula ξ n → Γ.Semiformula ξ n → Γ.Semiformula ξ n
  | SigmaSymbol.sigma-[m], φ, ψ => mkSigma (binop% HWedge.hWedge φ.val ψ.val) (by simp)
  | PiSymbol.pi-[m], φ, ψ => mkPi (binop% HWedge.hWedge φ.val ψ.val) (by simp)
  | DeltaSymbol.delta-[m], φ, ψ =>
    mkDelta (mkSigma (binop% HWedge.hWedge φ.sigma.val ψ.sigma.val) (by simp))
      (mkPi (binop% HWedge.hWedge φ.pi.val ψ.pi.val) (by simp))


-- @@ L250-253 expanded
def or : {Γ : HierarchySymbol} → Γ.Semiformula ξ n → Γ.Semiformula ξ n → Γ.Semiformula ξ n
  | SigmaSymbol.sigma-[m], φ, ψ => mkSigma (binop% HVee.hVee φ.val ψ.val) (by simp)
  | PiSymbol.pi-[m], φ, ψ => mkPi (binop% HVee.hVee φ.val ψ.val) (by simp)
  | DeltaSymbol.delta-[m], φ, ψ =>
    mkDelta (mkSigma (binop% HVee.hVee φ.sigma.val ψ.sigma.val) (by simp))
      (mkPi (binop% HVee.hVee φ.pi.val ψ.pi.val) (by simp))


-- @@ L255-255 expanded
def negSigma (φ : SigmaSymbol.sigma-[m].Semiformula ξ n) : PiSymbol.pi-[m].Semiformula ξ n :=
  mkPi (unop% HTilde.hTilde φ.val) (by simp)


-- @@ L257-257 expanded
def negPi (φ : PiSymbol.pi-[m].Semiformula ξ n) : SigmaSymbol.sigma-[m].Semiformula ξ n :=
  mkSigma (unop% HTilde.hTilde φ.val) (by simp)


-- @@ L259-259 expanded
def negDelta (φ : DeltaSymbol.delta-[m].Semiformula ξ n) : DeltaSymbol.delta-[m].Semiformula ξ n :=
  mkDelta (φ.pi.negPi) (φ.sigma.negSigma)


-- @@ L261-265 expanded
def ball (t : ArithmeticSemiterm ξ n) :
    {Γ : HierarchySymbol} → Γ.Semiformula ξ (n + 1) → Γ.Semiformula ξ n
  | SigmaSymbol.sigma-[m], φ =>
    mkSigma (ball (Semiformula.Operator.operator Operator.LT.lt ![#0, (Rew.bShift t)]) φ.val)
      (by simp)
  | PiSymbol.pi-[m], φ =>
    mkPi (ball (Semiformula.Operator.operator Operator.LT.lt ![#0, (Rew.bShift t)]) φ.val) (by simp)
  | DeltaSymbol.delta-[m], φ =>
    mkDelta
      (mkSigma
        (ball (Semiformula.Operator.operator Operator.LT.lt ![#0, (Rew.bShift t)]) φ.sigma.val)
        (by simp))
      (mkPi (ball (Semiformula.Operator.operator Operator.LT.lt ![#0, (Rew.bShift t)]) φ.pi.val)
        (by simp))


-- @@ L267-271 expanded
def bexs (t : ArithmeticSemiterm ξ n) :
    {Γ : HierarchySymbol} → Γ.Semiformula ξ (n + 1) → Γ.Semiformula ξ n
  | SigmaSymbol.sigma-[m], φ =>
    mkSigma (bexs (Semiformula.Operator.operator Operator.LT.lt ![#0, (Rew.bShift t)]) φ.val)
      (by simp)
  | PiSymbol.pi-[m], φ =>
    mkPi (bexs (Semiformula.Operator.operator Operator.LT.lt ![#0, (Rew.bShift t)]) φ.val) (by simp)
  | DeltaSymbol.delta-[m], φ =>
    mkDelta
      (mkSigma
        (bexs (Semiformula.Operator.operator Operator.LT.lt ![#0, (Rew.bShift t)]) φ.sigma.val)
        (by simp))
      (mkPi (bexs (Semiformula.Operator.operator Operator.LT.lt ![#0, (Rew.bShift t)]) φ.pi.val)
        (by simp))


-- @@ L273-273 expanded
def all (φ : PiSymbol.pi-[m + 1].Semiformula ξ (n + 1)) : PiSymbol.pi-[m + 1].Semiformula ξ n :=
  mkPi (UnivQuantifier.all φ.val) φ.pi_prop.all


-- @@ L275-275 expanded
def exs (φ : SigmaSymbol.sigma-[m + 1].Semiformula ξ (n + 1)) :
    SigmaSymbol.sigma-[m + 1].Semiformula ξ n :=
  mkSigma (ExsQuantifier.exs φ.val) φ.sigma_prop.exs


-- @@ L277-277 verbatim
instance : Top (Γ.Semiformula ξ n) := ⟨verum⟩


-- @@ L279-279 verbatim
instance : Bot (Γ.Semiformula ξ n) := ⟨falsum⟩


-- @@ L281-281 verbatim
instance : Wedge (Γ.Semiformula ξ n) := ⟨and⟩


-- @@ L283-283 verbatim
instance : Vee (Γ.Semiformula ξ n) := ⟨or⟩


-- @@ L285-285 expanded
instance : Tilde (DeltaSymbol.delta-[m].Semiformula ξ n) :=
  ⟨negDelta⟩


-- @@ L287-288 expanded
instance : LogicalConnective (DeltaSymbol.delta-[m].Semiformula ξ n) where
  arrow φ ψ := binop% HVee.hVee (unop% HTilde.hTilde φ) ψ


-- @@ L290-290 expanded
instance : ExsQuantifier (SigmaSymbol.sigma-[m + 1].Semiformula ξ) :=
  ⟨exs⟩


-- @@ L292-292 expanded
instance : UnivQuantifier (PiSymbol.pi-[m + 1].Semiformula ξ) :=
  ⟨all⟩


-- @@ L294-295 expanded
def substSigma (φ : SigmaSymbol.sigma-[m + 1].Semiformula ξ 1)
    (F : SigmaSymbol.sigma-[m + 1].Semiformula ξ (n + 1)) :
    SigmaSymbol.sigma-[m + 1].Semiformula ξ n :=
  (binop% HWedge.hWedge F (φ.rew (Rew.subst ![#0]))).exs


-- @@ L297-298 verbatim
@[simp] lemma val_verum : (⊤ : Γ.Semiformula ξ n).val = ⊤ := by
  rcases Γ with ⟨Γ, m⟩; rcases Γ <;> simp <;> rfl


-- @@ L300-300 expanded
@[simp]
lemma sigma_verum {m} : (⊤ : DeltaSymbol.delta-[m].Semiformula ξ n).sigma = ⊤ := by
  simp [Top.top, verum]


-- @@ L302-302 expanded
@[simp]
lemma pi_verum {m} : (⊤ : DeltaSymbol.delta-[m].Semiformula ξ n).pi = ⊤ := by simp [Top.top, verum]


-- @@ L304-305 verbatim
@[simp] lemma val_falsum : (⊥ : Γ.Semiformula ξ n).val = ⊥ := by
  rcases Γ with ⟨Γ, m⟩; rcases Γ <;> simp <;> rfl


-- @@ L307-307 expanded
@[simp]
lemma sigma_falsum {m} : (⊥ : DeltaSymbol.delta-[m].Semiformula ξ n).sigma = ⊥ := by
  simp [Bot.bot, falsum]


-- @@ L309-309 expanded
@[simp]
lemma pi_falsum {m} : (⊥ : DeltaSymbol.delta-[m].Semiformula ξ n).pi = ⊥ := by
  simp [Bot.bot, falsum]


-- @@ L311-313 expanded
@[simp]
lemma val_and (φ ψ : Γ.Semiformula ξ n) :
    (binop% HWedge.hWedge φ ψ).val = binop% HWedge.hWedge φ.val ψ.val :=
  by
  suffices (φ.and ψ).val = binop% HWedge.hWedge φ.val ψ.val from this
  rcases Γ with ⟨Γ, m⟩; rcases Γ <;> simp [and, val, val_sigma]


-- @@ L315-315 expanded
@[simp]
lemma sigma_and (φ ψ : DeltaSymbol.delta-[m].Semiformula ξ n) :
    (binop% HWedge.hWedge φ ψ).sigma = binop% HWedge.hWedge φ.sigma ψ.sigma :=
  rfl


-- @@ L317-317 expanded
@[simp]
lemma pi_and (φ ψ : DeltaSymbol.delta-[m].Semiformula ξ n) :
    (binop% HWedge.hWedge φ ψ).pi = binop% HWedge.hWedge φ.pi ψ.pi :=
  rfl


-- @@ L319-321 expanded
@[simp]
lemma val_or (φ ψ : Γ.Semiformula ξ n) :
    (binop% HVee.hVee φ ψ).val = binop% HVee.hVee φ.val ψ.val :=
  by
  suffices (φ.or ψ).val = binop% HVee.hVee φ.val ψ.val from this
  rcases Γ with ⟨Γ, m⟩; rcases Γ <;> simp [or, val, val_sigma]


-- @@ L323-323 expanded
@[simp]
lemma sigma_or (φ ψ : DeltaSymbol.delta-[m].Semiformula ξ n) :
    (binop% HVee.hVee φ ψ).sigma = binop% HVee.hVee φ.sigma ψ.sigma :=
  rfl


-- @@ L325-325 expanded
@[simp]
lemma pi_or (φ ψ : DeltaSymbol.delta-[m].Semiformula ξ n) :
    (binop% HVee.hVee φ ψ).pi = binop% HVee.hVee φ.pi ψ.pi :=
  rfl


-- @@ L327-327 expanded
@[simp]
lemma val_negSigma {m} (φ : SigmaSymbol.sigma-[m].Semiformula ξ n) :
    φ.negSigma.val = unop% HTilde.hTilde φ.val := by simp [negSigma]


-- @@ L329-329 expanded
@[simp]
lemma val_negPi {m} (φ : PiSymbol.pi-[m].Semiformula ξ n) :
    φ.negPi.val = unop% HTilde.hTilde φ.val := by simp [negPi]


-- @@ L331-331 expanded
lemma val_negDelta {m} (φ : DeltaSymbol.delta-[m].Semiformula ξ n) :
    (unop% HTilde.hTilde φ).val = unop% HTilde.hTilde φ.pi.val := by
  simp [HTilde.hTilde, Tilde.tilde, negDelta]


-- @@ L333-333 expanded
@[simp]
lemma sigma_negDelta {m} (φ : DeltaSymbol.delta-[m].Semiformula ξ n) :
    (unop% HTilde.hTilde φ).sigma = φ.pi.negPi := by simp [HTilde.hTilde, Tilde.tilde, negDelta]


-- @@ L335-335 expanded
@[simp]
lemma sigma_negPi {m} (φ : DeltaSymbol.delta-[m].Semiformula ξ n) :
    (unop% HTilde.hTilde φ).pi = φ.sigma.negSigma := by simp [HTilde.hTilde, Tilde.tilde, negDelta]


-- @@ L337-338 expanded
@[simp]
lemma val_ball (t : ArithmeticSemiterm ξ n) (φ : Γ.Semiformula ξ (n + 1)) :
    (ball t φ).val =
      ball (Semiformula.Operator.operator Operator.LT.lt ![#0, (Rew.bShift t)]) φ.val :=
  by rcases Γ with ⟨Γ, m⟩; rcases Γ <;> simp [ball, val, val_sigma]


-- @@ L340-341 expanded
@[simp]
lemma val_bexs (t : ArithmeticSemiterm ξ n) (φ : Γ.Semiformula ξ (n + 1)) :
    (bexs t φ).val =
      bexs (Semiformula.Operator.operator Operator.LT.lt ![#0, (Rew.bShift t)]) φ.val :=
  by rcases Γ with ⟨Γ, m⟩; rcases Γ <;> simp [bexs, val, val_sigma]


-- @@ L343-343 expanded
@[simp]
lemma val_exsSigma {m} (φ : SigmaSymbol.sigma-[m + 1].Semiformula ξ (n + 1)) :
    (exs φ).val = ExsQuantifier.exs φ.val :=
  rfl


-- @@ L345-345 expanded
@[simp]
lemma val_allPi {m} (φ : PiSymbol.pi-[m + 1].Semiformula ξ (n + 1)) :
    (all φ).val = UnivQuantifier.all φ.val :=
  rfl


-- @@ L347-347 expanded
@[simp]
lemma ProperOn.verum : (⊤ : DeltaSymbol.delta-[m].Semisentence k).ProperOn M := by intro e; simp


-- @@ L349-349 expanded
@[simp]
lemma ProperOn.falsum : (⊥ : DeltaSymbol.delta-[m].Semisentence k).ProperOn M := by intro e; simp


-- @@ L351-352 expanded
lemma ProperOn.and {φ ψ : DeltaSymbol.delta-[m].Semisentence k} (hp : φ.ProperOn M)
    (hq : ψ.ProperOn M) : (binop% HWedge.hWedge φ ψ).ProperOn M := by intro e; simp [hp.iff, hq.iff]


-- @@ L354-355 expanded
lemma ProperOn.or {φ ψ : DeltaSymbol.delta-[m].Semisentence k} (hp : φ.ProperOn M)
    (hq : ψ.ProperOn M) : (binop% HVee.hVee φ ψ).ProperOn M := by intro e; simp [hp.iff, hq.iff]


-- @@ L357-358 expanded
lemma ProperOn.neg {φ : DeltaSymbol.delta-[m].Semisentence k} (hp : φ.ProperOn M) :
    (unop% HTilde.hTilde φ).ProperOn M := by intro e; simp [hp.iff]


-- @@ L360-362 expanded
lemma ProperOn.eval_neg {φ : DeltaSymbol.delta-[m].Semisentence k} (hp : φ.ProperOn M)
    (e : Fin k → M) : (unop% HTilde.hTilde φ).val.Evalb e ↔ ¬φ.val.Evalb e := by
  simp [← val_sigma, hp.iff]


-- @@ L364-365 expanded
lemma ProperOn.ball {t} {φ : DeltaSymbol.delta-[m + 1].Semisentence (k + 1)} (hp : φ.ProperOn M) :
    (ball t φ).ProperOn M := by intro e; simp [Semiformula.ball, hp.iff]


-- @@ L367-368 expanded
lemma ProperOn.bexs {t} {φ : DeltaSymbol.delta-[m + 1].Semisentence (k + 1)} (hp : φ.ProperOn M) :
    (bexs t φ).ProperOn M := by intro e; simp [Semiformula.bexs, hp.iff]


-- @@ L370-370 expanded
@[simp]
lemma ProperWithParamOn.verum : (⊤ : DeltaSymbol.delta-[m].Semiformula M k).ProperWithParamOn M :=
  by intro e; simp


-- @@ L372-372 expanded
@[simp]
lemma ProperWithParamOn.falsum : (⊥ : DeltaSymbol.delta-[m].Semiformula M k).ProperWithParamOn M :=
  by intro e; simp


-- @@ L374-376 expanded
lemma ProperWithParamOn.and {φ ψ : DeltaSymbol.delta-[m].Semiformula M k}
    (hp : φ.ProperWithParamOn M) (hq : ψ.ProperWithParamOn M) :
    (binop% HWedge.hWedge φ ψ).ProperWithParamOn M := by intro e; simp [hp.iff, hq.iff]


-- @@ L378-380 expanded
lemma ProperWithParamOn.or {φ ψ : DeltaSymbol.delta-[m].Semiformula M k}
    (hp : φ.ProperWithParamOn M) (hq : ψ.ProperWithParamOn M) :
    (binop% HVee.hVee φ ψ).ProperWithParamOn M := by intro e; simp [hp.iff, hq.iff]


-- @@ L382-383 expanded
lemma ProperWithParamOn.neg {φ : DeltaSymbol.delta-[m].Semiformula M k}
    (hp : φ.ProperWithParamOn M) : (unop% HTilde.hTilde φ).ProperWithParamOn M := by intro e;
  simp [hp.iff]


-- @@ L385-387 expanded
lemma ProperWithParamOn.eval_neg {φ : DeltaSymbol.delta-[m].Semiformula M k}
    (hp : φ.ProperWithParamOn M) (e : Fin k → M) :
    (unop% HTilde.hTilde φ).val.Eval e id ↔ ¬φ.val.Eval e id := by simp [← val_sigma, hp.iff]


-- @@ L389-391 expanded
lemma ProperWithParamOn.ball {t} {φ : DeltaSymbol.delta-[m].Semiformula M (k + 1)}
    (hp : φ.ProperWithParamOn M) : (ball t φ).ProperWithParamOn M := by intro e;
  simp [Semiformula.ball, hp.iff]


-- @@ L393-395 expanded
lemma ProperWithParamOn.bexs {t} {φ : DeltaSymbol.delta-[m].Semiformula M (k + 1)}
    (hp : φ.ProperWithParamOn M) : (bexs t φ).ProperWithParamOn M := by intro e;
  simp [Semiformula.bexs, hp.iff]


-- @@ L397-400 expanded
def graphDelta (φ : SigmaSymbol.sigma-[m].Semiformula ξ (k + 1)) :
    DeltaSymbol.delta-[m].Semiformula ξ (k + 1) :=
  match m with
  | 0 => φ.ofZero _
  | m + 1 =>
    mkDelta φ
      (mkPi
        (UnivQuantifier.all
          (@HArrow.hArrow _ _ _ Arrow.instHArrow
            (FFL.FirstOrder.Rewriting.subst φ.val (vecCons #0 fun x ↦ #(finSuccItr x 2)))
            (Semiformula.Operator.operator Operator.Eq.eq ![#0, #1]))))


-- @@ L402-402 expanded
@[simp]
lemma graphDelta_val (φ : SigmaSymbol.sigma-[m].Semiformula ξ (k + 1)) : φ.graphDelta.val = φ.val :=
  by cases m <;> simp [graphDelta]


-- @@ L404-404 verbatim
end Semiformula


-- @@ L406-406 verbatim
end HierarchySymbol


-- @@ L408-408 verbatim
end FFL.FirstOrder.Arithmetic
