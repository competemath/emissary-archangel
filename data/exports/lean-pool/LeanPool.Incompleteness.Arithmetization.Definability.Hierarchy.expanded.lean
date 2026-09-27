/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Arithmetization.Vorspiel.Lemmata
public import LeanPool.Incompleteness.Arithmetization.Vorspiel.Vorspiel
import LeanPool.Incompleteness.Foundation.FirstOrder.Basic.Soundness
import LeanPool.Incompleteness.Foundation.FirstOrder.Completeness.Completeness


-- @@ L13-25 verbatim
/-!

# Arithmetical Formula Sorted by Arithmetical Hierarchy

This file defines the $\Sigma_n / \Pi_n / \Delta_n$ formulas of arithmetic of first-order logic.

- `Sg-[m].Semiformula ξ n` is a `Semiformula ℒₒᵣ ξ n` which is `Sg-[m]`.
- `Pg-[m].Semiformula ξ n` is a `Semiformula ℒₒᵣ ξ n` which is `Pg-[m]`.
- `Dlt-[m].Semiformula ξ n` is a pair of `Sg-[m].Semiformula ξ n` and `Pg-[m].Semiformula ξ n`.
- `ProperOn` : `φ.ProperOn M` iff `φ`'s two element `φ.sigma` and `φ.pi` are equivalent on model
  `M`.

-/


-- @@ L27-27 verbatim
@[expose] public section


-- @@ L29-29 verbatim
namespace LO

-- @@ L30-30 verbatim
namespace FirstOrder

-- @@ L31-31 verbatim
namespace Arith


-- @@ L33-38 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
structure HierarchySymbol where
  /-- Imported declaration from the Incompleteness formalization. -/
  Γ : SigmaPiDelta
  /-- Imported declaration from the Incompleteness formalization. -/
  rank : ℕ


-- @@ L40-41 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
scoped notation:max Γ:max "-[" n "]" => HierarchySymbol.mk Γ n


-- @@ L43-44 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Arith.HierarchySymbol.sigmaZero : HierarchySymbol :=
  SigmaSymbol.sigma-[0]


-- @@ L46-47 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Arith.HierarchySymbol.piZero : HierarchySymbol :=
  PiSymbol.pi-[0]


-- @@ L49-50 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Arith.HierarchySymbol.deltaZero : HierarchySymbol :=
  DeltaSymbol.delta-[0]


-- @@ L52-53 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Arith.HierarchySymbol.sigmaOne : HierarchySymbol :=
  SigmaSymbol.sigma-[1]


-- @@ L55-56 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Arith.HierarchySymbol.piOne : HierarchySymbol :=
  PiSymbol.pi-[1]


-- @@ L58-59 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Arith.HierarchySymbol.deltaOne : HierarchySymbol :=
  DeltaSymbol.delta-[1]


-- @@ L61-62 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev Sg0 : HierarchySymbol := HierarchySymbol.sigmaZero


-- @@ L64-65 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev Pg0 : HierarchySymbol := HierarchySymbol.piZero


-- @@ L67-68 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev Dlt0 : HierarchySymbol := HierarchySymbol.deltaZero


-- @@ L70-71 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev Sg1 : HierarchySymbol := HierarchySymbol.sigmaOne


-- @@ L73-74 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev Pg1 : HierarchySymbol := HierarchySymbol.piOne


-- @@ L76-77 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev Dlt1 : HierarchySymbol := HierarchySymbol.deltaOne


-- @@ L79-79 verbatim
namespace HierarchySymbol


-- @@ L81-81 verbatim
variable (ξ : Type*) (n : ℕ)


-- @@ L83-87 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected inductive Semiformula : HierarchySymbol → Type _ where
  |
  mkSigma {m} :
    (φ : Semiformula oRing ξ n) →
      Hierarchy SigmaSymbol.sigma m φ → SigmaSymbol.sigma-[m].Semiformula
  | mkPi {m} : (φ : Semiformula oRing ξ n) → Hierarchy PiSymbol.pi m φ → PiSymbol.pi-[m].Semiformula
  |
  mkDelta {m} :
    SigmaSymbol.sigma-[m].Semiformula →
      PiSymbol.pi-[m].Semiformula → DeltaSymbol.delta-[m].Semiformula


-- @@ L89-90 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Semisentence (Γ : HierarchySymbol) (n : ℕ) := Γ.Semiformula Empty n


-- @@ L92-93 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Sentence (Γ : HierarchySymbol) := Γ.Semiformula Empty 0


-- @@ L95-95 verbatim
variable {Γ : HierarchySymbol}


-- @@ L97-97 verbatim
variable {ξ n}


-- @@ L99-99 verbatim
namespace Semiformula


-- @@ L101-105 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def val {Γ : HierarchySymbol} : Γ.Semiformula ξ n → Semiformula oRing ξ n
  | mkSigma φ _ => φ
  | mkPi φ _ => φ
  | mkDelta φ _ => φ.val


-- @@ L107-109 expanded
@[simp]
lemma val_mkSigma (φ : Semiformula oRing ξ n) (hp : Hierarchy SigmaSymbol.sigma m φ) :
    (mkSigma φ hp).val = φ :=
  rfl


-- @@ L111-113 expanded
@[simp]
lemma val_mkPi (φ : Semiformula oRing ξ n) (hp : Hierarchy PiSymbol.pi m φ) : (mkPi φ hp).val = φ :=
  rfl


-- @@ L115-117 expanded
@[simp]
lemma val_mkDelta (φ : SigmaSymbol.sigma-[m].Semiformula ξ n)
    (ψ : PiSymbol.pi-[m].Semiformula ξ n) : (mkDelta φ ψ).val = φ.val :=
  rfl


-- @@ L119-119 expanded
instance : Coe (Sg0.Semisentence n) (Semisentence oRing n) :=
  ⟨Semiformula.val⟩


-- @@ L120-120 expanded
instance : Coe (Pg0.Semisentence n) (Semisentence oRing n) :=
  ⟨Semiformula.val⟩


-- @@ L121-121 expanded
instance : Coe (Dlt0.Semisentence n) (Semisentence oRing n) :=
  ⟨Semiformula.val⟩


-- @@ L123-123 expanded
instance : Coe (Sg1.Semisentence n) (Semisentence oRing n) :=
  ⟨Semiformula.val⟩


-- @@ L124-124 expanded
instance : Coe (Pg1.Semisentence n) (Semisentence oRing n) :=
  ⟨Semiformula.val⟩


-- @@ L125-125 expanded
instance : Coe (Dlt1.Semisentence n) (Semisentence oRing n) :=
  ⟨Semiformula.val⟩


-- @@ L127-128 expanded
lemma sigma_prop : (φ : SigmaSymbol.sigma-[m].Semiformula ξ n) → Hierarchy SigmaSymbol.sigma m φ.val
  | mkSigma _ h => h


-- @@ L130-131 expanded
lemma pi_prop : (φ : PiSymbol.pi-[m].Semiformula ξ n) → Hierarchy PiSymbol.pi m φ.val
  | mkPi _ h => h


-- @@ L133-135 expanded
@[simp]
lemma polarity_prop : {Γ : Polarity} → (φ : Γ-[m].Semiformula ξ n) → Hierarchy Γ m φ.val
  | SigmaSymbol.sigma, φ => φ.sigma_prop
  | PiSymbol.pi, φ => φ.pi_prop


-- @@ L137-139 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def sigma : DeltaSymbol.delta-[m].Semiformula ξ n → SigmaSymbol.sigma-[m].Semiformula ξ n
  | mkDelta φ _ => φ


-- @@ L141-143 expanded
@[simp]
lemma sigma_mkDelta (φ : SigmaSymbol.sigma-[m].Semiformula ξ n)
    (ψ : PiSymbol.pi-[m].Semiformula ξ n) : (mkDelta φ ψ).sigma = φ :=
  rfl


-- @@ L145-147 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def pi : DeltaSymbol.delta-[m].Semiformula ξ n → PiSymbol.pi-[m].Semiformula ξ n
  | mkDelta _ φ => φ


-- @@ L149-151 expanded
@[simp]
lemma pi_mkDelta (φ : SigmaSymbol.sigma-[m].Semiformula ξ n) (ψ : PiSymbol.pi-[m].Semiformula ξ n) :
    (mkDelta φ ψ).pi = ψ :=
  rfl


-- @@ L153-153 expanded
lemma val_sigma (φ : DeltaSymbol.delta-[m].Semiformula ξ n) : φ.sigma.val = φ.val := by rcases φ;
  simp


-- @@ L155-158 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def mkPolarity (φ : Semiformula oRing ξ n) :
    (Γ : Polarity) → Hierarchy Γ m φ → Γ-[m].Semiformula ξ n
  | SigmaSymbol.sigma, h => mkSigma φ h
  | PiSymbol.pi, h => mkPi φ h


-- @@ L160-161 expanded
@[simp]
lemma val_mkPolarity (φ : Semiformula oRing ξ n) {Γ} (h : Hierarchy Γ m φ) :
    (mkPolarity φ Γ h).val = φ := by cases Γ <;> rfl


-- @@ L163-163 expanded
@[simp]
lemma hierarchy_sigma (φ : SigmaSymbol.sigma-[m].Semiformula ξ n) :
    Hierarchy SigmaSymbol.sigma m φ.val :=
  φ.sigma_prop


-- @@ L165-165 expanded
@[simp]
lemma hierarchy_pi (φ : PiSymbol.pi-[m].Semiformula ξ n) : Hierarchy PiSymbol.pi m φ.val :=
  φ.pi_prop


-- @@ L167-172 verbatim
@[simp] lemma hierarchy_zero {Γ Γ' m} (φ : Γ-[0].Semiformula ξ n) : Hierarchy Γ' m φ.val := by
  cases Γ
  · exact Hierarchy.of_zero φ.sigma_prop
  · exact Hierarchy.of_zero φ.pi_prop
  · cases φ
    simp only [val_mkDelta]; exact Hierarchy.of_zero (sigma_prop _)


-- @@ L174-174 verbatim
variable {M : Type*} [ORingStruc M]


-- @@ L176-176 verbatim
variable (M)


-- @@ L178-180 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def ProperOn (φ : DeltaSymbol.delta-[m].Semisentence n) : Prop :=
  ∀ (e : Fin n → M), Semiformula.Evalbm M e φ.sigma.val ↔ Semiformula.Evalbm M e φ.pi.val


-- @@ L182-184 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def ProperWithParamOn (φ : DeltaSymbol.delta-[m].Semiformula M n) : Prop :=
  ∀ (e : Fin n → M), Semiformula.Evalm M e id φ.sigma.val ↔ Semiformula.Evalm M e id φ.pi.val


-- @@ L186-188 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def ProvablyProperOn (φ : DeltaSymbol.delta-[m].Semisentence n) (T : Theory oRing) : Prop :=
  Provable₀ T
    (univClosure
      (LogicalConnective.iff
        (LO.FirstOrder.Rewriting.substitute φ.sigma.val fun x ↦ #(finSuccItr x 0))
        (LO.FirstOrder.Rewriting.substitute φ.pi.val fun x ↦ #(finSuccItr x 0))))


-- @@ L190-190 verbatim
variable {M}


-- @@ L192-195 expanded
lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperOn.iff
    {φ : DeltaSymbol.delta-[m].Semisentence n} (h : φ.ProperOn M) (e : Fin n → M) :
    Semiformula.Evalbm M e φ.sigma.val ↔ Semiformula.Evalbm M e φ.pi.val :=
  h e


-- @@ L197-200 expanded
lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperWithParamOn.iff
    {φ : DeltaSymbol.delta-[m].Semiformula M n} (h : φ.ProperWithParamOn M) (e : Fin n → M) :
    Semiformula.Evalm M e id φ.sigma.val ↔ Semiformula.Evalm (L := oRing) M e id φ.pi.val :=
  h e


-- @@ L202-205 expanded
lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperOn.iff'
    {φ : DeltaSymbol.delta-[m].Semisentence n} (h : φ.ProperOn M) (e : Fin n → M) :
    Semiformula.Evalbm M e φ.pi.val ↔ Semiformula.Evalbm M e φ.val := by simp [← h.iff, val_sigma]


-- @@ L207-211 expanded
lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperWithParamOn.iff'
    {φ : DeltaSymbol.delta-[m].Semiformula M n} (h : φ.ProperWithParamOn M) (e : Fin n → M) :
    Semiformula.Evalm M e id φ.pi.val ↔ Semiformula.Evalm (L := oRing) M e id φ.val := by
  simp [← h.iff, val_sigma]


-- @@ L213-213 verbatim
section «lp_section_1»


-- @@ L215-215 expanded
variable (T : Theory oRing)


-- @@ L217-223 expanded
lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProvablyProperOn.ofProperOn
    [WeakerThan eqAxiom T] {φ : DeltaSymbol.delta-[m].Semisentence n}
    (h : ∀ (M : Type w) [ORingStruc M] [ModelsTheory M T], φ.ProperOn M) : φ.ProvablyProperOn T :=
  by
  apply complete (T := T) <| FirstOrder.Arith.oRing_consequence_of.{w} T _ ?_
  intro M _ _
  simpa [models_iff] using (h M).iff


-- @@ L225-225 verbatim
variable {T}


-- @@ L227-232 expanded
lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProvablyProperOn.properOn
    {φ : DeltaSymbol.delta-[m].Semisentence n} (h : φ.ProvablyProperOn T) (M : Type w)
    [ORingStruc M] [ModelsTheory M T] : φ.ProperOn M :=
  by
  intro v
  have := by simpa [models_iff] using consequence_iff.mp (sound! (T := T) h) M inferInstance
  exact this v


-- @@ L234-234 verbatim
end «lp_section_1»


-- @@ L236-241 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def rew (ω : Rew oRing ξ₁ n₁ ξ₂ n₂) :
    {Γ : HierarchySymbol} → Γ.Semiformula ξ₁ n₁ → Γ.Semiformula ξ₂ n₂
  | SigmaSymbol.sigma-[_], mkSigma φ hp => mkSigma (app ω φ) (by simpa using hp)
  | PiSymbol.pi-[_], mkPi φ hp => mkPi (app ω φ) (by simpa using hp)
  | DeltaSymbol.delta-[_], mkDelta φ ψ => mkDelta (φ.rew ω) (ψ.rew ω)


-- @@ L243-245 expanded
@[simp]
lemma val_rew (ω : Rew oRing ξ₁ n₁ ξ₂ n₂) {Γ : HierarchySymbol} (φ : Γ.Semiformula ξ₁ n₁) :
    (φ.rew ω).val = app ω φ.val := by rcases Γ with ⟨Γ, m⟩;
  rcases φ with (_ | _ | ⟨⟨p, _⟩, ⟨q, _⟩⟩) <;> simp [rew]


-- @@ L247-254 expanded
@[simp]
lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperOn.rew
    {φ : DeltaSymbol.delta-[m].Semisentence n₁} (h : φ.ProperOn M)
    (ω : Rew oRing Empty n₁ Empty n₂) : (φ.rew ω).ProperOn M :=
  by
  rcases φ
  simp only [Semiformula.ProperOn, Semiformula.rew, Semiformula.sigma_mkDelta, Semiformula.val_rew,
    Semiformula.eval_rew, Empty.eq_elim, Semiformula.pi_mkDelta]
  intro e; exact h.iff _


-- @@ L256-261 expanded
@[simp]
lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperOn.rew'
    {φ : DeltaSymbol.delta-[m].Semisentence n₁} (h : φ.ProperOn M) (ω : Rew oRing Empty n₁ M n₂) :
    (φ.rew ω).ProperWithParamOn M := by
  rcases φ; intro e; simp [Semiformula.rew, Semiformula.eval_rew, Empty.eq_elim]
  simpa using h.iff _


-- @@ L263-270 expanded
@[simp]
lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperWithParamOn.rew
    {φ : DeltaSymbol.delta-[m].Semiformula M n₁} (h : φ.ProperWithParamOn M)
    (f : Fin n₁ → Semiterm oRing M n₂) : (φ.rew (Rew.substs f)).ProperWithParamOn M :=
  by
  rcases φ; intro e;
  simp only [Semiformula.rew, Semiformula.sigma_mkDelta, Semiformula.val_rew, Semiformula.eval_rew,
    Semiformula.pi_mkDelta]
  exact h.iff _


-- @@ L272-276 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def emb : {Γ : HierarchySymbol} → Γ.Semiformula ξ n → Γ.Semiformula ξ n
  | SigmaSymbol.sigma-[_], mkSigma φ hp =>
    mkSigma (Semiformula.lMap Language.oringEmb φ) (Hierarchy.oringEmb hp)
  | PiSymbol.pi-[_], mkPi φ hp =>
    mkPi (Semiformula.lMap Language.oringEmb φ) (Hierarchy.oringEmb hp)
  | DeltaSymbol.delta-[_], mkDelta φ ψ => mkDelta φ.emb ψ.emb


-- @@ L278-280 verbatim
@[simp] lemma val_emb {Γ : HierarchySymbol} (φ : Γ.Semiformula ξ n) :
    φ.emb.val = Semiformula.lMap Language.oringEmb φ.val := by
  rcases Γ with ⟨Γ, m⟩; rcases φ with (_ | _ | ⟨⟨p, _⟩, ⟨q, _⟩⟩) <;> simp [val, emb]


-- @@ L282-282 expanded
@[simp]
lemma pi_emb (φ : DeltaSymbol.delta-[m].Semiformula ξ n) : φ.emb.pi = φ.pi.emb := by cases φ; rfl


-- @@ L284-284 expanded
@[simp]
lemma sigma_emb (φ : DeltaSymbol.delta-[m].Semiformula ξ n) : φ.emb.sigma = φ.sigma.emb := by
  cases φ; rfl


-- @@ L286-287 expanded
@[simp]
lemma emb_proper (φ : DeltaSymbol.delta-[m].Semisentence n) : φ.emb.ProperOn M ↔ φ.ProperOn M := by
  rcases φ; simp [ProperOn, emb]


-- @@ L289-290 expanded
@[simp]
lemma emb_properWithParam (φ : DeltaSymbol.delta-[m].Semiformula M n) :
    φ.emb.ProperWithParamOn M ↔ φ.ProperWithParamOn M := by rcases φ; simp [ProperWithParamOn, emb]


-- @@ L292-296 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def extd {Γ : HierarchySymbol} : Γ.Semiformula ξ n → Γ.Semiformula ξ n
  | mkSigma φ hp => mkSigma (Semiformula.lMap Language.oringEmb φ) (Hierarchy.oringEmb hp)
  | mkPi φ hp    => mkPi (Semiformula.lMap Language.oringEmb φ) (Hierarchy.oringEmb hp)
  | mkDelta φ ψ  => mkDelta φ.extd ψ.extd


-- @@ L298-301 verbatim
@[simp]
lemma eval_extd_iff {e ε} {φ : Γ.Semiformula ξ n} :
    Semiformula.Evalm M e ε φ.extd.val ↔ Semiformula.Evalm M e ε φ.val := by
  induction φ <;> simp [extd, *]


-- @@ L303-306 expanded
lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperOn.extd
    {φ : DeltaSymbol.delta-[m].Semisentence n} (h : φ.ProperOn M) : φ.extd.ProperOn M := by intro e;
  rcases φ; simpa [Semiformula.extd] using h.iff e


-- @@ L308-311 expanded
lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperWithParamOn.extd
    {φ : DeltaSymbol.delta-[m].Semisentence n} (h : φ.ProperOn M) : φ.extd.ProperOn M :=
  ProperOn.extd h


-- @@ L313-314 expanded
lemma sigma_extd_val (φ : SigmaSymbol.sigma-[m].Semiformula ξ n) :
    φ.extd.val = Semiformula.lMap Language.oringEmb φ.val := by rcases φ; simp [extd]


-- @@ L316-317 expanded
lemma pi_extd_val (φ : PiSymbol.pi-[m].Semiformula ξ n) :
    φ.extd.val = Semiformula.lMap Language.oringEmb φ.val := by rcases φ; simp [extd]


-- @@ L319-323 expanded
lemma sigmaZero {Γ} (φ : Γ-[0].Semiformula ξ k) : Hierarchy SigmaSymbol.sigma 0 φ.val :=
  match Γ with
  | SigmaSymbol.sigma => φ.sigma_prop
  | PiSymbol.pi => φ.pi_prop.of_zero
  | DeltaSymbol.delta => by simp []


-- @@ L325-329 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def ofZero {Γ'} (φ : Γ'-[0].Semiformula ξ k) : (Γ : HierarchySymbol) → Γ.Semiformula ξ k
  | SigmaSymbol.sigma-[_] => mkSigma φ.val φ.sigmaZero.of_zero
  | PiSymbol.pi-[_] => mkPi φ.val φ.sigmaZero.of_zero
  | DeltaSymbol.delta-[_] =>
    mkDelta (mkSigma φ.val φ.sigmaZero.of_zero) (mkPi φ.val φ.sigmaZero.of_zero)


-- @@ L331-337 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def ofDeltaOne (φ : Dlt1.Semiformula ξ k) : (Γ : SigmaPiDelta) → (m : ℕ) → Γ-[m + 1].Semiformula ξ k
  | SigmaSymbol.sigma, m => mkSigma φ.sigma.val (φ.sigma.sigma_prop.mono (by simp))
  | PiSymbol.pi, m => mkPi φ.pi.val (φ.pi.pi_prop.mono (by simp))
  | DeltaSymbol.delta, m =>
    mkDelta (mkSigma φ.sigma.val (φ.sigma.sigma_prop.mono (by simp)))
      (mkPi φ.pi.val (φ.pi.pi_prop.mono (by simp)))


-- @@ L339-343 expanded
@[simp]
lemma ofZero_val {Γ'} (φ : Γ'-[0].Semiformula ξ n) (Γ) : (ofZero φ Γ).val = φ.val := by
  match Γ with
  | SigmaSymbol.sigma-[_] => simp [ofZero]
  | PiSymbol.pi-[_] => simp [ofZero]
  | DeltaSymbol.delta-[_] => simp [ofZero]


-- @@ L345-347 expanded
@[simp]
lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperOn.of_zero
    (φ : Γ'-[0].Semisentence k) (m) : (ofZero φ DeltaSymbol.delta-[m]).ProperOn M := by
  simp [ProperOn, ofZero]


-- @@ L349-351 expanded
@[simp]
lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperWithParamOn.of_zero
    (φ : Γ'-[0].Semiformula M k) (m) : (ofZero φ DeltaSymbol.delta-[m]).ProperWithParamOn M := by
  simp [ProperWithParamOn, ofZero]


-- @@ L353-357 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def verum : {Γ : HierarchySymbol} → Γ.Semiformula ξ n
  | SigmaSymbol.sigma-[m] => mkSigma ⊤ (by simp)
  | PiSymbol.pi-[m] => mkPi ⊤ (by simp)
  | DeltaSymbol.delta-[m] => mkDelta (mkSigma ⊤ (by simp)) (mkPi ⊤ (by simp))


-- @@ L359-363 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def falsum : {Γ : HierarchySymbol} → Γ.Semiformula ξ n
  | SigmaSymbol.sigma-[m] => mkSigma ⊥ (by simp)
  | PiSymbol.pi-[m] => mkPi ⊥ (by simp)
  | DeltaSymbol.delta-[m] => mkDelta (mkSigma ⊥ (by simp)) (mkPi ⊥ (by simp))


-- @@ L365-370 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def and : {Γ : HierarchySymbol} → Γ.Semiformula ξ n → Γ.Semiformula ξ n → Γ.Semiformula ξ n
  | SigmaSymbol.sigma-[m], φ, ψ => mkSigma (Wedge.wedge φ.val ψ.val) (by simp)
  | PiSymbol.pi-[m], φ, ψ => mkPi (Wedge.wedge φ.val ψ.val) (by simp)
  | DeltaSymbol.delta-[m], φ, ψ =>
    mkDelta (mkSigma (Wedge.wedge φ.sigma.val ψ.sigma.val) (by simp))
      (mkPi (Wedge.wedge φ.pi.val ψ.pi.val) (by simp))


-- @@ L372-377 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def or : {Γ : HierarchySymbol} → Γ.Semiformula ξ n → Γ.Semiformula ξ n → Γ.Semiformula ξ n
  | SigmaSymbol.sigma-[m], φ, ψ => mkSigma (Vee.vee φ.val ψ.val) (by simp)
  | PiSymbol.pi-[m], φ, ψ => mkPi (Vee.vee φ.val ψ.val) (by simp)
  | DeltaSymbol.delta-[m], φ, ψ =>
    mkDelta (mkSigma (Vee.vee φ.sigma.val ψ.sigma.val) (by simp))
      (mkPi (Vee.vee φ.pi.val ψ.pi.val) (by simp))


-- @@ L379-380 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def negSigma (φ : SigmaSymbol.sigma-[m].Semiformula ξ n) : PiSymbol.pi-[m].Semiformula ξ n :=
  mkPi (Tilde.tilde φ.val) (by simp)


-- @@ L382-383 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def negPi (φ : PiSymbol.pi-[m].Semiformula ξ n) : SigmaSymbol.sigma-[m].Semiformula ξ n :=
  mkSigma (Tilde.tilde φ.val) (by simp)


-- @@ L385-388 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def negDelta (φ : DeltaSymbol.delta-[m].Semiformula ξ n) : DeltaSymbol.delta-[m].Semiformula ξ n :=
  mkDelta (φ.pi.negPi) (φ.sigma.negSigma)


-- @@ L390-397 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def ball (t : Semiterm oRing ξ n) :
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


-- @@ L399-405 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def bex (t : Semiterm oRing ξ n) :
    {Γ : HierarchySymbol} → Γ.Semiformula ξ (n + 1) → Γ.Semiformula ξ n
  | SigmaSymbol.sigma-[m], φ =>
    mkSigma (bex (Semiformula.Operator.operator Operator.LT.lt ![#0, (Rew.bShift t)]) φ.val)
      (by simp)
  | PiSymbol.pi-[m], φ =>
    mkPi (bex (Semiformula.Operator.operator Operator.LT.lt ![#0, (Rew.bShift t)]) φ.val) (by simp)
  | DeltaSymbol.delta-[m], φ =>
    mkDelta
      (mkSigma
        (bex (Semiformula.Operator.operator Operator.LT.lt ![#0, (Rew.bShift t)]) φ.sigma.val)
        (by simp))
      (mkPi (bex (Semiformula.Operator.operator Operator.LT.lt ![#0, (Rew.bShift t)]) φ.pi.val)
        (by simp))


-- @@ L407-410 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def all (φ : PiSymbol.pi-[m + 1].Semiformula ξ (n + 1)) : PiSymbol.pi-[m + 1].Semiformula ξ n :=
  mkPi (UnivQuantifier.univ φ.val) φ.pi_prop.all


-- @@ L412-415 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def ex (φ : SigmaSymbol.sigma-[m + 1].Semiformula ξ (n + 1)) :
    SigmaSymbol.sigma-[m + 1].Semiformula ξ n :=
  mkSigma (ExQuantifier.ex φ.val) φ.sigma_prop.ex


-- @@ L417-417 verbatim
instance : Top (Γ.Semiformula ξ n) := ⟨verum⟩


-- @@ L419-419 verbatim
instance : Bot (Γ.Semiformula ξ n) := ⟨falsum⟩


-- @@ L421-421 verbatim
instance : Wedge (Γ.Semiformula ξ n) := ⟨and⟩


-- @@ L423-423 verbatim
instance : Vee (Γ.Semiformula ξ n) := ⟨or⟩


-- @@ L425-425 expanded
instance : Tilde (DeltaSymbol.delta-[m].Semiformula ξ n) :=
  ⟨negDelta⟩


-- @@ L427-428 expanded
instance : LogicalConnective (DeltaSymbol.delta-[m].Semiformula ξ n) where
  arrow φ ψ := Vee.vee (Tilde.tilde φ) ψ


-- @@ L430-430 expanded
instance : ExQuantifier (SigmaSymbol.sigma-[m + 1].Semiformula ξ) :=
  ⟨ex⟩


-- @@ L432-432 expanded
instance : UnivQuantifier (PiSymbol.pi-[m + 1].Semiformula ξ) :=
  ⟨all⟩


-- @@ L434-436 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def substSigma (φ : SigmaSymbol.sigma-[m + 1].Semiformula ξ 1)
    (F : SigmaSymbol.sigma-[m + 1].Semiformula ξ (n + 1)) :
    SigmaSymbol.sigma-[m + 1].Semiformula ξ n :=
  (Wedge.wedge F (φ.rew (Rew.substs ![#0]))).ex


-- @@ L438-440 verbatim
@[simp] lemma val_verum : (⊤ : Γ.Semiformula ξ n).val = ⊤ := by
  rcases Γ with ⟨Γ, m⟩
  rcases Γ <;> rfl


-- @@ L442-442 expanded
@[simp]
lemma sigma_verum {m} : (⊤ : DeltaSymbol.delta-[m].Semiformula ξ n).sigma = ⊤ := by
  simp [Top.top, verum]


-- @@ L444-444 expanded
@[simp]
lemma pi_verum {m} : (⊤ : DeltaSymbol.delta-[m].Semiformula ξ n).pi = ⊤ := by simp [Top.top, verum]


-- @@ L446-448 verbatim
@[simp] lemma val_falsum : (⊥ : Γ.Semiformula ξ n).val = ⊥ := by
  rcases Γ with ⟨Γ, m⟩
  rcases Γ <;> rfl


-- @@ L450-451 expanded
@[simp]
lemma sigma_falsum {m} : (⊥ : DeltaSymbol.delta-[m].Semiformula ξ n).sigma = ⊥ := by
  simp [Bot.bot, falsum]


-- @@ L453-453 expanded
@[simp]
lemma pi_falsum {m} : (⊥ : DeltaSymbol.delta-[m].Semiformula ξ n).pi = ⊥ := by
  simp [Bot.bot, falsum]


-- @@ L455-457 expanded
@[simp]
lemma val_and (φ ψ : Γ.Semiformula ξ n) : (Wedge.wedge φ ψ).val = Wedge.wedge φ.val ψ.val :=
  by
  suffices (φ.and ψ).val = Wedge.wedge φ.val ψ.val from this
  rcases Γ with ⟨Γ, m⟩; rcases Γ <;> simp [and, val, val_sigma]


-- @@ L459-460 expanded
@[simp]
lemma sigma_and (φ ψ : DeltaSymbol.delta-[m].Semiformula ξ n) :
    (Wedge.wedge φ ψ).sigma = Wedge.wedge φ.sigma ψ.sigma := by simp [Wedge.wedge, and]


-- @@ L462-463 expanded
@[simp]
lemma pi_and (φ ψ : DeltaSymbol.delta-[m].Semiformula ξ n) :
    (Wedge.wedge φ ψ).pi = Wedge.wedge φ.pi ψ.pi := by simp [Wedge.wedge, and]


-- @@ L465-467 expanded
@[simp]
lemma val_or (φ ψ : Γ.Semiformula ξ n) : (Vee.vee φ ψ).val = Vee.vee φ.val ψ.val :=
  by
  suffices (φ.or ψ).val = Vee.vee φ.val ψ.val from this
  rcases Γ with ⟨Γ, m⟩; rcases Γ <;> simp [or, val, val_sigma]


-- @@ L469-470 expanded
@[simp]
lemma sigma_or (φ ψ : DeltaSymbol.delta-[m].Semiformula ξ n) :
    (Vee.vee φ ψ).sigma = Vee.vee φ.sigma ψ.sigma := by simp [Vee.vee, or]


-- @@ L472-473 expanded
@[simp]
lemma pi_or (φ ψ : DeltaSymbol.delta-[m].Semiformula ξ n) : (Vee.vee φ ψ).pi = Vee.vee φ.pi ψ.pi :=
  by simp [Vee.vee, or]


-- @@ L475-476 expanded
@[simp]
lemma val_negSigma {m} (φ : SigmaSymbol.sigma-[m].Semiformula ξ n) :
    φ.negSigma.val = Tilde.tilde φ.val := by simp [negSigma]


-- @@ L478-478 expanded
@[simp]
lemma val_negPi {m} (φ : PiSymbol.pi-[m].Semiformula ξ n) : φ.negPi.val = Tilde.tilde φ.val := by
  simp [negPi]


-- @@ L480-481 expanded
lemma val_negDelta {m} (φ : DeltaSymbol.delta-[m].Semiformula ξ n) :
    (Tilde.tilde φ).val = Tilde.tilde φ.pi.val := by simp [Tilde.tilde, negDelta]


-- @@ L483-484 expanded
@[simp]
lemma sigma_negDelta {m} (φ : DeltaSymbol.delta-[m].Semiformula ξ n) :
    (Tilde.tilde φ).sigma = φ.pi.negPi := by simp [Tilde.tilde, negDelta]


-- @@ L486-487 expanded
@[simp]
lemma sigma_negPi {m} (φ : DeltaSymbol.delta-[m].Semiformula ξ n) :
    (Tilde.tilde φ).pi = φ.sigma.negSigma := by simp [Tilde.tilde, negDelta]


-- @@ L489-491 expanded
@[simp]
lemma val_ball (t : Semiterm oRing ξ n) (φ : Γ.Semiformula ξ (n + 1)) :
    (ball t φ).val =
      ball (Semiformula.Operator.operator Operator.LT.lt ![#0, (Rew.bShift t)]) φ.val :=
  by rcases Γ with ⟨Γ, m⟩; rcases Γ <;> simp [ball, val, val_sigma]


-- @@ L493-495 expanded
@[simp]
lemma val_bex (t : Semiterm oRing ξ n) (φ : Γ.Semiformula ξ (n + 1)) :
    (bex t φ).val =
      bex (Semiformula.Operator.operator Operator.LT.lt ![#0, (Rew.bShift t)]) φ.val :=
  by rcases Γ with ⟨Γ, m⟩; rcases Γ <;> simp [bex, val, val_sigma]


-- @@ L497-497 expanded
@[simp]
lemma val_exSigma {m} (φ : SigmaSymbol.sigma-[m + 1].Semiformula ξ (n + 1)) :
    (ex φ).val = ExQuantifier.ex φ.val :=
  rfl


-- @@ L499-499 expanded
@[simp]
lemma val_allPi {m} (φ : PiSymbol.pi-[m + 1].Semiformula ξ (n + 1)) :
    (all φ).val = UnivQuantifier.univ φ.val :=
  rfl


-- @@ L501-502 expanded
@[simp]
lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperOn.verum :
    (⊤ : DeltaSymbol.delta-[m].Semisentence k).ProperOn M := by intro e; simp


-- @@ L504-505 expanded
@[simp]
lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperOn.falsum :
    (⊥ : DeltaSymbol.delta-[m].Semisentence k).ProperOn M := by intro e; simp


-- @@ L507-510 expanded
lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperOn.and
    {φ ψ : DeltaSymbol.delta-[m].Semisentence k} (hp : φ.ProperOn M) (hq : ψ.ProperOn M) :
    (Wedge.wedge φ ψ).ProperOn M := by intro e; simp [hp.iff, hq.iff]


-- @@ L512-515 expanded
lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperOn.or
    {φ ψ : DeltaSymbol.delta-[m].Semisentence k} (hp : φ.ProperOn M) (hq : ψ.ProperOn M) :
    (Vee.vee φ ψ).ProperOn M := by intro e; simp [hp.iff, hq.iff]


-- @@ L517-520 expanded
lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperOn.neg
    {φ : DeltaSymbol.delta-[m].Semisentence k} (hp : φ.ProperOn M) : (Tilde.tilde φ).ProperOn M :=
  by intro e; simp [hp.iff]


-- @@ L522-525 expanded
lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperOn.eval_neg
    {φ : DeltaSymbol.delta-[m].Semisentence k} (hp : φ.ProperOn M) (e) :
    Semiformula.Evalbm M e (Tilde.tilde φ).val ↔ ¬Semiformula.Evalbm M e φ.val := by
  simp [← val_sigma, hp.iff]


-- @@ L527-530 expanded
lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperOn.ball {t}
    {φ : DeltaSymbol.delta-[m + 1].Semisentence (k + 1)} (hp : φ.ProperOn M) :
    (ball t φ).ProperOn M := by intro e; simp [Semiformula.ball, hp.iff]


-- @@ L532-535 expanded
lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperOn.bex {t}
    {φ : DeltaSymbol.delta-[m + 1].Semisentence (k + 1)} (hp : φ.ProperOn M) :
    (bex t φ).ProperOn M := by intro e; simp [Semiformula.bex, hp.iff]


-- @@ L537-538 expanded
@[simp]
lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperWithParamOn.verum :
    (⊤ : DeltaSymbol.delta-[m].Semiformula M k).ProperWithParamOn M := by intro e; simp


-- @@ L540-541 expanded
@[simp]
lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperWithParamOn.falsum :
    (⊥ : DeltaSymbol.delta-[m].Semiformula M k).ProperWithParamOn M := by intro e; simp


-- @@ L543-546 expanded
lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperWithParamOn.and
    {φ ψ : DeltaSymbol.delta-[m].Semiformula M k} (hp : φ.ProperWithParamOn M)
    (hq : ψ.ProperWithParamOn M) : (Wedge.wedge φ ψ).ProperWithParamOn M := by intro e;
  simp [hp.iff, hq.iff]


-- @@ L548-551 expanded
lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperWithParamOn.or
    {φ ψ : DeltaSymbol.delta-[m].Semiformula M k} (hp : φ.ProperWithParamOn M)
    (hq : ψ.ProperWithParamOn M) : (Vee.vee φ ψ).ProperWithParamOn M := by intro e;
  simp [hp.iff, hq.iff]


-- @@ L553-556 expanded
lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperWithParamOn.neg
    {φ : DeltaSymbol.delta-[m].Semiformula M k} (hp : φ.ProperWithParamOn M) :
    (Tilde.tilde φ).ProperWithParamOn M := by intro e; simp [hp.iff]


-- @@ L558-562 expanded
lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperWithParamOn.eval_neg
    {φ : DeltaSymbol.delta-[m].Semiformula M k} (hp : φ.ProperWithParamOn M) (e) :
    Semiformula.Evalm M e id (Tilde.tilde φ).val ↔ ¬Semiformula.Evalm M e id φ.val := by
  simp [← val_sigma, hp.iff]


-- @@ L564-567 expanded
lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperWithParamOn.ball {t}
    {φ : DeltaSymbol.delta-[m].Semiformula M (k + 1)} (hp : φ.ProperWithParamOn M) :
    (ball t φ).ProperWithParamOn M := by intro e; simp [Semiformula.ball, hp.iff]


-- @@ L569-572 expanded
lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperWithParamOn.bex {t}
    {φ : DeltaSymbol.delta-[m].Semiformula M (k + 1)} (hp : φ.ProperWithParamOn M) :
    (bex t φ).ProperWithParamOn M := by intro e; simp [Semiformula.bex, hp.iff]


-- @@ L574-578 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def graphDelta (φ : SigmaSymbol.sigma-[m].Semiformula ξ (k + 1)) :
    DeltaSymbol.delta-[m].Semiformula ξ (k + 1) :=
  match m with
  | 0 => φ.ofZero _
  | m + 1 =>
    mkDelta φ
      (mkPi
        (UnivQuantifier.univ
          (Arrow.arrow
            (LO.FirstOrder.Rewriting.substitute φ.val (vecCons #0 fun x ↦ #(finSuccItr x 2)))
            (Semiformula.Operator.operator Operator.Eq.eq ![#0, #1])))
        (by simp))


-- @@ L580-581 expanded
@[simp]
lemma graphDelta_val (φ : SigmaSymbol.sigma-[m].Semiformula ξ (k + 1)) : φ.graphDelta.val = φ.val :=
  by cases m <;> simp [graphDelta]


-- @@ L583-583 verbatim
end Semiformula


-- @@ L585-585 verbatim
end HierarchySymbol


-- @@ L587-587 verbatim
end Arith

-- @@ L588-588 verbatim
end FirstOrder

-- @@ L589-589 verbatim
end LO
