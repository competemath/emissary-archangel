/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Arithmetization.Definability.Hierarchy
public import LeanPool.Incompleteness.Arithmetization.Vorspiel.Graph
import Mathlib.Algebra.Order.Sub.Basic


-- @@ L12-12 verbatim
/-! # Boldface -/


-- @@ L14-14 verbatim
@[expose] public section



-- @@ L17-17 verbatim
namespace LO

-- @@ L18-18 verbatim
namespace FirstOrder

-- @@ L19-19 verbatim
namespace Arith


-- @@ L21-21 verbatim
end Arith


-- @@ L23-25 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def Defined {k} (R : (Fin k → V) → Prop) [Structure L V] (φ : Semisentence L k) : Prop :=
  ∀ v, R v ↔ Semiformula.Evalbm V v φ


-- @@ L27-29 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def DefinedWithParam {k} (R : (Fin k → V) → Prop) [Structure L V] (φ : Semiformula L V k) : Prop :=
  ∀ v, R v ↔ Semiformula.Evalm V v id φ


-- @@ L31-34 verbatim
lemma _root_.LO.FirstOrder.Defined.iff [Structure L V] {k} {R : (Fin k → V) → Prop} {φ :
    Semisentence L k} (h :
    Defined R φ) (v) :
    Semiformula.Evalbm V v φ ↔ R v := (h v).symm


-- @@ L36-39 verbatim
lemma _root_.LO.FirstOrder.DefinedWithParam.iff [Structure L V] {k} {R : (Fin k → V) → Prop} {φ :
    Semiformula L V k} (h :
    DefinedWithParam R φ) (v) :
    Semiformula.Evalm V v id φ ↔ R v := (h v).symm


-- @@ L41-41 verbatim
namespace Arith

-- @@ L42-42 verbatim
namespace HierarchySymbol


-- @@ L44-44 verbatim
variable (ξ : Type*) (n : ℕ)


-- @@ L46-46 verbatim
open LO.Arith


-- @@ L48-48 verbatim
variable {V : Type*} [ORingStruc V]


-- @@ L50-54 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def Defined (R : (Fin k → V) → Prop) : {ℌ : HierarchySymbol} → ℌ.Semisentence k → Prop
  | SigmaSymbol.sigma-[_], φ => FirstOrder.Defined R φ.val
  | PiSymbol.pi-[_], φ => FirstOrder.Defined R φ.val
  | DeltaSymbol.delta-[_], φ => φ.ProperOn V ∧ FirstOrder.Defined R φ.val


-- @@ L56-60 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def DefinedWithParam (R : (Fin k → V) → Prop) : {ℌ : HierarchySymbol} → ℌ.Semiformula V k → Prop
  | SigmaSymbol.sigma-[_], φ => FirstOrder.DefinedWithParam R φ.val
  | PiSymbol.pi-[_], φ => FirstOrder.DefinedWithParam R φ.val
  | DeltaSymbol.delta-[_], φ => φ.ProperWithParamOn V ∧ FirstOrder.DefinedWithParam R φ.val


-- @@ L62-62 verbatim
variable {ℌ : HierarchySymbol} {Γ : SigmaPiDelta}


-- @@ L64-64 verbatim
section «lp_section_1»


-- @@ L66-66 verbatim
variable (ℌ)


-- @@ L68-70 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class Lightface {k} (P : (Fin k → V) → Prop) : Prop where
  definable : ∃ φ : ℌ.Semisentence k, Defined P φ


-- @@ L72-74 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class Boldface {k} (P : (Fin k → V) → Prop) : Prop where
  definable : ∃ φ : ℌ.Semiformula V k, DefinedWithParam P φ


-- @@ L76-77 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev DefinedPred (P : V → Prop) (φ : ℌ.Semisentence 1) : Prop := Defined (fun v ↦ P (v 0)) φ


-- @@ L79-81 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev DefinedRel (R : V → V → Prop) (φ : ℌ.Semisentence 2) : Prop :=
  Defined (fun v ↦ R (v 0) (v 1)) φ


-- @@ L83-85 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev DefinedRel₃ (R : V → V → V → Prop) (φ : ℌ.Semisentence 3) : Prop :=
  Defined (fun v ↦ R (v 0) (v 1) (v 2)) φ


-- @@ L87-89 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev DefinedRel₄ (R : V → V → V → V → Prop) (φ : ℌ.Semisentence 4) : Prop :=
  Defined (fun v ↦ R (v 0) (v 1) (v 2) (v 3)) φ


-- @@ L91-91 verbatim
variable {ℌ}


-- @@ L93-95 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev DefinedFunction {k} (f : (Fin k → V) → V) (φ : ℌ.Semisentence (k + 1)) : Prop :=
  Defined (fun v => v 0 = f (v ·.succ)) φ


-- @@ L97-97 verbatim
variable (ℌ)


-- @@ L99-100 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev DefinedFunction₀ (c : V) (φ : ℌ.Semisentence 1) : Prop := DefinedFunction (fun _ => c) φ


-- @@ L102-104 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev DefinedFunction₁ (f : V → V) (φ : ℌ.Semisentence 2) : Prop :=
  DefinedFunction (fun v => f (v 0)) φ


-- @@ L106-108 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev DefinedFunction₂ (f : V → V → V) (φ : ℌ.Semisentence 3) : Prop :=
  DefinedFunction (fun v => f (v 0) (v 1)) φ


-- @@ L110-112 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev DefinedFunction₃ (f : V → V → V → V) (φ : ℌ.Semisentence 4) : Prop :=
  DefinedFunction (fun v => f (v 0) (v 1) (v 2)) φ


-- @@ L114-116 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev DefinedFunction₄ (f : V → V → V → V → V) (φ : ℌ.Semisentence 5) : Prop :=
  DefinedFunction (fun v => f (v 0) (v 1) (v 2) (v 3)) φ


-- @@ L118-120 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev DefinedFunction₅ (f : V → V → V → V → V → V) (φ : ℌ.Semisentence 6) : Prop :=
  DefinedFunction (fun v => f (v 0) (v 1) (v 2) (v 3) (v 4)) φ


-- @@ L122-123 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev BoldfacePred (P : V → Prop) : Prop := ℌ.Boldface (k := 1) (fun v ↦ P (v 0))


-- @@ L125-126 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev BoldfaceRel (P : V → V → Prop) : Prop := ℌ.Boldface (k := 2) (fun v ↦ P (v 0) (v 1))


-- @@ L128-130 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev BoldfaceRel₃ (P : V → V → V → Prop) : Prop :=
  ℌ.Boldface (k := 3) (fun v ↦ P (v 0) (v 1) (v 2))


-- @@ L132-134 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev BoldfaceRel₄ (P : V → V → V → V → Prop) : Prop :=
  ℌ.Boldface (k := 4) (fun v ↦ P (v 0) (v 1) (v 2) (v 3))


-- @@ L136-138 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev BoldfaceRel₅ (P : V → V → V → V → V → Prop) : Prop :=
  ℌ.Boldface (k := 5) (fun v ↦ P (v 0) (v 1) (v 2) (v 3) (v 4))


-- @@ L140-142 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev BoldfaceRel₆ (P : V → V → V → V → V → V → Prop) : Prop :=
  ℌ.Boldface (k := 6) (fun v ↦ P (v 0) (v 1) (v 2) (v 3) (v 4) (v 5))


-- @@ L144-146 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev BoldfaceFunction (f : (Fin k → V) → V) : Prop :=
  ℌ.Boldface (k := k + 1) (fun v ↦ v 0 = f (v ·.succ))


-- @@ L148-149 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev BoldfaceFunction₀ (c : V) : Prop := ℌ.BoldfaceFunction (k := 0) (fun _ ↦ c)


-- @@ L151-152 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev BoldfaceFunction₁ (f : V → V) : Prop := ℌ.BoldfaceFunction (k := 1) (fun v ↦ f (v 0))


-- @@ L154-156 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev BoldfaceFunction₂ (f : V → V → V) : Prop :=
  ℌ.BoldfaceFunction (k := 2) (fun v ↦ f (v 0) (v 1))


-- @@ L158-160 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev BoldfaceFunction₃ (f : V → V → V → V) : Prop :=
  ℌ.BoldfaceFunction (k := 3) (fun v ↦ f (v 0) (v 1) (v 2))


-- @@ L162-164 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev BoldfaceFunction₄ (f : V → V → V → V → V) : Prop :=
  ℌ.BoldfaceFunction (k := 4) (fun v ↦ f (v 0) (v 1) (v 2) (v 3))


-- @@ L166-168 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev BoldfaceFunction₅ (f : V → V → V → V → V → V) : Prop :=
  ℌ.BoldfaceFunction (k := 5) (fun v ↦ f (v 0) (v 1) (v 2) (v 3) (v 4))


-- @@ L170-170 verbatim
variable {ℌ}


-- @@ L172-173 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation Γ "-Predicate " P " via " φ => DefinedPred Γ P φ


-- @@ L175-176 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation Γ "-Relation " P " via " φ => DefinedRel Γ P φ


-- @@ L178-179 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation Γ "-Relation₃ " P " via " φ => DefinedRel₃ Γ P φ


-- @@ L181-182 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation Γ "-Relation₄ " P " via " φ => DefinedRel₄ Γ P φ


-- @@ L184-185 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation Γ "-Function₀ " c " via " φ => DefinedFunction₀ Γ c φ


-- @@ L187-188 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation Γ "-Function₁ " f " via " φ => DefinedFunction₁ Γ f φ


-- @@ L190-191 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation Γ "-Function₂ " f " via " φ => DefinedFunction₂ Γ f φ


-- @@ L193-194 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation Γ "-Function₃ " f " via " φ => DefinedFunction₃ Γ f φ


-- @@ L196-197 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation Γ "-Function₄ " f " via " φ => DefinedFunction₄ Γ f φ


-- @@ L199-200 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation Γ "-Function₅ " f " via " φ => DefinedFunction₅ Γ f φ


-- @@ L202-203 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation Γ "-Predicate " P => BoldfacePred Γ P


-- @@ L205-206 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation Γ "-Relation " P => BoldfaceRel Γ P


-- @@ L208-209 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation Γ "-Relation₃ " P => BoldfaceRel₃ Γ P


-- @@ L211-212 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation Γ "-Relation₄ " P => BoldfaceRel₄ Γ P


-- @@ L214-215 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation Γ "-Relation₅ " P => BoldfaceRel₅ Γ P


-- @@ L217-218 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation Γ "-Function₁ " f => BoldfaceFunction₁ Γ f


-- @@ L220-221 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation Γ "-Function₂ " f => BoldfaceFunction₂ Γ f


-- @@ L223-224 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation Γ "-Function₃ " f => BoldfaceFunction₃ Γ f


-- @@ L226-227 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation Γ "-Function₄ " f => BoldfaceFunction₄ Γ f



-- @@ L230-230 verbatim
end «lp_section_1»


-- @@ L232-232 verbatim
section «lp_section_2»


-- @@ L234-234 verbatim
variable {k} {P Q : (Fin k → V) → Prop}


-- @@ L236-236 verbatim
namespace Defined


-- @@ L238-243 expanded
lemma df {R : (Fin k → V) → Prop} {φ : ℌ.Semisentence k} (h : Defined R φ) :
    FirstOrder.Defined R φ.val :=
  match ℌ with
  | SigmaSymbol.sigma-[_] => h
  | PiSymbol.pi-[_] => h
  | DeltaSymbol.delta-[_] => h.2


-- @@ L245-247 expanded
lemma proper {R : (Fin k → V) → Prop} {m} {φ : DeltaSymbol.delta-[m].Semisentence k}
    (h : Defined R φ) : φ.ProperOn V :=
  h.1


-- @@ L249-254 expanded
lemma of_zero {R : (Fin k → V) → Prop} {φ : Sg0.Semisentence k} (h : Defined R φ) :
    Defined R (φ.ofZero ℌ) :=
  match ℌ with
  | SigmaSymbol.sigma-[m] => by intro _; simp [h.iff]
  | PiSymbol.pi-[m] => by intro _; simp [h.iff]
  | DeltaSymbol.delta-[m] => ⟨by simp, by intro _; simp [h.iff]⟩


-- @@ L256-260 expanded
lemma emb {R : (Fin k → V) → Prop} {φ : ℌ.Semisentence k} (h : Defined R φ) : Defined R φ.emb :=
  match ℌ with
  | SigmaSymbol.sigma-[m] => by intro _; simp [h.iff]
  | PiSymbol.pi-[m] => by intro _; simp [h.iff]
  | DeltaSymbol.delta-[m] => ⟨by simpa using h.proper, by intro _; simp [h.df.iff]⟩


-- @@ L262-264 verbatim
lemma of_iff {P Q : (Fin k → V) → Prop} (h : ∀ x, P x ↔ Q x) {φ : ℌ.Semisentence k} (H :
    Defined Q φ) :
    Defined P φ := by rwa [show P = Q from by funext v; simp [h]]


-- @@ L266-272 expanded
lemma to_definable (φ : ℌ.Semisentence k) (hP : Defined P φ) : ℌ.Boldface P :=
  ⟨φ.rew Rew.emb, by
    match ℌ with
    | SigmaSymbol.sigma-[_] => intro; simp [hP.iff]
    | PiSymbol.pi-[_] => intro; simp [hP.iff]
    | DeltaSymbol.delta-[_] =>
      exact
        ⟨fun v ↦ by rcases φ; simpa [HierarchySymbol.Semiformula.rew] using hP.proper.rew Rew.emb v,
          by intro; simp [hP.df.iff]⟩⟩


-- @@ L274-275 verbatim
lemma to_definable₀ {φ : Sg0.Semisentence k} (hP : Defined P φ) :
    ℌ.Boldface P := Defined.to_definable (φ.ofZero ℌ) hP.of_zero


-- @@ L277-278 verbatim
lemma to_definable_oRing (φ : ℌ.Semisentence k) (hP : Defined P φ) :
    ℌ.Boldface P := Defined.to_definable φ.emb hP.emb


-- @@ L280-281 verbatim
lemma to_definable_oRing₀ (φ : Sg0.Semisentence k) (hP : Defined P φ) :
    ℌ.Boldface P := Defined.to_definable₀ hP.emb


-- @@ L283-283 verbatim
end Defined


-- @@ L285-285 verbatim
namespace DefinedFunction


-- @@ L287-289 verbatim
lemma of_eq {f g : (Fin k → V) → V} (h : ∀ x, f x = g x)
    {φ : ℌ.Semisentence (k + 1)} (H : DefinedFunction f φ) : DefinedFunction g φ :=
  Defined.of_iff (by intro; simp [h]) H


-- @@ L291-303 expanded
lemma graph_delta {f : (Fin k → V) → V} {φ : SigmaSymbol.sigma-[m].Semisentence (k + 1)}
    (h : DefinedFunction f φ) : DefinedFunction f φ.graphDelta :=
  ⟨by
    rcases m with _ | m <;>
      simp only [HierarchySymbol.Semiformula.graphDelta, Semiformula.ProperOn.of_zero]
    intro e
    simp only [Semiformula.sigma_mkDelta, h.df.iff, Semiformula.pi_mkDelta, Semiformula.val_mkPi,
      Semiformula.eval_all, Nat.succ_eq_add_one, LogicalConnective.HomClass.map_imply,
      Semiformula.eval_substs, Matrix.comp_vecCons', Semiterm.val_bvar, Matrix.vecCons_zero,
      Matrix.vecCons_succ, Semiformula.eval_operator₂, Matrix.cons_val_one, Structure.Eq.eq,
      LogicalConnective.Prop.arrow_eq, forall_eq]
    rw [eq_comm], by intro v; simp [h.df.iff]⟩


-- @@ L305-305 verbatim
end DefinedFunction


-- @@ L307-307 verbatim
namespace DefinedWithParam


-- @@ L309-314 expanded
lemma df {R : (Fin k → V) → Prop} {φ : ℌ.Semiformula V k} (h : DefinedWithParam R φ) :
    FirstOrder.DefinedWithParam R φ.val :=
  match ℌ with
  | SigmaSymbol.sigma-[_] => h
  | PiSymbol.pi-[_] => h
  | DeltaSymbol.delta-[_] => h.2


-- @@ L316-318 expanded
lemma proper {R : (Fin k → V) → Prop} {m} {φ : DeltaSymbol.delta-[m].Semiformula V k}
    (h : DefinedWithParam R φ) : φ.ProperWithParamOn V :=
  h.1


-- @@ L320-325 expanded
lemma of_zero {R : (Fin k → V) → Prop} {Γ'} {φ : Γ'-[0].Semiformula V k} (h : DefinedWithParam R φ)
    {Γ} : DefinedWithParam R (φ.ofZero Γ) :=
  match Γ with
  | SigmaSymbol.sigma-[m] => by intro _; simp [h.df.iff]
  | PiSymbol.pi-[m] => by intro _; simp [h.df.iff]
  | DeltaSymbol.delta-[m] => ⟨by simp, by intro _; simp [h.df.iff]⟩


-- @@ L327-341 expanded
lemma of_deltaOne {R : (Fin k → V) → Prop} {Γ m} {φ : Dlt1.Semiformula V k}
    (h : DefinedWithParam R φ) : DefinedWithParam R (φ.ofDeltaOne Γ m) :=
  match Γ with
  | SigmaSymbol.sigma => by
    intro _
    simp [HierarchySymbol.Semiformula.ofDeltaOne, h.df.iff, HierarchySymbol.Semiformula.val_sigma]
  | PiSymbol.pi => by intro _;
    simp [HierarchySymbol.Semiformula.ofDeltaOne, h.df.iff, h.proper.iff']
  | DeltaSymbol.delta =>
    ⟨by
      intro _
      simp [HierarchySymbol.Semiformula.ofDeltaOne, h.df.iff, HierarchySymbol.Semiformula.val_sigma,
        h.proper.iff'],
      by intro _;
      simp [HierarchySymbol.Semiformula.ofDeltaOne, h.df.iff,
        HierarchySymbol.Semiformula.val_sigma]⟩


-- @@ L343-348 expanded
lemma emb {R : (Fin k → V) → Prop} {φ : ℌ.Semiformula V k} (h : DefinedWithParam R φ) :
    DefinedWithParam R φ.emb :=
  match ℌ with
  | SigmaSymbol.sigma-[m] => by intro _; simp [h.iff]
  | PiSymbol.pi-[m] => by intro _; simp [h.iff]
  | DeltaSymbol.delta-[m] => ⟨by simpa using h.proper, by intro _; simp [h.df.iff]⟩


-- @@ L350-352 verbatim
lemma of_iff {P Q : (Fin k → V) → Prop} (h : ∀ x, P x ↔ Q x)
    {φ : ℌ.Semiformula V k} (H : DefinedWithParam Q φ) : DefinedWithParam P φ := by
  rwa [show P = Q from by funext v; simp [h]]


-- @@ L354-354 verbatim
lemma to_definable {φ : ℌ.Semiformula V k} (h : DefinedWithParam P φ) : ℌ.Boldface P := ⟨φ, h⟩


-- @@ L356-357 verbatim
lemma to_definable₀ {φ : Γ'-[0].Semiformula V k}
    (h : DefinedWithParam P φ) : ℌ.Boldface P := ⟨φ.ofZero ℌ, h.of_zero⟩


-- @@ L359-360 verbatim
lemma to_definable_deltaOne {φ : Dlt1.Semiformula V k} {Γ m}
    (h : DefinedWithParam P φ) : Γ-[m + 1].Boldface P := ⟨φ.ofDeltaOne Γ m, h.of_deltaOne⟩


-- @@ L362-367 expanded
lemma retraction {φ : ℌ.Semiformula V k} (hp : DefinedWithParam P φ) (f : Fin k → Fin l) :
    DefinedWithParam (fun v ↦ P fun i ↦ v (f i)) (φ.rew <| Rew.substs fun x ↦ #(f x)) :=
  match ℌ with
  | SigmaSymbol.sigma-[_] => by intro; simp [hp.df.iff]
  | PiSymbol.pi-[_] => by intro; simp [hp.df.iff]
  | DeltaSymbol.delta-[_] => ⟨hp.proper.rew _, by intro; simp [hp.df.iff]⟩


-- @@ L369-373 expanded
@[simp]
lemma verum : DefinedWithParam (fun _ ↦ True) (⊤ : ℌ.Semiformula V k) :=
  match ℌ with
  | SigmaSymbol.sigma-[m] => by intro v; simp
  | PiSymbol.pi-[m] => by intro v; simp
  | DeltaSymbol.delta-[m] => ⟨by simp, by intro v; simp⟩


-- @@ L375-379 expanded
@[simp]
lemma falsum : DefinedWithParam (fun _ ↦ False) (⊥ : ℌ.Semiformula V k) :=
  match ℌ with
  | SigmaSymbol.sigma-[m] => by intro v; simp
  | PiSymbol.pi-[m] => by intro v; simp
  | DeltaSymbol.delta-[m] => ⟨by simp, by intro v; simp⟩


-- @@ L381-386 expanded
lemma and {φ ψ : ℌ.Semiformula V k} (hp : DefinedWithParam P φ) (hq : DefinedWithParam Q ψ) :
    DefinedWithParam (fun x ↦ P x ∧ Q x) (Wedge.wedge φ ψ) :=
  match ℌ with
  | SigmaSymbol.sigma-[m] => by intro v; simp [hp.iff, hq.iff]
  | PiSymbol.pi-[m] => by intro v; simp [hp.iff, hq.iff]
  | DeltaSymbol.delta-[m] => ⟨hp.proper.and hq.proper, by intro v; simp [hp.df.iff, hq.df.iff]⟩


-- @@ L388-393 expanded
lemma or {φ ψ : ℌ.Semiformula V k} (hp : DefinedWithParam P φ) (hq : DefinedWithParam Q ψ) :
    DefinedWithParam (fun x ↦ P x ∨ Q x) (Vee.vee φ ψ) :=
  match ℌ with
  | SigmaSymbol.sigma-[m] => by intro v; simp [hp.iff, hq.iff]
  | PiSymbol.pi-[m] => by intro v; simp [hp.iff, hq.iff]
  | DeltaSymbol.delta-[m] => ⟨hp.proper.or hq.proper, by intro v; simp [hp.df.iff, hq.df.iff]⟩


-- @@ L395-396 expanded
lemma negSigma {φ : SigmaSymbol.sigma-[m].Semiformula V k} (hp : DefinedWithParam P φ) :
    DefinedWithParam (fun x ↦ ¬P x) φ.negSigma := by intro v; simp [hp.iff]


-- @@ L398-399 expanded
lemma negPi {φ : PiSymbol.pi-[m].Semiformula V k} (hp : DefinedWithParam P φ) :
    DefinedWithParam (fun x ↦ ¬P x) φ.negPi := by intro v; simp [hp.iff]


-- @@ L401-403 expanded
lemma not {φ : DeltaSymbol.delta-[m].Semiformula V k} (hp : DefinedWithParam P φ) :
    DefinedWithParam (fun x ↦ ¬P x) (Tilde.tilde φ) :=
  ⟨hp.proper.neg, by intro v; simp [hp.proper.eval_neg, hp.df.iff]⟩


-- @@ L405-407 expanded
lemma imp {φ ψ : DeltaSymbol.delta-[m].Semiformula V k} (hp : DefinedWithParam P φ)
    (hq : DefinedWithParam Q ψ) : DefinedWithParam (fun x ↦ P x → Q x) (Arrow.arrow φ ψ) :=
  (hp.not.or hq).of_iff (by intro x; simp [imp_iff_not_or])


-- @@ L409-411 expanded
lemma iff {φ ψ : DeltaSymbol.delta-[m].Semiformula V k} (hp : DefinedWithParam P φ)
    (hq : DefinedWithParam Q ψ) :
    DefinedWithParam (fun x ↦ P x ↔ Q x) (LogicalConnective.iff φ ψ) :=
  ((hp.imp hq).and (hq.imp hp)).of_iff <| by intro v; simp [iff_iff_implies_and_implies]


-- @@ L413-420 expanded
lemma ball {P : (Fin (k + 1) → V) → Prop} {φ : ℌ.Semiformula V (k + 1)} (hp : DefinedWithParam P φ)
    (t : Semiterm oRing V k) :
    DefinedWithParam (fun v ↦ ∀ x < t.valm V v id, P (vecCons x v))
      (HierarchySymbol.Semiformula.ball t φ) :=
  match ℌ with
  | SigmaSymbol.sigma-[m] => by intro v; simp [hp.df.iff]
  | PiSymbol.pi-[m] => by intro v; simp [hp.df.iff]
  | DeltaSymbol.delta-[m] => ⟨hp.proper.ball, by intro v; simp [hp.df.iff]⟩


-- @@ L422-429 expanded
lemma bex {P : (Fin (k + 1) → V) → Prop} {φ : ℌ.Semiformula V (k + 1)} (hp : DefinedWithParam P φ)
    (t : Semiterm oRing V k) :
    DefinedWithParam (fun v ↦ ∃ x < t.valm V v id, P (vecCons x v))
      (HierarchySymbol.Semiformula.bex t φ) :=
  match ℌ with
  | SigmaSymbol.sigma-[m] => by intro v; simp [hp.df.iff]
  | PiSymbol.pi-[m] => by intro v; simp [hp.df.iff]
  | DeltaSymbol.delta-[m] => ⟨hp.proper.bex, by intro v; simp [hp.df.iff]⟩


-- @@ L431-433 expanded
lemma ex {P : (Fin (k + 1) → V) → Prop} {φ : SigmaSymbol.sigma-[m + 1].Semiformula V (k + 1)}
    (hp : DefinedWithParam P φ) : DefinedWithParam (fun v ↦ ∃ x, P (vecCons x v)) φ.ex := by
  intro _; simp [hp.df.iff]


-- @@ L435-437 expanded
lemma all {P : (Fin (k + 1) → V) → Prop} {φ : PiSymbol.pi-[m + 1].Semiformula V (k + 1)}
    (hp : DefinedWithParam P φ) : DefinedWithParam (fun v ↦ ∀ x, P (vecCons x v)) φ.all := by
  intro _; simp [hp.df.iff]


-- @@ L439-439 verbatim
end DefinedWithParam


-- @@ L441-441 verbatim
namespace BoldfaceRel


-- @@ L443-444 expanded
@[simp]
instance eq : ℌ.BoldfaceRel (Eq : V → V → Prop) :=
  Defined.to_definable_oRing₀
    (.mkSigma (Semiformula.Operator.operator Operator.Eq.eq ![#0, #1]) (by simp)) (by intro _; simp)


-- @@ L446-447 expanded
@[simp]
instance lt : ℌ.BoldfaceRel (LT.lt : V → V → Prop) :=
  Defined.to_definable_oRing₀
    (.mkSigma (Semiformula.Operator.operator Operator.LT.lt ![#0, #1]) (by simp)) (by intro _; simp)


-- @@ L449-450 expanded
@[simp]
instance le [ModelsTheory V PeanoMinus] : ℌ.BoldfaceRel (LE.le : V → V → Prop) :=
  Defined.to_definable_oRing₀
    (.mkSigma (Semiformula.Operator.operator Operator.LE.le ![#0, #1]) (by simp)) (by intro _; simp)


-- @@ L452-452 verbatim
end BoldfaceRel


-- @@ L454-454 verbatim
namespace BoldfaceFunction₂


-- @@ L456-457 expanded
instance add : ℌ.BoldfaceFunction₂ ((· + ·) : V → V → V) :=
  Defined.to_definable_oRing₀
    (.mkSigma
      (Semiformula.Operator.operator Operator.Eq.eq
        ![#0, Semiterm.Operator.Add.add.operator ![#1, #2]])
      (by simp))
    (by intro _; simp)


-- @@ L459-460 expanded
instance mul : ℌ.BoldfaceFunction₂ ((· * ·) : V → V → V) :=
  Defined.to_definable_oRing₀
    (.mkSigma
      (Semiformula.Operator.operator Operator.Eq.eq
        ![#0, Semiterm.Operator.Mul.mul.operator ![#1, #2]])
      (by simp))
    (by intro _; simp)


-- @@ L462-463 expanded
instance hAdd : ℌ.BoldfaceFunction₂ (HAdd.hAdd : V → V → V) :=
  Defined.to_definable_oRing₀
    (.mkSigma
      (Semiformula.Operator.operator Operator.Eq.eq
        ![#0, Semiterm.Operator.Add.add.operator ![#1, #2]])
      (by simp))
    (by intro _; simp)


-- @@ L465-466 expanded
instance hMul : ℌ.BoldfaceFunction₂ (HMul.hMul : V → V → V) :=
  Defined.to_definable_oRing₀
    (.mkSigma
      (Semiformula.Operator.operator Operator.Eq.eq
        ![#0, Semiterm.Operator.Mul.mul.operator ![#1, #2]])
      (by simp))
    (by intro _; simp)


-- @@ L468-468 verbatim
end BoldfaceFunction₂


-- @@ L470-470 verbatim
namespace Boldface


-- @@ L472-477 expanded
lemma mkPolarity {P : (Fin k → V) → Prop} {Γ : Polarity} (φ : Semiformula oRing V k)
    (hp : Hierarchy Γ m φ) (hP : ∀ v, P v ↔ Semiformula.Evalm V v id φ) : Γ-[m].Boldface P :=
  match Γ with
  | SigmaSymbol.sigma => ⟨.mkSigma φ hp, by intro v; simp [hP]⟩
  | PiSymbol.pi => ⟨.mkPi φ hp, by intro v; simp [hP]⟩


-- @@ L479-480 verbatim
lemma of_iff (H : ℌ.Boldface Q) (h : ∀ x, P x ↔ Q x) : ℌ.Boldface P := by
  rwa [show P = Q from by funext v; simp [h]]


-- @@ L482-482 verbatim
lemma of_oRing (h : ℌ.Boldface P) : ℌ.Boldface P := by rcases h with ⟨φ, hP⟩; exact ⟨φ.emb, hP.emb⟩


-- @@ L484-490 expanded
lemma of_delta (h : DeltaSymbol.delta-[m].Boldface P) : Γ-[m].Boldface P :=
  by
  rcases h with ⟨φ, h⟩
  match Γ with
  | SigmaSymbol.sigma =>
    exact ⟨φ.sigma, by intro v; simp [HierarchySymbol.Semiformula.val_sigma, h.df.iff]⟩
  | PiSymbol.pi =>
    exact ⟨φ.pi, by intro v; simp [← h.proper v, HierarchySymbol.Semiformula.val_sigma, h.df.iff]⟩
  | DeltaSymbol.delta => exact ⟨φ, h⟩


-- @@ L492-492 expanded
instance [DeltaSymbol.delta-[m].Boldface P] (Γ) : Γ-[m].Boldface P :=
  of_delta inferInstance


-- @@ L494-500 expanded
lemma of_sigma_of_pi (hσ : SigmaSymbol.sigma-[m].Boldface P) (hπ : PiSymbol.pi-[m].Boldface P) :
    Γ-[m].Boldface P :=
  match Γ with
  | SigmaSymbol.sigma => hσ
  | PiSymbol.pi => hπ
  | DeltaSymbol.delta => by
    rcases hσ with ⟨φ, hp⟩; rcases hπ with ⟨ψ, hq⟩
    exact ⟨.mkDelta φ ψ, by intro v; simp [hp.df.iff, hq.df.iff], by intro v; simp [hp.df.iff]⟩


-- @@ L502-503 verbatim
lemma of_zero (h : Γ'-[0].Boldface P) : ℌ.Boldface P := by
  rcases h with ⟨⟨φ, hp⟩⟩; exact hp.to_definable₀


-- @@ L505-506 verbatim
lemma of_deltaOne (h : Dlt1.Boldface P) {Γ m} : Γ-[m + 1].Boldface P := by
  rcases h with ⟨⟨φ, hp⟩⟩; exact hp.to_definable_deltaOne


-- @@ L508-509 expanded
instance [Sg0.Boldface P] (ℌ : HierarchySymbol) : ℌ.Boldface P :=
  Boldface.of_zero (Γ' := SigmaSymbol.sigma) (ℌ := ℌ) inferInstance


-- @@ L511-518 expanded
lemma retraction (h : ℌ.Boldface P) {n} (f : Fin k → Fin n) :
    ℌ.Boldface fun v ↦ P (fun i ↦ v (f i)) :=
  by
  rcases h with ⟨φ, h⟩
  exact
    ⟨φ.rew (Rew.substs (fun i ↦ #(f i))),
      match ℌ with
      | SigmaSymbol.sigma-[_] => by intro; simp [h.df.iff]
      | PiSymbol.pi-[_] => by intro; simp [h.df.iff]
      | DeltaSymbol.delta-[_] => ⟨h.proper.rew _, by intro; simp [h.df.iff]⟩⟩


-- @@ L520-527 expanded
lemma retractiont (h : ℌ.Boldface P) (f : Fin k → Semiterm oRing V n) :
    ℌ.Boldface fun v ↦ P (fun i ↦ Semiterm.valm V v id (f i)) :=
  by
  rcases h with ⟨φ, h⟩
  exact
    ⟨φ.rew (Rew.substs f),
      match ℌ with
      | SigmaSymbol.sigma-[_] => by intro; simp [h.df.iff]
      | PiSymbol.pi-[_] => by intro; simp [h.df.iff]
      | DeltaSymbol.delta-[_] => ⟨h.proper.rew _, by intro; simp [h.df.iff]⟩⟩


-- @@ L529-532 verbatim
@[simp] lemma const {P : Prop} : ℌ.Boldface (fun _ : Fin k → V ↦ P) := of_zero (by
  by_cases hP : P
  · exact ⟨.mkSigma ⊤ (by simp), by intro; simp[hP]⟩
  · exact ⟨.mkSigma ⊥ (by simp), by intro; simp[hP]⟩)


-- @@ L534-537 expanded
lemma and (h₁ : ℌ.Boldface P) (h₂ : ℌ.Boldface Q) : ℌ.Boldface (fun v ↦ P v ∧ Q v) :=
  by
  rcases h₁ with ⟨p₁, h₁⟩; rcases h₂ with ⟨p₂, h₂⟩
  exact ⟨Wedge.wedge p₁ p₂, h₁.and h₂⟩


-- @@ L539-554 verbatim
lemma conj {k l} {P : Fin l → (Fin k → V) → Prop}
    (h : ∀ i, ℌ.Boldface fun w : Fin k → V ↦ P i w) :
    ℌ.Boldface fun v : Fin k → V ↦ ∀ i, P i v := by
  induction l
  case zero => simp
  case succ l ih =>
    suffices ℌ.Boldface fun v : Fin k → V ↦ P 0 v ∧ ∀ i : Fin l, P i.succ v by
      apply of_iff this; intro x
      constructor
      · simp_all
      · rintro ⟨h0, hs⟩
        intro i
        cases i using Fin.cases with
        | zero => exact h0
        | succ i => exact hs i
    apply and (h 0); simp_all


-- @@ L556-559 expanded
lemma or (h₁ : ℌ.Boldface P) (h₂ : ℌ.Boldface Q) : ℌ.Boldface (fun v ↦ P v ∨ Q v) :=
  by
  rcases h₁ with ⟨p₁, h₁⟩; rcases h₂ with ⟨p₂, h₂⟩
  exact ⟨Vee.vee p₁ p₂, h₁.or h₂⟩


-- @@ L561-566 expanded
lemma not (h : Γ.alt-[m].Boldface P) : Γ-[m].Boldface (fun v ↦ ¬P v) := by
  match Γ with
  | SigmaSymbol.sigma => rcases h with ⟨φ, h⟩; exact ⟨φ.negPi, h.negPi⟩
  | PiSymbol.pi => rcases h with ⟨φ, h⟩; exact ⟨φ.negSigma, h.negSigma⟩
  | DeltaSymbol.delta => rcases h with ⟨φ, h⟩; exact ⟨φ.negDelta, h.not⟩


-- @@ L568-578 expanded
lemma imp (h₁ : Γ.alt-[m].Boldface P) (h₂ : Γ-[m].Boldface Q) :
    Γ-[m].Boldface (fun v ↦ P v → Q v) := by
  match Γ with
  | SigmaSymbol.sigma =>
    rcases h₁ with ⟨p₁, h₁⟩; rcases h₂ with ⟨p₂, h₂⟩
    exact ⟨p₁.negPi.or p₂, (h₁.negPi.or h₂).of_iff (fun x ↦ by simp [imp_iff_not_or])⟩
  | PiSymbol.pi =>
    rcases h₁ with ⟨p₁, h₁⟩; rcases h₂ with ⟨p₂, h₂⟩
    exact ⟨p₁.negSigma.or p₂, (h₁.negSigma.or h₂).of_iff (fun x ↦ by simp [imp_iff_not_or])⟩
  | DeltaSymbol.delta => rcases h₁ with ⟨p₁, h₁⟩; rcases h₂ with ⟨p₂, h₂⟩;
    exact ⟨Arrow.arrow p₁ p₂, h₁.imp h₂⟩


-- @@ L580-582 expanded
lemma iff (h₁ : DeltaSymbol.delta-[m].Boldface P) (h₂ : DeltaSymbol.delta-[m].Boldface Q) {Γ} :
    Γ-[m].Boldface (fun v ↦ P v ↔ Q v) :=
  .of_delta
    (by rcases h₁ with ⟨φ, hp⟩; rcases h₂ with ⟨ψ, hq⟩;
      exact ⟨LogicalConnective.iff φ ψ, hp.iff hq⟩)


-- @@ L584-587 expanded
lemma all {P : (Fin k → V) → V → Prop}
    (h : PiSymbol.pi-[s + 1].Boldface (fun w ↦ P (w ·.succ) (w 0))) :
    PiSymbol.pi-[s + 1].Boldface (fun v ↦ ∀ x, P v x) :=
  by
  rcases h with ⟨φ, hp⟩
  exact ⟨.mkPi (UnivQuantifier.univ φ.val) (by simp), by intro v; simp [hp.df.iff]⟩


-- @@ L589-592 expanded
lemma ex {P : (Fin k → V) → V → Prop}
    (h : SigmaSymbol.sigma-[s + 1].Boldface (fun w ↦ P (w ·.succ) (w 0))) :
    SigmaSymbol.sigma-[s + 1].Boldface (fun v ↦ ∃ x, P v x) :=
  by
  rcases h with ⟨φ, hp⟩
  exact ⟨.mkSigma (ExQuantifier.ex φ.val) (by simp), by intro v; simp [hp.df.iff]⟩


-- @@ L594-595 verbatim
lemma equal' (i j : Fin k) : ℌ.Boldface fun v : Fin k → V ↦ v i = v j := by
  simpa using retraction BoldfaceRel.eq ![i, j]


-- @@ L597-607 expanded
lemma of_sigma {f : (Fin k → V) → V} (h : SigmaSymbol.sigma-[m].BoldfaceFunction f) {Γ} :
    Γ-[m].BoldfaceFunction f := by
  cases m with
  | zero => exact of_zero h
  | succ m =>
    apply of_sigma_of_pi
    · exact h
    · have : PiSymbol.pi-[m + 1].Boldface fun v ↦ ∀ y, y = f (v ·.succ) → v 0 = y :=
        all <|
          imp (by simpa using retraction h (vecCons 0 (·.succ.succ))) (by simpa using equal' 1 0)
      exact of_iff this (fun v ↦ by simp)


-- @@ L609-633 expanded
lemma exVec {k l} {P : (Fin k → V) → (Fin l → V) → Prop}
    (h :
      SigmaSymbol.sigma-[m + 1].Boldface fun w : Fin (k + l) → V ↦
        P (fun i ↦ w (i.castAdd l)) (fun j ↦ w (j.natAdd k))) :
    SigmaSymbol.sigma-[m + 1].Boldface fun v : Fin k → V ↦ ∃ ys : Fin l → V, P v ys :=
  by
  induction l generalizing k
  case zero => simpa [Matrix.empty_eq] using h
  case succ l
    ih =>
    suffices
      SigmaSymbol.sigma-[m + 1].Boldface fun v : Fin k → V ↦
        ∃ y, ∃ ys : Fin l → V, P v (vecCons y ys)
      by
      apply of_iff this; intro x
      constructor
      · rintro ⟨ys, h⟩; exact ⟨ys 0, (ys ·.succ), by simpa using h⟩
      · rintro ⟨y, ys, h⟩; exact ⟨_, h⟩
    apply ex; apply ih
    let g : Fin (k + (l + 1)) → Fin (k + 1 + l) :=
      Matrix.vecAppend rfl (fun x ↦ x.succ.castAdd l)
        (vecCons (Fin.castAdd l 0) fun j ↦ j.natAdd (k + 1))
    exact
      of_iff (retraction h g)
        (by
          intro v; simp only [g]
          apply iff_of_eq; congr
          · ext i; congr 1; ext; simp [Matrix.vecAppend_eq_ite]
          · ext i
            cases i using Fin.cases with
            | zero => simp only [Matrix.vecCons_zero]; congr 1; ext; simp [Matrix.vecAppend_eq_ite]
            | succ i => simp only [Matrix.vecCons_succ]; congr 1; ext;
              simp [Matrix.vecAppend_eq_ite])


-- @@ L635-659 expanded
lemma allVec {k l} {P : (Fin k → V) → (Fin l → V) → Prop}
    (h :
      PiSymbol.pi-[m + 1].Boldface fun w : Fin (k + l) → V ↦
        P (fun i ↦ w (i.castAdd l)) (fun j ↦ w (j.natAdd k))) :
    PiSymbol.pi-[m + 1].Boldface fun v : Fin k → V ↦ ∀ ys : Fin l → V, P v ys :=
  by
  induction l generalizing k
  case zero => simpa [Matrix.empty_eq] using h
  case succ l
    ih =>
    suffices
      PiSymbol.pi-[m + 1].Boldface fun v : Fin k → V ↦ ∀ y, ∀ ys : Fin l → V, P v (vecCons y ys)
      by
      apply of_iff this; intro x
      constructor
      · intro h y ys; apply h
      · intro h ys; simpa using h (ys 0) (ys ·.succ)
    apply all; apply ih
    let g : Fin (k + (l + 1)) → Fin (k + 1 + l) :=
      Matrix.vecAppend rfl (fun x ↦ x.succ.castAdd l)
        (vecCons (Fin.castAdd l 0) fun j ↦ j.natAdd (k + 1))
    exact
      of_iff (retraction h g)
        (by
          intro v; simp only [g]
          apply iff_of_eq; congr
          · ext i; congr 1; ext; simp [Matrix.vecAppend_eq_ite]
          · ext i
            cases i using Fin.cases with
            | zero => simp only [Matrix.vecCons_zero]; congr 1; ext; simp [Matrix.vecAppend_eq_ite]
            | succ i => simp only [Matrix.vecCons_succ]; congr 1; ext;
              simp [Matrix.vecAppend_eq_ite])


-- @@ L661-676 expanded
private lemma substitution_sigma {f : Fin k → (Fin l → V) → V}
    (hP : SigmaSymbol.sigma-[m + 1].Boldface P)
    (hf : ∀ i, SigmaSymbol.sigma-[m + 1].BoldfaceFunction (f i)) :
    SigmaSymbol.sigma-[m + 1].Boldface fun z ↦ P (fun i ↦ f i z) :=
  by
  have : SigmaSymbol.sigma-[m + 1].Boldface fun z ↦ ∃ ys : Fin k → V, (∀ i, ys i = f i z) ∧ P ys :=
    by
    apply exVec; apply and
    · apply conj; intro i
      simpa using retraction (of_sigma (hf i)) (vecCons (i.natAdd l) fun i ↦ i.castAdd k)
    · exact retraction hP (Fin.natAdd l)
  exact
    of_iff this <| by
      intro v
      constructor
      · intro hP
        exact ⟨(f · v), by simp, hP⟩
      · rintro ⟨ys, hys, hP⟩
        have : ys = fun i ↦ f i v := funext hys
        rcases this; exact hP


-- @@ L678-692 expanded
private lemma substitution_pi {f : Fin k → (Fin l → V) → V} (hP : PiSymbol.pi-[m + 1].Boldface P)
    (hf : ∀ i, SigmaSymbol.sigma-[m + 1].BoldfaceFunction (f i)) :
    PiSymbol.pi-[m + 1].Boldface fun z ↦ P (fun i ↦ f i z) :=
  by
  have : PiSymbol.pi-[m + 1].Boldface fun z ↦ ∀ ys : Fin k → V, (∀ i, ys i = f i z) → P ys :=
    by
    apply allVec; apply imp
    · apply conj; intro i
      simpa using retraction (of_sigma (hf i)) (vecCons (i.natAdd l) fun i ↦ i.castAdd k)
    · exact retraction hP (Fin.natAdd l)
  exact
    of_iff this <| by
      intro v
      constructor
      · intro h ys e
        have : ys = (f · v) := funext e
        rcases this; exact h
      · intro h; apply h _ (by simp)


-- @@ L694-700 expanded
lemma substitution {f : Fin k → (Fin l → V) → V} (hP : Γ-[m + 1].Boldface P)
    (hf : ∀ i, SigmaSymbol.sigma-[m + 1].BoldfaceFunction (f i)) :
    Γ-[m + 1].Boldface fun z ↦ P (fun i ↦ f i z) :=
  match Γ with
  | SigmaSymbol.sigma => substitution_sigma hP hf
  | PiSymbol.pi => substitution_pi hP hf
  | DeltaSymbol.delta =>
    of_sigma_of_pi (substitution_sigma (of_delta hP) hf) (substitution_pi (of_delta hP) hf)


-- @@ L702-702 verbatim
end Boldface


-- @@ L704-708 expanded
lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.BoldfacePred.comp {P : V → Prop} {k}
    {f : (Fin k → V) → V} (hP : Γ-[m + 1].BoldfacePred P)
    (hf : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f) : Γ-[m + 1].Boldface (fun v ↦ P (f v)) :=
  Boldface.substitution (f := ![f]) hP (by simpa using hf)


-- @@ L710-715 expanded
lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.BoldfaceRel.comp {P : V → V → Prop} {k}
    {f g : (Fin k → V) → V} (hP : Γ-[m + 1].BoldfaceRel P)
    (hf : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f)
    (hg : SigmaSymbol.sigma-[m + 1].BoldfaceFunction g) :
    Γ-[m + 1].Boldface fun v ↦ P (f v) (g v) :=
  Boldface.substitution (f := ![f, g]) hP (by simp [forall_fin_iff_zero_and_forall_succ, hf, hg])


-- @@ L717-725 expanded
lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.BoldfaceRel₃.comp {k} {P : V → V → V → Prop}
    {f₁ f₂ f₃ : (Fin k → V) → V} (hP : Γ-[m + 1].BoldfaceRel₃ P)
    (hf₁ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f₁)
    (hf₂ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f₂)
    (hf₃ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f₃) :
    Γ-[m + 1].Boldface (fun v ↦ P (f₁ v) (f₂ v) (f₃ v)) :=
  Boldface.substitution (f := ![f₁, f₂, f₃]) hP
    (by simp [forall_fin_iff_zero_and_forall_succ, hf₁, hf₂, hf₃])


-- @@ L727-735 expanded
lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.BoldfaceRel₄.comp {k} {P : V → V → V → V → Prop}
    {f₁ f₂ f₃ f₄ : (Fin k → V) → V} (hP : Γ-[m + 1].BoldfaceRel₄ P)
    (hf₁ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f₁)
    (hf₂ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f₂)
    (hf₃ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f₃)
    (hf₄ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f₄) :
    Γ-[m + 1].Boldface (fun v ↦ P (f₁ v) (f₂ v) (f₃ v) (f₄ v)) :=
  Boldface.substitution (f := ![f₁, f₂, f₃, f₄]) hP
    (by simp [forall_fin_iff_zero_and_forall_succ, hf₁, hf₂, hf₃, hf₄])


-- @@ L737-747 expanded
lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.BoldfaceRel₅.comp {k}
    {P : V → V → V → V → V → Prop} {f₁ f₂ f₃ f₄ f₅ : (Fin k → V) → V}
    (hP : Γ-[m + 1].BoldfaceRel₅ P) (hf₁ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f₁)
    (hf₂ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f₂)
    (hf₃ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f₃)
    (hf₄ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f₄)
    (hf₅ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f₅) :
    Γ-[m + 1].Boldface (fun v ↦ P (f₁ v) (f₂ v) (f₃ v) (f₄ v) (f₅ v)) :=
  Boldface.substitution (f := ![f₁, f₂, f₃, f₄, f₅]) hP
    (by simp [forall_fin_iff_zero_and_forall_succ, hf₁, hf₂, hf₃, hf₄, hf₅])


-- @@ L749-749 verbatim
namespace Boldface


-- @@ L751-754 expanded
lemma comp₁ {k} {P : V → Prop} {f : (Fin k → V) → V} [Γ-[m + 1].BoldfacePred P]
    (hf : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f) : Γ-[m + 1].Boldface fun v ↦ P (f v) :=
  BoldfacePred.comp inferInstance hf


-- @@ L756-760 expanded
lemma comp₂ {k} {P : V → V → Prop} {f g : (Fin k → V) → V} [Γ-[m + 1].BoldfaceRel P]
    (hf : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f)
    (hg : SigmaSymbol.sigma-[m + 1].BoldfaceFunction g) :
    Γ-[m + 1].Boldface (fun v ↦ P (f v) (g v)) :=
  BoldfaceRel.comp inferInstance hf hg


-- @@ L762-767 expanded
lemma comp₃ {k} {P : V → V → V → Prop} {f₁ f₂ f₃ : (Fin k → V) → V} [Γ-[m + 1].BoldfaceRel₃ P]
    (hf₁ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f₁)
    (hf₂ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f₂)
    (hf₃ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f₃) :
    Γ-[m + 1].Boldface (fun v ↦ P (f₁ v) (f₂ v) (f₃ v)) :=
  BoldfaceRel₃.comp inferInstance hf₁ hf₂ hf₃


-- @@ L769-774 expanded
lemma comp₄ {k} {P : V → V → V → V → Prop} {f₁ f₂ f₃ f₄ : (Fin k → V) → V}
    [Γ-[m + 1].BoldfaceRel₄ P] (hf₁ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f₁)
    (hf₂ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f₂)
    (hf₃ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f₃)
    (hf₄ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f₄) :
    Γ-[m + 1].Boldface (fun v ↦ P (f₁ v) (f₂ v) (f₃ v) (f₄ v)) :=
  BoldfaceRel₄.comp inferInstance hf₁ hf₂ hf₃ hf₄


-- @@ L776-782 expanded
lemma comp₅ {k} {P : V → V → V → V → V → Prop} {f₁ f₂ f₃ f₄ f₅ : (Fin k → V) → V}
    [Γ-[m + 1].BoldfaceRel₅ P] (hf₁ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f₁)
    (hf₂ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f₂)
    (hf₃ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f₃)
    (hf₄ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f₄)
    (hf₅ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f₅) :
    Γ-[m + 1].Boldface (fun v ↦ P (f₁ v) (f₂ v) (f₃ v) (f₄ v) (f₅ v)) :=
  BoldfaceRel₅.comp inferInstance hf₁ hf₂ hf₃ hf₄ hf₅


-- @@ L784-784 verbatim
end Boldface


-- @@ L786-786 verbatim
section «lp_section_3»


-- @@ L788-788 verbatim
variable {ℌ : HierarchySymbol}


-- @@ L790-792 verbatim
lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.BoldfacePred.of_iff {P Q : V → Prop}
    (H : ℌ.BoldfacePred Q) (h : ∀ x, P x ↔ Q x) : ℌ.BoldfacePred P := by
  rwa [show P = Q from by funext v; simp [h]]


-- @@ L794-796 verbatim
instance _root_.LO.FirstOrder.Arith.HierarchySymbol.BoldfaceFunction₁.graph {f : V → V} [h :
    ℌ.BoldfaceFunction₁ f] :
  ℌ.BoldfaceRel (Function.Graph f) := h


-- @@ L798-800 verbatim
instance _root_.LO.FirstOrder.Arith.HierarchySymbol.BoldfaceFunction₂.graph {f : V → V → V} [h :
    ℌ.BoldfaceFunction₂ f] :
  ℌ.BoldfaceRel₃ (Function.Graph₂ f) := h


-- @@ L802-804 verbatim
instance _root_.LO.FirstOrder.Arith.HierarchySymbol.BoldfaceFunction₃.graph {f : V → V → V → V} [h :
    ℌ.BoldfaceFunction₃ f] :
  ℌ.BoldfaceRel₄ (Function.Graph₃ f) := h


-- @@ L806-806 verbatim
end «lp_section_3»


-- @@ L808-808 verbatim
namespace BoldfaceFunction


-- @@ L810-810 verbatim
variable {ℌ : HierarchySymbol}


-- @@ L812-825 expanded
lemma graph_delta {k} {f : (Fin k → V) → V} (h : SigmaSymbol.sigma-[m].BoldfaceFunction f) :
    DeltaSymbol.delta-[m].BoldfaceFunction f :=
  by
  rcases h with ⟨φ, h⟩
  exact
    ⟨φ.graphDelta,
      by
      rcases m with _ | m <;>
        simp only [HierarchySymbol.Semiformula.graphDelta, Semiformula.ProperWithParamOn.of_zero]
      intro e
      simp only [Semiformula.sigma_mkDelta, h.df.iff, Semiformula.pi_mkDelta, Semiformula.val_mkPi,
        Semiformula.eval_all, Nat.succ_eq_add_one, LogicalConnective.HomClass.map_imply,
        Semiformula.eval_substs, Matrix.comp_vecCons', Semiterm.val_bvar, Matrix.vecCons_zero,
        Matrix.vecCons_succ, Semiformula.eval_operator₂, Matrix.cons_val_one, Structure.Eq.eq,
        LogicalConnective.Prop.arrow_eq, forall_eq]
      exact eq_comm, by intro v; simp [h.df.iff]⟩


-- @@ L827-828 expanded
instance {k} {f : (Fin k → V) → V} [h : SigmaSymbol.sigma-[m].BoldfaceFunction f] :
    DeltaSymbol.delta-[m].BoldfaceFunction f :=
  BoldfaceFunction.graph_delta h


-- @@ L830-830 verbatim
instance {k} {f : (Fin k → V) → V} [Sg0.BoldfaceFunction f] : ℌ.BoldfaceFunction f := inferInstance


-- @@ L832-834 verbatim
lemma of_sigmaOne {k} {f : (Fin k → V) → V}
    (h : Sg1.BoldfaceFunction f) {Γ m} : Γ-[m + 1].BoldfaceFunction f :=
      Boldface.of_deltaOne (graph_delta h)


-- @@ L836-837 expanded
@[simp 1100]
lemma var {k} (i : Fin k) : ℌ.BoldfaceFunction (fun v : Fin k → V ↦ v i) :=
  .of_zero (Γ' := SigmaSymbol.sigma)
    ⟨.mkSigma (Semiformula.Operator.operator Operator.Eq.eq ![#0, #i.succ]) (by simp), by intro _;
      simp⟩


-- @@ L839-840 expanded
@[simp]
lemma const {k} (c : V) : ℌ.BoldfaceFunction (fun _ : Fin k → V ↦ c) :=
  .of_zero (Γ' := SigmaSymbol.sigma)
    ⟨.mkSigma (Semiformula.Operator.operator Operator.Eq.eq ![#0, &c]) (by simp), by intro v; simp⟩


-- @@ L842-846 expanded
@[simp]
lemma term_retraction (t : Semiterm oRing V n) (e : Fin n → Fin k) :
    ℌ.BoldfaceFunction fun v : Fin k → V ↦ Semiterm.valm V (fun x ↦ v (e x)) id t :=
  .of_zero (Γ' := SigmaSymbol.sigma)
    ⟨.mkSigma
        (Semiformula.Operator.operator Operator.Eq.eq ![#0, (Rew.substs (fun x ↦ #(e x).succ) t)])
        (by simp),
      by intro v; simp [Semiterm.val_substs]⟩


-- @@ L848-851 expanded
@[simp 1100]
lemma term (t : Semiterm oRing V k) :
    ℌ.BoldfaceFunction fun v : Fin k → V ↦ Semiterm.valm V v id t :=
  .of_zero (Γ' := SigmaSymbol.sigma)
    ⟨.mkSigma (Semiformula.Operator.operator Operator.Eq.eq ![#0, (Rew.bShift t)]) (by simp), by
      intro v; simp [Semiterm.val_bShift']⟩


-- @@ L853-854 verbatim
lemma of_eq {f : (Fin k → V) → V} (g) (h : ∀ v, f v = g v) (H : ℌ.BoldfaceFunction f) :
    ℌ.BoldfaceFunction g := by rwa [show g = f from by funext v; simp [h]]


-- @@ L856-858 expanded
lemma retraction {n k} {f : (Fin k → V) → V} (hf : ℌ.BoldfaceFunction f) (e : Fin k → Fin n) :
    ℌ.BoldfaceFunction fun v ↦ f (fun i ↦ v (e i)) := by
  have := Boldface.retraction (n := n + 1) hf (vecCons 0 fun i ↦ (e i).succ); simp_all


-- @@ L860-864 expanded
lemma retractiont {n k} {f : (Fin k → V) → V} (hf : ℌ.BoldfaceFunction f)
    (t : Fin k → Semiterm oRing V n) :
    ℌ.BoldfaceFunction fun v ↦ f (fun i ↦ Semiterm.valm V v id (t i)) :=
  by
  have := Boldface.retractiont (n := n + 1) hf (vecCons #0 fun i ↦ Rew.bShift (t i)); simp at this
  exact this.of_iff (by intro x; simp [Semiterm.val_bShift'])


-- @@ L866-867 verbatim
lemma rel {f : (Fin k → V) → V} (h : ℌ.BoldfaceFunction f) :
  ℌ.Boldface (fun v ↦ v 0 = f (v ·.succ)) := h


-- @@ L869-870 verbatim
lemma nth (ℌ : HierarchySymbol) (i : Fin k) : ℌ.BoldfaceFunction fun w : Fin k → V ↦ w i := by
  simp_all


-- @@ L872-879 expanded
lemma substitution {f : Fin k → (Fin l → V) → V} (hF : Γ-[m + 1].BoldfaceFunction F)
    (hf : ∀ i, SigmaSymbol.sigma-[m + 1].BoldfaceFunction (f i)) :
    Γ-[m + 1].BoldfaceFunction fun z ↦ F (fun i ↦ f i z) := by
  simpa using
    Boldface.substitution (f := vecCons (· 0) fun i w ↦ f i (w ·.succ)) hF <|
      by
      intro i
      cases i using Fin.cases with
      | zero => simp
      | succ i => simpa using Boldface.retraction (hf i) (vecCons 0 (·.succ.succ))


-- @@ L881-881 verbatim
end BoldfaceFunction


-- @@ L883-887 expanded
lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.BoldfaceFunction₁.comp {k} {F : V → V}
    {f : (Fin k → V) → V} (hF : Γ-[m + 1].BoldfaceFunction₁ F)
    (hf : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f) :
    Γ-[m + 1].BoldfaceFunction (fun v ↦ F (f v)) :=
  BoldfaceFunction.substitution (f := ![f]) hF (by simp [hf])


-- @@ L889-895 expanded
lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.BoldfaceFunction₂.comp {k} {F : V → V → V}
    {f₁ f₂ : (Fin k → V) → V} (hF : Γ-[m + 1].BoldfaceFunction₂ F)
    (hf₁ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f₁)
    (hf₂ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f₂) :
    Γ-[m + 1].BoldfaceFunction (fun v ↦ F (f₁ v) (f₂ v)) :=
  BoldfaceFunction.substitution (f := ![f₁, f₂]) hF
    (by simp [forall_fin_iff_zero_and_forall_succ, *])


-- @@ L897-905 expanded
lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.BoldfaceFunction₃.comp {k} {F : V → V → V → V}
    {f₁ f₂ f₃ : (Fin k → V) → V} (hF : Γ-[m + 1].BoldfaceFunction₃ F)
    (hf₁ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f₁)
    (hf₂ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f₂)
    (hf₃ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f₃) :
    Γ-[m + 1].BoldfaceFunction (fun v ↦ F (f₁ v) (f₂ v) (f₃ v)) :=
  BoldfaceFunction.substitution (f := ![f₁, f₂, f₃]) hF
    (by simp [forall_fin_iff_zero_and_forall_succ, *])


-- @@ L907-915 expanded
lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.BoldfaceFunction₄.comp {k} {F : V → V → V → V → V}
    {f₁ f₂ f₃ f₄ : (Fin k → V) → V} (hF : Γ-[m + 1].BoldfaceFunction₄ F)
    (hf₁ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f₁)
    (hf₂ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f₂)
    (hf₃ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f₃)
    (hf₄ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f₄) :
    Γ-[m + 1].BoldfaceFunction (fun v ↦ F (f₁ v) (f₂ v) (f₃ v) (f₄ v)) :=
  BoldfaceFunction.substitution (f := ![f₁, f₂, f₃, f₄]) hF
    (by simp [forall_fin_iff_zero_and_forall_succ, *])


-- @@ L917-926 expanded
lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.BoldfaceFunction₅.comp {k}
    {F : V → V → V → V → V → V} {f₁ f₂ f₃ f₄ f₅ : (Fin k → V) → V}
    (hF : Γ-[m + 1].BoldfaceFunction₅ F) (hf₁ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f₁)
    (hf₂ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f₂)
    (hf₃ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f₃)
    (hf₄ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f₄)
    (hf₅ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f₅) :
    Γ-[m + 1].BoldfaceFunction (fun v ↦ F (f₁ v) (f₂ v) (f₃ v) (f₄ v) (f₅ v)) :=
  BoldfaceFunction.substitution (f := ![f₁, f₂, f₃, f₄, f₅]) hF
    (by simp [forall_fin_iff_zero_and_forall_succ, *])


-- @@ L928-928 verbatim
namespace BoldfaceFunction


-- @@ L930-933 expanded
lemma comp₁ {k} {f : V → V} [Γ-[m + 1].BoldfaceFunction₁ f] {g : (Fin k → V) → V}
    (hg : SigmaSymbol.sigma-[m + 1].BoldfaceFunction g) :
    Γ-[m + 1].BoldfaceFunction (fun v ↦ f (g v)) :=
  BoldfaceFunction₁.comp inferInstance hg


-- @@ L935-939 expanded
lemma comp₂ {k} {f : V → V → V} [Γ-[m + 1].BoldfaceFunction₂ f] {g₁ g₂ : (Fin k → V) → V}
    (hg₁ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction g₁)
    (hg₂ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction g₂) :
    Γ-[m + 1].BoldfaceFunction (fun v ↦ f (g₁ v) (g₂ v)) :=
  BoldfaceFunction₂.comp inferInstance hg₁ hg₂


-- @@ L941-946 expanded
lemma comp₃ {k} {f : V → V → V → V} [Γ-[m + 1].BoldfaceFunction₃ f] {g₁ g₂ g₃ : (Fin k → V) → V}
    (hg₁ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction g₁)
    (hg₂ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction g₂)
    (hg₃ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction g₃) :
    Γ-[m + 1].BoldfaceFunction (fun v ↦ f (g₁ v) (g₂ v) (g₃ v)) :=
  BoldfaceFunction₃.comp inferInstance hg₁ hg₂ hg₃


-- @@ L948-953 expanded
lemma comp₄ {k} {f : V → V → V → V → V} [Γ-[m + 1].BoldfaceFunction₄ f]
    {g₁ g₂ g₃ g₄ : (Fin k → V) → V} (hg₁ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction g₁)
    (hg₂ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction g₂)
    (hg₃ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction g₃)
    (hg₄ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction g₄) :
    Γ-[m + 1].BoldfaceFunction (fun v ↦ f (g₁ v) (g₂ v) (g₃ v) (g₄ v)) :=
  BoldfaceFunction₄.comp inferInstance hg₁ hg₂ hg₃ hg₄


-- @@ L955-961 expanded
lemma comp₅ {k} {f : V → V → V → V → V → V} [Γ-[m + 1].BoldfaceFunction₅ f]
    {g₁ g₂ g₃ g₄ g₅ : (Fin k → V) → V} (hg₁ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction g₁)
    (hg₂ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction g₂)
    (hg₃ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction g₃)
    (hg₄ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction g₄)
    (hg₅ : SigmaSymbol.sigma-[m + 1].BoldfaceFunction g₅) :
    Γ-[m + 1].BoldfaceFunction (fun v ↦ f (g₁ v) (g₂ v) (g₃ v) (g₄ v) (g₅ v)) :=
  BoldfaceFunction₅.comp inferInstance hg₁ hg₂ hg₃ hg₄ hg₅


-- @@ L963-963 verbatim
end BoldfaceFunction


-- @@ L965-965 verbatim
namespace Boldface


-- @@ L967-984 expanded
lemma ball_lt {Γ} {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f)
    (h : Γ-[m + 1].Boldface (fun w ↦ P (w ·.succ) (w 0))) :
    Γ-[m + 1].Boldface (fun v ↦ ∀ x < f v, P v x) :=
  by
  rcases hf with ⟨bf, hbf⟩
  rcases h with ⟨φ, hp⟩
  match Γ with
  | SigmaSymbol.sigma =>
    exact
      ⟨.mkSigma
          (ExQuantifier.ex
            (Wedge.wedge bf.val
              (ball (Semiformula.Operator.operator Operator.LT.lt ![#0, #1])
                (LO.FirstOrder.Rewriting.substitute φ.val (vecCons #0 (#·.succ.succ))))))
          (by simp),
        by intro v; simp [hbf.df.iff, hp.df.iff]⟩
  | PiSymbol.pi =>
    exact
      ⟨.mkPi
          (UnivQuantifier.univ
            (Arrow.arrow bf.val
              (ball (Semiformula.Operator.operator Operator.LT.lt ![#0, #1])
                (LO.FirstOrder.Rewriting.substitute φ.val (vecCons #0 (#·.succ.succ))))))
          (by simp),
        by intro v; simp [hbf.df.iff, hp.df.iff]⟩
  | DeltaSymbol.delta =>
    exact
      .of_sigma_of_pi
        ⟨.mkSigma
            (ExQuantifier.ex
              (Wedge.wedge bf.val
                (ball (Semiformula.Operator.operator Operator.LT.lt ![#0, #1])
                  (LO.FirstOrder.Rewriting.substitute φ.sigma.val (vecCons #0 (#·.succ.succ))))))
            (by simp),
          by intro v; simp [hbf.df.iff, hp.df.iff, HierarchySymbol.Semiformula.val_sigma]⟩
        ⟨.mkPi
            (UnivQuantifier.univ
              (Arrow.arrow bf.val
                (ball (Semiformula.Operator.operator Operator.LT.lt ![#0, #1])
                  (LO.FirstOrder.Rewriting.substitute φ.pi.val (vecCons #0 (#·.succ.succ))))))
            (by simp),
          by intro v; simp [hbf.df.iff, hp.df.iff, hp.proper.iff']⟩


-- @@ L986-1003 expanded
lemma bex_lt {Γ} {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f)
    (h : Γ-[m + 1].Boldface (fun w ↦ P (w ·.succ) (w 0))) :
    Γ-[m + 1].Boldface (fun v ↦ ∃ x < f v, P v x) :=
  by
  rcases hf with ⟨bf, hbf⟩
  rcases h with ⟨φ, hp⟩
  match Γ with
  | SigmaSymbol.sigma =>
    exact
      ⟨.mkSigma
          (ExQuantifier.ex
            (Wedge.wedge bf.val
              (bex (Semiformula.Operator.operator Operator.LT.lt ![#0, #1])
                (LO.FirstOrder.Rewriting.substitute φ.val (vecCons #0 (#·.succ.succ))))))
          (by simp),
        by intro v; simp [hbf.df.iff, hp.df.iff]⟩
  | PiSymbol.pi =>
    exact
      ⟨.mkPi
          (UnivQuantifier.univ
            (Arrow.arrow bf.val
              (bex (Semiformula.Operator.operator Operator.LT.lt ![#0, #1])
                (LO.FirstOrder.Rewriting.substitute φ.val (vecCons #0 (#·.succ.succ))))))
          (by simp),
        by intro v; simp [hbf.df.iff, hp.df.iff]⟩
  | DeltaSymbol.delta =>
    exact
      .of_sigma_of_pi
        ⟨.mkSigma
            (ExQuantifier.ex
              (Wedge.wedge bf.val
                (bex (Semiformula.Operator.operator Operator.LT.lt ![#0, #1])
                  (LO.FirstOrder.Rewriting.substitute φ.sigma.val (vecCons #0 (#·.succ.succ))))))
            (by simp),
          by intro v; simp [hbf.df.iff, hp.df.iff, HierarchySymbol.Semiformula.val_sigma]⟩
        ⟨.mkPi
            (UnivQuantifier.univ
              (Arrow.arrow bf.val
                (bex (Semiformula.Operator.operator Operator.LT.lt ![#0, #1])
                  (LO.FirstOrder.Rewriting.substitute φ.pi.val (vecCons #0 (#·.succ.succ))))))
            (by simp),
          by intro v; simp [hbf.df.iff, hp.df.iff, hp.proper.iff']⟩


-- @@ L1005-1010 expanded
lemma ball_le [ModelsTheory V PeanoMinus] {Γ} {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f)
    (h : Γ-[m + 1].Boldface (fun w ↦ P (w ·.succ) (w 0))) :
    Γ-[m + 1].Boldface (fun v ↦ ∀ x ≤ f v, P v x) :=
  by
  have : Γ-[m + 1].Boldface (fun v ↦ ∀ x < f v + 1, P v x) :=
    ball_lt (BoldfaceFunction₂.comp inferInstance hf (BoldfaceFunction.const 1)) h
  exact this.of_iff <| by intro v; simp [lt_succ_iff_le]


-- @@ L1012-1017 expanded
lemma bex_le [ModelsTheory V PeanoMinus] {Γ} {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f)
    (h : Γ-[m + 1].Boldface (fun w ↦ P (w ·.succ) (w 0))) :
    Γ-[m + 1].Boldface (fun v ↦ ∃ x ≤ f v, P v x) :=
  by
  have : Γ-[m + 1].Boldface (fun v ↦ ∃ x < f v + 1, P v x) :=
    bex_lt (BoldfaceFunction₂.comp inferInstance hf (BoldfaceFunction.const 1)) h
  exact this.of_iff <| by intro v; simp [lt_succ_iff_le]


-- @@ L1019-1021 expanded
lemma ball_lt' {Γ} {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f)
    (h : Γ-[m + 1].Boldface (fun w ↦ P (w ·.succ) (w 0))) :
    Γ-[m + 1].Boldface (fun v ↦ ∀ {x}, x < f v → P v x) :=
  ball_lt hf h


-- @@ L1023-1025 expanded
lemma ball_le' [ModelsTheory V PeanoMinus] {Γ} {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f)
    (h : Γ-[m + 1].Boldface (fun w ↦ P (w ·.succ) (w 0))) :
    Γ-[m + 1].Boldface (fun v ↦ ∀ {x}, x ≤ f v → P v x) :=
  ball_le hf h


-- @@ L1027-1027 verbatim
end Boldface


-- @@ L1029-1029 verbatim
end «lp_section_2»


-- @@ L1031-1031 verbatim
end HierarchySymbol

-- @@ L1032-1032 verbatim
end Arith


-- @@ L1034-1034 verbatim
end FirstOrder

-- @@ L1035-1035 verbatim
end LO
