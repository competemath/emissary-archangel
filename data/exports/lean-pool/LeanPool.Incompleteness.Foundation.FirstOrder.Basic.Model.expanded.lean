/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.FirstOrder.Basic.Operator
public import LeanPool.Incompleteness.Foundation.FirstOrder.Basic.Semantics.Elementary
import Mathlib.Tactic.Bound.Init


-- @@ L12-12 verbatim
/-! # Model -/


-- @@ L14-14 verbatim
@[expose] public section


-- @@ L16-16 verbatim
namespace LO


-- @@ L18-18 verbatim
namespace FirstOrder


-- @@ L20-20 verbatim
namespace Structure


-- @@ L22-25 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
structure Model (L : Language) (M : Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  intro : M


-- @@ L27-27 verbatim
namespace Model


-- @@ L29-29 verbatim
variable [Structure L M]


-- @@ L31-36 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def equiv (L : Language) (M : Type*) : M ≃ Model L M where
  toFun := fun x => ⟨x⟩
  invFun := Model.intro
  left_inv := by intro x; simp
  right_inv := by rintro ⟨x⟩; simp


-- @@ L38-38 verbatim
instance : Structure L (Model L M) := Structure.ofEquiv (equiv L M)


-- @@ L40-40 verbatim
instance [h : Nonempty M] : Nonempty (Model L M) := by rcases h with ⟨x⟩; exact ⟨equiv L M x⟩


-- @@ L42-43 expanded
lemma elementaryEquiv (L : Language) (M : Type*) [Nonempty M] [Structure L M] :
    ElementaryEquiv L M (Model L M) :=
  ElementaryEquiv.ofEquiv _


-- @@ L45-45 verbatim
section «lp_section_1»


-- @@ L47-47 verbatim
open Semiterm Semiformula


-- @@ L49-49 verbatim
instance [Operator.Zero L] : Zero (Model L M) := ⟨(@Operator.Zero.zero L _).val ![]⟩


-- @@ L51-51 verbatim
instance [Operator.Zero L] : Structure.Zero L (Model L M) := ⟨rfl⟩


-- @@ L53-53 verbatim
instance [Operator.One L] : One (Model L M) := ⟨(@Operator.One.one L _).val ![]⟩


-- @@ L55-55 verbatim
instance [Operator.One L] : Structure.One L (Model L M) := ⟨rfl⟩


-- @@ L57-57 verbatim
instance [Operator.Add L] : Add (Model L M) := ⟨fun x y => (@Operator.Add.add L _).val ![x, y]⟩


-- @@ L59-59 verbatim
instance [Operator.Add L] : Structure.Add L (Model L M) := ⟨fun _ _ => rfl⟩


-- @@ L61-61 verbatim
instance [Operator.Mul L] : Mul (Model L M) := ⟨fun x y => (@Operator.Mul.mul L _).val ![x, y]⟩


-- @@ L63-63 verbatim
instance [Operator.Mul L] : Structure.Mul L (Model L M) := ⟨fun _ _ => rfl⟩


-- @@ L65-65 verbatim
instance [Operator.Exp L] : Exp (Model L M) := ⟨fun x => (@Operator.Exp.exp L _).val ![x]⟩


-- @@ L67-67 verbatim
instance [Operator.Exp L] : Structure.Exp L (Model L M) := ⟨fun _ => rfl⟩


-- @@ L69-70 verbatim
instance [Operator.Eq L] [Structure.Eq L M] : Structure.Eq L (Model L M) :=
  ⟨fun x y => by simp [operator_val_ofEquiv_iff]⟩


-- @@ L72-72 verbatim
instance [Operator.LT L] : LT (Model L M) := ⟨fun x y => (@Operator.LT.lt L _).val ![x, y]⟩


-- @@ L74-74 verbatim
instance [Operator.LT L] : Structure.LT L (Model L M) := ⟨fun _ _ => iff_of_eq rfl⟩


-- @@ L76-77 verbatim
instance [Operator.Mem L] : Membership (Model L M) (Model L M) :=
  ⟨fun x y => (@Operator.Mem.mem L _).val ![y, x]⟩


-- @@ L79-79 verbatim
instance [Operator.Mem L] : Structure.Mem L (Model L M) := ⟨fun _ _ => iff_of_eq rfl⟩


-- @@ L81-81 verbatim
end «lp_section_1»


-- @@ L83-83 verbatim
end Model


-- @@ L85-85 verbatim
section «lp_section_2»


-- @@ L87-87 verbatim
variable (F : ℕ → Type*) {M : Type*} (fF : {k : ℕ} → (f : F k) → (Fin k → M) → M)


-- @@ L89-93 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
@[reducible]
def ofFunc : Structure (Language.ofFunc F) M where
  func := fun _ f v => fF f v
  rel  := fun _ r _ => r.elim


-- @@ L95-95 verbatim
lemma func_ofFunc {k} (f : F k) (v : Fin k → M) : (ofFunc F fF).func f v = fF f v := rfl


-- @@ L97-97 verbatim
end «lp_section_2»


-- @@ L99-99 verbatim
section «lp_section_3»


-- @@ L101-101 verbatim
variable (L₁ : Language.{u₁}) (L₂ : Language.{u₂}) (M : Type*) [str₁ : Structure L₁ M]

-- @@ L102-102 verbatim
variable [str₂ : Structure L₂ M]


-- @@ L104-112 verbatim
instance add : Structure (L₁.add L₂) M where
  func := fun _ f v =>
    match f with
    | Sum.inl f => func f v
    | Sum.inr f => func f v
  rel := fun _ r v =>
    match r with
    | Sum.inl r => rel r v
    | Sum.inr r => rel r v


-- @@ L114-114 verbatim
variable {L₁ L₂ M}


-- @@ L116-117 verbatim
@[simp] lemma func_sigma_inl {k} (f : L₁.Func k) (v : Fin k → M) :
    (add L₁ L₂ M).func (Sum.inl f) v = func f v := rfl


-- @@ L119-120 verbatim
@[simp] lemma func_sigma_inr {k} (f : L₂.Func k) (v : Fin k → M) :
    (add L₁ L₂ M).func (Sum.inr f) v = func f v := rfl


-- @@ L122-123 verbatim
@[simp] lemma rel_sigma_inl {k} (r : L₁.Rel k) (v : Fin k → M) :
    (add L₁ L₂ M).rel (Sum.inl r) v ↔ rel r v := iff_of_eq rfl


-- @@ L125-126 verbatim
@[simp] lemma rel_sigma_inr {k} (r : L₂.Rel k) (v : Fin k → M) :
    (add L₁ L₂ M).rel (Sum.inr r) v ↔ rel r v := iff_of_eq rfl


-- @@ L128-130 verbatim
@[simp] lemma val_lMap_add₁ {n} (t : Semiterm L₁ μ n) (e : Fin n → M) (ε : μ → M) :
    Semiterm.val (add L₁ L₂ M) e ε (t.lMap (Language.Hom.add₁ L₁ L₂)) = t.val str₁ e ε := by
  induction t <;> simp [Semiterm.lMap_func, Semiterm.val, Language.Hom.func_add₁, *]


-- @@ L132-134 verbatim
@[simp] lemma val_lMap_add₂ {n} (t : Semiterm L₂ μ n) (e : Fin n → M) (ε : μ → M) :
    Semiterm.val (add L₁ L₂ M) e ε (t.lMap (Language.Hom.add₂ L₁ L₂)) = t.val str₂ e ε := by
  induction t <;> simp [Semiterm.lMap_func, Semiterm.val, Language.Hom.func_add₂, *]


-- @@ L136-142 verbatim
@[simp] lemma eval_lMap_add₁ {n} (φ : Semiformula L₁ μ n) (e : Fin n → M) (ε : μ → M) :
    Semiformula.Eval (add L₁ L₂ M) e ε (Semiformula.lMap (Language.Hom.add₁ L₁ L₂) φ)
    ↔ Semiformula.Eval str₁ e ε φ := by
  have h : (add L₁ L₂ M).lMap (Language.Hom.add₁ L₁ L₂) = str₁ := rfl
  simpa only [h] using
    (Semiformula.eval_lMap (s₂ := add L₁ L₂ M)
      (Φ := Language.Hom.add₁ L₁ L₂) (e := e) (ε := ε) (φ := φ))


-- @@ L144-150 verbatim
@[simp] lemma eval_lMap_add₂ {n} (φ : Semiformula L₂ μ n) (e : Fin n → M) (ε : μ → M) :
    Semiformula.Eval (add L₁ L₂ M) e ε (Semiformula.lMap (Language.Hom.add₂ L₁ L₂) φ)
    ↔ Semiformula.Eval str₂ e ε φ := by
  have h : (add L₁ L₂ M).lMap (Language.Hom.add₂ L₁ L₂) = str₂ := rfl
  simpa only [h] using
    (Semiformula.eval_lMap (s₂ := add L₁ L₂ M)
      (Φ := Language.Hom.add₂ L₁ L₂) (e := e) (ε := ε) (φ := φ))


-- @@ L152-152 verbatim
end «lp_section_3»


-- @@ L154-154 verbatim
section «lp_section_4»


-- @@ L156-156 verbatim
variable (L : ι → Language) (M : Type*) [str : (i : ι) → Structure (L i) M]


-- @@ L158-160 verbatim
instance sigma : Structure (Language.sigma L) M where
  func := fun _ ⟨_, f⟩ v => func f v
  rel  := fun _ ⟨_, r⟩ v => rel r v


-- @@ L162-163 verbatim
@[simp] lemma func_sigma {k} (f : (L i).Func k) (v : Fin k → M) :
    (sigma L M).func ⟨i, f⟩ v = func f v := rfl


-- @@ L165-166 verbatim
@[simp] lemma rel_sigma {k} (r : (L i).Rel k) (v : Fin k → M) :
    (sigma L M).rel ⟨i, r⟩ v ↔ rel r v := iff_of_eq rfl


-- @@ L168-170 verbatim
@[simp] lemma val_lMap_sigma {n} (t : Semiterm (L i) μ n) (e : Fin n → M) (ε : μ → M) :
    Semiterm.val (sigma L M) e ε (t.lMap (Language.Hom.sigma L i)) = t.val (str i) e ε := by
  induction t <;> simp [Semiterm.lMap_func, Semiterm.val, Language.Hom.func_sigma, *]


-- @@ L172-178 verbatim
@[simp] lemma eval_lMap_sigma {n} (φ : Semiformula (L i) μ n) (e : Fin n → M) (ε : μ → M) :
    Semiformula.Eval (sigma L M) e ε (Semiformula.lMap (Language.Hom.sigma L i) φ)
    ↔ Semiformula.Eval (str i) e ε φ := by
  have h : (sigma L M).lMap (Language.Hom.sigma L i) = str i := rfl
  simpa only [h] using
    (Semiformula.eval_lMap (s₂ := sigma L M)
      (Φ := Language.Hom.sigma L i) (e := e) (ε := ε) (φ := φ))


-- @@ L180-180 verbatim
end «lp_section_4»


-- @@ L182-182 verbatim
end Structure


-- @@ L184-184 verbatim
section «lp_section_5»


-- @@ L186-186 verbatim
variable {L : Language.{u}} {M : Type v} [Structure L M]


-- @@ L188-190 verbatim
instance : Structure L (ULift.{v'} M) where
  func := fun _ f v ↦ ⟨Structure.func f fun i ↦ (v i).down⟩
  rel := fun _ r v ↦ Structure.rel r fun i ↦ (v i).down


-- @@ L192-194 verbatim
@[simp] lemma _root_.LO.FirstOrder.Structure.func_uLift {k} (f : L.Func k) (v :
    Fin k → ULift.{v'} M) :
    Structure.func f v = ⟨Structure.func f fun i ↦ (v i).down⟩ := rfl


-- @@ L196-198 verbatim
@[simp] lemma _root_.LO.FirstOrder.Structure.rel_uLift {k} (r : L.Rel k) (v :
    Fin k → ULift.{v'} M) :
    Structure.rel r v = Structure.rel r fun i ↦ (v i).down := rfl


-- @@ L200-205 verbatim
lemma _root_.LO.FirstOrder.Semiterm.valm_uLift {e : Fin n → ULift.{v'} M} {ε :
    ξ → ULift.{v'} M} {t :
    Semiterm L ξ n} :
    Semiterm.valm (ULift.{v'} M) e ε t =
        ⟨Semiterm.valm M (fun i ↦ (e i).down) (fun i ↦ (ε i).down) t⟩ := by
  induction t <;> simp [*, Semiterm.val_func]


-- @@ L207-213 verbatim
lemma _root_.LO.FirstOrder.Semiformula.evalm_uLift {e : Fin n → ULift.{v'} M} {ε :
    ξ → ULift.{v'} M} {φ :
    Semiformula L ξ n} :
    Semiformula.Evalm (ULift.{v'} M) e ε φ ↔
        Semiformula.Evalm M (fun i ↦ (e i).down) (fun i ↦ (ε i).down) φ := by
  induction φ using Semiformula.rec' <;>
    simp [*, Semiformula.eval_rel, Semiformula.eval_nrel, Semiterm.valm_uLift, Matrix.comp_vecCons']


-- @@ L215-215 verbatim
variable (L M)


-- @@ L217-220 expanded
lemma uLift_elementaryEquiv [Nonempty M] : ElementaryEquiv L (ULift.{v'} M) M :=
  by
  intro σ
  simp only [models_iff, Semiformula.evalm_uLift, Matrix.empty_eq]
  exact ⟨fun h f ↦ h (fun x ↦ ⟨f x⟩), fun h f ↦ h (fun x ↦ (f x).down)⟩


-- @@ L222-222 verbatim
end «lp_section_5»


-- @@ L224-224 verbatim
end FirstOrder


-- @@ L226-226 verbatim
end LO
