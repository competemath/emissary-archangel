/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Logic.Predicate.Term
public import LeanPool.Incompleteness.Foundation.Logic.Predicate.Quantifier
import Mathlib.Algebra.Order.Ring.Nat


-- @@ L12-30 verbatim
/-!
# Rewriting Entailment

term/formula morphisms such as Rewritings, substitutions, and embeddings are handled by the
structure `LO.FirstOrder.Rew`.
- `LO.FirstOrder.Rew.rewrite f` is a Rewriting of the free variables occurring in the term by `f :
  ξ₁ → Semiterm L ξ₂ n`.
- `LO.FirstOrder.Rew.substs v` is a substitution of the bounded variables occurring in the term by
  `v : Fin n → Semiterm L ξ n'`.
- `LO.FirstOrder.Rew.bShift` is a transformation of the bounded variables occurring in the term by
  `#x ↦ #(Fin.succ x)`.
- `LO.FirstOrder.Rew.shift` is a transformation of the free variables occurring in the term by `&x ↦
  &(x + 1)`.
- `LO.FirstOrder.Rew.emb` is a embedding of the term with no free variables.

Rewritings `LO.FirstOrder.Rew` is naturally converted to formula Rewritings by
`LO.FirstOrder.Rew.hom`.

-/


-- @@ L32-32 verbatim
@[expose] public section


-- @@ L34-34 verbatim
namespace LO


-- @@ L36-36 verbatim
namespace FirstOrder


-- @@ L38-43 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
structure Rew (L : Language) (ξ₁ : Type*) (n₁ : ℕ) (ξ₂ : Type*) (n₂ : ℕ) where
  /-- Imported declaration from the Incompleteness formalization. -/
  toFun : Semiterm L ξ₁ n₁ → Semiterm L ξ₂ n₂
  func' : ∀ {k} (f : L.Func k) (v : Fin k → Semiterm L ξ₁ n₁), toFun (Semiterm.func f v) =
    Semiterm.func f (fun i => toFun (v i))


-- @@ L45-46 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev SyntacticRew (L : Language) (n₁ n₂ : ℕ) := Rew L ℕ n₁ ℕ n₂


-- @@ L48-48 verbatim
namespace Rew


-- @@ L50-50 verbatim
open Semiterm

-- @@ L51-51 verbatim
variable {L L' L₁ L₂ L₃ : Language} {ξ ξ' ξ₁ ξ₂ ξ₃ : Type*} {n n₁ n₂ n₃ : ℕ}

-- @@ L52-52 verbatim
variable (ω : Rew L ξ₁ n₁ ξ₂ n₂)


-- @@ L54-56 verbatim
instance : FunLike (Rew L ξ₁ n₁ ξ₂ n₂) (Semiterm L ξ₁ n₁) (Semiterm L ξ₂ n₂) where
  coe := fun f => f.toFun
  coe_injective := fun f g h => by rcases f; rcases g; simpa using h


-- @@ L58-59 verbatim
protected lemma func {k} (f : L.Func k) (v : Fin k → Semiterm L ξ₁ n₁) :
    ω (func f v) = func f (fun i => ω (v i)) := ω.func' f v


-- @@ L61-62 verbatim
lemma func'' {k} (f : L.Func k) (v : Fin k → Semiterm L ξ₁ n₁) :
    ω (func f v) = func f (ω ∘ v) := ω.func' f v


-- @@ L64-65 verbatim
@[simp] lemma func0 (f : L.Func 0) (v : Fin 0 → Semiterm L ξ₁ n₁) :
    ω (func f v) = func f ![] := by simp[Rew.func, Matrix.empty_eq]


-- @@ L67-68 verbatim
@[simp] lemma func1 (f : L.Func 1) (t : Semiterm L ξ₁ n₁) :
    ω (func f ![t]) = func f ![ω t] := by simp[Matrix.constant_eq_singleton, Rew.func]


-- @@ L70-74 verbatim
@[simp] lemma func2 (f : L.Func 2) (t₁ t₂ : Semiterm L ξ₁ n₁) :
    ω (func f ![t₁, t₂]) = func f ![ω t₁, ω t₂] := by
  simp only [Rew.func, func.injEq, heq_eq_eq, true_and]
  funext i
  induction i using Fin.induction <;> simp


-- @@ L76-83 verbatim
@[simp] lemma func3 (f : L.Func 3) (t₁ t₂ t₃ : Semiterm L ξ₁ n₁) :
    ω (func f ![t₁, t₂, t₃]) = func f ![ω t₁, ω t₂, ω t₃] := by
  simp only [Rew.func, func.injEq, heq_eq_eq, true_and]
  funext i
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
    induction i using Fin.induction <;> simp


-- @@ L85-88 verbatim
@[ext] lemma ext (ω₁ ω₂ : Rew L ξ₁ n₁ ξ₂ n₂) (hb : ∀ x, ω₁ #x = ω₂ #x) (hf : ∀ x, ω₁ &x = ω₂ &x) :
    ω₁ = ω₂ := by
  apply DFunLike.ext ω₁ ω₂; intro t
  induction t <;> simp[*, ω₁.func, ω₂.func]


-- @@ L90-90 verbatim
lemma ext' {ω₁ ω₂ : Rew L ξ₁ n₁ ξ₂ n₂} (h : ω₁ = ω₂) (t) : ω₁ t = ω₂ t := by simp[h]


-- @@ L92-95 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected def id : Rew L ξ n ξ n where
  toFun := id
  func' := fun _ _ => rfl


-- @@ L97-97 verbatim
@[simp] lemma id_app (t : Semiterm L ξ n) : Rew.id t = t := rfl


-- @@ L99-102 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected def comp (ω₂ : Rew L ξ₂ n₂ ξ₃ n₃) (ω₁ : Rew L ξ₁ n₁ ξ₂ n₂) : Rew L ξ₁ n₁ ξ₃ n₃ where
  toFun := fun t => ω₂ (ω₁ t)
  func' := fun f v => by simp[func'']; rfl


-- @@ L104-105 verbatim
lemma comp_app (ω₂ : Rew L ξ₂ n₂ ξ₃ n₃) (ω₁ : Rew L ξ₁ n₁ ξ₂ n₂) (t : Semiterm L ξ₁ n₁) :
    (ω₂.comp ω₁) t = ω₂ (ω₁ t) := rfl


-- @@ L107-107 verbatim
@[simp] lemma id_comp (ω : Rew L ξ₁ n₁ ξ₂ n₂) : Rew.id.comp ω = ω := by ext <;> simp[comp_app]


-- @@ L109-109 verbatim
@[simp] lemma comp_id (ω : Rew L ξ₁ n₁ ξ₂ n₂) : ω.comp Rew.id = ω := by ext <;> simp[comp_app]


-- @@ L111-116 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def bindAux (b : Fin n₁ → Semiterm L ξ₂ n₂) (e : ξ₁ → Semiterm L ξ₂ n₂) :
    Semiterm L ξ₁ n₁ → Semiterm L ξ₂ n₂
  | (#x)       => b x
  | (&x)       => e x
  | (func f v) => func f (fun i => bindAux b e (v i))


-- @@ L118-121 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def bind (b : Fin n₁ → Semiterm L ξ₂ n₂) (e : ξ₁ → Semiterm L ξ₂ n₂) : Rew L ξ₁ n₁ ξ₂ n₂ where
  toFun := bindAux b e
  func' := fun _ _ => rfl


-- @@ L123-124 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def rewrite (f : ξ₁ → Semiterm L ξ₂ n) : Rew L ξ₁ n ξ₂ n := bind Semiterm.bvar f


-- @@ L126-127 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def rewriteMap (e : ξ₁ → ξ₂) : Rew L ξ₁ n ξ₂ n := rewrite (fun m => &(e m))


-- @@ L129-131 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def map (b : Fin n₁ → Fin n₂) (e : ξ₁ → ξ₂) : Rew L ξ₁ n₁ ξ₂ n₂ :=
  bind (fun n => #(b n)) (fun m => &(e m))


-- @@ L133-134 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def substs {n'} (v : Fin n → Semiterm L ξ n') : Rew L ξ n ξ n' := bind v fvar


-- @@ L136-137 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def emb {o : Type v₁} [h : IsEmpty o] {ξ : Type v₂} {n} : Rew L o n ξ n := map id h.elim


-- @@ L139-140 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev embs {o : Type v₁} [IsEmpty o] {n} : Rew L o n ℕ n := emb


-- @@ L142-143 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def empty {o : Type v₁} [h : IsEmpty o] {ξ : Type v₂} {n} : Rew L o 0 ξ n := map Fin.elim0 h.elim


-- @@ L145-146 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def bShift : Rew L ξ n ξ (n + 1) := map Fin.succ id


-- @@ L148-149 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def bShiftAdd (m : ℕ) : Rew L ξ n ξ (n + m) := map (Fin.addNat · m) id


-- @@ L151-152 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def cast {n n' : ℕ} (h : n = n') : Rew L ξ n ξ n' := map (Fin.cast h) id


-- @@ L154-155 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def castLE {n n' : ℕ} (h : n ≤ n') : Rew L ξ n ξ n' := map (Fin.castLE h) id


-- @@ L157-158 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def toS : Rew L (Fin n) 0 Empty n := Rew.bind ![] (#·)


-- @@ L160-161 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def toF : Rew L Empty n (Fin n) 0 := Rew.bind (&·) Empty.elim


-- @@ L163-164 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def embSubsts (v : Fin k → Semiterm L ξ n) : Rew L Empty k ξ n := Rew.bind v Empty.elim


-- @@ L166-168 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected def q (ω : Rew L ξ₁ n₁ ξ₂ n₂) : Rew L ξ₁ (n₁ + 1) ξ₂ (n₂ + 1) :=
  bind (vecCons (#0) (bShift ∘ ω ∘ bvar)) (bShift ∘ ω ∘ fvar)


-- @@ L170-173 verbatim
lemma eq_id_of_eq {ω : Rew L ξ n ξ n} (hb : ∀ x, ω #x = #x) (he : ∀ x, ω &x = &x) (t) :
    ω t = t := by
  have : ω = Rew.id := by ext <;> simp[*]
  simp[this]


-- @@ L175-178 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def qpow (ω : Rew L ξ₁ n₁ ξ₂ n₂) : (k : ℕ) → Rew L ξ₁ (n₁ + k) ξ₂ (n₂ + k)
  | 0     => ω
  | k + 1 => (ω.qpow k).q


-- @@ L180-180 verbatim
@[simp] lemma qpow_zero (ω : Rew L ξ₁ n₁ ξ₂ n₂) : qpow ω 0 = ω := rfl


-- @@ L182-182 verbatim
@[simp] lemma qpow_succ (ω : Rew L ξ₁ n₁ ξ₂ n₂) (k : ℕ) : qpow ω (k + 1) = (ω.qpow k).q := rfl


-- @@ L184-184 verbatim
section «lp_section_1»


-- @@ L186-186 verbatim
variable (b : Fin n₁ → Semiterm L ξ₂ n₂) (e : ξ₁ → Semiterm L ξ₂ n₂)


-- @@ L188-188 verbatim
@[simp] lemma bind_fvar (m : ξ₁) : bind b e (&m : Semiterm L ξ₁ n₁) = e m := rfl


-- @@ L190-190 verbatim
@[simp] lemma bind_bvar (n : Fin n₁) : bind b e (#n : Semiterm L ξ₁ n₁) = b n := rfl


-- @@ L192-193 verbatim
lemma eq_bind (ω : Rew L ξ₁ n₁ ξ₂ n₂) : ω = bind (ω ∘ bvar) (ω ∘ fvar) := by
  ext t <;> rfl


-- @@ L195-196 verbatim
@[simp] lemma bind_eq_id_of_zero (f : Fin 0 → Semiterm L ξ₂ 0) : bind f fvar = Rew.id := by
  ext x <;> simp only [bind_bvar, bind_fvar, id_app]; exact Fin.elim0 x


-- @@ L198-198 verbatim
end «lp_section_1»


-- @@ L200-200 verbatim
section «lp_section_2»


-- @@ L202-202 verbatim
variable (b : Fin n₁ → Fin n₂) (e : ξ₁ → ξ₂)


-- @@ L204-204 verbatim
@[simp] lemma map_fvar (m : ξ₁) : map b e (&m : Semiterm L ξ₁ n₁) = &(e m) := rfl


-- @@ L206-206 verbatim
@[simp] lemma map_bvar (n : Fin n₁) : map b e (#n : Semiterm L ξ₁ n₁) = #(b n) := rfl


-- @@ L208-208 verbatim
@[simp] lemma map_id : map (L := L) (id : Fin n → Fin n) (id : ξ → ξ) = Rew.id := by ext <;> simp


-- @@ L210-229 verbatim
lemma map_inj {b : Fin n₁ → Fin n₂} {e : ξ₁ → ξ₂} (hb : Function.Injective b) (he :
    Function.Injective e) :
    Function.Injective <| map (L := L) b e
  | #x,                    #y                    => by simpa using @hb _ _
  | #x,                    &y                    => by simp
  | #x,                    func f w              => by simp [Rew.func]
  | &x,                    #y                    => by simp
  | &x,                    &y                    => by simpa using @he _ _
  | &x,                    func f w              => by simp [Rew.func]
  | func f v,              #y                    => by simp [Rew.func]
  | func f v,              &y                    => by simp [Rew.func]
  | func (arity := k) f v, func (arity := l) g w => fun h ↦ by
    have : k = l := by simp [Rew.func] at h; simp_all
    rcases this
    have : f = g := by simp [Rew.func] at h; simp_all
    rcases this
    have : v = w := by
      have : (fun i ↦ (map b e) (v i)) = (fun i ↦ (map b e) (w i)) := by simpa [Rew.func] using h
      funext i; exact map_inj hb he (congrFun this i)
    simp_all


-- @@ L231-231 verbatim
end «lp_section_2»


-- @@ L233-233 verbatim
section «lp_section_3»


-- @@ L235-235 verbatim
variable (f : ξ₁ → Semiterm L ξ₂ n)


-- @@ L237-237 verbatim
@[simp] lemma rewrite_fvar (x : ξ₁) : rewrite f &x = f x := rfl


-- @@ L239-239 verbatim
@[simp] lemma rewrite_bvar (x : Fin n) : rewrite e (#x : Semiterm L ξ₁ n) = #x := rfl


-- @@ L241-243 verbatim
lemma rewrite_comp_rewrite (v : ξ₂ → Semiterm L ξ₃ n) (w : ξ₁ → Semiterm L ξ₂ n) :
    (rewrite v).comp (rewrite w) = rewrite (rewrite v ∘ w) :=
  by ext <;> simp[comp_app]


-- @@ L245-245 verbatim
@[simp] lemma rewrite_eq_id : (rewrite Semiterm.fvar : Rew L ξ n ξ n) = Rew.id := by ext <;> simp


-- @@ L247-247 verbatim
end «lp_section_3»


-- @@ L249-249 verbatim
section «lp_section_4»


-- @@ L251-251 verbatim
variable (e : ξ₁ → ξ₂)


-- @@ L253-253 verbatim
@[simp] lemma rewriteMap_fvar (x : ξ₁) : rewriteMap e (&x : Semiterm L ξ₁ n) = &(e x) := rfl


-- @@ L255-255 verbatim
@[simp] lemma rewriteMap_bvar (x : Fin n) : rewriteMap e (#x : Semiterm L ξ₁ n) = #x := rfl


-- @@ L257-257 verbatim
@[simp] lemma rewriteMap_id : rewriteMap (L := L) (n := n) (id : ξ → ξ) = Rew.id := by ext <;> simp


-- @@ L259-269 verbatim
lemma eq_rewriteMap_of_funEqOn_fv [DecidableEq ξ₁] (t : Semiterm L ξ₁ n₁) (f g :
    ξ₁ → Semiterm L ξ₂ n₂) (h :
    Function.funEqOn t.FVar? f g) :
    Rew.rewriteMap f t = Rew.rewriteMap g t := by
  induction t
  case bvar => simp
  case fvar x => simpa using h x (by simp)
  case func f v ih =>
    simp only [Rew.func, func.injEq, heq_eq_eq, true_and]
    funext i
    exact ih i (fun x hx ↦ h x (by simpa [Semiterm.fvar?_func] using ⟨i, hx⟩))


-- @@ L271-271 verbatim
end «lp_section_4»


-- @@ L273-273 verbatim
section «lp_section_5»


-- @@ L275-275 verbatim
variable {o : Type v₂} [IsEmpty o]


-- @@ L277-277 verbatim
@[simp] lemma emb_bvar (x : Fin n) : emb (ξ := ξ) (#x : Semiterm L o n) = #x := rfl


-- @@ L279-280 verbatim
@[simp] lemma emb_eq_id : (emb : Rew L o n o n) = Rew.id := by
  ext x <;> simp only [emb_bvar, id_app]; exact isEmptyElim x


-- @@ L282-283 verbatim
lemma eq_empty [h : IsEmpty ξ₁] (ω : Rew L ξ₁ 0 ξ₂ n) :
  ω = empty := by ext x; { exact x.elim0 }; { exact h.elim' x }


-- @@ L285-285 verbatim
end «lp_section_5»


-- @@ L287-287 verbatim
section «lp_section_6»


-- @@ L289-289 verbatim
@[simp] lemma bShift_bvar (x : Fin n) : bShift (#x : Semiterm L ξ n) = #(Fin.succ x) := rfl


-- @@ L291-291 verbatim
@[simp] lemma bShift_fvar (x : ξ) : bShift (&x : Semiterm L ξ n) = &x := rfl


-- @@ L293-294 verbatim
@[simp 1100] lemma bShift_ne_zero (t : Semiterm L ξ n) : bShift t ≠ #0 := by
  cases t <;> simp[Rew.func, Fin.succ_ne_zero]


-- @@ L296-297 verbatim
lemma bShift_positive (t : Semiterm L ξ n) : (bShift t).Positive := by
  induction t <;> simp [Rew.func, *]


-- @@ L299-314 verbatim
lemma positive_iff {t : Semiterm L ξ (n + 1)} : t.Positive ↔ ∃ t', t = bShift t' :=
  ⟨by
      induction t <;> simp only [
        Semiterm.Positive.bvar, Semiterm.Positive.fvar, Semiterm.Positive.func, true_implies]
      case bvar x =>
        intro hx; exact ⟨#(x.pred (Fin.pos_iff_ne_zero.mp hx)), by simp⟩
      case fvar x => exact ⟨&x, by simp⟩
      case func k f v ih =>
        intro h
        have : ∀ i, ∃ t', v i = bShift t' := fun i => ih i (h i)
        choose w hw using this
        exact ⟨func f w, by
          simp only [Rew.func, func.injEq, heq_eq_eq, true_and]
          funext i
          exact hw i⟩,
   by rintro ⟨t', rfl⟩; exact bShift_positive t'⟩


-- @@ L316-318 expanded
@[simp]
lemma leftConcat_bShift_comp_bvar :
    (vecCons (#0) (bShift ∘ bvar) : Fin (n + 1) → Semiterm L ξ (n + 1)) = bvar :=
  funext (Fin.cases (by simp) (by simp))


-- @@ L320-322 verbatim
@[simp] lemma bShift_comp_fvar :
    (bShift ∘ fvar : ξ → Semiterm L ξ (n + 1)) = fvar :=
  funext (by simp)


-- @@ L324-324 verbatim
end «lp_section_6»


-- @@ L326-326 verbatim
section «lp_section_7»


-- @@ L328-330 verbatim
@[simp] lemma bShiftAdd_bvar (m) (x : Fin n) : bShiftAdd m (#x :
    Semiterm L ξ n) = #(Fin.addNat x m) :=
  rfl


-- @@ L332-332 verbatim
@[simp] lemma bShiftAdd_fvar (m) (x : ξ) : bShiftAdd m (&x : Semiterm L ξ n) = &x := rfl


-- @@ L334-334 verbatim
end «lp_section_7»


-- @@ L336-336 verbatim
section «lp_section_8»


-- @@ L338-338 verbatim
variable {n'} (w : Fin n → Semiterm L ξ n')


-- @@ L340-340 verbatim
@[simp] lemma substs_bvar (x : Fin n) : substs w #x = w x := by simp[substs]


-- @@ L342-342 verbatim
@[simp] lemma substs_fvar (x : ξ) : substs w &x = &x := by simp[substs]


-- @@ L344-348 verbatim
@[simp] lemma substs_zero (w : Fin 0 → Term L ξ) : substs w = Rew.id :=
  by
    ext x
    · exact Fin.elim0 x
    · rfl


-- @@ L350-352 verbatim
lemma substs_comp_substs (v : Fin l → Semiterm L ξ k) (w : Fin k → Semiterm L ξ n) :
    (substs w).comp (substs v) = substs (substs w ∘ v) :=
  by ext <;> simp[comp_app]


-- @@ L354-354 verbatim
@[simp] lemma substs_eq_id : (substs Semiterm.bvar : Rew L ξ n ξ n) = Rew.id := by ext <;> simp


-- @@ L356-356 verbatim
end «lp_section_8»


-- @@ L358-358 verbatim
section «lp_section_9»


-- @@ L360-360 verbatim
variable {n'} (h : n = n')


-- @@ L362-362 verbatim
@[simp] lemma cast_bvar (x : Fin n) : cast h (#x : Semiterm L ξ n) = #(Fin.cast h x) := rfl


-- @@ L364-364 verbatim
@[simp] lemma cast_fvar (x : ξ) : cast h (&x : Semiterm L ξ n) = &x := rfl


-- @@ L366-366 verbatim
@[simp] lemma cast_eq_id {h} : (cast h : Rew L ξ n ξ n) = Rew.id := by ext <;> simp


-- @@ L368-368 verbatim
end «lp_section_9»


-- @@ L370-370 verbatim
section «lp_section_10»


-- @@ L372-374 verbatim
@[simp] lemma castLe_bvar {n'} (h : n ≤ n') (x : Fin n) : castLE h (#x :
    Semiterm L ξ n) = #(Fin.castLE h x) :=
  rfl


-- @@ L376-376 verbatim
@[simp] lemma castLe_fvar {n'} (h : n ≤ n') (x : ξ) : castLE h (&x : Semiterm L ξ n) = &x := rfl


-- @@ L378-378 verbatim
@[simp] lemma castLe_eq_id {h} : (castLE h : Rew L ξ n ξ n) = Rew.id := by ext <;> simp


-- @@ L380-380 verbatim
end «lp_section_10»


-- @@ L382-382 verbatim
section «lp_section_11»


-- @@ L384-384 verbatim
@[simp] lemma toS_fvar {n} (x : Fin n) : toS (&x : Term L (Fin n)) = #x := rfl


-- @@ L386-386 verbatim
end «lp_section_11»


-- @@ L388-388 verbatim
section «lp_section_12»


-- @@ L390-390 verbatim
variable {k} (w : Fin k → Semiterm L ξ n)


-- @@ L392-392 verbatim
@[simp] lemma embSubsts_bvar (x : Fin k) : embSubsts w #x = w x := by simp[embSubsts]


-- @@ L394-397 verbatim
@[simp] lemma embSubsts_zero (w : Fin 0 → Term L ξ) : embSubsts w = Rew.emb := by
  ext x
  · exact Fin.elim0 x
  · exact Empty.elim x


-- @@ L399-403 verbatim
lemma substs_comp_embSubsts (v : Fin l → Semiterm L ξ k) (w : Fin k → Semiterm L ξ n) :
    (substs w).comp (embSubsts v) = embSubsts (substs w ∘ v) := by
  ext x
  · rfl
  · exact Empty.elim x


-- @@ L405-407 verbatim
@[simp] lemma embSubsts_eq_id : (embSubsts Semiterm.bvar : Rew L Empty n ξ n) = Rew.emb := by
  ext x <;> try simp
  · exact Empty.elim x


-- @@ L409-409 verbatim
end «lp_section_12»


-- @@ L411-411 verbatim
section «lp_section_13»


-- @@ L413-413 verbatim
variable (ω : Rew L ξ₁ n₁ ξ₂ n₂)


-- @@ L415-415 verbatim
@[simp] lemma q_bvar_zero : ω.q #0 = #0 := by simp[Rew.q]


-- @@ L417-417 verbatim
@[simp] lemma q_bvar_succ (i : Fin n₁) : ω.q #(i.succ) = bShift (ω #i) := by simp[Rew.q]


-- @@ L419-419 verbatim
@[simp] lemma q_fvar (x : ξ₁) : ω.q &x = bShift (ω &x) := by simp[Rew.q]


-- @@ L421-422 verbatim
@[simp] lemma q_comp_bShift : ω.q.comp bShift = bShift.comp ω := by
  ext x <;> simp[comp_app]


-- @@ L424-425 verbatim
@[simp] lemma q_comp_bShift_app (t : Semiterm L ξ₁ n₁) : ω.q (bShift t) = bShift (ω t) := by
  have := ext' (ω.q_comp_bShift) t; simpa only [comp_app] using this


-- @@ L427-429 verbatim
@[simp] lemma q_id : (Rew.id :
    Rew L ξ n ξ n).q = Rew.id := by
  ext x; { cases x using Fin.cases <;> simp }; { simp }


-- @@ L431-436 verbatim
@[simp] lemma q_eq_zero_iff : ω.q t = #0 ↔ t = #0 := by
  cases t
  · rename_i i
    cases i using Fin.cases <;> simp
  · simp only [q_fvar, bShift_ne_zero, reduceCtorEq]
  · simp only [Rew.func, reduceCtorEq]


-- @@ L438-447 verbatim
@[simp] lemma q_positive_iff : (ω.q t).Positive ↔ t.Positive := by
  induction t
  · rename_i x
    cases x using Fin.cases
    · simp_all
    · simp only [q_bvar_succ, bShift_positive, Semiterm.Positive.bvar]
      exact ⟨fun _ ↦ Nat.succ_pos _, fun _ ↦ trivial⟩
  · simp only [q_fvar, bShift_positive, Semiterm.Positive.fvar]
  · rename_i v ih
    simpa only [Rew.func, Semiterm.Positive.func] using forall_congr' ih


-- @@ L449-449 verbatim
@[simp] lemma qpow_id {k} : (Rew.id : Rew L ξ n ξ n).qpow k = Rew.id := by induction k <;> simp[*]


-- @@ L451-453 verbatim
lemma q_comp (ω₂ : Rew L ξ₂ n₂ ξ₃ n₃) (ω₁ : Rew L ξ₁ n₁ ξ₂ n₂) :
    (Rew.comp ω₂ ω₁).q = ω₂.q.comp ω₁.q := by
      ext x; { cases x using Fin.cases <;> simp[comp_app] }; { simp[comp_app] }


-- @@ L455-456 verbatim
lemma qpow_comp (k) (ω₂ : Rew L ξ₂ n₂ ξ₃ n₃) (ω₁ : Rew L ξ₁ n₁ ξ₂ n₂) :
    (Rew.comp ω₂ ω₁).qpow k = (ω₂.qpow k).comp (ω₁.qpow k) := by induction k <;> simp[*, q_comp]


-- @@ L458-460 expanded
lemma q_bind (b : Fin n₁ → Semiterm L ξ₂ n₂) (e : ξ₁ → Semiterm L ξ₂ n₂) :
    (bind b e).q = bind (vecCons (#0) (bShift ∘ b)) (bShift ∘ e) := by ext x;
  { cases x using Fin.cases <;> simp
  };
  { simp
  }


-- @@ L462-464 expanded
lemma q_map (b : Fin n₁ → Fin n₂) (e : ξ₁ → ξ₂) :
    (map (L := L) b e).q = map (vecCons 0 (Fin.succ ∘ b)) e := by ext x;
  { cases x using Fin.cases <;> simp
  };
  { simp
  }


-- @@ L466-468 verbatim
lemma q_rewrite (f : ξ₁ → Semiterm L ξ₂ n) :
    (rewrite f).q = rewrite (bShift ∘ f) := by
      ext x; { cases x using Fin.cases <;> simp[] }; { simp }


-- @@ L470-472 verbatim
@[simp] lemma q_rewriteMap (e : ξ₁ → ξ₂) :
    (rewriteMap (L := L) (n := n) e).q = rewriteMap e := by
      ext x; { cases x using Fin.cases <;> simp[rewriteMap] }; { simp }


-- @@ L474-476 verbatim
@[simp] lemma q_emb {o : Type v₁} [e : IsEmpty o] {n} :
    (emb (L := L) (o := o) (ξ := ξ₂) (n := n)).q = emb := by
      ext x; { cases x using Fin.cases <;> simp }; { exact e.elim x }


-- @@ L478-479 verbatim
@[simp] lemma qpow_emb {o : Type v₁} [e : IsEmpty o] {n k} :
    (emb (L := L) (o := o) (ξ := ξ₂) (n := n)).qpow k = emb := by induction k <;> simp[*]


-- @@ L481-483 verbatim
@[simp] lemma q_cast {n n'} (h : n = n') :
    (cast h : Rew L ξ n ξ n').q = cast (congrFun (congrArg HAdd.hAdd h) 1) := by
  ext x <;> simp; cases x using Fin.cases <;> simp


-- @@ L485-487 verbatim
@[simp] lemma q_castLE {n n'} (h : n ≤ n') :
    (castLE h : Rew L ξ n ξ n').q = castLE (Nat.add_le_add_right h 1) := by
  ext x <;> simp; cases x using Fin.cases <;> simp


-- @@ L489-496 verbatim
lemma q_toS :
    (toS : Rew L (Fin n) 0 Empty n).q = bind ![#0] (#·.succ) := by
  ext x
  · cases x using Fin.cases
    · rfl
    · rename_i i
      exact Fin.elim0 i
  · rfl


-- @@ L498-500 verbatim
@[simp] lemma qpow_castLE {n n'} (h : n ≤ n') :
    (castLE h : Rew L ξ n ξ n').qpow k = castLE (Nat.add_le_add_right h k) := by
  induction k <;> simp[*]


-- @@ L502-504 expanded
lemma q_substs (w : Fin n → Semiterm L ξ n') : (substs w).q = substs (vecCons (#0) (bShift ∘ w)) :=
  by ext x;
  { cases x using Fin.cases <;> simp
  };
  { simp
  }


-- @@ L506-511 expanded
lemma q_embSubsts (w : Fin k → Semiterm L ξ n) :
    (embSubsts w).q = embSubsts (vecCons (#0) (bShift ∘ w)) :=
  by
  ext x
  · cases x using Fin.cases <;> simp
  · simp only [q_fvar, Nat.succ_eq_add_one]
    exact Empty.elim x


-- @@ L513-513 verbatim
end «lp_section_13»


-- @@ L515-521 verbatim
section «lp_section_14»

/-
  #0 #1 ... #(n - 1) &0 &1 ...
   ↓shift
  #0 #1 ... #(n - 1) &1 &2 &3 ...
-/


-- @@ L523-530 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def shift : SyntacticRew L n n := map id Nat.succ

/-
  #0 #1 ... #(n - 1) #n &0 &1 ...
   ↓free           ↑fix
  #0 #1 ... #(n - 1) &0 &1 &2 ...
 -/


-- @@ L532-533 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def free : SyntacticRew L (n + 1) n :=
  bind (vecConsLast bvar &0) (fun m => &(Nat.succ m))


-- @@ L535-536 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def fix : SyntacticRew L n (n + 1) :=
  bind (fun x => #(Fin.castSucc x)) (cases (#(Fin.last n)) fvar)


-- @@ L538-539 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev rewrite1 (t : SyntacticSemiterm L n) : SyntacticRew L n n :=
  bind Semiterm.bvar (cases t fvar)


-- @@ L541-541 verbatim
section «lp_section_15»


-- @@ L543-543 verbatim
@[simp] lemma shift_bvar (x : Fin n) : shift (#x : SyntacticSemiterm L n) = #x := rfl


-- @@ L545-545 verbatim
@[simp] lemma shift_fvar (x : ℕ) : shift (&x : SyntacticSemiterm L n) = &(x + 1) := rfl


-- @@ L547-548 verbatim
lemma shift_func {k} (f : L.Func k) (v : Fin k → SyntacticSemiterm L n) :
    shift (func f v) = func f (fun i => shift (v i)) := rfl


-- @@ L550-562 verbatim
lemma shift_Injective : Function.Injective (@shift L n) :=
  Function.LeftInverse.injective (g := map id Nat.pred)
    (by
      intro φ
      exact eq_id_of_eq
        (ω := (map (L := L) (id : Fin n → Fin n) Nat.pred).comp shift)
        (by
          intro x
          rfl)
        (by
          intro x
          simp only [comp_app, shift_fvar, map_fvar, Nat.pred_succ])
        φ)


-- @@ L564-564 verbatim
end «lp_section_15»


-- @@ L566-566 verbatim
section «lp_section_16»


-- @@ L568-570 verbatim
@[simp] lemma free_bvar_castSucc (x : Fin n) : free (#(Fin.castSucc x) :
    SyntacticSemiterm L (n + 1)) = #x := by
  simp[free]


-- @@ L572-574 verbatim
@[simp] lemma free_bvar_castSucc_zero : free (#0 :
    SyntacticSemiterm L (n + 1 + 1)) = #0 :=
  free_bvar_castSucc 0


-- @@ L576-578 verbatim
@[simp] lemma free_bvar_last : free (#(Fin.last n) :
    SyntacticSemiterm L (n + 1)) = &0 := by
  simp[free]


-- @@ L580-580 verbatim
@[simp] lemma free_bvar_last_zero : free (#0 : SyntacticSemiterm L 1) = &0 := free_bvar_last


-- @@ L582-584 verbatim
@[simp] lemma free_fvar (x : ℕ) : free (&x :
    SyntacticSemiterm L (n + 1)) = &(x + 1) := by
  simp[free]


-- @@ L586-586 verbatim
end «lp_section_16»


-- @@ L588-588 verbatim
section «lp_section_17»


-- @@ L590-592 verbatim
@[simp] lemma fix_bvar (x : Fin n) : fix (#x :
    SyntacticSemiterm L n) = #(Fin.castSucc x) := by
  simp[fix]


-- @@ L594-594 verbatim
@[simp] lemma fix_fvar_zero : fix (&0 : SyntacticSemiterm L n) = #(Fin.last n) := by simp[fix]


-- @@ L596-596 verbatim
@[simp] lemma fix_fvar_succ (x : ℕ) : fix (&(x + 1) : SyntacticSemiterm L n) = &x := by simp[fix]


-- @@ L598-598 verbatim
end «lp_section_17»


-- @@ L600-605 verbatim
@[simp] lemma free_comp_fix : (free (L := L) (n := n)).comp fix = Rew.id := by
  ext x
  · simp only [comp_app, fix_bvar, free_bvar_castSucc, id_app]
  · cases x
    · simp only [comp_app, fix_fvar_zero, free_bvar_last, id_app]
    · simp only [comp_app, fix_fvar_succ, free_fvar, id_app]


-- @@ L607-612 verbatim
@[simp] lemma fix_comp_free : (fix (L := L) (n := n)).comp free = Rew.id := by
  ext x
  · cases x using Fin.lastCases
    · simp only [comp_app, free_bvar_last, fix_fvar_zero, id_app]
    · simp only [comp_app, free_bvar_castSucc, fix_bvar, id_app]
  · simp only [comp_app, free_fvar, fix_fvar_succ, id_app]


-- @@ L614-617 verbatim
@[simp] lemma bShift_free_eq_shift : (free (L := L) (n := 0)).comp bShift = shift := by
  ext x
  · exact Fin.elim0 x
  · rfl


-- @@ L619-620 verbatim
lemma bShift_comp_substs (v : Fin n₁ → Semiterm L ξ₂ n₂) :
  bShift.comp (substs v) = substs (bShift ∘ v) := by ext x <;> rfl


-- @@ L622-623 verbatim
lemma shift_comp_substs (v : Fin n₁ → SyntacticSemiterm L n₂) :
  shift.comp (substs v) = (substs (shift ∘ v)).comp shift := by ext x <;> rfl


-- @@ L625-632 verbatim
lemma shift_comp_substs1 (t : SyntacticSemiterm L n₂) :
  shift.comp (substs ![t]) = (substs ![shift t]).comp shift := by
  ext x
  · cases x using Fin.cases
    · simp only [comp_app, substs_bvar, shift_bvar, Matrix.cons_val_fin_one]
    · rename_i i
      exact Fin.elim0 i
  · rfl


-- @@ L634-638 verbatim
@[simp] lemma rewrite_comp_emb {o : Type v₁} [e : IsEmpty o] (f : ξ₂ → Semiterm L ξ₃ n) :
  (rewrite f).comp emb = (emb : Rew L o n ξ₃ n) := by
    ext x
    · rfl
    · exact IsEmpty.elim e x


-- @@ L640-644 verbatim
@[simp] lemma shift_comp_emb {o : Type v₁} [e : IsEmpty o] :
  shift.comp emb = (emb : Rew L o n ℕ n) := by
    ext x
    · rfl
    · exact IsEmpty.elim e x


-- @@ L646-648 expanded
lemma rewrite_comp_free_eq_substs (t : SyntacticTerm L) :
    (rewrite (cases t Semiterm.fvar)).comp free = substs ![t] := by
  ext x <;> simp [comp_app, Fin.eq_zero]


-- @@ L650-651 expanded
lemma rewrite_comp_shift_eq_id (t : SyntacticTerm L) :
    (rewrite (cases t Semiterm.fvar)).comp shift = Rew.id := by ext x <;> simp [comp_app]


-- @@ L653-654 verbatim
@[simp] lemma substs_mbar_zero_comp_shift_eq_free :
    (substs (L := L) ![&0]).comp shift = free := by ext x <;> simp[comp_app, Fin.eq_zero]


-- @@ L656-660 verbatim
@[simp] lemma substs_comp_bShift_eq_id (v : Fin 1 → Semiterm L ξ 0) :
    (substs (L := L) v).comp bShift = Rew.id := by
  ext x
  · exact Fin.elim0 x
  · rfl


-- @@ L662-664 verbatim
lemma free_comp_substs_eq_substs_comp_shift {n'} (w : Fin n' → SyntacticSemiterm L (n + 1)) :
    free.comp (substs w) = (substs (free ∘ w)).comp shift :=
  by ext x <;> simp[comp_app]


-- @@ L666-668 verbatim
@[simp] lemma rewriteMap_comp_rewriteMap (f : ξ₁ → ξ₂) (g : ξ₂ → ξ₃) :
  (rewriteMap (L := L) (n := n) g).comp (rewriteMap f) = rewriteMap (g ∘ f) := by
    ext x <;> simp [comp_app]


-- @@ L670-672 verbatim
@[simp] lemma fix_free_app (t : SyntacticSemiterm L (n + 1)) :
    fix (free t) = t := by
  simp[←comp_app]


-- @@ L674-674 verbatim
@[simp] lemma free_fix_app (t : SyntacticSemiterm L n) : free (fix t) = t := by simp[←comp_app]


-- @@ L676-678 verbatim
@[simp] lemma free_bShift_app (t : SyntacticSemiterm L 0) :
    free (bShift t) = shift t := by
  simp[←comp_app]


-- @@ L680-682 verbatim
@[simp] lemma substs_bShift_app (v : Fin 1 → Semiterm L ξ 0) :
    substs v (bShift t) = t := by
  simp[←comp_app]


-- @@ L684-686 expanded
lemma rewrite_comp_fix_eq_substs (t) :
    ((rewrite (cases t (&·))).comp free : SyntacticRew L 1 0) = substs ![t] := by
  ext x <;> simp [comp_app, Fin.eq_zero]


-- @@ L688-692 verbatim
lemma bShift_eq_rewrite :
    (Rew.bShift : SyntacticRew L 0 1) = Rew.substs ![] := by
  ext x
  · exact x.elim0
  · simp


-- @@ L694-694 verbatim
section «lp_section_18»


-- @@ L696-696 verbatim
variable (ω : SyntacticRew L n₁ n₂)


-- @@ L698-700 verbatim
@[simp] lemma q_shift :
    (shift (L := L) (n := n)).q = shift := by
  ext x; { cases x using Fin.cases <;> simp }; { simp }


-- @@ L702-713 verbatim
@[simp] lemma q_free : (free (L := L) (n := n)).q = free := by
  ext x
  · cases x using Fin.cases with
    | zero => simp
    | succ x =>
      simp only [q_bvar_succ]
      cases x using Fin.lastCases
      · simp
      · rename_i i
        rw [Fin.succ_castSucc]
        simp only [free_bvar_castSucc, bShift_bvar]
  · simp


-- @@ L715-718 verbatim
@[simp] lemma q_fix : (fix (L := L) (n := n)).q = fix := by
  ext x
  · cases x using Fin.cases <;> simp
  · cases x <;> simp


-- @@ L720-720 verbatim
end «lp_section_18»


-- @@ L722-725 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def fixitr (n : ℕ) : (m : ℕ) → SyntacticRew L n (n + m)
  | 0     => Rew.id
  | m + 1 => Rew.fix.comp (fixitr n m)


-- @@ L727-728 verbatim
@[simp] lemma fixitr_zero :
    fixitr (L := L) n 0 = Rew.id := by simp [fixitr]


-- @@ L730-732 verbatim
lemma fixitr_succ (m) :
    fixitr (L := L) n (m + 1) = Rew.fix.comp (fixitr n m) := by
  simp [fixitr]


-- @@ L734-740 verbatim
@[simp] lemma fixitr_bvar (n m) (x : Fin n) : fixitr n m (#x :
    SyntacticSemiterm L n) = #(x.castAdd m) := by
  induction m
  · simp only [Nat.add_zero, fixitr_zero, id_app, Fin.castAdd_zero, Fin.cast_eq_self]
  case succ m ih =>
    simp only [fixitr_succ, comp_app, fix_bvar, bvar.injEq, ih]
    simp only [Fin.castSucc_castAdd]


-- @@ L742-761 verbatim
lemma fixitr_fvar (n m) (x : ℕ) :
    fixitr n m (&x : SyntacticSemiterm L n) =
        if h : x < m then #(Fin.natAdd n ⟨x, h⟩) else &(x - m) := by
  induction m
  · simp only [Nat.add_zero, fixitr_zero, id_app, not_lt_zero, ↓reduceDIte, tsub_zero]
  case succ m ih =>
    suffices fix (fixitr n m &x) =
      if h : x < m + 1 then #⟨n + x, _⟩ else &(x - (m + 1)) from Eq.trans (comp_app _ _ _) this
    simp only [ih]
    by_cases hx : x < m
    · simp [hx, Nat.lt_add_right 1 hx]
    by_cases hx2 : x < m + 1
    · have : x = m := Nat.le_antisymm (by { simpa [Nat.lt_succ_iff] using hx2 }) (by simpa using hx)
      simp only [this, lt_self_iff_false, ↓reduceDIte, Nat.sub_self, fix_fvar_zero,
        lt_add_iff_pos_right, zero_lt_one, bvar.injEq]
      ext
      simp
    · simp [hx, hx2]
      have : x - m = x - (m + 1) + 1 := by omega
      simp [this]


-- @@ L763-763 verbatim
end «lp_section_14»


-- @@ L765-767 verbatim
lemma substs_bv (t : Semiterm L ξ n) (v : Fin n → Semiterm L ξ m) :
    (Rew.substs v t).bv = t.bv.biUnion (fun i ↦ (v i).bv) := by
  induction t <;> simp [Rew.func, Semiterm.bv_func, Finset.biUnion_biUnion, *]


-- @@ L769-772 verbatim
@[simp] lemma substs_positive (t : Semiterm L ξ n) (v : Fin n → Semiterm L ξ (m + 1)) :
    (Rew.substs v t).Positive ↔ ∀ i ∈ t.bv, (v i).Positive := by
  simp only [Semiterm.Positive, substs_bv, Finset.mem_biUnion, forall_exists_index, and_imp]
  exact ⟨fun H i hi x hx ↦ H x i hi hx, fun H x i hi hx ↦ H i hi x hx⟩


-- @@ L774-782 verbatim
lemma embSubsts_bv (t : Semiterm L Empty n) (v : Fin n → Semiterm L ξ m) :
    (Rew.embSubsts v t).bv = t.bv.biUnion (fun i ↦ (v i).bv) := by
  induction t
  case bvar =>
    simp only [embSubsts_bvar, bv_bvar, Finset.singleton_biUnion]
  case fvar =>
    contradiction
  case func =>
    simp only [Rew.func, bv_func, Finset.biUnion_biUnion, *]


-- @@ L784-787 verbatim
@[simp] lemma embSubsts_positive (t : Semiterm L Empty n) (v : Fin n → Semiterm L ξ (m + 1)) :
    (Rew.embSubsts v t).Positive ↔ ∀ i ∈ t.bv, (v i).Positive := by
  simp only [Semiterm.Positive, embSubsts_bv, Finset.mem_biUnion, forall_exists_index, and_imp]
  exact ⟨fun H i hi x hx ↦ H x i hi hx, fun H x i hi hx ↦ H i hi x hx⟩


-- @@ L789-789 verbatim
@[simp] lemma bshift_positive (t : Semiterm L ξ n) : Positive (Rew.bShift t) := bShift_positive t


-- @@ L791-795 verbatim
lemma emb_comp_bShift_comm {o : Type v₁} [IsEmpty o] :
    Rew.bShift.comp (Rew.emb : Rew L o n ξ n) = Rew.emb.comp Rew.bShift := by
  ext x
  · simp [comp_app]
  · exact IsEmpty.elim (by assumption) x


-- @@ L797-799 verbatim
lemma emb_bShift_term {o : Type v₁} [IsEmpty o] (t : Semiterm L o n) :
    Rew.bShift (Rew.emb t : Semiterm L ξ n) = Rew.emb (Rew.bShift t) := by
  simp [←comp_app, emb_comp_bShift_comm]


-- @@ L801-801 verbatim
end Rew


-- @@ L803-806 verbatim
/-!
### Rewriting system of terms

-/

-- @@ L807-807 verbatim
namespace Semiterm


-- @@ L809-809 verbatim
variable {L L' L₁ L₂ L₃ : Language} {ξ ξ' ξ₁ ξ₂ ξ₃ : Type*} {n n₁ n₂ n₃ : ℕ}


-- @@ L811-811 verbatim
instance : Coe (Semiterm L Empty n) (SyntacticSemiterm L n) := ⟨Rew.emb⟩


-- @@ L813-819 verbatim
@[simp] lemma freeVariables_emb {ο : Type*} [IsEmpty ο] [DecidableEq ξ] {t : Semiterm L ο n} :
    (Rew.emb t : Semiterm L ξ n).freeVariables = ∅ := by
  induction t
  case bvar => simp
  case fvar x => exact IsEmpty.elim inferInstance x
  case func k f v ih =>
    ext x; simp [Rew.func, freeVariables_func, ih]


-- @@ L821-832 verbatim
lemma rew_eq_of_funEqOn [DecidableEq ξ₁] (ω₁ ω₂ : Rew L ξ₁ n₁ ξ₂ n₂) (t : Semiterm L ξ₁ n₁)
  (hb : ∀ x, ω₁ #x = ω₂ #x)
  (he : Function.funEqOn t.FVar? (ω₁ ∘ Semiterm.fvar) (ω₂ ∘ Semiterm.fvar)) :
    ω₁ t = ω₂ t := by
  induction t
  case bvar x => exact hb x
  case fvar => simpa [FVar?, Function.funEqOn] using he
  case func k f v ih =>
    simp only [Rew.func]
    congr
    funext i
    exact ih i (he.of_subset <| by simp only [fvar?_func]; intro x hx; exact ⟨i, hx⟩)


-- @@ L834-834 verbatim
section «lp_section_19»


-- @@ L836-836 verbatim
variable (Φ : L₁ →ᵥ L₂)

-- @@ L837-837 verbatim
open Rew


-- @@ L839-841 verbatim
lemma lMap_bind (b : Fin n₁ → Semiterm L₁ ξ₂ n₂) (e : ξ₁ → Semiterm L₁ ξ₂ n₂) (t) :
    lMap Φ (bind b e t) = bind (lMap Φ ∘ b) (lMap Φ ∘ e) (t.lMap Φ) :=
  by induction t <;> simp[*, lMap_func, Rew.func]


-- @@ L843-845 verbatim
lemma lMap_map (b : Fin n₁ → Fin n₂) (e : ξ₁ → ξ₂) (t) :
    (map b e t).lMap Φ = map b e (t.lMap Φ) := by
  simp [map, lMap_bind, Function.comp_def]


-- @@ L847-848 verbatim
lemma lMap_bShift (t : Semiterm L₁ ξ₁ n) : (bShift t).lMap Φ = bShift (t.lMap Φ) :=
  by simp[bShift, lMap_map]


-- @@ L850-851 verbatim
lemma lMap_shift (t : SyntacticSemiterm L₁ n) : (shift t).lMap Φ = shift (t.lMap Φ) :=
  by simp[shift, lMap_map]


-- @@ L853-857 verbatim
lemma lMap_free (t : SyntacticSemiterm L₁ (n + 1)) : (free t).lMap Φ = free (t.lMap Φ) :=
  by
    simp only [free, Nat.succ_eq_add_one, lMap_bind]
    congr
    exact funext <| Fin.lastCases (by simp) (by simp)


-- @@ L859-864 verbatim
lemma lMap_fix (t : SyntacticSemiterm L₁ n) : (fix t).lMap Φ = fix (t.lMap Φ) :=
  by
    simp only [fix, lMap_bind]
    congr
    funext x
    cases x <;> simp


-- @@ L866-866 verbatim
end «lp_section_19»


-- @@ L868-882 verbatim
lemma «fvar?_rew» [DecidableEq ξ₁] [DecidableEq ξ₂]
    {ω : Rew L ξ₁ n₁ ξ₂ n₂}
    {t : Semiterm L ξ₁ n₁} {x} :
    (ω t).FVar? x → (∃ i : Fin n₁, (ω #i).FVar? x) ∨ (∃ z : ξ₁, t.FVar? z ∧ (ω &z).FVar? x) := by
  induction t
  case bvar z =>
    intro h; left; exact ⟨z, h⟩
  case fvar z =>
    intro h; right; exact ⟨z, by simp [h]⟩
  case func k F v ih =>
    simp only [Rew.func, fvar?_func, forall_exists_index]
    intro i hx
    rcases ih i hx with (h | ⟨z, hi, hz⟩)
    · left; exact h
    · right; exact ⟨z, ⟨i, hi⟩, hz⟩


-- @@ L884-886 verbatim
@[simp] lemma «fvar?_bShift» [DecidableEq ξ] {t : Semiterm L ξ n} {x} :
    (Rew.bShift t).FVar? x ↔ t.FVar? x := by
  induction t <;> simp [Rew.func, *]


-- @@ L888-898 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def toEmpty [DecidableEq ξ] {n : ℕ} : (t :
    Semiterm L ξ n) → t.freeVariables = ∅ → Semiterm L Empty n
  | #x,        _ => #x
  | &x,        h => by simp at h
  | func f v, h =>
    have : ∀ i, (v i).freeVariables = ∅ := by
      intro i; ext x
      have := by simpa using Eq.to_iff (congrFun (congrArg Membership.mem h) x)
      simpa using this i
    func f fun i ↦ toEmpty (v i) (this i)


-- @@ L900-903 verbatim
@[simp] lemma emb_toEmpty [DecidableEq ξ] (t : Semiterm L ξ n) (ht : t.freeVariables = ∅) :
    Rew.emb (t.toEmpty ht) = t := by
  induction t <;> try simp [toEmpty, Rew.func, *]
  case fvar => simp at ht


-- @@ L905-905 verbatim
end Semiterm


-- @@ L907-910 verbatim
/-!
### Rewriting system of formulae

-/


-- @@ L912-913 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class FreeVar (ξ : outParam Type*) (F : ℕ → Type*) where


-- @@ L915-922 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class Rewriting (L : outParam Language) (ξ : outParam Type*) (F : ℕ → Type*) (ζ : Type*)
    (G : outParam (ℕ → Type*)) [LCWQ F] [LCWQ G] where
  /-- Imported declaration from the Incompleteness formalization. -/
  app {n₁ n₂} : Rew L ξ n₁ ζ n₂ → Hom (F n₁) (G n₂)
  app_all (ω₁₂ : Rew L ξ n₁ ζ n₂) (φ) :
    app ω₁₂ (UnivQuantifier.univ φ) = UnivQuantifier.univ (app ω₁₂.q φ)
  app_ex (ω₁₂ : Rew L ξ n₁ ζ n₂) (φ) : app ω₁₂ (ExQuantifier.ex φ) = ExQuantifier.ex (app ω₁₂.q φ)


-- @@ L924-927 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev SyntacticRewriting (L : outParam Language) (F : ℕ → Type*) (G :
    outParam (ℕ → Type*)) [LCWQ F] [LCWQ G] :=
  Rewriting L ℕ F ℕ G


-- @@ L929-929 verbatim
namespace Rewriting


-- @@ L931-931 verbatim
variable [LCWQ F] [LCWQ G] [Rewriting L ξ F ζ G]


-- @@ L933-933 verbatim
attribute [simp] app_all app_ex


-- @@ L935-936 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infixr:73 " ▹ " => app


-- @@ L938-938 expanded
lemma smul_ext' {ω₁ ω₂ : Rew L ξ n₁ ζ n₂} (h : ω₁ = ω₂) {φ : F n₁} : app ω₁ φ = app ω₂ φ := by
  rw [h]


-- @@ L940-942 expanded
@[simp]
lemma smul_ball (ω : Rew L ξ n₁ ζ n₂) (φ ψ : F (n₁ + 1)) :
    app ω (ball φ ψ) = ball (app ω.q φ) (app ω.q ψ) := by simp [ball]


-- @@ L944-946 expanded
@[simp]
lemma smul_bex (ω : Rew L ξ n₁ ζ n₂) (φ ψ : F (n₁ + 1)) :
    app ω (bex φ ψ) = bex (app ω.q φ) (app ω.q ψ) := by simp [bex]


-- @@ L948-951 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev substitute [Rewriting L ξ F ξ F] (φ : F n₁) (w : Fin n₁ → Semiterm L ξ n₂) : F n₂ :=
  app (Rew.substs w) φ


-- @@ L953-954 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infix:90 " <~ " => LO.FirstOrder.Rewriting.substitute


-- @@ L956-957 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev shift [Rewriting L ℕ F ℕ F] (φ : F n) : F n :=
  app (@Rew.shift L n) φ


-- @@ L959-960 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev free [Rewriting L ℕ F ℕ F] (φ : F (n + 1)) : F n :=
  app (@Rew.free L n) φ


-- @@ L962-963 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev fix [Rewriting L ℕ F ℕ F] (φ : F n) : F (n + 1) :=
  app (@Rew.fix L n) φ


-- @@ L965-966 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def shifts [Rewriting L ℕ F ℕ F] (Γ : List (F n)) : List (F n) := Γ.map Rewriting.shift


-- @@ L968-969 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
scoped[LO.FirstOrder] postfix:max "⁺" => FirstOrder.Rewriting.shifts


-- @@ L971-975 expanded
/-- Imported declaration from the Incompleteness formalization. -/
@[coe]
abbrev embedding {ο ξ} [IsEmpty ο] {O F : ℕ → Type*} [LCWQ O] [LCWQ F] [Rewriting L ο O ξ F]
    (φ : O n) : F n :=
  app (@Rew.emb L ο _ ξ n) φ


-- @@ L977-977 verbatim
end Rewriting


-- @@ L979-979 verbatim
section «lp_section_20»


-- @@ L981-981 verbatim
open Lean PrettyPrinter Delaborator


-- @@ L983-984 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax (name := substituteNotation) term:max "/[" term,* "]" : term


-- @@ L986-987 expanded
macro_rules (kind:=substituteNotation)
  | `(LO.FirstOrder.Rewriting.substitute $φ:term ![$terms:term,*]) =>
    `(LO.FirstOrder.Rewriting.substitute $φ ![$terms,*])


-- @@ L989-993 unexpanded
/-- Imported declaration from the Incompleteness formalization. -/
@[app_unexpander Rewriting.substitute]
meta def _root_.unexpsnderSubstitute : Unexpander
  | `($_ $φ:term ![$ts:term,*]) => `($φ /[ $ts,* ])
  | _                           => throw ()


-- @@ L995-995 verbatim
end «lp_section_20»


-- @@ L997-1000 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class ReflectiveRewriting (L : outParam Language) (ξ : outParam Type*) (F : ℕ → Type*) [LCWQ F]
    [Rewriting L ξ F ξ F] where
  id_app (φ : F n) : app (@Rew.id L ξ n) φ = φ


-- @@ L1002-1009 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class TransitiveRewriting (L : outParam Language) (ξ₁ : outParam Type*) (F₁ : ℕ → Type*)
    (ξ₂ : Type*) (F₂ : outParam (ℕ → Type*)) (ξ₃ : Type*) (F₃ : outParam (ℕ → Type*)) [LCWQ F₁]
    [LCWQ F₂] [LCWQ F₃] [Rewriting L ξ₁ F₁ ξ₂ F₂] [Rewriting L ξ₂ F₂ ξ₃ F₃]
    [Rewriting L ξ₁ F₁ ξ₃ F₃] where
  comp_app (ω₁₂ : Rew L ξ₁ n₁ ξ₂ n₂) (ω₂₃ : Rew L ξ₂ n₂ ξ₃ n₃) (φ : F₁ n₁) :
    app (ω₂₃.comp ω₁₂) φ = app ω₂₃ (app ω₁₂ φ)


-- @@ L1011-1018 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class InjMapRewriting (L : outParam Language) (ξ : outParam Type*) (F : ℕ → Type*) (ζ : Type*)
    (G : outParam (ℕ → Type*)) [LCWQ F] [LCWQ G] [Rewriting L ξ F ζ G] where
  smul_map_injective {b : Fin n₁ → Fin n₂} {f : ξ → ζ} :
    (hb : Function.Injective b) →
      (hf : Function.Injective f) → Function.Injective fun φ : F n₁ ↦ app (Rew.map (L := L) b f) φ


-- @@ L1020-1023 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class LawfulSyntacticRewriting (L : outParam Language) (S : ℕ →
  Type*) [LCWQ S] [SyntacticRewriting L S S] extends
  ReflectiveRewriting L ℕ S, TransitiveRewriting L ℕ S ℕ S ℕ S, InjMapRewriting L ℕ S ℕ S


-- @@ L1025-1025 verbatim
attribute [simp] ReflectiveRewriting.id_app


-- @@ L1027-1027 verbatim
namespace LawfulSyntacticRewriting


-- @@ L1029-1029 verbatim
variable {S : ℕ → Type*} [LCWQ S] [SyntacticRewriting L S S]


-- @@ L1031-1031 verbatim
open Rewriting ReflectiveRewriting TransitiveRewriting InjMapRewriting


-- @@ L1033-1037 expanded
lemma fix_allClosure (φ : S n) : UnivQuantifier.univ (fix (univClosure φ)) = univClosure (fix φ) :=
  by
  induction n
  case zero => simp [univClosure_succ]
  case succ n ih => simp [univClosure_succ, ih]


-- @@ L1039-1040 verbatim
@[simp] lemma shifts_cons (φ : S n) (Γ : List (S n)) :
    (φ :: Γ)⁺ = Rewriting.shift φ :: Γ⁺ := by simp [shifts]


-- @@ L1042-1042 verbatim
@[simp] lemma shifts_nil : ([] : List (S n))⁺ = [] := by rfl


-- @@ L1044-1045 verbatim
lemma shifts_union (Γ Δ : List (S n)) :
    (Γ ++ Δ)⁺ = Γ⁺ ++ Δ⁺ := by simp [shifts]


-- @@ L1047-1048 expanded
lemma shifts_neg (Γ : List (S n)) : (Γ.map (Tilde.tilde ·))⁺ = (Γ⁺).map (Tilde.tilde ·) := by
  simp [shifts]


-- @@ L1050-1056 expanded
lemma shift_conj₂ (Γ : List (S n)) : shift (List.conj₂ Γ) = List.conj₂ Γ⁺ :=
  by
  induction Γ using List.induction_with_singleton
  case hnil => simp
  case hsingle => simp
  case hcons φ Γ hΓ
    ih =>
    have : Γ⁺ ≠ [] := by intro H; have : Γ = [] := List.map_eq_nil_iff.mp H; contradiction
    simp [hΓ, this, ih]


-- @@ L1058-1058 verbatim
variable [LawfulSyntacticRewriting L S]


-- @@ L1060-1061 verbatim
lemma shift_injective : Function.Injective fun φ : S n ↦ shift φ :=
  smul_map_injective Function.injective_id Nat.succ_injective


-- @@ L1063-1064 verbatim
@[simp] lemma fix_free (φ : S (n + 1)) :
    fix (free φ) = φ := by simp [←comp_app]


-- @@ L1066-1067 verbatim
@[simp] lemma free_fix (φ : S n) :
    free (fix φ) = φ := by simp [←comp_app]


-- @@ L1069-1071 expanded
@[simp]
lemma substitute_empty (φ : S 0) (v : Fin 0 → Semiterm L ℕ 0) :
    (LO.FirstOrder.Rewriting.substitute φ v) = φ := by simp [substitute]


-- @@ L1073-1075 expanded
/-- `hom_substs_mbar_zero_comp_shift_eq_free` -/
@[simp]
lemma app_substs_fbar_zero_comp_shift_eq_free (φ : S 1) :
    LO.FirstOrder.Rewriting.substitute (shift φ) ![&0] = free φ := by
  simp [← comp_app, Rew.substs_mbar_zero_comp_shift_eq_free]


-- @@ L1077-1080 expanded
lemma free_rewrite_eq (f : ℕ → SyntacticTerm L) (φ : S 1) :
    free (app (Rew.rewrite fun x ↦ Rew.bShift (f x)) φ) =
      app (Rew.rewrite (cases &0 fun x ↦ Rew.shift (f x))) (free φ) :=
  by simpa [← comp_app] using smul_ext' <| by ext x <;> simp [Rew.comp_app, Fin.eq_zero]


-- @@ L1082-1084 expanded
lemma shift_rewrite_eq (f : ℕ → SyntacticTerm L) (φ : S 0) :
    shift (app (Rew.rewrite f) φ) =
      app (Rew.rewrite (cases &0 fun x ↦ Rew.shift (f x))) (shift φ) :=
  by simpa [← comp_app] using smul_ext' <| by ext x <;> simp [Rew.comp_app]


-- @@ L1086-1088 expanded
lemma rewrite_subst_eq (f : ℕ → SyntacticTerm L) (t) (φ : S 1) :
    app (Rew.rewrite f) (LO.FirstOrder.Rewriting.substitute φ ![t]) =
      LO.FirstOrder.Rewriting.substitute (app (Rew.rewrite (Rew.bShift ∘ f)) φ)
        ![Rew.rewrite f t] :=
  by simpa [← comp_app] using smul_ext' <| by ext x <;> simp [Rew.comp_app]


-- @@ L1090-1093 verbatim
@[simp] lemma free_substs_nil (φ : S 0) : free (Rewriting.substitute (ξ := ℕ) φ ![]) = shift φ := by
  simpa [←comp_app] using smul_ext' <| by
    ext x <;> simp only [Rew.comp_app, Rew.substs_fvar, Rew.free_fvar,
      Rew.shift_fvar]; { exact Fin.elim0 x }


-- @@ L1095-1101 expanded
lemma rewrite_substs_nil (f : ℕ → SyntacticTerm L) (φ : S 0) :
    app (Rew.rewrite (Rew.bShift ∘ f)) (Rewriting.substitute (ξ := ℕ) φ ![]) =
      Rewriting.substitute (ξ := ℕ) (app (Rew.rewrite f) φ) ![] :=
  by
  simpa [← comp_app] using
    smul_ext' <| by
      ext x
      · exact x.elim0
      · simp [Rew.comp_app, Rew.bShift_eq_rewrite]


-- @@ L1103-1109 expanded
@[simp]
lemma cast_substs_eq (t : SyntacticTerm L) (φ : S 0) :
    LO.FirstOrder.Rewriting.substitute (Rewriting.substitute (ξ := ℕ) φ ![]) ![t] = φ :=
  by
  suffices
    LO.FirstOrder.Rewriting.substitute (Rewriting.substitute (ξ := ℕ) φ ![]) ![t] = app Rew.id φ by
    rwa [ReflectiveRewriting.id_app] at this
  simpa [← comp_app, -id_app] using
    smul_ext' <|
      by
      ext x <;> simp only [Rew.comp_app, Rew.substs_bvar, Rew.substs_fvar, Rew.id_app]
      exact x.elim0


-- @@ L1111-1113 expanded
lemma rewrite_free_eq_subst (t : SyntacticTerm L) (φ : S 1) :
    app (Rew.rewrite (cases t fun x ↦ &x)) (free φ) = LO.FirstOrder.Rewriting.substitute φ ![t] :=
  by simpa [← comp_app] using smul_ext' <| by ext x <;> simp [Rew.comp_app, Fin.fin_one_eq_zero]


-- @@ L1115-1118 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def shiftEmb : S n ↪ S n where
  toFun := shift
  inj' := shift_injective


-- @@ L1120-1121 verbatim
lemma shiftEmb_def (φ : S n) :
  shiftEmb φ = shift φ := rfl


-- @@ L1123-1125 expanded
lemma allClosure_fixitr (φ : S 0) :
    univClosure (app (Rew.fixitr 0 (m + 1)) φ) =
      UnivQuantifier.univ (app Rew.fix (univClosure (app (Rew.fixitr 0 m) φ))) :=
  by simp [Rew.fixitr_succ, fix_allClosure, comp_app]


-- @@ L1127-1129 verbatim
@[simp] lemma mem_shifts_iff {φ : S n} {Γ : List (S n)} :
    Rewriting.shift φ ∈ Γ⁺ ↔ φ ∈ Γ :=
  List.mem_map_of_injective shift_injective


-- @@ L1131-1132 verbatim
@[simp] lemma shifts_ss (Γ Δ : List (S n)) :
    Γ⁺ ⊆ Δ⁺ ↔ Γ ⊆ Δ := List.map_subset_iff _ shift_injective


-- @@ L1134-1134 verbatim
end LawfulSyntacticRewriting


-- @@ L1136-1136 verbatim
namespace Rewriting


-- @@ L1138-1138 verbatim
variable {ο ξ : Type*} [IsEmpty ο] {O F : ℕ → Type*} [LCWQ O] [LCWQ F]


-- @@ L1140-1140 verbatim
open ReflectiveRewriting TransitiveRewriting InjMapRewriting


-- @@ L1142-1146 verbatim
lemma embedding_injective
    [Rewriting L ο O ξ F] [InjMapRewriting L ο O ξ F] : Function.Injective fun φ :
    O n ↦ (embedding (ξ := ξ) φ :
    F n) :=
  smul_map_injective Function.injective_id (IsEmpty.elim inferInstance)


-- @@ L1148-1150 expanded
@[simp]
lemma emb_univClosure [Rewriting L ο O ξ F] {σ : O n} :
    (embedding (ξ := ξ) (univClosure σ)) = univClosure (embedding (ξ := ξ) σ) := by
  induction n <;> simp [*, univClosure_succ]


-- @@ L1152-1165 expanded
/-- `coe_substs_eq_substs_coe` -/
lemma embedding_substitute_eq_substitute_embedding [Rewriting L ο O ο O] [Rewriting L ο O ξ F]
    [Rewriting L ξ F ξ F] [TransitiveRewriting L ο O ο O ξ F] [TransitiveRewriting L ο O ξ F ξ F]
    (φ : O k) (v : Fin k → Semiterm L ο n) :
    (embedding (ξ := ξ) (LO.FirstOrder.Rewriting.substitute φ v)) =
      Rewriting.substitute (ξ := ξ) (embedding (ξ := ξ) φ) (fun i ↦ Rew.emb (v i)) :=
  by
  unfold embedding substitute
  rw [← comp_app, ← comp_app]
  congr 2
  ext x
  · simp [Rew.comp_app]
  · exact IsEmpty.elim inferInstance x


-- @@ L1167-1174 expanded
/-- `coe_substs_eq_substs_coe₁` -/
lemma embedding_substs_eq_substs_coe₁ [Rewriting L ο O ο O] [Rewriting L ο O ξ F]
    [Rewriting L ξ F ξ F] [TransitiveRewriting L ο O ο O ξ F] [TransitiveRewriting L ο O ξ F ξ F]
    (φ : O 1) (t : Semiterm L ο n) :
    (embedding (ξ := ξ) (LO.FirstOrder.Rewriting.substitute φ ![t])) =
      LO.FirstOrder.Rewriting.substitute (embedding (ξ := ξ) φ) ![(Rew.emb t : Semiterm L ξ n)] :=
  by simpa [Matrix.constant_eq_singleton] using embedding_substitute_eq_substitute_embedding φ ![t]


-- @@ L1176-1176 verbatim
variable {S : ℕ → Type*} [LCWQ S] [SyntacticRewriting L S S] [LawfulSyntacticRewriting L S]


-- @@ L1178-1187 verbatim
@[simp] lemma shifts_emb
    [Rewriting L ο O ℕ F] [Rewriting L ℕ F ℕ F]
    [TransitiveRewriting L ο O ℕ F ℕ F]
    (Γ : List (O n)) :
    (Γ.map (Rewriting.embedding (ξ := ℕ)))⁺ = Γ.map (Rewriting.embedding (ξ := ℕ)) := by
  suffices ∀ a ∈ Γ, shift (embedding (ξ :=
    ℕ) a) = embedding (ξ := ℕ) a by simp [shifts, Function.comp_def, ← comp_app]
  intro j hj
  unfold embedding shift
  rw [←comp_app]; simp_all


-- @@ L1189-1189 verbatim
end Rewriting


-- @@ L1191-1191 verbatim
end FirstOrder

-- @@ L1192-1192 verbatim
end LO
