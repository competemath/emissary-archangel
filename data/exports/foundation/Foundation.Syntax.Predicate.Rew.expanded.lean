module

public import Foundation.Syntax.Predicate.Quantifier
public import Foundation.Syntax.Predicate.Term
public import Foundation.Vorspiel.Function
public import Foundation.Vorspiel.Multiset


-- @@ L8-20 verbatim
/-!
# Rewriting

term/formula morphisms such as rewritings, substitutions, and embeddings are handled by the structure `FFL.FirstOrder.Rew`.
- `FFL.FirstOrder.Rew.rewrite f` is a rewriting of the free variables occurring in a term by `f : ξ₁ → Semiterm L ξ₂ n`.
- `FFL.FirstOrder.Rew.subst v` is a substitution of the bounded variables occurring in a term by `v : Fin n → Semiterm L ξ n'`.
- `FFL.FirstOrder.Rew.bShift` is a transformation of the bounded variables occurring in a term by `#x ↦ #(Fin.succ x)`.
- `FFL.FirstOrder.Rew.shift` is a transformation of the free variables occurring in a term by `&x ↦ &(x + 1)`.
- `FFL.FirstOrder.Rew.emb` is a embedding of a term with no free variables.

Rewritings `FFL.FirstOrder.Rew` is naturally converted to formula rewritings by `FFL.FirstOrder.Rew.hom`.

-/


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
namespace FFL


-- @@ L26-26 verbatim
namespace FirstOrder


-- @@ L28-37 verbatim
/--
A structure for maps which rewrite the semiterms occurring in a term.

toFun - A function from `Semiterm L ξ₁ n₁` to `Semiterm L ξ₂ n₂`.

func'' - A proof that `toFun` respects the function symbols of `L`.
-/
structure Rew (L : Language) (ξ₁ : Type*) (n₁ : ℕ) (ξ₂ : Type*) (n₂ : ℕ) where
  toFun : Semiterm L ξ₁ n₁ → Semiterm L ξ₂ n₂
  func'' (f : L.Func k) (v : Fin k → Semiterm L ξ₁ n₁) : toFun (Semiterm.func f v) = Semiterm.func f fun i ↦ toFun (v i)


-- @@ L39-39 verbatim
abbrev SyntacticRew (L : Language) (n₁ n₂ : ℕ) := Rew L ℕ n₁ ℕ n₂


-- @@ L41-41 verbatim
namespace Rew


-- @@ L43-43 verbatim
open Semiterm

-- @@ L44-44 verbatim
variable {L L' L₁ L₂ L₃ : Language} {ξ ξ' ξ₁ ξ₂ ξ₃ : Type*} {n n₁ n₂ n₃ : ℕ}

-- @@ L45-45 verbatim
variable (ω : Rew L ξ₁ n₁ ξ₂ n₂)


-- @@ L47-49 verbatim
instance : FunLike (Rew L ξ₁ n₁ ξ₂ n₂) (Semiterm L ξ₁ n₁) (Semiterm L ξ₂ n₂) where
  coe := fun f => f.toFun
  coe_injective := fun f g h => by rcases f; rcases g; simpa using h


-- @@ L51-51 verbatim
instance : CoeFun (Rew L ξ₁ n₁ ξ₂ n₂) (fun _ => Semiterm L ξ₁ n₁ → Semiterm L ξ₂ n₂) := DFunLike.toCoeFun


-- @@ L53-57 verbatim
@[simp] protected lemma func {k} (f : L.Func k) (v : Fin k → Semiterm L ξ₁ n₁) :
    ω (func f v) = func f (ω ∘ v) := ω.func'' f v

lemma func' {k} (f : L.Func k) (v : Fin k → Semiterm L ξ₁ n₁) :
    ω (func f v) = func f fun i ↦ ω (v i) := ω.func'' f v


-- @@ L59-63 verbatim
@[ext] lemma ext (ω₁ ω₂ : Rew L ξ₁ n₁ ξ₂ n₂) (hb : ∀ x, ω₁ #x = ω₂ #x) (hf : ∀ x, ω₁ &x = ω₂ &x) : ω₁ = ω₂ := by
  apply DFunLike.ext ω₁ ω₂; intro t
  induction t <;> simp [*, ω₁.func, ω₂.func, Function.comp_def]

lemma ext' {ω₁ ω₂ : Rew L ξ₁ n₁ ξ₂ n₂} (h : ω₁ = ω₂) (t) : ω₁ t = ω₂ t := by simp [h]


-- @@ L65-67 verbatim
protected def id : Rew L ξ n ξ n where
  toFun := id
  func'' := fun _ _ => rfl


-- @@ L69-69 verbatim
@[simp] lemma id_app (t : Semiterm L ξ n) : Rew.id t = t := rfl


-- @@ L71-76 verbatim
protected def comp (ω₂ : Rew L ξ₂ n₂ ξ₃ n₃) (ω₁ : Rew L ξ₁ n₁ ξ₂ n₂) : Rew L ξ₁ n₁ ξ₃ n₃ where
  toFun := fun t => ω₂ (ω₁ t)
  func'' := fun f v => by simp; rfl

lemma comp_app (ω₂ : Rew L ξ₂ n₂ ξ₃ n₃) (ω₁ : Rew L ξ₁ n₁ ξ₂ n₂) (t : Semiterm L ξ₁ n₁) :
    (ω₂.comp ω₁) t = ω₂ (ω₁ t) := rfl


-- @@ L78-78 verbatim
@[simp] lemma id_comp (ω : Rew L ξ₁ n₁ ξ₂ n₂) : Rew.id.comp ω = ω := by ext <;> simp [comp_app]


-- @@ L80-80 verbatim
@[simp] lemma comp_id (ω : Rew L ξ₁ n₁ ξ₂ n₂) : ω.comp Rew.id = ω := by ext <;> simp [comp_app]


-- @@ L82-85 verbatim
def bindAux (b : Fin n₁ → Semiterm L ξ₂ n₂) (e : ξ₁ → Semiterm L ξ₂ n₂) : Semiterm L ξ₁ n₁ → Semiterm L ξ₂ n₂
  |       #x => b x
  |       &x => e x
  | func f v => func f (fun i => bindAux b e (v i))


-- @@ L87-90 verbatim
/-- `FFL.FirstOrder.Rew.bind f` is a substitution of the bound variables occurring in a term by `b : Fin n₁ → Semiterm L ξ₂ n₂`, and the free variables occurring in a term by `e : ξ₁ → Semiterm L ξ₂ n₂`. -/
def bind (b : Fin n₁ → Semiterm L ξ₂ n₂) (e : ξ₁ → Semiterm L ξ₂ n₂) : Rew L ξ₁ n₁ ξ₂ n₂ where
  toFun := bindAux b e
  func'' := fun _ _ => rfl


-- @@ L92-93 verbatim
/-- `FFL.FirstOrder.Rew.rewrite f` is a substitution of the free variables occurring in a term by `f : ξ₁ → Semiterm L ξ₂ n`. -/
def rewrite (f : ξ₁ → Semiterm L ξ₂ n) : Rew L ξ₁ n ξ₂ n := bind Semiterm.bvar f


-- @@ L95-96 verbatim
/-- `FFL.FirstOrder.Rew.rewriteMap` f is a substitution of the free variables occurring in a term by `e : ξ₁ → ξ₂`. -/
def rewriteMap (e : ξ₁ → ξ₂) : Rew L ξ₁ n ξ₂ n := rewrite (fun m => &(e m))


-- @@ L98-99 verbatim
def map (b : Fin n₁ → Fin n₂) (e : ξ₁ → ξ₂) : Rew L ξ₁ n₁ ξ₂ n₂ :=
  bind (fun n => #(b n)) (fun m => &(e m))


-- @@ L101-103 verbatim
/-- `FFL.FirstOrder.Rew.subst v` is a substitution of the bound variables occurring in a term by `v : Fin n → Semiterm L ξ n'`. -/
def subst {n'} (v : Fin n → Semiterm L ξ n') : Rew L ξ n ξ n' :=
  bind v fvar


-- @@ L105-106 verbatim
/-- `FFL.FirstOrder.Rew.emb` is a embedding of a term with no free variables. It can be thought of as a cast from `Semiterm L Empty n` to `Semiterm L ξ n` for any type `ξ`. -/
def emb {o : Type v₁} [h : IsEmpty o] {ξ : Type v₂} {n} : Rew L o n ξ n := map id h.elim


-- @@ L108-108 verbatim
abbrev embs {o : Type v₁} [IsEmpty o] {n} : Rew L o n ℕ n := emb


-- @@ L110-110 verbatim
def empty {o : Type v₁} [h : IsEmpty o] {ξ : Type v₂} {n} : Rew L o 0 ξ n := map Fin.elim0 h.elim


-- @@ L112-114 verbatim
/-- `FFL.FirstOrder.Rew.bShift` is a transformation of the bounded variables occurring in a term by `#x ↦ #(Fin.succ x)`. -/
def bShift : Rew L ξ n ξ (n + 1) :=
  map Fin.succ id


-- @@ L116-117 verbatim
def bShiftAdd (m : ℕ) : Rew L ξ n ξ (n + m) :=
  map (Fin.addNat · m) id


-- @@ L119-120 verbatim
def cast {n n' : ℕ} (h : n = n') : Rew L ξ n ξ n' :=
  map (Fin.cast h) id


-- @@ L122-123 verbatim
def castLE {n n' : ℕ} (h : n ≤ n') : Rew L ξ n ξ n' :=
  map (Fin.castLE h) id


-- @@ L125-127 verbatim
/-- `FFL.FirstOrder.Rew.embSubsts v` is a substitution of the bound variables occurring in a term with no free variables by `v : Fin n → Semiterm L ξ n'`.
This closely resembles `FFL.FirstOrder.Rew.subst`, however the term is required to have free variables of type `Empty`. -/
def embSubsts (v : Fin k → Semiterm L ξ n) : Rew L Empty k ξ n := Rew.bind v Empty.elim


-- @@ L129-134 verbatim
protected def q (ω : Rew L ξ₁ n₁ ξ₂ n₂) : Rew L ξ₁ (n₁ + 1) ξ₂ (n₂ + 1) :=
  bind (#0 :> bShift ∘ ω ∘ bvar) (bShift ∘ ω ∘ fvar)

lemma eq_id_of_eq {ω : Rew L ξ n ξ n} (hb : ∀ x, ω #x = #x) (he : ∀ x, ω &x = &x) (t) : ω t = t := by
  have : ω = Rew.id := by ext <;> simp [*]
  simp [this]


-- @@ L136-138 verbatim
def qpow (ω : Rew L ξ₁ n₁ ξ₂ n₂) : (k : ℕ) → Rew L ξ₁ (n₁ + k) ξ₂ (n₂ + k)
  |     0 => ω
  | k + 1 => (ω.qpow k).q


-- @@ L140-140 verbatim
@[simp] lemma qpow_zero (ω : Rew L ξ₁ n₁ ξ₂ n₂) : qpow ω 0 = ω := rfl


-- @@ L142-142 verbatim
@[simp] lemma qpow_succ (ω : Rew L ξ₁ n₁ ξ₂ n₂) (k : ℕ) : qpow ω (k + 1) = (ω.qpow k).q := rfl


-- @@ L144-144 verbatim
section bind


-- @@ L146-146 verbatim
variable (b : Fin n₁ → Semiterm L ξ₂ n₂) (e : ξ₁ → Semiterm L ξ₂ n₂)


-- @@ L148-148 verbatim
@[simp] lemma bind_fvar (m : ξ₁) : bind b e (&m : Semiterm L ξ₁ n₁) = e m := rfl


-- @@ L150-155 verbatim
@[simp] lemma bind_bvar (n : Fin n₁) : bind b e (#n : Semiterm L ξ₁ n₁) = b n := rfl

lemma eq_bind (ω : Rew L ξ₁ n₁ ξ₂ n₂) : ω = bind (ω ∘ bvar) (ω ∘ fvar) := by
  ext t; induction t
  · simp
  · simp [*]


-- @@ L157-158 verbatim
@[simp] lemma bind_eq_id_of_zero (f : Fin 0 → Semiterm L ξ₂ 0) : bind f fvar = Rew.id := by
  ext x <;> simp only [bind_bvar, bind_fvar, id_app]; exact Fin.elim0 x


-- @@ L160-160 verbatim
end bind


-- @@ L162-162 verbatim
section map


-- @@ L164-164 verbatim
variable (b : Fin n₁ → Fin n₂) (e : ξ₁ → ξ₂)


-- @@ L166-166 verbatim
@[simp] lemma map_fvar (m : ξ₁) : map b e (&m : Semiterm L ξ₁ n₁) = &(e m) := rfl


-- @@ L168-168 verbatim
@[simp] lemma map_bvar (n : Fin n₁) : map b e (#n : Semiterm L ξ₁ n₁) = #(b n) := rfl


-- @@ L170-190 verbatim
@[simp] lemma map_id : map (L := L) (id : Fin n → Fin n) (id : ξ → ξ) = Rew.id := by ext <;> simp

lemma map_inj {b : Fin n₁ → Fin n₂} {e : ξ₁ → ξ₂} (hb : Function.Injective b) (he : Function.Injective e) :
    Function.Injective <| map (L := L) b e
  |                    #x,                    #y => by simpa using @hb _ _
  |                    #x,                    &y => by simp
  |                    #x,              func f w => by simp [Rew.func]
  |                    &x,                    #y => by simp
  |                    &x,                    &y => by simpa using @he _ _
  |                    &x,              func f w => by simp [Rew.func]
  |              func f v,                    #y => by simp [Rew.func]
  |              func f v,                    &y => by simp [Rew.func]
  | func (arity := k) f v, func (arity := l) g w => fun h ↦ by
    have : k = l := by simp [Rew.func] at h; simp_all
    rcases this
    have : f = g := by simp [Rew.func] at h; simp_all
    rcases this
    have : v = w := by
      have : (fun i ↦ (map b e) (v i)) = (fun i ↦ (map b e) (w i)) := by simpa [Rew.func, Function.comp_def] using h
      funext i; exact map_inj hb he (congrFun this i)
    simp_all


-- @@ L192-192 verbatim
end map


-- @@ L194-194 verbatim
section rewrite


-- @@ L196-196 verbatim
variable (f : ξ₁ → Semiterm L ξ₂ n)


-- @@ L198-198 verbatim
@[simp] lemma rewrite_fvar (x : ξ₁) : rewrite f &x = f x := rfl


-- @@ L200-204 verbatim
@[simp] lemma rewrite_bvar (x : Fin n) : rewrite e (#x : Semiterm L ξ₁ n) = #x := rfl

lemma rewrite_comp_rewrite (v : ξ₂ → Semiterm L ξ₃ n) (w : ξ₁ → Semiterm L ξ₂ n) :
    (rewrite v).comp (rewrite w) = rewrite (rewrite v ∘ w) := by
  ext <;> simp [comp_app]


-- @@ L206-206 verbatim
@[simp] lemma rewrite_eq_id : (rewrite Semiterm.fvar : Rew L ξ n ξ n) = Rew.id := by ext <;> simp


-- @@ L208-208 verbatim
end rewrite


-- @@ L210-210 verbatim
section rewriteMap


-- @@ L212-212 verbatim
variable (e : ξ₁ → ξ₂)


-- @@ L214-214 verbatim
@[simp] lemma rewriteMap_fvar (x : ξ₁) : rewriteMap e (&x : Semiterm L ξ₁ n) = &(e x) := rfl


-- @@ L216-216 verbatim
@[simp] lemma rewriteMap_bvar (x : Fin n) : rewriteMap e (#x : Semiterm L ξ₁ n) = #x := rfl


-- @@ L218-228 verbatim
@[simp] lemma rewriteMap_id : rewriteMap (L := L) (n := n) (id : ξ → ξ) = Rew.id := by ext <;> simp

lemma eq_rewriteMap_of_funEqOn_fv [DecidableEq ξ₁] (t : Semiterm L ξ₁ n₁) (f g : ξ₁ → Semiterm L ξ₂ n₂) (h : Function.funEqOn t.FVar? f g) :
    Rew.rewriteMap f t = Rew.rewriteMap g t := by
  induction t
  case bvar => simp
  case fvar x => simpa using h x (by simp)
  case func f v ih =>
    simp only [Rew.func, func.injEq, heq_eq_eq, true_and]
    funext i
    exact ih i (fun x hx ↦ h x (by simpa [Semiterm.fvar?_func] using ⟨i, hx⟩))


-- @@ L230-230 verbatim
end rewriteMap


-- @@ L232-232 verbatim
section emb


-- @@ L234-234 verbatim
variable {o : Type v₂} [IsEmpty o]


-- @@ L236-236 verbatim
@[simp] lemma emb_bvar (x : Fin n) : emb (ξ := ξ) (#x : Semiterm L o n) = #x := rfl


-- @@ L238-242 verbatim
@[simp] lemma emb_eq_id : (emb : Rew L o n o n) = Rew.id := by
  ext x <;> simp only [emb_bvar, id_app]; exact isEmptyElim x

lemma eq_empty [h : IsEmpty ξ₁] (ω : Rew L ξ₁ 0 ξ₂ n) :
  ω = empty := by ext x; { exact x.elim0 }; { exact h.elim' x }


-- @@ L244-244 verbatim
end emb


-- @@ L246-246 verbatim
section bShift


-- @@ L248-248 verbatim
@[simp] lemma bShift_bvar (x : Fin n) : bShift (#x : Semiterm L ξ n) = #(Fin.succ x) := rfl


-- @@ L250-250 verbatim
@[simp] lemma bShift_fvar (x : ξ) : bShift (&x : Semiterm L ξ n) = &x := rfl


-- @@ L252-253 verbatim
@[simp] lemma bShift_ne_zero (t : Semiterm L ξ n) : bShift t ≠ #0 := by
  cases t <;> simp [Rew.func, Fin.succ_ne_zero]


-- @@ L255-270 verbatim
@[simp] lemma bShift_positive (t : Semiterm L ξ n) : (bShift t).Positive := by
  induction t <;> simp [Rew.func, *]

lemma positive_iff {t : Semiterm L ξ (n + 1)} : t.Positive ↔ ∃ t', t = bShift t' :=
  ⟨by induction t
      case bvar x =>
        simp only [Positive.bvar]
        intro hx; exact ⟨#(x.pred (Fin.pos_iff_ne_zero.mp hx)), by simp⟩
      case fvar x => simpa using ⟨&x, by simp⟩
      case func k f v ih =>
        simp only [Positive.func]
        intro h
        have : ∀ i, ∃ t', v i = bShift t' := fun i => ih i (h i)
        choose w hw using this
        exact ⟨func f w, by simp only [Rew.func, func.injEq, heq_eq_eq, true_and]; funext i; exact hw i⟩,
   by rintro ⟨t', rfl⟩; simp⟩


-- @@ L272-274 verbatim
@[simp] lemma leftConcat_bShift_comp_bvar :
    (#0 :> bShift ∘ bvar : Fin (n + 1) → Semiterm L ξ (n + 1)) = bvar :=
  funext (Fin.cases (by simp) (by simp))


-- @@ L276-278 verbatim
@[simp] lemma bShift_comp_fvar :
    (bShift ∘ fvar : ξ → Semiterm L ξ (n + 1)) = fvar :=
  funext (by simp)


-- @@ L280-280 verbatim
end bShift


-- @@ L282-282 verbatim
section bShiftAdd


-- @@ L284-284 verbatim
@[simp] lemma bShiftAdd_bvar (m) (x : Fin n) : bShiftAdd m (#x : Semiterm L ξ n) = #(Fin.addNat x m) := rfl


-- @@ L286-286 verbatim
@[simp] lemma bShiftAdd_fvar (m) (x : ξ) : bShiftAdd m (&x : Semiterm L ξ n) = &x := rfl


-- @@ L288-288 verbatim
end bShiftAdd


-- @@ L290-290 verbatim
section subst


-- @@ L292-292 verbatim
variable {n'} (w : Fin n → Semiterm L ξ n')


-- @@ L294-295 verbatim
@[simp] lemma subst_bvar (x : Fin n) : subst w #x = w x := by
  simp [subst]


-- @@ L297-298 verbatim
@[simp] lemma subst_fvar (x : ξ) : subst w &x = &x := by
  simp [subst]


-- @@ L300-307 verbatim
@[simp] lemma subst_zero (w : Fin 0 → Term L ξ) : subst w = Rew.id := by
  ext x
  · exact Fin.elim0 x
  · simp

lemma subst_comp_subst (v : Fin l → Semiterm L ξ k) (w : Fin k → Semiterm L ξ n) :
    (subst w).comp (subst v) = subst (subst w ∘ v) := by
  ext <;> simp [comp_app]


-- @@ L309-309 verbatim
@[simp] lemma subst_eq_id : (subst Semiterm.bvar : Rew L ξ n ξ n) = Rew.id := by ext <;> simp


-- @@ L311-311 verbatim
end subst


-- @@ L313-313 verbatim
section cast


-- @@ L315-315 verbatim
variable {n'} (h : n = n')


-- @@ L317-317 verbatim
@[simp] lemma cast_bvar (x : Fin n) : cast h (#x : Semiterm L ξ n) = #(Fin.cast h x) := rfl


-- @@ L319-319 verbatim
@[simp] lemma cast_fvar (x : ξ) : cast h (&x : Semiterm L ξ n) = &x := rfl


-- @@ L321-321 verbatim
@[simp] lemma cast_eq_id {h} : (cast h : Rew L ξ n ξ n) = Rew.id := by ext <;> simp


-- @@ L323-323 verbatim
end cast


-- @@ L325-325 verbatim
section castLE


-- @@ L327-327 verbatim
@[simp] lemma castLe_bvar {n'} (h : n ≤ n') (x : Fin n) : castLE h (#x : Semiterm L ξ n) = #(Fin.castLE h x) := rfl


-- @@ L329-329 verbatim
@[simp] lemma castLe_fvar {n'} (h : n ≤ n') (x : ξ) : castLE h (&x : Semiterm L ξ n) = &x := rfl


-- @@ L331-331 verbatim
@[simp] lemma castLe_eq_id {h} : (castLE h : Rew L ξ n ξ n) = Rew.id := by ext <;> simp


-- @@ L333-335 verbatim
@[simp] lemma castLE_comp {h₁ : n₁ ≤ n₂} {h₂ : n₂ ≤ n₃} :
    (castLE h₂).comp (castLE h₁) = (castLE (h₁.trans h₂) : Rew L ξ n₁ ξ n₃) := by
  ext x <;> simp [comp_app]


-- @@ L337-337 verbatim
end castLE


-- @@ L339-339 verbatim
section embSubsts


-- @@ L341-341 verbatim
variable {k} (w : Fin k → Semiterm L ξ n)


-- @@ L343-344 verbatim
@[simp] lemma embSubsts_bvar (x : Fin k) : embSubsts w #x = w x := by
  simp [embSubsts]


-- @@ L346-355 verbatim
@[simp] lemma embSubsts_zero (w : Fin 0 → Term L ξ) : embSubsts w = Rew.emb := by
  ext x
  · exact Fin.elim0 x
  · exact Empty.elim x

lemma subst_comp_embSubsts (v : Fin l → Semiterm L ξ k) (w : Fin k → Semiterm L ξ n) :
    (subst w).comp (embSubsts v) = embSubsts (subst w ∘ v) := by
  ext x
  · simp [comp_app]
  · exact Empty.elim x


-- @@ L357-359 verbatim
@[simp] lemma embSubsts_eq_id : (embSubsts Semiterm.bvar : Rew L Empty n ξ n) = Rew.emb := by
  ext x <;> try simp
  · exact Empty.elim x


-- @@ L361-361 verbatim
end embSubsts


-- @@ L363-363 verbatim
section ψ


-- @@ L365-365 verbatim
variable (ω : Rew L ξ₁ n₁ ξ₂ n₂)


-- @@ L367-367 verbatim
@[simp] lemma q_bvar_zero : ω.q #0 = #0 := by simp [Rew.q]


-- @@ L369-369 verbatim
@[simp] lemma q_bvar_succ (i : Fin n₁) : ω.q #(i.succ) = bShift (ω #i) := by simp [Rew.q]


-- @@ L371-371 verbatim
@[simp] lemma q_fvar (x : ξ₁) : ω.q &x = bShift (ω &x) := by simp [Rew.q]


-- @@ L373-374 verbatim
@[simp] lemma q_comp_bShift : ω.q.comp bShift = bShift.comp ω := by
  ext x <;> simp [comp_app]


-- @@ L376-377 verbatim
@[simp] lemma q_comp_bShift_app (t : Semiterm L ξ₁ n₁) : ω.q (bShift t) = bShift (ω t) := by
  have := ext' (ω.q_comp_bShift) t; simpa only [comp_app] using this


-- @@ L379-382 verbatim
@[simp] lemma q_id : (Rew.id : Rew L ξ n ξ n).q = Rew.id := by
  ext x
  · cases x using Fin.cases <;> simp
  · simp


-- @@ L384-389 verbatim
@[simp] lemma q_eq_zero_iff : ω.q t = #0 ↔ t = #0 := by
  cases t
  case bvar i =>
    cases i using Fin.cases <;> simp [Fin.succ_ne_zero]
  · simp
  · simp [Rew.func]


-- @@ L391-396 verbatim
@[simp] lemma q_positive_iff : (ω.q t).Positive ↔ t.Positive := by
  induction t
  case bvar x =>
    cases x using Fin.cases <;> simp
  · simp
  · simp [Rew.func, *]


-- @@ L398-426 verbatim
@[simp] lemma qpow_id {k} : (Rew.id : Rew L ξ n ξ n).qpow k = Rew.id := by induction k <;> simp [*]

lemma q_comp (ω₂ : Rew L ξ₂ n₂ ξ₃ n₃) (ω₁ : Rew L ξ₁ n₁ ξ₂ n₂) :
    (Rew.comp ω₂ ω₁).q = ω₂.q.comp ω₁.q := by
  ext x
  · cases x using Fin.cases <;> simp [comp_app]
  · simp [comp_app]

lemma qpow_comp (k) (ω₂ : Rew L ξ₂ n₂ ξ₃ n₃) (ω₁ : Rew L ξ₁ n₁ ξ₂ n₂) :
    (Rew.comp ω₂ ω₁).qpow k = (ω₂.qpow k).comp (ω₁.qpow k) := by
  induction k <;> simp [*, q_comp]

lemma q_bind (b : Fin n₁ → Semiterm L ξ₂ n₂) (e : ξ₁ → Semiterm L ξ₂ n₂) :
    (bind b e).q = bind (#0 :> bShift ∘ b) (bShift ∘ e) := by
  ext x
  · cases x using Fin.cases <;> simp
  · simp

lemma q_map (b : Fin n₁ → Fin n₂) (e : ξ₁ → ξ₂) :
    (map (L := L) b e).q = map (0 :> Fin.succ ∘ b) e := by
  ext x
  · cases x using Fin.cases <;> simp
  · simp

lemma q_rewrite (f : ξ₁ → Semiterm L ξ₂ n) :
    (rewrite f).q = rewrite (bShift ∘ f) := by
  ext x
  · cases x using Fin.cases <;> simp
  · simp


-- @@ L428-432 verbatim
@[simp] lemma q_rewriteMap (e : ξ₁ → ξ₂) :
    (rewriteMap (L := L) (n := n) e).q = rewriteMap e := by
  ext x
  · cases x using Fin.cases <;> simp
  · simp


-- @@ L434-438 verbatim
@[simp] lemma q_emb {o : Type v₁} [e : IsEmpty o] {n} :
    (emb (L := L) (o := o) (ξ := ξ₂) (n := n)).q = emb := by
  ext x
  · cases x using Fin.cases <;> simp
  · exact e.elim x


-- @@ L440-441 verbatim
@[simp] lemma qpow_emb {o : Type v₁} [e : IsEmpty o] {n k} :
    (emb (L := L) (o := o) (ξ := ξ₂) (n := n)).qpow k = emb := by induction k <;> simp [*]


-- @@ L443-445 verbatim
@[simp] lemma q_cast {n n'} (h : n = n') :
    (cast h : Rew L ξ n ξ n').q = cast (congrFun (congrArg HAdd.hAdd h) 1) := by
  ext x <;> simp; cases x using Fin.cases <;> simp


-- @@ L447-449 verbatim
@[simp] lemma q_castLE {n n'} (h : n ≤ n') :
    (castLE h : Rew L ξ n ξ n').q = castLE (Nat.add_le_add_right h 1) := by
  ext x <;> simp; cases x using Fin.cases <;> simp


-- @@ L451-459 verbatim
@[simp] lemma qpow_castLE {n n'} (h : n ≤ n') :
    (castLE h : Rew L ξ n ξ n').qpow k = castLE (Nat.add_le_add_right h k) := by
  induction k <;> simp [*]

lemma q_subst (w : Fin n → Semiterm L ξ n') :
    (subst w).q = subst (#0 :> bShift ∘ w) := by ext x; { cases x using Fin.cases <;> simp }; { simp }

lemma q_embSubsts (w : Fin k → Semiterm L ξ n) :
    (embSubsts w).q = embSubsts (#0 :> bShift ∘ w) := by ext x; { cases x using Fin.cases <;> simp }; { simpa using Empty.elim x }


-- @@ L461-461 verbatim
end ψ


-- @@ L463-469 verbatim
section Syntactic

/-
  #0 #1 ... #(n - 1) &0 &1 ...
   ↓shift
  #0 #1 ... #(n - 1) &1 &2 &3 ...
-/


-- @@ L471-478 verbatim
/-- `FFL.FirstOrder.Rew.shift` is a transformation of the free variables occurring in the term by `&x ↦ &(x + 1)`. -/
def shift : SyntacticRew L n n := map id Nat.succ

/-
  #0 #1 ... #(n - 1) #n &0 &1 ...
   ↓free           ↑fix
  #0 #1 ... #(n - 1) &0 &1 &2 ...
 -/


-- @@ L480-480 verbatim
def free : SyntacticRew L (n + 1) n := bind (bvar <: &0) (fun m => &(Nat.succ m))


-- @@ L482-482 verbatim
def fix : SyntacticRew L n (n + 1) := bind (fun x => #(Fin.castSucc x)) (#(Fin.last n) :>ₙ fvar)


-- @@ L484-484 verbatim
abbrev rewrite1 (t : SyntacticSemiterm L n) : SyntacticRew L n n := bind Semiterm.bvar (t :>ₙ fvar)


-- @@ L486-486 verbatim
section shift


-- @@ L488-488 verbatim
@[simp] lemma shift_bvar (x : Fin n) : shift (#x : SyntacticSemiterm L n) = #x := rfl


-- @@ L490-497 verbatim
@[simp] lemma shift_fvar (x : ℕ) : shift (&x : SyntacticSemiterm L n) = &(x + 1) := rfl

lemma shift_func {k} (f : L.Func k) (v : Fin k → SyntacticSemiterm L n) :
    shift (func f v) = func f (fun i => shift (v i)) := rfl

lemma shift_Injective : Function.Injective (@shift L n) :=
  Function.LeftInverse.injective (g := map id Nat.pred)
    (by intros φ; simp only [← comp_app]; apply eq_id_of_eq <;> simp [comp_app])


-- @@ L499-499 verbatim
end shift


-- @@ L501-501 verbatim
section free


-- @@ L503-503 verbatim
@[simp] lemma free_bvar_castSucc (x : Fin n) : free (#(Fin.castSucc x) : SyntacticSemiterm L (n + 1)) = #x := by simp [free]


-- @@ L505-505 verbatim
@[simp] lemma free_bvar_castSucc_zero : free (#0 : SyntacticSemiterm L (n + 1 + 1)) = #0 := free_bvar_castSucc 0


-- @@ L507-507 verbatim
@[simp] lemma free_bvar_last : free (#(Fin.last n) : SyntacticSemiterm L (n + 1)) = &0 := by simp [free]


-- @@ L509-509 verbatim
@[simp] lemma free_bvar_last_zero : free (#0 : SyntacticSemiterm L 1) = &0 := free_bvar_last


-- @@ L511-511 verbatim
@[simp] lemma free_fvar (x : ℕ) : free (&x : SyntacticSemiterm L (n + 1)) = &(x + 1) := by simp [free]


-- @@ L513-513 verbatim
end free


-- @@ L515-515 verbatim
section fix


-- @@ L517-517 verbatim
@[simp] lemma fix_bvar (x : Fin n) : fix (#x : SyntacticSemiterm L n) = #(Fin.castSucc x) := by simp [fix]


-- @@ L519-519 verbatim
@[simp] lemma fix_fvar_zero : fix (&0 : SyntacticSemiterm L n) = #(Fin.last n) := by simp [fix]


-- @@ L521-521 verbatim
@[simp] lemma fix_fvar_succ (x : ℕ) : fix (&(x + 1) : SyntacticSemiterm L n) = &x := by simp [fix]


-- @@ L523-523 verbatim
end fix


-- @@ L525-529 verbatim
@[simp] lemma free_comp_fix : (free (L := L) (n := n)).comp fix = Rew.id := by
  ext x
  · simp [comp_app]
  · simp [comp_app]
    cases x <;> simp


-- @@ L531-535 verbatim
@[simp] lemma fix_comp_free : (fix (L := L) (n := n)).comp free = Rew.id := by
  ext x
  · simp [comp_app]
    cases x using Fin.lastCases <;> simp
  · simp [comp_app]


-- @@ L537-549 verbatim
@[simp] lemma bShift_free_eq_shift : (free (L := L) (n := 0)).comp bShift = shift := by
  ext x
  · exact Fin.elim0 x
  · simp [comp_app]

lemma bShift_comp_subst (v : Fin n₁ → Semiterm L ξ₂ n₂) :
    bShift.comp (subst v) = subst (bShift ∘ v) := by ext x <;> simp [comp_app]

lemma shift_comp_subst (v : Fin n₁ → SyntacticSemiterm L n₂) :
    shift.comp (subst v) = (subst (shift ∘ v)).comp shift := by ext x <;> simp [comp_app]

lemma shift_comp_subst1 (t : SyntacticSemiterm L n₂) :
    shift.comp (subst ![t]) = (subst ![shift t]).comp shift := by ext x <;> simp [comp_app]


-- @@ L551-555 verbatim
@[simp] lemma rewrite_comp_emb {o : Type v₁} [e : IsEmpty o] (f : ξ₂ → Semiterm L ξ₃ n) :
    (rewrite f).comp emb = (emb : Rew L o n ξ₃ n) := by
  ext x
  · simp [comp_app]
  · exact IsEmpty.elim e x


-- @@ L557-561 verbatim
@[simp] lemma shift_comp_emb {o : Type v₁} [e : IsEmpty o] :
    shift.comp emb = (emb : Rew L o n ℕ n) := by
  ext x
  · simp [comp_app]
  · exact IsEmpty.elim e x


-- @@ L563-573 verbatim
@[simp] lemma comp_emb_eq_emb {o : Type v₁} [e : IsEmpty o] {ω : Rew L ξ₁ 0 ξ₂ 0} :
    ω.comp emb = (emb : Rew L o 0 ξ₂ 0) := by
  ext x
  · exact Fin.elim0 x
  · exact IsEmpty.elim e x

lemma rewrite_comp_free_eq_subst (t : SyntacticTerm L) :
    (rewrite (t :>ₙ Semiterm.fvar)).comp free = subst ![t] := by ext x <;> simp [comp_app]

lemma rewrite_comp_shift_eq_id (t : SyntacticTerm L) :
    (rewrite (t :>ₙ Semiterm.fvar)).comp shift = Rew.id := by ext x <;> simp [comp_app]


-- @@ L575-576 verbatim
@[simp] lemma subst_mbar_zero_comp_shift_eq_free :
    (subst (L := L) ![&0]).comp shift = free := by ext x <;> simp [comp_app]


-- @@ L578-586 verbatim
@[simp] lemma subst_comp_bShift_eq_id (v : Fin 1 → Semiterm L ξ 0) :
    (subst (L := L) v).comp bShift = Rew.id := by
  ext x
  · exact Fin.elim0 x
  · simp [comp_app]

lemma free_comp_subst_eq_subst_comp_shift {n'} (w : Fin n' → SyntacticSemiterm Lf (n + 1)) :
    free.comp (subst w) = (subst (free ∘ w)).comp shift := by
  ext x <;> simp [comp_app]


-- @@ L588-589 verbatim
@[simp] lemma rewriteMap_comp_rewriteMap (f : ξ₁ → ξ₂) (g : ξ₂ → ξ₃) :
  (rewriteMap (L := L) (n := n) g).comp (rewriteMap f) = rewriteMap (g ∘ f) := by ext x <;> simp [comp_app]


-- @@ L591-591 verbatim
@[simp] lemma fix_free_app (t : SyntacticSemiterm L (n + 1)) : fix (free t) = t := by simp [←comp_app]


-- @@ L593-593 verbatim
@[simp] lemma free_fix_app (t : SyntacticSemiterm L n) : free (fix t) = t := by simp [←comp_app]


-- @@ L595-595 verbatim
@[simp] lemma free_bShift_app (t : SyntacticSemiterm L 0) : free (bShift t) = shift t := by simp [←comp_app]


-- @@ L597-607 verbatim
@[simp] lemma subst_bShift_app (v : Fin 1 → Semiterm L ξ 0) : subst v (bShift t) = t := by simp [←comp_app]

lemma rewrite_comp_fix_eq_subst (t) :
    ((rewrite (t :>ₙ (&·))).comp free : SyntacticRew L 1 0) = subst ![t] := by
  ext x <;> simp [comp_app]

lemma bShift_eq_rewrite :
    (Rew.bShift : SyntacticRew L 0 1) = Rew.subst ![] := by
  ext x
  · exact x.elim0
  · simp


-- @@ L609-609 verbatim
section ψ


-- @@ L611-611 verbatim
variable (ω : SyntacticRew L n₁ n₂)


-- @@ L613-616 verbatim
@[simp] lemma q_shift : (shift (L := L) (n := n)).q = shift := by
  ext x
  · cases x using Fin.cases <;> simp
  · simp


-- @@ L618-624 verbatim
@[simp] lemma q_free : (free (L := L) (n := n)).q = free := by
  ext x
  · cases' x using Fin.cases with x
    · simp
    · simp
      cases x using Fin.lastCases <;> simp [-Fin.castSucc_succ, Fin.succ_castSucc]
  · simp


-- @@ L626-629 verbatim
@[simp] lemma q_fix : (fix (L := L) (n := n)).q = fix := by
  ext x; { cases x using Fin.cases <;> simp [-Fin.castSucc_succ, Fin.succ_castSucc] }; { cases x <;> simp }

--@[simp] lemma qpow_fix (k : ℕ) : (fix (L := L) (n := n)).qpow k = fix := by


-- @@ L631-631 verbatim
end ψ


-- @@ L633-635 verbatim
def fixitr (n : ℕ) : (m : ℕ) → SyntacticRew L n (n + m)
  |     0 => Rew.id
  | m + 1 => Rew.fix.comp (fixitr n m)


-- @@ L637-642 verbatim
@[simp] lemma fixitr_zero :
    fixitr (L := L) n 0 = Rew.id := by simp [fixitr]

lemma fixitr_succ (m) :
    fixitr (L := L) n (m + 1) = Rew.fix.comp (fixitr n m) := by
  simp [fixitr]


-- @@ L644-664 verbatim
@[simp] lemma fixitr_bvar (n m) (x : Fin n) : fixitr n m (#x : SyntacticSemiterm L n) = #(x.castAdd m) := by
  induction m
  · simp [*]
  case succ m ih =>
    rw [fixitr_succ, comp_app, ih]; simp [Fin.castSucc_castAdd]

lemma fixitr_fvar (n m) (x : ℕ) :
    fixitr n m (&x : SyntacticSemiterm L n) = if h : x < m then #(Fin.natAdd n ⟨x, h⟩) else &(x - m) := by
  induction m
  · simp [*]
  case succ m ih =>
    suffices fix (fixitr n m &x) = if h : x < m + 1 then #⟨n + x, _⟩ else &(x - (m + 1)) from Eq.trans (comp_app _ _ _) this
    simp only [ih, Fin.natAdd_mk]
    by_cases hx : x < m
    · simp [hx, Nat.lt_add_right 1 hx]
    by_cases hx2 : x < m + 1
    · have : x = m := Nat.le_antisymm (by { simpa [Nat.lt_succ_iff] using hx2 }) (by simpa using hx)
      aesop
    · simp [hx, hx2]
      have : x - m = x - (m + 1) + 1 := by omega
      simp [this]


-- @@ L666-670 verbatim
end Syntactic

lemma subst_bv (t : Semiterm L ξ n) (v : Fin n → Semiterm L ξ m) :
    (Rew.subst v t).bv = t.bv.biUnion (fun i ↦ (v i).bv) := by
  induction t <;> simp [Rew.func, Semiterm.bv_func, Finset.biUnion_biUnion, *]


-- @@ L672-682 verbatim
@[simp] lemma subst_positive (t : Semiterm L ξ n) (v : Fin n → Semiterm L ξ (m + 1)) :
    (Rew.subst v t).Positive ↔ ∀ i ∈ t.bv, (v i).Positive := by
  simpa [Semiterm.Positive, subst_bv]
    using ⟨fun H i hi x hx ↦ H x i hi hx, fun H x i hi hx ↦ H i hi x hx⟩

lemma embSubsts_bv (t : ClosedSemiterm L n) (v : Fin n → Semiterm L ξ m) :
    (Rew.embSubsts v t).bv = t.bv.biUnion (fun i ↦ (v i).bv) := by
  induction t
  · simp
  · contradiction
  · simp [Rew.func, Semiterm.bv_func, Finset.biUnion_biUnion, *]


-- @@ L684-687 verbatim
@[simp] lemma embSubsts_positive (t : ClosedSemiterm L n) (v : Fin n → Semiterm L ξ (m + 1)) :
    (Rew.embSubsts v t).Positive ↔ ∀ i ∈ t.bv, (v i).Positive := by
  simpa [Semiterm.Positive, embSubsts_bv]
    using ⟨fun H i hi x hx ↦ H x i hi hx, fun H x i hi hx ↦ H i hi x hx⟩


-- @@ L689-700 verbatim
@[simp] lemma bshift_positive (t : Semiterm L ξ n) : Positive (Rew.bShift t) := by
  induction t <;> simp

lemma emb_comp_bShift_comm {o : Type v₁} [IsEmpty o] :
    Rew.bShift.comp (Rew.emb : Rew L o n ξ n) = Rew.emb.comp Rew.bShift := by
  ext x
  · simp [comp_app]
  · exact IsEmpty.elim (by assumption) x

lemma emb_bShift_term {o : Type v₁} [IsEmpty o] (t : Semiterm L o n) :
    Rew.bShift (Rew.emb t : Semiterm L ξ n) = Rew.emb (Rew.bShift t) := by
  simp [←comp_app, emb_comp_bShift_comm]


-- @@ L702-702 verbatim
end Rew


-- @@ L704-704 verbatim
/-! ### Rewriting system of terms -/


-- @@ L706-706 verbatim
namespace Semiterm


-- @@ L708-708 verbatim
variable {L L' L₁ L₂ L₃ : Language} {ξ ξ' ξ₁ ξ₂ ξ₃ : Type*} {n n₁ n₂ n₃ : ℕ}


-- @@ L710-710 verbatim
instance : Coe (ClosedSemiterm L n) (SyntacticSemiterm L n) := ⟨Rew.emb⟩


-- @@ L712-730 verbatim
@[simp] lemma freeVariables_emb {ο : Type*} [IsEmpty ο] [DecidableEq ξ] {t : Semiterm L ο n} :
    (Rew.emb t : Semiterm L ξ n).freeVariables = ∅ := by
  induction t
  case bvar => simp
  case fvar x => exact IsEmpty.elim inferInstance x
  case func k f v ih =>
    ext x; simp [Rew.func, freeVariables_func, ih]

lemma rew_eq_of_funEqOn [DecidableEq ξ₁] (ω₁ ω₂ : Rew L ξ₁ n₁ ξ₂ n₂) (t : Semiterm L ξ₁ n₁)
  (hb : ∀ x, ω₁ #x = ω₂ #x)
  (he : Function.funEqOn t.FVar? (ω₁ ∘ Semiterm.fvar) (ω₂ ∘ Semiterm.fvar)) :
    ω₁ t = ω₂ t := by
  induction t
  case bvar => simp [hb]
  case fvar => simpa [FVar?, Function.funEqOn] using he
  case func k f v ih =>
    simp only [Rew.func, func.injEq, heq_eq_eq, true_and]
    funext i
    exact ih i (he.of_subset <| by intro x hx; simpa using ⟨i, hx⟩)


-- @@ L732-732 verbatim
section lMap


-- @@ L734-734 verbatim
variable (Φ : L₁ →ᵥ L₂)

-- @@ L735-757 verbatim
open Rew

lemma lMap_bind (b : Fin n₁ → Semiterm L₁ ξ₂ n₂) (e : ξ₁ → Semiterm L₁ ξ₂ n₂) (t) :
    lMap Φ (bind b e t) = bind (lMap Φ ∘ b) (lMap Φ ∘ e) (t.lMap Φ) := by
  induction t <;> simp [*, -lMap_func, lMap_func', -Rew.func, Rew.func']

lemma lMap_map (b : Fin n₁ → Fin n₂) (e : ξ₁ → ξ₂) (t) :
    (map b e t).lMap Φ = map b e (t.lMap Φ) := by
  simp [map, lMap_bind, Function.comp_def]

lemma lMap_bShift (t : Semiterm L₁ ξ₁ n) : (bShift t).lMap Φ = bShift (t.lMap Φ) := by
  simp [bShift, lMap_map]

lemma lMap_shift (t : SyntacticSemiterm L₁ n) : (shift t).lMap Φ = shift (t.lMap Φ) := by
  simp [shift, lMap_map]

lemma lMap_free (t : SyntacticSemiterm L₁ (n + 1)) : (free t).lMap Φ = free (t.lMap Φ) := by
  simp only [free, Nat.succ_eq_add_one, lMap_bind]
  congr; exact funext $ Fin.lastCases (by simp) (by simp)

lemma lMap_fix (t : SyntacticSemiterm L₁ n) : (fix t).lMap Φ = fix (t.lMap Φ) := by
  simp only [fix, lMap_bind]
  congr; funext x; cases x <;> simp


-- @@ L759-775 verbatim
end lMap

lemma fvar?_rew [DecidableEq ξ₁] [DecidableEq ξ₂]
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


-- @@ L777-779 verbatim
@[simp] lemma fvar?_bShift [DecidableEq ξ] {t : Semiterm L ξ n} {x} :
    (Rew.bShift t).FVar? x ↔ t.FVar? x := by
  induction t <;> simp [Rew.func, *]


-- @@ L781-789 verbatim
def toEmpty [DecidableEq ξ] {n : ℕ} : (t : Semiterm L ξ n) → t.freeVariables = ∅ → ClosedSemiterm L n
  |       #x, _ => #x
  |       &x, h => by simp at h
  | func f v, h =>
    have : ∀ i, (v i).freeVariables = ∅ := by
      intro i; ext x
      have := by simpa using Eq.to_iff (congrFun (congrArg Membership.mem h) x)
      simpa using this i
    func f fun i ↦ toEmpty (v i) (this i)


-- @@ L791-793 verbatim
@[simp] lemma emb_toEmpty [DecidableEq ξ] (t : Semiterm L ξ n) (ht : t.freeVariables = ∅) : Rew.emb (t.toEmpty ht) = t := by
  induction t <;> try simp [toEmpty, Rew.func, *, Function.comp_def]
  case fvar => simp at ht


-- @@ L795-798 verbatim
@[simp] lemma toEmpty_emb [DecidableEq ξ] (t : ClosedSemiterm L n) :
    (Rew.emb t : Semiterm L ξ n).toEmpty (by simp) = t := by
  induction t <;> try simp [toEmpty, Rew.func, *]
  case fvar => contradiction


-- @@ L800-800 verbatim
end Semiterm


-- @@ L802-802 verbatim
/-! ### Rewriting system of formulae -/


-- @@ L804-817 verbatim
/--
A typeclass for `Rew`s which additionally respect quantifiers.

`app` - A notion of application of `Rew`s to formulas.

`app_all` - Application preserves universal quantification.

`app_exs` - Application preserves existential quantification.
-/
class Rewriting (L : outParam Language) (ξ : outParam Type*) (F : ℕ → Type*) (ζ : Type*) (G : outParam (ℕ → Type*))
    [LCWQ F] [LCWQ G] where
  app {n₁ n₂} : Rew L ξ n₁ ζ n₂ → F n₁ →ˡᶜ G n₂
  app_all (ω₁₂ : Rew L ξ n₁ ζ n₂) (φ) : app ω₁₂ (∀¹ φ) = ∀¹ (app ω₁₂.q φ)
  app_exs (ω₁₂ : Rew L ξ n₁ ζ n₂) (φ) : app ω₁₂ (∃¹ φ) = ∃¹ (app ω₁₂.q φ)


-- @@ L819-820 verbatim
abbrev SyntacticRewriting (L : outParam Language) (F : ℕ → Type*) (G : outParam (ℕ → Type*)) [LCWQ F] [LCWQ G] :=
  Rewriting L ℕ F ℕ G


-- @@ L822-822 verbatim
namespace Rewriting


-- @@ L824-824 verbatim
variable [LCWQ F] [LCWQ G] [Rewriting L ξ F ζ G]


-- @@ L826-826 verbatim
attribute [simp] app_all app_exs


-- @@ L828-831 verbatim
/-- Application of a `Rewriting` to a formula. -/
infixr:73 " ▹ " => app

lemma smul_ext' {ω₁ ω₂ : Rew L ξ n₁ ζ n₂} (h : ω₁ = ω₂) {φ : F n₁} : ω₁ ▹ φ = ω₂ ▹ φ := by rw [h]


-- @@ L833-833 verbatim
@[simp] lemma smul_ball (ω : Rew L ξ n₁ ζ n₂) (φ ψ : F (n₁ + 1)) : ω ▹ (∀¹[φ] ψ) = ∀¹[ω.q ▹ φ] (ω.q ▹ ψ) := by simp [ball]


-- @@ L835-835 verbatim
@[simp] lemma smul_bexs (ω : Rew L ξ n₁ ζ n₂) (φ ψ : F (n₁ + 1)) : ω ▹ (∃¹[φ] ψ) = ∃¹[ω.q ▹ φ] (ω.q ▹ ψ) := by simp [bexs]


-- @@ L837-839 verbatim
@[simp] lemma smul_allItr (ω : Rew L ξ n₁ ζ n₂) (φ : F (n₁ + k)) :
    ω ▹ (∀¹^[k] φ) = ∀¹^[k] (ω.qpow k ▹ φ : G (n₂ + k)) := by
  induction k <;> simp [allItr_succ, *]


-- @@ L841-843 verbatim
@[simp] lemma smul_exsItr (ω : Rew L ξ n₁ ζ n₂) (φ : F (n₁ + k)) :
    ω ▹ (∃¹^[k] φ) = ∃¹^[k] (ω.qpow k ▹ φ : G (n₂ + k)) := by
  induction k <;> simp [exsItr_succ, *]


-- @@ L845-847 verbatim
@[simp] lemma smul_quant (ω : Rew L ξ n₁ ζ n₂) (Γ : Polarity) (φ : F (n₁ + 1)) :
    ω ▹ Γ.quant φ = Γ.quant (ω.q ▹ φ) := by
  rcases Γ <;> simp


-- @@ L849-851 verbatim
@[simp] lemma smul_quantItr (ω : Rew L ξ n₁ ζ n₂) (Γ : Polarity) (φ : F (n₁ + k)) :
    ω ▹ Polarity.quantItr Γ k φ = Polarity.quantItr Γ k (ω.qpow k ▹ φ : G (n₂ + k)) := by
  induction k <;> simp [Polarity.quantItr_succ', *]


-- @@ L853-853 verbatim
abbrev subst [Rewriting L ξ F ξ F] (φ : F n₁) (w : Fin n₁ → Semiterm L ξ n₂) : F n₂ := Rew.subst w ▹ φ


-- @@ L855-856 verbatim
/-- Applies the substitution `FFL.FirstOrder.Rew.subst w` to a formula. This substitutes the bound variables occurring in the formula by `w : Fin n₁ → Semiterm L ξ n₂`. -/
infix:90 " ⇜ " => FFL.FirstOrder.Rewriting.subst


-- @@ L858-859 verbatim
/-- Applies the substitution `FFL.FirstOrder.Rew.shift` to a formula. This substitutes each free variable `&x` with `&(x + 1)`. -/
abbrev shift [Rewriting L ℕ F ℕ F] : F n →ˡᶜ F n := app Rew.shift


-- @@ L861-861 verbatim
abbrev free [Rewriting L ℕ F ℕ F] : F (n + 1) →ˡᶜ F n := app Rew.free


-- @@ L863-863 verbatim
abbrev fix [Rewriting L ℕ F ℕ F] : F n →ˡᶜ F (n + 1) := app Rew.fix


-- @@ L865-865 verbatim
def shifts [Rewriting L ℕ F ℕ F] (Γ : Multiset (F n)) : Multiset (F n) := Γ.map Rewriting.shift


-- @@ L867-867 verbatim
scoped[FFL.FirstOrder] 
-- @@ L867-867 verbatim
postfix:max "⁺" => FirstOrder.Rewriting.shifts


-- @@ L869-869 verbatim
@[simp] lemma shifts_empty [Rewriting L ℕ F ℕ F] : (0 : Multiset (F n))⁺ = 0 := by rfl


-- @@ L871-871 verbatim
@[simp] lemma shifts_add [Rewriting L ℕ F ℕ F] (Γ Δ : Multiset (F n)) : (Γ + Δ)⁺ = Γ⁺ + Δ⁺ := by simp [shifts]


-- @@ L873-873 verbatim
@[simp] lemma shifts_singleton [Rewriting L ℕ F ℕ F] (φ : F n) : (⦃φ⦄ : Multiset (F n))⁺ = ⦃shift φ⦄ := by simp [shifts]


-- @@ L875-877 verbatim
@[simp] lemma shifts_neg [Rewriting L ℕ F ℕ F] (Γ : Multiset (F n)) :
    (∼Γ)⁺ = ∼(Γ⁺) := by
  simp [shifts, Multiset.tilde_def]


-- @@ L879-879 verbatim
abbrev emb {ο ξ} [IsEmpty ο] {O F : ℕ → Type*} [LCWQ O] [LCWQ F] [Rewriting L ο O ξ F] : O n →ˡᶜ F n := app (Rew.emb (ξ := ξ))


-- @@ L881-881 verbatim
end Rewriting


-- @@ L883-883 verbatim
section Notation


-- @@ L885-885 verbatim
open Lean PrettyPrinter Delaborator


-- @@ L887-887 verbatim
syntax (name := substNotation) term:max "/[" term,* "]" : term


-- @@ L889-893 verbatim
/-- Slash notation for rewriting bound variables of a formula.

The notation `φ/w` is equivalent to `φ ⇜ w`, which for a formula `φ` with bound variables from `Fin n₁`, substitutes the bound variables occurring in `φ` by `w : Fin n₁ → Semiterm L ξ n₂`. -/
macro_rules (kind := substNotation)
  | `($φ:term /[$terms:term,*]) => `($φ ⇜ ![$terms,*])


-- @@ L895-898 verbatim
@[app_unexpander Rewriting.subst]
meta def _root_.unexpanderSubstitute : Unexpander
  | `($_ $φ:term ![$ts:term,*]) => `($φ /[ $ts,* ])
  | _                           => throw ()


-- @@ L900-900 verbatim
end Notation


-- @@ L902-904 verbatim
class ReflectiveRewriting (L : outParam Language) (ξ : outParam Type*) (F : ℕ → Type*)
    [LCWQ F] [Rewriting L ξ F ξ F] where
  id_app (φ : F n) : @Rew.id L ξ n ▹ φ = φ


-- @@ L906-910 verbatim
class TransitiveRewriting (L : outParam Language)
    (ξ₁ : outParam Type*) (F₁ : ℕ → Type*) (ξ₂ : Type*) (F₂ : outParam (ℕ → Type*)) (ξ₃ : Type*) (F₃ : outParam (ℕ → Type*))
    [LCWQ F₁] [LCWQ F₂] [LCWQ F₃]
    [Rewriting L ξ₁ F₁ ξ₂ F₂] [Rewriting L ξ₂ F₂ ξ₃ F₃] [Rewriting L ξ₁ F₁ ξ₃ F₃] where
  comp_app (ω₁₂ : Rew L ξ₁ n₁ ξ₂ n₂) (ω₂₃ : Rew L ξ₂ n₂ ξ₃ n₃) (φ : F₁ n₁) : (ω₂₃.comp ω₁₂) ▹ φ = ω₂₃ ▹ ω₁₂ ▹ φ


-- @@ L912-915 verbatim
class InjMapRewriting (L : outParam Language) (ξ : outParam Type*) (F : ℕ → Type*) (ζ : Type*) (G : outParam (ℕ → Type*))
    [LCWQ F] [LCWQ G] [Rewriting L ξ F ζ G] where
  smul_map_injective {b : Fin n₁ → Fin n₂} {f : ξ → ζ} :
    (hb : Function.Injective b) → (hf : Function.Injective f) → Function.Injective fun φ : F n₁ ↦ Rew.map (L := L) b f ▹ φ


-- @@ L917-918 verbatim
class LawfulSyntacticRewriting (L : outParam Language) (S : ℕ → Type*) [LCWQ S] [SyntacticRewriting L S S] extends
  ReflectiveRewriting L ℕ S, TransitiveRewriting L ℕ S ℕ S ℕ S, InjMapRewriting L ℕ S ℕ S


-- @@ L920-920 verbatim
attribute [simp] ReflectiveRewriting.id_app


-- @@ L922-922 verbatim
namespace Rewriting


-- @@ L924-940 verbatim
variable [LCWQ F] [Rewriting L ξ F ξ F] [ReflectiveRewriting L ξ F]

lemma quantItr_succ_smul_castLE {φ : F ((n + 1) + s)} :
    Polarity.quantItr Γ (s + 1)
      ((Rew.castLE (Nat.succ_add n s).le : Rew L ξ ((n + 1) + s) ξ (n + (s + 1))) ▹ φ)
      = Γ.quant (Polarity.quantItr Γ.alt s φ) := by
  induction s with
  | zero => simp [Polarity.quantItr_succ']
  | succ s ih =>
    have hcast :
        (Rew.castLE (Nat.succ_add n (s + 1)).le : Rew L ξ ((n + 1) + (s + 1)) ξ (n + ((s + 1) + 1)))
          = (Rew.castLE (Nat.succ_add n s).le : Rew L ξ ((n + 1) + s) ξ (n + (s + 1))).q := by
      simp
    rw [Polarity.quantItr_succ', hcast, ← smul_quant]
    rw [ih]
    congr 1
    rw [Polarity.quantItr_succ', Polarity.altItr_succ']


-- @@ L942-942 verbatim
end Rewriting


-- @@ L944-944 verbatim
namespace LawfulSyntacticRewriting


-- @@ L946-946 verbatim
variable {S : ℕ → Type*} [LCWQ S] [SyntacticRewriting L S S]


-- @@ L948-954 verbatim
open Rewriting ReflectiveRewriting TransitiveRewriting InjMapRewriting Semiterm

lemma fix_allClosure (φ : S n) :
    ∀¹ fix (∀¹* φ) = ∀¹* fix φ := by
  induction n
  case zero => simp [allClosure_succ]
  case succ n ih => simp [allClosure_succ, ih]


-- @@ L956-959 verbatim
variable [LawfulSyntacticRewriting L S]

lemma shift_injective : Function.Injective fun φ : S n ↦ shift φ :=
  smul_map_injective Function.injective_id Nat.succ_injective


-- @@ L961-962 verbatim
@[simp] lemma fix_free (φ : S (n + 1)) :
    fix (free φ) = φ := by simp [←comp_app]


-- @@ L964-965 verbatim
@[simp] lemma free_fix (φ : S n) :
    free (fix φ) = φ := by simp [←comp_app]


-- @@ L967-967 verbatim
@[simp] lemma subst_empty (φ : S 0) (v : Fin 0 → Semiterm L ℕ  0) : (φ ⇜ v) = φ := by simp [subst]


-- @@ L969-984 verbatim
/-- `hom_subst_mbar_zero_comp_shift_eq_free` -/
@[simp] lemma app_subst_fbar_zero_comp_shift_eq_free (φ : S 1) :
    (shift φ)/[&0] = free φ := by simp [← comp_app, Rew.subst_mbar_zero_comp_shift_eq_free]

lemma free_rewrite_eq (f : ℕ → SyntacticTerm L) (φ : S 1) :
    free ((Rew.rewrite fun x ↦ Rew.bShift (f x)) ▹ φ) =
    Rew.rewrite (&0 :>ₙ fun x ↦ Rew.shift (f x)) ▹ free φ := by
  simpa [← comp_app] using smul_ext' <| by ext x <;> simp [Rew.comp_app]

lemma shift_rewrite_eq (f : ℕ → SyntacticTerm L) (φ : S 0) :
    shift (Rew.rewrite f ▹ φ) = (Rew.rewrite (&0 :>ₙ fun x ↦ Rew.shift (f x))) ▹ shift φ := by
  simpa [←comp_app] using smul_ext' <| by ext x <;> simp [Rew.comp_app]

lemma rewrite_subst_eq (f : ℕ → SyntacticTerm L) (t) (φ : S 1) :
    Rew.rewrite f ▹ φ/[t] = (Rew.rewrite (Rew.bShift ∘ f) ▹ φ)/[Rew.rewrite f t] := by
  simpa [←comp_app] using smul_ext' <| by ext x <;> simp [Rew.comp_app]


-- @@ L986-996 verbatim
@[simp] lemma free_subst_nil (φ : S 0) : free (Rewriting.subst (ξ := ℕ) φ ![]) = shift φ := by
  simpa [←comp_app] using smul_ext' <| by
    ext x <;> simp only [Rew.comp_app, Rew.subst_fvar, Rew.free_fvar, Rew.shift_fvar]; { exact Fin.elim0 x }

lemma rewrite_subst_nil (f : ℕ → SyntacticTerm L) (φ : S 0) :
    Rew.rewrite (Rew.bShift ∘ f) ▹ (Rewriting.subst (ξ := ℕ) φ ![]) =
    Rewriting.subst (ξ := ℕ) (Rew.rewrite f ▹ φ) ![] := by
  simpa [←comp_app] using smul_ext' <| by
    ext x
    · exact x.elim0
    · simp [Rew.comp_app, Rew.bShift_eq_rewrite]


-- @@ L998-1007 verbatim
@[simp] lemma cast_subst_eq (t : SyntacticTerm L) (φ : S 0) :
    (Rewriting.subst (ξ := ℕ) φ ![])/[t] = φ := by
  suffices (Rewriting.subst (ξ := ℕ) φ ![])/[t] = Rew.id ▹ φ by rwa [ReflectiveRewriting.id_app] at this
  simpa [←comp_app, -id_app] using smul_ext' <| by
    ext x <;> simp only [Rew.comp_app, Rew.subst_bvar, Rew.subst_fvar, Rew.id_app]
    exact x.elim0

lemma rewrite_free_eq_subst (t : SyntacticTerm L) (φ : S 1) :
    Rew.rewrite (t :>ₙ fun x ↦ &x) ▹ free φ = φ/[t] := by
  simpa [←comp_app] using smul_ext' <| by ext x <;> simp [Rew.comp_app]


-- @@ L1009-1017 verbatim
def shiftEmb : S n ↪ S n where
  toFun := shift
  inj' := shift_injective

lemma shiftEmb_def (φ : S n) :
  shiftEmb φ = shift φ := rfl

lemma allClosure_fixitr (φ : S 0) : ∀¹* Rew.fixitr 0 (m + 1) ▹ φ = ∀¹ Rew.fix ▹ (∀¹* Rew.fixitr 0 m ▹ φ) := by
  simp [Rew.fixitr_succ, fix_allClosure, comp_app];


-- @@ L1019-1021 verbatim
@[simp] lemma mem_shifts_iff {φ : S n} {Γ : Multiset (S n)} :
    Rewriting.shift φ ∈ Γ⁺ ↔ φ ∈ Γ :=
  Multiset.mem_map_of_injective shift_injective


-- @@ L1023-1024 verbatim
@[simp] lemma shifts_ss (Γ Δ : Multiset (S n)) :
    Γ⁺ ⊆ Δ⁺ ↔ Γ ⊆ Δ := Multiset.map_subset_iff _ shift_injective


-- @@ L1026-1026 verbatim
end LawfulSyntacticRewriting


-- @@ L1028-1028 verbatim
namespace Rewriting


-- @@ L1030-1030 verbatim
variable {ο ξ : Type*} [IsEmpty ο] {O F F₁ F₂ : ℕ → Type*} [LCWQ O] [LCWQ F] [LCWQ F₁] [LCWQ F₂]


-- @@ L1032-1035 verbatim
open ReflectiveRewriting TransitiveRewriting InjMapRewriting Semiterm

lemma emb_injective [Rewriting L ο O ξ F] [InjMapRewriting L ο O ξ F] : Function.Injective fun φ : O n ↦ (emb (ξ := ξ) φ : F n) :=
  smul_map_injective Function.injective_id (IsEmpty.elim inferInstance)


-- @@ L1037-1038 verbatim
@[simp] lemma emb_allClosure [Rewriting L ο O ξ F] {σ : O n} :
    (emb (ξ := ξ) (∀¹* σ)) = ∀¹* (emb (ξ := ξ) σ) := by induction n <;> simp [*, allClosure_succ]


-- @@ L1040-1048 verbatim
@[simp] lemma rew_emb_eq_emb
    [Rewriting L ξ₁ F₁ ξ₂ F₂] [Rewriting L ο O ξ₁ F₁] [Rewriting L ο O ξ₂ F₂]
    [TransitiveRewriting L ο O ξ₁ F₁ ξ₂ F₂]
    (φ : O 0) (ω : Rew L ξ₁ 0 ξ₂ 0) :
    ω ▹ (emb (ξ := ξ₁) φ) = emb (ξ := ξ₂) φ := by
  unfold emb
  rw [←comp_app]
  congr 2
  simp


-- @@ L1050-1062 verbatim
/-- `coe_subst_eq_subst_coe` -/
lemma emb_subst_eq_subst_emb
    [Rewriting L ο O ο O] [Rewriting L ο O ξ F] [Rewriting L ξ F ξ F]
    [TransitiveRewriting L ο O ο O ξ F]
    [TransitiveRewriting L ο O ξ F ξ F]
    (φ : O k) (v : Fin k → Semiterm L ο n) :
    (emb (ξ := ξ) (φ ⇜ v)) = Rewriting.subst (ξ := ξ) (emb (ξ := ξ) φ) (fun i ↦ Rew.emb (v i)) := by
  unfold emb subst
  rw [←comp_app, ←comp_app]
  congr 2
  ext x
  · simp [Rew.comp_app]
  · exact IsEmpty.elim inferInstance x


-- @@ L1064-1071 verbatim
/-- `coe_subst_eq_subst_coe₁` -/
lemma emb_subst_eq_subst_coe₁
    [Rewriting L ο O ο O] [Rewriting L ο O ξ F] [Rewriting L ξ F ξ F]
    [TransitiveRewriting L ο O ο O ξ F]
    [TransitiveRewriting L ο O ξ F ξ F]
    (φ : O 1) (t : Semiterm L ο n) :
    (emb (ξ := ξ) (φ/[t])) = (emb (ξ := ξ) φ)/[(Rew.emb t : Semiterm L ξ n)] := by
  simpa [Matrix.constant_eq_singleton] using emb_subst_eq_subst_emb φ ![t]


-- @@ L1073-1073 verbatim
variable {S : ℕ → Type*} [LCWQ S] [SyntacticRewriting L S S] [LawfulSyntacticRewriting L S]


-- @@ L1075-1084 verbatim
@[simp] lemma shifts_emb
    [Rewriting L ο O ℕ F] [Rewriting L ℕ F ℕ F]
    [TransitiveRewriting L ο O ℕ F ℕ F]
    (Γ : Multiset (O n)) :
    (Γ.map (Rewriting.emb (ξ := ℕ)))⁺ = Γ.map (Rewriting.emb (ξ := ℕ)) := by
  suffices ∀ a ∈ Γ, shift (emb (ξ := ℕ) a) = emb (ξ := ℕ) a by simp [shifts, ← comp_app]
  intro j hj
  unfold emb shift
  rw [←comp_app]; congr 2
  ext x <;> simp


-- @@ L1086-1090 verbatim
@[simp] lemma subst1_bvar0_eq [Rewriting L ξ F ξ F] [ReflectiveRewriting L ξ F] (φ : F 1) :
    φ/[(#0 : Semiterm L ξ 1)] = φ := by
  suffices φ/[(#0 : Semiterm L ξ 1)] = Rew.id ▹ φ by rwa [ReflectiveRewriting.id_app] at this
  apply smul_ext'
  ext x <;> simp


-- @@ L1092-1092 verbatim
end Rewriting


-- @@ L1094-1094 verbatim
end FirstOrder


-- @@ L1096-1096 verbatim
end FFL


-- @@ L1098-1098 verbatim
end
