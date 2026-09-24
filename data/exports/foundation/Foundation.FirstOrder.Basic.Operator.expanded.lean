module

public import Foundation.FirstOrder.Basic.Semantics.Semantics


-- @@ L5-5 verbatim
@[expose] public section


-- @@ L7-7 verbatim
namespace FFL


-- @@ L9-9 verbatim
namespace FirstOrder


-- @@ L11-11 verbatim
variable {L : Language}


-- @@ L13-13 verbatim
namespace Semiterm


-- @@ L15-16 verbatim
structure Operator (L : Language) (n : ℕ) where
  term : ClosedSemiterm L n


-- @@ L18-18 verbatim
abbrev Const (L : Language.{u}) := Operator L 0


-- @@ L20-20 verbatim
def fn {k} (f : L.Func k) : Operator L k := ⟨Semiterm.func f (#·)⟩


-- @@ L22-22 verbatim
namespace Operator


-- @@ L24-28 verbatim
def equiv : Operator L n ≃ ClosedSemiterm L n where
  toFun := Operator.term
  invFun := Operator.mk
  left_inv := by intro _; simp
  right_inv := by intro _; simp


-- @@ L30-31 verbatim
def operator {arity : ℕ} (o : Operator L arity) (v : Fin arity → Semiterm L ξ n) : Semiterm L ξ n :=
  Rew.subst v (Rew.emb o.term)


-- @@ L33-33 verbatim
@[coe] abbrev const (c : Const L) : Semiterm L ξ n := c.operator ![]


-- @@ L35-35 verbatim
instance : Coe (Const L) (Semiterm L ξ n) := ⟨Operator.const⟩


-- @@ L37-38 verbatim
def comp (o : Operator L k) (w : Fin k → Operator L l) : Operator L l :=
  ⟨o.operator (fun x => (w x).term)⟩


-- @@ L40-45 verbatim
@[simp] lemma operator_comp (o : Operator L k) (w : Fin k → Operator L l) (v : Fin l → Semiterm L ξ n) :
  (o.comp w).operator v = o.operator (fun x ↦ (w x).operator v) := by
    simp only [operator, comp, Rew.emb_eq_id, Rew.id_app, ← Rew.comp_app]; congr 1
    ext
    · simp [Rew.comp_app]
    · contradiction


-- @@ L47-63 verbatim
def bvar (x : Fin n) : Operator L n := ⟨#x⟩

lemma operator_bvar (x : Fin k) (v : Fin k → Semiterm L ξ n) : (bvar x).operator v = v x := by
  simp [operator, bvar]

lemma bv_operator {k} (o : Operator L k) (v : Fin k → Semiterm L ξ (n + 1)) :
    (o.operator v).bv = .biUnion o.term.bv fun i ↦ (v i).bv  := by
  simp only [operator]
  generalize o.term = s
  induction s
  case bvar => simp
  case fvar => contradiction
  case func => simp [Rew.func, bv_func, Finset.biUnion_biUnion, *]

lemma positive_operator_iff {k} {o : Operator L k} {v : Fin k → Semiterm L ξ (n + 1)} :
    (o.operator v).Positive ↔ ∀ i ∈ o.term.bv, (v i).Positive := by
  simpa [Positive, bv_operator] using ⟨fun h i hi x hx ↦ h x i hi hx, fun h x i hi hx ↦ h i hi x hx⟩


-- @@ L65-67 verbatim
@[simp] lemma positive_const (c : Const L) : (c : Semiterm L ξ (n + 1)).Positive := by simp [const, positive_operator_iff]

-- f.operator ![ ... f.operator ![f.operator ![z, t 0], t 1], ... ,t (n-1)]

-- @@ L68-70 verbatim
def foldr (f : Operator L 2) (z : Operator L k) : List (Operator L k) → Operator L k
  | []      => z
  | o :: os => f.comp ![foldr f z os, o]


-- @@ L72-72 verbatim
@[simp] lemma foldr_nil (f : Operator L 2) (z : Operator L k) : f.foldr z [] = z := rfl


-- @@ L74-77 verbatim
@[simp] lemma operator_foldr_cons (f : Operator L 2) (z : Operator L k) (o : Operator L k) (os : List (Operator L k))
  (v : Fin k → Semiterm L ξ n) :
    (f.foldr z (o :: os)).operator v = f.operator ![(f.foldr z os).operator v, o.operator v] := by
  simp [foldr, operator_comp, Matrix.fun_eq_vec_two]


-- @@ L79-81 verbatim
def iterr (f : Operator L 2) (z : Const L) : (n : ℕ) → Operator L n
  | 0     => z
  | _ + 1 => f.foldr (bvar 0) (List.ofFn fun x => bvar x.succ)


-- @@ L83-83 verbatim
@[simp] lemma iterr_zero (f : Operator L 2) (z : Const L) : f.iterr z 0 = z := rfl


-- @@ L85-85 verbatim
section numeral


-- @@ L87-88 verbatim
protected class Zero (L : Language) where
  zero : Semiterm.Const L


-- @@ L90-91 verbatim
protected class One (L : Language) where
  one : Semiterm.Const L


-- @@ L93-94 verbatim
protected class Add (L : Language) where
  add : Semiterm.Operator L 2


-- @@ L96-97 verbatim
protected class Mul (L : Language) where
  mul : Semiterm.Operator L 2


-- @@ L99-100 verbatim
protected class Exp (L : Language) where
  exp : Semiterm.Operator L 1


-- @@ L102-103 verbatim
protected class Sub (L : Language) where
  sub : Semiterm.Operator L 2


-- @@ L105-106 verbatim
protected class Div (L : Language) where
  div : Semiterm.Operator L 2


-- @@ L108-109 verbatim
protected class Star (L : Language) where
  star : Semiterm.Const L


-- @@ L111-112 verbatim
class GödelNumber (L : Language) (α : Type*) where
  gödelNumber : α → Semiterm.Const L


-- @@ L114-114 verbatim
notation "op(0)" => Zero.zero


-- @@ L116-116 verbatim
notation "op(0)[" L "]" => Zero.zero (L := L)


-- @@ L118-118 verbatim
notation "op(1)" => One.one


-- @@ L120-120 verbatim
notation "op(1)[" L "]" => One.one (L := L)


-- @@ L122-122 verbatim
notation "op(+)" => Add.add


-- @@ L124-124 verbatim
notation "op(+)[" L "]" => Add.add (L := L)


-- @@ L126-126 verbatim
notation "op(*)" => Mul.mul


-- @@ L128-128 verbatim
notation "op(*)[" L "]" => Mul.mul (L := L)


-- @@ L130-130 verbatim
instance [L.Zero] : Operator.Zero L := ⟨⟨Semiterm.func Language.Zero.zero ![]⟩⟩


-- @@ L132-132 verbatim
instance [L.One] : Operator.One L := ⟨⟨Semiterm.func Language.One.one ![]⟩⟩


-- @@ L134-134 verbatim
instance [L.Add] : Operator.Add L := ⟨⟨Semiterm.func Language.Add.add Semiterm.bvar⟩⟩


-- @@ L136-136 verbatim
instance [L.Mul] : Operator.Mul L := ⟨⟨Semiterm.func Language.Mul.mul Semiterm.bvar⟩⟩


-- @@ L138-138 verbatim
instance [L.Exp] : Operator.Exp L := ⟨⟨Semiterm.func Language.Exp.exp Semiterm.bvar⟩⟩


-- @@ L140-152 verbatim
instance [L.Star] : Operator.Star L := ⟨⟨Semiterm.func Language.Star.star ![]⟩⟩

lemma Zero.term_eq [L.Zero] : (@Zero.zero L _).term = Semiterm.func Language.Zero.zero ![] := rfl

lemma One.term_eq [L.One] : (@One.one L _).term = Semiterm.func Language.One.one ![] := rfl

lemma Add.term_eq [L.Add] : (@Add.add L _).term = Semiterm.func Language.Add.add Semiterm.bvar := rfl

lemma Mul.term_eq [L.Mul] : (@Mul.mul L _).term = Semiterm.func Language.Mul.mul Semiterm.bvar := rfl

lemma Exp.term_eq [L.Exp] : (@Exp.exp L _).term = Semiterm.func Language.Exp.exp Semiterm.bvar := rfl

lemma Star.term_eq [L.Star] : (@Star.star L _).term = Semiterm.func Language.Star.star ![] := rfl


-- @@ L154-154 verbatim
open Language Semiterm


-- @@ L156-158 verbatim
def numeral (L : Language) [Operator.Zero L] [Operator.One L] [Operator.Add L] : ℕ → Const L
  | 0     => Zero.zero
  | n + 1 => Add.add.foldr One.one (List.replicate n One.one)


-- @@ L160-173 verbatim
variable [hz : Operator.Zero L] [ho : Operator.One L] [ha : Operator.Add L]

lemma numeral_zero : numeral L 0 = Zero.zero := by rfl

lemma numeral_one : numeral L 1 = One.one := by rfl

lemma numeral_succ (hz : z ≠ 0) : numeral L (z + 1) = Operator.Add.add.comp ![numeral L z, One.one] := by
  simp [numeral]
  cases' z with z
  · simp at hz
  · rfl

lemma numeral_add_two : numeral L (z + 2) = Operator.Add.add.comp ![numeral L (z + 1), One.one] :=
  numeral_succ (by simp)


-- @@ L175-177 verbatim
protected abbrev encode (L : Language) [Operator.Zero L] [Operator.One L] [Operator.Add L]
    {α : Type*} [Encodable α] (a : α) : Semiterm.Const L :=
  Semiterm.Operator.numeral L (Encodable.encode a)


-- @@ L179-179 verbatim
end numeral


-- @@ L181-183 verbatim
@[simp] lemma Add.positive_iff [L.Add] (t u : Semiterm L ξ (n + 1)) :
    (add.operator ![t, u]).Positive ↔ t.Positive ∧ u.Positive := by
  simp [positive_operator_iff, Add.term_eq, bv_func]


-- @@ L185-187 verbatim
@[simp] lemma Mul.positive_iff [L.Mul] (t u : Semiterm L ξ (n + 1)) :
    (mul.operator ![t, u]).Positive ↔ t.Positive ∧ u.Positive := by
  simp [positive_operator_iff, Mul.term_eq, bv_func]


-- @@ L189-191 verbatim
@[simp] lemma Exp.positive_iff [L.Exp] (t : Semiterm L ξ (n + 1)) :
    (exp.operator ![t]).Positive ↔ t.Positive := by
  simp [positive_operator_iff, Exp.term_eq, bv_func]


-- @@ L193-193 verbatim
section npow


-- @@ L195-196 verbatim
def npow (L : Language) [Operator.One L] [Operator.Mul L] (n : ℕ) : Operator L 1 :=
  Operator.Mul.mul.foldr (One.one.comp ![]) (List.replicate n (bvar 0))


-- @@ L198-203 verbatim
variable [Operator.One L] [Operator.Mul L]


lemma npow_zero : npow L 0 = One.one.comp ![] := rfl

lemma npow_succ : npow L (n + 1) = Operator.Mul.mul.comp ![npow L n, bvar 0] := rfl


-- @@ L205-205 verbatim
end npow


-- @@ L207-215 verbatim
@[simp] lemma npow_positive_iff [Operator.One L] [L.Mul] (t : Semiterm L ξ (n + 1)) (k : ℕ) :
    ((Operator.npow L k).operator ![t]).Positive ↔ k = 0 ∨ t.Positive := by
  cases k
  case zero =>
    simp [positive_operator_iff, operator_comp, npow_zero]
  case succ k n =>
    simp [positive_operator_iff, operator_comp, npow_succ, Mul.term_eq,
      bv_func, Fin.forall_fin_iff_zero_and_forall_succ, bvar]
    tauto


-- @@ L217-217 verbatim
namespace GödelNumber


-- @@ L219-219 verbatim
variable {α} [GödelNumber L α]


-- @@ L221-221 verbatim
abbrev gödelNumber' (a : α) : Semiterm L ξ n := const (gödelNumber a)


-- @@ L223-223 verbatim
instance : GödelQuote α (Semiterm L ξ n) := ⟨gödelNumber'⟩


-- @@ L225-225 verbatim
abbrev ofEncodable [Operator.Zero L] [Operator.One L] [Operator.Add L] {α : Type*} [Encodable α] : GödelNumber L α := ⟨Operator.encode L⟩


-- @@ L227-227 verbatim
end GödelNumber


-- @@ L229-229 verbatim
end Operator


-- @@ L231-231 verbatim
section complexity


-- @@ L233-233 verbatim
variable {L : Language}


-- @@ L235-236 verbatim
@[simp] lemma complexity_zero [L.Zero] : ((Operator.Zero.zero : Const L) : Semiterm L ξ n).complexity = 1 := by
  simp [Operator.const, Operator.operator, Operator.Zero.term_eq, complexity_func]


-- @@ L238-239 verbatim
@[simp] lemma complexity_one [L.One] : ((Operator.One.one : Const L) : Semiterm L ξ n).complexity = 1 := by
  simp [Operator.const, Operator.operator, Operator.One.term_eq, complexity_func]


-- @@ L241-244 verbatim
@[simp] lemma complexity_add [L.Add] (t u : Semiterm L ξ n) :
    (Operator.Add.add.operator ![t, u]).complexity = max t.complexity u.complexity + 1 := by
  simp [Operator.operator, Operator.Add.term_eq, complexity_func, Rew.func]
  simp [show (Finset.univ : Finset (Fin 2)) = {0, 1} from by ext i; cases i using Fin.cases <;> simp]


-- @@ L246-249 verbatim
@[simp] lemma complexity_mul [L.Mul] (t u : Semiterm L ξ n) :
    (Operator.Mul.mul.operator ![t, u]).complexity = max t.complexity u.complexity + 1 := by
  simp [Operator.operator, Operator.Mul.term_eq, complexity_func, Rew.func]
  simp [show (Finset.univ : Finset (Fin 2)) = {0, 1} from by ext i; cases i using Fin.cases <;> simp]


-- @@ L251-251 verbatim
end complexity


-- @@ L253-253 verbatim
section semantics


-- @@ L255-256 verbatim
def Operator.val {M : Type w} [s : Structure L M] (v : Fin k → M) (o : Operator L k) : M :=
  Semiterm.val v Empty.elim o.term


-- @@ L258-258 verbatim
variable {M : Type w} {s : Structure L M}


-- @@ L260-269 verbatim
@[simp] lemma val_operator {k} (b : Fin n → M) (f : ξ → M) (o : Operator L k) (v : Fin k → Semiterm L ξ n) :
    val b f (o.operator v) = o.val (Semiterm.val b f ∘ v) := by
  simp [Operator.operator, val_substs, Empty.eq_elim]; congr

lemma val_operator' {k} (b : Fin k → M) (f : ξ → M) (o : Operator L k) (v) :
    val b f (o.operator v) = o.val fun i ↦ (v i).val b f := val_operator b f o v

lemma Operator.val_comp (o₁ : Operator L k) (o₂ : Fin k → Operator L m) (v : Fin m → M) :
  (o₁.comp o₂).val v = o₁.val (val v ∘ o₂) := by
  simp [comp, val, Function.comp_def]


-- @@ L271-272 verbatim
@[simp] lemma Operator.val_bvar {n} (x : Fin n) (v : Fin n → M) :
    (Operator.bvar (L := L) x).val v = v x := by simp [Operator.bvar, Operator.val]


-- @@ L274-274 verbatim
end semantics


-- @@ L276-276 verbatim
end Semiterm


-- @@ L278-278 verbatim
namespace Semiformula


-- @@ L280-281 verbatim
structure Operator (L : Language.{u}) (n : ℕ) where
  sentence : Semisentence L n


-- @@ L283-283 verbatim
abbrev Const (L : Language.{u}) := Operator L 0


-- @@ L285-285 verbatim
namespace Operator


-- @@ L287-288 verbatim
def operator {arity : ℕ} (o : Operator L arity) (v : Fin arity → Semiterm L ξ n) : Semiformula L ξ n :=
  Rewriting.emb o.sentence ⇜ v


-- @@ L290-290 verbatim
@[coe] def const (c : Const L) : Semiformula L ξ n := c.operator ![]


-- @@ L292-292 verbatim
instance : Coe (Const L) (Semiformula L ξ n) := ⟨Operator.const⟩


-- @@ L294-304 verbatim
def comp (o : Operator L k) (w : Fin k → Semiterm.Operator L l) : Operator L l :=
  ⟨o.operator (fun x => (w x).term)⟩

lemma operator_comp (o : Operator L k) (w : Fin k → Semiterm.Operator L l) (v : Fin l → Semiterm L ξ n) :
  (o.comp w).operator v = o.operator (fun x => (w x).operator v) := by
    unfold operator Rewriting.emb Rewriting.subst comp
    simp only [operator, ← TransitiveRewriting.comp_app, Rew.emb_eq_id, Rew.comp_id];
    congr 2
    ext
    · simp [Rew.comp_app]; congr
    · contradiction


-- @@ L306-306 verbatim
def and {k} (o₁ o₂ : Operator L k) : Operator L k := ⟨o₁.sentence ⋏ o₂.sentence⟩


-- @@ L308-308 verbatim
def or {k} (o₁ o₂ : Operator L k) : Operator L k := ⟨o₁.sentence ⋎ o₂.sentence⟩


-- @@ L310-311 verbatim
@[simp] lemma operator_and (o₁ o₂ : Operator L k) (v : Fin k → Semiterm L ξ n) :
  (o₁.and o₂).operator v = o₁.operator v ⋏ o₂.operator v := by simp [operator, and]


-- @@ L313-314 verbatim
@[simp] lemma operator_or (o₁ o₂ : Operator L k) (v : Fin k → Semiterm L ξ n) :
  (o₁.or o₂).operator v = o₁.operator v ⋎ o₂.operator v := by simp [operator, or]


-- @@ L316-317 verbatim
protected class Eq (L : Language) where
  eq : Semiformula.Operator L 2


-- @@ L319-320 verbatim
protected class LT (L : Language) where
  lt : Semiformula.Operator L 2


-- @@ L322-323 verbatim
protected class LE (L : Language) where
  le : Semiformula.Operator L 2


-- @@ L325-326 verbatim
protected class Mem (L : Language) where
  mem : Semiformula.Operator L 2


-- @@ L328-328 verbatim
notation "op(=)" => Operator.Eq.eq


-- @@ L330-330 verbatim
notation "op(=)[" L "]" => Operator.Eq.eq (L := L)


-- @@ L332-332 verbatim
notation "op(<)" => Operator.LT.lt


-- @@ L334-334 verbatim
notation "op(<)[" L "]" => Operator.LT.lt (L := L)


-- @@ L336-336 verbatim
notation "op(≤)" => Operator.LE.le


-- @@ L338-338 verbatim
notation "op(≤)[" L "]" => Operator.LE.le (L := L)


-- @@ L340-340 verbatim
notation "op(∈)" => Operator.Mem.mem


-- @@ L342-342 verbatim
notation "op(∈)[" L "]" => Operator.Mem.mem (L := L)


-- @@ L344-344 verbatim
instance [Language.Eq L] : Operator.Eq L := ⟨⟨Semiformula.rel Language.Eq.eq Semiterm.bvar⟩⟩


-- @@ L346-346 verbatim
instance [Language.LT L] : Operator.LT L := ⟨⟨Semiformula.rel Language.LT.lt Semiterm.bvar⟩⟩


-- @@ L348-348 verbatim
instance [L.Mem] : Operator.Mem L := ⟨⟨Semiformula.rel Language.Mem.mem Semiterm.bvar⟩⟩


-- @@ L350-361 verbatim
instance [Operator.Eq L] [Operator.LT L] : Operator.LE L := ⟨Eq.eq.or LT.lt⟩

lemma Eq.sentence_eq [L.Eq] : (@Eq.eq L _).sentence = Semiformula.rel Language.Eq.eq Semiterm.bvar := rfl

lemma LT.sentence_eq [L.LT] : (@LT.lt L _).sentence = Semiformula.rel Language.LT.lt Semiterm.bvar := rfl

lemma Mem.sentence_eq [L.Mem] : (@Mem.mem L _).sentence = Semiformula.rel Language.Mem.mem Semiterm.bvar := rfl

lemma LE.sentence_eq [L.Eq] [L.LT] : (@LE.le L _).sentence = Eq.eq.sentence ⋎ LT.lt.sentence := rfl

lemma LE.def_of_Eq_of_LT [Operator.Eq L] [Operator.LT L] :
    (@Operator.LE.le L _) = Eq.eq.or LT.lt := rfl


-- @@ L363-365 verbatim
@[simp] lemma Eq.equal_inj [L.Eq] {t₁ t₂ u₁ u₂ : Semiterm L ξ₂ n₂} :
    Eq.eq.operator ![t₁, u₁] = Eq.eq.operator ![t₂, u₂] ↔ t₁ = t₂ ∧ u₁ = u₂ := by
  simp [operator, Eq.sentence_eq, Matrix.fun_eq_vec_two]


-- @@ L367-369 verbatim
@[simp] lemma LT.lt_inj [L.LT] {t₁ t₂ u₁ u₂ : Semiterm L ξ₂ n₂} :
    LT.lt.operator ![t₁, u₁] = LT.lt.operator ![t₂, u₂] ↔ t₁ = t₂ ∧ u₁ = u₂ := by
  simp [operator, LT.sentence_eq, Matrix.fun_eq_vec_two]


-- @@ L371-373 verbatim
@[simp] lemma Mem.mem_inj [L.Mem] {t₁ t₂ u₁ u₂ : Semiterm L ξ₂ n₂} :
    Mem.mem.operator ![t₁, u₁] = Mem.mem.operator ![t₂, u₂] ↔ t₁ = t₂ ∧ u₁ = u₂ := by
  simp [operator, Mem.sentence_eq, Matrix.fun_eq_vec_two]


-- @@ L375-394 verbatim
@[simp] lemma LE.le_inj [L.Eq] [L.LT] {t₁ t₂ u₁ u₂ : Semiterm L ξ₂ n₂} :
    LE.le.operator ![t₁, u₁] = LE.le.operator ![t₂, u₂] ↔ t₁ = t₂ ∧ u₁ = u₂ := by
  simp [operator, LE.sentence_eq, Eq.sentence_eq, LT.sentence_eq, Matrix.fun_eq_vec_two];


lemma lt_def [L.LT] (t u : Semiterm L ξ n) :
    LT.lt.operator ![t, u] = Semiformula.rel Language.LT.lt ![t, u] := by
  simp [operator, LT.sentence_eq, Matrix.fun_eq_vec_two]

lemma eq_def [L.Eq] (t u : Semiterm L ξ n) :
    Eq.eq.operator ![t, u] = Semiformula.rel Language.Eq.eq ![t, u] := by
  simp [operator, Eq.sentence_eq, Matrix.fun_eq_vec_two]

lemma mem_def [L.Mem] (t u : Semiterm L ξ n) :
    Mem.mem.operator ![t, u] = Semiformula.rel Language.Mem.mem ![t, u] := by
  simp [operator, Mem.sentence_eq, Matrix.fun_eq_vec_two]

lemma le_def [L.Eq] [L.LT] (t u : Semiterm L ξ n) :
    LE.le.operator ![t, u] = Semiformula.rel Language.Eq.eq ![t, u] ⋎ Semiformula.rel Language.LT.lt ![t, u] := by
  simp [operator, Eq.sentence_eq, LT.sentence_eq, LE.sentence_eq, Matrix.fun_eq_vec_two]


-- @@ L396-396 verbatim
variable {L : Language}


-- @@ L398-398 verbatim
@[simp] lemma Eq.open [L.Eq] (t u : Semiterm L ξ n) : (Eq.eq.operator ![t, u]).Open := by simp [Operator.operator, Operator.Eq.sentence_eq]


-- @@ L400-400 verbatim
@[simp] lemma LT.open [L.LT] (t u : Semiterm L ξ n) : (LT.lt.operator ![t, u]).Open := by simp [Operator.operator, Operator.LT.sentence_eq]


-- @@ L402-402 verbatim
@[simp] lemma Mem.open [L.Mem] (t u : Semiterm L ξ n) : (Mem.mem.operator ![t, u]).Open := by simp [Operator.operator, Operator.Mem.sentence_eq]


-- @@ L404-405 verbatim
@[simp] lemma LE.open [L.Eq] [L.LT] (t u : Semiterm L ξ n) : (LE.le.operator ![t, u]).Open := by
  simp [Operator.operator, Operator.LE.sentence_eq, Operator.Eq.sentence_eq, Operator.LT.sentence_eq]


-- @@ L407-407 verbatim
end Operator


-- @@ L409-410 verbatim
def Operator.val {M : Type w} [s : Structure L M] {k} (v : Fin k → M) (o : Operator L k) : Prop :=
  o.sentence.Eval v Empty.elim


-- @@ L412-412 verbatim
section


-- @@ L414-414 verbatim
variable {M : Type w} {s : Structure L M}


-- @@ L416-417 verbatim
@[simp] lemma val_operator_and {k} {o₁ o₂ : Operator L k} {v : Fin k → M} :
    (o₁.and o₂).val v ↔ o₁.val v ∧ o₂.val v := by simp [Operator.and, Operator.val]


-- @@ L419-420 verbatim
@[simp] lemma val_operator_or {k} {o₁ o₂ : Operator L k} {v : Fin k → M} :
    (o₁.or o₂).val v ↔ o₁.val v ∨ o₂.val v := by simp [Operator.or, Operator.val]


-- @@ L422-424 verbatim
@[simp] lemma eval_operator {k} {o : Operator L k} {e : Fin n → M} {f : ξ → M} {v : Fin k → Semiterm L ξ n} :
    Eval e f (o.operator v) ↔ o.val (Semiterm.val e f ∘ v) := by
  simp [Operator.operator, eval_substs, Operator.val]


-- @@ L426-426 verbatim
end


-- @@ L428-428 verbatim
def ballLT [Operator.LT L] (t : Semiterm L ξ n) (φ : Semiformula L ξ (n + 1)) : Semiformula L ξ n := ∀¹[Operator.LT.lt.operator ![#0, Rew.bShift t]] φ


-- @@ L430-430 verbatim
def bexsLT [Operator.LT L] (t : Semiterm L ξ n) (φ : Semiformula L ξ (n + 1)) : Semiformula L ξ n := ∃¹[Operator.LT.lt.operator ![#0, Rew.bShift t]] φ


-- @@ L432-432 verbatim
def ballLE [Operator.LE L] (t : Semiterm L ξ n) (φ : Semiformula L ξ (n + 1)) : Semiformula L ξ n := ∀¹[Operator.LE.le.operator ![#0, Rew.bShift t]] φ


-- @@ L434-434 verbatim
def bexsLE [Operator.LE L] (t : Semiterm L ξ n) (φ : Semiformula L ξ (n + 1)) : Semiformula L ξ n := ∃¹[Operator.LE.le.operator ![#0, Rew.bShift t]] φ


-- @@ L436-436 verbatim
def ballMem [Operator.Mem L] (t : Semiterm L ξ n) (φ : Semiformula L ξ (n + 1)) : Semiformula L ξ n := ∀¹[Operator.Mem.mem.operator ![#0, Rew.bShift t]] φ


-- @@ L438-438 verbatim
def bexsMem [Operator.Mem L] (t : Semiterm L ξ n) (φ : Semiformula L ξ (n + 1)) : Semiformula L ξ n := ∃¹[Operator.Mem.mem.operator ![#0, Rew.bShift t]] φ


-- @@ L440-440 verbatim
end Semiformula


-- @@ L442-442 verbatim
namespace Rew


-- @@ L444-445 verbatim
variable
  {L L' : Language.{u}} {L₁ : Language.{u₁}} {L₂ : Language.{u₂}} {L₃ : Language.{u₃}}


-- @@ L447-447 verbatim
variable (ω : Rew L ξ₁ n₁ ξ₂ n₂)


-- @@ L449-454 verbatim
protected lemma operator (o : Semiterm.Operator L k) (v : Fin k → Semiterm L ξ₁ n₁) :
    ω (o.operator v) = o.operator (fun i ↦ ω (v i)) := by
  simp only [Semiterm.Operator.operator, ← comp_app]; congr 1
  ext
  · simp [comp_app]
  · contradiction


-- @@ L456-457 verbatim
protected lemma operator' (o : Semiterm.Operator L k) (v : Fin k → Semiterm L ξ₁ n₁) :
    ω (o.operator v) = o.operator (ω ∘ v) := ω.operator o v


-- @@ L459-460 verbatim
@[simp] lemma finitary0 (o : Semiterm.Operator L 0) (v : Fin 0 → Semiterm L ξ₁ n₁) :
    ω (o.operator v) = o.operator ![] := by simp [ω.operator', Matrix.empty_eq]


-- @@ L462-463 verbatim
@[simp] lemma finitary1 (o : Semiterm.Operator L 1) (t : Semiterm L ξ₁ n₁) :
    ω (o.operator ![t]) = o.operator ![ω t] := by simp [ω.operator']


-- @@ L465-466 verbatim
@[simp] lemma finitary2 (o : Semiterm.Operator L 2) (t₁ t₂ : Semiterm L ξ₁ n₁) :
    ω (o.operator ![t₁, t₂]) = o.operator ![ω t₁, ω t₂] := by simp [ω.operator']


-- @@ L468-469 verbatim
@[simp] lemma finitary3 (o : Semiterm.Operator L 3) (t₁ t₂ t₃ : Semiterm L ξ₁ n₁) :
    ω (o.operator ![t₁, t₂, t₃]) = o.operator ![ω t₁, ω t₂, ω t₃] := by simp [ω.operator']


-- @@ L471-482 verbatim
@[simp] protected lemma const (c : Semiterm.Const L) : ω c = c := by simp [Semiterm.Operator.const]

lemma hom_operator (o : Semiformula.Operator L k) (v : Fin k → Semiterm L ξ₁ n₁) :
    ω ▹ o.operator v = o.operator fun i ↦ ω (v i) := by
  unfold Semiformula.Operator.operator Rewriting.subst Rewriting.emb
  simp only [← TransitiveRewriting.comp_app]; congr 2
  ext
  · simp [Rew.comp_app]
  · contradiction

lemma hom_operator' (o : Semiformula.Operator L k) (v : Fin k → Semiterm L ξ₁ n₁) :
    ω ▹ o.operator v = o.operator (ω ∘ v) := ω.hom_operator o v


-- @@ L484-485 verbatim
@[simp] lemma hom_finitary0 (o : Semiformula.Operator L 0) (v : Fin 0 → Semiterm L ξ₁ n₁) :
    ω ▹ (o.operator v) = o.operator ![] := by simp [ω.hom_operator', Matrix.empty_eq]


-- @@ L487-488 verbatim
@[simp] lemma hom_finitary1 (o : Semiformula.Operator L 1) (t : Semiterm L ξ₁ n₁) :
    ω ▹ (o.operator ![t]) = o.operator ![ω t] := by simp [ω.hom_operator']


-- @@ L490-491 verbatim
@[simp] lemma hom_finitary2 (o : Semiformula.Operator L 2) (t₁ t₂ : Semiterm L ξ₁ n₁) :
    ω ▹ (o.operator ![t₁, t₂]) = o.operator ![ω t₁, ω t₂] := by simp [ω.hom_operator']


-- @@ L493-494 verbatim
@[simp] lemma hom_finitary3 (o : Semiformula.Operator L 3) (t₁ t₂ t₃ : Semiterm L ξ₁ n₁) :
    ω ▹ (o.operator ![t₁, t₂, t₃]) = o.operator ![ω t₁, ω t₂, ω t₃] := by simp [ω.hom_operator']


-- @@ L496-497 verbatim
@[simp] lemma hom_const : ω ▹ (Semiformula.Operator.const c : Semiformula L ξ₁ n₁) = Semiformula.Operator.const c := by
  simp [Semiformula.Operator.const, ω.hom_operator']


-- @@ L499-562 verbatim
open Semiformula

lemma eq_equal_iff [L.Eq] {φ : Semiformula L ξ₁ n₁} {t u : Semiterm L ξ₂ n₂} :
    ω ▹ φ = Operator.Eq.eq.operator ![t, u]
    ↔ ∃ t' u', ω t' = t ∧ ω u' = u ∧ φ = Operator.Eq.eq.operator ![t', u'] := by
  match φ with
  | .rel (arity := k') r' v =>
    by_cases hk : k' = 2
    case neg => simp [Operator.operator, Operator.Eq.sentence_eq, hk]
    rcases hk
    by_cases hr : r' = Language.Eq.eq
    case neg => simp [Operator.operator, Operator.Eq.sentence_eq, hr]
    rcases hr
    simp [Operator.operator, Operator.Eq.sentence_eq,
      funext_iff, Fin.forall_fin_iff_zero_and_forall_succ]
  | .nrel _ _ => simp [Operator.operator, Operator.Eq.sentence_eq]
  |         ⊤ => simp [Operator.operator, Operator.Eq.sentence_eq]
  |         ⊥ => simp [Operator.operator, Operator.Eq.sentence_eq]
  |     _ ⋏ _ => simp [Operator.operator, Operator.Eq.sentence_eq]
  |     _ ⋎ _ => simp [Operator.operator, Operator.Eq.sentence_eq]
  |      ∀¹ _ => simp [Operator.operator, Operator.Eq.sentence_eq]
  |      ∃¹ _ => simp [Operator.operator, Operator.Eq.sentence_eq]

lemma eq_lt_iff [L.LT] {φ : Semiformula L ξ₁ n₁} {t u : Semiterm L ξ₂ n₂} :
    ω ▹ φ = Operator.LT.lt.operator ![t, u]
    ↔ ∃ t' u', ω t' = t ∧ ω u' = u ∧ φ = Operator.LT.lt.operator ![t', u'] := by
  match φ with
  | .rel (arity := k') r' v =>
    by_cases hk : k' = 2
    case neg => simp [Operator.operator, Operator.LT.sentence_eq, hk]
    rcases hk
    by_cases hr : r' = Language.LT.lt
    case neg => simp [Operator.operator, Operator.LT.sentence_eq, hr]
    rcases hr
    simp [Operator.operator, Operator.LT.sentence_eq,
      funext_iff, Fin.forall_fin_iff_zero_and_forall_succ]
  | .nrel _ _ => simp [Operator.operator, Operator.LT.sentence_eq]
  |         ⊤ => simp [Operator.operator, Operator.LT.sentence_eq]
  |         ⊥ => simp [Operator.operator, Operator.LT.sentence_eq]
  |     _ ⋏ _ => simp [Operator.operator, Operator.LT.sentence_eq]
  |     _ ⋎ _ => simp [Operator.operator, Operator.LT.sentence_eq]
  |      ∀¹ _ => simp [Operator.operator, Operator.LT.sentence_eq]
  |      ∃¹ _ => simp [Operator.operator, Operator.LT.sentence_eq]

lemma eq_mem_iff [L.Mem] {φ : Semiformula L ξ₁ n₁} {t u : Semiterm L ξ₂ n₂} :
    ω ▹ φ = Operator.Mem.mem.operator ![t, u]
    ↔ ∃ t' u', ω t' = t ∧ ω u' = u ∧ φ = Operator.Mem.mem.operator ![t', u'] := by
  match φ with
  | .rel (arity := k') r' v =>
    by_cases hk : k' = 2
    case neg => simp [Operator.operator, Operator.Mem.sentence_eq, hk]
    rcases hk
    by_cases hr : r' = Language.Mem.mem
    case neg => simp [Operator.operator, Operator.Mem.sentence_eq, hr]
    rcases hr
    simp [Operator.operator, Operator.Mem.sentence_eq,
      funext_iff, Fin.forall_fin_iff_zero_and_forall_succ]
  | .nrel _ _ => simp [Operator.operator, Operator.Mem.sentence_eq]
  |         ⊤ => simp [Operator.operator, Operator.Mem.sentence_eq]
  |         ⊥ => simp [Operator.operator, Operator.Mem.sentence_eq]
  |     _ ⋏ _ => simp [Operator.operator, Operator.Mem.sentence_eq]
  |     _ ⋎ _ => simp [Operator.operator, Operator.Mem.sentence_eq]
  |      ∀¹ _ => simp [Operator.operator, Operator.Mem.sentence_eq]
  |      ∃¹ _ => simp [Operator.operator, Operator.Mem.sentence_eq]


-- @@ L564-564 verbatim
end Rew


-- @@ L566-566 verbatim
namespace Structure


-- @@ L568-568 verbatim
open Semiterm Semiformula


-- @@ L570-570 verbatim
variable (L) (M : Type*) [Structure L M]


-- @@ L572-573 verbatim
protected class Zero [Operator.Zero L] [Zero M] : Prop where
  zero : (@Operator.Zero.zero L _).val ![] = (0 : M)


-- @@ L575-576 verbatim
protected class One [Operator.One L] [One M] : Prop where
  one : (@Operator.One.one L _).val ![] = (1 : M)


-- @@ L578-579 verbatim
protected class Add [Operator.Add L] [Add M] : Prop where
  add : ∀ a b : M, (@Operator.Add.add L _).val ![a, b] = a + b


-- @@ L581-582 verbatim
protected class Mul [Operator.Mul L] [Mul M] : Prop where
  mul : ∀ a b : M, (@Operator.Mul.mul L _).val ![a, b] = a * b


-- @@ L584-585 verbatim
protected class Exp [Operator.Exp L] [Exp M] : Prop where
  exp : ∀ a : M, (@Operator.Exp.exp L _).val ![a] = Exp.exp a


-- @@ L587-588 verbatim
protected class Eq [Operator.Eq L] : Prop where
  eq : ∀ a b : M, (@Operator.Eq.eq L _).val ![a, b] ↔ a = b


-- @@ L590-591 verbatim
protected class LT [Operator.LT L] [LT M] : Prop where
  lt : ∀ a b : M, (@Operator.LT.lt L _).val ![a, b] ↔ a < b


-- @@ L593-594 verbatim
protected class LE [Operator.LE L] [LE M] : Prop where
  le : ∀ a b : M, (@Operator.LE.le L _).val ![a, b] ↔ a ≤ b


-- @@ L596-597 verbatim
protected class Mem [Operator.Mem L] [Membership M M] : Prop where
  mem : ∀ a b : M, (@Operator.Mem.mem L _).val ![a, b] ↔ a ∈ b


-- @@ L599-599 verbatim
attribute [simp] Zero.zero One.one Add.add Mul.mul Exp.exp Eq.eq LT.lt LE.le Mem.mem


-- @@ L601-602 verbatim
instance [L.Eq] [L.LT] [Structure.Eq L M] [PartialOrder M] [Structure.LT L M] :
  Structure.LE L M := ⟨by intro a b; simpa [Operator.LE.def_of_Eq_of_LT] using le_iff_eq_or_lt.symm⟩


-- @@ L604-604 verbatim
variable {L M}


-- @@ L606-609 verbatim
@[simp] lemma zero_eq_of_lang [L.Zero] [Zero M] [Structure.Zero L M] (v : Fin 0 → M) :
    Structure.func (L := L) Language.Zero.zero v = (0 : M) := by
  simpa [Matrix.empty_eq, Semiterm.Operator.val, Semiterm.Operator.Zero.zero, ←Matrix.fun_eq_vec_two] using
    Structure.Zero.zero (L := L) (M := M)


-- @@ L611-614 verbatim
@[simp] lemma one_eq_of_lang [L.One] [One M] [Structure.One L M] (v : Fin 0 → M) :
    Structure.func (L := L) Language.One.one v = (1 : M) := by
  simpa [Matrix.empty_eq, Semiterm.Operator.val, Semiterm.Operator.One.one, ←Matrix.fun_eq_vec_two] using
    Structure.One.one (L := L) (M := M)


-- @@ L616-620 verbatim
@[simp] lemma add_eq_of_lang [L.Add] [Add M] [Structure.Add L M] {v : Fin 2 → M} :
    Structure.func (L := L) Language.Add.add v = v 0 + v 1 := by
  have h := Structure.Add.add (L := L) (v 0) (v 1)
  simp only [←Matrix.fun_eq_vec_two] at h
  exact h


-- @@ L622-626 verbatim
@[simp] lemma mul_eq_of_lang [L.Mul] [Mul M] [Structure.Mul L M] {v : Fin 2 → M} :
    Structure.func (L := L) Language.Mul.mul v = v 0 * v 1 := by
  have h := Structure.Mul.mul (L := L) (v 0) (v 1)
  simp only [←Matrix.fun_eq_vec_two] at h
  exact h


-- @@ L628-632 verbatim
@[simp] lemma exp_eq_of_lang [L.Exp] [Exp M] [Structure.Exp L M] {v : Fin 1 → M} :
    Structure.func (L := L) Language.Exp.exp v = FFL.Exp.exp (v 0) := by
  have h := Structure.Exp.exp (L := L) (v 0)
  simp only [←Matrix.fun_eq_vec_one] at h
  exact h


-- @@ L634-636 verbatim
@[simp] lemma eq_iff_eq [Operator.Eq L] [Structure.Eq L M] {v : Fin 2 →M} :
    (@Operator.Eq.eq L _).val v ↔ v 0 = v 1 := by
  rw [Matrix.fun_eq_vec_two v]; simp


-- @@ L638-640 verbatim
@[simp] lemma lt_iff_lt [Operator.LT L] [LT M] [Structure.LT L M] {v : Fin 2 →M} :
    (@Operator.LT.lt L _).val v ↔ v 0 < v 1 := by
  rw [Matrix.fun_eq_vec_two v]; simp


-- @@ L642-648 verbatim
@[simp] lemma mem_iff_mem [Operator.Mem L] [Membership M M] [Structure.Mem L M] {v : Fin 2 →M} :
    (@Operator.Mem.mem L _).val v ↔ v 0 ∈ v 1 := by
  rw [Matrix.fun_eq_vec_two v]; simp

lemma le_iff_of_eq_of_lt [Operator.Eq L] [Operator.LT L] [LT M] [Structure.Eq L M] [Structure.LT L M] {a b : M} :
    (@Operator.LE.le L _).val ![a, b] ↔ a = b ∨ a < b := by
  simp [Operator.LE.def_of_Eq_of_LT]


-- @@ L650-651 verbatim
@[simp] lemma eq_lang [L.Eq] [Structure.Eq L M] {v : Fin 2 → M} :
    Structure.rel (L := L) Language.Eq.eq v ↔ v 0 = v 1 := by simpa [-eq_iff_eq] using! eq_iff_eq (L := L) (v := v)


-- @@ L653-654 verbatim
@[simp] lemma lt_lang [L.LT] [LT M] [Structure.LT L M] {v : Fin 2 → M} :
    Structure.rel (L := L) Language.LT.lt v ↔ v 0 < v 1 := by simpa [-lt_iff_lt] using! lt_iff_lt (L := L) (v := v)


-- @@ L656-661 verbatim
@[simp] lemma mem_lang [L.Mem] [Membership M M] [Structure.Mem L M] {v : Fin 2 → M} :
    Structure.rel (L := L) Language.Mem.mem v ↔ v 0 ∈ v 1 := by simpa [-mem_iff_mem] using! mem_iff_mem (L := L) (v := v)

lemma operator_val_ofEquiv_iff (φ : M ≃ N) {k : ℕ} {o : Semiformula.Operator L k} {v : Fin k → N} :
    letI : Structure L N := ofEquiv φ
    o.val v ↔ o.val (φ.symm ∘ v) := by simp [Semiformula.Operator.val, eval_ofEquiv_iff, Empty.eq_elim]


-- @@ L663-663 verbatim
end Structure


-- @@ L665-665 verbatim
namespace Semiformula


-- @@ L667-667 verbatim
variable {M : Type*} {s : Structure L M}


-- @@ L669-669 verbatim
variable {e : Fin n → M} {f : ξ → M} {t : Semiterm L ξ n} {φ : Semiformula L ξ (n + 1)}


-- @@ L671-672 verbatim
@[simp] lemma eval_ballLT [Operator.LT L] [LT M] [Structure.LT L M] :
    (φ.ballLT t).Eval e f ↔ ∀ x < t.val e f, φ.Eval (x :> e) f := by simp [ballLT]


-- @@ L674-675 verbatim
@[simp] lemma eval_bexsLT [Operator.LT L] [LT M] [Structure.LT L M] :
    (φ.bexsLT t).Eval e f ↔ ∃ x < t.val e f, φ.Eval (x :> e) f := by simp [bexsLT]


-- @@ L677-678 verbatim
@[simp] lemma eval_ballLE [Operator.LE L] [LE M] [Structure.LE L M] :
    (φ.ballLE t).Eval e f ↔ ∀ x ≤ t.val e f, φ.Eval (x :> e) f := by simp [ballLE]


-- @@ L680-681 verbatim
@[simp] lemma eval_bexsLE [Operator.LE L] [LE M] [Structure.LE L M] :
    (φ.bexsLE t).Eval e f ↔ ∃ x ≤ t.val e f, φ.Eval (x :> e) f := by simp [bexsLE]


-- @@ L683-684 verbatim
@[simp] lemma eval_ballMem [Operator.Mem L] [Membership M M] [Structure.Mem L M] :
    (φ.ballMem t).Eval e f ↔ ∀ x ∈ t.val e f, φ.Eval (x :> e) f := by simp [ballMem]


-- @@ L686-687 verbatim
@[simp] lemma eval_bexsMem [Operator.Mem L] [Membership M M] [Structure.Mem L M] :
    (φ.bexsMem t).Eval e f ↔ ∃ x ∈ t.val e f, φ.Eval (x :> e) f := by simp [bexsMem]


-- @@ L689-689 verbatim
end Semiformula


-- @@ L691-691 verbatim
namespace Semiterm


-- @@ L693-693 verbatim
variable [L.Zero] [L.One] [L.Add]


-- @@ L695-695 verbatim
@[coe] abbrev numeral (k : ℕ) : Semiterm L ξ n := Operator.numeral L k


-- @@ L697-697 verbatim
instance : Coe ℕ (Semiterm L ξ n) := ⟨numeral⟩


-- @@ L699-699 verbatim
end Semiterm


-- @@ L701-701 verbatim
end FirstOrder


-- @@ L703-703 verbatim
end FFL


-- @@ L705-705 verbatim
end
