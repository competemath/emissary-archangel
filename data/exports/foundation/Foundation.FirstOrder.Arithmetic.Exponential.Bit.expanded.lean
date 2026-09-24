module

public import Foundation.FirstOrder.Arithmetic.Exponential.Log


-- @@ L5-7 verbatim
/-!
# $\mathrm{Bit}$ predicate
-/


-- @@ L9-9 verbatim
@[expose] public section


-- @@ L11-11 verbatim
namespace FFL.FirstOrder.Arithmetic


-- @@ L13-13 verbatim
variable {V : Type*} [ORingStructure V]


-- @@ L15-15 verbatim
section


-- @@ L17-17 verbatim
variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]


-- @@ L19-19 verbatim
section model


-- @@ L21-21 verbatim
def Bit (i a : V) : Prop := LenBit (Exp.exp i) a


-- @@ L23-24 verbatim
/-- Support for `∈` notation over a model of arithmetic, implemented by binary encoding. -/
instance : Membership V V := ⟨fun a i ↦ Bit i a⟩


-- @@ L26-27 verbatim
def _root_.FFL.FirstOrder.Arithmetic.bitDef : 𝚺₀.Semisentence 2 := .mkSigma
  “x y. ∃ z <⁺ y, !expDef z x ∧ !lenbitDef z y”


-- @@ L29-34 verbatim
set_option linter.flexible false in
instance bit_defined : 𝚺₀-Relation[V] (· ∈ ·) via bitDef := .mk fun v ↦ by
  simp [bitDef]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h; exact ⟨by simp [h.le], h⟩


-- @@ L36-36 verbatim
instance mem_definable : 𝚺₀-Relation[V] (· ∈ ·) := bit_defined.to_definable


-- @@ L38-38 verbatim
instance mem_definable' (ℌ : HierarchySymbol) : ℌ-Relation[V] (· ∈ ·) := mem_definable.of_zero


-- @@ L40-52 verbatim
instance mem_definable'' (ℌ : HierarchySymbol) : ℌ-Relation[V] Membership.mem := by
  simpa using (mem_definable' ℌ).retraction ![1, 0]

lemma mem_absolute (i a : ℕ) : i ∈ a ↔ (i : V) ∈ (a : V) := by
  simpa using Defined.shigmaZero_absolute V bit_defined bit_defined ![i, a]

lemma mem_iff_bit {i a : V} : i ∈ a ↔ Bit i a := iff_of_eq rfl

lemma exp_le_of_mem {i a : V} (h : i ∈ a) : Exp.exp i ≤ a := LenBit.le h

lemma lt_of_mem {i a : V} (h : i ∈ a) : i < a := lt_of_lt_of_le (lt_exp i) (exp_le_of_mem h)

lemma not_mem_of_lt_exp {i a : V} (h : a < Exp.exp i) : i ∉ a := fun H ↦ by have := lt_of_le_of_lt (exp_le_of_mem H) h; simp at this


-- @@ L54-59 verbatim
@[definability] lemma HierarchySymbol.Definable.ball_mem (Γ m) {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : 𝚺-[m + 1].DefinableFunction f) (h : Γ-[m + 1].Definable (fun w ↦ P (w ·.succ) (w 0))) :
    Γ-[m + 1].Definable (fun v ↦ ∀ x ∈ f v, P v x) := by
  have : Γ-[m + 1].Definable (fun v ↦ ∀ x < f v, x ∈ f v → P v x) :=
    .ball_lt hf (.imp (HierarchySymbol.Definable.comp₂ (P := (· ∈ ·)) (.var 0) (hf.retraction Fin.succ)) h)
  exact this.of_iff <| by intro v; exact ⟨fun h x _ hxv ↦ h x hxv, fun h x hx ↦ h x (lt_of_mem hx) hx⟩


-- @@ L61-67 verbatim
@[definability] lemma HierarchySymbol.Definable.bexs_mem (Γ m) {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : 𝚺-[m + 1].DefinableFunction f) (h : Γ-[m + 1].Definable (fun w ↦ P (w ·.succ) (w 0))) :
    Γ-[m + 1].Definable (fun v ↦ ∃ x ∈ f v, P v x) := by
  have : Γ-[m + 1].Definable (fun v ↦ ∃ x < f v, x ∈ f v ∧ P v x) :=
    .bexs_lt hf (.and (HierarchySymbol.Definable.comp₂ (P := (· ∈ ·)) (.var 0) (hf.retraction _)) h)
  exact this.of_iff <| by
    intro v; exact ⟨by rintro ⟨x, hx, hxv⟩; exact ⟨x, lt_of_mem hx, hx, hxv⟩, by rintro ⟨x, _, hx, hvx⟩; exact ⟨x, hx, hvx⟩⟩


-- @@ L69-69 verbatim
end model


-- @@ L71-71 verbatim
section mem


-- @@ L73-73 verbatim
variable {ξ : Type*} {n}


-- @@ L75-78 verbatim
instance : Semiformula.Operator.Mem ℒₒᵣ := ⟨⟨bitDef.val⟩⟩

lemma operator_mem_def : Semiformula.Operator.Mem.mem.sentence = bitDef.val := by
  simp [Semiformula.Operator.Mem.mem]


-- @@ L80-80 verbatim
def ballIn (t : ArithmeticSemiterm ξ n) (p : ArithmeticSemiformula ξ (n + 1)) : ArithmeticSemiformula ξ n := “∀ x < !!t, x ∈ !!(Rew.bShift t) → !p x ⋯”


-- @@ L82-82 verbatim
def bexsIn (t : ArithmeticSemiterm ξ n) (p : ArithmeticSemiformula ξ (n + 1)) : ArithmeticSemiformula ξ n := “∃ x < !!t, x ∈ !!(Rew.bShift t) ∧ !p x ⋯”


-- @@ L84-85 verbatim
@[simp] lemma Hierarchy.bit {t u : ArithmeticSemiterm μ n} : Hierarchy Γ s “!!t ∈ !!u” := by
  simp [Semiformula.Operator.operator, Matrix.fun_eq_vec_two, operator_mem_def]


-- @@ L87-90 verbatim
@[simp] lemma Hieralchy.ballIn {Γ m} (t : ArithmeticSemiterm ξ n) (p : ArithmeticSemiformula ξ (n + 1)) :
    Hierarchy Γ m (ballIn t p) ↔ Hierarchy Γ m p := by
  simp only [Arithmetic.ballIn]
  simp [Semiformula.Operator.operator, operator_mem_def]


-- @@ L92-95 verbatim
@[simp] lemma Hieralchy.bexsIn {Γ m} (t : ArithmeticSemiterm ξ n) (p : ArithmeticSemiformula ξ (n + 1)) :
    Hierarchy Γ m (bexsIn t p) ↔ Hierarchy Γ m p := by
  simp only [Arithmetic.bexsIn]
  simp [Semiformula.Operator.operator, operator_mem_def]


-- @@ L97-98 verbatim
def memRel : 𝚺₀.Semisentence 3 := .mkSigma
  “R x y. ∃ p <⁺ (x + y + 1)², !pairDef p x y ∧ p ∈ R”


-- @@ L100-101 verbatim
def memRel₃ : 𝚺₀.Semisentence 4 := .mkSigma
  “R x y z. ∃ yz <⁺ (y + z + 1)², !pairDef yz y z ∧ ∃ xyz <⁺ (x + yz + 1)², !pairDef xyz x yz ∧ xyz ∈ R”


-- @@ L103-104 verbatim
/-- The relation `⟪x, y⟫ ∈ R` in arithmetic, implemented by binary coding, as an operator. -/
def memRelOpr : Semiformula.Operator ℒₒᵣ 3 := ⟨memRel.val⟩


-- @@ L106-106 verbatim
def memRel₃Opr : Semiformula.Operator ℒₒᵣ 4 := ⟨memRel₃.val⟩


-- @@ L108-108 verbatim
section notations


-- @@ L110-110 verbatim
open Lean PrettyPrinter Delaborator


-- @@ L112-112 verbatim
syntax:max "∀ " ident " ∈' " first_order_term ", " first_order_formula:0 : first_order_formula

-- @@ L113-113 verbatim
syntax:max "∃ " ident " ∈' " first_order_term ", " first_order_formula:0 : first_order_formula


-- @@ L115-123 verbatim
macro_rules
  | `(⤫formula(lit)[ $binders* | $fbinders* | ∀ $x ∈' $t, $p]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    let binders' := binders.insertIdx 0 x
    `(ballIn ⤫term(lit)[ $binders* | $fbinders* | $t] ⤫formula(lit)[$binders'* | $fbinders* | $p])
  | `(⤫formula(lit)[ $binders* | $fbinders* | ∃ $x ∈' $t, $p]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    let binders' := binders.insertIdx 0 x
    `(bexsIn ⤫term(lit)[$binders* | $fbinders* | $t] ⤫formula(lit)[$binders'* | $fbinders* | $p])


-- @@ L125-126 verbatim
/-- `x ~[m] y` states that `⟪x, y⟫` is in `m`, where the notion of "in" is implemented by binary coding. -/
syntax:45 first_order_term:45 " ∼[" first_order_term "]" first_order_term:0 : first_order_formula

-- @@ L127-127 verbatim
syntax:45 first_order_term:45 " ≁[" first_order_term "]" first_order_term:0 : first_order_formula

-- @@ L128-128 verbatim
syntax:45 ":⟪" first_order_term ", " first_order_term "⟫:∈ " first_order_term:0 : first_order_formula

-- @@ L129-129 verbatim
syntax:45 ":⟪" first_order_term ", " first_order_term ", " first_order_term "⟫:∈ " first_order_term:0 : first_order_formula


-- @@ L131-139 verbatim
macro_rules
  | `(⤫formula(lit)[ $binders* | $fbinders* | $t₁:first_order_term ∼[ $u:first_order_term ] $t₂:first_order_term]) =>
    `(memRelOpr.operator ![⤫term(lit)[$binders* | $fbinders* | $u], ⤫term(lit)[$binders* | $fbinders* | $t₁], ⤫term(lit)[$binders* | $fbinders* | $t₂]])
  | `(⤫formula(lit)[ $binders* | $fbinders* | $t₁:first_order_term ≁[ $u:first_order_term ] $t₂:first_order_term]) =>
    `(∼memRelOpr.operator ![⤫term(lit)[$binders* | $fbinders* | $u], ⤫term(lit)[$binders* | $fbinders* | $t₁], ⤫term(lit)[$binders* | $fbinders* | $t₂]])
  | `(⤫formula(lit)[ $binders* | $fbinders* | :⟪$t₁:first_order_term, $t₂:first_order_term⟫:∈ $u:first_order_term]) =>
    `(memRelOpr.operator ![⤫term(lit)[$binders* | $fbinders* | $u], ⤫term(lit)[$binders* | $fbinders* | $t₁], ⤫term(lit)[$binders* | $fbinders* | $t₂]])
  | `(⤫formula(lit)[ $binders* | $fbinders* | :⟪$t₁:first_order_term, $t₂:first_order_term, $t₃:first_order_term⟫:∈ $u:first_order_term]) =>
    `(memRel₃Opr.operator ![⤫term(lit)[$binders* | $fbinders* | $u], ⤫term(lit)[$binders* | $fbinders* | $t₁], ⤫term(lit)[$binders* | $fbinders* | $t₂], ⤫term(lit)[$binders* | $fbinders* | $t₃]])


-- @@ L141-142 verbatim
@[simp] lemma Hierarchy.memRel {t₁ t₂ u : ArithmeticSemiterm μ n} : Hierarchy Γ s “!!t₁ ∼[ !!u ] !!t₂” := by
  simp [Semiformula.Operator.operator, Matrix.fun_eq_vec_two, memRelOpr]


-- @@ L144-145 verbatim
@[simp] lemma Hierarchy.memRel₃ {t₁ t₂ t₃ u : ArithmeticSemiterm μ n} : Hierarchy Γ s “:⟪!!t₁, !!t₂, !!t₃⟫:∈ !!u” := by
  simp [Semiformula.Operator.operator, Matrix.fun_eq_vec_two, memRel₃Opr]


-- @@ L147-147 verbatim
end notations


-- @@ L149-149 verbatim
end mem


-- @@ L151-151 verbatim
section model


-- @@ L153-153 verbatim
scoped instance : Structure.Mem ℒₒᵣ V := ⟨by intro a b; simp [Semiformula.Operator.val, operator_mem_def]⟩


-- @@ L155-162 verbatim
@[simp] lemma eval_ballIn {t : ArithmeticSemiterm ξ n} {φ : ArithmeticSemiformula ξ (n + 1)} {bv : Fin n → V} {fv : ξ → V} :
    (ballIn t φ).Eval (M := V) bv fv ↔ ∀ x ∈ t.val bv fv, φ.Eval (x :> bv) fv := by
  suffices
    (∀ x < t.val bv fv, x ∈ t.val bv fv → φ.Eval (x :> bv) fv) ↔
    ∀ x ∈ t.val bv fv, φ.Eval (x :> bv) fv by simpa [ballIn]
  constructor
  · intro h x hx; exact h x (lt_of_mem hx) hx
  · intro h x _ hx; exact h x hx


-- @@ L164-171 verbatim
@[simp] lemma eval_bexsIn {t : ArithmeticSemiterm ξ n} {φ : ArithmeticSemiformula ξ (n + 1)} {bv : Fin n → V} {fv : ξ → V} :
    (bexsIn t φ).Eval (M := V) bv fv ↔ ∃ x ∈ t.val bv fv, φ.Eval (x :> bv) fv := by
  suffices
    (∃ x < t.val bv fv, x ∈ t.val bv fv ∧ φ.Eval (x :> bv) fv) ↔
    ∃ x ∈ t.val bv fv, φ.Eval (x :> bv) fv by simpa [bexsIn]
  constructor
  · rintro ⟨x, _, hx, h⟩; exact ⟨x, hx, h⟩
  · rintro ⟨x, hx, h⟩; exact ⟨x, lt_of_mem hx, hx, h⟩


-- @@ L173-173 verbatim
instance memRel_defined : 𝚺₀-Relation₃ (fun r x y : V ↦ ⟪x, y⟫ ∈ r) via memRel := .mk fun v ↦ by simp [memRel]


-- @@ L175-175 verbatim
instance memRel₃_defined : 𝚺₀-Relation₄ (fun r x y z : V ↦ ⟪x, y, z⟫ ∈ r) via memRel₃ := .mk fun v ↦ by simp [memRel₃]


-- @@ L177-180 verbatim
@[simp] lemma eval_memRel {x y r : V} :
    memRelOpr.val ![r, x, y] ↔ ⟪x, y⟫ ∈ r := by
  unfold Semiformula.Operator.val
  simp [memRelOpr]


-- @@ L182-185 verbatim
@[simp] lemma eval_memRel₃ {x y z r : V} :
    memRel₃Opr.val ![r, x, y, z] ↔ ⟪x, y, z⟫ ∈ r := by
  unfold Semiformula.Operator.val
  simp [memRel₃Opr]


-- @@ L187-187 verbatim
end model


-- @@ L189-195 verbatim
section model

lemma mem_iff_mul_exp_add_exp_add {i a : V} : i ∈ a ↔ ∃ k, ∃ r < Exp.exp i, a = k * Exp.exp (i + 1) + Exp.exp i + r := by
  simpa [mem_iff_bit, exp_succ] using! lenbit_iff_add_mul (exp_pow2 i) (a := a)

lemma not_mem_iff_mul_exp_add {i a : V} : i ∉ a ↔ ∃ k, ∃ r < Exp.exp i, a = k * Exp.exp (i + 1) + r := by
  simpa [mem_iff_bit, exp_succ] using! not_lenbit_iff_add_mul (exp_pow2 i) (a := a)


-- @@ L197-197 verbatim
section empty


-- @@ L199-199 verbatim
scoped instance : EmptyCollection V := ⟨0⟩


-- @@ L201-202 verbatim
omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma emptyset_def : (∅ : V) = 0 := rfl


-- @@ L204-204 verbatim
@[simp] lemma not_mem_empty (i : V) : i ∉ (∅ : V) := by simp [emptyset_def, mem_iff_bit, Bit]


-- @@ L206-206 verbatim
@[simp] lemma not_mem_zero (i : V) : i ∉ (0 : V) := by simp [mem_iff_bit, Bit]


-- @@ L208-208 verbatim
end empty


-- @@ L210-210 verbatim
section singleton


-- @@ L212-214 verbatim
noncomputable scoped instance : Singleton V V := ⟨fun a ↦ Exp.exp a⟩

lemma singleton_def (a : V) : {a} = Exp.exp a := rfl


-- @@ L216-220 verbatim
@[simp] lemma singleton_injective (a b : V) : ({a} : V) = {b} ↔ a = b := by
  constructor
  · intro h
    simpa [singleton_def] using congr_arg log h
  · rintro rfl; rfl


-- @@ L222-222 verbatim
end singleton


-- @@ L224-224 verbatim
section insert


-- @@ L226-227 verbatim
open Classical in
noncomputable def bitInsert (i a : V) : V := if i ∈ a then a else a + Exp.exp i


-- @@ L229-230 verbatim
open Classical in
noncomputable def bitRemove (i a : V) : V := if i ∈ a then a - Exp.exp i else a


-- @@ L232-236 verbatim
noncomputable scoped instance : Insert V V := ⟨bitInsert⟩

lemma insert_eq {i a : V} : insert i a = bitInsert i a := rfl

lemma singleton_eq_insert (i : V) : ({i} : V) = insert i ∅ := by simp [singleton_def, insert, bitInsert, emptyset_def]


-- @@ L238-239 verbatim
instance : LawfulSingleton V V where
  insert_empty_eq := fun x ↦ Eq.symm <| singleton_eq_insert x


-- @@ L241-246 verbatim
@[simp] lemma mem_bitInsert_iff {i j a : V} :
    i ∈ insert j a ↔ i = j ∨ i ∈ a := by
  by_cases h : j ∈ a <;> simp [h, insert_eq, bitInsert]
  · by_cases e : i = j <;> simp [h, e]
  · simpa [exp_inj.eq_iff] using!
      lenbit_add_pow2_iff_of_not_lenbit (exp_pow2 i) (exp_pow2 j) h


-- @@ L248-254 verbatim
@[simp] lemma mem_bitRemove_iff {i j a : V} :
    i ∈ bitRemove j a ↔ i ≠ j ∧ i ∈ a := by
  by_cases h : j ∈ a
  · simpa [h, bitRemove, exp_inj.eq_iff] using!
      lenbit_sub_pow2_iff_of_lenbit (exp_pow2 i) (exp_pow2 j) h
  · simp only [bitRemove, h, ↓reduceIte, ne_eq, iff_and_self]
    rintro _ rfl; contradiction


-- @@ L256-264 verbatim
@[simp] lemma not_mem_bitRemove_self (i a : V) : i ∉ bitRemove i a := by simp

lemma insert_graph (b i a : V) :
    b = insert i a ↔ (i ∈ a ∧ b = a) ∨ (i ∉ a ∧ ∃ e ≤ b, e = Exp.exp i ∧ b = a + e) :=
  ⟨by rintro rfl; by_cases hi : i ∈ a <;> simp [hi, insert, bitInsert],
   by by_cases hi : i ∈ a <;> simp only [hi, true_and, not_true_eq_false, false_and,
        or_false, insert, bitInsert, ↓reduceIte, imp_self,
        not_false_eq_true, true_and, false_or, forall_exists_index, and_imp]
      rintro x _ rfl rfl; rfl ⟩


-- @@ L266-267 verbatim
def _root_.FFL.FirstOrder.Arithmetic.insertDef : 𝚺₀.Semisentence 3 := .mkSigma
  “b i a. (i ∈ a ∧ b = a) ∨ (i ∉ a ∧ ∃ e <⁺ b, !expDef e i ∧ b = a + e)”


-- @@ L269-269 verbatim
instance insert_defined : 𝚺₀-Function₂[V] insert via insertDef := .mk fun v ↦ by simp [insertDef, insert_graph]


-- @@ L271-271 verbatim
instance insert_definable : 𝚺₀-Function₂[V] insert := insert_defined.to_definable


-- @@ L273-273 verbatim
instance insert_definable' (Γ) : Γ-Function₂[V] insert := insert_definable.of_zero


-- @@ L275-286 verbatim
open Classical in
lemma insert_le_of_le_of_le {i j a b : V} (hij : i ≤ j) (hab : a ≤ b) : insert i a ≤ b + Exp.exp j := by
  suffices (if i ∈ a then a else a + Exp.exp i) ≤ b + Exp.exp j by simpa [insert, bitInsert]
  by_cases hi : i ∈ a
  · simpa [hi] using le_trans hab (by simp)
  · simpa [hi] using add_le_add hab (exp_monotone_le.mpr hij)

lemma insert_absolute (x s : ℕ) :
    ((insert x s : ℕ) : V) = insert (x : V) (s : V) := by
  have := DefinedFunction.shigmaZero_absolute_func V (k := 2) (f := fun v ↦ insert (v 0) (v 1)) (f' := fun v ↦ insert (v 0) (v 1))
      (φ := insertDef) insert_defined insert_defined ![x, s]
  simpa using this


-- @@ L288-290 verbatim
end insert

lemma one_eq_singleton : (1 : V) = {∅} := by simp [singleton_eq_insert, insert, bitInsert, emptyset_def]


-- @@ L292-301 verbatim
@[simp] lemma mem_singleton_iff {i j : V} :
    i ∈ ({j} : V) ↔ i = j := by simp [singleton_eq_insert, -insert_empty_eq]

lemma bitRemove_lt_of_mem {i a : V} (h : i ∈ a) : bitRemove i a < a := by
  simp [h, bitRemove, tsub_lt_iff_left (exp_le_of_mem h)]

lemma pos_of_nonempty {i a : V} (h : i ∈ a) : 0 < a := by
  by_contra A
  rcases show a = 0 by simpa using A
  simp_all


-- @@ L303-327 verbatim
@[simp] lemma mem_insert (i a : V) : i ∈ insert i a := by simp

lemma insert_eq_self_of_mem {i a : V} (h : i ∈ a) : insert i a = a := by
  simp [insert_eq, bitInsert, h]

lemma log_mem_of_pos {a : V} (h : 0 < a) : log a ∈ a :=
  mem_iff_mul_exp_add_exp_add.mpr
    ⟨0, a - Exp.exp (log a),
      (tsub_lt_iff_left (exp_log_le_self h)).mpr (by rw [←two_mul]; exact lt_two_mul_exponential_log h),
      by simpa using Eq.symm <| add_tsub_self_of_le (exp_log_le_self h)⟩

lemma le_log_of_mem {i a : V} (h : i ∈ a) : i ≤ log a := (exp_le_iff_le_log (pos_of_nonempty h)).mp (exp_le_of_mem h)

lemma succ_mem_iff_mem_div_two {i a : V} : i + 1 ∈ a ↔ i ∈ a / 2 := by
  simp [mem_iff_bit, Bit, LenBit.iff_rem, exp_succ, Arithmetic.div_mul]

lemma lt_length_of_mem {i a : V} (h : i ∈ a) : i < ‖a‖ := by
  simpa [length_of_pos (pos_of_nonempty h), ←le_iff_lt_succ] using le_log_of_mem h

lemma lt_exp_iff {a i : V} : a < Exp.exp i ↔ ∀ j ∈ a, j < i :=
  ⟨fun h j hj ↦ exp_monotone.mp <| lt_of_le_of_lt (exp_le_of_mem hj) h,
   by suffices Exp.exp i ≤ a → ∃ x ∈ a, i ≤ x by contrapose; simpa
      intro h
      have pos : 0 < a := lt_of_lt_of_le (by simp) h
      exact ⟨log a, log_mem_of_pos pos, (exp_le_iff_le_log pos).mp h⟩⟩


-- @@ L329-329 verbatim
instance : HasSubset V := ⟨fun a b ↦ ∀ ⦃i⦄, i ∈ a → i ∈ b⟩


-- @@ L331-332 verbatim
def _root_.FFL.FirstOrder.Arithmetic.bitSubsetDef : 𝚺₀.Semisentence 2 := .mkSigma
  “a b. ∀ i < a, i ∈ a → i ∈ b”


-- @@ L334-336 verbatim
instance bitSubset_defined : 𝚺₀-Relation[V] Subset via bitSubsetDef := .mk fun v ↦ by
  simpa [bitSubsetDef]
    using ⟨by intro h x hx; exact h x (lt_of_mem hx) hx, by intro h x _ hx; exact h hx⟩


-- @@ L338-338 verbatim
instance bitSubset_definable : 𝚺₀-Relation[V] Subset := bitSubset_defined.to_definable₀


-- @@ L340-342 verbatim
@[simp, definability] instance bitSubset_definable' (ℌ : HierarchySymbol) : ℌ-Relation[V] Subset := bitSubset_defined.to_definable₀

lemma subset_iff {a b : V} : a ⊆ b ↔ (∀ x ∈ a, x ∈ b) := by simp [HasSubset.Subset]


-- @@ L344-344 verbatim
@[refl, simp] lemma subset_refl (a : V) : a ⊆ a := by intro x; simp


-- @@ L346-357 verbatim
@[trans] lemma subset_trans {a b c : V} (hab : a ⊆ b) (hbc : b ⊆ c) : a ⊆ c := by
  intro x hx; exact hbc (hab hx)

lemma mem_exp_add_succ_sub_one (i j : V) : i ∈ Exp.exp (i + j + 1) - 1 := by
  have : Exp.exp (i + j + 1) - 1 = (Exp.exp j - 1) * Exp.exp (i + 1) + Exp.exp i + (Exp.exp i - 1) := calc
    Exp.exp (i + j + 1) - 1 = Exp.exp j * Exp.exp (i + 1) - 1                             := by simp [exp_add, ←mul_assoc, mul_comm]
    _                   = Exp.exp j * Exp.exp (i + 1) - Exp.exp (i + 1) + Exp.exp (i + 1) - 1 := by rw [sub_add_self_of_le]; exact le_mul_of_pos_left (exp_pos j)
    _                   = (Exp.exp j - 1) * Exp.exp (i + 1) + Exp.exp (i + 1) - 1         := by simp [sub_mul]
    _                   = (Exp.exp j - 1) * Exp.exp (i + 1) + (Exp.exp i + Exp.exp i) - 1     := by simp [←two_mul, ←exp_succ i]
    _                   = (Exp.exp j - 1) * Exp.exp (i + 1) + (Exp.exp i + Exp.exp i - 1)     := by rw [add_tsub_assoc_of_le]; simp [←two_mul, ←pos_iff_one_le]
    _                   = (Exp.exp j - 1) * Exp.exp (i + 1) + Exp.exp i + (Exp.exp i - 1)     := by simp [add_assoc, add_tsub_assoc_of_le]
  exact mem_iff_mul_exp_add_exp_add.mpr ⟨Exp.exp j - 1, Exp.exp i - 1, (tsub_lt_iff_left (by simp)).mpr $ by simp, this⟩


-- @@ L359-360 verbatim
/-- under a = {0, 1, 2, ..., a - 1} -/
noncomputable def under (a : V) : V := Exp.exp a - 1


-- @@ L362-363 verbatim
@[simp] lemma le_under (a : V) : a ≤ under a :=
  le_iff_lt_succ.mpr (by simp [under, show Exp.exp a - 1 + 1 = Exp.exp a from sub_add_self_of_le (by simp)])


-- @@ L365-379 verbatim
@[simp] lemma mem_under_iff {i j : V} : i ∈ under j ↔ i < j := by
  constructor
  · intro h
    have : Exp.exp i < Exp.exp j := calc
      Exp.exp i ≤ Exp.exp j - 1 := exp_le_of_mem h
      _     < Exp.exp j     := pred_lt_self_of_pos (exp_pos j)
    exact exp_monotone.mp this
  · intro lt
    have := lt_iff_succ_le.mp lt
    let k := j - (i + 1)
    have : j = i + k + 1 := calc
      j = i + (j - i)         := by rw [add_tsub_self_of_le (le_of_lt lt)]
      _ = i + (j - i - 1 + 1) := by rw [sub_add_self_of_le <| le_tsub_of_add_le_left <| lt_iff_succ_le.mp lt]
      _ = i + k + 1           := by simp [add_assoc, ←Arithmetic.sub_sub, k]
    rw [this]; exact mem_exp_add_succ_sub_one i k


-- @@ L381-381 verbatim
@[simp] lemma not_mem_under_self (i : V) : i ∉ under i := by simp


-- @@ L383-388 verbatim
private lemma under_graph (x y : V) : y = under x ↔ y + 1 = Exp.exp x := by
  constructor
  · rintro rfl; simp [under, sub_add_self_of_le]
  · intro h
    have := congr_arg (· - 1) h
    simpa [under] using this


-- @@ L390-391 verbatim
def _root_.FFL.FirstOrder.Arithmetic.underDef : 𝚺₀.Semisentence 2 := .mkSigma
  “y x. !expDef.val (y + 1) x”


-- @@ L393-393 verbatim
instance under_defined : 𝚺₀-Function₁[V] under via underDef := .mk fun v ↦ by simp [underDef, under_graph]


-- @@ L395-395 verbatim
instance under_definable : 𝚺₀-Function₁[V] under := under_defined.to_definable


-- @@ L397-409 verbatim
instance under_definable' (Γ) : Γ-Function₁[V] under := under_definable.of_zero

lemma eq_zero_of_subset_zero {a : V} : a ⊆ 0 → a = 0 := by
  intro h; by_contra A
  have : log a ∈ (0 : V) := h (log_mem_of_pos (pos_iff_ne_zero.mpr A))
  simp_all

lemma subset_div_two {a b : V} : a ⊆ b → a / 2 ⊆ b / 2 := by
  intro ss i hi
  have : i + 1 ∈ a := succ_mem_iff_mem_div_two.mpr hi
  exact succ_mem_iff_mem_div_two.mp <| ss this

lemma zero_mem_iff {a : V} : 0 ∉ a ↔ 2 ∣ a := by simp [mem_iff_bit, Bit, LenBit]


-- @@ L411-411 verbatim
@[simp] lemma zero_not_mem (a : V) : 0 ∉ 2 * a := by simp [mem_iff_bit, Bit, LenBit]


-- @@ L413-413 verbatim
@[simp] lemma zero_mem_double_add_one (a : V) : 0 ∈ 2 * a + 1 := by simp [mem_iff_bit, Bit, LenBit, ←mod_eq_zero_iff_dvd]


-- @@ L415-416 verbatim
@[simp] lemma succ_mem_two_mul_iff {i a : V} : i + 1 ∈ 2 * a ↔ i ∈ a := by
  simp [mem_iff_bit, Bit, LenBit, exp_succ, div_cancel_left]


-- @@ L418-458 verbatim
@[simp] lemma succ_mem_two_mul_succ_iff {i a : V} : i + 1 ∈ 2 * a + 1 ↔ i ∈ a := by
  simp [mem_iff_bit, Bit, LenBit, exp_succ, Arithmetic.div_mul]

lemma le_of_subset {a b : V} (h : a ⊆ b) : a ≤ b := by
  induction b using pi1_polynomial_induction generalizing a
  · definability
  case zero =>
    simp [eq_zero_of_subset_zero h]
  case even b _ IH =>
    have IH : a / 2 ≤ b := IH (by simpa using subset_div_two h)
    have : 2 * (a / 2) = a :=
      mul_div_self_of_dvd.mpr (zero_mem_iff.mp $ by intro ha; have : 0 ∈ 2 * b := h ha; simp_all)
    simpa [this] using mul_le_mul_left (a := 2) IH
  case odd b IH =>
    have IH : a / 2 ≤ b := IH (by simpa [div_mul_add' b 2 one_lt_two] using subset_div_two h)
    exact le_trans (le_two_mul_div_two_add_one a) (by simpa using IH)

lemma mem_ext {a b : V} (h : ∀ i, i ∈ a ↔ i ∈ b) : a = b :=
  le_antisymm (le_of_subset fun i hi ↦ (h i).mp hi) (le_of_subset fun i hi ↦ (h i).mpr hi)

lemma mem_ext_iff {a b : V} : a = b ↔ ∀ i, i ∈ a ↔ i ∈ b := ⟨by rintro rfl; simp, mem_ext⟩

lemma pos_iff_nonempty {s : V} : 0 < s ↔ s ≠ ∅ := pos_iff_ne_zero

lemma nonempty_of_pos {a : V} (h : 0 < a) : ∃ i, i ∈ a := by
  by_contra A
  have : a = 0 := mem_ext (by simpa using A)
  simp [this] at h

lemma eq_empty_or_nonempty (a : V) : a = ∅ ∨ ∃ i, i ∈ a := by
  rcases Arithmetic.zero_le a with (rfl | pos)
  · simp [emptyset_def]
  · right; exact nonempty_of_pos pos

lemma nonempty_iff {s : V} : s ≠ ∅ ↔ ∃ x, x ∈ s := by
  rcases eq_empty_or_nonempty s with ⟨rfl, hy⟩
  · simp
  · simpa [show s ≠ ∅ from by rintro rfl; simp_all]

lemma isempty_iff {s : V} : s = ∅ ↔ ∀ x, x ∉ s := by
  simpa using not_iff_not.mpr (nonempty_iff (s := s))


-- @@ L460-466 verbatim
@[simp] lemma empty_subset (s : V) : ∅ ⊆ s := by intro x; simp

lemma lt_of_lt_log {a b : V} (pos : 0 < b) (h : ∀ i ∈ a, i < log b) : a < b := by
  rcases Arithmetic.zero_le a with (rfl | apos)
  · exact pos
  by_contra A
  exact not_lt_of_ge (log_monotone <| show b ≤ a by simpa using A) (h (log a) (log_mem_of_pos apos))


-- @@ L468-474 verbatim
@[simp] lemma under_inj {i j : V} : under i = under j ↔ i = j := ⟨fun h ↦ by
  by_contra ne
  wlog lt : i < j
  · exact this (Eq.symm h) (Ne.symm ne) (lt_of_le_of_ne (by simpa using lt) (Ne.symm ne))
  have : i ∉ under i := by simp
  have : i ∈ under i := by rw [h]; simp [mem_under_iff, lt]
  contradiction, by rintro rfl; simp⟩


-- @@ L476-476 verbatim
@[simp] lemma under_zero : under (0 : V) = ∅ := mem_ext (by simp [mem_under_iff])


-- @@ L478-486 verbatim
@[simp] lemma under_succ (i : V) : under (i + 1) = insert i (under i) :=
  mem_ext (by simp [mem_under_iff, lt_succ_iff_le, le_iff_eq_or_lt])

lemma insert_remove {i a : V} (h : i ∈ a) : insert i (bitRemove i a) = a := mem_ext <| by
  suffices ∀ j, j = i ∨ j ≠ i ∧ j ∈ a ↔ j ∈ a by simpa
  intro j
  constructor
  · rintro (rfl | ⟨_, hj⟩) <;> assumption
  · intro hj; simp [hj, eq_or_ne j i]


-- @@ L488-488 verbatim
end model


-- @@ L490-490 verbatim
end



-- @@ L493-493 verbatim
section


-- @@ L495-524 verbatim
variable {m : ℕ} [Fact (1 ≤ m)] [V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 𝚺 m]

lemma finset_comprehension_aux (Γ : Polarity) {P : V → Prop} (hP : Γ-[m]-Predicate P) (a : V) :
  haveI : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := mod_ISigma_of_le (show 1 ≤ m from Fact.out)
  ∃ s < Exp.exp a, ∀ i < a, i ∈ s ↔ P i := by
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := mod_ISigma_of_le (show 1 ≤ m from Fact.out)
  have : ∃ s < Exp.exp a, ∀ i < a, P i → i ∈ s :=
    ⟨under a, pred_lt_self_of_pos (by simp), fun i hi _ ↦ by simpa [mem_under_iff] using hi⟩
  rcases this with ⟨s, hsn, hs⟩
  have : Γ.alt-[m]-Predicate (fun s : V ↦ ∀ i < a, P i → i ∈ s) := by
    apply HierarchySymbol.Definable.ball_blt
    · simp
    apply HierarchySymbol.Definable.imp
    · simpa using HierarchySymbol.Definable.bcomp₁ (by definability)
    · simpa using HierarchySymbol.Definable.bcomp₂ (by definability) (by definability)
  have : ∃ t, (∀ i < a, P i → i ∈ t) ∧ ∀ t' < t, ∃ x < a, P x ∧ x ∉ (t' : V) := by
    simpa using InductionOnHierarchy.least_number Γ.alt m this hs
  rcases this with ⟨t, ht, t_minimal⟩
  have t_le_s : t ≤ s := not_lt.mp (by
    intro lt
    rcases t_minimal s lt with ⟨i, hin, hi, his⟩
    exact his (hs i hin hi))
  have : ∀ i < a, i ∈ t → P i := by
    intro i _ hit
    by_contra Hi
    have : ∃ j < a, P j ∧ (j ∈ t → j = i) := by
      simpa [not_imp_not] using t_minimal (bitRemove i t) (bitRemove_lt_of_mem hit)
    rcases this with ⟨j, hjn, Hj, hm⟩
    rcases hm (ht j hjn Hj); contradiction
  exact ⟨t, lt_of_le_of_lt t_le_s hsn, fun i hi ↦ ⟨this i hi, ht i hi⟩⟩


-- @@ L526-532 verbatim
theorem finset_comprehension {Γ} {P : V → Prop} (hP : Γ-[m]-Predicate P) (a : V) :
    haveI : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := mod_ISigma_of_le (show 1 ≤ m from Fact.out)
    ∃ s < Exp.exp a, ∀ i < a, i ∈ s ↔ P i :=
  match Γ with
  | 𝚺 => finset_comprehension_aux 𝚺 hP a
  | 𝚷 => finset_comprehension_aux 𝚷 hP a
  | 𝚫 => finset_comprehension_aux 𝚺 hP.of_delta a


-- @@ L534-549 verbatim
theorem finset_comprehension_exists_unique {P : V → Prop} (hP : Γ-[m]-Predicate P) (a : V) :
    haveI : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := mod_ISigma_of_le (show 1 ≤ m from Fact.out)
    ∃! s, s < Exp.exp a ∧ ∀ i < a, i ∈ s ↔ P i := by
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := mod_ISigma_of_le (show 1 ≤ m from Fact.out)
  rcases finset_comprehension hP a with ⟨s, hs, Hs⟩
  exact ExistsUnique.intro s ⟨hs, Hs⟩ (by
    intro t ⟨ht, Ht⟩
    apply mem_ext
    intro i
    constructor
    · intro hi
      have hin : i < a := exp_monotone.mp (lt_of_le_of_lt (exp_le_of_mem hi) ht)
      exact (Hs i hin).mpr ((Ht i hin).mp hi)
    · intro hi
      have hin : i < a := exp_monotone.mp (lt_of_le_of_lt (exp_le_of_mem hi) hs)
      exact (Ht i hin).mpr ((Hs i hin).mp hi))


-- @@ L551-551 verbatim
end



-- @@ L554-554 verbatim
section


-- @@ L556-556 verbatim
variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]


-- @@ L558-558 verbatim
instance : Fact (1 ≤ 1) := ⟨by rfl⟩


-- @@ L560-562 verbatim
theorem finset_comprehension₁ {P : V → Prop} (hP : Γ-[1]-Predicate P) (a : V) :
    ∃ s < Exp.exp a, ∀ i < a, i ∈ s ↔ P i :=
  finset_comprehension hP a


-- @@ L564-578 verbatim
theorem finset_comprehension₁! {P : V → Prop} (hP : Γ-[1]-Predicate P) (a : V) :
    ∃! s, s < Exp.exp a ∧ (∀ i < a, i ∈ s ↔ P i) := by
  rcases finset_comprehension₁ hP a with ⟨s, hs, Ha⟩
  exact ExistsUnique.intro s ⟨hs, Ha⟩
    (by
      rintro b ⟨hb, Hb⟩
      apply mem_ext
      intro x
      constructor
      · intro hx
        have : x < a := exp_monotone.mp <| LE.le.trans_lt (exp_le_of_mem hx) hb
        exact (Ha x this).mpr <| (Hb x this).mp hx
      · intro hx
        have : x < a := exp_monotone.mp <| LE.le.trans_lt (exp_le_of_mem hx) hs
        exact (Hb x this).mpr <| (Ha x this).mp hx)


-- @@ L580-588 verbatim
theorem finite_comprehension₁! {P : V → Prop} (hP : Γ-[1]-Predicate P) (fin : ∃ m, ∀ i, P i → i < m)  :
    ∃! s : V, ∀ i, i ∈ s ↔ P i := by
  rcases fin with ⟨m, mh⟩
  rcases finset_comprehension₁ hP m with ⟨s, hs, Hs⟩
  have H : ∀ i, i ∈ s ↔ P i :=
    fun i ↦ ⟨
      fun h ↦ (Hs i (exp_monotone.mp (lt_of_le_of_lt (exp_le_of_mem h) hs))).mp h,
      fun h ↦ (Hs i (mh i h)).mpr h⟩
  exact ExistsUnique.intro s H (fun s' H' ↦ mem_ext <| fun i ↦ by simp [H, H'])


-- @@ L590-590 verbatim
end


-- @@ L592-592 verbatim
end FFL.FirstOrder.Arithmetic
