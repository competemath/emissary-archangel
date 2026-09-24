import Clean.Circuit.Basic
import Clean.Utils.Field
import Clean.Utils.Tactics.CircuitProofStart
import Mathlib.Data.Nat.Bitwise


-- @@ L6-7 verbatim
/-- A predicate stating that an element is boolean (0 or 1) for any type with 0 and 1 -/
def IsBool {α : Type*} [Zero α] [One α] (x : α) : Prop := x = 0 ∨ x = 1


-- @@ L9-11 verbatim
/-- IsBool is decidable for types with decidable equality -/
instance {α : Type*} [Zero α] [One α] [DecidableEq α] {x : α} : Decidable (IsBool x) :=
  inferInstanceAs (Decidable (x = 0 ∨ x = 1))


-- @@ L13-13 verbatim
namespace IsBool


-- @@ L15-16 verbatim
@[circuit_norm]
theorem zero {α : Type*} [Zero α] [One α] : IsBool (0 : α) := Or.inl rfl


-- @@ L18-19 verbatim
@[circuit_norm]
theorem one {α : Type*} [Zero α] [One α] : IsBool (1 : α) := Or.inr rfl


-- @@ L21-26 verbatim
/-- If x is boolean in a type with a < relation, then x < 2 (when 2 exists) -/
theorem lt_two {α : Type*} [Zero α] [One α] [Preorder α] [OfNat α 2]
    {x : α} (h : IsBool x) (h0 : (0 : α) < 2) (h1 : (1 : α) < 2) : x < 2 := by
  rcases h with h0' | h1'
  · rw [h0']; exact h0
  · rw [h1']; exact h1


-- @@ L28-29 verbatim
/-- x is boolean iff x * (x - 1) = 0 -/
@[grind =]

-- @@ L30-32 verbatim
theorem iff_mul_sub_one {F : Type} [FiniteField F] {x : F} :
    IsBool x ↔ x * (x - 1) = 0 := by
  rw [mul_eq_zero, sub_eq_zero, IsBool]


-- @@ L34-46 verbatim
/-- If a natural number is less than 2, then it is boolean (0 or 1) -/
theorem nat_of_lt_two {x : ℕ} (h : x < 2) : IsBool x := by
  cases x with
  | zero => exact IsBool.zero
  | succ n =>
    cases n with
    | zero => exact IsBool.one
    | succ m =>
      -- This case is impossible since x = m + 2 ≥ 2
      exfalso
      have : m + 2 ≥ 2 := by omega
      have : m + 2 < 2 := h
      omega


-- @@ L48-63 verbatim
/-- If l is boolean, then l AND r is boolean -/
theorem land_inherit_left (l r : ℕ) (h : IsBool l) : IsBool (l &&& r) := by
  rcases h with h_l0 | h_l1
  · -- Case: l = 0
    left
    rw [h_l0]
    simp only [HAnd.hAnd, AndOp.and]
    have : (0 : ℕ).land r = 0 := by
      unfold Nat.land
      simp
    exact this
  · -- Case: l = 1
    subst h_l1
    simp only [Nat.one_and_eq_mod_two]
    apply nat_of_lt_two
    omega


-- @@ L65-69 verbatim
/-- For field elements, if x is boolean then x.val < 2 -/
theorem val_lt_two {p : ℕ} [Fact p.Prime] {x : F p} (h : IsBool x) : x.val < 2 := by
  rcases h with h0 | h1
  · rw [h0]; simp only [ZMod.val_zero]; norm_num
  · rw [h1]; simp only [ZMod.val_one, Nat.one_lt_ofNat]


-- @@ L71-76 verbatim
/-- If x and y are boolean, then x AND y is boolean -/
theorem and_is_bool {α : Type*} [MulZeroOneClass α] {x y : α} (hx : IsBool x) (hy : IsBool y) :
    IsBool (x * y) := by
  rcases hx with hx0 | hx1
  · simp [hx0, zero]
  · simp [hx1, one_mul, hy]


-- @@ L78-85 verbatim
/-- If x and y are boolean, then x OR y is boolean -/
theorem or_is_bool {α : Type*} [Ring α] {x y : α} (hx : IsBool x) (hy : IsBool y) :
    IsBool (x - x*y + y) := by
  rcases hx with hx0 | hx1
  · simp [hx0, zero_add, zero_mul, hy]
  · rcases hy with hy0 | hy1
    · simp [hx1, hy0, mul_zero, add_zero, sub_zero, one]
    · simp [hx1, hy1, mul_one, sub_self, one]


-- @@ L87-94 verbatim
/-- If x is boolean, then NOT x is boolean -/
theorem not_is_bool {α : Type*} [Ring α] {x : α} (hx : IsBool x) :
    IsBool (1 + x - 2*x) := by
  rcases hx with hx0 | hx1
  · simp [hx0, add_zero, sub_zero, one]
  · simp only [hx1]
    norm_num
    exact zero


-- @@ L96-105 verbatim
/-- If x and y are boolean, then x XOR y is boolean -/
theorem xor_is_bool {α : Type*} [Ring α] {x y : α} (hx : IsBool x) (hy : IsBool y) :
    IsBool (x + y - 2*x*y) := by
  rcases hx with hx0 | hx1
  · simp [hx0, zero_add, zero_mul, mul_zero, sub_zero, hy]
  · rcases hy with hy0 | hy1
    · simp [hx1, hy0, add_zero, mul_zero, sub_zero, one]
    · simp only [hx1, hy1, mul_one]
      norm_num
      exact zero


-- @@ L107-114 verbatim
/-- If x and y are boolean, then NAND(x,y) is boolean -/
theorem nand_is_bool {α : Type*} [Ring α] {x y : α} (hx : IsBool x) (hy : IsBool y) :
    IsBool (1 - x * y) := by
  rcases hx with hx0 | hx1
  · simp [hx0, sub_zero, one]
  · rcases hy with hy0 | hy1
    · simp [hx1, hy0, sub_zero, one]
    · simp [hx1, hy1, sub_self, zero]


-- @@ L116-126 verbatim
/-- If x and y are boolean, then NOR(x,y) is boolean -/
theorem nor_is_bool {α : Type*} [Ring α] {x y : α} (hx : IsBool x) (hy : IsBool y) :
    IsBool (x * y + 1 - x - y) := by
  rcases hx with hx0 | hx1
  · rcases hy with hy0 | hy1
    · simp [hx0, hy0, zero_add, sub_zero, one]
    · simp [hx0, hy1, zero_add, sub_self, zero]
  · rcases hy with hy0 | hy1
    · simp [hx1, hy0, mul_zero, sub_self, zero]
    · simp [hx1, hy1]
      exact zero


-- @@ L128-132 verbatim
/-- If a is boolean (0 or 1), then a &&& 1 = a -/
theorem land_one_of_IsBool (a : ℕ) (h : IsBool a) : a &&& 1 = a := by
  rcases h with h0 | h1
  · rw [h0]; norm_num
  · rw [h1]; norm_num


-- @@ L134-137 verbatim
/-- If a is boolean (0 or 1), then 1 &&& a = a -/
theorem one_land_of_IsBool (a : ℕ) (h : IsBool a) : 1 &&& a = a := by
  rw [Nat.land_comm]
  exact land_one_of_IsBool a h


-- @@ L139-143 verbatim
/-- If x is boolean in F p, then x.val is boolean as a natural number -/
theorem val_of_IsBool {p : ℕ} [Fact p.Prime] {x : F p} (h : IsBool x) : IsBool x.val := by
  rcases h with h0 | h1
  · rw [h0]; simp only [ZMod.val_zero]; exact zero
  · rw [h1]; simp only [ZMod.val_one]; exact one


-- @@ L145-145 verbatim
section BinaryOps

-- @@ L146-146 verbatim
variable {p : ℕ} [Fact p.Prime]


-- @@ L148-151 verbatim
/-- For boolean field elements, XOR operation matches bitwise XOR of values -/
theorem xor_eq_val_xor {a b : F p} (ha : IsBool a) (hb : IsBool b) :
    (a + b - 2*a*b).val = a.val ^^^ b.val := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb]; norm_num


-- @@ L153-156 verbatim
/-- For boolean field elements, AND operation matches bitwise AND of values -/
theorem and_eq_val_and {a b : F p} (ha : IsBool a) (hb : IsBool b) :
    (a * b).val = a.val &&& b.val := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb]


-- @@ L158-161 verbatim
/-- For boolean field elements, OR operation matches bitwise OR of values -/
theorem or_eq_val_or {a b : F p} (ha : IsBool a) (hb : IsBool b) :
    (a - a * b + b).val = a.val ||| b.val := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb]


-- @@ L163-166 verbatim
/-- For boolean field elements, NAND operation matches 1 - AND of values -/
theorem nand_eq_val_nand {a b : F p} (ha : IsBool a) (hb : IsBool b) :
    (1 - a * b).val = 1 - (a.val &&& b.val) := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb, ZMod.val_one]


-- @@ L168-171 verbatim
/-- For boolean field elements, NOR operation matches 1 - OR of values -/
theorem nor_eq_val_nor {a b : F p} (ha : IsBool a) (hb : IsBool b) :
    (a * b + 1 - a - b).val = 1 - (a.val ||| b.val) := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb, ZMod.val_one]


-- @@ L173-176 verbatim
/-- For boolean field elements, NOT operation matches 1 - value -/
theorem not_eq_val_not {a : F p} (ha : IsBool a) :
    (1 - 2*a + a).val = 1 - a.val := by
  rcases ha with ha | ha <;> rw [ha] <;> ring_nf <;> simp [ZMod.val_one]


-- @@ L178-178 verbatim
end BinaryOps

-- @@ L179-179 verbatim
end IsBool


-- @@ L181-181 verbatim
section

-- @@ L182-182 verbatim
variable {p : ℕ} [Fact p.Prime]


-- @@ L184-192 verbatim
/--
Asserts that x is boolean by adding the constraint x * (x - 1) = 0
-/
@[circuit_norm]
def assertBool : FormalAssertion (F p) field where
  main x := assertZero (x * (x - 1))
  Spec x := IsBool x
  soundness := by circuit_proof_all
  completeness := by circuit_proof_all


-- @@ L194-195 verbatim
inductive Boolean (F : Type) where
  | private mk : Variable F → Boolean F


-- @@ L197-197 verbatim
namespace Boolean

-- @@ L198-201 verbatim
def witness (e : Witgen.FExpr (F p)) := do
  let x ← witnessVar (.ofFExpr e)
  assertZero (var x * (var x - 1))
  return Boolean.mk x


-- @@ L203-203 verbatim
def var (b : Boolean (F p)) := Expression.var b.1


-- @@ L205-206 verbatim
instance : Coe (Boolean (F p)) (Expression (F p)) where
  coe x := x.var

-- @@ L207-207 verbatim
end Boolean
