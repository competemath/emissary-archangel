import Clean.Circuit
import Clean.Gadgets.Xor.ByteXorTable
import Clean.Utils.Primes


-- @@ L5-5 verbatim
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]


-- @@ L7-7 verbatim
namespace Gadgets.And.And8

-- @@ L8-8 verbatim
open Gadgets.Xor (ByteXorTable)

-- @@ L9-9 verbatim
open FieldUtils


-- @@ L11-14 verbatim
structure Inputs (F : Type) where
  x: F
  y: F
deriving ProvableStruct


-- @@ L16-18 verbatim
def Assumptions (input : Inputs (F p)) :=
  let ⟨x, y⟩ := input
  x.val < 256 ∧ y.val < 256


-- @@ L20-22 verbatim
def Spec (input : Inputs (F p)) (z : F p) :=
  let ⟨x, y⟩ := input
  z.val = x.val &&& y.val


-- @@ L24-31 verbatim
def main (input : Var Inputs (F p)) : Circuit (F p) (Expression (F p)) := do
  let and ← witness (input.x.val &&& input.y.val).toField
  -- we prove AND correct using an XOR lookup and the following identity:
  let xor := input.x + input.y - 2*and
  lookup ByteXorTable (input.x, input.y, xor)
  return and

-- AND / XOR identity that justifies the circuit


-- @@ L33-57 verbatim
theorem and_times_two_add_xor {x y : ℕ} (hx : x < 256) (hy : y < 256) : 2 * (x &&& y) + (x ^^^ y) = x + y := by
  -- proof strategy: prove a UInt16 version of the identity using `bv_decide`,
  -- and show that the UInt16 identity is the same as the Nat version since everything is small enough
  let x16 := x.toUInt16
  let y16 := y.toUInt16
  have h_u16 : (2 * (x16 &&& y16) + (x16 ^^^ y16)).toNat = (x16 + y16).toNat := by
    apply congrArg UInt16.toNat
    bv_decide

  have hx16 : x.toUInt16.toNat = x := UInt16.toNat_ofNat_of_lt (by linarith)
  have hy16 : y.toUInt16.toNat = y := UInt16.toNat_ofNat_of_lt (by linarith)

  have h_mod_2_to_16 : (2 * (x &&& y) + (x ^^^ y)) % 2^16 = (x + y) % 2^16 := by
    rw [←hx16, ←hy16]
    simp only [x16, y16] at h_u16
    simpa using h_u16

  have h_and_byte : x &&& y < 256 := Nat.and_lt_two_pow (n:=8) x hy
  have h_xor_byte : x ^^^ y < 256 := Nat.xor_lt_two_pow (n:=8) hx hy
  have h_lhs : 2 * (x &&& y) + (x ^^^ y) < 2^16 := by linarith
  have h_rhs : x + y < 2^16 := by linarith
  rw [Nat.mod_eq_of_lt h_lhs, Nat.mod_eq_of_lt h_rhs] at h_mod_2_to_16
  exact h_mod_2_to_16

-- corollaries that we also need


-- @@ L59-60 verbatim
theorem xor_le_add {x y : ℕ} (hx : x < 256) (hy : y < 256) : x ^^^ y ≤ x + y := by
  rw [←and_times_two_add_xor hx hy]; linarith


-- @@ L62-65 verbatim
theorem two_and_le_add {x y : ℕ} (hx : x < 256) (hy : y < 256) : 2 * (x &&& y) ≤ x + y := by
  rw [←and_times_two_add_xor hx hy]; linarith

-- some helper lemmas about 2

-- @@ L66-66 verbatim
lemma val_two : (2 : F p).val = 2 := val_lt_p 2 (by linarith [p_large_enough.elim])


-- @@ L68-71 verbatim
lemma two_non_zero : (2 : F p) ≠ 0 := by
  apply_fun ZMod.val
  rw [val_two, ZMod.val_zero]
  trivial


-- @@ L73-75 verbatim
@[reducible]
instance elaborated : ElaboratedCircuit (F p) Inputs field main := by
  elaborate_circuit


-- @@ L77-105 expanded
theorem soundness : Soundness (Input := Inputs) (Output := field) (F p) main Assumptions Spec :=
  by
  intro i env ⟨x_var, y_var⟩ ⟨x, y⟩ h_input h_assumptions h_xor
  simp_all only [circuit_norm, main, Assumptions, Spec, ByteXorTable, Inputs.mk.injEq]
  have ⟨hx_byte, hy_byte⟩ := h_assumptions
  set w := env.get i
  set z := x + y - 2 * w
  show w.val = x.val &&& y.val
  have two_and_field : 2 * w = x + y - z := by ring
  have x_y_val : (x + y).val = x.val + y.val := by
    ( intros
      repeat rw [ZMod.val_add]
      repeat rw [ZMod.val_mul]
      repeat rw [val_eq_256]
      try simp only [Nat.add_mod_mod, Nat.mod_add_mod, Nat.mul_mod_mod, Nat.mod_mul_mod]
      rw [Nat.mod_eq_of_lt _]
      repeat linarith [‹Fact (_ > 512)›.elim])
  have z_lt : z.val ≤ (x + y).val := by
    rw [h_xor, x_y_val]
    exact xor_le_add hx_byte hy_byte
  have x_y_z_val : (x + y - z).val = x.val + y.val - z.val := by rw [ZMod.val_sub z_lt, x_y_val]
  have two_and : (2 * w).val = 2 * (x.val &&& y.val) := by
    rw [two_and_field, x_y_z_val, h_xor, ← and_times_two_add_xor hx_byte hy_byte,
      Nat.add_sub_cancel]
  clear two_and_field x_y_val x_y_z_val h_xor z_lt
  have two_mul_val : (2 * w).val = 2 * w.val :=
    FieldUtils.mul_nat_val_of_dvd 2 (by linarith [p_large_enough.elim]) two_and
  rw [two_mul_val, Nat.mul_left_cancel_iff (by linarith)] at two_and
  exact two_and


-- @@ L107-134 expanded
theorem completeness : Completeness (Input := Inputs) (Output := field) (F p) main Assumptions :=
  by
  intro i env ⟨x_var, y_var⟩ h_env ⟨x, y⟩ h_input h_assumptions
  obtain ⟨hx_byte, hy_byte⟩ := h_assumptions
  simp_all only [circuit_norm, main, ByteXorTable, Inputs.mk.injEq]
  set w : F p := ZMod.val x &&& ZMod.val y
  have hw : w = ZMod.val x &&& ZMod.val y := rfl
  have and_byte : x.val &&& y.val < 256 := Nat.and_lt_two_pow (n := 8) x.val hy_byte
  have p_large := p_large_enough.elim
  have and_lt : x.val &&& y.val < p := by linarith
  rw [natToField_eq_natCast and_lt] at hw
  have h_and : w.val = x.val &&& y.val := natToField_eq w hw
  have two_and_val : (2 * w).val = 2 * (x.val &&& y.val) :=
    by
    rw [ZMod.val_mul_of_lt, val_two, h_and]
    rw [val_two]
    linarith
  have x_y_val : (x + y).val = x.val + y.val := by
    ( intros
      repeat rw [ZMod.val_add]
      repeat rw [ZMod.val_mul]
      repeat rw [val_eq_256]
      try simp only [Nat.add_mod_mod, Nat.mod_add_mod, Nat.mul_mod_mod, Nat.mod_mul_mod]
      rw [Nat.mod_eq_of_lt _]
      repeat linarith [‹Fact (_ > 512)›.elim])
  have two_and_lt : (2 * w).val ≤ (x + y).val :=
    by
    rw [two_and_val, x_y_val]
    exact two_and_le_add hx_byte hy_byte
  rw [ZMod.val_sub two_and_lt, x_y_val, two_and_val, ← and_times_two_add_xor hx_byte hy_byte,
    add_comm, Nat.add_sub_cancel]


-- @@ L136-137 verbatim
def circuit : FormalCircuit (F p) Inputs field :=
  { main, elaborated, Assumptions, Spec, soundness, completeness }


-- @@ L139-139 verbatim
end Gadgets.And.And8
