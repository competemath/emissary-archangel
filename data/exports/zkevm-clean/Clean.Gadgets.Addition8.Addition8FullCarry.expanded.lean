import Clean.Circuit
import Clean.Gadgets.ByteLookup
import Clean.Gadgets.Boolean
import Clean.Gadgets.Addition8.Theorems


-- @@ L6-6 verbatim
namespace Gadgets.Addition8FullCarry

-- @@ L7-7 verbatim
variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]


-- @@ L9-9 verbatim
open ByteUtils (mod256)


-- @@ L11-15 verbatim
structure Inputs (F : Type) where
  x: F
  y: F
  carryIn: F
deriving ProvableStruct


-- @@ L17-20 verbatim
structure Outputs (F : Type) where
  z: F
  carryOut: F
deriving ProvableStruct


-- @@ L22-33 verbatim
def main (input : Var Inputs (F p)) : Circuit (F p) (Var Outputs (F p)) := do
  -- witness the result
  let z ← witness ((input.x + input.y + input.carryIn).val % 256).toField
  lookup ByteTable z

  -- witness the output carry
  let carryOut ← witness ((input.x + input.y + input.carryIn).val / 256).toField
  assertBool carryOut

  assertZero (input.x + input.y + input.carryIn - z - carryOut * 256)

  return { z, carryOut }


-- @@ L35-37 verbatim
def Assumptions (input : Inputs (F p)) :=
  let ⟨x, y, carryIn⟩ := input
  x.val < 256 ∧ y.val < 256 ∧ IsBool carryIn


-- @@ L39-42 verbatim
def Spec (input : Inputs (F p)) (out : Outputs (F p)) :=
  let ⟨x, y, carryIn⟩ := input
  out.z.val = (x.val + y.val + carryIn.val) % 256 ∧
  out.carryOut.val = (x.val + y.val + carryIn.val) / 256


-- @@ L44-122 expanded
/-- Compute the 8-bit addition of two numbers with a carry-in bit.
  Returns the sum and the output carry bit.
-/
def circuit : FormalCircuit (F p) Inputs Outputs
    where
  main
  Assumptions
  Spec
  soundness := by
    -- introductions
    
    rintro i0 env ⟨x_var, y_var, carry_in_var⟩ ⟨x, y, carry_in⟩ h_inputs h_assumptions h_holds
    replace h_inputs : x_var.eval env = x ∧ y_var.eval env = y ∧ carry_in_var.eval env = carry_in :=
      by simpa [circuit_norm] using h_inputs
    simp_all only [circuit_norm, Spec, Assumptions, main, ByteTable]
    set z := env.get i0
    set carry_out := env.get (i0 + 1)
    obtain ⟨h_byte, h_bool_carry, h_add⟩ := h_holds
    guard_hyp h_assumptions : x.val < 256 ∧ y.val < 256 ∧ IsBool carry_in
    guard_hyp h_byte : z.val < 256
    guard_hyp h_add : x + y + carry_in - z - carry_out * 256 = 0
    show
      z.val = (x.val + y.val + carry_in.val) % 256 ∧
        carry_out.val = (x.val + y.val + carry_in.val) / 256
    have ⟨as_x, as_y, as_carry_in⟩ := h_assumptions
    rw [sub_eq_add_neg, sub_eq_add_neg] at h_add
    apply
      Addition8.Theorems.soundness x y z carry_in carry_out as_x as_y h_byte as_carry_in
        h_bool_carry h_add
  completeness := by
    -- introductions
    
    rintro i0 env ⟨x_var, y_var, carry_in_var⟩ h_env ⟨x, y, carry_in⟩ h_inputs h_assumptions
    replace h_inputs : x_var.eval env = x ∧ y_var.eval env = y ∧ carry_in_var.eval env = carry_in :=
      by simpa [circuit_norm] using h_inputs
    obtain ⟨as_x, as_y, as_carry_in⟩ := h_assumptions
    have carry_in_bound := IsBool.val_lt_two as_carry_in
    have sum_val : (x + y + carry_in).val = x.val + y.val + carry_in.val := by
      ( intros
        repeat rw [ZMod.val_add]
        repeat rw [ZMod.val_mul]
        repeat rw [val_eq_256]
        try simp only [Nat.add_mod_mod, Nat.mod_add_mod, Nat.mul_mod_mod, Nat.mod_mul_mod]
        rw [Nat.mod_eq_of_lt _]
        repeat linarith [‹Fact (_ > 512)›.elim])
    have sum_lt : (x + y + carry_in).val < 2 ^ 64 := by rw [sum_val];
      omega
        -- simplify assumptions and goal
        
    simp only [circuit_norm, h_inputs, main, ByteTable] at *
    obtain ⟨hz, hcarry_out⟩ := h_env
    set z := env.get i0
    set carry_out := env.get (i0 + 1)
    let goal_byte := z.val < 256
    let goal_bool := IsBool carry_out
    let goal_add := x + y + carry_in - z - carry_out * 256 = 0
    show goal_byte ∧ goal_bool ∧ goal_add
    change z = mod256 (x + y + carry_in) at hz
    have completeness1 : z.val < 256 :=
      by
      rw [hz, ByteUtils.mod256, FieldUtils.mod_val]
      exact Nat.mod_lt _ (by norm_num)
    have completeness2 : IsBool carry_out :=
      by
      rw [hcarry_out]
      apply Addition8.Theorems.completeness_bool
      repeat assumption
    have completeness3 : x + y + carry_in - z - carry_out * 256 = 0 :=
      by
      rw [hz, hcarry_out, sub_eq_add_neg, sub_eq_add_neg]
      apply Addition8.Theorems.completeness_add
      repeat assumption
    exact ⟨completeness1, completeness2, completeness3⟩


-- @@ L124-132 verbatim
def lookupCircuit : LookupCircuit (F p) Inputs Outputs := {
  circuit with
  name := "Addition8FullCarry"

  computableWitnesses n input := by
    obtain ⟨x, y, carryIn⟩ := input
    simp_all +instances only [circuit_norm, circuit, main,
      FormalAssertion.toSubcircuit, Operations.forAllFlat, FlatOperation.forAll, Inputs.mk.injEq]
}


-- @@ L134-134 verbatim
end Gadgets.Addition8FullCarry
