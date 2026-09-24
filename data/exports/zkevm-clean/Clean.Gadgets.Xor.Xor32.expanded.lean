import Clean.Circuit
import Clean.Utils.Primes
import Clean.Utils.Field
import Clean.Types.U32
import Clean.Gadgets.Xor.ByteXorTable


-- @@ L7-7 verbatim
section

-- @@ L8-8 verbatim
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]


-- @@ L10-10 verbatim
namespace Gadgets.Xor32

-- @@ L11-11 verbatim
open Gadgets.Xor


-- @@ L13-16 verbatim
structure Inputs (F : Type) where
  x: U32 F
  y: U32 F
deriving ProvableStruct


-- @@ L18-30 verbatim
def main (input : Var Inputs (F p)) : Circuit (F p) (Var U32 (F p))  := do
  let z ← witness <|
    let z0 := (input.x.x0.val ^^^ input.y.x0.val).toField
    let z1 := (input.x.x1.val ^^^ input.y.x1.val).toField
    let z2 := (input.x.x2.val ^^^ input.y.x2.val).toField
    let z3 := (input.x.x3.val ^^^ input.y.x3.val).toField
    U32.mk z0 z1 z2 z3

  lookup ByteXorTable (input.x.x0, input.y.x0, z.x0)
  lookup ByteXorTable (input.x.x1, input.y.x1, z.x1)
  lookup ByteXorTable (input.x.x2, input.y.x2, z.x2)
  lookup ByteXorTable (input.x.x3, input.y.x3, z.x3)
  return z


-- @@ L32-34 verbatim
def Assumptions (input : Inputs (F p)) :=
  let ⟨x, y⟩ := input
  x.Normalized ∧ y.Normalized


-- @@ L36-38 verbatim
def Spec (input : Inputs (F p)) (z : U32 (F p)) :=
  let ⟨x, y⟩ := input
  z.value = x.value ^^^ y.value ∧ z.Normalized


-- @@ L40-41 verbatim
instance elaborated : ElaboratedCircuit (F p) Inputs U32 main := by
  elaborate_circuit


-- @@ L43-62 verbatim
omit [Fact (Nat.Prime p)] p_large_enough in
theorem soundness_to_u32 {x y z : U32 (F p)}
  (x_norm : x.Normalized) (y_norm : y.Normalized)
  (h_eq :
    z.x0.val = x.x0.val ^^^ y.x0.val ∧
    z.x1.val = x.x1.val ^^^ y.x1.val ∧
    z.x2.val = x.x2.val ^^^ y.x2.val ∧
    z.x3.val = x.x3.val ^^^ y.x3.val) : Spec { x, y } z := by
  simp only [Spec]
  have ⟨ hx0, hx1, hx2, hx3 ⟩ := x_norm
  have ⟨ hy0, hy1, hy2, hy3 ⟩ := y_norm

  have z_norm : z.Normalized := by
    simp only [U32.Normalized, h_eq]
    exact ⟨ Nat.xor_lt_two_pow (n:=8) hx0 hy0, Nat.xor_lt_two_pow (n:=8) hx1 hy1,
      Nat.xor_lt_two_pow (n:=8) hx2 hy2, Nat.xor_lt_two_pow (n:=8) hx3 hy3 ⟩

  suffices z.value = x.value ^^^ y.value from ⟨ this, z_norm ⟩
  simp only [U32.value_xor_horner, x_norm, y_norm, z_norm, h_eq, xor_mul_two_pow]
  ac_rfl


-- @@ L64-74 verbatim
theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [ByteXorTable]
  rcases input_x with ⟨ x0, x1, x2, x3 ⟩
  rcases input_y with ⟨ y0, y1, y2, y3 ⟩
  simp only [circuit_norm, explicit_provable_type, U32.mk.injEq] at h_input
  simp only [circuit_norm] at h_assumptions
  obtain ⟨ x_norm, y_norm ⟩ := h_assumptions
  simp only [h_input, circuit_norm, explicit_provable_type] at h_holds
  apply soundness_to_u32 (by simp [circuit_norm, x_norm]) (by simp [circuit_norm, y_norm])
  simp only [circuit_norm, explicit_provable_type]
  simp [h_holds]


-- @@ L76-80 verbatim
omit [Fact (Nat.Prime p)] in
lemma xor_val {x y : F p} (hx : x.val < 256) (hy : y.val < 256) :
    (x.val ^^^ y.val) % p = x.val ^^^ y.val := by
  have h_byte : x.val ^^^ y.val < 256 := Nat.xor_lt_two_pow (n:=8) hx hy
  exact Nat.mod_eq_of_lt (by linarith [p_large_enough.elim])


-- @@ L82-95 verbatim
theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [ByteXorTable]
  rcases input_x with ⟨ x0, x1, x2, x3 ⟩
  rcases input_y with ⟨ y0, y1, y2, y3 ⟩
  simp only [circuit_norm, explicit_provable_type, U32.mk.injEq] at h_input

  simp only [circuit_norm, U32.Normalized] at h_assumptions
  obtain ⟨ x_bytes, y_bytes ⟩ := h_assumptions
  obtain ⟨ x0_byte, x1_byte, x2_byte, x3_byte ⟩ := x_bytes
  obtain ⟨ y0_byte, y1_byte, y2_byte, y3_byte ⟩ := y_bytes

  simp only [h_input, circuit_norm] at h_env ⊢
  simp only [circuit_norm, explicit_provable_type, U32.mk.injEq] at h_env ⊢
  simp_all [circuit_norm, xor_val]


-- @@ L97-103 verbatim
def circuit : FormalCircuit (F p) Inputs U32 where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness

-- @@ L104-104 verbatim
end Gadgets.Xor32
