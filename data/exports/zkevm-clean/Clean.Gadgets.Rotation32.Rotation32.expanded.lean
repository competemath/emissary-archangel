import Clean.Types.U32
import Clean.Circuit.Subcircuit
import Clean.Utils.Rotation
import Clean.Gadgets.Rotation32.Rotation32Bytes
import Clean.Gadgets.Rotation32.Rotation32Bits
import Clean.Circuit.Provable


-- @@ L8-8 verbatim
namespace Gadgets.Rotation32

-- @@ L9-9 verbatim
variable {p : ℕ} [Fact p.Prime]

-- @@ L10-10 verbatim
variable [p_large_enough: Fact (p > 2^16 + 2^8)]


-- @@ L12-14 verbatim
instance : Fact (p > 512) := by
  constructor
  linarith [p_large_enough.elim]


-- @@ L16-16 verbatim
open Utils.Rotation (rotRight32_composition)


-- @@ L18-27 verbatim
/--
  Rotate the 32-bit integer by `offset` bits
-/
def main (offset : Fin 32) (x : Var U32 (F p)) : Circuit (F p) (Var U32 (F p)) := do
  let byte_offset : Fin 4 := ⟨ offset.val / 8, by omega ⟩
  let bit_offset : Fin 8 := ⟨ offset.val % 8, by omega ⟩

  -- rotation is performed by combining a bit and a byte rotation
  let byte_rotated ← Rotation32Bytes.circuit byte_offset x
  Rotation32Bits.circuit bit_offset byte_rotated


-- @@ L29-29 verbatim
def Assumptions (input : U32 (F p)) := input.Normalized


-- @@ L31-33 verbatim
def Spec (offset : Fin 32) (x : U32 (F p)) (y : U32 (F p)) :=
  y.value = rotRight32 x.value offset.val
  ∧ y.Normalized


-- @@ L35-36 verbatim
def output (offset : Fin 32) (i0 : ℕ) : U32 (Expression (F p)) :=
  Rotation32Bits.output ⟨ offset.val % 8, by omega ⟩ i0


-- @@ L38-42 verbatim
@[reducible] instance elaborated (off : Fin 32) : ElaboratedCircuit (F p) U32 U32 (main off) := by
  elaborate_circuit_with {
    localLength _ := 8
    output _inputs i0 := output off i0
  }


-- @@ L44-61 verbatim
theorem soundness (offset : Fin 32) : Soundness (F p) (main offset) Assumptions (Spec offset) := by
  circuit_proof_start [Rotation32Bits.circuit, Rotation32Bits.elaborated,
    Rotation32Bytes.circuit, Rotation32Bytes.elaborated]

  -- abstract away intermediate U32
  let byte_offset : Fin 4 := ⟨ offset.val / 8, by omega ⟩
  let bit_offset : Fin 8 := ⟨ offset.val % 8, by omega ⟩
  set byte_rotated := eval env
    ((Rotation32Bytes.circuit byte_offset).output input_var i₀)

  simp only [Rotation32Bytes.Assumptions, Rotation32Bytes.Spec,
    Rotation32Bits.Assumptions, Rotation32Bits.Spec, output] at h_holds ⊢
  set y : U32 (F p) := eval env (Rotation32Bits.output (p:=p) ⟨ offset.val % 8, by omega ⟩ i₀)
  simp_all only [forall_const, and_true]

  -- reason about rotation
  rw [rotRight32_composition _ _ _ (U32.value_lt_of_normalized h_assumptions),
    Nat.div_add_mod']


-- @@ L63-66 verbatim
theorem completeness (offset : Fin 32) : Completeness (F p) (main offset) Assumptions := by
  circuit_proof_all [Rotation32Bits.circuit, Rotation32Bits.elaborated,
    Rotation32Bits.Assumptions, Rotation32Bytes.circuit,
    Rotation32Bytes.Assumptions, Rotation32Bytes.Spec]


-- @@ L68-74 verbatim
def circuit (offset : Fin 32) : FormalCircuit (F p) U32 U32 where
  main := main offset
  elaborated := elaborated offset
  Assumptions
  Spec := Spec offset
  soundness := soundness offset
  completeness := completeness offset


-- @@ L76-76 verbatim
end Gadgets.Rotation32
