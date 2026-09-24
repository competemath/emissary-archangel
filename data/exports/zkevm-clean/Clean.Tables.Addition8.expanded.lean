import Clean.Utils.Vector
import Clean.Circuit.Basic
import Clean.Table.Basic
import Clean.Gadgets.Addition8.Addition8


-- @@ L6-6 verbatim
namespace Tables.Addition8

-- @@ L7-7 verbatim
open Gadgets

-- @@ L8-8 verbatim
variable {p : ℕ} [Fact p.Prime]

-- @@ L9-9 verbatim
variable [p_large_enough: Fact (p > 512)]


-- @@ L11-14 verbatim
structure RowType (F : Type) where
  x: F
  y: F
  z: F


-- @@ L16-21 verbatim
instance : ProvableType RowType where
  size := 3
  toElements x := #v[x.x, x.y, x.z]
  fromElements v :=
    let ⟨ .mk [x, y, z], _ ⟩ := v
    ⟨ x, y, z ⟩


-- @@ L23-28 verbatim
def add8Inline : SingleRowConstraint RowType (F p) := do
  let row ← TableConstraint.getCurrRow
  lookup ByteTable row.x
  lookup ByteTable row.y
  let z ← Gadgets.Addition8.circuit { x := row.x, y := row.y }
  assign (.curr 2) z


-- @@ L30-32 verbatim
def add8Table : List (TableOperation RowType (F p)) := [
  .everyRow add8Inline
]


-- @@ L34-48 verbatim
def Spec_add8 {N : ℕ} (trace : TraceOfLength (F p) RowType N) : Prop :=
  trace.ForAllRowsOfTrace (fun row => (row.z.val = (row.x.val + row.y.val) % 256))

lemma add8_vars (row : Row (F p) RowType) (aux_env : ProverEnvironment (F p)) :
    let env := add8Inline.windowEnv ⟨<+> +> row, rfl⟩ aux_env;
    env.get 0 = row.x ∧
    env.get 1 = row.y ∧
    env.get 3 = row.z := by
  intro env
  simp [env, windowEnv, TableConstraint.finalAssignment, add8Inline, table_assignment_norm,
    circuit_norm, Gadgets.Addition8.circuit, Vector.mapFinRange_zero, Vector.mapFinRange_succ,
    Vector.mapRange_zero, Vector.mapRange_succ, Vector.getElem_mk,
    Pure.pure]
  change row.x = row.x ∧ row.y = row.y
  simp


-- @@ L50-85 verbatim
def formalAdd8Table : FormalTable (F p) RowType := {
  constraints := add8Table,
  Spec trace _ := Spec_add8 trace,
  soundness := by
    intro N trace envs _
    simp [table_norm, add8Table, Spec_add8]
    induction trace.val with
    | empty => simp [table_norm]
    | cons rest row ih =>
        -- get rid of induction hypothesis
        simp only [table_norm]
        rintro ⟨ h_holds, h_rest ⟩
        suffices h' : row.z.val = (row.x.val + row.y.val) % 256 from ⟨ h', ih h_rest ⟩
        clear ih h_rest

        -- simplify constraints

        -- first, abstract away `env` to avoid blow-up of expression size
        let env := add8Inline.windowEnv ⟨<+> +> row, rfl⟩ (envs.toEnvironment 0 rest.len)
        change ConstraintsHold.Soundness env.toEnvironment _ at h_holds
        have ⟨ h_x_env, h_y_env, h_z_env ⟩ := add8_vars row (envs.toEnvironment 0 rest.len)

        -- this is the slowest step, but still ok
        simp [table_norm, circuit_norm, varFromOffset, Vector.mapRange,
          add8Inline, Gadgets.Addition8.circuit, ByteTable
        ] at h_holds

        change _ ∧ _ ∧ (_ → _) at h_holds

        -- now we prove a local property about the current row, from the constraints
        obtain ⟨ lookup_x, lookup_y, h_add⟩ := h_holds
        rw [h_x_env] at lookup_x
        rw [h_y_env] at lookup_y
        rw [h_z_env, h_x_env, h_y_env] at h_add
        exact h_add lookup_x lookup_y
}


-- @@ L87-87 verbatim
end Tables.Addition8
