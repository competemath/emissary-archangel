import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Clean.Utils.Primes
import Clean.Utils.Vector
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Expression
import Clean.Circuit.Provable
import Clean.Utils.Field
import Clean.Table.SimpTable


-- @@ L12-16 verbatim
/--
  A row is StructuredElement that contains field elements.
-/
@[reducible]
def Row (F : Type) (S : Type → Type) [ProvableType S] := S F


-- @@ L18-18 verbatim
variable {F : Type} {S : Type → Type} [ProvableType S]


-- @@ L20-22 verbatim
@[table_norm, table_assignment_norm]
def Row.get (row : Row F S) (i : Fin (size S)) : F :=
  (toElements row)[i.val]


-- @@ L24-32 verbatim
/--
  A trace is an inductive list of rows. It can be viewed as a structured
  environment that maps cells to field elements.
-/
inductive Trace (F : Type) (S : Type → Type) [ProvableType S] where
  /-- An empty trace -/
  | empty : Trace F S
  /-- Add a row to the end of the trace -/
  | cons (rest : Trace F S) (row : Row F S) : Trace F S


-- @@ L34-34 verbatim
@[inherit_doc] notation:67 "<+>" => Trace.empty

-- @@ L35-35 verbatim
@[inherit_doc] infixl:67 " +> " => Trace.cons


-- @@ L37-37 verbatim
namespace Trace

-- @@ L38-44 expanded
/-- The length of a trace is the number of rows it contains.
-/
@[table_norm, table_assignment_norm]
def len : Trace F S → ℕ
  | Trace.empty => 0
  | Trace.cons rest _ => rest.len + 1


-- @@ L46-53 expanded
/-- Get the row at a specific index in the trace, starting from the bottom of the trace
-/
@[table_assignment_norm]
def getLeFromBottom : (trace : Trace F S) → (row : Fin trace.len) → (col : Fin (size S)) → F
  | Trace.cons _ currRow, ⟨0, _⟩, j => currRow.get j
  | Trace.cons rest _, ⟨i + 1, h⟩, j => getLeFromBottom rest ⟨i, Nat.le_of_succ_le_succ h⟩ j


-- @@ L55-58 expanded
@[table_norm]
def lastRow : (trace : Trace F S) → (hlen : trace.len > 0) → S F
  | Trace.empty, h => nomatch h
  | Trace.cons _ row, _ => row


-- @@ L60-62 expanded
def tail : Trace F S → Trace F S
  | Trace.empty => Trace.empty
  | Trace.cons rest _ => rest


-- @@ L64-66 expanded
lemma tail_len : (trace : Trace F S) → trace.tail.len = trace.len - 1
  | Trace.empty => rfl
  | Trace.cons rest _ => by rw [tail, len, Nat.succ_sub_one]


-- @@ L68-76 expanded
@[table_norm]
def ForAllRowsOfTraceWithIndex (trace : Trace F S) (prop : Row F S → ℕ → Prop) : Prop :=
  inner trace prop
where@[table_norm] inner : Trace F S → (Row F S → ℕ → Prop) → Prop
    | Trace.empty, _ => true
    | Trace.cons rest row, prop => (prop row rest.len) ∧ inner rest prop


-- @@ L78-81 expanded
/-- variant where the condition receives the entire previous trace instead of just the length -/
def ForAllRowsWithPrevious : Trace F S → (Row F S → Trace F S → Prop) → Prop
  | Trace.empty, _ => true
  | Trace.cons rest row, prop => (prop row rest) ∧ ForAllRowsWithPrevious rest prop


-- @@ L83-85 expanded
def toList : Trace F S → List (Row F S)
  | Trace.empty => []
  | Trace.cons rest row => rest.toList.concat row


-- @@ L87-91 expanded
lemma toList_length : (trace : Trace F S) → trace.toList.length = trace.len
  | Trace.empty => rfl
  | Trace.cons rest _ => by
    rw [toList, List.length_concat, len, Nat.succ_inj]
    exact rest.toList_length


-- @@ L93-93 verbatim
end Trace


-- @@ L95-99 verbatim
/--
  A trace of length N is a trace with exactly N rows.
-/
def TraceOfLength (F : Type) (S : Type → Type) [ProvableType S] (N : ℕ) : Type :=
  { env : Trace F S // env.len = N }


-- @@ L101-101 verbatim
namespace TraceOfLength


-- @@ L103-112 verbatim
/--
  Get the row at a specific index in the trace, starting from the top
-/
@[table_assignment_norm]
def get {M : ℕ} :
    (env : TraceOfLength F S M) → (i : Fin M) → (j : Fin (size S)) → F
  | ⟨env, h⟩, i, j => env.getLeFromBottom ⟨
      M - 1 - i,
      by rw [h]; apply Nat.sub_one_sub_lt_of_lt; exact i.is_lt
    ⟩ j


-- @@ L114-116 verbatim
@[table_norm]
def lastRow {M : ℕ+} (trace : TraceOfLength F S M) : S F :=
  trace.val.lastRow (by rw [trace.property]; exact M.pos)


-- @@ L118-119 verbatim
def tail {M : ℕ} (trace : TraceOfLength F S M) : TraceOfLength F S (M - 1) :=
  ⟨ trace.val.tail, by rw [trace.val.tail_len, trace.prop] ⟩


-- @@ L121-132 expanded
/-- Apply a proposition to every row in the trace
-/
@[table_norm]
def ForAllRowsOfTrace {N : ℕ} (trace : TraceOfLength F S N) (prop : Row F S → Prop) : Prop :=
  inner trace.val prop
where@[table_norm] inner : Trace F S → (Row F S → Prop) → Prop
    | Trace.empty, _ => true
    | Trace.cons rest row, prop => prop row ∧ inner rest prop


-- @@ L134-145 expanded
/-- Apply a proposition to every row in the trace except the last one
-/
@[table_norm]
def ForAllRowsOfTraceExceptLast {N : ℕ} (trace : TraceOfLength F S N) (prop : Row F S → Prop) :
    Prop :=
  inner trace.val prop
where inner : Trace F S → (Row F S → Prop) → Prop
    | Trace.empty, _ => true
    | Trace.cons Trace.empty _, _ => true
    | Trace.cons (Trace.cons rest curr) _, prop => prop curr ∧ inner (Trace.cons rest curr) prop


-- @@ L147-153 verbatim
/--
  Apply a proposition, which could be dependent on the row index, to every row of the trace
-/
@[table_norm]
def ForAllRowsOfTraceWithIndex {N : ℕ}
    (trace : TraceOfLength F S N) (prop : Row F S → ℕ → Prop) : Prop :=
  trace.val.ForAllRowsOfTraceWithIndex prop


-- @@ L155-157 verbatim
def ForAllRowsWithPrevious {N : ℕ}
    (trace : TraceOfLength F S N) (prop : Row F S → (i : ℕ) → TraceOfLength F S i → Prop) : Prop :=
  trace.val.ForAllRowsWithPrevious fun row rest => prop row rest.len ⟨ rest, rfl ⟩


-- @@ L159-160 verbatim
def toList {N : ℕ} (trace : TraceOfLength F S N) : List.Vector (Row F S) N :=
  ⟨ trace.val.toList, by rw [trace.val.toList_length, trace.prop] ⟩


-- @@ L162-169 expanded
def take : {N : ℕ} → TraceOfLength F S N → (i : Fin (N + 1)) → TraceOfLength F S i
  | 0, ⟨Trace.empty, h0⟩, i => ⟨Trace.empty, i.val_eq_zero.symm ▸ rfl⟩
  | N + 1, ⟨Trace.cons rest row, h⟩, ⟨i, hi⟩ =>
    if hi' : i = N + 1 then
        -- if `i` is the full length, we return the whole trace
         ⟨Trace.cons rest row, hi' ▸ h⟩
    else take ⟨rest, Nat.succ_inj.mp h⟩ ⟨i, by omega⟩


-- @@ L171-171 verbatim
end TraceOfLength

-- @@ L172-172 verbatim
variable {W : ℕ+} {α : Type}


-- @@ L174-183 verbatim
/--
  A cell offset is an offset in a table that points to a specific cell in a row.
  It is used to define a relative position in the trace.
  `W` is the size of the "vertical window", which means that we can reference at most
  `W` rows above the current row.
  To make sure that the vertical offset is bounded, it is represented as a `Fin W`.
-/
structure CellOffset (W : ℕ+) (S : Type → Type) [ProvableType S]  where
  row: Fin W
  column: Fin (size S)


-- @@ L185-186 verbatim
instance : Repr (CellOffset W S) where
  reprPrec off _ := "⟨" ++ reprStr off.row ++ ", " ++ reprStr off.column ++ "⟩"


-- @@ L188-188 verbatim
namespace CellOffset


-- @@ L190-194 verbatim
/--
  Current row offset
-/
@[table_assignment_norm]
def curr {W : ℕ+} (j : Fin (size S)) : CellOffset W S := ⟨0, j⟩


-- @@ L196-200 verbatim
/--
  Next row offset
-/
@[table_assignment_norm]
def next {W : ℕ+} (j : Fin (size S)) : CellOffset W S := ⟨1, j⟩


-- @@ L202-202 verbatim
end CellOffset


-- @@ L204-206 verbatim
inductive Cell (W : ℕ+) (S : Type → Type) [ProvableType S] where
  | input : CellOffset W S → Cell W S
  | aux : ℕ → Cell W S


-- @@ L208-211 verbatim
instance : Repr (Cell W S) where
  reprPrec cell _ := match cell with
    | .input off => ".input " ++ reprStr off
    | .aux i => ".aux " ++ reprStr i


-- @@ L213-224 verbatim
/--
Mapping between cell offsets in the table and variable indices.

The mapping must maintain the invariant that each variable is assigned to at most one cell.
On the other hand, a cell can be assigned zero, one or more variables.
-/
structure CellAssignment (W : ℕ+) (S : Type → Type) [ProvableType S] where
  offset : ℕ -- number of variables
  aux_length : ℕ -- maximum number of auxiliary cells (i.e. those not part of the input/output layout)

  /-- every variable is assigned to exactly one cell in the trace -/
  vars : Vector (Cell W S) offset


-- @@ L226-226 verbatim
namespace CellAssignment

-- @@ L227-229 verbatim
instance : Repr (CellAssignment W S) where
  reprPrec := fun { offset, aux_length, vars } _ =>
    "{ offset := " ++ reprStr offset ++ ", aux_length := " ++ reprStr aux_length ++ ", vars := " ++ reprStr vars ++ "}"


-- @@ L231-235 verbatim
@[table_assignment_norm, reducible]
def empty (W : ℕ+) : CellAssignment W S where
  offset := 0
  aux_length := 0
  vars := #v[]


-- @@ L237-241 verbatim
@[table_assignment_norm]
def pushVarAux (assignment : CellAssignment W S) : CellAssignment W S where
  offset := assignment.offset + 1
  aux_length := assignment.aux_length + 1
  vars := assignment.vars.push (.aux assignment.aux_length)


-- @@ L243-247 verbatim
@[table_assignment_norm]
def pushVarsAux (assignment : CellAssignment W S) (n : ℕ) : CellAssignment W S where
  offset := assignment.offset + n
  aux_length := assignment.aux_length + n
  vars := assignment.vars ++ (.mapRange n fun i => .aux (assignment.aux_length + i) : Vector (Cell W S) n)


-- @@ L249-253 verbatim
@[table_assignment_norm]
def pushVarInput (assignment : CellAssignment W S) (off : CellOffset W S) : CellAssignment W S where
  offset := assignment.offset + 1
  aux_length := assignment.aux_length
  vars := assignment.vars.push (.input off)


-- @@ L255-262 verbatim
@[table_assignment_norm]
def pushRow (assignment : CellAssignment W S) (row : Fin W) : CellAssignment W S :=
  let row_vars : Vector (Cell W S) (size S) := .mapFinRange _ fun col => .input ⟨ row, col ⟩
  {
    offset := assignment.offset + size S
    aux_length := assignment.aux_length
    vars := assignment.vars ++ row_vars
  }


-- @@ L264-269 verbatim
@[table_assignment_norm]
def setVarInput (assignment : CellAssignment W S) (off : CellOffset W S) (var : ℕ) : CellAssignment W S :=
  let vars := assignment.vars.set? var (.input off)
  -- note that we don't change the `aux_length` and the indices of existing aux variables.
  -- that would unnecessarily complicate reasoning about the assignment
  { assignment with vars }


-- @@ L271-279 verbatim
/--
  The number of auxiliary cells in the final assignment
-/
def numAux (assignment : CellAssignment W S) : ℕ :=
  assignment.vars.foldl (fun acc cell =>
    match cell with
    | .input _ => acc
    | .aux _ => acc + 1
  ) 0


-- @@ L281-281 verbatim
end CellAssignment


-- @@ L283-291 verbatim
/--
  Context of the TableConstraint that keeps track of the current state, this includes the underlying
  offset, and the current assignment of the variables to the cells in the trace.
-/
structure TableContext (W : ℕ+) (S : Type → Type) (F : Type) [FiniteField F] [ProvableType S] where
  inputSize : ℕ := 0
  circuit : Operations F
  assignment : CellAssignment W S
deriving Repr


-- @@ L293-293 verbatim
variable [FiniteField F] {α : Type}


-- @@ L295-295 verbatim
namespace TableContext

-- @@ L296-300 verbatim
@[reducible, table_norm, table_assignment_norm]
def empty : TableContext W S F where
  inputSize := 0
  circuit := []
  assignment := .empty W


-- @@ L302-303 verbatim
@[reducible, table_norm, table_assignment_norm]
def offset (table : TableContext W S F) : ℕ := table.inputSize + table.circuit.localLength

-- @@ L304-304 verbatim
end TableContext


-- @@ L306-308 verbatim
@[reducible, table_norm, table_assignment_norm]
def TableConstraint (W : ℕ+) (S : Type → Type) (F : Type) [FiniteField F] [ProvableType S] :=
  StateM (TableContext W S F)


-- @@ L310-314 verbatim
@[table_norm, table_assignment_norm]
theorem bind_def {β : Type} (f : TableConstraint W S F α) (g : α → TableConstraint W S F β) :
  (f >>= g) = fun ctx =>
    let (a, ctx') := f ctx
    g a ctx' := rfl


-- @@ L316-320 verbatim
@[table_norm, table_assignment_norm]
theorem pure_def (a : α) : (pure a : TableConstraint W S F α) = fun ctx => (a, ctx) := rfl

/- Matchers do not see through the `Id` monad's `pure`, leaving goals stuck on
`match pure (a, ctx) with ...`; reduce it in simp. -/

-- @@ L321-322 verbatim
@[table_norm, table_assignment_norm]
theorem id_pure_def {α : Type} (a : α) : (pure a : Id α) = a := rfl


-- @@ L324-325 verbatim
@[table_norm, table_assignment_norm]
theorem id_bind_def {α β : Type} (a : Id α) (f : α → Id β) : (a >>= f) = f a := rfl


-- @@ L327-328 verbatim
instance [Repr F] : Repr (TableConstraint W S F α) where
  reprPrec table _ := reprStr (table .empty).2


-- @@ L330-339 verbatim
@[table_assignment_norm]
def assignmentFromCircuit (as : CellAssignment W S) : Operations F → CellAssignment W S
  | [] => as
  | .witness m _ :: ops => assignmentFromCircuit (as.pushVarsAux m) ops
  | .assert _ :: ops => assignmentFromCircuit as ops
  | .lookup _ :: ops => assignmentFromCircuit as ops
  | .interact _ :: ops => assignmentFromCircuit as ops
  | .subcircuit s :: ops => assignmentFromCircuit (as.pushVarsAux s.localLength) ops

-- alternative, simpler definition, but makes it harder for lean to check defeq `(windowEnv ..).get i = ..`

-- @@ L340-343 verbatim
def assignmentFromCircuit' (as : CellAssignment W S) (ops : Operations F) : CellAssignment W S where
  offset := as.offset + ops.localLength
  aux_length := as.aux_length + ops.localLength
  vars := as.vars ++ (.mapRange _ fun i => .aux (as.aux_length + i) : Vector (Cell W S) _)


-- @@ L345-357 verbatim
/--
A `MonadLift` instance from `Circuit` to `TableConstraint` means that we can just use
all circuit operations inside a table constraint.
-/
@[reducible, table_norm, table_assignment_norm]
instance : MonadLift (Circuit F) (TableConstraint W S F) where
  monadLift circuit ctx :=
    let (a, ops) := circuit ctx.offset
    (a, {
      inputSize := ctx.inputSize,
      circuit := ctx.circuit ++ ops,
      assignment := assignmentFromCircuit ctx.assignment ops
    })


-- @@ L359-359 verbatim
namespace TableConstraint

-- @@ L360-362 verbatim
@[reducible, table_norm, table_assignment_norm]
def finalOffset (table : TableConstraint W S F α) : ℕ :=
  (table .empty).snd.offset


-- @@ L364-366 verbatim
@[table_norm]
def operations (table : TableConstraint W S F α) : Operations F :=
  table .empty |>.snd.circuit


-- @@ L368-370 verbatim
@[table_assignment_norm]
def finalAssignment (table : TableConstraint W S F α) : CellAssignment W S :=
  table .empty |>.snd.assignment


-- @@ L372-377 verbatim
@[table_assignment_norm]
def OffsetConsistent (table : TableConstraint W S F α) : Prop :=
  table.finalOffset = table.finalAssignment.offset

-- construct an env by taking the result of the assignment function for input/output cells,
-- and allowing arbitrary values for aux cells and invalid variables

-- @@ L378-386 verbatim
def windowEnv (table : TableConstraint W S F Unit)
  (window : TraceOfLength F S W) (aux_env : ProverEnvironment F) : ProverEnvironment F :=
  let assignment := table.finalAssignment
  { aux_env with get i :=
      if hi : i < assignment.offset then
        match assignment.vars[i] with
        | .input ⟨i, j⟩ => window.get i j
        | .aux k => aux_env.get k
      else aux_env.get (i + assignment.aux_length) }


-- @@ L388-397 verbatim
/--
  A table constraint holds on a window of rows if the constraints hold on a suitable environment.
  In particular, we construct the environment by taking directly the result of the assignment function
  so that every variable evaluate to the trace cell value which is assigned to
-/
@[table_norm]
def ConstraintsHoldOnWindow (table : TableConstraint W S F Unit)
  (window : TraceOfLength F S W) (aux_env : ProverEnvironment F) : Prop :=
  let env := windowEnv table window aux_env
  ConstraintsHold.Soundness env table.operations


-- @@ L399-401 verbatim
@[table_norm]
def output {α : Type} (table : TableConstraint W S F α) : α :=
  table .empty |>.fst


-- @@ L403-414 verbatim
/--
  Get a fresh variable for each cell in a given row
-/
@[table_norm, table_assignment_norm]
def getRow (row : Fin W) : TableConstraint W S F (Var S F) :=
  modifyGet fun ctx =>
    let ctx' : TableContext W S F := {
      inputSize := ctx.inputSize,
      circuit := ctx.circuit ++ [.witness (size S) (.ir [] (.envRange ctx.offset))],
      assignment := ctx.assignment.pushRow row
    }
    (varFromOffset S ctx.offset, ctx')


-- @@ L416-420 verbatim
/--
  Get a fresh variable for each cell in the current row
-/
@[table_norm, table_assignment_norm]
def getCurrRow : TableConstraint W S F (Var S F) := getRow 0


-- @@ L422-426 verbatim
/--
  Get a fresh variable for each cell in the next row
-/
@[table_norm, table_assignment_norm]
def getNextRow : TableConstraint W S F (Var S F) := getRow 1


-- @@ L428-441 verbatim
/--
  Read a variable for each cell in a given row, without creating witness operations.
  This is like `getRow` but does not add witness operations to the circuit.
  Instead, it advances the `inputSize` offset, assuming these variables are pre-existing.
-/
@[table_norm, table_assignment_norm]
def readRow (row : Fin W) : TableConstraint W S F (Var S F) :=
  modifyGet fun ctx =>
    let ctx' : TableContext W S F := {
      inputSize := ctx.inputSize + size S,
      circuit := ctx.circuit,
      assignment := ctx.assignment.pushRow row
    }
    (varFromOffset S ctx.offset, ctx')


-- @@ L443-447 verbatim
/--
  Read a variable for each cell in the current row, without creating witness operations.
-/
@[table_norm, table_assignment_norm]
def readCurrRow : TableConstraint W S F (Var S F) := readRow 0


-- @@ L449-453 verbatim
/--
  Read a variable for each cell in the next row, without creating witness operations.
-/
@[table_norm, table_assignment_norm]
def readNextRow : TableConstraint W S F (Var S F) := readRow 1


-- @@ L455-459 verbatim
@[table_norm, table_assignment_norm]
def assignVar (off : CellOffset W S) (v : Variable F) : TableConstraint W S F Unit :=
  modify fun ctx =>
    let assignment := ctx.assignment.setVarInput off v.index
    { ctx with assignment }


-- @@ L461-469 verbatim
@[table_norm, table_assignment_norm]
def assign (off : CellOffset W S) : Expression F → TableConstraint W S F Unit
  -- a variable is assigned directly
  | .var v => assignVar off v
  -- a composed expression or constant is first stored in a new variable, which is assigned
  | x => do
    let new_var ← witnessVar (.ofFExpr (.expr x))
    assertZero (x - var new_var)
    assignVar off new_var


-- @@ L471-475 verbatim
@[table_norm, table_assignment_norm]
def assignCurrRow {W : ℕ+} (curr : Var S F) : TableConstraint W S F Unit :=
  let vars := toElements (M:=S) curr
  forM (List.finRange (size S)) fun i =>
    assign (.curr i) vars[i]


-- @@ L477-481 verbatim
@[table_norm, table_assignment_norm]
def assignNextRow {W : ℕ+} (next : Var S F) : TableConstraint W S F Unit :=
  let vars := toElements (M:=S) next
  forM (List.finRange (size S)) fun i =>
    assign (.next i) vars[i]

-- @@ L482-482 verbatim
end TableConstraint


-- @@ L484-484 verbatim
export TableConstraint (windowEnv getCurrRow getNextRow readCurrRow readNextRow assignVar assign assignNextRow assignCurrRow)


-- @@ L486-487 verbatim
@[reducible]
def SingleRowConstraint (S : Type → Type) (F : Type) [FiniteField F] [ProvableType S] := TableConstraint 1 S F Unit


-- @@ L489-492 verbatim
@[reducible]
def TwoRowsConstraint (S : Type → Type) (F : Type) [FiniteField F] [ProvableType S] := TableConstraint 2 S F Unit

-- specify a row, either counting from the start or from the end of the trace.

-- @@ L493-495 verbatim
inductive RowIndex where
  | fromStart : ℕ → RowIndex
  | fromEnd : ℕ → RowIndex


-- @@ L497-515 verbatim
inductive TableOperation (S : Type → Type) (F : Type) [FiniteField F] [ProvableType S] where
  /--
    A `Boundary` constraint is a constraint that is applied only to a specific row
  -/
  | boundary: RowIndex → SingleRowConstraint S F → TableOperation S F

  /--
    An `EveryRow` constraint is a constraint that is applied to every row.
    It can only reference cells on the same row
  -/
  | everyRow: SingleRowConstraint S F → TableOperation S F

  /--
    An `EveryRowExceptLast` constraint is a constraint that is applied to every row except the last.
    It can reference cells from the current row, or the next row.

    Note that this will not apply any constraints to a trace of length one.
  -/
  | everyRowExceptLast: TwoRowsConstraint S F → TableOperation S F


-- @@ L517-520 verbatim
instance : Repr RowIndex where
  reprPrec
    | .fromStart i, _ => reprStr (i : ℤ)
    | .fromEnd i, _ => reprStr (-i-1 : ℤ)


-- @@ L522-526 verbatim
instance [Repr F] : Repr (TableOperation S F) where
  reprPrec op _ := match op with
    | .boundary i c => "boundary " ++ reprStr i ++ " " ++ reprStr c
    | .everyRow c => "everyRow " ++ reprStr c
    | .everyRowExceptLast c => "everyRowExceptLast " ++ reprStr c


-- @@ L528-528 verbatim
export TableOperation (boundary everyRow everyRowExceptLast)


-- @@ L530-534 verbatim
structure TableEnvironments (F : Type) where
  /-- environment for each constraint, for each row -/
  witnessEnvs : (constraint : ℕ) → (row : ℕ) → (varIndex : ℕ) → F
  /-- auxiliary data available to all rows -/
  data : ProverData F


-- @@ L536-539 verbatim
def TableEnvironments.toEnvironment {F : Type} (envs : TableEnvironments F) (constraint row : ℕ) : ProverEnvironment F :=
  { envs with
    get := envs.witnessEnvs constraint row
    hint := .empty F }

-- @@ L540-602 expanded
/-- The constraints hold over a trace if the hold individually in a suitable environment, where the
  environment is derived from the `CellAssignment` functions. Intuitively, if a variable `x`
  is assigned to a field element in the trace `y: F` using a `CellAssignment` function, then ` env x = y`
-/
@[table_norm]
def TableConstraintsHold {N : ℕ} (constraints : List (TableOperation S F))
    (trace : TraceOfLength F S N) (env : TableEnvironments F) : Prop :=
  let constraints_and_envs := constraints.mapIdx (fun i cs => (cs, env.toEnvironment i))
  foldl N constraints_and_envs trace.val constraints_and_envs
where/-- The foldl function applies the constraints to the trace inductively on the trace
  
      We want to write something like:
      ```
      for row in trace:
        for constraint in constraints:
          apply constraint to row
      ```
      in this exact order, so that the row-inductive structure is at the top-level.
  
      We do double induction: first on the trace, then on the constraints: we apply every constraint to the current row, and
      then recurse on the rest of the trace.
      `cs` is the list of constraints that we have to apply and it is never changed during the induction
      `cs_iterator` is walked inductively for every row.
      Once the `cs_iterator` is empty, we start again on the rest of the trace with the initial constraints `cs`
    -/
  @[table_norm] foldl (N : ℕ) (cs : List (TableOperation S F × (ℕ → (ProverEnvironment F)))) :
    Trace F S →
      (cs_iterator : List (TableOperation S F × (ℕ → (ProverEnvironment F)))) →
        Prop
          -- if the trace has at least two rows and the constraint is a "every row except last" constraint, we apply the constraint
          
    | Trace.cons (Trace.cons trace curr) next, (⟨.everyRowExceptLast constraint, env⟩) :: rest =>
      let others := foldl N cs (Trace.cons (Trace.cons trace curr) next) rest
      let window : TraceOfLength F S 2 := ⟨Trace.cons (Trace.cons Trace.empty curr) next, rfl⟩
      constraint.ConstraintsHoldOnWindow window (env (trace.len + 1)) ∧ others
    | Trace.cons trace row, (⟨.boundary idx constraint, env⟩) :: rest =>
      let others := foldl N cs (Trace.cons trace row) rest
      let window : TraceOfLength F S 1 := ⟨Trace.cons Trace.empty row, rfl⟩
      let targetIdx :=
        match idx with
        | .fromStart i => i
        | .fromEnd i => N - 1 - i
      (if trace.len = targetIdx then constraint.ConstraintsHoldOnWindow window (env trace.len)
        else True) ∧
        others
    | Trace.cons trace row, (⟨.everyRow constraint, env⟩) :: rest =>
      let others := foldl N cs (Trace.cons trace row) rest
      let window : TraceOfLength F S 1 := ⟨Trace.cons Trace.empty row, rfl⟩
      constraint.ConstraintsHoldOnWindow window (env trace.len) ∧ others
    | trace, (⟨.everyRowExceptLast _, _⟩) :: rest => foldl N cs trace rest
    | Trace.cons trace _, [] => foldl N cs trace cs
    | Trace.empty, _ => True


-- @@ L604-630 verbatim
structure FormalTable (F : Type) [FiniteField F] (S : Type → Type) [ProvableType S] where
  /-- list of constraints that are applied over the table -/
  constraints : List (TableOperation S F)

  /-- optional assumption on the table length and other tables in the environment -/
  Assumption : ℕ → ProverData F → Prop := fun _ _ => True

  /-- specification for the table -/
  Spec {N : ℕ}  : TraceOfLength F S N → ProverData F → Prop

  /-- the soundness states that if the assumptions hold, then
      the constraints hold implies that the spec holds. -/
  soundness :
    ∀ (N : ℕ) (trace : TraceOfLength F S N) (env : TableEnvironments F),
    Assumption N env.data →
    TableConstraintsHold constraints trace env →
    Spec trace env.data

  /-- this property tells us that that the number of variables contained in the `assignment` of each
      constraint is consistent with the number of variables introduced in the circuit. -/
  offset_consistent :
    constraints.Forall fun cs =>
      match cs with
      | .boundary _ constraint => constraint.OffsetConsistent
      | .everyRow constraint => constraint.OffsetConsistent
      | .everyRowExceptLast constraint => constraint.OffsetConsistent
    := by repeat constructor


-- @@ L632-635 verbatim
def FormalTable.statement (table : FormalTable F S) (N : ℕ) (trace : TraceOfLength F S N) (env : ProverData F) : Prop :=
  table.Assumption N env → table.Spec trace env

-- add some important lemmas to simp sets

-- @@ L636-636 verbatim
attribute [table_norm] List.mapIdx List.mapIdx.go

-- @@ L637-637 verbatim
attribute [table_norm low] size fromElements toElements

-- @@ L638-638 verbatim
attribute [table_assignment_norm low] toElements


-- @@ L640-640 verbatim
attribute [table_norm, table_assignment_norm] Vector.set? List.set_cons_succ List.set_cons_zero


-- @@ L642-642 verbatim
attribute [table_norm, table_assignment_norm] liftM monadLift

-- @@ L643-643 verbatim
attribute [table_norm, table_assignment_norm] StateT.bind

-- @@ L644-646 verbatim
attribute [table_norm, table_assignment_norm] modify modifyGet MonadStateOf.modifyGet StateT.modifyGet

-- simp lemma to simplify updated circuit after an assignment

-- @@ L647-649 verbatim
@[table_norm, table_assignment_norm]
theorem TableConstraint.assignVar_circuit : ∀ ctx (off : CellOffset W S) (v : Variable F),
  (assignVar off v ctx).snd.circuit = ctx.circuit := by intros; rfl


-- @@ L651-656 verbatim
/--
Tactic script to unfold `assignCurrRow` and `assignNextRow` in a `TableConstraint`.

TODO this is fairly useless without support for `at h` syntax
-/
syntax "simp_assign_row" : tactic

-- @@ L657-667 expanded
macro_rules
  |
  `(tactic|
      ( simp only [assignCurrRow, assignNextRow, size]
        rw [List.finRange, List.ofFn]
        repeat rw [Fin.foldr_succ]
        rw [Fin.foldr_zero]
        repeat rw [List.forM_cons]
        rw [List.forM_nil, bind_pure_unit]
        simp only [seval, toElements, Fin.cast_eq_self, Fin.val_zero, Fin.val_one, Fin.isValue,
          List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
          Fin.succ_zero_eq_one])) =>
    `(tactic|
      ( simp only [assignCurrRow, assignNextRow, size]
        rw [List.finRange, List.ofFn]
        repeat rw [Fin.foldr_succ]
        rw [Fin.foldr_zero]
        repeat rw [List.forM_cons]
        rw [List.forM_nil, bind_pure_unit]
        simp only [seval, toElements, Fin.cast_eq_self, Fin.val_zero, Fin.val_one, Fin.isValue,
          List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
          Fin.succ_zero_eq_one]))

