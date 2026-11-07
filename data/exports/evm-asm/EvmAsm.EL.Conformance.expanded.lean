/-
  EvmAsm.EL.Conformance

  Lean-side conformance vector surface for GH #125.
-/

module


-- @@ L9-9 verbatim
@[expose] public section

-- @@ L10-10 verbatim
namespace EvmAsm.EL

-- @@ L11-11 verbatim
namespace Conformance


-- @@ L13-17 verbatim
/-- Expected result for a conformance vector: either a value or an expected error. -/
inductive ExpectedResult (α : Type) where
  | value (output : α)
  | error (label : String)
  deriving Repr


-- @@ L19-25 verbatim
/-- Typed conformance vector. Later slices can instantiate `ι`/`ο` with
    opcode inputs, transaction/state inputs, or decoded execution-spec cases. -/
structure TestVector (ι ο : Type) where
  id : String
  input : ι
  expected : ExpectedResult ο
  deriving Repr


-- @@ L27-32 verbatim
/-- Result of checking one vector against an executable specification. -/
inductive CheckResult where
  | passed
  | failed (id : String)
  | errored (id label : String)
  deriving DecidableEq, Repr


-- @@ L34-34 verbatim
namespace CheckResult


-- @@ L36-38 verbatim
def isPassed : CheckResult → Prop
  | passed => True
  | _ => False


-- @@ L40-40 verbatim
@[simp] theorem isPassed_passed : passed.isPassed := trivial


-- @@ L42-44 verbatim
@[simp] theorem not_isPassed_failed (id : String) :
    ¬ (failed id).isPassed := by
  simp [isPassed]


-- @@ L46-48 verbatim
@[simp] theorem not_isPassed_errored (id label : String) :
    ¬ (errored id label).isPassed := by
  simp [isPassed]


-- @@ L50-50 verbatim
end CheckResult


-- @@ L52-57 verbatim
/-- Check a vector whose expected result is a concrete output. -/
def checkVector [DecidableEq ο] (run : ι → ο) (vector : TestVector ι ο) : CheckResult :=
  match vector.expected with
  | .value expected =>
      if run vector.input = expected then .passed else .failed vector.id
  | .error label => .errored vector.id label


-- @@ L59-69 verbatim
/-- Check a vector against a partial executable specification. -/
def checkVector? [DecidableEq ο] (run : ι → Option ο) (vector : TestVector ι ο) : CheckResult :=
  match vector.expected with
  | .value expected =>
      match run vector.input with
      | some actual => if actual = expected then .passed else .failed vector.id
      | none => .failed vector.id
  | .error label =>
      match run vector.input with
      | some _ => .failed vector.id
      | none => .errored vector.id label


-- @@ L71-75 verbatim
theorem checkVector_value_passed
    [DecidableEq ο] (run : ι → ο) (id : String) (input : ι) (expected : ο)
    (h_run : run input = expected) :
    checkVector run { id := id, input := input, expected := .value expected } = .passed := by
  simp [checkVector, h_run]


-- @@ L77-81 verbatim
theorem checkVector_value_failed
    [DecidableEq ο] (run : ι → ο) (id : String) (input : ι) (expected : ο)
    (h_run : run input ≠ expected) :
    checkVector run { id := id, input := input, expected := .value expected } = .failed id := by
  simp [checkVector, h_run]


-- @@ L83-85 verbatim
theorem checkVector_error_errored
    [DecidableEq ο] (run : ι → ο) (id label : String) (input : ι) :
    checkVector run { id := id, input := input, expected := .error label } = .errored id label := rfl


-- @@ L87-91 verbatim
theorem checkVector?_some_passed
    [DecidableEq ο] (run : ι → Option ο) (id : String) (input : ι) (expected : ο)
    (h_run : run input = some expected) :
    checkVector? run { id := id, input := input, expected := .value expected } = .passed := by
  simp [checkVector?, h_run]


-- @@ L93-97 verbatim
theorem checkVector?_none_error
    [DecidableEq ο] (run : ι → Option ο) (id label : String) (input : ι)
    (h_run : run input = none) :
    checkVector? run { id := id, input := input, expected := .error label } = .errored id label := by
  simp [checkVector?, h_run]


-- @@ L99-103 verbatim
/-- Check a batch of total executable-spec conformance vectors.
    Distinctive token: conformanceBatchHelpers. -/
def checkBatch [DecidableEq ο] (run : ι → ο) (vectors : List (TestVector ι ο)) :
    List CheckResult :=
  vectors.map (checkVector run)


-- @@ L105-108 verbatim
/-- Check a batch of partial executable-spec conformance vectors. -/
def checkBatch? [DecidableEq ο] (run : ι → Option ο) (vectors : List (TestVector ι ο)) :
    List CheckResult :=
  vectors.map (checkVector? run)


-- @@ L110-113 verbatim
/-- Batch predicate used by conformance files that expect every vector to pass. -/
def allPassed : List CheckResult → Prop
  | [] => True
  | result :: rest => result.isPassed ∧ allPassed rest


-- @@ L115-116 verbatim
@[simp] theorem checkBatch_nil [DecidableEq ο] (run : ι → ο) :
    checkBatch run [] = [] := rfl


-- @@ L118-119 verbatim
@[simp] theorem checkBatch?_nil [DecidableEq ο] (run : ι → Option ο) :
    checkBatch? run [] = [] := rfl


-- @@ L121-123 verbatim
@[simp] theorem checkBatch_cons [DecidableEq ο] (run : ι → ο)
    (vector : TestVector ι ο) (vectors : List (TestVector ι ο)) :
    checkBatch run (vector :: vectors) = checkVector run vector :: checkBatch run vectors := rfl


-- @@ L125-127 verbatim
@[simp] theorem checkBatch?_cons [DecidableEq ο] (run : ι → Option ο)
    (vector : TestVector ι ο) (vectors : List (TestVector ι ο)) :
    checkBatch? run (vector :: vectors) = checkVector? run vector :: checkBatch? run vectors := rfl


-- @@ L129-132 verbatim
@[simp] theorem checkBatch_append [DecidableEq ο] (run : ι → ο)
    (left right : List (TestVector ι ο)) :
    checkBatch run (left ++ right) = checkBatch run left ++ checkBatch run right := by
  simp [checkBatch]


-- @@ L134-137 verbatim
@[simp] theorem checkBatch?_append [DecidableEq ο] (run : ι → Option ο)
    (left right : List (TestVector ι ο)) :
    checkBatch? run (left ++ right) = checkBatch? run left ++ checkBatch? run right := by
  simp [checkBatch?]


-- @@ L139-139 verbatim
@[simp] theorem allPassed_nil : allPassed [] := trivial


-- @@ L141-142 verbatim
@[simp] theorem allPassed_cons (result : CheckResult) (rest : List CheckResult) :
    allPassed (result :: rest) ↔ result.isPassed ∧ allPassed rest := Iff.rfl


-- @@ L144-146 verbatim
@[simp] theorem allPassed_passed_cons (rest : List CheckResult) :
    allPassed (.passed :: rest) ↔ allPassed rest := by
  simp [allPassed]


-- @@ L148-150 verbatim
@[simp] theorem not_allPassed_failed_cons (id : String) (rest : List CheckResult) :
    ¬ allPassed (.failed id :: rest) := by
  simp [allPassed]


-- @@ L152-154 verbatim
@[simp] theorem not_allPassed_errored_cons (id label : String) (rest : List CheckResult) :
    ¬ allPassed (.errored id label :: rest) := by
  simp [allPassed]


-- @@ L156-162 verbatim
theorem allPassed_append (left right : List CheckResult) :
    allPassed (left ++ right) ↔ allPassed left ∧ allPassed right := by
  induction left with
  | nil =>
      simp [allPassed]
  | cons result rest ih =>
      cases result <;> simp [allPassed, ih]


-- @@ L164-164 verbatim
end Conformance

-- @@ L165-165 verbatim
end EvmAsm.EL
