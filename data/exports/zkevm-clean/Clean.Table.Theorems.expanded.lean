import Clean.Table.Basic


-- @@ L3-3 verbatim
namespace Trace

-- @@ L4-4 verbatim
variable {F : Type} {S : Type → Type} [ProvableType S]


-- @@ L6-20 expanded
/-- Induction principle that applies for every row in the trace, where the inductive step takes into
  account the previous two rows.
-/
def every_row_two_rows_induction {P : Trace F S → Sort*} (zero : P (Trace.empty))
    (one : ∀ row : Row F S, P (Trace.cons empty row))
    (more :
      ∀ curr next : Row F S,
        ∀ rest : Trace F S,
          P (rest) → P (Trace.cons rest curr) → P (Trace.cons (Trace.cons rest curr) next)) :
    ∀ trace, P trace
  | Trace.empty => zero
  | Trace.cons Trace.empty first => one first
  | Trace.cons (Trace.cons rest curr) _ =>
    more _ _ _ (every_row_two_rows_induction zero one more (rest))
      (every_row_two_rows_induction zero one more (Trace.cons rest curr))


-- @@ L22-40 expanded
/-- This induction principle states that if a trace length is at least two, then to prove a property
  about the whole trace, we can provide just a proof for the first two rows, and then a proof
  for the inductive step.
-/
def everyRowTwoRowsInduction' {P : (t : Trace F S) → t.len ≥ 2 → Sort*}
    (base :
      ∀ first second, P (Trace.cons (Trace.cons Trace.empty first) second) (show 2 ≤ 2 by norm_num))
    (more :
      ∀ (row : Row F S) (rest : Trace F S) (h : rest.len ≥ 2),
        P rest h → P (Trace.cons rest row) (Nat.le_succ_of_le h)) :
    ∀ (trace : Trace F S) (h : trace.len ≥ 2), P trace h
  | Trace.empty => by intro; contradiction
  | Trace.cons Trace.empty first => by intro; contradiction
  | Trace.cons (Trace.cons Trace.empty first) second => fun _ => base first second
  | Trace.cons (Trace.cons (Trace.cons rest prev) curr) next => fun h =>
    have h_len : 2 ≤ rest.len + 2 := by simp
    let ih := everyRowTwoRowsInduction' base more (Trace.cons (Trace.cons rest prev) curr) h_len
    more next (Trace.cons (Trace.cons rest prev) curr) h_len ih


-- @@ L42-42 verbatim
end Trace


-- @@ L44-44 verbatim
namespace TraceOfLength

-- @@ L45-45 verbatim
variable {F : Type} {S : Type → Type} [ProvableType S] (N : ℕ)

-- @@ L46-64 expanded
/-- Induction principle that applies for every row in the trace, where the inductive step takes into
  account the previous two rows.
-/
def every_row_two_rows_induction {P : (N : ℕ) → TraceOfLength F S N → Sort*}
    (zero : P 0 ⟨Trace.empty, rfl⟩) (one : ∀ row : Row F S, P 1 ⟨Trace.cons Trace.empty row, rfl⟩)
    (more :
      ∀ (N : ℕ) (curr next : Row F S),
        ∀ rest : TraceOfLength F S N,
          P N (rest) →
            P (N + 1) ⟨Trace.cons rest.val curr, by rw [Trace.len, rest.property]⟩ →
              P (N + 2)
                ⟨Trace.cons (Trace.cons rest.val curr) next, by
                  simp only [Trace.len, rest.property]⟩) :
    ∀ N trace, P N trace
  | 0, ⟨Trace.empty, _⟩ => zero
  | 1, ⟨Trace.cons Trace.empty first, _⟩ => one first
  | N + 2, ⟨Trace.cons (Trace.cons rest curr) next, (h : rest.len + 2 = N + 2)⟩ =>
    by
    have eq : rest.len = N := by rw [Nat.add_left_inj] at h; exact h
    exact
      more N curr next ⟨rest, eq⟩ (every_row_two_rows_induction zero one more N ⟨rest, eq⟩)
        (every_row_two_rows_induction zero one more (N + 1)
          ⟨Trace.cons rest curr, by rw [Trace.len, eq]⟩)


-- @@ L66-80 expanded
theorem everyRowTwoRowsInduction' {P : (N : ℕ+) → TraceOfLength F S N → Prop}
    (one : ∀ row : Row F S, P 1 ⟨Trace.cons Trace.empty row, rfl⟩)
    (more :
      ∀ (N : ℕ) (curr next : Row F S) (rest : TraceOfLength F S N),
        P ⟨N + 1, Nat.succ_pos N⟩ ⟨Trace.cons rest.val curr, by simp [Trace.len, rest.property]⟩ →
          P ⟨N + 2, Nat.succ_pos (N + 1)⟩
            ⟨Trace.cons (Trace.cons rest.val curr) next, by simp [Trace.len, rest.property]⟩) :
    ∀ N trace, P N trace := by
  intro N trace
  let P' (N : ℕ) (trace : TraceOfLength F S N) : Prop :=
    if h : N = 0 then True else P ⟨N, Nat.pos_iff_ne_zero.mpr h⟩ trace
  have goal' :=
    every_row_two_rows_induction (P := P') trivial one
      (by
        intro N curr next rest h_rest h_curr
        exact more N curr next rest h_curr)
      N trace
  simp only [P'] at goal'
  rw [dif_neg N.pos.ne'] at goal'
  exact goal'


-- @@ L82-96 expanded
theorem two_row_induction {prop : Row F S → ℕ → Prop}
    (zero : ∀ first_row : Row F S, prop first_row 0)
    (succ : ∀ (N : ℕ) (curr next : Row F S), prop curr N → prop next (N + 1)) :
    ∀ N (trace : TraceOfLength F S N), ForAllRowsOfTraceWithIndex trace prop :=
  by
  intro N trace
  simp only [ForAllRowsOfTraceWithIndex, Trace.ForAllRowsOfTraceWithIndex]
  induction trace.val using Trace.every_row_two_rows_induction with
  | zero => trivial
  | one first_row =>
    simp only [Trace.ForAllRowsOfTraceWithIndex.inner]
    exact ⟨zero first_row, trivial⟩
  | more curr next rest _
    ih2 =>
    simp only [Trace.ForAllRowsOfTraceWithIndex.inner] at *
    have h3 : prop next (Trace.cons rest curr).len := succ _ _ _ ih2.left
    exact ⟨h3, ih2.left, ih2.right⟩


-- @@ L98-108 verbatim
theorem lastRow_of_forAllWithIndex {N : ℕ+} {prop : Row F S → ℕ → Prop}
  (trace : TraceOfLength F S N) (h : ForAllRowsOfTraceWithIndex trace prop) :
    prop trace.lastRow (N - 1) := by
  induction N, trace using everyRowTwoRowsInduction' with
  | one row =>
    simp only [table_norm, and_true] at h
    exact h
  | more N curr next rest ih =>
    simp only [table_norm] at h ⊢
    rw [rest.property] at h
    exact h.left


-- @@ L110-122 verbatim
theorem lastRow_of_forAllWithPrevious {N : ℕ+} {prop : Row F S → (i : ℕ) → TraceOfLength F S i → Prop}
  (trace : TraceOfLength F S N) (h : ForAllRowsWithPrevious trace prop) :
    prop trace.lastRow (N - 1) trace.tail := by
  induction N, trace using everyRowTwoRowsInduction' with
  | one row =>
    simp only [ForAllRowsWithPrevious, Trace.ForAllRowsWithPrevious, and_true] at h
    exact h
  | more N curr next rest ih =>
    rcases rest with ⟨ rest, hN ⟩
    subst hN
    simp only [ForAllRowsWithPrevious, Trace.ForAllRowsWithPrevious, table_norm] at h ⊢
    simp only [PNat.mk_coe, Nat.add_one_sub_one, tail, Trace.tail]
    exact h.left


-- @@ L124-124 verbatim
end TraceOfLength


-- @@ L126-126 verbatim
variable {F : Type} [FiniteField F] {S : Type → Type} [ProvableType S] {W : ℕ+}


-- @@ L128-128 verbatim
namespace CellAssignment


-- @@ L130-132 verbatim
theorem pushVarInput_offset (assignment : CellAssignment W S) (off : CellOffset W S) :
  (assignment.pushVarInput off).offset = assignment.offset + 1 := by
  simp [pushVarInput, Vector.push]


-- @@ L134-135 verbatim
lemma pushRow_offset (assignment : CellAssignment W S) (row : Fin W) :
  (assignment.pushRow row).offset = assignment.offset + size S := rfl


-- @@ L137-142 verbatim
theorem assignmentFromCircuit_offset (as : CellAssignment W S) (ops : Operations F) :
    (assignmentFromCircuit as ops).offset = as.offset + ops.localLength := by
  induction ops using Operations.induct generalizing as with
  | empty => rfl
  | witness | assert | lookup | subcircuit | interact =>
    simp_all +arith [assignmentFromCircuit, CellAssignment.pushVarsAux, Operations.localLength]


-- @@ L144-151 verbatim
theorem assignmentFromCircuit_vars (as : CellAssignment W S) (ops : Operations F) :
    (assignmentFromCircuit as ops).vars = (as.vars ++ (.mapRange ops.localLength fun i => .aux (as.aux_length + i) : Vector (Cell W S) _)
      ).cast (assignmentFromCircuit_offset ..).symm := by
  induction ops using Operations.induct generalizing as with
  | empty => rfl
  | witness | assert | lookup | subcircuit | interact =>
    simp_all +arith [assignmentFromCircuit, pushVarsAux, Operations.localLength,
      Vector.mapRange_add_eq_append, Vector.cast, Vector.toArray_append, Array.append_assoc]


-- @@ L153-153 verbatim
end CellAssignment
