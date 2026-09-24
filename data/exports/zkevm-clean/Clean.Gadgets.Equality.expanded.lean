/-
This file provides the built-in `assertEquals` gadget, which works for any provable type
and smoothly simplifies to an equality statement under `circuit_norm`.
-/
import Clean.Circuit.Loops
import Clean.Circuit.Explicit


-- @@ L8-8 verbatim
variable {F : Type} [FiniteField F] {M : TypeMap} [ProvableType M]


-- @@ L10-10 verbatim
namespace Gadgets

-- @@ L11-11 verbatim
def allZero {n} (xs : Vector (Expression F) n) : Circuit F Unit := .forEach xs assertZero


-- @@ L13-18 verbatim
theorem allZero.soundness {offset : ℕ} {env : Environment F} {n} {xs : Vector (Expression F) n} :
    ConstraintsHold.Soundness env ((allZero xs).operations offset) → ∀ x ∈ xs, x.eval env = 0 := by
  simp only [allZero, circuit_norm]
  intro h_holds x hx
  obtain ⟨i, hi, rfl⟩ := Vector.getElem_of_mem hx
  exact h_holds ⟨i, hi⟩


-- @@ L20-25 verbatim
theorem allZero.completeness {offset : ℕ} {env : ProverEnvironment F} {n} {xs : Vector (Expression F) n} :
    (∀ x ∈ xs, x.eval env = 0) →
    ConstraintsHold.Completeness env ((allZero xs).operations offset) := by
  simp only [allZero, circuit_norm]
  intro h_holds i
  exact h_holds xs[i] (Vector.mem_of_getElem rfl)


-- @@ L27-27 verbatim
namespace Equality

-- @@ L28-31 verbatim
def main (input : Var M F × Var M F) : Circuit F Unit := do
  let (x, y) := input
  let diffs := (toElements (M:=M) x).zip (toElements y) |>.map (fun (xi, yi) => xi - yi)
  .forEach diffs assertZero


-- @@ L33-35 verbatim
@[reducible]
instance elaborated (M : TypeMap) [ProvableType M] : ElaboratedCircuit F (ProvablePair M M) unit main := by
  elaborate_circuit


-- @@ L37-37 verbatim
@[simps! -isSimp (attr := circuit_norm)]

-- @@ L38-92 verbatim
def circuit (M : TypeMap) [ProvableType M] : FormalAssertion F (ProvablePair M M) where
  main

  Spec : M F × M F → Prop
  | (x, y) => x = y

  soundness := by
    intro offset env input_var input h_input _ h_holds
    replace h_holds := allZero.soundness h_holds
    simp only at h_holds
    -- destructure before splitting: the `match input_var` in `main` only reduces on a literal pair
    let ⟨x, y⟩ := input
    let ⟨x_var, y_var⟩ := input_var
    constructor; swap
    · simp only [main, circuit_norm]

    simp only [circuit_norm, Prod.mk.injEq] at h_input
    obtain ⟨ hx, hy ⟩ := h_input
    rw [←hx, ←hy]
    simp only [CircuitType.eval_expression, ProvableType.eval]
    congr 1
    ext i hi
    simp only [Vector.getElem_map]

    rw [Vector.forall_mem_iff_forall_getElem] at h_holds
    specialize h_holds i hi
    rw [Vector.getElem_map, Vector.getElem_zip] at h_holds
    rw [eval_sub, sub_eq_zero] at h_holds
    exact h_holds

  completeness := by
    intro offset env input_var h_env input  h_input _ h_spec
    apply allZero.completeness
    simp only

    let ⟨x, y⟩ := input
    let ⟨x_var, y_var⟩ := input_var
    simp only [circuit_norm, Prod.mk.injEq] at h_input
    obtain ⟨ hx, hy ⟩ := h_input
    rw [←hx, ←hy] at h_spec
    clear hx hy
    apply_fun toElements at h_spec
    simp only [CircuitType.eval_expression, ProvableType.eval,
      ProvableType.toElements_fromElements] at h_spec
    rw [Vector.ext_iff] at h_spec

    rw [Vector.forall_mem_iff_forall_getElem]
    intro i hi
    specialize h_spec i hi
    simp only [Vector.getElem_map] at h_spec
    simp only [Vector.getElem_map, Vector.getElem_zip, eval_sub]
    rw [h_spec]
    ring

-- allow `circuit_norm` to elaborate properties of the `circuit` while keeping main/spec/assumptions opaque

-- @@ L93-94 verbatim
@[circuit_norm ↓, explicit_circuit_norm]
lemma elaborated_eq : (circuit M (F:=F)).elaborated = elaborated M := rfl


-- @@ L96-98 verbatim
@[circuit_norm, explicit_circuit_norm]
lemma localLength_eq (input : Var (ProvablePair M M) F) :
  (circuit M).localLength input = 0 := by simp only [circuit_norm, circuit]

-- @@ L99-101 verbatim
@[circuit_norm, explicit_circuit_norm]
lemma output_eq (input : Var (ProvablePair M M) F) (offset : ℕ) :
  (circuit M).output input offset = () := by simp only [circuit_norm, circuit]

-- @@ L102-104 verbatim
@[circuit_norm, explicit_circuit_norm]
lemma channelsWithGuarantees_eq :
  (circuit M (F:=F)).channelsWithGuarantees = [] := by simp only [circuit_norm, circuit]

-- @@ L105-109 verbatim
@[circuit_norm, explicit_circuit_norm]
lemma channelsWithRequirements_eq :
  (circuit M (F:=F)).channelsWithRequirements = [] := by simp only [circuit_norm, circuit]

-- rewrite spec/proverAssumptions/proverSpec directly


-- @@ L111-114 verbatim
@[circuit_norm]
theorem spec (n : ℕ) (env : Environment F) (x y : Var M F) :
    ((circuit M).toSubcircuit n (x, y)).Spec env = (eval env x = eval env y) := by
  simp only [circuit_norm, circuit]


-- @@ L116-119 verbatim
@[circuit_norm]
theorem proverAssumptions (n : ℕ) (env : ProverEnvironment F) (x y : Var M F) :
    ((circuit M).toSubcircuit n (x, y)).ProverAssumptions env = (eval env x = eval env y) := by
  simp only [circuit_norm, circuit]


-- @@ L121-124 verbatim
@[circuit_norm]
theorem proverSpec (n : ℕ) (env : ProverEnvironment F) (x y : Var M F) :
    ((circuit M).toSubcircuit n (x, y)).ProverSpec env = True := by
  simp only [FormalAssertion.toSubcircuit, circuit]


-- @@ L126-126 verbatim
end Equality

-- @@ L127-129 verbatim
end Gadgets

-- Defines a unified `===` notation for asserting equality in circuits.


-- @@ L131-133 verbatim
@[circuit_norm]
def assertEquals (x y : M (Expression F)) : Circuit F Unit :=
  Gadgets.Equality.circuit M (x, y)


-- @@ L135-137 verbatim
@[circuit_norm, reducible]
def Expression.assertEquals (x y : Expression F) : Circuit F Unit :=
  Gadgets.Equality.circuit field (x, y)


-- @@ L139-140 verbatim
class HasAssertEq (β : Type) (F : outParam Type) [FiniteField F] where
  assert_eq : β → β → Circuit F Unit


-- @@ L142-143 verbatim
instance : HasAssertEq (Expression F) F where
  assert_eq := Expression.assertEquals


-- @@ L145-146 verbatim
instance : HasAssertEq (M (Expression F)) F where
  assert_eq := @assertEquals F _ M _


-- @@ L148-148 verbatim
attribute [circuit_norm] HasAssertEq.assert_eq

-- @@ L149-151 verbatim
infix:50 " === " => HasAssertEq.assert_eq

-- Defines a unified `<==` notation for witness assignment with equality assertion in circuits.


-- @@ L153-154 verbatim
class HasAssignEq (β : Type) (F : outParam Type) [FiniteField F] where
  assignEq : β → Circuit F β


-- @@ L156-160 verbatim
instance : HasAssignEq (Expression F) F where
  assignEq rhs := do
    let w ← witness (.expr rhs)
    w === rhs
    return w


-- @@ L162-166 verbatim
instance : HasAssignEq (M (Expression F)) F where
  assignEq rhs := do
    let w ← witnessIR M (.ofExprs (toElements rhs))
    w === rhs
    return w


-- @@ L168-169 verbatim
instance {n : ℕ} : HasAssignEq (Vector (Expression F) n) F :=
  inferInstanceAs (HasAssignEq (fields n (Expression F)) F)


-- @@ L171-173 verbatim
attribute [circuit_norm] HasAssignEq.assignEq

-- Custom syntax to allow `let var <== expr` without monadic arrow

-- @@ L174-174 verbatim
syntax "let " ident " <== " term : doElem

-- @@ L175-175 verbatim
syntax "let " ident " : " term " <== " term : doElem


-- @@ L177-181 verbatim
macro_rules
  | `(doElem| let $x <== $e) => `(doElem| let $x ← HasAssignEq.assignEq $e)
  | `(doElem| let $x : $t <== $e) => `(doElem| let $x : $t ← HasAssignEq.assignEq $e)

-- `ExplicitCircuit` integration


-- @@ L183-183 verbatim
instance {x y : Expression F} : ExplicitCircuit (Expression.assertEquals x y) := inferInstance


-- @@ L185-187 verbatim
instance {x y : M (Expression F)} :
    ExplicitCircuit (assertEquals x y) := inferInstanceAs <|
  ExplicitCircuit (Gadgets.Equality.circuit M (x, y))


-- @@ L189-190 verbatim
instance {x y : M (Expression F)} : ExplicitCircuit (HasAssertEq.assert_eq x y) :=
  inferInstanceAs (ExplicitCircuit (assertEquals x y))


-- @@ L192-193 verbatim
instance {x y : Expression F} : ExplicitCircuit (HasAssertEq.assert_eq x y) :=
  inferInstanceAs (ExplicitCircuit (Expression.assertEquals x y))
