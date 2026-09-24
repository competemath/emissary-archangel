module

public import Foundation.FirstOrder.Arithmetic.HFS.PRF


-- @@ L5-9 verbatim
/-!

# Superexponential Function in $\mathsf{I} \Sigma_1$

-/


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
namespace FFL.FirstOrder.Arithmetic


-- @@ L15-15 verbatim
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]


-- @@ L17-17 verbatim
section iterExp


-- @@ L19-21 verbatim
def iterExp.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y x. y = x”
  succ := .mkSigma “y ih n x. !(expDef.ofZero 𝚺₁) y ih”


-- @@ L23-27 verbatim
noncomputable def iterExp.construction : PR.Construction V iterExp.blueprint where
  zero := fun v ↦ v 0
  succ := fun _ _ ih ↦ Exp.exp ih
  zero_defined := .mk fun v ↦ by simp [iterExp.blueprint]
  succ_defined := .mk fun v ↦ by simp [iterExp.blueprint, expDef, exponential_graph]


-- @@ L29-30 verbatim
/-- `iterExp x y = 2^x_y` (iterated exponentiation). -/
noncomputable def iterExp (x y : V) : V := iterExp.construction.result ![x] y


-- @@ L32-32 verbatim
@[simp] lemma iterExp_zero (x : V) : iterExp x 0 = x := by simp [iterExp, iterExp.construction]


-- @@ L34-35 verbatim
@[simp] lemma iterExp_succ (x y : V) : iterExp x (y + 1) = Exp.exp (iterExp x y) := by
  simp [iterExp, iterExp.construction]


-- @@ L37-38 verbatim
def _root_.FFL.FirstOrder.Arithmetic.iterExpDef : 𝚺₁.Semisentence 3 :=
  iterExp.blueprint.resultDef |>.rew (Rew.subst ![#0, #2, #1])


-- @@ L40-41 verbatim
instance iterExp_defined : 𝚺₁-Function₂[V] iterExp via iterExpDef := .mk
  fun v ↦ by simp [iterExp.construction.result_defined_iff, iterExpDef]; rfl


-- @@ L43-43 verbatim
instance iterExp_definable : 𝚺₁-Function₂[V] iterExp := iterExp_defined.to_definable


-- @@ L45-45 verbatim
instance iterExp_definable' (Γ) : Γ-[m + 1]-Function₂ (iterExp : V → V → V) := iterExp_definable.of_sigmaOne


-- @@ L47-47 verbatim
end iterExp


-- @@ L49-49 verbatim
section superexp


-- @@ L51-53 verbatim
noncomputable instance : Superexp V := ⟨fun x ↦ iterExp x x⟩

lemma superexp_eq (x : V) : Superexp.superexp x = iterExp x x := rfl


-- @@ L55-55 verbatim
@[simp] lemma superexp_zero : Superexp.superexp (0 : V) = 0 := by simp [superexp_eq]


-- @@ L57-58 verbatim
@[simp] lemma superexp_one : Superexp.superexp (1 : V) = 2 := by
  rw [superexp_eq, congrArg (iterExp 1) (zero_add 1).symm, iterExp_succ, iterExp_zero, exp_one]


-- @@ L60-68 verbatim
@[simp] lemma superexp_two : Superexp.superexp (2 : V) = 16 := by
  have exp_two : Exp.exp (2 : V) = 4 := by
    rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm, exp_succ, exp_one]; norm_num
  have exp_four : Exp.exp (4 : V) = 16 := by
    rw [show (4 : V) = 3 + 1 from three_add_one_eq_four.symm, exp_succ,
      show (3 : V) = 2 + 1 from two_add_one_eq_three.symm, exp_succ, exp_two]
    norm_num
  rw [superexp_eq, congrArg (iterExp 2) (one_add_one_eq_two (R := V)).symm, iterExp_succ,
    congrArg (iterExp 2) (zero_add 1).symm, iterExp_succ, iterExp_zero, exp_two, exp_four]


-- @@ L70-81 verbatim
@[simp] lemma superexp_three : Superexp.superexp (3 : V) = Exp.exp 256 := by
  have exp_two : Exp.exp (2 : V) = 4 := by
    rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm, exp_succ, exp_one]; norm_num
  have exp_three : Exp.exp (3 : V) = 8 := by
    rw [show (3 : V) = 2 + 1 from two_add_one_eq_three.symm, exp_succ, exp_two]; norm_num
  have exp_four : Exp.exp (4 : V) = 16 := by
    rw [show (4 : V) = 3 + 1 from three_add_one_eq_four.symm, exp_succ, exp_three]; norm_num
  have exp_eight : Exp.exp (8 : V) = 256 := by
    rw [show (8 : V) = 2 * 4 from by norm_num, exp_even, exp_four]; norm_num [sq]
  rw [superexp_eq, congrArg (iterExp 3) (two_add_one_eq_three (R := V)).symm, iterExp_succ,
    congrArg (iterExp 3) (one_add_one_eq_two (R := V)).symm, iterExp_succ,
    congrArg (iterExp 3) (zero_add 1).symm, iterExp_succ, iterExp_zero, exp_three, exp_eight]


-- @@ L83-84 verbatim
def _root_.FFL.FirstOrder.Arithmetic.superexpDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y x. !iterExpDef y x x”


-- @@ L86-87 verbatim
instance superexp_defined : 𝚺₁-Function₁[V] Superexp.superexp via superexpDef := .mk
  fun v ↦ by simp [superexpDef, superexp_eq, iterExp_defined.iff]


-- @@ L89-89 verbatim
instance superexp_definable : 𝚺₁-Function₁[V] Superexp.superexp := superexp_defined.to_definable


-- @@ L91-91 verbatim
end superexp


-- @@ L93-93 verbatim
end FFL.FirstOrder.Arithmetic
