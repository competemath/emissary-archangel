import DG.Module.ExternalTensorOver
import DG.Algebra.TensorProductComparison
import DG.Homotopy.ChangeOfRings


-- @@ L5-18 verbatim
/-!
# The external tensor product over `R` is induced from the one over `ℤ`

Let `R` be a commutative ring and `A`, `B` dg `R`-algebras, with the comparison morphism of dg
rings `φ : A ᵍ⊗[ℤ] B → A ᵍ⊗[R] B` (`DG.GradedTensorProduct.intComparison`). For a dg `A`-module
`M` and a dg `B`-module `N`,

`(A ⊗_R B) ⊗_{A ⊗_ℤ B} (M ⊗_ℤ N) ≅ M ⊗_R N`, `x ⊗ (m ⊗ n) ↦ x • (m ⊗ n)`

as dg modules over `A ᵍ⊗[R] B` (`DG.ExternalTensorOver.extendEquiv`), with inverse
`m ⊗ n ↦ 1 ⊗ (m ⊗ n)`. The forward map is adjoint to the canonical map
`M ⊗_ℤ N → M ⊗_R N` (`DG.ExternalTensorOver.comparison`), a morphism of dg modules over
`A ᵍ⊗[ℤ] B` after restriction along `φ`.
-/


-- @@ L20-20 verbatim
open scoped TensorProduct

-- @@ L21-21 verbatim
open MulOpposite


-- @@ L23-23 verbatim
set_option linter.unusedSectionVars false


-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-27 verbatim
namespace DG


-- @@ L29-29 verbatim
namespace ExternalTensorOver


-- @@ L31-37 verbatim
variable {R : Type*} [CommRing R]
  {A : Type*} [Ring A] [Algebra R A] [DGAddCommGroup A] [DGRing A] [DGAlgebra R A]
  {B : Type*} [Ring B] [Algebra R B] [DGAddCommGroup B] [DGRing B] [DGAlgebra R B]
  {M : Type*} [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M] [Module R M]
  [IsScalarTower R A M]
  {N : Type*} [AddCommGroup N] [DGAddCommGroup N] [Module B N] [DGModule B N] [Module R N]
  [IsScalarTower R B N]


-- @@ L39-39 verbatim
local notation "𝒜" => DGAlgebra.gradingSubmodule ℤ A

-- @@ L40-40 verbatim
local notation "ℬ" => DGAlgebra.gradingSubmodule ℤ B

-- @@ L41-41 verbatim
local notation "𝒜ᵣ" => DGAlgebra.gradingSubmodule R A

-- @@ L42-42 verbatim
local notation "ℬᵣ" => DGAlgebra.gradingSubmodule R B


-- @@ L44-47 verbatim
variable (R A B M N) in
/-- The canonical additive map `M ⊗_ℤ N → M ⊗_R N`, `m ⊗ n ↦ m ⊗ n`. -/
def comparisonAddHom : M ⊗[ℤ] N →+ ExternalTensorOver R A B M N :=
  (TensorProduct.mapOfCompatibleSMul R ℤ ℤ M N).toAddMonoidHom


-- @@ L49-51 verbatim
@[simp]
theorem comparisonAddHom_tmul (m : M) (n : N) :
    comparisonAddHom R A B M N (m ⊗ₜ n) = tmul m n := rfl


-- @@ L53-66 verbatim
theorem comparisonAddHom_smul (c : 𝒜 ᵍ⊗[ℤ] ℬ) (x : M ⊗[ℤ] N) :
    comparisonAddHom R A B M N (c • x) =
      GradedTensorProduct.intComparison R A B c • comparisonAddHom R A B M N x := by
  induction c using GradedTensorProduct.induction_on_tmul (R := ℤ) with
  | zero => rw [ExternalTensor.zero_smul', map_zero, map_zero, zero_smul']
  | add c c' hc hc' => rw [ExternalTensor.add_smul', map_add, hc, hc', map_add, add_smul']
  | @tmul i j a ha b hb =>
    induction x using DG.tensor_induction_on with
    | zero => rw [ExternalTensor.smul_zero', map_zero, smul_zero']
    | add x y hx hy => rw [ExternalTensor.smul_add', map_add, hx, hy, map_add, smul_add']
    | tmul m n =>
      rw [ExternalTensor.tmul_smul_tmul a hb m.2, map_units_zsmul, comparisonAddHom_tmul,
        comparisonAddHom_tmul, GradedTensorProduct.intComparison_tmul,
        tmul_smul_tmul a hb m.2]


-- @@ L68-91 expanded
variable (R A B M N) in
/-- **The canonical map `M ⊗_ℤ N → M ⊗_R N`**, a morphism of dg modules over `A ᵍ⊗[ℤ] B` after
restricting scalars along `A ᵍ⊗[ℤ] B → A ᵍ⊗[R] B`. -/
def comparison :
    DGModuleHom (𝒜 ᵍ⊗[ℤ] ℬ) (M ⊗[ℤ] N)
      (RestrictScalars (GradedTensorProduct.intComparison R A B) (ExternalTensorOver R A B M N))
    where
  toFun x := comparisonAddHom R A B M N x
  map_add' := map_add _
  map_smul' c x := comparisonAddHom_smul c x
  map_mem' {k x}
    hx :=
    by
    have :=
      DG.map_mem_grading_of_tmul (Y := ExternalTensorOver R A B M N) (comparisonAddHom R A B M N) 0
        (fun {i j m n} hm hn => by
          rw [add_zero, comparisonAddHom_tmul]
          exact tmul_mem_grading hm hn)
        hx
    rw [add_zero] at this
    exact this
  map_d'
    x := by
    change comparisonAddHom R A B M N (d x) = d (comparisonAddHom R A B M N x)
    induction x using DG.tensor_induction_on with
    | zero => simp
    | add x y hx hy => rw [d_add, map_add, hx, hy, map_add, d_add]
    | tmul m n =>
      rw [DG.d_tmul_of_mem m.2, map_add, map_units_zsmul, comparisonAddHom_tmul,
        comparisonAddHom_tmul, comparisonAddHom_tmul, d_tmul_of_mem m.2]


-- @@ L93-102 verbatim
/-- `(r • m) ⊗ n = (r ⊗ 1) • (m ⊗ n)` over `ℤ`. -/
theorem ground_smul_tmul_eq (r : R) (m : M) (n : N) :
    ((r • m) ⊗ₜ[ℤ] n : M ⊗[ℤ] N) = (algebraMap R A r ᵍ⊗ₜ[ℤ] (1 : B) : 𝒜 ᵍ⊗[ℤ] ℬ) • (m ⊗ₜ n) := by
  induction m using DG.induction_on with
  | h_zero => rw [smul_zero, TensorProduct.zero_tmul, ExternalTensor.smul_zero']
  | h_homogeneous m =>
    rw [ExternalTensor.tmul_smul_tmul _ (one_mem_grading (A := B)) m.2, zero_mul,
      koszulSign_zero, one_smul, one_smul, algebraMap_smul]
  | h_add m m' hm hm' => rw [smul_add, TensorProduct.add_tmul, TensorProduct.add_tmul, hm, hm',
      ExternalTensor.smul_add']


-- @@ L104-113 verbatim
/-- `m ⊗ (r • n) = (1 ⊗ r) • (m ⊗ n)` over `ℤ`. -/
theorem tmul_ground_smul_eq (r : R) (m : M) (n : N) :
    (m ⊗ₜ[ℤ] (r • n) : M ⊗[ℤ] N) = ((1 : A) ᵍ⊗ₜ[ℤ] algebraMap R B r : 𝒜 ᵍ⊗[ℤ] ℬ) • (m ⊗ₜ n) := by
  induction m using DG.induction_on with
  | h_zero => simp only [TensorProduct.zero_tmul, ExternalTensor.smul_zero']
  | h_homogeneous m =>
    rw [ExternalTensor.tmul_smul_tmul _ (algebraMap_mem_grading R (A := B) r) m.2, zero_mul,
      koszulSign_zero, one_smul, one_smul, algebraMap_smul]
  | h_add m m' hm hm' => rw [TensorProduct.add_tmul, TensorProduct.add_tmul, hm, hm',
      ExternalTensor.smul_add']


-- @@ L115-126 verbatim
variable (R A B M N) in
/-- The biadditive map `(m, n) ↦ 1 ⊗ (m ⊗ n)`. -/
def extendInvAux : M →+ N →+ TensorProductOver (𝒜 ᵍ⊗[ℤ] ℬ)
    (GradedTensorProduct.intComparison R A B).Bimodule (M ⊗[ℤ] N) :=
  AddMonoidHom.mk' (fun m => AddMonoidHom.mk'
      (fun n => TensorProductOver.tmul _
        ((GradedTensorProduct.intComparison R A B).bimoduleEquiv 1) (m ⊗ₜ[ℤ] n))
      fun n n' => by rw [TensorProduct.tmul_add, TensorProductOver.tmul_add])
    fun m m' => by
      ext n
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      rw [TensorProduct.add_tmul, TensorProductOver.tmul_add]


-- @@ L128-130 verbatim
theorem extendInvAux_apply (m : M) (n : N) :
    extendInvAux R A B M N m n = TensorProductOver.tmul _
      ((GradedTensorProduct.intComparison R A B).bimoduleEquiv 1) (m ⊗ₜ[ℤ] n) := rfl


-- @@ L132-138 verbatim
theorem extendInvAux_balanced (r : R) (m : M) (n : N) :
    extendInvAux R A B M N (r • m) n = extendInvAux R A B M N m (r • n) := by
  rw [extendInvAux_apply, extendInvAux_apply, ground_smul_tmul_eq (A := A) (B := B) r m n,
    tmul_ground_smul_eq (A := A) (B := B) r m n,
    DGModuleCat.ExtendScalars.tmul_smul_eq, DGModuleCat.ExtendScalars.tmul_smul_eq,
    GradedTensorProduct.intComparison_tmul, GradedTensorProduct.intComparison_tmul,
    ← _root_.GradedTensorProduct.algebraMap_def, ← _root_.GradedTensorProduct.algebraMap_def']


-- @@ L140-144 verbatim
variable (R A B M N) in
/-- `M ⊗_R N → (A ⊗_R B) ⊗_{A ⊗_ℤ B} (M ⊗_ℤ N)`, `m ⊗ n ↦ 1 ⊗ (m ⊗ n)`. -/
def extendInv : ExternalTensorOver R A B M N →+ TensorProductOver (𝒜 ᵍ⊗[ℤ] ℬ)
    (GradedTensorProduct.intComparison R A B).Bimodule (M ⊗[ℤ] N) :=
  liftAddHom (A := A) (B := B) (extendInvAux R A B M N) extendInvAux_balanced


-- @@ L146-152 verbatim
theorem extendInv_comparisonAddHom (x : M ⊗[ℤ] N) :
    extendInv R A B M N (comparisonAddHom R A B M N x) = TensorProductOver.tmul _
      ((GradedTensorProduct.intComparison R A B).bimoduleEquiv 1) x := by
  induction x using DG.tensor_induction_on with
  | zero => rw [map_zero, map_zero, TensorProductOver.tmul_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, TensorProductOver.tmul_add]
  | tmul m n => rfl


-- @@ L154-191 expanded
variable (R A B M N) in
/-- **`(A ⊗_R B) ⊗_{A ⊗_ℤ B} (M ⊗_ℤ N) ≅ M ⊗_R N`** as dg modules over `A ᵍ⊗[R] B`:
extension of scalars along `A ᵍ⊗[ℤ] B → A ᵍ⊗[R] B` of the external tensor product over `ℤ` is
the external tensor product over `R`. -/
def extendEquiv :
    DGModuleEquiv (𝒜ᵣ ᵍ⊗[R] ℬᵣ)
      (TensorProductOver (𝒜 ᵍ⊗[ℤ] ℬ) (GradedTensorProduct.intComparison R A B).Bimodule (M ⊗[ℤ] N))
      (ExternalTensorOver R A B M N)
    where
  toLinearMap :=
    ((DGModuleCat.ExtendScalars.homEquiv _ _ _).symm (comparison R A B M N)).toLinearMap
  invFun := extendInv R A B M N
  left_inv
    y :=
    by
    change
      extendInv R A B M N
          ((DGModuleCat.ExtendScalars.homEquiv _ _ _).symm (comparison R A B M N) y) =
        y
    induction y using TensorProductOver.induction_on with
    | zero => rw [map_zero, map_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul x
      z =>
      obtain ⟨c, hc⟩ :=
        GradedTensorProduct.intComparison_surjective R A B
          ((GradedTensorProduct.intComparison R A B).bimoduleEquiv.symm x)
      have hx : x = op c • (GradedTensorProduct.intComparison R A B).bimoduleEquiv 1 := by
        rw [DGRingHom.Bimodule.op_smul_bimoduleEquiv, one_mul, hc, LinearEquiv.apply_symm_apply]
      rw [hx, TensorProductOver.op_smul_tmul, DGModuleCat.ExtendScalars.homEquiv_symm_tmul,
        LinearEquiv.symm_apply_apply, one_smul]
      exact extendInv_comparisonAddHom (c • z)
  right_inv
    t :=
    by
    change
      (DGModuleCat.ExtendScalars.homEquiv _ _ _).symm (comparison R A B M N)
          (extendInv R A B M N t) =
        t
    induction t using induction_on with
    | zero => rw [map_zero, map_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul' m _ n
      _ =>
      change
        (DGModuleCat.ExtendScalars.homEquiv _ _ _).symm (comparison R A B M N)
            (TensorProductOver.tmul _ ((GradedTensorProduct.intComparison R A B).bimoduleEquiv 1)
              (m ⊗ₜ[ℤ] n)) =
          tmul m n
      rw [DGModuleCat.ExtendScalars.homEquiv_symm_tmul, LinearEquiv.symm_apply_apply, one_smul]
      rfl
  map_mem' := ((DGModuleCat.ExtendScalars.homEquiv _ _ _).symm (comparison R A B M N)).map_mem
  map_d' := ((DGModuleCat.ExtendScalars.homEquiv _ _ _).symm (comparison R A B M N)).map_d


-- @@ L193-196 verbatim
theorem extendEquiv_tmul (x : (GradedTensorProduct.intComparison R A B).Bimodule)
    (m : M) (n : N) :
    extendEquiv R A B M N (TensorProductOver.tmul _ x (m ⊗ₜ[ℤ] n)) =
      (GradedTensorProduct.intComparison R A B).bimoduleEquiv.symm x • tmul m n := rfl


-- @@ L198-200 verbatim
theorem extendEquiv_symm_tmul (m : M) (n : N) :
    (extendEquiv R A B M N).symm (tmul m n) = TensorProductOver.tmul _
      ((GradedTensorProduct.intComparison R A B).bimoduleEquiv 1) (m ⊗ₜ[ℤ] n) := rfl


-- @@ L202-202 verbatim
end ExternalTensorOver


-- @@ L204-204 verbatim
end DG
