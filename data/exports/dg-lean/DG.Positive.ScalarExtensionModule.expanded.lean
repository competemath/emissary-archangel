import DG.Positive.ScalarExtension
import DG.Homotopy.ChangeOfRings
import DG.Homotopy.ExternalTensor


-- @@ L5-22 verbatim
/-!
# Base change of dg modules along `ℤ → K`

Let `K` be a commutative ring, `A` a dg ring and `K ⊗ A = K ᵍ⊗[ℤ] A` (`DG.ExtendScalars K A`).
For a dg `A`-module `M`, the tensor product `K ⊗_ℤ M` of dg abelian groups (`K` in degree `0`)
is a dg `K ⊗ A`-module: it is the external tensor product (`DG.ExternalTensor`) of the regular
module `K` and `M`, with `(k ⊗ a) • (k' ⊗ m) = k k' ⊗ a m` (`DG.ExtendScalars.tmul_smul_tmul`).
This gives the base-change functor `DG.ExtendScalars.baseChange K A : DGModuleCat A ⥤
DGModuleCat (K ⊗ A)`.

Base change is extension of scalars along `unitHom : A → K ⊗ A`, `a ↦ 1 ⊗ a`:
`(K ⊗ A) ⊗_A M ≅ K ⊗_ℤ M`, `x ⊗ m ↦ x • (1 ⊗ m)`, with inverse `k ⊗ m ↦ (k ⊗ 1) ⊗ m`
(`DG.ExtendScalars.extendScalarsEquiv`), naturally in `M`
(`DG.ExtendScalars.extendScalarsIso : extendScalars (unitHom K A) ≅ baseChange K A`).

No hypothesis on `K` (beyond commutativity) or on `A` is needed; dg modules are taken in the
universe of `K` and `A`.
-/


-- @@ L24-24 verbatim
open CategoryTheory MulOpposite

-- @@ L25-25 verbatim
open scoped TensorProduct


-- @@ L27-27 verbatim
universe u


-- @@ L29-29 verbatim
noncomputable section


-- @@ L31-31 verbatim
namespace DG


-- @@ L33-33 verbatim
namespace ExtendScalars


-- @@ L35-35 verbatim
variable (K : Type u) [CommRing K] (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]


-- @@ L37-37 verbatim
local notation "𝒦" => DGAlgebra.gradingSubmodule ℤ (DegreeZeroRing K)

-- @@ L38-38 verbatim
local notation "𝒜" => DGAlgebra.gradingSubmodule ℤ A


-- @@ L40-44 verbatim
/-- **Base change** `M ↦ K ⊗_ℤ M` of dg modules along `ℤ → K`: the external tensor product with
the regular module `K` (in degree `0`), a dg module over `K ⊗ A`. -/
def baseChange : DGModuleCat.{u} A ⥤ DGModuleCat.{u} (ExtendScalars K A) :=
  (ExternalTensor.functor (DegreeZeroRing K) A).obj
    (DGModuleCat.of (DegreeZeroRing K) (DegreeZeroRing K))


-- @@ L46-48 verbatim
@[simp]
theorem baseChange_obj (M : DGModuleCat.{u} A) :
    ((baseChange K A).obj M : Type u) = (DegreeZeroRing K ⊗[ℤ] M) := rfl


-- @@ L50-50 verbatim
variable {K A}

-- @@ L51-51 verbatim
variable {M : Type u} [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]


-- @@ L53-68 verbatim
omit [DGModule A M] in
/-- `(k ⊗ a) • (k' ⊗ m) = k k' ⊗ a m`: no sign, since `K` sits in degree `0`. -/
theorem tmul_smul_tmul (k k' : DegreeZeroRing K) (a : A) (m : M) :
    ((k ᵍ⊗ₜ[ℤ] a : ExtendScalars K A) • (k' ⊗ₜ[ℤ] m : DegreeZeroRing K ⊗[ℤ] M)) =
      (k * k') ⊗ₜ (a • m) := by
  induction a using DG.induction_on with
  | h_zero =>
    rw [GradedTensorProduct.tmul_zero, ExternalTensor.zero_smul', zero_smul,
      TensorProduct.tmul_zero]
  | h_homogeneous a =>
    rename_i j
    rw [ExternalTensor.tmul_smul_tmul k a.2 (DegreeZeroRing.mem_grading_zero K k') m, mul_zero,
      koszulSign_zero, one_smul, smul_eq_mul]
  | h_add a b ha hb =>
    rw [GradedTensorProduct.tmul_add, ExternalTensor.add_smul', ha, hb, add_smul,
      TensorProduct.tmul_add]


-- @@ L70-70 verbatim
variable (K A M)


-- @@ L72-85 expanded
/-- `m ↦ 1 ⊗ m`, a morphism of dg `A`-modules `M → K ⊗_ℤ M` (restricted along `unitHom`). -/
def unitMap : DGModuleHom A M (RestrictScalars (unitHom K A) (DegreeZeroRing K ⊗[ℤ] M))
    where
  toFun m := (RestrictScalars.addEquiv _).symm ((1 : DegreeZeroRing K) ⊗ₜ m)
  map_add' m m' := by rw [TensorProduct.tmul_add, map_add]
  map_smul' a
    m := by
    rw [RingHom.id_apply, RestrictScalars.smul_def, AddEquiv.apply_symm_apply, unitHom_apply,
      tmul_smul_tmul, mul_one]
  map_mem' {n m}
    hm := by
    have h := tmul_mem_grading (DegreeZeroRing.mem_grading_zero K 1) hm
    rwa [zero_add] at h
  map_d'
    m := by
    change (1 : DegreeZeroRing K) ⊗ₜ[ℤ] d m = d ((1 : DegreeZeroRing K) ⊗ₜ[ℤ] m)
    rw [d_tmul_of_mem (DegreeZeroRing.mem_grading_zero K 1), DegreeZeroRing.d_eq_zero,
      TensorProduct.zero_tmul, zero_add, koszulSign_zero, one_smul]


-- @@ L87-93 expanded
/-- `(K ⊗ A) ⊗_A M → K ⊗_ℤ M`, `x ⊗ m ↦ x • (1 ⊗ m)`, the morphism of dg `K ⊗ A`-modules
adjoint to `unitMap`. -/
def extendScalarsHom :
    DGModuleHom (ExtendScalars K A) (TensorProductOver A (unitHom K A).Bimodule M)
      (DegreeZeroRing K ⊗[ℤ] M) :=
  (DGModuleCat.ExtendScalars.homEquiv (unitHom K A) M (DegreeZeroRing K ⊗[ℤ] M)).symm
    (unitMap K A M)


-- @@ L95-95 verbatim
variable {K A M}


-- @@ L97-99 verbatim
theorem extendScalarsHom_tmul (x : ExtendScalars K A) (m : M) :
    extendScalarsHom K A M (TensorProductOver.tmul A ((unitHom K A).bimoduleEquiv x) m) =
      x • ((1 : DegreeZeroRing K) ⊗ₜ[ℤ] m) := rfl


-- @@ L101-113 verbatim
variable (K A M) in
/-- The biadditive map `(k, m) ↦ (k ⊗ 1) ⊗ m`. -/
def extendScalarsInvAux : DegreeZeroRing K →+ M →+ TensorProductOver A (unitHom K A).Bimodule M :=
  AddMonoidHom.mk'
    (fun k => AddMonoidHom.mk'
      (fun m => TensorProductOver.tmul A ((unitHom K A).bimoduleEquiv (k ᵍ⊗ₜ[ℤ] (1 : A))) m)
      fun m m' => TensorProductOver.tmul_add _ m m')
    fun k k' => by
      ext m
      change TensorProductOver.tmul A ((unitHom K A).bimoduleEquiv ((k + k') ᵍ⊗ₜ[ℤ] (1 : A))) m =
        TensorProductOver.tmul A ((unitHom K A).bimoduleEquiv (k ᵍ⊗ₜ[ℤ] (1 : A))) m +
          TensorProductOver.tmul A ((unitHom K A).bimoduleEquiv (k' ᵍ⊗ₜ[ℤ] (1 : A))) m
      rw [GradedTensorProduct.add_tmul, map_add, TensorProductOver.add_tmul]


-- @@ L115-119 verbatim
variable (K A M) in
/-- `K ⊗_ℤ M → (K ⊗ A) ⊗_A M`, `k ⊗ m ↦ (k ⊗ 1) ⊗ m`. -/
def extendScalarsInv : DegreeZeroRing K ⊗[ℤ] M →+ TensorProductOver A (unitHom K A).Bimodule M :=
  TensorProduct.liftAddHom (extendScalarsInvAux K A M) fun r k m => by
    rw [map_zsmul, AddMonoidHom.zsmul_apply, map_zsmul]


-- @@ L121-124 verbatim
omit [DGAddCommGroup M] [DGModule A M] in
theorem extendScalarsInv_tmul (k : DegreeZeroRing K) (m : M) :
    extendScalarsInv K A M (k ⊗ₜ m) =
      TensorProductOver.tmul A ((unitHom K A).bimoduleEquiv (k ᵍ⊗ₜ[ℤ] (1 : A))) m := rfl


-- @@ L126-140 verbatim
omit [DGModule A M] in
theorem extendScalarsInv_smul_one_tmul (x : ExtendScalars K A) (m : M) :
    extendScalarsInv K A M (x • ((1 : DegreeZeroRing K) ⊗ₜ[ℤ] m)) =
      TensorProductOver.tmul A ((unitHom K A).bimoduleEquiv x) m := by
  induction x using GradedTensorProduct.induction_on_tmul (R := ℤ) with
  | zero =>
    rw [ExternalTensor.zero_smul', map_zero, map_zero, TensorProductOver.zero_tmul]
  | @tmul i j k _ a ha =>
    rw [tmul_smul_tmul, mul_one, extendScalarsInv_tmul, ← TensorProductOver.op_smul_tmul,
      DGRingHom.Bimodule.op_smul_bimoduleEquiv, unitHom_apply,
      GradedTensorProduct.tmul_mul_tmul 𝒦 𝒜 (j := 0) (i' := 0) k (one_mem_grading (A := A))
        (DegreeZeroRing.mem_grading_zero K 1) a,
      zero_mul, koszulSign_zero, one_smul, mul_one, one_mul]
  | add x y hx hy =>
    rw [ExternalTensor.add_smul', map_add, hx, hy, map_add, TensorProductOver.add_tmul]


-- @@ L142-170 expanded
variable (K A M) in
/-- **Base change is extension of scalars**: `(K ⊗ A) ⊗_A M ≅ K ⊗_ℤ M` as dg `K ⊗ A`-modules,
`x ⊗ m ↦ x • (1 ⊗ m)`, with inverse `k ⊗ m ↦ (k ⊗ 1) ⊗ m`. -/
def extendScalarsEquiv :
    DGModuleEquiv (ExtendScalars K A) (TensorProductOver A (unitHom K A).Bimodule M)
      (DegreeZeroRing K ⊗[ℤ] M)
    where
  toLinearMap := (extendScalarsHom K A M).toLinearMap
  invFun := extendScalarsInv K A M
  left_inv
    y := by
    change extendScalarsInv K A M (extendScalarsHom K A M y) = y
    induction y using TensorProductOver.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul x
      m =>
      change
        extendScalarsInv K A M
            (extendScalarsHom K A M
              (TensorProductOver.tmul A
                ((unitHom K A).bimoduleEquiv ((unitHom K A).bimoduleEquiv.symm x)) m)) =
          _
      rw [extendScalarsHom_tmul, extendScalarsInv_smul_one_tmul, LinearEquiv.apply_symm_apply]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  right_inv
    z := by
    change extendScalarsHom K A M (extendScalarsInv K A M z) = z
    induction z using TensorProduct.inductionOn with
    | tmul k m =>
      rw [extendScalarsInv_tmul, extendScalarsHom_tmul, tmul_smul_tmul, mul_one, one_smul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  map_mem' := (extendScalarsHom K A M).map_mem
  map_d' := (extendScalarsHom K A M).map_d


-- @@ L172-174 verbatim
theorem extendScalarsEquiv_tmul (x : ExtendScalars K A) (m : M) :
    extendScalarsEquiv K A M (TensorProductOver.tmul A ((unitHom K A).bimoduleEquiv x) m) =
      x • ((1 : DegreeZeroRing K) ⊗ₜ[ℤ] m) := rfl


-- @@ L176-178 verbatim
theorem extendScalarsEquiv_symm_tmul (k : DegreeZeroRing K) (m : M) :
    (extendScalarsEquiv K A M).symm (k ⊗ₜ m) =
      TensorProductOver.tmul A ((unitHom K A).bimoduleEquiv (k ᵍ⊗ₜ[ℤ] (1 : A))) m := rfl


-- @@ L180-193 expanded
theorem extendScalarsEquiv_naturality {M' : Type u} [AddCommGroup M'] [DGAddCommGroup M']
    [Module A M'] [DGModule A M'] (g : DGModuleHom A M M')
    (y : TensorProductOver A (unitHom K A).Bimodule M) :
    extendScalarsEquiv K A M' (DGModuleHom.lTensor (ExtendScalars K A) _ g y) =
      ExternalTensor.tensorDGHom
        (DGModuleHom.id : DGModuleHom (DegreeZeroRing K) (DegreeZeroRing K) (DegreeZeroRing K)) g
        (extendScalarsEquiv K A M y) :=
  by
  induction y using TensorProductOver.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul x
    m =>
    rw [DGModuleHom.lTensor_tmul, ← LinearEquiv.apply_symm_apply (unitHom K A).bimoduleEquiv x,
      extendScalarsEquiv_tmul, extendScalarsEquiv_tmul, map_smul, ExternalTensor.tensorDGHom_tmul]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]


-- @@ L195-200 verbatim
variable (K A) in
/-- **Base change is extension of scalars along `unitHom`**, naturally:
`extendScalars (unitHom K A) ≅ baseChange K A`, i.e. `(K ⊗ A) ⊗_A M ≅ K ⊗_ℤ M`. -/
def extendScalarsIso : DGModuleCat.extendScalars.{u} (unitHom K A) ≅ baseChange K A :=
  NatIso.ofComponents (fun M => (extendScalarsEquiv K A M).toDGModuleCatIso) fun {_ _} g =>
    DGModuleCat.hom_ext_apply fun y => extendScalarsEquiv_naturality g.hom y


-- @@ L202-205 verbatim
theorem extendScalarsIso_hom_app_tmul (M : DGModuleCat.{u} A) (x : ExtendScalars K A) (m : M) :
    (extendScalarsIso K A).hom.app M
        (TensorProductOver.tmul A ((unitHom K A).bimoduleEquiv x) m) =
      x • ((1 : DegreeZeroRing K) ⊗ₜ[ℤ] (m : M)) := rfl


-- @@ L207-207 verbatim
end ExtendScalars


-- @@ L209-209 verbatim
end DG


-- @@ L211-211 verbatim
end
