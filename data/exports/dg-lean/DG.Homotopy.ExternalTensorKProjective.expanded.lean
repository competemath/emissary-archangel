import DG.Module.HomTensor
import DG.Homotopy.ExternalTensorOverExtend
import DG.Homotopy.ExternalTensor
import DG.Category.Derived.ExtendScalars


-- @@ L6-24 verbatim
/-!
# The external tensor product of K-projective modules is K-projective

Let `A`, `B` be dg rings and `C = A ᵍ⊗[ℤ] B`.

* `DG.IsKProjective.tensorProductOver`: for a dg `(C, B)`-bimodule `X` which is K-projective over
  `C` and a K-projective dg `B`-module `P'`, `X ⊗_B P'` is K-projective over `C`. Proof: by the
  `HOM`–`⊗` adjunction (`DG.TensorProductOver.curryEquiv`),
  `HOM_C(X ⊗_B P', N) ≅ HOM_B(P', HOM_C(X, N))`, which is acyclic for acyclic `N`.
* `M ⊠ B = M ⊗[ℤ] B` with the right action of `B` on the second factor is a dg `(C, B)`-bimodule
  (local instances in `DG.ExternalTensor.RightRegular`); it is extension of scalars of `M` along
  `a ↦ a ⊗ 1` (`DG.ExternalTensor.RightRegular.extendEquiv`, with the Koszul sign
  `m ⊗ b ↦ (-1)^{|m||b|} (1 ⊗ b) ⊗ m` in the inverse), hence K-projective over `C` when `M` is
  K-projective over `A`; and `(M ⊠ B) ⊗_B N ≅ M ⊠ N` (`DG.ExternalTensor.RightRegular.tensorEquiv`).
* **`DG.ExternalTensor.isKProjective`**: if `P` and `P'` are K-projective over `A` and `B`, then
  `P ⊠ P'` is K-projective over `A ⊗ B`; and over a commutative ring `R`,
  `DG.ExternalTensorOver.isKProjective`: `P ⊗_R P'` is K-projective over `A ᵍ⊗[R] B` (it is
  extension of scalars of `P ⊠ P'`, `DG.ExternalTensorOver.extendEquiv`).
-/


-- @@ L26-26 verbatim
open CategoryTheory MulOpposite

-- @@ L27-27 verbatim
open scoped TensorProduct


-- @@ L29-29 verbatim
set_option linter.unusedSectionVars false


-- @@ L31-31 verbatim
universe u


-- @@ L33-33 verbatim
noncomputable section


-- @@ L35-35 verbatim
namespace DG


-- @@ L37-37 verbatim
/-! ### `X ⊗_B P` for a K-projective bimodule `X` and a K-projective module `P` -/


-- @@ L39-39 verbatim
section TensorProductOver


-- @@ L41-41 verbatim
open DGModule DGModule.HOM DGModule.HOM.LeftAction


-- @@ L43-47 verbatim
private theorem isAcyclic_of_dgAddEquiv' {M N : Type*} [AddCommGroup M] [DGAddCommGroup M]
    [AddCommGroup N] [DGAddCommGroup N] (e : DGAddEquiv M N) (h : IsAcyclic N) : IsAcyclic M := by
  refine DG.isAcyclic_iff.mpr fun n m hm hdm => ?_
  obtain ⟨y, hy, hdy⟩ := h.exists_d_eq (e.map_mem hm) (by rw [← e.map_d, hdm, map_zero])
  exact ⟨e.symm y, e.symm.map_mem hy, e.injective (by rw [e.map_d, e.apply_symm_apply, hdy])⟩


-- @@ L49-53 verbatim
variable {C B : Type u} [Ring C] [DGAddCommGroup C] [DGRing C] [Ring B] [DGAddCommGroup B]
  [DGRing B]
  {X : Type u} [AddCommGroup X] [DGAddCommGroup X] [Module C X] [Module Bᵐᵒᵖ X]
  [DGBimodule C B X]
  {P : Type u} [AddCommGroup P] [DGAddCommGroup P] [Module B P] [DGModule B P]


-- @@ L55-61 verbatim
/-- **`X ⊗_B P` is K-projective** for a dg `(C, B)`-bimodule `X` which is K-projective over `C`
and a K-projective dg `B`-module `P`. -/
theorem IsKProjective.tensorProductOver (hX : IsKProjective.{u} C X)
    (hP : IsKProjective.{u} B P) : IsKProjective.{u} C (TensorProductOver B X P) :=
  isKProjective_iff_isAcyclic_hom.mpr fun N _ _ _ _ hN =>
    isAcyclic_of_dgAddEquiv' (TensorProductOver.curryEquiv C B X P N)
      (isKProjective_iff_isAcyclic_hom.mp hP _ (hX.isAcyclic_hom hN))


-- @@ L63-63 verbatim
end TensorProductOver


-- @@ L65-65 verbatim
namespace ExternalTensor


-- @@ L67-68 verbatim
variable {A B : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B]
  [DGRing B]


-- @@ L70-70 verbatim
local notation "𝒜" => DGAlgebra.gradingSubmodule ℤ A

-- @@ L71-71 verbatim
local notation "ℬ" => DGAlgebra.gradingSubmodule ℤ B

-- @@ L72-72 verbatim
local notation "AB" => 𝒜 ᵍ⊗[ℤ] ℬ


-- @@ L74-77 verbatim
private theorem ks_val (n : ℤ) : (koszulSign n : ℤ) = if Even n then 1 else -1 := by
  split_ifs with h
  · rw [koszulSign, Int.negOnePow_even n h]; rfl
  · rw [koszulSign, Int.negOnePow_odd n (Int.not_even_iff_odd.mp h)]; rfl


-- @@ L79-79 verbatim
/-! ### `M ⊠ B` as a bimodule -/


-- @@ L81-81 verbatim
namespace RightRegular


-- @@ L83-83 verbatim
variable {M : Type u} [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]


-- @@ L85-88 verbatim
variable (B M) in
/-- Right multiplication on the second factor, `m ⊗ b' ↦ m ⊗ b' b`. -/
def rightAct (b : B) : (M ⊗[ℤ] B) →+ (M ⊗[ℤ] B) :=
  DG.tensorMap (AddMonoidHom.id M) (AddMonoidHom.mulRight b)


-- @@ L90-91 verbatim
theorem rightAct_tmul (b : B) (m : M) (b' : B) :
    rightAct B M b (TensorProduct.tmul ℤ m b') = TensorProduct.tmul ℤ m (b' * b) := rfl


-- @@ L93-109 verbatim
variable (B M) in
/-- The right action of `B` as a ring homomorphism `Bᵐᵒᵖ → End(M ⊠ B)`. -/
def rightActHom : Bᵐᵒᵖ →+* AddMonoid.End ((M ⊗[ℤ] B)) where
  toFun b := rightAct B M b.unop
  map_one' := DG.tensor_addHom_ext fun m n => by
    change (m : M) ⊗ₜ[ℤ] ((n : B) * 1) = (m : M) ⊗ₜ[ℤ] (n : B)
    rw [mul_one]
  map_mul' b b' := DG.tensor_addHom_ext fun m n => by
    change (m : M) ⊗ₜ[ℤ] ((n : B) * (b * b').unop) = (m : M) ⊗ₜ[ℤ] ((n : B) * b'.unop * b.unop)
    rw [MulOpposite.unop_mul, mul_assoc]
  map_zero' := DG.tensor_addHom_ext fun m n => by
    change (m : M) ⊗ₜ[ℤ] ((n : B) * 0) = 0
    rw [mul_zero, TensorProduct.tmul_zero]
  map_add' b b' := DG.tensor_addHom_ext fun m n => by
    change (m : M) ⊗ₜ[ℤ] ((n : B) * (b + b').unop) =
      (m : M) ⊗ₜ[ℤ] ((n : B) * b.unop) + (m : M) ⊗ₜ[ℤ] ((n : B) * b'.unop)
    rw [MulOpposite.unop_add, mul_add, TensorProduct.tmul_add]


-- @@ L111-112 verbatim
local instance instModuleOp : Module Bᵐᵒᵖ ((M ⊗[ℤ] B)) :=
  Module.compHom ((M ⊗[ℤ] B)) (rightActHom B M)


-- @@ L114-114 verbatim
theorem op_smul_def (b : B) (x : (M ⊗[ℤ] B)) : op b • x = rightAct B M b x := rfl


-- @@ L116-117 verbatim
theorem op_smul_tmul (b : B) (m : M) (b' : B) :
    op b • (TensorProduct.tmul ℤ m b' : (M ⊗[ℤ] B)) = TensorProduct.tmul ℤ m (b' * b) := rfl


-- @@ L119-142 verbatim
local instance instDGRightModule : DGRightModule B ((M ⊗[ℤ] B)) where
  op_smul_mem' {i j b x} hb hx := by
    have := DG.map_mem_grading_of_tmul (Y := M ⊗[ℤ] B) (rightAct B M b) i
      (fun {i' j' m n} hm hn => by
        rw [show i' + j' + i = i' + (j' + i) by ring]
        exact DG.tmul_mem_grading hm (mul_mem_grading hn hb)) hx
    exact this
  d_op_smul' {j x} hx b := by
    change d (rightAct B M b x) = rightAct B M b (d x) + koszulSign j • rightAct B M (d b) x
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, k, rfl, m, hm, n, hn, rfl⟩ := hx
      change d ((m ⊗ₜ[ℤ] (n * b) : M ⊗[ℤ] B)) =
        rightAct B M b (d (m ⊗ₜ[ℤ] n : M ⊗[ℤ] B)) + koszulSign (i + k) • (m ⊗ₜ[ℤ] (n * d b))
      rw [DG.d_tmul_of_mem hm, DG.d_tmul_of_mem hm, d_mul hn, map_add, map_units_zsmul]
      change _ = (d m ⊗ₜ[ℤ] (n * b) + koszulSign i • (m ⊗ₜ[ℤ] (d n * b))) + _
      rw [TensorProduct.tmul_add, smul_add, Units.smul_def, Units.smul_def, Units.smul_def,
        Units.smul_def, ← TensorProduct.tmul_smul, ← TensorProduct.tmul_smul,
        ← TensorProduct.tmul_smul, smul_smul, ← Units.val_mul, ← koszulSign_add, add_assoc]
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add, d_add, hx, hy, d_add, map_add, map_add, smul_add]
      abel
    | neg x _ hx => rw [map_neg, d_neg, hx, d_neg, map_neg, map_neg, smul_neg, neg_add]


-- @@ L144-162 verbatim
local instance instSMulCommClass : SMulCommClass AB Bᵐᵒᵖ ((M ⊗[ℤ] B)) where
  smul_comm c b x := by
    change c • rightAct B M b.unop x = rightAct B M b.unop (c • x)
    induction c using GradedTensorProduct.induction_on_tmul (R := ℤ) with
    | zero => rw [ExternalTensor.zero_smul', ExternalTensor.zero_smul', map_zero]
    | add c c' hc hc' =>
      rw [ExternalTensor.add_smul', ExternalTensor.add_smul', map_add, hc, hc']
    | @tmul i k a ha b'' hb'' =>
      induction x using DG.tensor_induction_on with
      | zero => simp only [map_zero, ExternalTensor.smul_zero']
      | add x y hx hy =>
        rw [map_add, ExternalTensor.smul_add', hx, hy, ExternalTensor.smul_add', map_add]
      | tmul m n =>
        change (a ᵍ⊗ₜ[ℤ] b'' : AB) • ((m : M) ⊗ₜ[ℤ] ((n : B) * b.unop)) =
          rightAct B M b.unop ((a ᵍ⊗ₜ[ℤ] b'' : AB) • ((m : M) ⊗ₜ[ℤ] (n : B)))
        rw [ExternalTensor.tmul_smul_tmul a hb'' m.2, ExternalTensor.tmul_smul_tmul a hb'' m.2,
          map_units_zsmul]
        change _ = koszulSign _ • ((a • (m : M)) ⊗ₜ[ℤ] (b'' * (n : B) * b.unop))
        rw [smul_eq_mul, mul_assoc]


-- @@ L164-164 verbatim
local instance instDGBimodule : DGBimodule AB B ((M ⊗[ℤ] B)) := DGBimodule.mk'


-- @@ L166-166 verbatim
/-! #### `(M ⊠ B) ⊗_B N ≅ M ⊠ N` -/


-- @@ L168-168 verbatim
variable {N : Type u} [AddCommGroup N] [DGAddCommGroup N] [Module B N] [DGModule B N]


-- @@ L170-178 verbatim
variable (M N) in
/-- The biadditive map `(m ⊗ b, n) ↦ m ⊗ b n`. -/
def tensorAux : (M ⊗[ℤ] B) →+ N →+ M ⊗[ℤ] N :=
  (AddMonoidHom.mk' (fun n : N =>
      DG.tensorMap (AddMonoidHom.id M) ((smulAddHom B N).flip n))
    fun n n' => DG.tensor_addHom_ext fun m b => by
      change (m : M) ⊗ₜ[ℤ] ((b : B) • (n + n')) =
        (m : M) ⊗ₜ[ℤ] ((b : B) • n) + (m : M) ⊗ₜ[ℤ] ((b : B) • n')
      rw [smul_add, TensorProduct.tmul_add]).flip


-- @@ L180-181 verbatim
theorem tensorAux_tmul (m : M) (b : B) (n : N) :
    tensorAux M N (TensorProduct.tmul ℤ m b) n = m ⊗ₜ[ℤ] (b • n) := rfl


-- @@ L183-192 verbatim
theorem tensorAux_balanced (b : B) (x : (M ⊗[ℤ] B)) (n : N) :
    tensorAux M N (op b • x) n = tensorAux M N x (b • n) := by
  induction x using DG.tensor_induction_on with
  | zero => simp only [smul_zero, map_zero, AddMonoidHom.zero_apply]
  | add x y hx hy => rw [smul_add, map_add, map_add, AddMonoidHom.add_apply,
      AddMonoidHom.add_apply, hx, hy]
  | tmul m b' =>
    change tensorAux M N (TensorProduct.tmul ℤ (m : M) ((b' : B) * b)) n =
      tensorAux M N (TensorProduct.tmul ℤ (m : M) (b' : B)) (b • n)
    rw [tensorAux_tmul, tensorAux_tmul, mul_smul]


-- @@ L194-197 verbatim
variable (M N) in
/-- `(M ⊠ B) ⊗_B N → M ⊠ N`, `(m ⊗ b) ⊗ n ↦ m ⊗ b n`, as an additive map. -/
def tensorHom : TensorProductOver B ((M ⊗[ℤ] B)) N →+ M ⊗[ℤ] N :=
  TensorProductOver.lift (tensorAux M N) tensorAux_balanced


-- @@ L199-200 verbatim
theorem tensorHom_tmul (m : M) (b : B) (n : N) :
    tensorHom M N (TensorProductOver.tmul B (TensorProduct.tmul ℤ m b) n) = m ⊗ₜ[ℤ] (b • n) := rfl


-- @@ L202-221 verbatim
theorem tensorAux_smul (c : AB) (x : (M ⊗[ℤ] B)) (n : N) :
    tensorAux M N (c • x) n = c • tensorAux M N x n := by
  induction c using GradedTensorProduct.induction_on_tmul (R := ℤ) with
  | zero => rw [ExternalTensor.zero_smul', map_zero, AddMonoidHom.zero_apply,
      ExternalTensor.zero_smul']
  | add c c' hc hc' => rw [ExternalTensor.add_smul', map_add, AddMonoidHom.add_apply, hc, hc',
      ExternalTensor.add_smul']
  | @tmul i k a ha b'' hb'' =>
    induction x using DG.tensor_induction_on with
    | zero => rw [ExternalTensor.smul_zero', map_zero, AddMonoidHom.zero_apply,
        ExternalTensor.smul_zero']
    | add x y hx hy => rw [ExternalTensor.smul_add', map_add, AddMonoidHom.add_apply, hx, hy,
        map_add, AddMonoidHom.add_apply, ExternalTensor.smul_add']
    | tmul m b =>
      change tensorAux M N ((a ᵍ⊗ₜ[ℤ] b'' : AB) • ((m : M) ⊗ₜ[ℤ] (b : B))) n =
        (a ᵍ⊗ₜ[ℤ] b'' : AB) • ((m : M) ⊗ₜ[ℤ] ((b : B) • n))
      rw [ExternalTensor.tmul_smul_tmul a hb'' m.2, ExternalTensor.tmul_smul_tmul a hb'' m.2,
        Units.smul_def, map_zsmul, AddMonoidHom.zsmul_apply, Units.smul_def]
      change ((koszulSign (k * _) : ℤ)) • ((a • (m : M)) ⊗ₜ[ℤ] ((b'' • (b : B)) • n)) = _
      rw [smul_assoc]


-- @@ L223-228 verbatim
theorem tensorAux_mem {i j : ℤ} {x : (M ⊗[ℤ] B)} (hx : x ∈ grading i) {n : N}
    (hn : n ∈ grading j) : tensorAux M N x n ∈ grading (i + j) :=
  DG.map_mem_grading_of_tmul (Y := M ⊗[ℤ] N) ((tensorAux M N).flip n) j
    (fun {i' j' m b} hm hb => by
      have := DG.tmul_mem_grading hm (smul_mem_grading hb hn)
      rwa [← add_assoc] at this) hx


-- @@ L230-254 verbatim
theorem d_tensorAux {i : ℤ} {x : (M ⊗[ℤ] B)} (hx : x ∈ grading i) (n : N) :
    d (tensorAux M N x n) = tensorAux M N (d x) n + koszulSign i • tensorAux M N x (d n) := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i', k, rfl, m, hm, b, hb, rfl⟩ := hx
    have e2 : tensorAux M N (d (m ⊗ₜ[ℤ] b : M ⊗[ℤ] B)) n =
        d m ⊗ₜ[ℤ] (b • n) + koszulSign i' • (m ⊗ₜ[ℤ] (d b • n)) := by
      rw [DG.d_tmul_of_mem hm]
      change ((tensorAux M N).flip n) (d m ⊗ₜ[ℤ] b + koszulSign i' • (m ⊗ₜ[ℤ] d b)) = _
      rw [map_add, map_units_zsmul]
      rfl
    change d ((m ⊗ₜ[ℤ] (b • n) : M ⊗[ℤ] N)) =
      tensorAux M N (d (m ⊗ₜ[ℤ] b : M ⊗[ℤ] B)) n + koszulSign (i' + k) • (m ⊗ₜ[ℤ] (b • d n))
    rw [e2, DG.d_tmul_of_mem hm, d_smul hb]
    simp only [TensorProduct.tmul_add, Units.smul_def, TensorProduct.tmul_smul, smul_add,
      smul_smul, koszulSign_add, Units.val_mul, add_assoc]
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [map_add, AddMonoidHom.add_apply, smul_add] at hx hy ⊢
    rw [hx, hy]
    abel
  | neg x _ hx =>
    simp only [map_neg, AddMonoidHom.neg_apply, smul_neg] at hx ⊢
    rw [hx]
    abel


-- @@ L256-275 verbatim
variable (M N) in
/-- `M ⊠ N → (M ⊠ B) ⊗_B N`, `m ⊗ n ↦ (m ⊗ 1) ⊗ n`. -/
def tensorInv : M ⊗[ℤ] N →+ TensorProductOver B ((M ⊗[ℤ] B)) N :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun m => AddMonoidHom.mk'
        (fun n => TensorProductOver.tmul B (TensorProduct.tmul ℤ m (1 : B) : (M ⊗[ℤ] B)) n)
        fun n n' => TensorProductOver.tmul_add _ _ _)
      fun m m' => by
        ext n
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
        change TensorProductOver.tmul B ((m + m') ⊗ₜ[ℤ] (1 : B) : (M ⊗[ℤ] B)) n = _
        rw [TensorProduct.add_tmul]
        exact TensorProductOver.add_tmul _ _ _)
    fun r m n => by
      change TensorProductOver.tmul B (TensorProduct.tmul ℤ (r • m) (1 : B) : (M ⊗[ℤ] B)) n =
        TensorProductOver.tmul B (TensorProduct.tmul ℤ m (1 : B) : (M ⊗[ℤ] B)) (r • n)
      have h : (TensorProduct.tmul ℤ (r • m) (1 : B) : (M ⊗[ℤ] B)) =
          r • TensorProduct.tmul ℤ m (1 : B) :=
        (TensorProduct.smul_tmul' r m (1 : B)).symm
      rw [h, TensorProductOver.zsmul_tmul, TensorProductOver.tmul_zsmul]


-- @@ L277-280 verbatim
theorem tensorInv_tmul (m : M) (n : N) :
    tensorInv M N (m ⊗ₜ n) =
      TensorProductOver.tmul B (TensorProduct.tmul ℤ m (1 : B) : (M ⊗[ℤ] B)) n :=
  rfl


-- @@ L282-316 expanded
variable (M N) in
/-- **`(M ⊠ B) ⊗_B N ≅ M ⊠ N`** as dg modules over `A ⊗ B`, `(m ⊗ b) ⊗ n ↦ m ⊗ b n`. -/
def tensorEquiv : DGModuleEquiv AB (TensorProductOver B ((M ⊗[ℤ] B)) N) (M ⊗[ℤ] N)
    where
  toFun := tensorHom M N
  invFun := tensorInv M N
  map_add' := map_add _
  map_smul' c
    y := by
    induction y using TensorProductOver.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
    | tmul x n =>
      rw [TensorProductOver.smul_tmul]
      exact tensorAux_smul c x n
  left_inv
    y := by
    induction y using TensorProductOver.induction_on with
    | zero => rw [map_zero, map_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul x n =>
      induction x using DG.tensor_induction_on with
      | zero => rw [TensorProductOver.zero_tmul, map_zero, map_zero]
      | add x y hx hy => rw [TensorProductOver.add_tmul, map_add, map_add, hx, hy]
      | tmul m
        b =>
        change
          tensorInv M N ((m : M) ⊗ₜ[ℤ] ((b : B) • n)) =
            TensorProductOver.tmul B (TensorProduct.tmul ℤ (m : M) (b : B)) n
        rw [tensorInv_tmul, ← TensorProductOver.op_smul_tmul, op_smul_tmul, one_mul]
  right_inv
    z := by
    induction z using TensorProduct.inductionOn with
    | tmul m n => rw [tensorInv_tmul, tensorHom_tmul, one_smul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  map_mem' {k y}
    hy :=
    TensorProductOver.lift_mem (tensorAux M N) tensorAux_balanced (fun hx hn => tensorAux_mem hx hn)
      hy
  map_d'
    y :=
    TensorProductOver.lift_d (tensorAux M N) tensorAux_balanced (fun hx n => d_tensorAux hx n) y


-- @@ L318-318 verbatim
/-! #### `M ⊠ B` is extension of scalars along `a ↦ a ⊗ 1` -/


-- @@ L320-322 expanded
variable (A B) in
/-- `a ↦ a ⊗ 1`, a morphism of dg rings `A → A ⊗ B`. -/
abbrev includeLeft : DGRingHom A AB :=
  (GradedTensorProduct.includeLeftDGAlgHom ℤ A B).toDGRingHom


-- @@ L324-324 verbatim
theorem includeLeft_apply (a : A) : includeLeft A B a = (a ᵍ⊗ₜ[ℤ] (1 : B) : AB) := rfl


-- @@ L326-348 expanded
variable (A B M) in
/-- `m ↦ m ⊗ 1`, a morphism of dg `A`-modules `M → M ⊠ B` (restricted along `a ↦ a ⊗ 1`). -/
def unitMap : DGModuleHom A M (RestrictScalars (includeLeft A B) ((M ⊗[ℤ] B)))
    where
  toFun m := (RestrictScalars.addEquiv _).symm (TensorProduct.tmul ℤ m (1 : B))
  map_add' m m' := TensorProduct.add_tmul _ _ _
  map_smul' a
    m :=
    by
    rw [RingHom.id_apply, RestrictScalars.smul_def, AddEquiv.apply_symm_apply, includeLeft_apply]
    change (a • m) ⊗ₜ[ℤ] (1 : B) = (a ᵍ⊗ₜ[ℤ] (1 : B) : AB) • (m ⊗ₜ[ℤ] (1 : B) : M ⊗[ℤ] B)
    induction m using DG.induction_on with
    | h_zero => rw [smul_zero, TensorProduct.zero_tmul, ExternalTensor.smul_zero']
    | h_homogeneous m =>
      rw [ExternalTensor.tmul_smul_tmul a (one_mem_grading (A := B)) m.2, zero_mul, koszulSign_zero,
        one_smul, one_smul]
    | h_add m m' hm hm' =>
      rw [smul_add, TensorProduct.add_tmul, TensorProduct.add_tmul, hm, hm',
        ExternalTensor.smul_add']
  map_mem' {k m}
    hm := by
    have := DG.tmul_mem_grading hm (one_mem_grading (A := B))
    rwa [add_zero] at this
  map_d'
    m := by
    change (d m) ⊗ₜ[ℤ] (1 : B) = d (m ⊗ₜ[ℤ] (1 : B) : M ⊗[ℤ] B)
    rw [DG.d_tmul, d_one, TensorProduct.tmul_zero, add_zero]


-- @@ L350-353 expanded
variable (A B M) in
/-- `(A ⊗ B) ⊗_A M → M ⊠ B`, `x ⊗ m ↦ x • (m ⊗ 1)`. -/
def extendHom : DGModuleHom AB (TensorProductOver A (includeLeft A B).Bimodule M) (M ⊗[ℤ] B) :=
  (DGModuleCat.ExtendScalars.homEquiv (includeLeft A B) M ((M ⊗[ℤ] B))).symm (unitMap A B M)


-- @@ L355-357 verbatim
theorem extendHom_tmul (x : AB) (m : M) :
    extendHom A B M (TensorProductOver.tmul A ((includeLeft A B).bimoduleEquiv x) m) =
      x • (TensorProduct.tmul ℤ m (1 : B) : (M ⊗[ℤ] B)) := rfl


-- @@ L359-373 verbatim
variable (A M) in
/-- `M ⊠ B → (A ⊗ B) ⊗_A M`, `m ⊗ b ↦ (-1)^{|m||b|} (1 ⊗ b) ⊗ m`. -/
def extendInv : (M ⊗[ℤ] B) →+ TensorProductOver A (includeLeft A B).Bimodule M :=
  DG.tensorLiftHomogeneous fun i j =>
    AddMonoidHom.mk' (fun m => AddMonoidHom.mk'
        (fun b => koszulSign (i * j) •
          TensorProductOver.tmul A ((includeLeft A B).bimoduleEquiv ((1 : A) ᵍ⊗ₜ[ℤ] (b : B)))
            (m : M))
        fun b b' => by
          simp only [AddSubgroup.coe_add, GradedTensorProduct.tmul_add, map_add,
            TensorProductOver.add_tmul, smul_add])
      fun m m' => by
        ext b
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
        simp only [AddSubgroup.coe_add, TensorProductOver.tmul_add, smul_add]


-- @@ L375-379 verbatim
theorem extendInv_tmul {i j : ℤ} {m : M} (hm : m ∈ grading i) {b : B} (hb : b ∈ grading j) :
    extendInv A M (TensorProduct.tmul ℤ m b : (M ⊗[ℤ] B)) =
      koszulSign (i * j) •
        TensorProductOver.tmul A ((includeLeft A B).bimoduleEquiv ((1 : A) ᵍ⊗ₜ[ℤ] b)) m :=
  DG.tensorLiftHomogeneous_tmul _ hm hb


-- @@ L381-430 expanded
variable (A B M) in
/-- **`M ⊠ B` is extension of scalars of `M` along `a ↦ a ⊗ 1`**:
`(A ⊗ B) ⊗_A M ≅ M ⊠ B`, `x ⊗ m ↦ x • (m ⊗ 1)`. -/
def extendEquiv : DGModuleEquiv AB (TensorProductOver A (includeLeft A B).Bimodule M) (M ⊗[ℤ] B)
    where
  toLinearMap := (extendHom A B M).toLinearMap
  invFun := extendInv A M
  left_inv
    y := by
    change extendInv A M (extendHom A B M y) = y
    induction y using TensorProductOver.induction_on with
    | zero => rw [map_zero, map_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul x m =>
      rw [← LinearEquiv.apply_symm_apply (includeLeft A B).bimoduleEquiv x]
      induction ((includeLeft A B).bimoduleEquiv.symm x) using
        GradedTensorProduct.induction_on_tmul (R := ℤ) with
      | zero => rw [map_zero, TensorProductOver.zero_tmul, map_zero, map_zero]
      | add c c' hc hc' => rw [map_add, TensorProductOver.add_tmul, map_add, map_add, hc, hc']
      | @tmul i k a ha b hb =>
        induction m using DG.induction_on with
        | h_zero => rw [TensorProductOver.tmul_zero, map_zero, map_zero]
        | h_add m m' hm hm' => rw [TensorProductOver.tmul_add, map_add, map_add, hm, hm']
        | @h_homogeneous p m =>
          rw [extendHom_tmul]
          rw [ExternalTensor.tmul_smul_tmul a hb m.2, map_units_zsmul, smul_eq_mul, mul_one]
          change koszulSign (k * p) • extendInv A M (TensorProduct.tmul ℤ (a • (m : M)) b) = _
          rw [extendInv_tmul (smul_mem_grading ha m.2) hb, smul_smul, ← koszulSign_add, ←
            TensorProductOver.op_smul_tmul, DGRingHom.Bimodule.op_smul_bimoduleEquiv,
            includeLeft_apply, GradedTensorProduct.tmul_mul_tmul 𝒜 ℬ (1 : A) hb ha (1 : B), one_mul,
            mul_one]
          rw [show
              (includeLeft A B).bimoduleEquiv (koszulSign (k * i) • (a ᵍ⊗ₜ[ℤ] b : AB)) =
                koszulSign (k * i) • (includeLeft A B).bimoduleEquiv (a ᵍ⊗ₜ[ℤ] b)
              by rw [Units.smul_def, Units.smul_def, map_zsmul],
            TensorProductOver.units_smul_tmul, smul_smul, ← koszulSign_add,
            koszulSign_even ⟨k * p + i * k, by ring⟩, one_smul]
  right_inv
    z := by
    change extendHom A B M (extendInv A M z) = z
    induction z using DG.tensor_induction_on with
    | zero => rw [map_zero, map_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | @tmul i j m
      b =>
      change
        extendHom A B M (extendInv A M (TensorProduct.tmul ℤ (m : M) (b : B))) =
          TensorProduct.tmul ℤ (m : M) (b : B)
      rw [extendInv_tmul m.2 b.2, Units.smul_def, map_zsmul, extendHom_tmul]
      change
        ((koszulSign (i * j) : ℤ)) •
            ((1 : A) ᵍ⊗ₜ[ℤ] (b : B) : AB) • ((m : M) ⊗ₜ[ℤ] (1 : B) : M ⊗[ℤ] B) =
          (m : M) ⊗ₜ[ℤ] (b : B)
      rw [ExternalTensor.tmul_smul_tmul (1 : A) b.2 m.2, one_smul, smul_eq_mul, mul_one, ←
        Units.smul_def, smul_smul, ← koszulSign_add, mul_comm j i, ← two_mul,
        koszulSign_even (even_two_mul _), one_smul]
  map_mem' := (extendHom A B M).map_mem
  map_d' := (extendHom A B M).map_d


-- @@ L432-436 verbatim
/-- `M ⊠ B` is K-projective over `A ⊗ B` when `M` is K-projective over `A`. -/
theorem isKProjective (hM : IsKProjective.{u} A M) :
    IsKProjective.{u} AB ((M ⊗[ℤ] B)) :=
  (IsKProjective.extendScalars (includeLeft A B) (P := DGModuleCat.of A M) hM).of_dgModuleEquiv
    (extendEquiv A B M).symm


-- @@ L438-439 verbatim
variable {P : Type u} [AddCommGroup P] [DGAddCommGroup P] [Module A P] [DGModule A P]
  {P' : Type u} [AddCommGroup P'] [DGAddCommGroup P'] [Module B P'] [DGModule B P']


-- @@ L441-447 verbatim
/-- **The external tensor product of K-projective modules is K-projective**: if `P` and `P'`
are K-projective over `A` and `B`, then `P ⊠ P'` is K-projective over `A ⊗ B`. -/
theorem _root_.DG.ExternalTensor.isKProjective (hP : IsKProjective.{u} A P)
    (hP' : IsKProjective.{u} B P') :
    IsKProjective.{u} AB (P ⊗[ℤ] P') :=
  (IsKProjective.tensorProductOver (RightRegular.isKProjective hP) hP').of_dgModuleEquiv
    (RightRegular.tensorEquiv P P').symm


-- @@ L449-449 verbatim
end RightRegular


-- @@ L451-451 verbatim
end ExternalTensor


-- @@ L453-453 verbatim
namespace ExternalTensorOver


-- @@ L455-461 verbatim
variable {R : Type*} [CommRing R]
  {A : Type u} [Ring A] [Algebra R A] [DGAddCommGroup A] [DGRing A] [DGAlgebra R A]
  {B : Type u} [Ring B] [Algebra R B] [DGAddCommGroup B] [DGRing B] [DGAlgebra R B]
  {P : Type u} [AddCommGroup P] [DGAddCommGroup P] [Module A P] [DGModule A P] [Module R P]
  [IsScalarTower R A P]
  {P' : Type u} [AddCommGroup P'] [DGAddCommGroup P'] [Module B P'] [DGModule B P']
  [Module R P'] [IsScalarTower R B P']


-- @@ L463-470 verbatim
/-- **`P ⊗_R P'` is K-projective** over `A ᵍ⊗[R] B` if `P` and `P'` are K-projective over `A`
and `B`: it is extension of scalars of `P ⊠ P'` along `A ᵍ⊗[ℤ] B → A ᵍ⊗[R] B`. -/
theorem isKProjective (hP : IsKProjective.{u} A P) (hP' : IsKProjective.{u} B P') :
    IsKProjective.{u} (DGAlgebra.gradingSubmodule R A ᵍ⊗[R] DGAlgebra.gradingSubmodule R B)
      (ExternalTensorOver R A B P P') :=
  (IsKProjective.extendScalars (GradedTensorProduct.intComparison R A B)
    (P := DGModuleCat.of _ (P ⊗[ℤ] P')) (ExternalTensor.isKProjective hP hP')).of_dgModuleEquiv
    (extendEquiv R A B P P').symm


-- @@ L472-472 verbatim
end ExternalTensorOver


-- @@ L474-474 verbatim
end DG
