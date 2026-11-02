import DG.Module.ExternalTensorShift
import DG.Module.Cone
import DG.Homotopy.ExternalTensor
import Mathlib.LinearAlgebra.TensorProduct.Prod


-- @@ L6-17 verbatim
/-!
# Mapping cones and the external tensor product

For a morphism `f : M →ᵈᵍ[A] M'` and a dg `B`-module `N`, the external tensor product with `N`
commutes with mapping cones:

`cone(f) ⊠ N ≅ cone(f ⊠ 1)`, `(x, y) ⊗ n ↦ (x ⊗ n, y ⊗ n)`
(`DG.ExternalTensor.coneLeftEquiv`),

an isomorphism of dg modules over `A ⊗ B`, using `cone(f) = M⟦1⟧ × M'` and the shift isomorphism
`M⟦1⟧ ⊠ N ≅ (M ⊠ N)⟦1⟧` (`DG.ExternalTensor.shiftLeftEquiv`).
-/


-- @@ L19-19 verbatim
open scoped TensorProduct


-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
namespace DG


-- @@ L25-25 verbatim
namespace ExternalTensor


-- @@ L27-31 verbatim
variable {A B : Type*} [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B]
  [DGRing B]
  {M M' : Type*} [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
  [AddCommGroup M'] [DGAddCommGroup M'] [Module A M'] [DGModule A M']
  {N : Type*} [AddCommGroup N] [DGAddCommGroup N] [Module B N] [DGModule B N]


-- @@ L33-33 verbatim
local notation "𝒜" => DGAlgebra.gradingSubmodule ℤ A

-- @@ L34-34 verbatim
local notation "ℬ" => DGAlgebra.gradingSubmodule ℤ B

-- @@ L35-35 verbatim
local notation "AB" => 𝒜 ᵍ⊗[ℤ] ℬ


-- @@ L37-37 expanded
variable (f : DGModuleHom A M M') (N)


-- @@ L39-43 expanded
/-- The underlying additive map `cone(f) ⊠ N → cone(f ⊠ 1)`, `(x, y) ⊗ n ↦ (x ⊗ n, y ⊗ n)`. -/
def coneLeftAddEquiv :
    (Cone f ⊗[ℤ] N) ≃+ Cone (tensorDGHom f (DGModuleHom.id : DGModuleHom B N N)) :=
  (TensorProduct.prodLeft ℤ ℤ (Shift 1 M) M' N).toAddEquiv.trans
    (AddEquiv.prodCongr (shiftLeftAddEquiv M N 1) (AddEquiv.refl _))


-- @@ L45-45 verbatim
variable {f N}


-- @@ L47-51 expanded
omit [DGModule B N] in
theorem coneLeftAddEquiv_tmul (p : Cone f) (n : N) :
    coneLeftAddEquiv (B := B) N f (p ⊗ₜ n) =
      ((shiftLeftAddEquiv M N 1 (p.1 ⊗ₜ n), p.2 ⊗ₜ n) :
        Cone (tensorDGHom f (DGModuleHom.id : DGModuleHom B N N))) :=
  rfl


-- @@ L53-124 expanded
variable (f N) in
/-- **`cone(f) ⊠ N ≅ cone(f ⊠ 1)`** as dg modules over `A ⊗ B`, `(x, y) ⊗ n ↦ (x ⊗ n, y ⊗ n)`. -/
def coneLeftEquiv :
    DGModuleEquiv AB (Cone f ⊗[ℤ] N) (Cone (tensorDGHom f (DGModuleHom.id : DGModuleHom B N N)))
    where
  __ := coneLeftAddEquiv N f
  map_smul' x
    y := by
    change coneLeftAddEquiv (B := B) N f (x • y) = x • coneLeftAddEquiv N f y
    induction x using GradedTensorProduct.induction_on_tmul (R := ℤ) with
    | zero =>
      rw [zero_smul', map_zero]
      exact (zero_smul AB (coneLeftAddEquiv (B := B) N f y)).symm
    | add x x' hx hx' =>
      rw [add_smul', map_add, hx, hx']
      exact (add_smul _ _ _).symm
    | @tmul i j a ha b hb =>
      induction y using DG.tensor_induction_on with
      | zero =>
        rw [smul_zero', map_zero]
        exact (smul_zero _).symm
      | add y y' hy hy' =>
        rw [smul_add', map_add, hy, hy', map_add]
        exact (smul_add _ _ _).symm
      | tmul p n =>
        obtain ⟨p, hp⟩ := p
        obtain ⟨n, -⟩ := n
        have hp1 : p.1 ∈ grading _ := (Cone.mem_grading_iff.mp hp).1
        have hp2 : p.2 ∈ grading _ := (Cone.mem_grading_iff.mp hp).2
        rw [tmul_smul_tmul a hb hp n, Units.smul_def, map_zsmul, coneLeftAddEquiv_tmul,
          coneLeftAddEquiv_tmul]
        refine Prod.ext ?_ ?_
        · change
            (_ : ℤ) • shiftLeftAddEquiv M N 1 ((a • p.1) ⊗ₜ (b • n)) =
              (a ᵍ⊗ₜ[ℤ] b : AB) • shiftLeftAddEquiv M N 1 (p.1 ⊗ₜ n)
          rw [← shiftLeftAddEquiv_smul_tmul 1 a hb hp1 n, tmul_smul_tmul a hb hp1 n, Units.smul_def,
            map_zsmul]
        · change (_ : ℤ) • ((a • p.2) ⊗ₜ (b • n)) = (a ᵍ⊗ₜ[ℤ] b : AB) • (p.2 ⊗ₜ n)
          rw [tmul_smul_tmul a hb hp2 n, Units.smul_def]
  map_mem' {k y}
    hy :=
    by
    have :=
      map_mem_grading_of_tmul (coneLeftAddEquiv (B := B) N f).toAddMonoidHom 0
        (fun {i j p n} hp hn => by
          rw [add_zero]
          refine Cone.mem_grading_iff.mpr ⟨?_, ?_⟩
          ·
            exact
              (shiftLeftEquiv (A := A) (B := B) M N 1).map_mem
                (tmul_mem_grading (Cone.mem_grading_iff.mp hp).1 hn)
          · exact tmul_mem_grading (Cone.mem_grading_iff.mp hp).2 hn)
        hy
    rwa [add_zero] at this
  map_d'
    y := by
    change coneLeftAddEquiv (B := B) N f (d y) = d (coneLeftAddEquiv N f y)
    induction y using DG.tensor_induction_on with
    | zero => simp
    | add y y' hy hy' => rw [d_add, map_add, hy, hy', map_add, d_add]
    | @tmul i j p n =>
      obtain ⟨p, hp⟩ := p
      obtain ⟨n, -⟩ := n
      have hp1 : p.1 ∈ grading i := (Cone.mem_grading_iff.mp hp).1
      have hp2 : p.2 ∈ grading i := (Cone.mem_grading_iff.mp hp).2
      rw [d_tmul_of_mem hp, map_add, Units.smul_def, map_zsmul, coneLeftAddEquiv_tmul,
        coneLeftAddEquiv_tmul, coneLeftAddEquiv_tmul]
      refine Prod.ext ?_ ?_
      · change
          shiftLeftAddEquiv M N 1 ((d p).1 ⊗ₜ n) + (_ : ℤ) • shiftLeftAddEquiv M N 1 (p.1 ⊗ₜ d n) =
            d (shiftLeftAddEquiv M N 1 (p.1 ⊗ₜ n))
        have h := (shiftLeftEquiv (A := A) (B := B) M N 1).map_d (p.1 ⊗ₜ n)
        change shiftLeftAddEquiv M N 1 (d (p.1 ⊗ₜ n)) = d (shiftLeftAddEquiv M N 1 (p.1 ⊗ₜ n)) at h
        rw [← h, d_tmul_of_mem hp1, map_add, Units.smul_def, map_zsmul]
        rfl
      · change
          ((d p).2 ⊗ₜ n) + (_ : ℤ) • (p.2 ⊗ₜ d n) =
            tensorDGHom f (DGModuleHom.id : DGModuleHom B N N)
                (Shift.unmk 1 (shiftLeftAddEquiv M N 1 (p.1 ⊗ₜ n))) +
              d (p.2 ⊗ₜ n)
        have h2 : (d p).2 = f (Shift.unmk 1 p.1) + d p.2 := rfl
        rw [h2, TensorProduct.add_tmul, d_tmul_of_mem hp2, Units.smul_def, add_assoc]
        rfl


-- @@ L126-126 verbatim
/-! ### The second variable -/


-- @@ L128-128 verbatim
section Right


-- @@ L130-131 expanded
variable {N' : Type*} [AddCommGroup N'] [DGAddCommGroup N'] [Module B N'] [DGModule B N']
  (g : DGModuleHom B N N')


-- @@ L133-139 expanded
variable (M) in
/-- The underlying additive map `M ⊠ cone(g) → cone(1 ⊠ g)`,
`m ⊗ (x, y) ↦ (shiftRight (m ⊗ x), m ⊗ y)`. -/
def coneRightAddEquiv :
    (M ⊗[ℤ] Cone g) ≃+ Cone (tensorDGHom (DGModuleHom.id : DGModuleHom A M M) g) :=
  (TensorProduct.prodRight ℤ ℤ M (Shift 1 N) N').toAddEquiv.trans
    (AddEquiv.prodCongr (shiftRightAddEquiv M N 1) (AddEquiv.refl _))


-- @@ L141-145 expanded
omit [DGModule B N] [DGModule B N'] in
theorem coneRightAddEquiv_tmul (m : M) (q : Cone g) :
    coneRightAddEquiv (A := A) M g (m ⊗ₜ q) =
      ((shiftRightAddEquiv M N 1 (m ⊗ₜ q.1), m ⊗ₜ q.2) :
        Cone (tensorDGHom (DGModuleHom.id : DGModuleHom A M M) g)) :=
  rfl


-- @@ L147-220 expanded
variable (M) in
/-- **`M ⊠ cone(g) ≅ cone(1 ⊠ g)`** as dg modules over `A ⊗ B`,
`m ⊗ (x, y) ↦ ((-1)^{|m|} m ⊗ x, m ⊗ y)` (with `x ∈ N⟦1⟧`). -/
def coneRightEquiv :
    DGModuleEquiv AB (M ⊗[ℤ] Cone g) (Cone (tensorDGHom (DGModuleHom.id : DGModuleHom A M M) g))
    where
  __ := coneRightAddEquiv M g
  map_smul' x
    y := by
    change coneRightAddEquiv (A := A) M g (x • y) = x • coneRightAddEquiv M g y
    induction x using GradedTensorProduct.induction_on_tmul (R := ℤ) with
    | zero =>
      rw [zero_smul', map_zero]
      exact (zero_smul AB (coneRightAddEquiv (A := A) M g y)).symm
    | add x x' hx hx' =>
      rw [add_smul', map_add, hx, hx']
      exact (add_smul _ _ _).symm
    | @tmul i j a ha b hb =>
      induction y using DG.tensor_induction_on with
      | zero =>
        rw [smul_zero', map_zero]
        exact (smul_zero _).symm
      | add y y' hy hy' =>
        rw [smul_add', map_add, hy, hy', map_add]
        exact (smul_add _ _ _).symm
      | tmul m q =>
        obtain ⟨m, hm⟩ := m
        obtain ⟨q, -⟩ := q
        rw [tmul_smul_tmul a hb hm q, Units.smul_def, map_zsmul, coneRightAddEquiv_tmul,
          coneRightAddEquiv_tmul]
        refine Prod.ext ?_ ?_
        · change
            (_ : ℤ) • shiftRightAddEquiv M N 1 ((a • m) ⊗ₜ (b • q.1)) =
              (a ᵍ⊗ₜ[ℤ] b : AB) • shiftRightAddEquiv M N 1 (m ⊗ₜ q.1)
          rw [← shiftRightAddEquiv_smul_tmul 1 a hb hm q.1, tmul_smul_tmul a hb hm q.1,
            Units.smul_def, map_zsmul]
        · change (_ : ℤ) • ((a • m) ⊗ₜ (b • q.2)) = (a ᵍ⊗ₜ[ℤ] b : AB) • (m ⊗ₜ q.2)
          rw [tmul_smul_tmul a hb hm q.2, Units.smul_def]
  map_mem' {k y}
    hy :=
    by
    have :=
      map_mem_grading_of_tmul (coneRightAddEquiv (A := A) M g).toAddMonoidHom 0
        (fun {i j m q} hm hq => by
          rw [add_zero]
          refine Cone.mem_grading_iff.mpr ⟨?_, ?_⟩
          ·
            exact
              (shiftRightEquiv (A := A) (B := B) M N 1).map_mem
                (tmul_mem_grading hm (Cone.mem_grading_iff.mp hq).1)
          · exact tmul_mem_grading hm (Cone.mem_grading_iff.mp hq).2)
        hy
    rwa [add_zero] at this
  map_d'
    y := by
    change coneRightAddEquiv (A := A) M g (d y) = d (coneRightAddEquiv M g y)
    induction y using DG.tensor_induction_on with
    | zero => simp
    | add y y' hy hy' => rw [d_add, map_add, hy, hy', map_add, d_add]
    | @tmul i j m q =>
      obtain ⟨m, hm⟩ := m
      obtain ⟨q, -⟩ := q
      obtain ⟨x, hx⟩ := Shift.mk_surjective q.1
      rw [d_tmul_of_mem hm, map_add, Units.smul_def, map_zsmul, coneRightAddEquiv_tmul,
        coneRightAddEquiv_tmul, coneRightAddEquiv_tmul]
      refine Prod.ext ?_ ?_
      · change
          shiftRightAddEquiv M N 1 (d m ⊗ₜ q.1) +
              (_ : ℤ) • shiftRightAddEquiv M N 1 (m ⊗ₜ (d q).1) =
            d (shiftRightAddEquiv M N 1 (m ⊗ₜ q.1))
        have h := (shiftRightEquiv (A := A) (B := B) M N 1).map_d (m ⊗ₜ q.1)
        change
          shiftRightAddEquiv M N 1 (d (m ⊗ₜ q.1)) = d (shiftRightAddEquiv M N 1 (m ⊗ₜ q.1)) at h
        rw [← h, d_tmul_of_mem hm, map_add, Units.smul_def, map_zsmul]
        rfl
      · change
          (d m ⊗ₜ q.2) + (_ : ℤ) • (m ⊗ₜ (d q).2) =
            tensorDGHom (DGModuleHom.id : DGModuleHom A M M) g
                (Shift.unmk 1 (shiftRightAddEquiv M N 1 (m ⊗ₜ q.1))) +
              d (m ⊗ₜ q.2)
        have h2 : (d q).2 = g (Shift.unmk 1 q.1) + d q.2 := rfl
        rw [h2, d_tmul_of_mem hm, TensorProduct.tmul_add, smul_add]
        rw [← hx, shiftRightAddEquiv_tmul 1 hm, Shift.unmk_units_smul, Shift.unmk_mk,
          Units.smul_def, map_zsmul, mul_one]
        change _ = (_ : ℤ) • (m ⊗ₜ g x) + _
        rw [Units.smul_def]
        abel


-- @@ L222-222 verbatim
end Right


-- @@ L224-224 verbatim
end ExternalTensor


-- @@ L226-226 verbatim
end DG
