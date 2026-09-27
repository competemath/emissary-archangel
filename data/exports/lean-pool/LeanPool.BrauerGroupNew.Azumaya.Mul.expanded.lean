/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/
module

public import LeanPool.BrauerGroupNew.Azumaya.Basic
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.TensorProduct.Opposite
public import Mathlib.Tactic.Continuity
public import Mathlib.Algebra.Azumaya.Matrix
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Integral.Bochner.Basic


-- @@ L16-20 verbatim
/-!
# LeanPool.BrauerGroupNew.Azumaya.Mul

Imported Lean Pool material for `LeanPool.BrauerGroupNew.Azumaya.Mul`.
-/


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
suppress_compilation


-- @@ L26-26 verbatim
open Function

-- @@ L27-27 verbatim
open scoped TensorProduct


-- @@ L29-29 verbatim
universe u v


-- @@ L31-31 verbatim
variable (R : Type u) [CommRing R]


-- @@ L33-33 verbatim
section formathlib


-- @@ L35-37 verbatim
variable (R : Type u) [CommRing R] (M N P Q : Type*) [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N] [Module.Finite R M] [Module.Finite R N] [Module.Projective R M]
  [Module.Projective R N] [AddCommGroup P] [AddCommGroup Q] [Module R P] [Module R Q]


-- @@ L39-40 verbatim
/-- The rank of a finite free module used to split a finite projective module. -/
abbrev nn : ℕ := (Module.Finite.exists_comp_eq_id_of_projective R M).choose


-- @@ L42-44 verbatim
/-- The surjective map from a finite free module onto a finite projective module. -/
abbrev f0 : (Fin (nn R M) → R) →ₗ[R] M :=
  (Module.Finite.exists_comp_eq_id_of_projective R M).choose_spec.choose


-- @@ L46-48 verbatim
/-- The injective splitting map from a finite projective module into a finite free module. -/
abbrev g0 : M →ₗ[R] Fin (nn R M) → R :=
  (Module.Finite.exists_comp_eq_id_of_projective R M).choose_spec.choose_spec.choose


-- @@ L50-51 verbatim
lemma f0_surj : Function.Surjective (f0 R M) :=
  (Module.Finite.exists_comp_eq_id_of_projective R M).choose_spec.choose_spec.choose_spec|>.1


-- @@ L53-54 verbatim
lemma g0_inj : Function.Injective (g0 R M) :=
  (Module.Finite.exists_comp_eq_id_of_projective R M).choose_spec.choose_spec.choose_spec|>.2.1


-- @@ L56-57 verbatim
lemma fg : (f0 R M) ∘ₗ (g0 R M) = LinearMap.id :=
  (Module.Finite.exists_comp_eq_id_of_projective R M).choose_spec.choose_spec.choose_spec|>.2.2


-- @@ L59-63 verbatim
/-- Precomposition with `f0`, embedding maps out of `M` into maps out of a finite free module. -/
abbrev inclusion1 : (M →ₗ[R] P) →ₗ[R] ((Fin (nn R M) → R) →ₗ[R] P) where
  toFun := fun f ↦ f.comp (f0 R M)
  map_add' := by simp [LinearMap.add_comp]
  map_smul' := by simp [LinearMap.smul_comp]


-- @@ L65-70 verbatim
/-- Precomposition with `g0`, projecting maps from the finite free cover
back to maps out of `M`. -/
abbrev projection1 : ((Fin (nn R M) → R) →ₗ[R] P) →ₗ[R] (M →ₗ[R] P) where
  toFun := fun f ↦ f.comp (g0 R M)
  map_add' := by simp [LinearMap.add_comp]
  map_smul' := by simp [LinearMap.smul_comp]


-- @@ L72-76 verbatim
/-- Hom(M, P) ⊗ Hom(N, Q) →ₗ[R] Hom(Rⁿ, P) ⊗ Hom(Rᵐ, Q) -/
abbrev tensorInclusion1 :
    (M →ₗ[R] P) ⊗[R] (N →ₗ[R] Q) →ₗ[R]
      ((Fin (nn R M) → R) →ₗ[R] P) ⊗[R] ((Fin (nn R N) → R) →ₗ[R] Q) :=
  TensorProduct.map (inclusion1 R M P) (inclusion1 R N Q)


-- @@ L78-79 verbatim
/-- Tensor product of the two first projection maps. -/
abbrev tensorProjection1 := TensorProduct.map (projection1 R M P) (projection1 R N Q)


-- @@ L81-83 verbatim
lemma projection_inlusion1 : (projection1 R M P).comp (inclusion1 R M P) = LinearMap.id := by
  ext f : 1
  simp [LinearMap.comp_assoc, fg]


-- @@ L85-87 verbatim
lemma tensorInclusion1_projection1 : (tensorProjection1 R M N P Q).comp
    (tensorInclusion1 R M N P Q) = LinearMap.id := by
  simp [← TensorProduct.map_comp, projection_inlusion1]


-- @@ L89-91 verbatim
lemma tensorInclusion1_projection1_apply (x : (M →ₗ[R] P) ⊗[R] (N →ₗ[R] Q)) :
    tensorProjection1 R M N P Q (tensorInclusion1 R M N P Q x) = x :=
  DFunLike.congr_fun (tensorInclusion1_projection1 R M N P Q) x


-- @@ L93-95 verbatim
lemma tensorInclusion1_inj : Function.Injective (tensorInclusion1 R M N P Q) :=
  Function.LeftInverse.injective (g := tensorProjection1 R M N P Q)
    <| DFunLike.congr_fun <| tensorInclusion1_projection1 R M N P Q


-- @@ L97-100 verbatim
open TensorProduct in
lemma Tensor_isDirectSummand : ∃(s0 : M ⊗[R] N →ₗ[R] (Fin (nn R M) → R) ⊗[R] (Fin (nn R N) → R))
    (s1 : (Fin (nn R M) → R) ⊗[R] (Fin (nn R N) → R) →ₗ[R] M ⊗[R] N), s1.comp s0 = .id :=
  ⟨map (g0 R M) (g0 R N), map (f0 R M) (f0 R N), by simp [← map_comp, fg]⟩


-- @@ L102-105 verbatim
variable {R M N} in
/-- The tensor-product inclusion induced by the free-module splittings of `M` and `N`. -/
abbrev inclusion2 : M ⊗[R] N →ₗ[R] (Fin (nn R M) → R) ⊗[R] (Fin (nn R N) → R) :=
  TensorProduct.map (g0 R M) (g0 R N)


-- @@ L107-110 verbatim
variable {R M N} in
/-- The tensor-product projection induced by the free-module covers of `M` and `N`. -/
abbrev projection2 : (Fin (nn R M) → R) ⊗[R] (Fin (nn R N) → R) →ₗ[R] M ⊗[R] N :=
  TensorProduct.map (f0 R M) (f0 R N)


-- @@ L112-118 verbatim
variable {M N} in
/-- Precomposition with `projection2` on homs out of `M ⊗ N`. -/
abbrev tensorInclusion2 : (M ⊗[R] N →ₗ[R] P ⊗[R] Q) →ₗ[R]
    ((Fin (nn R M) → R) ⊗[R] (Fin (nn R N) → R) →ₗ[R] P ⊗[R] Q) where
  toFun := fun f ↦ f.comp projection2
  map_add' := by simp [LinearMap.add_comp]
  map_smul' := by simp [LinearMap.smul_comp]


-- @@ L120-126 verbatim
variable {M N} in
/-- Precomposition with `inclusion2` on homs out of the finite free tensor product. -/
abbrev tensorProjection2 : ((Fin (nn R M) → R) ⊗[R] (Fin (nn R N) → R) →ₗ[R]
    P ⊗[R] Q) →ₗ[R] (M ⊗[R] N →ₗ[R] P ⊗[R] Q) where
  toFun := fun f ↦ f.comp inclusion2
  map_add' := by simp [LinearMap.add_comp]
  map_smul' := by simp [LinearMap.smul_comp]


-- @@ L128-130 verbatim
lemma projection2_inclusion2 : (projection2).comp (inclusion2) =
    LinearMap.id (R := R) (M := M ⊗[R] N) :=
  by simp [← TensorProduct.map_comp, fg]


-- @@ L132-133 verbatim
lemma projection2_inclusion2_apply (x : M ⊗[R] N) : (projection2) ((inclusion2) x) = x :=
  DFunLike.congr_fun (projection2_inclusion2 R M N) x


-- @@ L135-138 verbatim
lemma tensorProjection2_inclusion2 : (tensorProjection2 R P Q).comp (tensorInclusion2 R P Q) =
    LinearMap.id (R := R) (M := M ⊗[R] N →ₗ[R] P ⊗[R] Q) := by
  ext f : 1
  simp [LinearMap.comp_assoc, projection2_inclusion2]


-- @@ L140-142 verbatim
lemma tensorInclusion2_inj : Function.Injective (tensorInclusion2 R (M := M) (N := N) P Q) :=
  Function.LeftInverse.injective (g := tensorProjection2 R P Q)
    <| DFunLike.congr_fun <| tensorProjection2_inclusion2 R M N P Q


-- @@ L144-158 verbatim
/-- This proves the following square commutes:
               `TensorProduct.homTensorHomMap`
Hom(M, P) ⊗ Hom(N, Q) ---------------> Hom(M ⊗ N, P ⊗ Q)
    |       |                             |      |
 i  |       |  j                       i' |      |  j'
    |       |                             |      |
    |       |                             |      |
Hom(Rⁿ, P) ⊗ Hom(Rᵐ, Q) -------------> Hom(Rⁿ ⊗ Rᵐ, P ⊗ Q)
-/
lemma comm_square2 : (homTensorHomEquiv R (Fin (nn R M) → R) (Fin (nn R N) → R) P Q).toLinearMap ∘ₗ
    tensorInclusion1 R M N P Q =
      tensorInclusion2 R P Q ∘ₗ TensorProduct.homTensorHomMap _ M N P Q := by
  ext f g : 4
  refine LinearMap.ext fun v ↦ LinearMap.ext fun u ↦ ?_
  simp


-- @@ L160-164 verbatim
lemma comm_square2_apply (f : (M →ₗ[R] P) ⊗[R] (N →ₗ[R] Q)) :
  (homTensorHomEquiv R (Fin (nn R M) → R) (Fin (nn R N) → R) P Q).toLinearMap
    (tensorInclusion1 R M N P Q f) =
      tensorInclusion2 R P Q (TensorProduct.homTensorHomMap _ M N P Q f) :=
  DFunLike.congr_fun (comm_square2 R M N P Q) f


-- @@ L166-171 verbatim
lemma homTensorHomMap_inj : Function.Injective (TensorProduct.homTensorHomMap (.id R) M N P Q) := by
  apply Function.Injective.of_comp (f := tensorInclusion2 R P Q)
  rw [← LinearMap.coe_comp, ← comm_square2]
  exact Function.Injective.comp (f := tensorInclusion1 R M N P Q)
    (homTensorHomEquiv R (Fin (nn R M) → R) (Fin (nn R N) → R) P Q).injective <|
    tensorInclusion1_inj R M N P Q


-- @@ L173-178 verbatim
lemma comm_square3 : (homTensorHomEquiv R _ _ _ _).toLinearMap ∘ₗ
    tensorInclusion1 R M N P Q ∘ₗ tensorProjection1 R M N P Q = tensorInclusion2 R P Q ∘ₗ
    tensorProjection2 R P Q ∘ₗ (homTensorHomEquiv R _ _ _ _).toLinearMap := by
  ext f g : 4
  refine LinearMap.ext fun v ↦ LinearMap.ext fun u ↦ ?_
  simp


-- @@ L180-183 verbatim
lemma comm_square3_apply (f : ((Fin (nn R M) → R) →ₗ[R] P) ⊗[R] ((Fin (nn R N) → R) →ₗ[R] Q)) :
    (homTensorHomEquiv R _ _ _ _) (tensorInclusion1 R M N P Q (tensorProjection1 R M N P Q f)) =
    tensorInclusion2 R P Q (tensorProjection2 R P Q (homTensorHomEquiv R _ _ _ _ f)) :=
  DFunLike.congr_fun (comm_square3 R M N P Q) f


-- @@ L185-192 verbatim
lemma comm_square1 :
    tensorProjection1 R M N P Q ∘ₗ (homTensorHomEquiv R _ _ P Q).symm.toLinearMap ∘ₗ
      tensorInclusion2 R P Q ∘ₗ TensorProduct.homTensorHomMap _ M N P Q =
        .id (R := R) (M := (M →ₗ[R] P) ⊗[R] (N →ₗ[R] Q)) := by
  rw [← comm_square2]
  apply LinearMap.ext
  simp [-homTensorHomEquiv_toLinearMap, -homTensorHomEquiv_apply,
    tensorInclusion1_projection1_apply]


-- @@ L194-206 verbatim
lemma comm_square4 :
    TensorProduct.homTensorHomMap _ M N P Q ∘ₗ tensorProjection1 R M N P Q ∘ₗ
      (homTensorHomEquiv R _ _ _ _).symm.toLinearMap ∘ₗ tensorInclusion2 R P Q =
        .id (R := R) (M := (M ⊗[R] N) →ₗ[R] P ⊗[R] Q) := by
  apply LinearMap.ext
  intro fgfg
  simp only [LinearMap.comp_apply]
  apply tensorInclusion2_inj
  rw [← comm_square2_apply, LinearEquiv.coe_toLinearMap, comm_square3_apply]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, LinearMap.id_coe, id_eq]
  apply LinearMap.ext
  simp [projection2_inclusion2_apply]


-- @@ L208-212 verbatim
lemma homTensorHomMap_surj : Surjective (TensorProduct.homTensorHomMap (.id R) M N P Q) := by
  apply Function.Surjective.of_comp (g := (tensorProjection1 R M N P Q ∘ₗ
    (homTensorHomEquiv R _ _ _ _).symm.toLinearMap ∘ₗ tensorInclusion2 R P Q))
  rw [← LinearMap.coe_comp, comm_square4]
  exact Function.surjective_id


-- @@ L214-214 verbatim
end formathlib


-- @@ L216-216 verbatim
open MulOpposite


-- @@ L218-220 verbatim
/-- An Azumaya algebra over a commutative base ring, bundled as an algebra object. -/
structure Azumaya (R : Type u) [CommRing R] extends AlgCat R where
  isAzumaya : IsAzumaya R carrier


-- @@ L222-224 verbatim
@[coe]
instance : CoeSort (Azumaya R) (Type v) where
  coe s := s.carrier


-- @@ L226-226 verbatim
attribute [instance] Azumaya.isAzumaya


-- @@ L228-230 verbatim
/-- Morita equivalence of the carrier algebras of two bundled Azumaya algebras. -/
def Azumaya.IsMoritaEquivalent : Azumaya R → Azumaya R → Prop :=
    fun A B ↦ _root_.IsMoritaEquivalent R A.carrier B.carrier


-- @@ L232-234 verbatim
lemma Azumaya.IsMoritaEquivalent.iff {A B : Azumaya R} :
  Azumaya.IsMoritaEquivalent R A B ↔ _root_.IsMoritaEquivalent R A.carrier B.carrier :=
  Iff.rfl


-- @@ L236-239 verbatim
lemma AzuMorita.equiv : Equivalence (Azumaya.IsMoritaEquivalent R) where
  refl _ := .refl R _
  symm := .symm R
  trans := .trans R


-- @@ L241-244 verbatim
/-- The setoid on Azumaya algebras induced by Morita equivalence. -/
abbrev AzumayaSetoid : Setoid (Azumaya R) where
  r := Azumaya.IsMoritaEquivalent R
  iseqv := AzuMorita.equiv R


-- @@ L246-246 verbatim
namespace Azumaya


-- @@ L248-248 verbatim
variable (A B : Type v) [Ring A] [Ring B] [Algebra R A] [Algebra R B]

-- @@ L249-250 verbatim
instance [Module.Finite R A] [Module.Finite R B] :
    Module.Finite R (A ⊗[R] B) := Module.Finite.tensorProduct R A B


-- @@ L252-264 verbatim
variable {R A B} in
instance faithfulSMulTensor [Module.Projective R A]
    [FaithfulSMul R A] [FaithfulSMul R B] :
    FaithfulSMul R (A ⊗[R] B) where
  eq_of_smul_eq_smul {r1 r2} eq := by
    specialize eq 1
    rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul',
      TensorProduct.smul_tmul'] at eq
    have := Algebra.TensorProduct.includeLeft_injective (R := R) (S := R)
      (fun r1 r2 h ↦ by
        simp_all) eq
    exact eq_of_smul_eq_smul (M := R) (α := A) (m₁ := r1) (m₂ := r2) <|
      fun a ↦ by rw [← one_mul a, ← smul_mul_assoc, this, smul_mul_assoc, one_mul]


-- @@ L266-275 verbatim
open Algebra.TensorProduct (assoc congr opAlgEquiv) in
variable {R A B} in
/-- Rebracketing equivalence used to compare `mulLeftRight` with tensor products. -/
abbrev e : (A ⊗[R] Aᵐᵒᵖ) ⊗[R] (B ⊗[R] Bᵐᵒᵖ) ≃ₐ[R] (A ⊗[R] B) ⊗[R] (A ⊗[R] B)ᵐᵒᵖ :=
  (assoc R R R A B (Aᵐᵒᵖ ⊗[R] Bᵐᵒᵖ)|>.trans <|
  (congr .refl (assoc R R R B Aᵐᵒᵖ Bᵐᵒᵖ)).symm.trans <|
  congr .refl (congr (Algebra.TensorProduct.comm R _ _) .refl) |>.trans
  <| congr .refl (assoc R R R Aᵐᵒᵖ B Bᵐᵒᵖ) |>.trans
  <| assoc R R R A Aᵐᵒᵖ (B ⊗[R] Bᵐᵒᵖ)|>.symm).symm.trans
  <| Algebra.TensorProduct.congr .refl <| opAlgEquiv R R A B


-- @@ L277-278 verbatim
lemma e_apply (a : A) (b : B) (a' : Aᵐᵒᵖ) (b' : Bᵐᵒᵖ) :
    e ((a ⊗ₜ a') ⊗ₜ (b ⊗ₜ b')) = (a ⊗ₜ b) ⊗ₜ op (a'.unop ⊗ₜ[R] b'.unop) := rfl


-- @@ L280-288 verbatim
open TensorProduct.AlgebraTensorModule in
lemma top_square_comm'' (A B : Azumaya R) :
    (TensorProduct.homTensorHomMap _ A B A B) ∘ₗ (Algebra.TensorProduct.congr
    (AlgEquiv.ofBijective (AlgHom.mulLeftRight R A) A.isAzumaya.bij)
    (AlgEquiv.ofBijective (AlgHom.mulLeftRight R B) B.isAzumaya.bij)).toLinearMap
    = (AlgHom.mulLeftRight R (A ⊗[R] B)).toLinearMap ∘ₗ
    (e (R := R) (A := A) (B := B)).toLinearEquiv.toLinearMap := by
  ext a b c d a' b'
  simp


-- @@ L290-295 verbatim
lemma top_square_comm (A B : Azumaya R) :
    (TensorProduct.homTensorHomMap _ A B A B) ∘ (Algebra.TensorProduct.congr
    (AlgEquiv.ofBijective (AlgHom.mulLeftRight R A) A.isAzumaya.bij)
    (AlgEquiv.ofBijective (AlgHom.mulLeftRight R B) B.isAzumaya.bij))
    = (AlgHom.mulLeftRight R (A ⊗[R] B)) ∘ (e (R := R) (A := A) (B := B)) :=
  congr_arg DFunLike.coe <| top_square_comm'' R A B


-- @@ L297-313 verbatim
/--
A ⊗ Aᵐᵒᵖ ⊗ B ⊗ B ᵐᵒᵖ --------> (A ⊗ B) ⊗ (A ⊗ B)ᵐᵒᵖ
        |                              |
        |                              |
        |                              |
        |                              |
      f ⊗ g            ---->         f ⊗ g
End R A ⊗ End R B ---------------> End R (A ⊗ B)
    |     |                           |   |
  i |     | j                     i'  |   |  j'
    |     |                           |   |
    |     |   `homTensorHomEquiv`     |   |
End R Rⁿ ⊗ End R Rᵐ -------------> End R (Rⁿ ⊗ Rᵐ)
-/
lemma bij_homtensorhom (A B : Azumaya.{u, v} R) :
    Function.Bijective (TensorProduct.homTensorHomMap (.id R) A B A B) :=
  ⟨homTensorHomMap_inj R A B A B, homTensorHomMap_surj R A B A B⟩


-- @@ L315-318 verbatim
/-- The hom-tensor-hom equivalence for the carriers of two Azumaya algebras. -/
abbrev e1 (A B : Azumaya.{u, v} R) :
    (Module.End R A ⊗[R] Module.End R B) ≃ₗ[R] Module.End R (A ⊗[R] B) :=
  .ofBijective (TensorProduct.homTensorHomMap _ A B A B) <| bij_homtensorhom R A B


-- @@ L320-323 verbatim
/-- The tensor-product equivalence induced by the two `mulLeftRight` bijections. -/
abbrev e2 (A B : Azumaya R) := (Algebra.TensorProduct.congr
    (AlgEquiv.ofBijective (AlgHom.mulLeftRight R A) A.isAzumaya.bij)
    (AlgEquiv.ofBijective (AlgHom.mulLeftRight R B) B.isAzumaya.bij))


-- @@ L325-328 verbatim
lemma top_square_comm_apply (A B : Azumaya R) (x : (A ⊗[R] Aᵐᵒᵖ) ⊗[R] (B ⊗[R] Bᵐᵒᵖ)) :
    (e1 R A B) (e2 R A B x) =
      (AlgHom.mulLeftRight R (A ⊗[R] B)) ((e (R := R) (A := A) (B := B)).toAlgHom x) :=
  congrFun (top_square_comm R A B) x


-- @@ L330-336 verbatim
lemma bij_mulLeftRight (A B : Azumaya.{u, v} R) :
    Function.Bijective (AlgHom.mulLeftRight R (A ⊗[R] B)) :=
  Function.Bijective.of_comp_iff (AlgHom.mulLeftRight R (A ⊗[R] B))
    (e (R := R) (A := A) (B := B)).bijective|>.1 <| by
  rw [← top_square_comm]
  change Function.Bijective (e1 R A B ∘ e2 R A B)
  exact (e1 R A B).bijective.comp (e2 R A B).bijective


-- @@ L338-344 verbatim
/-- Tensor product of bundled Azumaya algebras. -/
abbrev mul (A B : Azumaya R) : Azumaya R where
  __ := AlgCat.of R (A.carrier ⊗[R] B.carrier)
  isAzumaya.out := Module.Projective.tensorProduct|>.out
  isAzumaya.eq_of_smul_eq_smul := Azumaya.faithfulSMulTensor|>.eq_of_smul_eq_smul
  isAzumaya.fg_top := Module.Finite.tensorProduct R A B|>.fg_top
  isAzumaya.bij := bij_mulLeftRight R A B


-- @@ L346-347 verbatim
instance : Mul (Azumaya R) where
  mul A B := mul R A B


-- @@ L349-350 verbatim
lemma mul_coe (A B : Azumaya.{u, v} R) :
    (A * B) = ⟨.of R (A ⊗[R] B), ⟨bij_mulLeftRight R A B⟩⟩ := rfl


-- @@ L352-353 verbatim
instance : One (Azumaya R) where
  one := ⟨.of R R, IsAzumaya_R R⟩


-- @@ L355-359 verbatim
instance : FaithfulSMul R Rᵐᵒᵖ where
  eq_of_smul_eq_smul {r1 r2} hr := by
    specialize hr 1
    change op _ = op _ at hr
    simp_all


-- @@ L361-374 verbatim
/--
A ⊗ Aᵐᵒᵖ  ------------> B ⊗ Bᵐᵒᵖ
  |                        |
  |                        |
  |                        |
  |                        |
End R A   ------------> End R B
-/
lemma small_comm_square (e : A ≃ₐ[R] B) :
    (AlgHom.mulLeftRight R B).comp (Algebra.TensorProduct.congr e e.op).toAlgHom =
      (e.toLinearEquiv.conjAlgEquiv R).toAlgHom.comp (AlgHom.mulLeftRight R A) := by
  apply AlgHom.toLinearMap_injective
  ext a a' b
  simp [AlgHom.mulLeftRight_apply, LinearEquiv.conjAlgEquiv]


-- @@ L376-383 verbatim
lemma _root_.IsAzumaya.ofAlgEquiv (e : A ≃ₐ[R] B) (hA : IsAzumaya R A) : IsAzumaya R B :=
  let _ : Module.Projective R B := .of_equiv e.toLinearEquiv
  let _ : FaithfulSMul R B := .of_injective e e.injective
  let _ : Module.Finite R B := .equiv e.toLinearEquiv
  ⟨Function.Bijective.of_comp_iff (AlgHom.mulLeftRight R B)
    (Algebra.TensorProduct.congr e e.op).bijective |>.1 <| by
    erw [← AlgHom.coe_comp, small_comm_square]
    simp [hA.bij]⟩


-- @@ L385-390 verbatim
/-- Inclusion of endomorphisms induced by a finite free cover of a projective module. -/
abbrev inclusion' (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M] : Module.End R M →ₗ[R] Module.End R (Fin (nn R M) → R) where
  toFun := fun f ↦ g0 R M ∘ₗ f ∘ₗ f0 R M
  map_add' := fun _ _ ↦ by simp [LinearMap.add_comp, LinearMap.comp_add]
  map_smul' := fun _ _ ↦ by simp [LinearMap.smul_comp, LinearMap.comp_smul]


-- @@ L392-397 verbatim
/-- Projection of endomorphisms induced by a splitting of the finite free cover. -/
abbrev projection' (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M] : Module.End R (Fin (nn R M) → R) →ₗ[R] Module.End R M where
  toFun := fun f ↦ f0 R M ∘ₗ f ∘ₗ g0 R M
  map_add' := fun _ _ ↦ by simp [LinearMap.add_comp, LinearMap.comp_add]
  map_smul' := fun _ _ ↦ by simp [LinearMap.smul_comp, LinearMap.comp_smul]


-- @@ L399-405 verbatim
lemma projection'_inclusion' (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M] : projection' R M ∘ₗ inclusion' R M = LinearMap.id := by
  ext f : 1
  simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, comp_apply, LinearMap.id_coe,
    id_eq]
  simp only [LinearMap.comp_assoc, fg, LinearMap.comp_id]
  rw [← LinearMap.comp_assoc, fg, LinearMap.id_comp]


-- @@ L407-411 verbatim
lemma projection'_surj (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M] : Function.Surjective (projection' R M) :=
  Function.Surjective.of_comp (g := inclusion' R M) <| by
  rw [← LinearMap.coe_comp, projection'_inclusion']
  exact Function.surjective_id


-- @@ L413-416 verbatim
lemma _root_.Module.Projective.ofEnd (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M] : Module.Projective R (Module.End R M) :=
  .of_split (M := Module.End R (Fin (nn R M) → R)) (inclusion' R M) (projection' R M)
    <| projection'_inclusion' R M


-- @@ L418-420 verbatim
instance _root_.Module.Finite.End (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M] : Module.Finite R (Module.End R M) :=
  Module.Finite.of_surjective (projection' R M) (projection'_surj R M)


-- @@ L422-428 verbatim
instance (M : Type v) [AddCommGroup M] [Module R M] [FaithfulSMul R M] :
    FaithfulSMul R (Module.End R M) where
  eq_of_smul_eq_smul {r1 r2} h12 := by
    specialize h12 1
    rw [LinearMap.ext_iff] at h12
    simp only [LinearMap.smul_apply, Module.End.one_apply] at h12
    exact eq_of_smul_eq_smul h12


-- @@ L430-433 verbatim
/-- The matrix algebra as a bundled Azumaya algebra. -/
abbrev MatrixAlg (n : ℕ) [NeZero n] : Azumaya R := {
  __ := AlgCat.of R (_root_.Matrix (Fin n) (Fin n) R)
  isAzumaya := IsAzumaya.matrix R (Fin n) }


-- @@ L435-440 verbatim
/-- The endomorphism algebra of `R^n` as a bundled Azumaya algebra. -/
abbrev EndRn (n : ℕ) [NeZero n] : Azumaya R := {
  __ := AlgCat.of R (Module.End R (Fin n → R))
  isAzumaya := IsAzumaya.ofAlgEquiv R _ _
    LinearMap.toMatrixAlgEquiv'.symm <| IsAzumaya.matrix R (Fin n)
}


-- @@ L442-443 verbatim
variable (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M]


-- @@ L445-445 verbatim
open MulOpposite


-- @@ L447-451 verbatim
/-- Tensor inclusion on endomorphism algebras induced by `inclusion'`. -/
abbrev tensorInclusion1' : (Module.End R M) ⊗[R] (Module.End R M)ᵐᵒᵖ →ₗ[R]
    (Module.End R (Fin (nn R M) → R)) ⊗[R] (Module.End R (Fin (nn R M) → R))ᵐᵒᵖ :=
  TensorProduct.map (inclusion' R M) <|
    (opLinearEquiv R).toLinearMap ∘ₗ (inclusion' R M) ∘ₗ (opLinearEquiv R).symm.toLinearMap


-- @@ L453-458 verbatim
/-- Tensor projection on endomorphism algebras induced by `projection'`. -/
abbrev tensorProjection1' :
    Module.End R (Fin (nn R M) → R) ⊗[R] (Module.End R (Fin (nn R M) → R))ᵐᵒᵖ →ₗ[R]
      Module.End R M ⊗[R] (Module.End R M)ᵐᵒᵖ :=
  TensorProduct.map (projection' R M) <|
    (opLinearEquiv R).toLinearMap ∘ₗ (projection' R M) ∘ₗ (opLinearEquiv R).symm.toLinearMap


-- @@ L460-464 verbatim
lemma tensor_projection_inclusion1' : tensorProjection1' R M ∘ₗ tensorInclusion1' R M = .id := by
  ext f g
  change (projection' R M ∘ₗ inclusion' R M) f ⊗ₜ[R]
    op ((projection' R M ∘ₗ inclusion' R M) g.unop) = f ⊗ₜ[R] g
  simp only [projection'_inclusion', LinearMap.id_apply, op_unop]


-- @@ L466-468 verbatim
lemma tensorInclusion1'_inj : Function.Injective (tensorInclusion1' R M) :=
  Function.LeftInverse.injective (g := tensorProjection1' R M)
    <| DFunLike.congr_fun <| tensor_projection_inclusion1' R M


-- @@ L470-475 verbatim
/-- Inclusion between second endomorphism algebras induced by the free-module splitting. -/
abbrev inclusion2' : Module.End R (Module.End R M) →ₗ[R]
    Module.End R (Module.End R (Fin (nn R M) → R)) where
  toFun f := inclusion' R M ∘ₗ f ∘ₗ projection' R M
  map_add' _ _ := by simp [LinearMap.add_comp, LinearMap.comp_add]
  map_smul' := by simp [LinearMap.smul_comp, LinearMap.comp_smul]


-- @@ L477-482 verbatim
/-- Projection between second endomorphism algebras induced by the free-module splitting. -/
abbrev projection2' : Module.End R (Module.End R (Fin (nn R M) → R)) →ₗ[R]
    Module.End R (Module.End R M) where
  toFun f := projection' R M ∘ₗ f ∘ₗ inclusion' R M
  map_add' _ _ := by simp [LinearMap.add_comp, LinearMap.comp_add]
  map_smul' := by simp [LinearMap.smul_comp, LinearMap.comp_smul]


-- @@ L484-488 verbatim
lemma projection2'_inclusion2' : projection2' R M ∘ₗ inclusion2' R M = LinearMap.id := by
  ext f : 1
  change (projection' R M ∘ₗ inclusion' R M) ∘ₗ f ∘ₗ
    (projection' R M ∘ₗ inclusion' R M) = f
  rw [projection'_inclusion', LinearMap.id_comp, LinearMap.comp_id]


-- @@ L490-491 verbatim
lemma projection2'_surj : Function.Surjective (projection2' R M) :=
  Function.RightInverse.surjective <| DFunLike.congr_fun <| projection2'_inclusion2' R M


-- @@ L493-514 verbatim
/--
End R M ⊗ (End R M)ᵐᵒᵖ ------------> End R (End R M)
    |         |                        |      |
    |         |                        |      |
    |         |                        |      |
    |         |                        |      |
End R Rⁿ ⊗ (End R Rⁿ)ᵐᵒᵖ ----------> End R (End R Rⁿ)
-/
lemma comm_square_endend :
    inclusion2' R M ∘ₗ (AlgHom.mulLeftRight R (Module.End R M)).toLinearMap =
    (AlgHom.mulLeftRight R (Module.End R (Fin (nn R M) → R))).toLinearMap ∘ₗ
      (tensorInclusion1' R M) := by
  ext f1 g1 : 3
  apply LinearMap.ext
  intro f2
  simp only [TensorProduct.AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_comp,
    TensorProduct.curry_apply, LinearMap.coe_comp, LinearMap.coe_restrictScalars, LinearMap.coe_mk,
    AddHom.coe_mk, Function.comp_apply, AlgHom.toLinearMap_apply,
    TensorProduct.map_tmul, LinearEquiv.coe_coe, coe_opLinearEquiv, coe_opLinearEquiv_symm,
    AlgHom.mulLeftRight_apply, unop_op]
  ext i j
  simp


-- @@ L516-529 verbatim
lemma comm_square_endend' :
    (AlgHom.mulLeftRight R (Module.End R M)).toLinearMap ∘ₗ tensorProjection1' R M =
    projection2' R M ∘ₗ
      (AlgHom.mulLeftRight R (Module.End R (Fin (nn R M) → R))).toLinearMap := by
  ext f1 g1 : 3
  apply LinearMap.ext
  intro f2
  simp only [TensorProduct.AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_comp,
    TensorProduct.curry_apply, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
    Function.comp_apply, TensorProduct.map_tmul, LinearMap.coe_mk, AddHom.coe_mk,
    LinearEquiv.coe_coe, coe_opLinearEquiv, coe_opLinearEquiv_symm, AlgHom.toLinearMap_apply,
    AlgHom.mulLeftRight_apply, unop_op]
  ext m
  simp


-- @@ L531-531 verbatim
variable [Nontrivial M]


-- @@ L533-540 verbatim
instance : NeZero (nn R M) := ⟨by
  by_contra! hn
  have : Subsingleton (Fin (nn R M) → R) := by
    rw [hn]
    exact Unique.instSubsingleton
  have : Subsingleton M := Function.Surjective.subsingleton (f0_surj R M)
  have : ¬ (Subsingleton M) := not_subsingleton_iff_nontrivial.2 inferInstance
  tauto⟩


-- @@ L542-547 verbatim
lemma inj_endM : Function.Injective (AlgHom.mulLeftRight R (Module.End R M)) := by
  refine .of_comp (f := inclusion2' R M) ?_
  suffices Function.Injective ((inclusion2' R M) ∘ₗ (AlgHom.mulLeftRight _ _).toLinearMap) by
    rw [LinearMap.coe_comp] at this; exact this
  rw [comm_square_endend, LinearMap.coe_comp]
  exact (EndRn R (nn R M)).isAzumaya.bij.injective.comp <| tensorInclusion1'_inj R M


-- @@ L549-554 verbatim
lemma surj_endM : Function.Surjective (AlgHom.mulLeftRight R (Module.End R M)) := by
  refine .of_comp (g := tensorProjection1' R M) ?_
  change Function.Surjective
    ((AlgHom.mulLeftRight R (Module.End R M)).toLinearMap ∘ₗ tensorProjection1' R M)
  rw [comm_square_endend', LinearMap.coe_comp]
  exact (projection2'_surj R M).comp (EndRn R (nn R M)).isAzumaya.bij.surjective


-- @@ L556-557 verbatim
lemma bij_endM : Function.Bijective (AlgHom.mulLeftRight R (Module.End R M)) :=
  ⟨inj_endM R M, surj_endM R M⟩


-- @@ L559-563 verbatim
/-- The endomorphism algebra of a faithful finite projective module is Azumaya. -/
abbrev ofEnd [FaithfulSMul R M] : Azumaya R where
  __ := AlgCat.of R (Module.End R M)
  isAzumaya.out := Module.Projective.ofEnd R M|>.out
  isAzumaya.bij := bij_endM R M


-- @@ L565-565 verbatim
end Azumaya
