/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import RepresentationTheory.Alignment.Attribute


-- @@ L14-14 verbatim
/-! # Tensor operations -/


-- @@ L16-16 verbatim
namespace RepresentationTheory.LinearAlgebra.TensorOperations


-- @@ L18-18 verbatim
open PiTensorProduct

-- @@ L19-19 verbatim
open scoped TensorProduct


-- @@ L21-21 verbatim
section Defs


-- @@ L23-23 verbatim
variable (k : Type*) [CommRing k] (V : Type*) [AddCommGroup V] [Module k V]


-- @@ L25-27 verbatim
/-- A type-valued construction determined by the displayed parameters. -/
@[source_ref "Chapter2/Discussion_pure_tensors" (role := supporting)]
abbrev AuxiliaryType_aux2 (n : ℕ) : Type _ := ⨂[k] (_ : Fin n), V


-- @@ L29-29 verbatim
variable {k V}


-- @@ L31-33 verbatim
/-- A linear equivalence between the displayed modules. -/
def linearEquiv_aux1 {n : ℕ} (σ : Equiv.Perm (Fin n)) : AuxiliaryType_aux2 k V n ≃ₗ[k] AuxiliaryType_aux2 k V n :=
  PiTensorProduct.reindex k (fun _ : Fin n => V) σ


-- @@ L35-39 verbatim
/-- The displayed tensor expressions are equal. -/
@[simp]
lemma tensor_eq_aux1 {n : ℕ} (σ : Equiv.Perm (Fin n)) (f : Fin n → V) :
    linearEquiv_aux1 σ (PiTensorProduct.tprod k f) = PiTensorProduct.tprod k fun i => f (σ.symm i) :=
  PiTensorProduct.reindex_tprod (s := fun _ : Fin n => V) σ f


-- @@ L41-41 verbatim
variable (k V)


-- @@ L43-47 verbatim
/-- The submodule specified by the displayed construction. -/
@[source_ref "Chapter2/Problem2.11.3" (role := supporting)]
def submodule_aux1 (n : ℕ) : Submodule k (AuxiliaryType_aux2 k V n) :=
  Submodule.span k {D : AuxiliaryType_aux2 k V n | ∃ (T : AuxiliaryType_aux2 k V n) (i j : Fin n), i ≠ j ∧
    D = T - linearEquiv_aux1 (Equiv.swap i j) T}


-- @@ L49-53 verbatim
/-- The submodule specified by the displayed construction. -/
@[source_ref "Chapter2/Problem2.11.3" (role := supporting)]
def submodule (n : ℕ) : Submodule k (AuxiliaryType_aux2 k V n) :=
  Submodule.span k {T : AuxiliaryType_aux2 k V n | ∃ i j : Fin n, i ≠ j ∧
    linearEquiv_aux1 (Equiv.swap i j) T = T}


-- @@ L55-57 verbatim
/-- A type-valued construction determined by the displayed parameters. -/
@[source_ref "Chapter2/Problem2.11.3" (role := supporting)]
abbrev AuxiliaryType_aux1 (n : ℕ) : Type _ := AuxiliaryType_aux2 k V n ⧸ submodule_aux1 k V n


-- @@ L59-61 verbatim
/-- A type-valued construction determined by the displayed parameters. -/
@[source_ref "Chapter2/Problem2.11.3" (role := supporting)]
abbrev AuxiliaryType (n : ℕ) : Type _ := AuxiliaryType_aux2 k V n ⧸ submodule k V n


-- @@ L63-65 verbatim
/-- A multilinear map on the displayed family of modules. -/
def multilinearMap (n : ℕ) : MultilinearMap k (fun _ : Fin n => V) (AuxiliaryType_aux1 k V n) :=
  (submodule_aux1 k V n).mkQ.compMultilinearMap (PiTensorProduct.tprod k)


-- @@ L67-70 verbatim
/-- The displayed tensor expressions are equal. -/
@[simp]
lemma tensor_eq_aux3 {n : ℕ} (f : Fin n → V) :
    multilinearMap k V n f = (submodule_aux1 k V n).mkQ (PiTensorProduct.tprod k f) := rfl


-- @@ L72-72 verbatim
end Defs


-- @@ L74-74 verbatim
section Basic


-- @@ L76-77 verbatim
variable {k : Type*} [CommRing k] {V W : Type*}
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]


-- @@ L79-84 verbatim
/-- The displayed map sends the specified input to the stated value. -/
@[simp]
lemma map_apply_aux4 {n : ℕ} (T : AuxiliaryType_aux2 k V n) : linearEquiv_aux1 (1 : Equiv.Perm (Fin n)) T = T := by
  rw [linearEquiv_aux1, show (1 : Equiv.Perm (Fin n)) = Equiv.refl (Fin n) from rfl,
    PiTensorProduct.reindex_refl]
  rfl


-- @@ L86-89 verbatim
/-- The displayed map sends the specified input to the stated value. -/
lemma map_apply_aux3 {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (T : AuxiliaryType_aux2 k V n) :
    linearEquiv_aux1 (σ * τ) T = linearEquiv_aux1 σ (linearEquiv_aux1 τ T) := by
  rw [linearEquiv_aux1, linearEquiv_aux1, linearEquiv_aux1, Equiv.Perm.mul_def, ← PiTensorProduct.reindex_reindex]


-- @@ L91-102 verbatim
/-- The specified element belongs to the indicated submodule. -/
lemma mem_submodule {n : ℕ} (f : Fin n → V) {i j : Fin n} (hij : i ≠ j)
    (hf : f i = f j) : PiTensorProduct.tprod k f ∈ submodule k V n := by
  refine Submodule.subset_span ⟨i, j, hij, ?_⟩
  rw [tensor_eq_aux1, Equiv.symm_swap]
  congr 1
  funext l
  rcases eq_or_ne l i with rfl | hli
  · rw [Equiv.swap_apply_left]; exact hf.symm
  · rcases eq_or_ne l j with rfl | hlj
    · rw [Equiv.swap_apply_right]; exact hf
    · rw [Equiv.swap_apply_of_ne_of_ne hli hlj]


-- @@ L104-109 verbatim
/-- A distinguished value of the displayed type. -/
def distinguishedElement_aux1 (k : Type*) [CommRing k] (V : Type*) [AddCommGroup V] [Module k V] (n : ℕ) :
    V [⋀^Fin n]→ₗ[k] AuxiliaryType k V n where
  toMultilinearMap := (submodule k V n).mkQ.compMultilinearMap (PiTensorProduct.tprod k)
  map_eq_zero_of_eq' f i j hf hij := by
    simpa using (Submodule.Quotient.mk_eq_zero _).2 (mem_submodule f hij hf)


-- @@ L111-114 verbatim
/-- The displayed tensor expressions are equal. -/
@[simp]
lemma tensor_eq {n : ℕ} (f : Fin n → V) :
    distinguishedElement_aux1 k V n f = (submodule k V n).mkQ (PiTensorProduct.tprod k f) := rfl


-- @@ L116-123 verbatim
/-- The displayed map sends the specified input to the stated value. -/
lemma map_apply_aux7 {n : ℕ} (f : Fin n → V) {i j : Fin n} (hij : i ≠ j) :
    multilinearMap k V n (fun l => f (Equiv.swap i j l)) = multilinearMap k V n f := by
  have h : PiTensorProduct.tprod k f -
      PiTensorProduct.tprod k (fun l => f (Equiv.swap i j l)) ∈ submodule_aux1 k V n := by
    refine Submodule.subset_span ⟨PiTensorProduct.tprod k f, i, j, hij, ?_⟩
    rw [tensor_eq_aux1, Equiv.symm_swap]
  simpa [tensor_eq_aux3, Submodule.mkQ_apply] using ((Submodule.Quotient.eq _).2 h).symm


-- @@ L125-134 verbatim
/-- The displayed map sends the specified input to the stated value. -/
lemma map_apply_aux6 {n : ℕ} (σ : Equiv.Perm (Fin n)) (f : Fin n → V) :
    multilinearMap k V n (fun l => f (σ l)) = multilinearMap k V n f := by
  induction σ using Equiv.Perm.swap_induction_on generalizing f with
  | one => simp
  | swap_mul τ i j hij ihτ =>
      have e1 : multilinearMap k V n (fun l => f ((Equiv.swap i j * τ) l))
          = multilinearMap k V n fun m => f (Equiv.swap i j m) :=
        ihτ fun m => f (Equiv.swap i j m)
      exact e1.trans (map_apply_aux7 f hij)


-- @@ L136-136 verbatim
end Basic


-- @@ L138-138 verbatim
section Functoriality


-- @@ L140-141 verbatim
variable {k : Type*} [CommRing k] {V W U : Type*}
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] [AddCommGroup U] [Module k U]


-- @@ L143-146 verbatim
/-- A linear map between the displayed modules. -/
@[source_ref "Chapter2/Problem2.11.3" (role := supporting)]
def linearMap_aux3 (A : V →ₗ[k] W) (n : ℕ) : AuxiliaryType_aux2 k V n →ₗ[k] AuxiliaryType_aux2 k W n :=
  PiTensorProduct.map fun _ : Fin n => A


-- @@ L148-152 verbatim
/-- The displayed tensor expressions are equal. -/
@[simp]
lemma tensor_eq_aux4 (A : V →ₗ[k] W) {n : ℕ} (f : Fin n → V) :
    linearMap_aux3 A n (PiTensorProduct.tprod k f) = PiTensorProduct.tprod k fun i => A (f i) :=
  PiTensorProduct.map_tprod _ _


-- @@ L154-160 verbatim
/-- The displayed map sends the specified input to the stated value. -/
lemma map_apply_aux8 (A : V →ₗ[k] W) {n : ℕ} (σ : Equiv.Perm (Fin n))
    (T : AuxiliaryType_aux2 k V n) :
    linearMap_aux3 A n (linearEquiv_aux1 σ T) = linearEquiv_aux1 σ (linearMap_aux3 A n T) := by
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r f => simp
  | add x y hx hy => simp [hx, hy]


-- @@ L162-168 verbatim
/-- The first displayed submodule is contained in the second. -/
lemma submodule_le_aux2 (A : V →ₗ[k] W) (n : ℕ) :
    submodule_aux1 k V n ≤ (submodule_aux1 k W n).comap (linearMap_aux3 A n) := by
  rw [submodule_aux1, Submodule.span_le]
  rintro _ ⟨T, i, j, hij, rfl⟩
  refine Submodule.subset_span ⟨linearMap_aux3 A n T, i, j, hij, ?_⟩
  rw [map_sub, map_apply_aux8]


-- @@ L170-176 verbatim
/-- The first displayed submodule is contained in the second. -/
lemma submodule_le (A : V →ₗ[k] W) (n : ℕ) :
    submodule k V n ≤ (submodule k W n).comap (linearMap_aux3 A n) := by
  rw [submodule, Submodule.span_le]
  rintro T ⟨i, j, hij, hT⟩
  refine Submodule.subset_span ⟨i, j, hij, ?_⟩
  rw [← map_apply_aux8, hT]


-- @@ L178-181 verbatim
/-- A linear map between the displayed modules. -/
@[source_ref "Chapter2/Problem2.11.3" (role := supporting)]
def linearMap_aux2 (A : V →ₗ[k] W) (n : ℕ) : AuxiliaryType_aux1 k V n →ₗ[k] AuxiliaryType_aux1 k W n :=
  Submodule.mapQ _ _ (linearMap_aux3 A n) (submodule_le_aux2 A n)


-- @@ L183-186 verbatim
/-- A linear map between the displayed modules. -/
@[source_ref "Chapter2/Problem2.11.3" (role := supporting)]
def linearMap (A : V →ₗ[k] W) (n : ℕ) : AuxiliaryType k V n →ₗ[k] AuxiliaryType k W n :=
  Submodule.mapQ _ _ (linearMap_aux3 A n) (submodule_le A n)


-- @@ L188-191 verbatim
/-- The displayed map sends the specified input to the stated value. -/
lemma map_apply_aux5 (A : V →ₗ[k] W) {n : ℕ} (f : Fin n → V) :
    linearMap_aux2 A n (multilinearMap k V n f) = multilinearMap k W n fun i => A (f i) := by
  simp [linearMap_aux2, multilinearMap, Submodule.mapQ_apply]


-- @@ L193-196 verbatim
/-- The displayed map sends the specified input to the stated value. -/
lemma map_apply (A : V →ₗ[k] W) {n : ℕ} (f : Fin n → V) :
    linearMap A n (distinguishedElement_aux1 k V n f) = distinguishedElement_aux1 k W n fun i => A (f i) := by
  simp [linearMap, distinguishedElement_aux1, Submodule.mapQ_apply]


-- @@ L198-205 verbatim
/-- The two displayed expressions are equal. -/
@[simp]
lemma displayed_eq_aux1 (n : ℕ) : linearMap_aux2 (LinearMap.id : V →ₗ[k] V) n = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨T, rfl⟩ := Submodule.mkQ_surjective _ x
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r f => simpa using congrArg (r • ·) (map_apply_aux5 LinearMap.id f)
  | add a b ha hb => simp only [map_add, ha, hb]


-- @@ L207-214 verbatim
/-- The two displayed expressions are equal. -/
@[simp]
lemma displayed_eq (n : ℕ) : linearMap (LinearMap.id : V →ₗ[k] V) n = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨T, rfl⟩ := Submodule.mkQ_surjective _ x
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r f => simpa using congrArg (r • ·) (map_apply LinearMap.id f)
  | add a b ha hb => simp only [map_add, ha, hb]


-- @@ L216-231 verbatim
/-- The composite of the displayed linear maps is the stated map. -/
@[source_ref "Chapter2/Problem2.11.3" (role := supporting)]
lemma linearMap_comp_eq_aux2 (A : W →ₗ[k] U) (B : V →ₗ[k] W) (n : ℕ) :
    linearMap_aux2 (A ∘ₗ B) n = linearMap_aux2 A n ∘ₗ linearMap_aux2 B n := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨T, rfl⟩ := Submodule.mkQ_surjective _ x
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r f =>
      simp only [map_smul, LinearMap.comp_apply]
      congr 1
      have h1 := map_apply_aux5 (A ∘ₗ B) f
      have h2 := map_apply_aux5 A fun i => B (f i)
      have h3 := map_apply_aux5 B f
      simp only [tensor_eq_aux3, Submodule.mkQ_apply, LinearMap.comp_apply] at h1 h2 h3 ⊢
      rw [h1, h3, h2]
  | add a b ha hb => simp only [map_add, ha, hb, LinearMap.comp_apply]


-- @@ L233-248 verbatim
/-- The composite of the displayed linear maps is the stated map. -/
@[source_ref "Chapter2/Problem2.11.3" (role := supporting)]
lemma linearMap_comp_eq (A : W →ₗ[k] U) (B : V →ₗ[k] W) (n : ℕ) :
    linearMap (A ∘ₗ B) n = linearMap A n ∘ₗ linearMap B n := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨T, rfl⟩ := Submodule.mkQ_surjective _ x
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r f =>
      simp only [map_smul, LinearMap.comp_apply]
      congr 1
      have h1 := map_apply (A ∘ₗ B) f
      have h2 := map_apply A fun i => B (f i)
      have h3 := map_apply B f
      simp only [tensor_eq, Submodule.mkQ_apply, LinearMap.comp_apply] at h1 h2 h3 ⊢
      rw [h1, h3, h2]
  | add a b ha hb => simp only [map_add, ha, hb, LinearMap.comp_apply]


-- @@ L250-250 verbatim
end Functoriality


-- @@ L252-252 verbatim
section ExteriorComparison


-- @@ L254-255 verbatim
variable {k : Type*} [CommRing k] {V W : Type*}
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]


-- @@ L257-260 verbatim
variable (k V) in
/-- A linear map between the displayed modules. -/
noncomputable def linearMap_aux1 (n : ℕ) : (⋀[k]^n V) →ₗ[k] AuxiliaryType k V n :=
  exteriorPower.alternatingMapLinearEquiv (distinguishedElement_aux1 k V n)


-- @@ L262-266 verbatim
/-- The displayed map sends the specified input to the stated value. -/
@[simp]
lemma map_apply_aux1 {n : ℕ} (f : Fin n → V) :
    linearMap_aux1 k V n (exteriorPower.ιMulti k n f) = distinguishedElement_aux1 k V n f :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _


-- @@ L268-279 verbatim
/-- The displayed map is surjective. -/
theorem map_surjective (n : ℕ) :
    Function.Surjective (linearMap_aux1 k V n) := by
  intro x
  obtain ⟨T, rfl⟩ := Submodule.mkQ_surjective _ x
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r f =>
      exact ⟨r • exteriorPower.ιMulti k n f, by simp⟩
  | add a b ha hb =>
      obtain ⟨u, hu⟩ := ha
      obtain ⟨v, hv⟩ := hb
      exact ⟨u + v, by rw [map_add, hu, hv, map_add]⟩


-- @@ L281-284 verbatim
variable (k V) in
/-- A linear map between the displayed modules. -/
noncomputable def linearMap_aux4 (n : ℕ) : AuxiliaryType_aux2 k V n →ₗ[k] ⋀[k]^n V :=
  PiTensorProduct.lift (exteriorPower.ιMulti k n).toMultilinearMap


-- @@ L286-290 verbatim
/-- The displayed tensor expressions are equal. -/
@[simp]
lemma tensor_eq_aux5 {n : ℕ} (f : Fin n → V) :
    linearMap_aux4 k V n (PiTensorProduct.tprod k f) = exteriorPower.ιMulti k n f :=
  PiTensorProduct.lift.tprod _


-- @@ L292-303 verbatim
/-- Swapping two distinct inputs negates the value of the displayed alternating construction. -/
lemma alternatingForm_swap {n : ℕ} {i j : Fin n} (hij : i ≠ j) (T : AuxiliaryType_aux2 k V n) :
    linearMap_aux4 k V n (linearEquiv_aux1 (Equiv.swap i j) T)
      = - linearMap_aux4 k V n T := by
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r f =>
      have h : exteriorPower.ιMulti k n (fun l => f (Equiv.swap i j l))
          = - exteriorPower.ιMulti k n f :=
        (exteriorPower.ιMulti k n).map_swap (v := f) hij
      simp only [map_smul, tensor_eq_aux1, Equiv.symm_swap, tensor_eq_aux5, h,
        smul_neg]
  | add a b ha hb => simp only [map_add, ha, hb, neg_add]


-- @@ L305-313 verbatim
/-- The composite of the displayed linear maps is the stated map. -/
lemma linearMap_comp_eq_aux1 (A : V →ₗ[k] W) (n : ℕ) :
    linearMap A n ∘ₗ linearMap_aux1 k V n
      = linearMap_aux1 k W n ∘ₗ exteriorPower.map n A := by
  refine LinearMap.ext_on (exteriorPower.ιMulti_span k n V) ?_
  rintro _ ⟨f, rfl⟩
  simp only [LinearMap.comp_apply, map_apply_aux1,
    exteriorPower.map_apply_ιMulti]
  simpa [Function.comp_def] using map_apply A f


-- @@ L315-326 verbatim
/-- The displayed tensor expressions are equal. -/
lemma tensor_eq_aux2 {I : Type*} (b : Module.Basis I k V) {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (T : AuxiliaryType_aux2 k V n) (g : Fin n → I) :
    (_root_.Basis.piTensorProduct fun _ : Fin n => b).repr (linearEquiv_aux1 σ T) g
      = (_root_.Basis.piTensorProduct fun _ : Fin n => b).repr T (g ∘ σ) := by
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r f =>
      simp only [map_smul, tensor_eq_aux1, Finsupp.smul_apply,
        _root_.Basis.piTensorProduct_repr_tprod_apply, Function.comp_apply]
      exact congrArg (r • ·)
        (Fintype.prod_equiv σ _ _ fun l => by rw [Equiv.symm_apply_apply]).symm
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]


-- @@ L328-367 verbatim
/-- The displayed map sends the specified input to the stated value. -/
lemma map_apply_aux9 {I : Type*} (b : Module.Basis I k V)
    {n : ℕ} {i j : Fin n} (hij : i ≠ j) {T : AuxiliaryType_aux2 k V n}
    (hT : linearEquiv_aux1 (Equiv.swap i j) T = T) :
    linearMap_aux4 k V n T = 0 := by
  classical

  have hcs : ∀ g : Fin n → I,
      (_root_.Basis.piTensorProduct fun _ : Fin n => b).repr T (g ∘ Equiv.swap i j)
        = (_root_.Basis.piTensorProduct fun _ : Fin n => b).repr T g := by
    intro g
    rw [← tensor_eq_aux2 b (Equiv.swap i j) T g, hT]

  have hexp : linearMap_aux4 k V n T
      = ∑ g ∈ ((_root_.Basis.piTensorProduct fun _ : Fin n => b).repr T).support,
          (_root_.Basis.piTensorProduct fun _ : Fin n => b).repr T g •
            exteriorPower.ιMulti k n fun l => b (g l) := by
    conv_lhs => rw [← (_root_.Basis.piTensorProduct fun _ : Fin n => b).linearCombination_repr T]
    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    exact Finset.sum_congr rfl fun g _ => by simp [_root_.Basis.piTensorProduct_apply]
  rw [hexp]
  refine Finset.sum_involution (fun g _ => g ∘ Equiv.swap i j) ?_ ?_ ?_ ?_
  · intro g _
    have hswap : (exteriorPower.ιMulti k n fun l => b ((g ∘ Equiv.swap i j) l))
        = -exteriorPower.ιMulti k n fun l => b (g l) :=
      (exteriorPower.ιMulti k n).map_swap (v := fun l => b (g l)) hij
    rw [hswap, hcs g, smul_neg, add_neg_cancel]
  · intro g _ hF hgs
    refine hF ?_
    have hgij : b (g i) = b (g j) := by
      have h := congrFun hgs i
      simp only [Function.comp_apply, Equiv.swap_apply_left] at h
      rw [h]
    rw [(exteriorPower.ιMulti k n).map_eq_zero_of_eq (fun l => b (g l)) hgij hij, smul_zero]
  · intro g hg
    rw [Finsupp.mem_support_iff] at hg ⊢
    rwa [hcs g]
  · intro g _
    funext l
    simp


-- @@ L369-369 verbatim
end ExteriorComparison


-- @@ L371-371 verbatim
section ExteriorEquiv


-- @@ L373-373 verbatim
variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]


-- @@ L375-381 verbatim
/-- The first displayed submodule is contained in the second. -/
lemma submodule_le_aux1 (n : ℕ) :
    submodule k V n ≤ LinearMap.ker (linearMap_aux4 k V n) := by
  rw [submodule, Submodule.span_le]
  rintro T ⟨i, j, hij, hT⟩
  exact map_apply_aux9
    (Module.Basis.ofVectorSpace k V) hij hT


-- @@ L383-395 verbatim
/-- A linear equivalence between the displayed modules. -/
noncomputable def linearEquiv (n : ℕ) :
    (⋀[k]^n V) ≃ₗ[k] AuxiliaryType k V n := by
  refine LinearEquiv.ofLinear (linearMap_aux1 k V n)
    (Submodule.liftQ _ (linearMap_aux4 k V n) (submodule_le_aux1 n)) ?_ ?_
  · refine LinearMap.ext fun x => ?_
    obtain ⟨T, rfl⟩ := Submodule.mkQ_surjective _ x
    induction T using PiTensorProduct.induction_on with
    | smul_tprod r f => simp
    | add a b ha hb => simp only [map_add, ha, hb]
  · refine LinearMap.ext_on (exteriorPower.ιMulti_span k n V) ?_
    rintro _ ⟨f, rfl⟩
    simp


-- @@ L397-401 verbatim
/-- The displayed map sends the specified input to the stated value. -/
@[simp]
lemma map_apply_aux2 {n : ℕ} (f : Fin n → V) :
    linearEquiv (V := V) n (exteriorPower.ιMulti k n f) = distinguishedElement_aux1 k V n f :=
  map_apply_aux1 f


-- @@ L403-408 verbatim
/-- A distinguished value of the displayed type. -/
@[source_ref "Chapter2/Problem2.11.3" (role := supporting)]
noncomputable def distinguishedElement {I : Type*} [LinearOrder I]
    (b : Module.Basis I k V) (n : ℕ) :
    Module.Basis (Set.powersetCard I n) k (AuxiliaryType k V n) :=
  (b.exteriorPower n).map (linearEquiv n)


-- @@ L410-414 verbatim
/-- The finite rank of the displayed module has the stated value. -/
@[source_ref "Chapter2/Problem2.11.3" (role := primary)]
theorem finrank_eq [Module.Finite k V] (n : ℕ) :
    Module.finrank k (AuxiliaryType k V n) = (Module.finrank k V).choose n := by
  rw [← (linearEquiv (V := V) n).finrank_eq, exteriorPower.finrank_eq]


-- @@ L416-416 verbatim
end ExteriorEquiv


-- @@ L418-418 verbatim
section TopDegree


-- @@ L420-420 verbatim
variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]


-- @@ L422-442 verbatim
/-- Applying an endomorphism to every factor of a top exterior product scales it by the determinant. -/
theorem exteriorPower_iota_map [FiniteDimensional k V] {N : ℕ} (hN : Module.finrank k V = N)
    (A : V →ₗ[k] V) (f : Fin N → V) :
    exteriorPower.ιMulti k N (fun i => A (f i))
      = LinearMap.det A • exteriorPower.ιMulti k N f := by
  classical
  set b := Module.finBasisOfFinrankEq k V hN with hb
  haveI : FiniteDimensional k (⋀[k]^N V) := Module.Finite.of_basis (b.exteriorPower N)

  set D : ⋀[k]^N V →ₗ[k] k := exteriorPower.alternatingMapLinearEquiv b.det with hD
  have hDsurj : Function.Surjective D := by
    intro c
    exact ⟨c • exteriorPower.ιMulti k N b, by simp [hD, Module.Basis.det_self]⟩
  have hrank : Module.finrank k (⋀[k]^N V) = Module.finrank k k := by
    rw [exteriorPower.finrank_eq, hN, Nat.choose_self, Module.finrank_self]
  have hDinj : Function.Injective D :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mpr hDsurj
  apply hDinj
  rw [map_smul, hD]
  simp only [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, smul_eq_mul]
  exact Module.Basis.det_comp b A f


-- @@ L444-451 verbatim
/-- The top exterior-power map is determinant scaling of the identity. -/
theorem exteriorPower_map_top [FiniteDimensional k V] {N : ℕ} (hN : Module.finrank k V = N)
    (A : V →ₗ[k] V) :
    exteriorPower.map N A = LinearMap.det A • (LinearMap.id : ⋀[k]^N V →ₗ[k] ⋀[k]^N V) := by
  refine LinearMap.ext_on (exteriorPower.ιMulti_span k N V) ?_
  rintro _ ⟨f, rfl⟩
  rw [exteriorPower.map_apply_ιMulti]
  simpa [Function.comp_def] using exteriorPower_iota_map hN A f


-- @@ L453-463 verbatim
/-- The induced map in top degree is determinant scaling of the identity. -/
@[source_ref "Chapter2/Problem2.11.3" (role := primary)]
theorem topExteriorPower_map [FiniteDimensional k V] {N : ℕ} (hN : Module.finrank k V = N)
    (A : V →ₗ[k] V) :
    linearMap A N = LinearMap.det A • (LinearMap.id : AuxiliaryType k V N →ₗ[k] AuxiliaryType k V N) := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨y, rfl⟩ := map_surjective (k := k) (V := V) N x
  have h := LinearMap.congr_fun (linearMap_comp_eq_aux1 A N) y
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
  rw [h, exteriorPower_map_top hN A]
  simp


-- @@ L465-479 verbatim
/-- The determinant of a composite endomorphism is the product of the two determinants. -/
@[source_ref "Chapter2/Problem2.11.3" (role := supporting)]
theorem det_comp [FiniteDimensional k V] {N : ℕ}
    (hN : Module.finrank k V = N) (A B : V →ₗ[k] V) :
    LinearMap.det (A ∘ₗ B) = LinearMap.det A * LinearMap.det B := by
  have hrank : Module.finrank k (AuxiliaryType k V N) = 1 := by
    rw [finrank_eq N, hN, Nat.choose_self]
  haveI : Nontrivial (AuxiliaryType k V N) :=
    Module.nontrivial_of_finrank_pos (R := k) (by rw [hrank]; exact Nat.zero_lt_succ 0)
  obtain ⟨x, hx⟩ := exists_ne (0 : AuxiliaryType k V N)
  have h := linearMap_comp_eq A B N
  rw [topExteriorPower_map hN (A ∘ₗ B), topExteriorPower_map hN A, topExteriorPower_map hN B] at h
  have hx' := LinearMap.congr_fun h x
  simp only [LinearMap.smul_apply, LinearMap.id_apply, LinearMap.comp_apply, smul_smul] at hx'
  exact smul_left_injective k hx hx'


-- @@ L481-481 verbatim
end TopDegree


-- @@ L483-483 verbatim
end RepresentationTheory.LinearAlgebra.TensorOperations


-- @@ L485-493 verbatim
attribute [nolint defsWithUnderscore]
  RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux2 RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv_aux1
  RepresentationTheory.LinearAlgebra.TensorOperations.submodule_aux1 RepresentationTheory.LinearAlgebra.TensorOperations.submodule
  RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux1 RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType
  RepresentationTheory.LinearAlgebra.TensorOperations.multilinearMap RepresentationTheory.LinearAlgebra.TensorOperations.distinguishedElement_aux1
  RepresentationTheory.LinearAlgebra.TensorOperations.linearMap_aux3 RepresentationTheory.LinearAlgebra.TensorOperations.linearMap_aux2
  RepresentationTheory.LinearAlgebra.TensorOperations.linearMap RepresentationTheory.LinearAlgebra.TensorOperations.linearMap_aux1
  RepresentationTheory.LinearAlgebra.TensorOperations.linearMap_aux4 RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv
  RepresentationTheory.LinearAlgebra.TensorOperations.distinguishedElement
