/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolai Kashcheev, Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.Vector.Pre.Modules

-- @@ L9-15 verbatim
/-!

# Complex Lorentz vectors

We define complex Lorentz vectors in 4d space-time as representations of SL(2, C).

-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
open Module Matrix

-- @@ L22-22 verbatim
open MatrixGroups

-- @@ L23-23 verbatim
open Complex

-- @@ L24-24 verbatim
open TensorProduct


-- @@ L26-26 verbatim
namespace Lorentz


-- @@ L28-30 verbatim
/-- The standard basis of complex contravariant Lorentz vectors. -/
def complexContrBasis : Basis (Fin 1 ⊕ Fin 3) ℂ ContrℂModule :=
  Basis.ofEquivFun ContrℂModule.toFin13ℂEquiv


-- @@ L32-36 verbatim
@[simp]
lemma complexContrBasis_toFin13ℂ (i :Fin 1 ⊕ Fin 3) :
    (complexContrBasis i).toFin13ℂ = Pi.single i 1 := by
  simp only [complexContrBasis, Basis.coe_ofEquivFun]
  rfl


-- @@ L38-45 verbatim
@[simp]
lemma complexContrBasis_ρ_apply (M : SL(2,ℂ)) (i j : Fin 1 ⊕ Fin 3) :
    (LinearMap.toMatrix complexContrBasis complexContrBasis) (ContrℂModule.SL2CRep M) i j =
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M)) i j := by
  rw [LinearMap.toMatrix_apply]
  simp only [complexContrBasis, Basis.coe_ofEquivFun, Basis.ofEquivFun_repr_apply]
  change (((LorentzGroup.toComplex (SL2C.toLorentzGroup M))) *ᵥ (Pi.single j 1)) i = _
  simp


-- @@ L47-50 verbatim
lemma complexContrBasis_ρ_val (M : SL(2,ℂ)) (v : ContrℂModule) :
    ((ContrℂModule.SL2CRep M) v).val =
    LorentzGroup.toComplex (SL2C.toLorentzGroup M) *ᵥ v.val := by
  rfl


-- @@ L52-54 verbatim
/-- The standard basis of complex contravariant Lorentz vectors indexed by `Fin 4`. -/
def complexContrBasisFin4 : Basis (Fin 4) ℂ ContrℂModule :=
  Basis.reindex complexContrBasis finSumFinEquiv


-- @@ L56-58 verbatim
lemma complexContrBasisFin4_eq_reindex :
    complexContrBasisFin4 = complexContrBasis.reindex finSumFinEquiv :=
  rfl


-- @@ L60-62 verbatim
lemma complexContrBasis_reindex_apply_eq_fin4 (j : Fin 4) :
    (complexContrBasis.reindex finSumFinEquiv) j = complexContrBasisFin4 j :=
  rfl


-- @@ L64-68 verbatim
@[simp]
lemma complexContrBasisFin4_apply_zero :
    complexContrBasisFin4 0 = complexContrBasis (Sum.inl 0) := by
  simp only [complexContrBasisFin4, Basis.reindex_apply]
  rfl


-- @@ L70-74 verbatim
@[simp]
lemma complexContrBasisFin4_apply_one :
    complexContrBasisFin4 1 = complexContrBasis (Sum.inr 0) := by
  simp only [complexContrBasisFin4, Basis.reindex_apply]
  rfl


-- @@ L76-80 verbatim
@[simp]
lemma complexContrBasisFin4_apply_two :
    complexContrBasisFin4 2 = complexContrBasis (Sum.inr 1) := by
  simp only [complexContrBasisFin4, Basis.reindex_apply]
  rfl


-- @@ L82-86 verbatim
@[simp]
lemma complexContrBasisFin4_apply_three :
    complexContrBasisFin4 3 = complexContrBasis (Sum.inr 2) := by
  simp only [complexContrBasisFin4, Basis.reindex_apply]
  rfl


-- @@ L88-93 verbatim
@[simp]
lemma complexContrBasisFin4_apply_succ (i : Fin 3) :
    complexContrBasisFin4 i.succ = complexContrBasis (Sum.inr i) := by
  simp only [complexContrBasisFin4, Basis.reindex_apply]
  congr 1
  fin_cases i <;> decide


-- @@ L95-97 verbatim
/-- The standard basis of complex covariant Lorentz vectors. -/
def complexCoBasis : Basis (Fin 1 ⊕ Fin 3) ℂ CoℂModule :=
  Basis.ofEquivFun CoℂModule.toFin13ℂEquiv


-- @@ L99-102 verbatim
@[simp]
lemma complexCoBasis_toFin13ℂ (i :Fin 1 ⊕ Fin 3) : (complexCoBasis i).toFin13ℂ = Pi.single i 1 := by
  simp only [complexCoBasis, Basis.coe_ofEquivFun]
  rfl


-- @@ L104-111 verbatim
@[simp]
lemma complexCoBasis_ρ_apply (M : SL(2,ℂ)) (i j : Fin 1 ⊕ Fin 3) :
    (LinearMap.toMatrix complexCoBasis complexCoBasis) (CoℂModule.SL2CRep M) i j =
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ᵀ i j := by
  rw [LinearMap.toMatrix_apply]
  simp only [complexCoBasis, Basis.coe_ofEquivFun, Basis.ofEquivFun_repr_apply, transpose_apply]
  change ((LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ᵀ *ᵥ (Pi.single j 1)) i = _
  simp


-- @@ L113-116 verbatim
lemma CoℂModule.SL2CRep_val (M : SL(2,ℂ)) (v : CoℂModule) :
    ((CoℂModule.SL2CRep M) v).val =
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ᵀ *ᵥ v.val := by
  rfl


-- @@ L118-120 verbatim
/-- The standard basis of complex covariant Lorentz vectors indexed by `Fin 4`. -/
def complexCoBasisFin4 : Basis (Fin 4) ℂ CoℂModule :=
  Basis.reindex complexCoBasis finSumFinEquiv


-- @@ L122-124 verbatim
lemma complexCoBasisFin4_eq_reindex :
    complexCoBasisFin4 = complexCoBasis.reindex finSumFinEquiv :=
  rfl


-- @@ L126-128 verbatim
lemma complexCoBasis_reindex_apply_eq_fin4 (j : Fin 4) :
    (complexCoBasis.reindex finSumFinEquiv) j = complexCoBasisFin4 j :=
  rfl


-- @@ L130-134 verbatim
@[simp]
lemma complexCoBasisFin4_apply_zero :
    complexCoBasisFin4 0 = complexCoBasis (Sum.inl 0) := by
  simp only [complexCoBasisFin4, Basis.reindex_apply]
  rfl


-- @@ L136-140 verbatim
@[simp]
lemma complexCoBasisFin4_apply_one :
    complexCoBasisFin4 1 = complexCoBasis (Sum.inr 0) := by
  simp only [complexCoBasisFin4, Basis.reindex_apply]
  rfl


-- @@ L142-146 verbatim
@[simp]
lemma complexCoBasisFin4_apply_two :
    complexCoBasisFin4 2 = complexCoBasis (Sum.inr 1) := by
  simp only [complexCoBasisFin4, Basis.reindex_apply]
  rfl


-- @@ L148-152 verbatim
@[simp]
lemma complexCoBasisFin4_apply_three :
    complexCoBasisFin4 3 = complexCoBasis (Sum.inr 2) := by
  simp only [complexCoBasisFin4, Basis.reindex_apply]
  rfl


-- @@ L154-158 verbatim
/-!

## Relation to real

-/


-- @@ L160-175 verbatim
/-- The semilinear map including real Lorentz vectors into complex contravariant
  lorentz vectors. -/
def inclCongrRealLorentz : ContrMod 3 →ₛₗ[Complex.ofRealHom] ContrℂModule where
  toFun v := {val := ofReal ∘ v.toFin1dℝ}
  map_add' x y := by
    apply Lorentz.ContrℂModule.ext
    rw [Lorentz.ContrℂModule.val_add]
    funext i
    simp only [Function.comp_apply, Pi.add_apply, map_add]
    simp only [ofReal_add]
  map_smul' c x := by
    apply Lorentz.ContrℂModule.ext
    rw [Lorentz.ContrℂModule.val_smul]
    funext i
    simp only [Function.comp_apply, ofRealHom_eq_coe, Pi.smul_apply, _root_.map_smul]
    simp only [smul_eq_mul, ofReal_mul]


-- @@ L177-178 verbatim
lemma inclCongrRealLorentz_val (v : ContrMod 3) :
    (inclCongrRealLorentz v).val = ofRealHom ∘ v.toFin1dℝ := rfl


-- @@ L180-193 verbatim
lemma complexContrBasis_of_real (i : Fin 1 ⊕ Fin 3) :
    (complexContrBasis i) = inclCongrRealLorentz (ContrMod.stdBasis i) := by
  apply Lorentz.ContrℂModule.ext
  simp only [complexContrBasis, Basis.coe_ofEquivFun, inclCongrRealLorentz,
    LinearMap.coe_mk, AddHom.coe_mk]
  ext j
  simp only [Function.comp_apply]
  change (Pi.single i 1) j = _
  by_cases h : i = j
  · subst h
    rw [ContrMod.toFin1dℝ, ContrMod.stdBasis_toFin1dℝEquiv_apply_same]
    simp
  · rw [ContrMod.toFin1dℝ, ContrMod.stdBasis_toFin1dℝEquiv_apply_ne h]
    simp [h]


-- @@ L195-201 verbatim
lemma inclCongrRealLorentz_ρ (M : SL(2, ℂ)) (v : ContrMod 3) :
    (ContrℂModule.SL2CRep M) (inclCongrRealLorentz v) =
    inclCongrRealLorentz (ContrMod.rep (SL2C.toLorentzGroup M) v) := by
  apply Lorentz.ContrℂModule.ext
  rw [complexContrBasis_ρ_val, inclCongrRealLorentz_val, inclCongrRealLorentz_val]
  rw [LorentzGroup.toComplex_mulVec_ofReal]
  rfl


-- @@ L203-212 verbatim
lemma SL2CRep_ρ_basis (M : SL(2, ℂ)) (i : Fin 1 ⊕ Fin 3) :
    (ContrℂModule.SL2CRep M) (complexContrBasis i) =
    ∑ j, (SL2C.toLorentzGroup M).1 j i •
    complexContrBasis j := by
  rw [complexContrBasis_of_real, inclCongrRealLorentz_ρ]
  rw [Contr.ρ_stdBasis, map_sum]
  apply congrArg
  funext j
  simp only [LinearMap.map_smulₛₗ, ofRealHom_eq_coe, coe_smul]
  rw [complexContrBasis_of_real]


-- @@ L214-227 verbatim
/-- The semilinear map including real Lorentz co-vectors into complex covariant
  Lorentz vectors. -/
def inclCoRealLorentz : CoMod 3 →ₛₗ[Complex.ofRealHom] CoℂModule where
  toFun v := { val := ofReal ∘ v.toFin1dℝ }
  map_add' x y := by
    ext i
    rw [CoℂModule.val_add]
    simp only [Function.comp_apply, Pi.add_apply, map_add]
    simp only [ofReal_add]
  map_smul' c x := by
    ext i
    rw [CoℂModule.val_smul]
    simp only [Function.comp_apply, ofRealHom_eq_coe, Pi.smul_apply, _root_.map_smul]
    simp only [smul_eq_mul, ofReal_mul]


-- @@ L229-230 verbatim
lemma inclCoRealLorentz_val (v : CoMod 3) :
    (inclCoRealLorentz v).val = ofRealHom ∘ v.toFin1dℝ := rfl


-- @@ L232-245 verbatim
lemma complexCoBasis_of_real (i : Fin 1 ⊕ Fin 3) :
    (complexCoBasis i) = inclCoRealLorentz (CoMod.stdBasis i) := by
  apply CoℂModule.ext
  simp only [complexCoBasis, Basis.coe_ofEquivFun, inclCoRealLorentz,
    LinearMap.coe_mk, AddHom.coe_mk]
  ext j
  simp only [Function.comp_apply]
  change (Pi.single i 1) j = _
  by_cases h : i = j
  · subst h
    rw [CoMod.toFin1dℝ, CoMod.stdBasis_toFin1dℝEquiv_apply_same]
    simp
  · rw [CoMod.toFin1dℝ, CoMod.stdBasis_toFin1dℝEquiv_apply_ne h]
    simp [h]


-- @@ L247-261 verbatim
lemma inclCoRealLorentz_ρ (M : SL(2, ℂ)) (v : CoMod 3) :
    (CoℂModule.SL2CRep M) (inclCoRealLorentz v) =
    inclCoRealLorentz (CoMod.rep (SL2C.toLorentzGroup M) v) := by
  ext i
  rw [CoℂModule.SL2CRep_val, inclCoRealLorentz_val, inclCoRealLorentz_val]
  change ((LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ᵀ *ᵥ
      (ofRealHom ∘ v.toFin1dℝ)) i =
    (ofRealHom ∘ ((LorentzGroup.transpose (SL2C.toLorentzGroup M)⁻¹).1 *ᵥ
      v.toFin1dℝ)) i
  rw [LorentzGroup.toComplex_inv]
  change (LorentzGroup.toComplex (LorentzGroup.transpose (SL2C.toLorentzGroup M)⁻¹) *ᵥ
      (ofRealHom ∘ v.toFin1dℝ)) i =
    (ofRealHom ∘ ((LorentzGroup.transpose (SL2C.toLorentzGroup M)⁻¹).1 *ᵥ
      v.toFin1dℝ)) i
  rw [LorentzGroup.toComplex_mulVec_ofReal]


-- @@ L263-263 verbatim
end Lorentz

-- @@ L264-264 verbatim
end
