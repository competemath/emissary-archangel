/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.AlgebraicGeometry.ProjectiveSpace.Hyperplane


-- @@ L8-20 verbatim
/-!
# Automorphisms of projective space from linear substitutions

An `R`-algebra automorphism `ψ` of `R[X₀, …, Xₙ]` which maps every variable to a linear form
(`ProjectiveSpace.IsLinearSubst`) is graded, and induces (`Proj.map`) an automorphism
`ProjectiveSpace.linearSubstIso ψ` of `ℙ(n; R)` over `Spec R`, whose inverse is induced by `ψ`
itself: `(linearSubstIso ψ).inv = linearSubstMap ψ`. We compute:

- `ProjectiveSpace.linearSubstMap_preimage_U`: if `ψ Xₖ = Xⱼ`, then the preimage of `Uₖ` under
  `linearSubstMap ψ` is `Uⱼ`;
- `ProjectiveSpace.linearSubstMap_appLE_xDiv`: in that case the pullback of `Xₗ / Xₖ` is
  `ψ(Xₗ) / Xⱼ`.
-/


-- @@ L22-22 verbatim
open CategoryTheory MvPolynomial HomogeneousLocalization

-- @@ L23-23 verbatim
open scoped AlgebraicGeometry.ProjectiveSpace


-- @@ L25-25 verbatim
universe u


-- @@ L27-27 verbatim
namespace AlgebraicGeometry.ProjectiveSpace


-- @@ L29-29 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra


-- @@ L31-31 verbatim
variable {n : ℕ} {R : Type u} [CommRing R]


-- @@ L33-33 verbatim
local notation "𝒜" => homogeneousSubmodule (Fin (n + 1)) R


-- @@ L35-51 verbatim
/-- A **surjective graded ring homomorphism** satisfies the condition on irrelevant ideals needed
by `Proj.map`. -/
lemma _root_.HomogeneousIdeal.irrelevant_le_map_of_surjective {A B σ τ : Type*} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A] [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜' : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜'] [GradedRing ℬ] (f : 𝒜' →+*ᵍ ℬ)
    (hf : Function.Surjective f) :
    HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜').map f := by
  intro b hb
  obtain ⟨a, rfl⟩ := hf b
  have ha : a - (DirectSum.decompose 𝒜' a 0 : A) ∈ HomogeneousIdeal.irrelevant 𝒜' := by
    simp
  have := Ideal.mem_map_of_mem f ha
  rw [map_sub, GradedRingHom.map_directSumDecompose] at this
  have hb' : ((DirectSum.decompose ℬ (f a) 0 : ℬ 0) : B) = 0 := by
    rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply] at hb
    exact hb
  rwa [hb', sub_zero] at this


-- @@ L53-56 verbatim
/-- An `R`-algebra endomorphism of `R[X₀, …, Xₙ]` is a **linear substitution** if it maps every
variable to a linear form. -/
def IsLinearSubst (ψ : MvPolynomial (Fin (n + 1)) R →ₐ[R] MvPolynomial (Fin (n + 1)) R) : Prop :=
  ∀ i, ψ (X i) ∈ 𝒜 1


-- @@ L58-63 verbatim
lemma IsLinearSubst.map_mem {ψ : MvPolynomial (Fin (n + 1)) R →ₐ[R] MvPolynomial (Fin (n + 1)) R}
    (hψ : IsLinearSubst ψ) {d : ℕ} {p : MvPolynomial (Fin (n + 1)) R} (hp : p ∈ 𝒜 d) :
    ψ p ∈ 𝒜 d := by
  have h := (mem_homogeneousSubmodule d p).1 hp
  rw [MvPolynomial.aeval_unique ψ, mem_homogeneousSubmodule]
  simpa using h.aeval (⇑ψ ∘ X) fun i ↦ (mem_homogeneousSubmodule 1 _).1 (hψ i)


-- @@ L65-69 verbatim
/-- A linear substitution as a graded ring homomorphism. -/
def linearSubstGradedHom (ψ : MvPolynomial (Fin (n + 1)) R →ₐ[R] MvPolynomial (Fin (n + 1)) R)
    (hψ : IsLinearSubst ψ) : 𝒜 →+*ᵍ 𝒜 where
  __ := ψ.toRingHom
  map_mem := hψ.map_mem


-- @@ L71-75 verbatim
@[simp]
lemma linearSubstGradedHom_apply
    (ψ : MvPolynomial (Fin (n + 1)) R →ₐ[R] MvPolynomial (Fin (n + 1)) R) (hψ : IsLinearSubst ψ)
    (p : MvPolynomial (Fin (n + 1)) R) : linearSubstGradedHom ψ hψ p = ψ p :=
  rfl


-- @@ L77-81 verbatim
/-- `ψ.trans ψ.symm` is the identity, a linear substitution. -/
lemma linearSubstMap_congr_aux
    (ψ : MvPolynomial (Fin (n + 1)) R ≃ₐ[R] MvPolynomial (Fin (n + 1)) R) :
    IsLinearSubst (ψ.trans ψ.symm).toAlgHom := fun i ↦ by
  simpa using X_mem_homogeneousSubmodule_one (R := R) i


-- @@ L83-84 verbatim
variable (ψ : MvPolynomial (Fin (n + 1)) R ≃ₐ[R] MvPolynomial (Fin (n + 1)) R)
  (hψ : IsLinearSubst ψ.toAlgHom)


-- @@ L86-90 verbatim
/-- The morphism `ℙ(n; R) ⟶ ℙ(n; R)` induced by a linear substitution `ψ`: it pulls `Xᵢ` back to
`ψ Xᵢ`. -/
noncomputable def linearSubstMap : ℙ(n; R) ⟶ ℙ(n; R) :=
  Proj.map (linearSubstGradedHom ψ.toAlgHom hψ)
    (HomogeneousIdeal.irrelevant_le_map_of_surjective _ ψ.surjective)


-- @@ L92-96 verbatim
lemma linearSubstMap_comp (ψ' : MvPolynomial (Fin (n + 1)) R ≃ₐ[R] MvPolynomial (Fin (n + 1)) R)
    (hψ' : IsLinearSubst ψ'.toAlgHom) (hψψ' : IsLinearSubst (ψ.trans ψ').toAlgHom) :
    linearSubstMap ψ' hψ' ≫ linearSubstMap ψ hψ = linearSubstMap (ψ.trans ψ') hψψ' := by
  rw [linearSubstMap, linearSubstMap, ← Proj.map_comp]
  rfl


-- @@ L98-100 verbatim
lemma isLinearSubst_refl :
    IsLinearSubst (AlgEquiv.refl : MvPolynomial (Fin (n + 1)) R ≃ₐ[R] _).toAlgHom :=
  X_mem_homogeneousSubmodule_one


-- @@ L102-105 verbatim
lemma linearSubstMap_refl :
    linearSubstMap AlgEquiv.refl isLinearSubst_refl = 𝟙 ℙ(n; R) := by
  rw [linearSubstMap, ← Proj.map_id]
  rfl


-- @@ L107-112 verbatim
omit hψ in
lemma linearSubstMap_congr {ψ' : MvPolynomial (Fin (n + 1)) R ≃ₐ[R] MvPolynomial (Fin (n + 1)) R}
    (h : ψ = ψ') (hψ : IsLinearSubst ψ.toAlgHom) (hψ' : IsLinearSubst ψ'.toAlgHom) :
    linearSubstMap ψ hψ = linearSubstMap ψ' hψ' := by
  subst h
  rfl


-- @@ L114-114 verbatim
section Chart


-- @@ L116-116 verbatim
variable {k j : Fin (n + 1)} (h : ψ (X k) = X j)

-- @@ L117-117 verbatim
include h


-- @@ L119-122 verbatim
/-- If `ψ Xₖ = Xⱼ`, the preimage of `Uₖ` under `linearSubstMap ψ` is `Uⱼ`. -/
lemma linearSubstMap_preimage_U : linearSubstMap ψ hψ ⁻¹ᵁ U n R k = U n R j := by
  rw [linearSubstMap, U, Proj.map_preimage_basicOpen, U]
  congr 1


-- @@ L124-136 verbatim
/-- If `ψ Xₖ = Xⱼ`, the pullback of `Xₗ / Xₖ` along `linearSubstMap ψ` is `ψ(Xₗ) / Xⱼ`. -/
lemma linearSubstMap_appLE_xDiv (l : Fin (n + 1))
    (e : U n R j ≤ linearSubstMap ψ hψ ⁻¹ᵁ U n R k) :
    (linearSubstMap ψ hψ).appLE (U n R k) (U n R j) e (xDiv k l) =
      Proj.awayToSection 𝒜 (X j) (Away.mk 𝒜 (X_mem_homogeneousSubmodule_one j) 1 (ψ (X l))
        (by rw [smul_eq_mul, mul_one]; exact hψ l)) := by
  refine (Proj.appLE_awayToSection_of_eq (linearSubstGradedHom ψ.toAlgHom hψ) _
    (X_mem_homogeneousSubmodule_one k) (t := X j) h e (awayXDiv R k l)).trans ?_
  congr 1
  apply val_injective
  simp only [awayXDiv, Away.mk, HomogeneousLocalization.map_mk, val_mk]
  congr 1
  exact Subtype.ext (by simpa using h)


-- @@ L138-138 verbatim
end Chart


-- @@ L140-140 verbatim
variable (hψ' : IsLinearSubst ψ.symm.toAlgHom)


-- @@ L142-164 verbatim
include hψ' in
/-- The morphism induced by a linear substitution is a morphism over `Spec R`. -/
lemma linearSubstMap_toSpec : linearSubstMap ψ hψ ≫ toSpec n R = toSpec n R := by
  refine (affineOpenCover n R).openCover.hom_ext _ _ fun (j : Fin (n + 1)) ↦ ?_
  change chart j ≫ linearSubstMap ψ hψ ≫ toSpec n R = chart j ≫ toSpec n R
  rw [chart_toSpec, chart, Category.assoc, ← Category.assoc (Proj.awayι _ _ _ _),
    linearSubstMap, Proj.awayι_comp_map_of_eq _ _ Nat.one_pos (hψ' j)
      (X_mem_homogeneousSubmodule_one j) (by simp), Category.assoc, toSpec,
    ← Category.assoc (Proj.awayι _ _ _ _), Proj.awayι_toSpecZero, ← Spec.map_comp,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext r : 2
  change (awayXEquiv R j).symm (HomogeneousLocalization.map (linearSubstGradedHom ψ.toAlgHom hψ)
      (P := .powers (ψ.symm (X j))) (Q := .powers (X j)) (by
        rintro _ ⟨k, rfl⟩; exact ⟨k, by simp⟩)
    (fromZeroRingHom _ _ (algebraMap R _ r))) = C r
  have h : HomogeneousLocalization.map (linearSubstGradedHom ψ.toAlgHom hψ)
      (P := .powers (ψ.symm (X j))) (Q := .powers (X j)) (by
        rintro _ ⟨k, rfl⟩; exact ⟨k, by simp⟩)
      (fromZeroRingHom _ _ (algebraMap R _ r)) = awayXBase R j r := by
    apply val_injective
    simp [HomogeneousLocalization.map_mk, fromZeroRingHom, awayXBase, MvPolynomial.algebraMap_eq]
  rw [h, ← toAwayX_C, ← awayXEquiv_apply, RingEquiv.symm_apply_apply]


-- @@ L166-176 verbatim
/-- The automorphism of `ℙ(n; R)` induced by a linear substitution `ψ`; its inverse is
`linearSubstMap ψ`. -/
noncomputable def linearSubstIso : ℙ(n; R) ≅ ℙ(n; R) where
  hom := linearSubstMap ψ.symm hψ'
  inv := linearSubstMap ψ hψ
  hom_inv_id := by
    rw [linearSubstMap_comp ψ hψ ψ.symm hψ' (linearSubstMap_congr_aux ψ),
      linearSubstMap_congr _ ψ.self_trans_symm _ isLinearSubst_refl, linearSubstMap_refl]
  inv_hom_id := by
    rw [linearSubstMap_comp ψ.symm hψ' ψ hψ (linearSubstMap_congr_aux ψ.symm),
      linearSubstMap_congr _ ψ.symm_trans_self _ isLinearSubst_refl, linearSubstMap_refl]


-- @@ L178-178 verbatim
section Examples


-- @@ L180-184 verbatim
variable (R) in
/-- The substitution `Xₐ ↦ Xₐ + c X_b`, fixing the other variables. -/
noncomputable def shearAlgHom (a b : Fin (n + 1)) (c : R) :
    MvPolynomial (Fin (n + 1)) R →ₐ[R] MvPolynomial (Fin (n + 1)) R :=
  aeval fun i ↦ if i = a then X a + C c * X b else X i


-- @@ L186-188 verbatim
lemma shearAlgHom_X_self (a b : Fin (n + 1)) (c : R) :
    shearAlgHom R a b c (X a) = X a + C c * X b := by
  simp [shearAlgHom]


-- @@ L190-192 verbatim
lemma shearAlgHom_X_of_ne {a b i : Fin (n + 1)} (c : R) (hi : i ≠ a) :
    shearAlgHom R a b c (X i) = X i := by
  simp [shearAlgHom, hi]


-- @@ L194-202 verbatim
lemma shearAlgHom_comp {a b : Fin (n + 1)} (hab : b ≠ a) (c d : R) :
    (shearAlgHom R a b c).comp (shearAlgHom R a b d) = shearAlgHom R a b (c + d) := by
  refine MvPolynomial.algHom_ext fun i ↦ ?_
  by_cases hi : i = a
  · subst hi
    simp only [AlgHom.comp_apply, shearAlgHom_X_self, map_add, map_mul, shearAlgHom_X_of_ne c hab]
    rw [show (shearAlgHom R i b c) (C d) = C d from (shearAlgHom R i b c).commutes d]
    ring
  · simp [shearAlgHom_X_of_ne _ hi]


-- @@ L204-209 verbatim
lemma shearAlgHom_zero (a b : Fin (n + 1)) : shearAlgHom R a b 0 = AlgHom.id R _ := by
  refine MvPolynomial.algHom_ext fun i ↦ ?_
  by_cases hi : i = a
  · subst hi
    simp [shearAlgHom_X_self]
  · simp [shearAlgHom_X_of_ne _ hi]


-- @@ L211-217 verbatim
variable (R) in
/-- The **shear** `Xₐ ↦ Xₐ + c X_b` (`b ≠ a`), an automorphism of `R[X₀, …, Xₙ]`. -/
noncomputable def shearEquiv {a b : Fin (n + 1)} (hab : b ≠ a) (c : R) :
    MvPolynomial (Fin (n + 1)) R ≃ₐ[R] MvPolynomial (Fin (n + 1)) R :=
  AlgEquiv.ofAlgHom (shearAlgHom R a b c) (shearAlgHom R a b (-c))
    (by rw [shearAlgHom_comp hab, add_neg_cancel, shearAlgHom_zero])
    (by rw [shearAlgHom_comp hab, neg_add_cancel, shearAlgHom_zero])


-- @@ L219-222 verbatim
lemma shearEquiv_apply {a b : Fin (n + 1)} (hab : b ≠ a) (c : R)
    (p : MvPolynomial (Fin (n + 1)) R) :
    shearEquiv R hab c p = shearAlgHom R a b c p :=
  rfl


-- @@ L224-227 verbatim
lemma shearEquiv_symm_apply {a b : Fin (n + 1)} (hab : b ≠ a) (c : R)
    (p : MvPolynomial (Fin (n + 1)) R) :
    (shearEquiv R hab c).symm p = shearAlgHom R a b (-c) p :=
  rfl


-- @@ L229-239 verbatim
lemma isLinearSubst_shearAlgHom (a b : Fin (n + 1)) (c : R) :
    IsLinearSubst (shearAlgHom R a b c) := fun i ↦ by
  by_cases hi : i = a
  · subst hi
    rw [shearAlgHom_X_self]
    exact add_mem (X_mem_homogeneousSubmodule_one i) (by
      simpa using (SetLike.GradedMul.mul_mem (A := 𝒜) (i := 0) (j := 1)
        ((mem_homogeneousSubmodule 0 _).2 (isHomogeneous_C _ c))
        (X_mem_homogeneousSubmodule_one b)))
  · rw [shearAlgHom_X_of_ne c hi]
    exact X_mem_homogeneousSubmodule_one i


-- @@ L241-243 verbatim
lemma isLinearSubst_renameEquiv (σ : Equiv.Perm (Fin (n + 1))) :
    IsLinearSubst (renameEquiv R σ).toAlgHom := fun i ↦ by
  simpa using X_mem_homogeneousSubmodule_one (R := R) (σ i)


-- @@ L245-245 verbatim
end Examples


-- @@ L247-247 verbatim
end AlgebraicGeometry.ProjectiveSpace
