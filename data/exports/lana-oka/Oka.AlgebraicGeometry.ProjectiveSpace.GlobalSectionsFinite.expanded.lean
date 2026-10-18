/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.AlgebraicGeometry.ProjectiveSpace.SerreVanishing
import Oka.AlgebraicGeometry.ProjectiveSpace.TwistSections
import Oka.AlgebraicGeometry.ProjectiveSpace.AwayEval


-- @@ L10-31 verbatim
/-!
# Finiteness of global sections of twists of coherent sheaves on projective space

Let `R` be a noetherian ring and `F` a coherent sheaf on `ℙⁿ = ℙ(n; R)`. Then `Γ(ℙⁿ, F(m))` is a
finitely generated `R`-module for `m ≫ 0`. Here `R` acts on global sections through the
constants `ProjectiveSpace.globalRingHom : R →+* Γ(ℙⁿ, ⊤)`; the corresponding module structure
`ProjectiveSpace.sectionsModule` is not a global instance, and is supplied with `letI` in the
statement of the main theorem.

The proof follows Serre: Theorem A gives an epimorphism `⊕_I O(-m₁) ⟶ F` with coherent kernel
`K`, and Serre vanishing gives `H¹(K(m)) = 0` for `m ≫ 0`, so `Γ(⊕_I O(m - m₁)) → Γ(F(m))` is
surjective. The source is finite since `Γ(O(k))` is: it embeds `R`-linearly into the Laurent
coefficients, which are homogeneous polynomials of degree `k` for `n ≥ 1`.

## Main definitions and results

- `ProjectiveSpace.globalRingHom`, `ProjectiveSpace.sectionsModule`: the `R`-module structure on
  `Γ(M, ⊤)`, and `ProjectiveSpace.sectionsMap`: the induced `R`-linear maps.
- `ProjectiveSpace.finite_sections_twistingSheaf`: `Γ(O(k), ⊤)` is a finite `R`-module.
- `ProjectiveSpace.exists_module_finite_twist`: `Γ(F(m), ⊤)` is a finite `R`-module for
  `m ≫ 0`.
-/


-- @@ L33-33 verbatim
open CategoryTheory Limits MvPolynomial HomogeneousLocalization

-- @@ L34-34 verbatim
open AlgebraicGeometry.Scheme.Modules

-- @@ L35-35 verbatim
open scoped AlgebraicGeometry.ProjectiveSpace


-- @@ L37-37 verbatim
universe u


-- @@ L39-39 verbatim
namespace AlgebraicGeometry.ProjectiveSpace


-- @@ L41-41 verbatim
variable {n : ℕ} {R : Type u} [CommRing R]


-- @@ L43-43 verbatim
local notation "𝒜" => homogeneousSubmodule (Fin (n + 1)) R


-- @@ L45-49 verbatim
variable (n R) in
/-- The constants `R → Γ(ℙ(n; R), ⊤)`, pulled back along the structure morphism
`ℙ(n; R) ⟶ Spec R`. -/
noncomputable def globalRingHom : R →+* Γ(ℙ(n; R), ⊤) :=
  (toSpec n R).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom


-- @@ L51-53 verbatim
lemma globalRingHom_apply (r : R) :
    globalRingHom n R r = (toSpec n R).appTop ((Scheme.ΓSpecIso (.of R)).inv r) :=
  rfl


-- @@ L55-58 verbatim
/-- The `R`-module structure on the global sections `Γ(M, ⊤)` of a sheaf of modules on
`ℙ(n; R)`, through `globalRingHom`. -/
noncomputable abbrev sectionsModule (M : ℙ(n; R).Modules) : Module R Γ(M, ⊤) :=
  Module.compHom _ (globalRingHom n R)


-- @@ L60-60 verbatim
attribute [local instance] sectionsModule


-- @@ L62-64 verbatim
lemma sections_smul_def {M : ℙ(n; R).Modules} (r : R) (s : Γ(M, ⊤)) :
    r • s = globalRingHom n R r • s :=
  rfl


-- @@ L66-73 verbatim
/-- On the chart `Uᵢ ≅ Spec A_(Xᵢ)`, the constant `r` is the image of `C r`. -/
lemma toAway_restrict_globalRingHom (i : Fin (n + 1)) (r : R) :
    toAway {i} (Finset.singleton_nonempty i)
      (TopCat.Presheaf.restrictOpen (globalRingHom n R r) (UI n R {i}) le_top) =
      algebraMap (MvPolynomial (Fin (n + 1)) R) _ (C r) := by
  rw [globalRingHom_apply, restrict_toSpec_appTop (prod_X_mem_homogeneousSubmodule _)
    (card_pos_of_mem (Finset.mem_singleton_self i)), toAway_awayToSection]
  rfl


-- @@ L75-82 verbatim
/-- The Laurent coefficients of global sections of `O(k)` are `R`-linear. -/
lemma globalCoeff_smul (k : ℤ) (i : Fin (n + 1)) (r : R) (s : Γ(twistingSheaf n R k, ⊤)) :
    globalCoeff k i (r • s) = r • globalCoeff k i s := by
  change awayCoeff R {i} _ = r • awayCoeff R {i} _
  rw [sections_smul_def, mres_smul, sectionsUIEquiv_smul, toAway_restrict_globalRingHom,
    awayCoeff_apply, awayCoeff_apply, map_mul, awayToLaurent_algebraMap]
  rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, ← Algebra.smul_def,
    AddMonoidAlgebra.coeff_smul]


-- @@ L84-90 verbatim
variable (n R) in
/-- `globalCoeff` as an `R`-linear map. -/
noncomputable def globalCoeffLinear (k : ℤ) (i : Fin (n + 1)) :
    Γ(twistingSheaf n R k, ⊤) →ₗ[R] ((Fin (n + 1) →₀ ℤ) →₀ R) where
  toFun := globalCoeff k i
  map_add' := map_add _
  map_smul' := globalCoeff_smul k i


-- @@ L92-95 verbatim
@[simp]
lemma globalCoeffLinear_apply (k : ℤ) (i : Fin (n + 1)) (s : Γ(twistingSheaf n R k, ⊤)) :
    globalCoeffLinear n R k i s = globalCoeff k i s :=
  rfl


-- @@ L97-105 verbatim
variable (n R) in
/-- `polyCoeff` as an `R`-linear map. -/
noncomputable def polyCoeffLinear (d : ℕ) : 𝒜 d →ₗ[R] ((Fin (n + 1) →₀ ℤ) →₀ R) where
  toFun := polyCoeff R d
  map_add' := map_add _
  map_smul' r p := by
    rw [polyCoeff_apply, polyCoeff_apply, Submodule.coe_smul, _root_.map_smul,
      AddMonoidAlgebra.coeff_smul]
    rfl


-- @@ L107-115 verbatim
/-- A global section of `O(k)` is determined by its Laurent coefficients, so `Γ(O(k), ⊤)` is a
finite `R`-module as soon as these lie in a finite submodule. -/
lemma finite_of_globalCoeff_mem [IsNoetherianRing R] (k : ℤ)
    (p : Submodule R ((Fin (n + 1) →₀ ℤ) →₀ R)) [Module.Finite R p]
    (h : ∀ s : Γ(twistingSheaf n R k, ⊤), globalCoeff k 0 s ∈ p) :
    Module.Finite R Γ(twistingSheaf n R k, ⊤) :=
  haveI := isNoetherian_of_isNoetherianRing_of_finite R p
  Module.Finite.of_injective ((globalCoeffLinear n R k 0).codRestrict p h)
    fun _ _ hab ↦ globalCoeff_injective k 0 (congrArg Subtype.val hab)


-- @@ L117-147 verbatim
variable (n R) in
/-- **The global sections of `O(k)` on `ℙ(n; R)` form a finite `R`-module** (`R` noetherian). -/
theorem finite_sections_twistingSheaf [IsNoetherianRing R] (k : ℤ) :
    Module.Finite R Γ(twistingSheaf n R k, ⊤) := by
  obtain rfl | hn : n = 0 ∨ 1 ≤ n := by omega
  · let S : Set (Fin 1 →₀ ℤ) := {Finsupp.single 0 k}
    haveI : Module.Finite R (Finsupp.supported R R S) :=
      Module.Finite.equiv (Finsupp.supportedEquivFinsupp S).symm
    refine finite_of_globalCoeff_mem k (Finsupp.supported R R S) fun s ↦ ?_
    rw [Finsupp.mem_supported]
    intro a ha
    have h := (mem_laurentPart.mp (globalCoeff_mem_laurentPart_singleton k 0 s) a
      (Finsupp.mem_support_iff.mp ha)).2
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_one] at h
    refine Set.mem_singleton_iff.mpr (Finsupp.ext fun j ↦ ?_)
    rw [Fin.fin_one_eq_zero j, Finsupp.single_eq_same, h]
  obtain hk | ⟨d, rfl⟩ : k < 0 ∨ ∃ d : ℕ, k = d := by
    rcases lt_or_ge k 0 with hk | hk
    · exact Or.inl hk
    · exact Or.inr ⟨k.toNat, (Int.toNat_of_nonneg hk).symm⟩
  · refine finite_of_globalCoeff_mem k ⊥ fun s ↦ ?_
    rw [globalSections_eq_zero k hn hk s, map_zero]
    exact zero_mem _
  · haveI : Module.Finite R (𝒜 d) :=
      Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg _ _ d)
    refine finite_of_globalCoeff_mem (d : ℤ) (LinearMap.range (polyCoeffLinear n R d))
      fun s ↦ ?_
    obtain ⟨p, hp⟩ : globalCoeff (d : ℤ) 0 s ∈ (polyCoeff R d).range := by
      rw [← range_globalCoeff hn d]
      exact ⟨s, rfl⟩
    exact ⟨p, hp⟩


-- @@ L149-154 verbatim
/-- The map on global sections induced by a morphism of sheaves of modules on `ℙ(n; R)`, as an
`R`-linear map. -/
noncomputable def sectionsMap {M N : ℙ(n; R).Modules} (φ : M ⟶ N) : Γ(M, ⊤) →ₗ[R] Γ(N, ⊤) where
  toFun := φ.app ⊤
  map_add' := map_add _
  map_smul' r x := Hom.app_smul φ (globalRingHom n R r) x


-- @@ L156-158 verbatim
lemma sectionsMap_apply {M N : ℙ(n; R).Modules} (φ : M ⟶ N) (x : Γ(M, ⊤)) :
    sectionsMap φ x = φ.app ⊤ x :=
  rfl


-- @@ L160-162 verbatim
lemma sectionsMap_comp {M N K : ℙ(n; R).Modules} (φ : M ⟶ N) (ψ : N ⟶ K) (x : Γ(M, ⊤)) :
    sectionsMap (φ ≫ ψ) x = sectionsMap ψ (sectionsMap φ x) :=
  rfl


-- @@ L164-165 verbatim
lemma sectionsMap_id (M : ℙ(n; R).Modules) (x : Γ(M, ⊤)) : sectionsMap (𝟙 M) x = x :=
  rfl


-- @@ L167-169 verbatim
lemma sectionsMap_add {M N : ℙ(n; R).Modules} (φ ψ : M ⟶ N) (x : Γ(M, ⊤)) :
    sectionsMap (φ + ψ) x = sectionsMap φ x + sectionsMap ψ x :=
  rfl


-- @@ L171-173 verbatim
lemma sectionsMap_zero {M N : ℙ(n; R).Modules} (x : Γ(M, ⊤)) :
    sectionsMap (0 : M ⟶ N) x = 0 :=
  rfl


-- @@ L175-179 verbatim
/-- Finiteness of global sections transfers along isomorphisms. -/
lemma finite_sections_of_iso {M N : ℙ(n; R).Modules} (e : M ≅ N) [Module.Finite R Γ(M, ⊤)] :
    Module.Finite R Γ(N, ⊤) :=
  Module.Finite.of_surjective (sectionsMap e.hom) fun y ↦
    ⟨sectionsMap e.inv y, by rw [← sectionsMap_comp, e.inv_hom_id, sectionsMap_id]⟩


-- @@ L181-202 verbatim
/-- The global sections of a finite coproduct are finite if those of every summand are. -/
lemma finite_sections_sigma {I : Type u} [Finite I] (G : I → ℙ(n; R).Modules)
    [∀ i, Module.Finite R Γ(G i, ⊤)] : Module.Finite R Γ(∐ G, ⊤) := by
  have := Fintype.ofFinite I
  have := HasBiproduct.of_hasCoproduct G
  suffices Module.Finite R Γ(⨁ G, ⊤) from finite_sections_of_iso (biproduct.isoCoproduct G)
  let L : (∀ i, Γ(G i, ⊤)) →ₗ[R] Γ(⨁ G, ⊤) :=
    ∑ i, (sectionsMap (biproduct.ι G i)).comp (LinearMap.proj i)
  refine Module.Finite.of_surjective L fun x ↦ ⟨fun i ↦ sectionsMap (biproduct.π G i) x, ?_⟩
  have htot : ∑ i, biproduct.π G i ≫ biproduct.ι G i = 𝟙 (⨁ G) :=
    IsBilimit.total (biproduct.isBilimit G)
  have hsum : ∀ (s : Finset I) (φ : I → (⨁ G ⟶ ⨁ G)),
      sectionsMap (∑ i ∈ s, φ i) x = ∑ i ∈ s, sectionsMap (φ i) x := by
    classical
    intro s φ
    induction s using Finset.induction_on with
    | empty => simp [sectionsMap_zero]
    | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, sectionsMap_add, ih]
  simp only [L, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]
  simp_rw [← sectionsMap_comp]
  rw [← hsum, htot, sectionsMap_id]


-- @@ L204-229 verbatim
/-- **Global sections of twists of coherent sheaves on `ℙⁿ` are finite**: for `R` noetherian and
`F` coherent on `ℙ(n; R)`, the `R`-module `Γ(ℙⁿ, F(m))` (with `R` acting through
`globalRingHom`, see `sectionsModule`) is finitely generated for `m ≫ 0`. -/
theorem exists_module_finite_twist [IsNoetherianRing R] (F : ℙ(n; R).Modules) [F.IsCoherent] :
    ∃ m₀ : ℤ, ∀ m : ℤ, m₀ ≤ m →
      letI := sectionsModule (twist F m); Module.Finite R Γ(twist F m, ⊤) := by
  obtain ⟨m₁, hm₁⟩ := exists_epi_twist_free_isCoherent_kernel F
  obtain ⟨I, _, π, _, -, hK⟩ := hm₁ m₁ le_rfl
  obtain ⟨m₂, hm₂⟩ := exists_H_twist_eq_zero (kernel π)
  refine ⟨m₂, fun m hm ↦ ?_⟩
  let S : ShortComplex ℙ(n; R).Modules := ShortComplex.mk (kernel.ι π) π (kernel.condition π)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel π))
      inferInstance inferInstance
  have hS' := (hS.map_of_exact (twistFunctor n R m)).map_of_exact
    (Scheme.Modules.toAbFunctor ℙ(n; R))
  have hsurj : Function.Surjective (sectionsMap ((twistFunctor n R m).map π)) :=
    TopCat.Sheaf.surjective_of_H_one hS' (hm₂ m hm 0)
  haveI (k : ℤ) := finite_sections_twistingSheaf n R k
  haveI := finite_sections_sigma fun _ : I ↦ twistingSheaf n R (-(m₁ : ℤ) + m)
  let e := twistTwistIso (SheafOfModules.free I : ℙ(n; R).Modules) (-(m₁ : ℤ)) m ≪≫
    twistFreeIso I (-(m₁ : ℤ) + m)
  have : Module.Finite R
      Γ((twistFunctor n R m).obj (twist (SheafOfModules.free I) (-(m₁ : ℤ))), ⊤) :=
    finite_sections_of_iso e.symm
  exact Module.Finite.of_surjective _ hsurj


-- @@ L231-231 verbatim
end AlgebraicGeometry.ProjectiveSpace
