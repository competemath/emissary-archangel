/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.CategoryO
import LieLean.Algebra.Lie.KacMoody.CategoryOSubmodule
import LieLean.Algebra.Lie.KacMoody.CharacterRing
import LieLean.Algebra.Lie.KacMoody.VermaPBW


-- @@ L11-37 verbatim
/-!
# Formal characters of modules in the category `𝒪`

Let `V` be a module over the Kac–Moody algebra `𝔤 = 𝔤(A)` lying in the category `𝒪`. Its formal
character ([Kac] §9.7) is the element `ch V = ∑_μ (dim V_μ) e^μ` of the algebra `ℰ`
(`Matrix.Realization.CharacterRing`).

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.IsCategoryO.character`: the formal character `ch V`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.IsCategoryO.quotient`: the category `𝒪` is stable under
  quotients (for submodules see `IsCategoryO.lieSubmodule`).
* `Matrix.Realization.KacMoodyAlgebra.IsCategoryO.character_eq_add`: `ch V = ch N + ch (V/N)`
  for a submodule `N` of `V`.
* `Matrix.Realization.KacMoodyAlgebra.IsCategoryO.character_congr`: isomorphic modules have the
  same character.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.finrank_weightSpace_sub_eq`:
  `dim M(Λ)_{Λ - β}` does not depend on `Λ`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.character_eq`: `ch M(Λ) = e^Λ ch M(0)`.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §9.1, §9.7.
-/


-- @@ L39-39 verbatim
open Module LieModule


-- @@ L41-41 verbatim
noncomputable section


-- @@ L43-43 verbatim
namespace Matrix.Realization.KacMoodyAlgebra


-- @@ L45-45 verbatim
attribute [local instance 100] LieRing.ofAssociativeRing


-- @@ L47-47 verbatim
open CharacterRing WeightOrd


-- @@ L49-50 verbatim
variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)


-- @@ L52-54 verbatim
variable {V W : Type*} [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V] [AddCommGroup W] [Module K W]
  [LieRingModule P.KacMoodyAlgebra W] [LieModule K P.KacMoodyAlgebra W]


-- @@ L56-56 verbatim
/-! ### Weight spaces of submodules, quotients and isomorphic modules -/


-- @@ L58-58 verbatim
section WeightSpace


-- @@ L60-60 verbatim
variable (N : LieSubmodule K P.KacMoodyAlgebra V)


-- @@ L62-71 verbatim
/-- The weight space `N_μ` of a submodule `N ⊆ V` is `N ∩ V_μ`. -/
lemma map_weightSpaceOfMap_lieSubmodule (μ : Dual K H) :
    (weightSpaceOfMap N (h P) μ).map N.toSubmodule.subtype =
      N.toSubmodule ⊓ weightSpaceOfMap V (h P) μ := by
  ext v
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n.2, fun a ↦ congrArg Subtype.val (hn a)⟩
  · rintro ⟨hvN, hv⟩
    exact ⟨⟨v, hvN⟩, fun a ↦ Subtype.ext (hv a), rfl⟩


-- @@ L73-77 verbatim
lemma finrank_weightSpaceOfMap_lieSubmodule (μ : Dual K H) :
    finrank K (weightSpaceOfMap N (h P) μ) =
      finrank K ↥(N.toSubmodule ⊓ weightSpaceOfMap V (h P) μ) := by
  rw [← map_weightSpaceOfMap_lieSubmodule, Submodule.finrank_map_subtype_eq]
  rfl


-- @@ L79-80 verbatim
/-- The quotient map `V → V/N`, as a linear map. -/
abbrev quotMk : V →ₗ[K] V ⧸ N := (LieSubmodule.Quotient.mk' N : V →ₗ⁅K,P.KacMoodyAlgebra⁆ V ⧸ N)


-- @@ L82-83 verbatim
lemma ker_quotMk : LinearMap.ker (quotMk P N) = N.toSubmodule :=
  Submodule.ker_mkQ _


-- @@ L85-86 verbatim
lemma range_quotMk : LinearMap.range (quotMk P N) = ⊤ :=
  LinearMap.range_eq_top.mpr (LieSubmodule.Quotient.surjective_mk' N)


-- @@ L88-97 verbatim
/-- If `V` is the sum of its weight spaces, the weight space `(V/N)_μ` is the image of `V_μ`. -/
lemma map_weightSpaceOfMap_quotient (hV : ⨆ μ, weightSpaceOfMap V (h P) μ = ⊤) (μ : Dual K H) :
    (weightSpaceOfMap V (h P) μ).map (quotMk P N) = weightSpaceOfMap (V ⧸ N) (h P) μ := by
  have hle : ∀ ν, (weightSpaceOfMap V (h P) ν).map (quotMk P N) ≤
      weightSpaceOfMap (V ⧸ N) (h P) ν := fun ν ↦ by
    rintro _ ⟨v, hv, rfl⟩
    exact map_mem_weightSpaceOfMap P (LieSubmodule.Quotient.mk' N) hv
  refine le_antisymm (hle μ) fun x hx ↦ mem_of_mem_iSup_of_le (h P) _ hle hx ?_
  rw [← Submodule.map_iSup, hV, Submodule.map_top, range_quotMk]
  trivial


-- @@ L99-110 verbatim
/-- `dim V_μ = dim N_μ + dim (V/N)_μ` for a submodule `N` of a module `V` which is the sum of its
weight spaces. -/
theorem finrank_weightSpaceOfMap_eq_add (hV : ⨆ μ, weightSpaceOfMap V (h P) μ = ⊤)
    (μ : Dual K H) [FiniteDimensional K (weightSpaceOfMap V (h P) μ)] :
    finrank K (weightSpaceOfMap V (h P) μ) =
      finrank K (weightSpaceOfMap N (h P) μ) + finrank K (weightSpaceOfMap (V ⧸ N) (h P) μ) := by
  have := LinearMap.finrank_range_add_finrank_ker
    (quotMk P N ∘ₗ (weightSpaceOfMap V (h P) μ).subtype)
  rw [LinearMap.range_comp, Submodule.range_subtype, map_weightSpaceOfMap_quotient P N hV,
    LinearMap.ker_comp, ker_quotMk, ← Submodule.finrank_map_subtype_eq,
    Submodule.map_comap_subtype] at this
  rw [← this, finrank_weightSpaceOfMap_lieSubmodule, inf_comm, add_comm]


-- @@ L112-118 verbatim
/-- A morphism of `𝔤`-modules which is a linear isomorphism maps `V_μ` onto `W_μ`. -/
lemma map_weightSpaceOfMap_equiv (e : V ≃ₗ⁅K,P.KacMoodyAlgebra⁆ W) (μ : Dual K H) :
    (weightSpaceOfMap V (h P) μ).map (e : V →ₗ[K] W) = weightSpaceOfMap W (h P) μ := by
  refine le_antisymm ?_ fun w hw ↦ ⟨e.symm w, ?_, e.apply_symm_apply w⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact map_mem_weightSpaceOfMap P (e : V →ₗ⁅K,P.KacMoodyAlgebra⁆ W) hv
  · exact map_mem_weightSpaceOfMap P (e.symm : W →ₗ⁅K,P.KacMoodyAlgebra⁆ V) hw


-- @@ L120-123 verbatim
lemma finrank_weightSpaceOfMap_equiv (e : V ≃ₗ⁅K,P.KacMoodyAlgebra⁆ W) (μ : Dual K H) :
    finrank K (weightSpaceOfMap V (h P) μ) = finrank K (weightSpaceOfMap W (h P) μ) := by
  rw [← map_weightSpaceOfMap_equiv P e,
    LinearEquiv.finrank_map_eq (e.toLinearEquiv : V ≃ₗ[K] W)]


-- @@ L125-125 verbatim
end WeightSpace


-- @@ L127-127 verbatim
/-! ### Stability of the category `𝒪` -/


-- @@ L129-129 verbatim
namespace IsCategoryO


-- @@ L131-131 verbatim
variable {P}


-- @@ L133-145 verbatim
/-- A quotient of a module in the category `𝒪` lies in `𝒪` ([Kac] §9.1). -/
theorem quotient (hV : IsCategoryO P V) (N : LieSubmodule K P.KacMoodyAlgebra V) :
    IsCategoryO P (V ⧸ N) := by
  have hmap := map_weightSpaceOfMap_quotient P N hV.iSup_weightSpaceOfMap_eq_top
  refine ⟨?_, fun μ ↦ ?_, ?_⟩
  · simp_rw [← hmap, ← Submodule.map_iSup, hV.iSup_weightSpaceOfMap_eq_top, Submodule.map_top,
      range_quotMk]
  · have := hV.finiteDimensional_weightSpaceOfMap μ
    rw [← hmap]
    infer_instance
  · obtain ⟨s, hs⟩ := hV.exists_finset
    refine ⟨s, fun μ hμ ↦ hs μ fun h0 ↦ hμ ?_⟩
    rw [← hmap, h0, Submodule.map_bot]


-- @@ L147-158 verbatim
/-- A module isomorphic to a module in the category `𝒪` lies in `𝒪`. -/
theorem of_equiv (hV : IsCategoryO P V) (e : V ≃ₗ⁅K,P.KacMoodyAlgebra⁆ W) : IsCategoryO P W := by
  have hmap := map_weightSpaceOfMap_equiv P e
  refine ⟨?_, fun μ ↦ ?_, ?_⟩
  · simp_rw [← hmap, ← Submodule.map_iSup, hV.iSup_weightSpaceOfMap_eq_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr e.surjective
  · have := hV.finiteDimensional_weightSpaceOfMap μ
    rw [← hmap]
    infer_instance
  · obtain ⟨s, hs⟩ := hV.exists_finset
    refine ⟨s, fun μ hμ ↦ hs μ fun h0 ↦ hμ ?_⟩
    rw [← hmap, h0, Submodule.map_bot]


-- @@ L160-160 verbatim
/-! ### The formal character -/


-- @@ L162-162 verbatim
variable [CharZero K]


-- @@ L164-170 verbatim
/-- The formal character `ch V = ∑_μ (dim V_μ) e^μ ∈ ℰ` of a module `V` in the category `𝒪`
([Kac] §9.7). -/
def character (hV : IsCategoryO P V) : P.CharacterRing ℤ :=
  ofFun P (fun μ ↦ (finrank K (weightSpaceOfMap V (h P) μ) : ℤ)) (by
    obtain ⟨s, hs⟩ := hV.exists_finset
    refine ⟨s, fun μ hμ ↦ hs μ fun h0 ↦ hμ ?_⟩
    rw [h0, finrank_bot, Nat.cast_zero])


-- @@ L172-173 verbatim
@[simp] lemma coeffAt_character (hV : IsCategoryO P V) (μ : Dual K H) :
    hV.character.coeffAt μ = finrank K (weightSpaceOfMap V (h P) μ) := rfl


-- @@ L175-183 verbatim
/-- **Additivity of characters**: `ch V = ch N + ch (V/N)` for a submodule `N` of a module `V` in
the category `𝒪` ([Kac] §9.7). -/
theorem character_eq_add (hV : IsCategoryO P V) (N : LieSubmodule K P.KacMoodyAlgebra V)
    (hN : IsCategoryO P N) (hQ : IsCategoryO P (V ⧸ N)) :
    hV.character = hN.character + hQ.character := by
  ext μ
  have := hV.finiteDimensional_weightSpaceOfMap μ
  simp only [coeffAt_character, HahnSeries.coeff_add, ← Nat.cast_add]
  rw [finrank_weightSpaceOfMap_eq_add P N hV.iSup_weightSpaceOfMap_eq_top]


-- @@ L185-189 verbatim
/-- Isomorphic modules in the category `𝒪` have the same character. -/
theorem character_congr (hV : IsCategoryO P V) (hW : IsCategoryO P W)
    (e : V ≃ₗ⁅K,P.KacMoodyAlgebra⁆ W) : hV.character = hW.character := by
  ext μ
  simp only [coeffAt_character, finrank_weightSpaceOfMap_equiv P e]


-- @@ L191-191 verbatim
end IsCategoryO


-- @@ L193-193 verbatim
/-! ### The character of a Verma module -/


-- @@ L195-195 verbatim
namespace VermaModule


-- @@ L197-197 verbatim
variable [CharZero K]


-- @@ L199-199 verbatim
local notation "mapN" => UniversalEnvelopingAlgebra.map (LieSubalgebra.incl (nNeg P))

-- @@ L200-200 verbatim
local notation "wt" => AuxLieAlgebra.wordWt P


-- @@ L202-204 verbatim
/-- The element `f_{j₁} ⋯ f_{jₖ}` of `U(𝔫₋)`. -/
def fWordNeg (w : List ι) : UniversalEnvelopingAlgebra K (nNeg P) :=
  (w.map fun i ↦ UniversalEnvelopingAlgebra.ι K (⟨f P i, f_mem_nNeg P i⟩ : nNeg P)).prod


-- @@ L206-210 verbatim
omit [CharZero K] in
lemma map_fWordNeg (w : List ι) : mapN (fWordNeg P w) = fWord P w := by
  simp only [fWordNeg, fWord, map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun i _ ↦ UniversalEnvelopingAlgebra.map_ι _ _


-- @@ L212-214 verbatim
lemma equivEnvNNeg_fWordNeg (Λ : Dual K H) (w : List ι) :
    equivEnvNNeg P Λ (fWordNeg P w) = fWord P w • hwv P Λ := by
  rw [equivEnvNNeg_apply, map_fWordNeg]


-- @@ L216-218 verbatim
/-- The linear isomorphism `M(Λ) ≃ M(Λ')`, `u v_Λ ↦ u v_Λ'` (`u ∈ U(𝔫₋)`). -/
def shiftEquiv (Λ Λ' : Dual K H) : VermaModule P Λ ≃ₗ[K] VermaModule P Λ' :=
  (equivEnvNNeg P Λ).symm.trans (equivEnvNNeg P Λ')


-- @@ L220-223 verbatim
lemma shiftEquiv_fWord (Λ Λ' : Dual K H) (w : List ι) :
    shiftEquiv P Λ Λ' (fWord P w • hwv P Λ) = fWord P w • hwv P Λ' := by
  rw [shiftEquiv, LinearEquiv.trans_apply, ← equivEnvNNeg_fWordNeg,
    LinearEquiv.symm_apply_apply, equivEnvNNeg_fWordNeg]


-- @@ L225-234 verbatim
/-- The isomorphism `M(Λ) ≃ M(Λ')` maps `M(Λ)_{Λ - β}` onto `M(Λ')_{Λ' - β}`. -/
lemma map_shiftEquiv_weightSpace (Λ Λ' β : Dual K H) :
    (weightSpace P Λ (Λ - β)).map (shiftEquiv P Λ Λ' : VermaModule P Λ →ₗ[K] VermaModule P Λ') =
      weightSpace P Λ' (Λ' - β) := by
  rw [weightSpace_eq_wordSpan, weightSpace_eq_wordSpan, wordSpan, wordSpan, Submodule.map_span,
    ← Set.image_comp]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, sub_right_inj, Function.comp_apply,
    LinearEquiv.coe_coe, shiftEquiv_fWord]


-- @@ L236-239 verbatim
/-- `dim M(Λ)_{Λ - β}` does not depend on `Λ` ([Kac] §9.7). -/
theorem finrank_weightSpace_sub_eq (Λ Λ' β : Dual K H) :
    finrank K (weightSpace P Λ (Λ - β)) = finrank K (weightSpace P Λ' (Λ' - β)) := by
  rw [← map_shiftEquiv_weightSpace P Λ Λ' β, LinearEquiv.finrank_map_eq]


-- @@ L241-248 verbatim
/-- The character of a Verma module: `ch M(Λ) = e^Λ ch M(0)` ([Kac] §9.7). -/
theorem character_eq (Λ : Dual K H) :
    (isCategoryO P Λ).character = exp P ℤ Λ * (isCategoryO P 0).character := by
  ext μ
  rw [coeff_exp_mul, IsCategoryO.coeffAt_character, IsCategoryO.coeffAt_character]
  have := finrank_weightSpace_sub_eq P Λ 0 (Λ - μ)
  rw [sub_sub_cancel, zero_sub, neg_sub] at this
  exact congrArg _ this


-- @@ L250-250 verbatim
end VermaModule


-- @@ L252-252 verbatim
end Matrix.Realization.KacMoodyAlgebra
