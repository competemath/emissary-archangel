/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.Character


-- @@ L8-42 verbatim
/-!
# The character of a Verma module and Kostant's partition function

Let `𝔤 = 𝔤(A)` be the Kac–Moody algebra of a realization `P` over a field `K` of characteristic
zero. We choose a basis of `𝔫₋` consisting of root vectors: `𝔫₋ = ⊕_{α ∈ Q₊ \ 0} 𝔤_{-α}`, and we
take a basis of each (finite-dimensional) root space `𝔤_{-α}`, indexed by `Fin (dim 𝔤_{-α})`.
By the Poincaré–Birkhoff–Witt theorem the ordered monomials in this basis form a basis of `U(𝔫₋)`;
transported to the Verma module `M(Λ)` via `U(𝔫₋) ≃ M(Λ)`, `u ↦ u v_Λ`, they form a basis of
`M(Λ)` consisting of weight vectors. Counting the basis vectors of weight `Λ - β` gives
([Kac] (9.7.2), (10.5.2))
`dim M(Λ)_{Λ - β} = K(β)`,
where `K(β)` is Kostant's partition function: the number of ways to write `β` as a sum of positive
roots, where each root `α` comes in `dim 𝔤_{-α}` "colours". (By the Chevalley involution,
`dim 𝔤_{-α} = dim 𝔤_α = mult α`.) Equivalently, `ch M(Λ) = e^Λ ∏_{α > 0} (1 - e^{-α})^{-mult α}`.

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.NegRootIndex`: the index set
  `{(α, j) | α ∈ Q₊ \ 0, j < dim 𝔤_{-α}}` of a basis of `𝔫₋` consisting of root vectors.
* `Matrix.Realization.KacMoodyAlgebra.nNegBasis`: such a basis of `𝔫₋`.
* `Matrix.Realization.KacMoodyAlgebra.kostantPartition`: Kostant's partition function `K(β)`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.pbwBasisVerma`: the PBW basis of `M(Λ)`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.isInternal_nNegRootSpace`: `𝔫₋ = ⊕_{α > 0} 𝔤_{-α}`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.finrank_weightSpace_sub`:
  `dim M(Λ)_{Λ - β} = K(β)`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.coeffAt_character`: the coefficient of
  `e^{Λ - β}` in `ch M(Λ)` is `K(β)` ([Kac] (9.7.2), (10.5.2)).

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §9.7, §10.5.
-/


-- @@ L44-44 verbatim
open Module LieModule UniversalEnvelopingAlgebra


-- @@ L46-46 verbatim
noncomputable section


-- @@ L48-48 verbatim
namespace Matrix.Realization.KacMoodyAlgebra


-- @@ L50-50 verbatim
attribute [local instance 100] LieRing.ofAssociativeRing


-- @@ L52-53 verbatim
variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)


-- @@ L55-55 verbatim
local notation "ιᵤ" => UniversalEnvelopingAlgebra.ι K

-- @@ L56-56 verbatim
/-! ### A basis of `𝔫₋` consisting of root vectors -/


-- @@ L58-59 verbatim
/-- The inclusion `𝔫₋ → 𝔤`, as a linear map. -/
abbrev nNegIncl : nNeg P →ₗ[K] P.KacMoodyAlgebra := (nNeg P).incl


-- @@ L61-64 verbatim
omit [CharZero K] in
lemma range_nNegIncl : LinearMap.range (nNegIncl P) = (nNeg P).toSubmodule := by
  ext x
  exact ⟨fun ⟨y, hy⟩ ↦ hy ▸ y.2, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩


-- @@ L66-67 verbatim
omit [CharZero K] in
lemma nNegIncl_injective : Function.Injective (nNegIncl P) := Subtype.val_injective


-- @@ L69-72 verbatim
omit [DecidableEq ι] [CharZero K] in
lemma neg_mem_negWeights {α : Dual K H} (hα : α ∈ P.posWeights) : -α ∈ P.negWeights := by
  obtain ⟨k, hk, rfl⟩ := hα
  exact ⟨k, hk, rfl⟩


-- @@ L74-77 verbatim
lemma rootSpace_neg_le_nNeg {α : Dual K H} (hα : α ∈ P.posWeights) :
    rootSpace P (-α) ≤ (nNeg P).toSubmodule := by
  rw [nNeg_toSubmodule_eq]
  exact le_iSup₂ (f := fun μ (_ : μ ∈ P.negWeights) ↦ rootSpace P μ) _ (neg_mem_negWeights P hα)


-- @@ L79-81 verbatim
/-- The root space `𝔤_{-α}`, `α ∈ Q₊ \ 0`, as a subspace of `𝔫₋`. -/
def nNegRootSpace (α : P.posWeights) : Submodule K (nNeg P) :=
  (rootSpace P (-(α : Dual K H))).comap (nNegIncl P)


-- @@ L83-86 verbatim
lemma map_nNegRootSpace (α : P.posWeights) :
    (nNegRootSpace P α).map (nNegIncl P) = rootSpace P (-(α : Dual K H)) := by
  rw [nNegRootSpace, Submodule.map_comap_eq, range_nNegIncl]
  exact inf_eq_right.mpr (rootSpace_neg_le_nNeg P α.2)


-- @@ L88-101 verbatim
omit [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H] [Module K H] in
/-- A family of submodules whose images under an injective linear map are independent is
independent. -/
lemma _root_.iSupIndep.of_map {R M N κ : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {g : M →ₗ[R] N} (hg : Function.Injective g)
    {p : κ → Submodule R M} (hp : iSupIndep fun i ↦ (p i).map g) : iSupIndep p := by
  intro i
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have hx'' : g x ∈ ⨆ (j) (_ : j ≠ i), (p j).map g := by
    simp only [← Submodule.map_iSup]
    exact Submodule.mem_map_of_mem hx'
  have := Submodule.disjoint_def.mp (hp i) (g x) (Submodule.mem_map_of_mem hx) hx''
  exact hg (this.trans (map_zero g).symm)


-- @@ L103-119 verbatim
open Classical in
/-- The root space decomposition `𝔫₋ = ⊕_{α ∈ Q₊ \ 0} 𝔤_{-α}` ([Kac] §1.3). -/
theorem isInternal_nNegRootSpace : DirectSum.IsInternal (nNegRootSpace P) := by
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
  · refine iSupIndep.of_map (nNegIncl_injective P) ?_
    simp_rw [map_nNegRootSpace]
    exact (iSupIndep_weightSpaceOfMap (M := P.KacMoodyAlgebra) (h P)).comp
      (f := fun α : P.posWeights ↦ -(α : Dual K H)) fun α β hαβ ↦
        Subtype.ext (neg_injective hαβ)
  · apply Submodule.map_injective_of_injective (nNegIncl_injective P)
    rw [Submodule.map_iSup, Submodule.map_top, range_nNegIncl, nNeg_toSubmodule_eq]
    simp_rw [map_nNegRootSpace]
    refine le_antisymm (iSup_le fun α ↦ ?_) (iSup₂_le fun μ hμ ↦ ?_)
    · exact le_iSup₂ (f := fun μ (_ : μ ∈ P.negWeights) ↦ rootSpace P μ) _
        (neg_mem_negWeights P α.2)
    · obtain ⟨k, hk, rfl⟩ := hμ
      exact le_iSup (fun α : P.posWeights ↦ rootSpace P (-(α : Dual K H))) ⟨_, k, hk, rfl⟩


-- @@ L121-124 verbatim
lemma finrank_nNegRootSpace (α : P.posWeights) :
    finrank K (nNegRootSpace P α) = finrank K (rootSpace P (-(α : Dual K H))) := by
  rw [← map_nNegRootSpace, LinearEquiv.finrank_eq
    (Submodule.equivMapOfInjective _ (nNegIncl_injective P) (nNegRootSpace P α))]


-- @@ L126-130 verbatim
instance (α : P.posWeights) : FiniteDimensional K (nNegRootSpace P α) := by
  have := finiteDimensional_rootSpace_neg P α.2
  rw [← map_nNegRootSpace] at this
  exact LinearEquiv.finiteDimensional
    (Submodule.equivMapOfInjective _ (nNegIncl_injective P) (nNegRootSpace P α)).symm


-- @@ L132-135 verbatim
/-- The index set `{(α, j) | α ∈ Q₊ \ 0, j < dim 𝔤_{-α}}` of a basis of `𝔫₋` consisting of root
vectors. -/
def NegRootIndex : Type _ :=
  Σ α : P.posWeights, Fin (finrank K (rootSpace P (-(α : Dual K H))))


-- @@ L137-138 verbatim
/-- An (arbitrary) linear order on `NegRootIndex`, used to form PBW monomials. -/
instance : LinearOrder (NegRootIndex P) := IsWellOrder.linearOrder WellOrderingRel


-- @@ L140-141 verbatim
/-- The positive root `α` attached to an index `(α, j)`. -/
def NegRootIndex.root {P : Realization A K H} (x : NegRootIndex P) : Dual K H := x.1


-- @@ L143-148 verbatim
open Classical in
/-- A basis of `𝔫₋` consisting of root vectors: the basis vector of index `(α, j)` lies in
`𝔤_{-α}`. -/
def nNegBasis : Basis (NegRootIndex P) K (nNeg P) :=
  (isInternal_nNegRootSpace P).collectedBasis fun α ↦
    Module.finBasisOfFinrankEq K _ (finrank_nNegRootSpace P α)


-- @@ L150-154 verbatim
open Classical in
lemma nNegBasis_mem (x : NegRootIndex P) :
    ((nNegBasis P x : nNeg P) : P.KacMoodyAlgebra) ∈ rootSpace P (-x.root) :=
  (isInternal_nNegRootSpace P).collectedBasis_mem
    (fun α ↦ Module.finBasisOfFinrankEq K _ (finrank_nNegRootSpace P α)) x


-- @@ L156-157 verbatim
/-- The weight `∑ s(α, j) α ∈ Q₊` of a multiset `s` of indices. -/
def negRootWt (s : NegRootIndex P →₀ ℕ) : Dual K H := s.sum fun x n ↦ n • x.root


-- @@ L159-163 verbatim
/-- **Kostant's partition function** `K(β)`: the number of ways of writing `β` as a sum of
positive roots, where each positive root `α` comes in `dim 𝔤_{-α}` colours ([Kac] (10.5.1);
`dim 𝔤_{-α} = dim 𝔤_α` is the multiplicity of `α`). -/
def kostantPartition (β : Dual K H) : ℕ :=
  Nat.card {s : NegRootIndex P →₀ ℕ // negRootWt P s = β}


-- @@ L165-165 verbatim
/-! ### The PBW basis of a Verma module -/


-- @@ L167-167 verbatim
namespace VermaModule


-- @@ L169-169 verbatim
variable (Λ : Dual K H)


-- @@ L171-180 verbatim
lemma listProd_smul_mem_weightSpace (l : List (NegRootIndex P)) {μ : Dual K H}
    {m : VermaModule P Λ} (hm : m ∈ weightSpace P Λ μ) :
    (l.map fun x ↦ ιᵤ ((nNegBasis P x : nNeg P) : P.KacMoodyAlgebra)).prod • m ∈
      weightSpace P Λ (μ - (l.map NegRootIndex.root).sum) := by
  induction l with
  | nil => simpa using hm
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, mul_smul, ← lie_eq_smul]
    convert lie_mem_weightSpaceOfMap (h P) (nNegBasis_mem P a) ih using 2
    abel


-- @@ L182-187 verbatim
omit [CharZero K] in
lemma sum_sort_toMultiset (s : NegRootIndex P →₀ ℕ) :
    (((Finsupp.toMultiset s).sort (· ≤ ·)).map NegRootIndex.root).sum = negRootWt P s := by
  rw [← Multiset.sum_coe, ← Multiset.map_coe, Multiset.sort_eq, Finsupp.toMultiset_map,
    Finsupp.sum_toMultiset, negRootWt, Finsupp.sum_mapDomain_index (h := fun a n ↦ n • a)
      (fun _ ↦ zero_nsmul _) (fun _ _ _ ↦ add_nsmul _ _ _)]


-- @@ L189-192 verbatim
/-- The PBW basis of `M(Λ)`: the vectors `x_{i₁} ⋯ x_{iₖ} v_Λ` for `i₁ ≤ ⋯ ≤ iₖ`, where
`(x_i)` is the basis `nNegBasis` of `𝔫₋`. -/
def pbwBasisVerma : Basis (NegRootIndex P →₀ ℕ) K (VermaModule P Λ) :=
  (pbwBasis (nNegBasis P)).map (equivEnvNNeg P Λ)


-- @@ L194-198 verbatim
lemma pbwBasisVerma_mem_weightSpace (s : NegRootIndex P →₀ ℕ) :
    pbwBasisVerma P Λ s ∈ weightSpace P Λ (Λ - negRootWt P s) := by
  rw [pbwBasisVerma, Basis.map_apply, pbwBasis_apply, equivEnvNNeg_apply, map_pbwMonomial,
    pbwMonomial, ← sum_sort_toMultiset]
  exact listProd_smul_mem_weightSpace P Λ _ (hwv_mem_weightSpace P Λ)


-- @@ L200-216 verbatim
/-- The weight space `M(Λ)_μ` is spanned by the PBW basis vectors of weight `μ`. -/
theorem weightSpace_eq_span (μ : Dual K H) :
    weightSpace P Λ μ =
      Submodule.span K (pbwBasisVerma P Λ '' {s | Λ - negRootWt P s = μ}) := by
  have hle : ∀ ν, Submodule.span K (pbwBasisVerma P Λ '' {s | Λ - negRootWt P s = ν}) ≤
      weightSpace P Λ ν := fun ν ↦ by
    rw [Submodule.span_le]
    rintro _ ⟨s, rfl, rfl⟩
    exact pbwBasisVerma_mem_weightSpace P Λ s
  refine le_antisymm (fun m hm ↦ mem_of_mem_iSup_of_le (h P) _ hle hm ?_) (hle μ)
  have htop : Submodule.span K (Set.range (pbwBasisVerma P Λ)) ≤
      ⨆ ν, Submodule.span K (pbwBasisVerma P Λ '' {s | Λ - negRootWt P s = ν}) := by
    rw [Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    exact Submodule.mem_iSup_of_mem (Λ - negRootWt P s)
      (Submodule.subset_span ⟨s, rfl, rfl⟩)
  exact htop (by rw [(pbwBasisVerma P Λ).span_eq]; trivial)


-- @@ L218-226 verbatim
/-- The dimension of `M(Λ)_μ` is the number of PBW basis vectors of weight `μ`. -/
theorem finrank_weightSpace (μ : Dual K H) :
    finrank K (weightSpace P Λ μ) = Nat.card {s | Λ - negRootWt P s = μ} := by
  set B := pbwBasisVerma P Λ
  have hli : LinearIndepOn K id (B '' {s | Λ - negRootWt P s = μ}) :=
    ((linearIndepOn_id_range_iff B.injective).mpr B.linearIndependent).mono
      (Set.image_subset_range _ _)
  rw [weightSpace_eq_span, finrank, rank_span_set hli, ← Nat.card.eq_1,
    Nat.card_image_of_injective B.injective]


-- @@ L228-233 verbatim
/-- **The character of a Verma module** ([Kac] (9.7.2), (10.5.2)): `dim M(Λ)_{Λ - β} = K(β)`,
Kostant's partition function. -/
theorem finrank_weightSpace_sub (β : Dual K H) :
    finrank K (weightSpace P Λ (Λ - β)) = kostantPartition P β := by
  rw [finrank_weightSpace, kostantPartition]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun s ↦ sub_right_inj)


-- @@ L235-240 verbatim
/-- **The character of a Verma module** ([Kac] (9.7.2), (10.5.2)): the coefficient of `e^{Λ - β}`
in `ch M(Λ)` is Kostant's partition function `K(β)`; that is,
`ch M(Λ) = e^Λ ∑_β K(β) e^{-β} = e^Λ ∏_{α > 0} (1 - e^{-α})^{-mult α}`. -/
theorem coeffAt_character (β : Dual K H) :
    (isCategoryO P Λ).character.coeffAt (Λ - β) = kostantPartition P β := by
  rw [IsCategoryO.coeffAt_character, ← finrank_weightSpace_sub P Λ β]


-- @@ L242-242 verbatim
end VermaModule


-- @@ L244-244 verbatim
end Matrix.Realization.KacMoodyAlgebra
