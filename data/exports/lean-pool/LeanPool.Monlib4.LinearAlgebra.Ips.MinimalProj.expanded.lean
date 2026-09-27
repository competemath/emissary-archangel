/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import LeanPool.Monlib4.LinearAlgebra.Ips.Pos
public import LeanPool.Monlib4.LinearAlgebra.LmulRmul
import LeanPool.Monlib4.LinearAlgebra.Ips.Basic
import LeanPool.Monlib4.LinearAlgebra.Ips.Ips


-- @@ L13-52 verbatim
/-!

# Minimal projections

In this file we show some necessary results for positive operators on a Hilbert space.

## main results

**Theorem.** If $p,q$ are (orthogonal) projections on $E$,
  then the following are equivalent:
   - (i) $pq = p = qp$
   - (ii) $p(E) \subseteq q(E)$
   - (iii) $q - p$ is an (orthogonal) projection
   - (iv) $q - p$ is positive

for part (iii), it suffices to show that the element is an idempotent since
  $q - p$ is self-adjoint

it turns out that $qp = p$ (from (i)) if and only if (ii) and
  (i) if and only if (iii) for idempotent operators on a module over a ring
  (see `IsIdempotentElem.comp_idempotent_iff` and
   `linear_map.commutes_iff_isIdempotent_elem`)

obviously when $p,q$ are self-adjoint operators, then $pq = p$ iff $qp=p$
  (see `self_adjoint_commutes_iff`)

so then, obviously, (ii) if and only if (iii) for idempotent self-adjoint operators as well
  (see `continuous_linear_map.image_subset_iff_sub_of_is_idempotent`)

we finally have (i) if and only if (iv) for idempotent self-adjoint operators on a
  finite-dimensional complex-Hilbert space:
  (see `orthogonal_projection_is_positive_iff_commutes`)

## main definition

* an operator is non-negative means that it is positive:
  $0 \leq p$ if and only if $p$ is positive
  (see `is_positive.is_nonneg`)

-/


-- @@ L54-54 verbatim
@[expose] public section


-- @@ L56-56 verbatim
open Module.End


-- @@ L58-58 verbatim
section


-- @@ L60-60 verbatim
variable {R E : Type _} [Ring R] [AddCommGroup E] [Module R E]


-- @@ L62-62 verbatim
open Submodule LinearMap


-- @@ L64-71 verbatim
/-- given an idempotent linear operator $p$, we have
  $x \in \textnormal{range}(p)$ if and only if $p(x) = x$ (for all $x \in E$) -/
theorem IsIdempotentElem.mem_range_iff {p : E →ₗ[R] E} (hp : IsIdempotentElem p) {x : E} :
    x ∈ range p ↔ p x = x := by
  simp_rw [mem_range]
  refine ⟨fun ⟨y, hy⟩ => ?_, fun h => ⟨x, h⟩⟩
  nth_rw 1 [← hy]
  rw [← mul_apply, hp.eq, hy]


-- @@ L73-73 verbatim
variable {U V : Submodule R E} {q : E →ₗ[R] E} (hq : IsIdempotentElem q)


-- @@ L75-82 verbatim
include hq in
/-- given idempotent linear operators $p,q$,
  we have $qp = p$ iff $p(E) \subseteq q(E)$ -/
theorem IsIdempotentElem.comp_idempotent_iff
  {E₂ : Type*} [AddCommGroup E₂] [Module R E₂] (p : E₂ →ₗ[R] E) :
    q.comp p = p ↔ LinearMap.range p ≤ LinearMap.range q := by
  simp_rw [LinearMap.ext_iff, comp_apply, ← IsIdempotentElem.mem_range_iff hq,
    SetLike.le_def, mem_range, forall_exists_index, forall_apply_eq_imp_iff]

-- @@ L83-87 verbatim
include hq in
theorem IsIdempotentElem.comp_idempotent_iff'
  {E₂ : Type*} [AddCommGroup E₂] [Module R E₂] (p : E₂ →ₗ[R] E) :
    q.comp p = p ↔ Submodule.map p ⊤ ≤ Submodule.map q ⊤ :=
by simp_rw [IsIdempotentElem.comp_idempotent_iff hq, Submodule.map_top]


-- @@ L89-89 verbatim
variable {p : E →ₗ[R] E} (hp : IsIdempotentElem p)


-- @@ L91-97 verbatim
include hp hq in
/-- if $p,q$ are idempotent operators and $pq = p = qp$,
  then $q - p$ is an idempotent operator -/
theorem LinearMap.isIdempotentElem_sub_of (h : p.comp q = p ∧ q.comp p = p) :
    IsIdempotentElem (q - p) := by
  simp_rw [IsIdempotentElem, mul_eq_comp, sub_comp, comp_sub, h.1, h.2, ← mul_eq_comp, hp.eq, hq.eq,
    sub_self, sub_zero]


-- @@ L99-119 verbatim
/-- if $p,q$ are idempotent operators and $q - p$ is also an idempotent
  operator, then $pq = p = qp$ -/
theorem LinearMap.commutes_of_isIdempotentElem {E 𝕜 : Type _} [RCLike 𝕜] [AddCommGroup E]
    [Module 𝕜 E] {p q : E →ₗ[𝕜] E} (hp : IsIdempotentElem p) (hq : IsIdempotentElem q)
    (h : IsIdempotentElem (q - p)) : p.comp q = p ∧ q.comp p = p := by
  simp_rw [IsIdempotentElem, mul_eq_comp, comp_sub, sub_comp, ← mul_eq_comp, hp.eq, hq.eq, ←
    sub_add_eq_sub_sub, sub_right_inj, add_sub] at h
  have h' : (2 : 𝕜) • p = q.comp p + p.comp q := by
    simp_rw [two_smul]
    nth_rw 2 [← h]
    simp_rw [mul_eq_comp, add_sub_cancel, add_comm]
  have H : ((2 : 𝕜) • p).comp q = q.comp (p.comp q) + p.comp q := by
    simp_rw [h', add_comp, comp_assoc, ← mul_eq_comp, hq.eq]
  simp_rw [add_comm, two_smul, add_comp, add_right_inj] at H
  have H' : q.comp ((2 : 𝕜) • p) = q.comp p + q.comp (p.comp q) := by
    simp_rw [h', comp_add, ← comp_assoc, ← mul_eq_comp, hq.eq]
  simp_rw [two_smul, comp_add, add_right_inj] at H'
  have H'' : q.comp p = p.comp q := by
    simp_rw [H']
    exact H.symm
  rw [← H'', and_self_iff, ← smul_right_inj (two_ne_zero' 𝕜), h', ← H'', two_smul]


-- @@ L121-127 verbatim
/-- given idempotent operators $p,q$,
  we have $pq = p = qp$ iff $q - p$ is an idempotent operator -/
theorem LinearMap.commutes_iff_isIdempotentElem {E 𝕜 : Type _} [RCLike 𝕜] [AddCommGroup E]
    [Module 𝕜 E] {p q : E →ₗ[𝕜] E} (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    p.comp q = p ∧ q.comp p = p ↔ IsIdempotentElem (q - p) :=
  ⟨fun h => LinearMap.isIdempotentElem_sub_of hq hp h, fun h =>
    LinearMap.commutes_of_isIdempotentElem hp hq h⟩


-- @@ L129-129 verbatim
end


-- @@ L131-131 verbatim
open ContinuousLinearMap


-- @@ L133-133 verbatim
variable {𝕜 E : Type _} [RCLike 𝕜] [NormedAddCommGroup E]


-- @@ L135-135 verbatim
local notation "P" => Submodule.orthogonalProjectionOnto


-- @@ L137-143 verbatim
/-- given self-adjoint operators $p,q$,
  we have $pq=p$ iff $qp=p$ -/
theorem self_adjoint_proj_commutes [InnerProductSpace 𝕜 E] [CompleteSpace E] {p q : E →L[𝕜] E}
    (hpa : IsSelfAdjoint p) (hqa : IsSelfAdjoint q) : p.comp q = p ↔ q.comp p = p := by
  constructor <;> intro h <;>
  · apply_fun adjoint using star_injective
    simp only [adjoint_comp, isSelfAdjoint_iff'.mp hpa, isSelfAdjoint_iff'.mp hqa, h]


-- @@ L145-145 verbatim
local notation "↥P" => orthogonalProjection'


-- @@ L147-147 verbatim
open Submodule


-- @@ L149-152 expanded
theorem orthogonalProjection_isSelfAdjoint [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] : IsSelfAdjoint (orthogonalProjection' U) :=
  isSelfAdjoint_starProjection U


-- @@ L154-157 verbatim
theorem orthogonalProjection_eq_self_iff [InnerProductSpace 𝕜 E]
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] {x : E} :
    (U.orthogonalProjectionOnto x : E) = x ↔ x ∈ U :=
  starProjection_eq_self_iff (K := U)


-- @@ L159-163 verbatim
theorem inner_orthogonalProjection_left_eq_right [InnerProductSpace 𝕜 E]
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (x y : E) :
    inner 𝕜 (U.orthogonalProjectionOnto x : E) y =
      inner 𝕜 x (U.orthogonalProjectionOnto y : E) :=
  inner_starProjection_left_eq_right U x y


-- @@ L165-171 expanded
theorem orthogonalProjection.isIdempotentElem [InnerProductSpace 𝕜 E] (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : IsIdempotentElem (orthogonalProjection' U) :=
  by
  rw [IsIdempotentElem]
  ext
  simp_rw [mul_apply_eq_comp, orthogonalProjection'_eq, comp_apply, Submodule.subtypeL_apply,
    orthogonalProjectionOnto_mem_subspace_eq_self]


-- @@ L173-178 verbatim
/-- A continuous linear map is an orthogonal projection if it is idempotent and
its kernel is the orthogonal complement of its range. -/
class ContinuousLinearMap.IsOrthogonalProjection [InnerProductSpace 𝕜 E]
  (T : E →L[𝕜] E) : Prop where
  isIdempotent : IsIdempotentElem T
  kerEqRangeOrtho : T.ker = T.rangeᗮ


-- @@ L180-183 verbatim
lemma ContinuousLinearMap.IsOrthogonalProjection.eq [InnerProductSpace 𝕜 E]
  {T : E →L[𝕜] E} (hT : T.IsOrthogonalProjection) :
    IsIdempotentElem T ∧ T.ker = T.rangeᗮ :=
⟨hT.1, hT.2⟩


-- @@ L185-187 verbatim
theorem IsIdempotentElem.clm_to_lm [InnerProductSpace 𝕜 E] {T : E →L[𝕜] E} :
    IsIdempotentElem T ↔ IsIdempotentElem (T : E →ₗ[𝕜] E) := by
  simp_rw [IsIdempotentElem, ← ContinuousLinearMap.toLinearMap_mul, coe_inj]


-- @@ L189-196 verbatim
lemma ContinuousLinearMap.HasOrthogonalProjection_of_isOrthogonalProjection [InnerProductSpace 𝕜 E]
    {T : E →L[𝕜] E} [h : T.IsOrthogonalProjection] : HasOrthogonalProjection T.range := by
  constructor
  intro x
  refine ⟨T x, ⟨x, rfl⟩, ?_⟩
  rw [← h.kerEqRangeOrtho]
  change T (x - T x) = 0
  rw [map_sub, ← _root_.mul_apply_eq_comp, h.isIdempotent.eq, sub_self]


-- @@ L198-204 verbatim
lemma ker_to_clm
  {R R₂ M M₂ : Type*} [Semiring R]
  [Semiring R₂] [AddCommMonoid M] [AddCommMonoid M₂]
  [TopologicalSpace M] [TopologicalSpace M₂]
  [Module R M] [Module R₂ M₂] {τ₁₂ : R →+* R₂} (f : M →SL[τ₁₂] M₂) :
    ∀ x, x ∈ LinearMap.ker (ContinuousLinearMap.toLinearMap f) ↔ f x = 0 :=
  fun _ => Iff.rfl



-- @@ L207-211 verbatim
lemma subtype_compL_ker [InnerProductSpace 𝕜 E] (U : Submodule 𝕜 E)
  (f : E →L[𝕜] U) :
    (U.subtypeL ∘L f).ker = f.ker := by
  ext x
  simp_all



-- @@ L214-219 expanded
lemma orthogonalProjection.isOrthogonalProjection [InnerProductSpace 𝕜 E] (U : Submodule 𝕜 E)
    [h : HasOrthogonalProjection U] : (orthogonalProjection' U).IsOrthogonalProjection :=
  by
  refine ⟨orthogonalProjection.isIdempotentElem _, ?_⟩
  rw [orthogonalProjection.range, ← ker_orthogonalProjectionOnto, orthogonalProjection'_eq,
    subtype_compL_ker]


-- @@ L221-250 verbatim
open LinearMap in
/-- given any idempotent operator $T ∈ L(V)$, then `is_compl T.ker T.range`,
in other words, there exists unique $v ∈ \textnormal{ker}(T)$ and $w ∈ \textnormal{range}(T)$ such
  that $x = v + w$ -/
theorem IsIdempotentElem.isCompl_range_ker {V R : Type _} [Semiring R] [AddCommGroup V]
    [Module R V] {T : V →ₗ[R] V} (h : IsIdempotentElem T) : IsCompl (ker T) (range T) := by
  constructor
  · rw [disjoint_iff]
    ext x
    simp only [Submodule.mem_bot, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_range]
    refine ⟨fun h' => ?_, fun h' => ?_⟩
    · rcases h'.2 with ⟨y, hy⟩
      rw [← hy, ← IsIdempotentElem.eq h, Module.End.mul_apply, hy]
      exact h'.1
    · rw [h', map_zero]
      simp only [true_and]
      use x
      simp only [h', map_zero]
  · suffices ∀ x : V, ∃ v : ker T, ∃ w : range T, x = v + w
      by
      rw [codisjoint_iff, ← Submodule.add_eq_sup]
      ext x
      rcases this x with ⟨v, w, hvw⟩
      simp only [Submodule.mem_top, iff_true, hvw]
      apply Submodule.add_mem_sup (SetLike.coe_mem v) (SetLike.coe_mem w)
    intro x
    use ⟨x - T x, ?_⟩, ⟨T x, ?_⟩
    · simp only [sub_add_cancel]
    · rw [LinearMap.mem_ker, map_sub, ← Module.End.mul_apply, IsIdempotentElem.eq h, sub_self]
    · rw [LinearMap.mem_range]; simp only [exists_apply_eq_apply]


-- @@ L252-254 verbatim
theorem IsCompl.of_orthogonal_projection [InnerProductSpace 𝕜 E] {T : E →L[𝕜] E}
    (h : T.IsOrthogonalProjection) : IsCompl T.ker T.range :=
IsIdempotentElem.isCompl_range_ker (IsIdempotentElem.clm_to_lm.mp h.1)


-- @@ L256-259 expanded
theorem orthogonalProjection.ker [InnerProductSpace 𝕜 E] {K : Submodule 𝕜 E}
    [HasOrthogonalProjection K] : (orthogonalProjection' K).ker = Kᗮ :=
  by
  rw [orthogonalProjection']
  exact Submodule.ker_starProjection K


-- @@ L261-265 verbatim
theorem _root_.LinearMap.isIdempotentElem_of_isProj {V R : Type _} [Semiring R] [AddCommGroup V]
    [Module R V] {T : V →ₗ[R] V} {U : Submodule R V}
    (h : LinearMap.IsProj U T) :
  IsIdempotentElem T :=
by ext; exact h.2 _ (h.1 _)


-- @@ L267-303 expanded
/-- $P_V P_U = P_U$ if and only if $P_V - P_U$ is an orthogonal projection -/
theorem sub_of_isOrthogonalProjection [InnerProductSpace ℂ E] [CompleteSpace E]
    {U V : Submodule ℂ E} [CompleteSpace U] [CompleteSpace V] :
    (orthogonalProjection' V).comp (orthogonalProjection' U) = orthogonalProjection' U ↔
      (orthogonalProjection' V - orthogonalProjection' U).IsOrthogonalProjection :=
  by
  let p := orthogonalProjection' U
  let q := orthogonalProjection' V
  have pp : p = U.subtypeL.comp (Submodule.orthogonalProjectionOnto U) := rfl
  have qq : q = V.subtypeL.comp (Submodule.orthogonalProjectionOnto V) := rfl
  have hp : IsIdempotentElem p := orthogonalProjection.isIdempotentElem U
  have hq : IsIdempotentElem q := orthogonalProjection.isIdempotentElem V
  have hpa := orthogonalProjection_isSelfAdjoint U
  have hqa := orthogonalProjection_isSelfAdjoint V
  have h2 := self_adjoint_proj_commutes hpa hqa
  simp_rw [orthogonalProjection', ← pp, ← qq] at *
  constructor
  · intro h
    have h_and : (p : E →ₗ[ℂ] E) ∘ₗ (q : E →ₗ[ℂ] E) = p ∧ (q : E →ₗ[ℂ] E) ∘ₗ (p : E →ₗ[ℂ] E) = p :=
      by
      constructor
      · change
          U.starProjection.toLinearMap ∘ₗ V.starProjection.toLinearMap =
            U.starProjection.toLinearMap
        exact congrArg ContinuousLinearMap.toLinearMap ((h2.mpr h))
      · change
          V.starProjection.toLinearMap ∘ₗ U.starProjection.toLinearMap =
            U.starProjection.toLinearMap
        exact congrArg ContinuousLinearMap.toLinearMap h
    rw [LinearMap.commutes_iff_isIdempotentElem (IsIdempotentElem.clm_to_lm.mp hp)
        (IsIdempotentElem.clm_to_lm.mp hq),
      ← ContinuousLinearMap.toLinearMap_sub, ← IsIdempotentElem.clm_to_lm] at h_and
    refine ⟨h_and, ?_⟩
    exact
      (IsIdempotentElem.isSelfAdjoint_iff_ker_isOrtho_to_range _ h_and).mp
        (IsSelfAdjoint.sub hqa hpa)
  · rintro ⟨h1, _⟩
    have hlin :=
      LinearMap.commutes_of_isIdempotentElem (IsIdempotentElem.clm_to_lm.mp hp)
        (IsIdempotentElem.clm_to_lm.mp hq) (IsIdempotentElem.clm_to_lm.mp h1)
    exact coe_inj.mp hlin.2


-- @@ L305-305 verbatim
section


-- @@ L307-310 verbatim
/-- instance for `≤` on linear maps -/
instance LinearMap.IsSymmetric.hasLe {𝕜 E : Type _} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] : LE (E →ₗ[𝕜] E) :=
  { le := fun u v => (v - u : E →ₗ[𝕜] E).IsPositive' }


-- @@ L312-315 verbatim
/-- The subtype of symmetric linear endomorphisms of a complex inner product space. -/
@[reducible]
def SymmetricLM (g : Type*) [NormedAddCommGroup g] [InnerProductSpace ℂ g] :=
{x : g →ₗ[ℂ] g | LinearMap.IsSymmetric x}


-- @@ L317-321 verbatim
/-- The subtype of self-adjoint continuous linear endomorphisms of a complex Hilbert space. -/
@[reducible]
def SelfAdjointCLM (g : Type*) [NormedAddCommGroup g] [InnerProductSpace ℂ g]
  [CompleteSpace g] :=
{x : g →L[ℂ] g | IsSelfAdjoint x}


-- @@ L323-323 verbatim
local notation "L(" x "," y ")" => x →L[y] x


-- @@ L325-325 verbatim
local notation "l(" x "," y ")" => x →ₗ[y] x


-- @@ L327-327 verbatim
open scoped ComplexOrder

-- @@ L328-351 verbatim
instance instPartialOrderLinearMapIdLeanPool {𝕜 E : Type _} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] :
    PartialOrder (E →ₗ[𝕜] E) where
  le := fun u v => LinearMap.IsPositive' (v - u : E →ₗ[𝕜] E)
  lt := fun u v =>
    LinearMap.IsPositive' (v - u : E →ₗ[𝕜] E) ∧
      ¬ LinearMap.IsPositive' (u - v : E →ₗ[𝕜] E)
  lt_iff_le_not_ge := fun _ _ => Iff.rfl
  le_refl := fun a => by
    simp_rw [sub_self]
    exact ⟨fun u v => by simp, fun x => by simp⟩
  le_trans := by
    intro a b c hab hbc
    rw [← add_zero (c : E →ₗ[𝕜] E), ← sub_self ↑b, ← add_sub_assoc, add_sub_right_comm,
      add_sub_assoc]
    exact LinearMap.IsPositive'.add hbc hab
  le_antisymm := by
    rintro a b hba hab
    rw [← sub_eq_zero, ← LinearMap.IsSymmetric.inner_map_self_eq_zero hab.1]
    intro x
    have hba2 := hba.2 x
    rw [← neg_le_neg_iff, ← inner_neg_right, ← LinearMap.neg_apply, neg_sub, neg_zero] at hba2
    rw [hab.1]
    apply le_antisymm hba2 (hab.2 _)


-- @@ L353-355 verbatim
/-- `p ≤ q` means `q - p` is positive -/
theorem LinearMap.IsPositive'.hasLe {E : Type _} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {p q : SymmetricLM E} : p ≤ q ↔ (q - p : l(E,ℂ)).IsPositive' := by rfl


-- @@ L357-360 verbatim
noncomputable instance IsSymmetric.hasZero {E : Type _} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] : Zero ↥{x : E →ₗ[ℂ] E | x.IsSymmetric} :=
  ⟨⟨0, by
    simp_all⟩⟩


-- @@ L362-366 verbatim
/-- saying `p` is positive is the same as saying `0 ≤ p` -/
theorem LinearMap.IsPositive'.is_nonneg {𝕜 E : Type _} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {p : l(E,𝕜)} : p.IsPositive' ↔ 0 ≤ p := by
  nth_rw 1 [← sub_zero p]
  rfl


-- @@ L368-368 verbatim
end


-- @@ L370-375 verbatim
/-- a self-adjoint idempotent operator is positive -/
theorem SelfAdjointAndIdempotent.is_positive {𝕜 E : Type _} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] {p : E →L[𝕜] E} (hp : IsIdempotentElem p)
    (hpa : IsSelfAdjoint p) : 0 ≤ p := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive]
  exact hp.isPositive_iff_isSelfAdjoint.mpr hpa


-- @@ L377-381 verbatim
/-- an idempotent is positive if and only if it is self-adjoint -/
theorem IsIdempotentElem.is_positive_iff_self_adjoint [InnerProductSpace 𝕜 E] [CompleteSpace E]
    {p : E →L[𝕜] E} (hp : IsIdempotentElem p) : 0 ≤ p ↔ IsSelfAdjoint p := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive]
  exact hp.isPositive_iff_isSelfAdjoint


-- @@ L383-395 verbatim
theorem IsIdempotentElem.self_adjoint_is_positive_isOrthogonalProjection_tFAE {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] {p : E →L[ℂ] E}
    (hp : IsIdempotentElem p) : List.TFAE [IsSelfAdjoint p, p.IsOrthogonalProjection, 0 ≤ p] := by
  tfae_have 3 ↔ 1 := hp.is_positive_iff_self_adjoint
  tfae_have 2 → 1 := by
    intro h
    rw [IsIdempotentElem.isSelfAdjoint_iff_ker_isOrtho_to_range _ hp]
    exact h.2
  tfae_have 1 → 2 := by
    intro h
    rw [IsIdempotentElem.isSelfAdjoint_iff_ker_isOrtho_to_range _ hp] at h
    exact ⟨hp, h⟩
  tfae_finish


-- @@ L397-401 expanded
/-- orthogonal projections are obviously positive -/
theorem orthogonalProjection.is_positive [InnerProductSpace ℂ E] {U : Submodule ℂ E}
    [CompleteSpace E] [CompleteSpace U] :
    0 ≤ U.subtypeL.comp (Submodule.orthogonalProjectionOnto U) :=
  SelfAdjointAndIdempotent.is_positive (orthogonalProjection.isIdempotentElem U)
    (orthogonalProjection_isSelfAdjoint U)


-- @@ L403-411 verbatim
theorem SelfAdjointAndIdempotent.sub_is_positive_of [InnerProductSpace 𝕜 E] [CompleteSpace E]
    {p q : E →L[𝕜] E} (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) (hpa : IsSelfAdjoint p)
    (hqa : IsSelfAdjoint q) (h : p.comp q = p) : 0 ≤ q - p :=
  SelfAdjointAndIdempotent.is_positive
    (coe_inj.mp
      ((LinearMap.commutes_iff_isIdempotentElem (IsIdempotentElem.clm_to_lm.mp hp)
            (IsIdempotentElem.clm_to_lm.mp hq)).mp
        ⟨coe_inj.mpr h, coe_inj.mpr ((self_adjoint_proj_commutes hpa hqa).mp h)⟩))
    (IsSelfAdjoint.sub hqa hpa)


-- @@ L413-420 expanded
/-- given orthogonal projections `Pᵤ,Pᵥ`,
  then `Pᵤ(Pᵥ)=Pᵤ` implies `Pᵥ-Pᵤ` is positive (i.e., `Pᵤ ≤ Pᵥ`) -/
theorem orthogonalProjection.sub_is_positive_of [InnerProductSpace ℂ E] {U V : Submodule ℂ E}
    [CompleteSpace U] [CompleteSpace V] [CompleteSpace E]
    (h : (orthogonalProjection' U).comp (orthogonalProjection' V) = orthogonalProjection' U) :
    0 ≤ orthogonalProjection' V - orthogonalProjection' U :=
  SelfAdjointAndIdempotent.sub_is_positive_of (orthogonalProjection.isIdempotentElem U)
    (orthogonalProjection.isIdempotentElem V) (orthogonalProjection_isSelfAdjoint U)
    (orthogonalProjection_isSelfAdjoint V) h


-- @@ L422-437 expanded
/-- given orthogonal projections `Pᵤ,Pᵥ`,
  then if `Pᵥ - Pᵤ` is idempotent, then `Pᵤ Pᵥ = Pᵤ` -/
theorem orthogonal_projection_commutes_of_is_idempotent [InnerProductSpace ℂ E]
    {U V : Submodule ℂ E} [CompleteSpace U] [CompleteSpace V]
    (h : IsIdempotentElem (orthogonalProjection' V - orthogonalProjection' U)) :
    (orthogonalProjection' V).comp (orthogonalProjection' U) = orthogonalProjection' U :=
  by
  let p := orthogonalProjection' U
  let q := orthogonalProjection' V
  have pp : p = U.subtypeL.comp (Submodule.orthogonalProjectionOnto U) := rfl
  have qq : q = V.subtypeL.comp (Submodule.orthogonalProjectionOnto V) := rfl
  simp_rw [← pp, ← qq] at *
  have hp : IsIdempotentElem p := orthogonalProjection.isIdempotentElem U
  have hq : IsIdempotentElem q := orthogonalProjection.isIdempotentElem V
  exact
    coe_inj.mp
      (LinearMap.commutes_of_isIdempotentElem (IsIdempotentElem.clm_to_lm.mp hp)
          (IsIdempotentElem.clm_to_lm.mp hq) (IsIdempotentElem.clm_to_lm.mp h)).2


-- @@ L439-439 verbatim
open scoped FiniteDimensional


-- @@ L441-454 verbatim
/-- copy of `linear_map.is_positive_iff_exists_adjoint_mul_self` -/
theorem ContinuousLinearMap.isPositive_iff_exists_adjoint_hMul_self [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [CompleteSpace E] (T : E →L[𝕜] E) :
    T.IsPositive ↔ ∃ S : E →L[𝕜] E, T = adjoint S * S := by
  rw [IsPositive.toLinearMap', LinearMap.isPositive'_iff_exists_adjoint_hMul_self]
  constructor
  · rintro ⟨S, hS⟩
    use LinearMap.toContinuousLinearMap S
    ext
    rw [← ContinuousLinearMap.coe_coe T, hS]
    rfl
  · rintro ⟨S, hS⟩
    simp_rw [ContinuousLinearMap.ext_iff, ← ContinuousLinearMap.coe_coe, ← LinearMap.ext_iff] at *
    exact ⟨S, hS⟩


-- @@ L456-456 verbatim
open RCLike

-- @@ L457-457 verbatim
open scoped InnerProductSpace


-- @@ L459-477 verbatim
/-- in a finite-dimensional complex Hilbert space `E`,
  if `p,q` are self-adjoint operators, then
  `p ≤ q` iff `∀ x ∈ E : ⟪x, p x⟫ ≤ ⟪x, q x⟫` -/
theorem ContinuousLinearMap.is_positive_le_iff_inner [InnerProductSpace 𝕜 E]
    [CompleteSpace E]
    {p q : E →L[𝕜] E} (hpa : IsSelfAdjoint p) (hqa : IsSelfAdjoint q) :
    p ≤ q ↔ ∀ x : E, re ⟪x, p x⟫_𝕜 ≤ re ⟪x, q x⟫_𝕜 := by
  rw [ContinuousLinearMap.le_def]
  constructor
  · intro h x
    rw [← sub_nonneg, ← map_sub, ← inner_sub_right, ← sub_apply]
    exact IsPositive.re_inner_nonneg_right h x
  · intro h
    rw [ContinuousLinearMap.isPositive_def']
    refine ⟨IsSelfAdjoint.sub hqa hpa, fun x => ?_⟩
    simp_rw [reApplyInnerSelf_apply, sub_apply, inner_sub_left, map_sub, sub_nonneg]
    nth_rw 1 [inner_re_symm]
    nth_rw 2 [inner_re_symm]
    exact h x


-- @@ L479-479 verbatim
local notation "⟪" x "," y "⟫" => @inner 𝕜 _ _ x y


-- @@ L481-490 expanded
/-- given self-adjoint idempotent operators `p,q`, we have
  `∀ x ∈ E : ⟪x, p x⟫ ≤ ⟪x, q x⟫ ↔ ∀ x ∈ E, ‖p x‖ ≤ ‖q x‖` -/
theorem ContinuousLinearMap.hasLe_norm [InnerProductSpace 𝕜 E] [CompleteSpace E] {p q : E →L[𝕜] E}
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) (hpa : IsSelfAdjoint p)
    (hqa : IsSelfAdjoint q) :
    (∀ x : E, re (@inner 𝕜 _ _ x (p x)) ≤ re (@inner 𝕜 _ _ x (q x))) ↔ ∀ x : E, ‖p x‖ ≤ ‖q x‖ :=
  by
  rw [← hp.eq, ← hq.eq]
  simp_rw [_root_.mul_apply_eq_comp, ← adjoint_inner_left _ (q _) _, ← adjoint_inner_left _ (p _) _,
    isSelfAdjoint_iff'.mp hpa, isSelfAdjoint_iff'.mp hqa, inner_self_eq_norm_sq, sq_le_sq, abs_norm,
    ← _root_.mul_apply_eq_comp, hp.eq, hq.eq]


-- @@ L492-493 verbatim
theorem IsPositive.HasLe.sub [InnerProductSpace 𝕜 E] {p q : E →L[𝕜] E} :
    p ≤ q ↔ 0 ≤ q - p := by simp only [LE.le, sub_zero]


-- @@ L495-520 verbatim
theorem self_adjoint_and_idempotent_is_positive_iff_commutes
    [InnerProductSpace ℂ E]
    [CompleteSpace E] {p q : E →L[ℂ] E}
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) (hpa : IsSelfAdjoint p)
    (hqa : IsSelfAdjoint q) : p ≤ q ↔ q.comp p = p := by
  rw [← self_adjoint_proj_commutes hpa hqa, IsPositive.HasLe.sub]
  constructor
  · intro h
    rw [← IsPositive.HasLe.sub,
      ContinuousLinearMap.is_positive_le_iff_inner hpa hqa] at h
    symm
    rw [← sub_eq_zero]
    nth_rw 1 [← mul_one p]
    simp_rw [ContinuousLinearMap.mul_def, ← comp_sub, ← ContinuousLinearMap.inner_map_self_eq_zero,
      comp_apply, sub_apply,
      one_apply_eq_self]
    intro x
    specialize h ((1 - q) x)
    simp_rw [sub_apply, map_sub, ← mul_apply_eq_comp, mul_one, hq.eq,
      sub_self, inner_zero_right, one_apply_eq_self,
      mul_apply_eq_comp, ← map_sub, zero_re] at h
    rw [← hp.eq, mul_apply_eq_comp, ← adjoint_inner_left, isSelfAdjoint_iff'.mp hpa,
      re_inner_self_nonpos] at h
    rw [h, inner_zero_left]
  · intro h
    exact SelfAdjointAndIdempotent.sub_is_positive_of hp hq hpa hqa h


-- @@ L522-529 expanded
/-- in a complex-finite-dimensional Hilbert space `E`, we have
  `Pᵤ ≤ Pᵤ` iff `PᵥPᵤ = Pᵤ` -/
theorem orthogonal_projection_is_le_iff_commutes [InnerProductSpace ℂ E] {U V : Submodule ℂ E}
    [CompleteSpace E] [CompleteSpace U] [CompleteSpace V] :
    orthogonalProjection' U ≤ orthogonalProjection' V ↔
      (orthogonalProjection' V).comp (orthogonalProjection' U) = orthogonalProjection' U :=
  self_adjoint_and_idempotent_is_positive_iff_commutes (orthogonalProjection.isIdempotentElem U)
    (orthogonalProjection.isIdempotentElem V) (orthogonalProjection_isSelfAdjoint U)
    (orthogonalProjection_isSelfAdjoint V)


-- @@ L531-533 expanded
theorem orthogonalProjection.is_le_iff_subset [InnerProductSpace ℂ E] {U V : Submodule ℂ E}
    [CompleteSpace U] [CompleteSpace V] :
    orthogonalProjection' U ≤ orthogonalProjection' V ↔ U ≤ V :=
  Submodule.starProjection_le_starProjection_iff


-- @@ L535-538 verbatim
theorem Submodule.map_to_linearMap [Module 𝕜 E] {p : E →L[𝕜] E} {U : Submodule 𝕜 E}
    {x : E} :
    x ∈ Submodule.map (p : E →ₗ[𝕜] E) U ↔ ∃ y ∈ U, p y = x :=
  Iff.rfl


-- @@ L540-552 verbatim
/-- given self-adjoint idempotent operators `p,q` we have,
  `p(E) ⊆ q(E)` iff `q - p` is an idempotent operator -/
theorem ContinuousLinearMap.image_subset_iff_sub_of_is_idempotent [InnerProductSpace 𝕜 E]
    [CompleteSpace E] {p q : E →L[𝕜] E} (hp : IsIdempotentElem p) (hq : IsIdempotentElem q)
    (hpa : IsSelfAdjoint p) (hqa : IsSelfAdjoint q) :
    p.range ≤ q.range ↔ IsIdempotentElem (q - p) := by
  simp_rw [IsIdempotentElem.clm_to_lm, ContinuousLinearMap.toLinearMap_sub, ←
    LinearMap.commutes_iff_isIdempotentElem (IsIdempotentElem.clm_to_lm.mp hp)
      (IsIdempotentElem.clm_to_lm.mp hq)]
  simp_rw [← ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.coe_inj,
    self_adjoint_proj_commutes hpa hqa, and_self_iff, ← ContinuousLinearMap.coe_inj,
    ContinuousLinearMap.toLinearMap_comp,
    IsIdempotentElem.comp_idempotent_iff (IsIdempotentElem.clm_to_lm.mp hq)]


-- @@ L554-554 verbatim
section MinProj


-- @@ L556-559 verbatim
/-- definition of a map being a minimal projection -/
def ContinuousLinearMap.IsMinimalProjection [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (x : E →L[𝕜] E) (U : Submodule 𝕜 E) : Prop :=
  IsSelfAdjoint x ∧ Module.finrank 𝕜 U = 1 ∧ LinearMap.IsProj U x


-- @@ L561-565 verbatim
/-- definition of orthogonal projection being minimal
  i.e., when the dimension of its space equals one -/
def orthogonalProjection.IsMinimalProjection [InnerProductSpace 𝕜 E] (U : Submodule 𝕜 E)
    : Prop :=
  Module.finrank 𝕜 U = 1


-- @@ L567-567 verbatim
open FiniteDimensional


-- @@ L569-588 verbatim
/-- when a submodule `U` has dimension `1`, then
  for any submodule `V`, we have `V ≤ U` if and only if `V = U` or `V = 0` -/
theorem Submodule.le_finrank_one
  {R M : Type*} [Field R] [AddCommGroup M] [Module R M]
  (U V : Submodule R M) [Module.Finite R ↥U] [Module.Finite R ↥V]
  (hU : Module.finrank R U = 1) : V ≤ U ↔ V = U ∨ V = 0 := by
  simp_rw [Submodule.zero_eq_bot]
  constructor
  · intro h
    have : Module.finrank R V ≤ 1 := by rw [← hU]; exact Submodule.finrank_mono h
    have h01 : Module.finrank R V = 0 ∨ Module.finrank R V = 1 := Order.le_succ_bot_iff.mp this
    rcases h01 with this_1 | this_1
    · exact Or.inr (Submodule.finrank_eq_zero.mp this_1)
    · left
      apply eq_of_le_of_finrank_eq h
      simp_rw [this_1, hU]
  · intro h
    rcases h with (⟨rfl, rfl⟩ | h)
    · exact le_refl U
    · simp_all


-- @@ L590-609 expanded
/-- for orthogonal projections `Pᵤ,Pᵥ`,
  if `Pᵤ` is a minimal orthogonal projection, then
  for any `Pᵥ` if `Pᵥ ≤ Pᵤ` and `Pᵥ ≠ 0`, then `Pᵥ = Pᵤ` -/
theorem orthogonalProjection.isMinimalProjection_of [InnerProductSpace ℂ E] (U W : Submodule ℂ E)
    [CompleteSpace U] [CompleteSpace W] [Module.Finite ℂ ↥U] [Module.Finite ℂ ↥W]
    (hU : orthogonalProjection.IsMinimalProjection U)
    (hW : orthogonalProjection' W ≤ orthogonalProjection' U) (h : orthogonalProjection' W ≠ 0) :
    orthogonalProjection' W = orthogonalProjection' U :=
  by
  refine le_antisymm hW ?_
  have hWU : W ≤ U := (orthogonalProjection.is_le_iff_subset).mp hW
  have := Submodule.finrank_mono hWU
  simp_rw [orthogonalProjection.IsMinimalProjection] at hU
  have hcases := (Submodule.le_finrank_one U W hU).mp hWU
  have hUW : U ≤ W := by
    rcases hcases with hW1 | hW2
    · rw [hW1]
    · simp_all
  exact (orthogonalProjection.is_le_iff_subset).mpr hUW


-- @@ L611-630 verbatim
/-- any rank one operator given by a norm one vector is a minimal projection -/
theorem rankOne_self_isMinimalProjection [InnerProductSpace ℂ E] [CompleteSpace E] {x : E}
    (h : ‖x‖ = 1) : (rankOne ℂ x x).IsMinimalProjection (Submodule.span ℂ {x}) := by
  refine ⟨rankOne_self_isSelfAdjoint (𝕜 := ℂ) (x := x), ?_, ?_⟩
  · rw [finrank_eq_one_iff']
    use ⟨x, Submodule.mem_span_singleton_self x⟩
    constructor
    · intro hw
      simp_all
    · intro w
      rcases Submodule.mem_span_singleton.mp (SetLike.coe_mem w) with ⟨r, hr⟩
      use r
      simp_all
  · apply LinearMap.IsProj.mk
    · intro z
      rw [rankOne_apply]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
    · intro z hz
      rcases Submodule.mem_span_singleton.mp hz with ⟨r, rfl⟩
      simp [inner_self_eq_norm_sq_to_K, h]


-- @@ L632-641 verbatim
/-- if `x ∈ E` then we can normalize this (i.e., there exists `y ∈ E`
  such that `∥y∥ = 1` where `x = r • y` for some `r ∈ ℝ`) unless `x = 0` -/
theorem normalize_op [InnerProductSpace ℂ E] (x : E) :
    (∃ (y : E) (r : ℝ), ‖y‖ = 1 ∧ x = (r : ℂ) • y) ∨ x = 0 := by
  by_cases A : x = 0
  · exact Or.inr A
  · have B : ‖x‖ ≠ 0 := by simpa only [ne_eq, norm_eq_zero]
    refine Or.inl ⟨(1 / ‖x‖) • x, ‖x‖, ?_, ?_⟩
    · simp_rw [norm_smul, one_div, norm_inv, norm_norm, mul_comm, mul_inv_cancel₀ B]
    · simp_rw [one_div, Complex.coe_smul, smul_inv_smul₀ B]


-- @@ L643-663 verbatim
/-- given any non-zero `x ∈ E`, we have
  `1 / ‖x‖ ^ 2 • |x⟩⟨x|` is a minimal projection -/
theorem rankOne_self_isMinimalProjection' [InnerProductSpace ℂ E] [CompleteSpace E] {x :
    E} (h : x ≠ 0) :
    IsMinimalProjection ((1 / ‖x‖ ^ 2) • rankOne ℂ x x) (Submodule.span ℂ {x}) := by
  rcases normalize_op x with ⟨y, r, ⟨hy, hx⟩⟩
  · have : r ^ 2 ≠ 0 := by
      simp_all
    simp_rw [hx, Complex.coe_smul, one_div, ← Complex.coe_smul, map_smulₛₗ, LinearMap.smul_apply,
      RingHom.id_apply, Complex.conj_ofReal,
      norm_smul, mul_pow, Complex.norm_real, mul_inv, smul_smul, hy,
      one_pow, inv_one, mul_one, Real.norm_eq_abs, ← abs_pow, pow_two, abs_mul_self, ← pow_two,
      Complex.ofReal_inv, Complex.ofReal_pow, Complex.coe_smul]
    norm_cast
    rw [inv_mul_cancel₀ this, one_smul]
    have : Submodule.span ℂ {((r : ℝ) : ℂ) • y} = Submodule.span ℂ {y} := by
      rw [Submodule.span_singleton_smul_eq _]
      simp_all
    rw [← Complex.coe_smul, this]
    exact rankOne_self_isMinimalProjection hy
  · contradiction


-- @@ L665-673 verbatim
lemma LinearMap.range_of_isProj {R M : Type*} [CommSemiring R] [AddCommGroup M] [Module R M]
  {p : M →ₗ[R] M} {U : Submodule R M}
  (hp : LinearMap.IsProj U p) :
  LinearMap.range p = U := by
  ext x
  rw [mem_range]
  refine ⟨fun ⟨y, hy⟩ => ?_, fun h => ⟨x, hp.map_id _ h⟩⟩
  · rw [← hy]
    exact hp.map_mem y


-- @@ L675-675 verbatim
open scoped FiniteDimensional

-- @@ L676-713 expanded
/-- a linear operator is an orthogonal projection onto a submodule, if and only if
  it is self-adjoint and idempotent;
  so it always suffices to say `p = p⋆ = p²` -/
theorem orthogonal_projection_iff [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [CompleteSpace E]
    {p : E →L[𝕜] E} :
    (∃ (U : Submodule 𝕜 E), --(hU : CompleteSpace U)
        orthogonalProjection' U = p) ↔
      IsSelfAdjoint p ∧ IsIdempotentElem p :=
  by
  constructor
  · rintro ⟨U, rfl⟩
    exact ⟨orthogonalProjection_isSelfAdjoint _, orthogonalProjection.isIdempotentElem _⟩
  · rintro ⟨h1, h2⟩
    simp_rw [IsIdempotentElem, ContinuousLinearMap.mul_def, ContinuousLinearMap.ext_iff, ←
      ContinuousLinearMap.coe_coe, ContinuousLinearMap.toLinearMap_comp, ← LinearMap.ext_iff] at h2
    rcases (LinearMap.isProj_iff_isIdempotentElem _).mpr h2 with ⟨W, hp⟩
    let p' := isProj' hp
    have hp' : p' = isProj' hp := rfl
    simp_rw [ContinuousLinearMap.ext_iff, ← ContinuousLinearMap.coe_coe, ← isProj'_apply hp,
      orthogonalProjection'_eq_linear_proj', ← hp']
    rw [← LinearMap.projectionOnto_of_proj p' (isProj'_eq hp)]
    use W
    · intro x
      simp_rw [LinearMap.coe_comp, Submodule.coe_subtype]
      suffices this : LinearMap.ker p' = Wᗮ by simp_rw [this]; rfl
      ext y
      simp_rw [LinearMap.mem_ker, Submodule.mem_orthogonal]
      constructor
      · intro hp'y u hu
        rw [← hp.2 u hu, ContinuousLinearMap.coe_coe, ← adjoint_inner_right,
          IsSelfAdjoint.adjoint_eq h1, ← ContinuousLinearMap.coe_coe, ← isProj'_apply hp, ← hp',
          hp'y, Submodule.coe_zero, inner_zero_right]
      · intro h
        rw [← Submodule.coe_eq_zero, ← @inner_self_eq_zero 𝕜, isProj'_apply hp,
          ContinuousLinearMap.coe_coe, ← adjoint_inner_left, IsSelfAdjoint.adjoint_eq h1, ←
          ContinuousLinearMap.coe_coe, ← LinearMap.comp_apply, h2,
          h _ (LinearMap.IsProj.map_mem hp _)]


-- @@ L715-718 expanded
private theorem starProjection_isProj [InnerProductSpace 𝕜 E] (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : LinearMap.IsProj U (orthogonalProjection' U) :=
  ⟨Submodule.starProjection_apply_mem U, fun _ hx => Submodule.starProjection_eq_self_iff.mpr hx⟩


-- @@ L720-756 expanded
/-- a linear operator is an orthogonal projection onto a submodule, if and only if
  it is a self-adjoint linear projection onto the submodule;
  also see `orthogonal_projection_iff` -/
theorem orthogonal_projection_iff' [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [CompleteSpace E]
    {p : E →L[𝕜] E} (U : Submodule 𝕜 E) :
    orthogonalProjection' U = p ↔ IsSelfAdjoint p ∧ LinearMap.IsProj U p :=
  by
  constructor
  · intro h
    rw [← h]
    exact ⟨orthogonalProjection_isSelfAdjoint _, starProjection_isProj U⟩
  · rintro ⟨h, h2⟩
    have hp : LinearMap.IsProj U (p : E →ₗ[𝕜] E) := ⟨h2.1, h2.2⟩
    have : IsIdempotentElem p := by
      rw [IsIdempotentElem.clm_to_lm]
      exact (LinearMap.isProj_iff_isIdempotentElem (p : E →ₗ[𝕜] E)).mp ⟨U, hp⟩
    simp_rw [ContinuousLinearMap.ext_iff, ← ContinuousLinearMap.coe_coe,
      orthogonalProjection'_eq_linear_proj']
    let p' := isProj' hp
    have hp' : p' = isProj' hp := rfl
    simp_rw [← isProj'_apply hp, ← hp']
    rw [← LinearMap.projectionOnto_of_proj p' (isProj'_eq hp)]
    simp_rw [LinearMap.coe_comp, Submodule.coe_subtype]
    intro x
    suffices this : LinearMap.ker p' = Uᗮ by simp_rw [this]; rfl
    ext y
    simp_rw [LinearMap.mem_ker, Submodule.mem_orthogonal]
    constructor
    · intro hp'y u hu
      rw [← hp.2 u hu, ContinuousLinearMap.coe_coe, ← adjoint_inner_right,
        IsSelfAdjoint.adjoint_eq h, ← ContinuousLinearMap.coe_coe, ← isProj'_apply hp, ← hp', hp'y,
        Submodule.coe_zero, inner_zero_right]
    · intro h'
      rw [← Submodule.coe_eq_zero, ← @inner_self_eq_zero 𝕜, isProj'_apply hp,
        ContinuousLinearMap.coe_coe, ← adjoint_inner_left, IsSelfAdjoint.adjoint_eq h, ←
        mul_apply_eq_comp, this, h' _ (LinearMap.IsProj.map_mem h2 _)]


-- @@ L758-762 expanded
theorem orthogonalProjection.isMinimalProjection_to_clm [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] [CompleteSpace E] (U : Submodule 𝕜 E) :
    (orthogonalProjection' U).IsMinimalProjection U ↔ orthogonalProjection.IsMinimalProjection U :=
  ⟨fun h => h.2.1, fun h => ⟨orthogonalProjection_isSelfAdjoint U, h, starProjection_isProj U⟩⟩


-- @@ L764-770 verbatim
theorem Submodule.isOrtho_iff_inner_eq' {𝕜 E : Type _} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {U W : Submodule 𝕜 E} :
    U ⟂ W ↔ ∀ (u : ↥U) (w : ↥W), inner 𝕜 (u : E) (w : E) = 0 := by
  rw [Submodule.isOrtho_iff_inner_eq]
  simp_all

-- moved from `ips.lean`

-- @@ L771-792 expanded
/-- `U` and `W` are mutually orthogonal if and only if `(P U).comp (P W) = 0`,
where `P U` is `orthogonal_projection U` -/
theorem Submodule.is_pairwise_orthogonal_iff_orthogonal_projection_comp_eq_zero
    [InnerProductSpace 𝕜 E] (U W : Submodule 𝕜 E) [HasOrthogonalProjection U]
    [HasOrthogonalProjection W] :
    U ⟂ W ↔ (orthogonalProjection' U).comp (orthogonalProjection' W) = 0 :=
  by
  rw [Submodule.isOrtho_iff_inner_eq']
  constructor
  · intro h
    ext v
    rw [ContinuousLinearMap.comp_apply, zero_apply, ← @inner_self_eq_zero 𝕜,
      orthogonalProjection'_apply, orthogonalProjection'_apply, ←
      inner_orthogonalProjection_left_eq_right, orthogonalProjectionOnto_mem_subspace_eq_self]
    exact h _ _
  · intro h x y
    rw [← (orthogonalProjection_eq_self_iff U).mpr (SetLike.coe_mem x), ←
      (orthogonalProjection_eq_self_iff W).mpr (SetLike.coe_mem y),
      inner_orthogonalProjection_left_eq_right, ← orthogonalProjection'_apply, ←
      orthogonalProjection'_apply, ← ContinuousLinearMap.comp_apply, h, zero_apply,
      inner_zero_right]
      --


-- @@ L793-795 expanded
theorem orthogonalProjection.orthogonal_complement_eq [InnerProductSpace 𝕜 E] (U : Submodule 𝕜 E)
    [HasOrthogonalProjection U] : orthogonalProjection' Uᗮ = 1 - orthogonalProjection' U :=
  Submodule.starProjection_orthogonal' U


-- @@ L797-803 expanded
example [InnerProductSpace ℂ E] {U W : Submodule ℂ E} [CompleteSpace E] [CompleteSpace U]
    [CompleteSpace W] :
    (orthogonalProjection' U).comp (orthogonalProjection' W) = 0 ↔
      orthogonalProjection' U + orthogonalProjection' W ≤ 1 :=
  by
  simp_rw [← Submodule.is_pairwise_orthogonal_iff_orthogonal_projection_comp_eq_zero,
    Submodule.isOrtho_iff_le, ← orthogonalProjection.is_le_iff_subset,
    orthogonalProjection.orthogonal_complement_eq,
    add_comm (orthogonalProjection' U) (orthogonalProjection' W), LE.le, sub_add_eq_sub_sub]


-- @@ L805-805 verbatim
end MinProj


-- @@ L807-807 verbatim
section

-- @@ L808-812 verbatim
lemma ContinuousLinearMap.isOrthogonalProjection_iff
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (T : E →L[𝕜] E) :
    T.IsOrthogonalProjection ↔ IsIdempotentElem T ∧ T.ker = T.rangeᗮ :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩


-- @@ L814-814 verbatim
open scoped FiniteDimensional

-- @@ L815-826 verbatim
theorem ContinuousLinearMap.isOrthogonalProjection_iff'
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {p : E →L[ℂ] E} :
    p.IsOrthogonalProjection
    ↔ IsIdempotentElem p ∧ IsSelfAdjoint p := by
  rw [isOrthogonalProjection_iff]
  simp only [and_congr_right_iff]
  intro h
  have := List.TFAE.out (IsIdempotentElem.self_adjoint_is_positive_isOrthogonalProjection_tFAE
    h) 1 2
  rw [this, isOrthogonalProjection_iff]
  simp only [h, true_and]


-- @@ L828-834 verbatim
lemma LinearMap.isSelfAdjoint_toContinuousLinearMap
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [CompleteSpace E]
    (f : E →ₗ[𝕜] E) :
      _root_.IsSelfAdjoint (LinearMap.toContinuousLinearMap f) ↔ _root_.IsSelfAdjoint f := by
    simp_rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric, isSymmetric_iff_isSelfAdjoint]
    rfl


-- @@ L836-846 verbatim
lemma LinearMap.isOrthogonalProjection_iff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [CompleteSpace E]
    (T : E →ₗ[ℂ] E) :
    (LinearMap.toContinuousLinearMap T).IsOrthogonalProjection
      ↔ IsIdempotentElem T ∧ IsSelfAdjoint T := by
  rw [ContinuousLinearMap.isOrthogonalProjection_iff',
    isSelfAdjoint_toContinuousLinearMap]
  refine ⟨fun h => ⟨by simpa using (IsIdempotentElem.clm_to_lm.mp h.1), h.2⟩, fun h => ⟨?_, h.2⟩⟩
  rw [IsIdempotentElem.clm_to_lm]
  simpa using h.1

-- @@ L847-847 verbatim
end


-- @@ L849-856 verbatim
lemma lmul_isIdempotentElem_iff {R A : Type*} [CommSemiring R]
  [Semiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] (a : A) :
  (IsIdempotentElem (lmul a : _ →ₗ[R] _)) ↔ (IsIdempotentElem a) := by
  simp_rw [IsIdempotentElem, mul_eq_comp, lmul_eq_mul, ← LinearMap.mulLeft_mul]
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  rw [LinearMap.ext_iff] at h
  specialize h 1
  simp_all


-- @@ L858-865 verbatim
lemma lmul_tmul {R A B : Type*} [CommSemiring R]
  [Semiring A] [Semiring B] [Module R A] [Module R B] [SMulCommClass R A A]
  [SMulCommClass R B B] [IsScalarTower R A A] [IsScalarTower R B B] (a : A) (b : B) :
  lmul (a ⊗ₜ[R] b) = TensorProduct.map (lmul a) (lmul b) := by
  ext
  simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.coe_restrictScalars, TensorProduct.map_tmul, lmul_apply,
    Algebra.TensorProduct.tmul_mul_tmul]


-- @@ L867-874 verbatim
lemma lmul_eq_lmul_iff {R A : Type*} [CommSemiring R]
  [Semiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] (a b : A) :
  lmul a = (lmul b : _ →ₗ[R] _) ↔ a = b := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  rw [LinearMap.ext_iff] at h
  specialize h 1
  simp_rw [lmul_apply, mul_one] at h
  exact h


-- @@ L876-882 verbatim
lemma isIdempotentElem_algEquiv_iff {R A B : Type*} [CommSemiring R]
  [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B]
  (φ : A ≃ₐ[R] B)
  (a : A) :
  IsIdempotentElem (φ a : B) ↔ IsIdempotentElem a := by
  simp_rw [IsIdempotentElem, ← map_mul, Function.Injective.eq_iff (AlgEquiv.injective _)]


-- @@ L884-890 verbatim
theorem orthogonalProjection'_isProj {R M : Type*} [RCLike R] [NormedAddCommGroup M]
  [InnerProductSpace R M] (U : Submodule R M) [HasOrthogonalProjection U] :
  LinearMap.IsProj U (orthogonalProjection' U) := by
  constructor <;>
  simp only [orthogonalProjection'_eq, coe_comp, Submodule.coe_subtypeL, Submodule.coe_subtype,
    Function.comp_apply, SetLike.coe_mem, implies_true,
    orthogonalProjection_eq_self_iff, imp_self, implies_true]


-- @@ L892-895 verbatim
theorem LinearMap.isProj_iff {S M F : Type*} [Semiring S] [AddCommMonoid M]
    [Module S M] (m : Submodule S M) [FunLike F M M] (f : F) :
  LinearMap.IsProj m f ↔ (∀ x, f x ∈ m) ∧ (∀ x ∈ m, f x = x) :=
⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩


-- @@ L897-900 verbatim
theorem LinearMap.isProj_coe {R M : Type*} [RCLike R] [NormedAddCommGroup M]
  [InnerProductSpace R M] (T : M →L[R] M) (U : Submodule R M) :
  LinearMap.IsProj U T.toLinearMap ↔ LinearMap.IsProj U T :=
by simp_rw [LinearMap.isProj_iff, ContinuousLinearMap.coe_coe]


-- @@ L902-910 verbatim
open LinearMap in
lemma orthogonalProjection_trace {R M :
    Type*} [RCLike R] [NormedAddCommGroup M] [InnerProductSpace R M]
  [FiniteDimensional R M]
  (U : Submodule R M) :
  (trace R M) (orthogonalProjection' U).toLinearMap = Module.finrank R U := by
  refine IsProj.trace ?_
  rw [isProj_coe]
  exact orthogonalProjection'_isProj U


-- @@ L912-929 verbatim
lemma ContinuousLinearMap.eq_comp_orthogonalProjection_ker_ortho
  {𝕜 M₁ M₂ : Type*} [RCLike 𝕜] [NormedAddCommGroup M₁] [InnerProductSpace 𝕜 M₁]
  [NormedAddCommGroup M₂] [InnerProductSpace 𝕜 M₂]
  {T : M₁ →L[𝕜] M₂} [HasOrthogonalProjection T.ker]
  [HasOrthogonalProjection T.range]
  :
  T = T ∘L (orthogonalProjection' (T.ker)ᗮ)
  ∧
  T = (orthogonalProjection' T.range) ∘L T := by
  constructor
  · ext x
    have hx : x - orthogonalProjection' ((T.ker)ᗮ) x ∈ T.ker := by
      simp_all
    have hzero : T (x - orthogonalProjection' ((T.ker)ᗮ) x) = 0 := hx
    rwa [map_sub, sub_eq_zero] at hzero
  · ext x
    exact ((Submodule.starProjection_eq_self_iff (K := T.range)).mpr
      (LinearMap.mem_range_self (T : M₁ →ₗ[𝕜] M₂) x)).symm


-- @@ L931-937 verbatim
theorem orthogonalProjection_of_top {𝕜 E : Type _} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] :
    orthogonalProjection' (⊤ : Submodule 𝕜 E) = 1 := by
  ext1
  simp_rw [one_apply_eq_self, orthogonalProjection'_apply]
  rw [orthogonalProjection_eq_self_iff]
  simp only [Submodule.mem_top]


-- @@ L939-942 verbatim
theorem LinearMap.IsProj.codRestrict_of_top {S M : Type*} [Semiring S] [AddCommMonoid M]
  [Module S M] :
    (Submodule.subtype ⊤).comp (LinearMap.IsProj.top S M).codRestrict = LinearMap.id :=
rfl


-- @@ L944-958 verbatim
theorem LinearMap.IsProj.codRestrict_eq_dim_iff {S M : Type*}
  [Semiring S] [AddCommMonoid M] [Module S M]
  {f : M →ₗ[S] M} {U : Submodule S M} (hf : LinearMap.IsProj U f) :
    U = (⊤ : Submodule S M)
    ↔ (Submodule.subtype _).comp hf.codRestrict = LinearMap.id := by
  rw[LinearMap.IsProj.subtype_comp_codRestrict]
  constructor
  · rintro rfl
    ext
    simp only [id_coe, id_eq, hf.2 _ Submodule.mem_top]
  · rintro rfl
    refine Submodule.eq_top_iff'.mpr ?mpr.a
    intro x
    rw [← id_apply (R := S) x]
    exact hf.map_mem x
