/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Flat.TorsionFree


-- @@ L11-17 verbatim
/-!
# Normal points of codimension at most one are smooth

Let `K` be a field of characteristic zero and `A` a `K`-algebra of finite type. If `q` is a prime
of `A` such that `A_q` is an integrally closed domain of dimension at most one, then `A` is smooth
over `K` at `q` (`Algebra.isSmoothAt_of_ringKrullDim_le_one`).
-/


-- @@ L19-19 verbatim
open TensorProduct IsLocalRing


-- @@ L21-21 verbatim
namespace Algebra


-- @@ L23-23 verbatim
local notation "𝓀[" R "]" => ResidueField R


-- @@ L25-25 verbatim
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]


-- @@ L27-63 verbatim
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **Flat with smooth closed fibre implies smooth.** Let `S` be a finitely presented
`R`-algebra and `q` a prime of `S` over the prime `p` of `R`. If `S_q` is flat over `R_p` and
`κ(p) ⊗[R_p] S_q` is formally smooth over `κ(p)`, then `S` is smooth over `R` at `q`. -/
lemma isSmoothAt_of_flat_of_formallySmooth_residueField_tensor [FinitePresentation R S]
    (p : Ideal R) (q : Ideal S) [p.IsPrime] [q.IsPrime] [q.LiesOver p] :
    letI := Localization.AtPrime.algebraOfLiesOver p q
    Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) →
    FormallySmooth 𝓀[Localization.AtPrime p]
      (𝓀[Localization.AtPrime p] ⊗[Localization.AtPrime p] Localization.AtPrime q) →
    Algebra.IsSmoothAt R q := by
  intro _ _
  let Rp := Localization.AtPrime p
  let Sp := Localization (algebraMapSubmonoid S p.primeCompl)
  let Sq := Localization.AtPrime q
  let := Localization.AtPrime.algebraOfLiesOver p q
  let f : Sp →ₐ[S] Sq := IsLocalization.liftAlgHom (M := algebraMapSubmonoid S p.primeCompl)
        (f := Algebra.ofId _ _) (by
      rintro ⟨_, x, hx, rfl⟩
      simpa using! IsLocalization.map_units (M := q.primeCompl) Sq ⟨algebraMap _ _ x,
        by simp_all [q.over_def p]⟩)
  algebraize [f.toRingHom]
  have : IsScalarTower R Sp Sq := .to₁₃₄ _ S _ _
  have : IsScalarTower Rp Sp Sq := .of_algebraMap_eq' <| by
    apply IsLocalization.ringHom_ext p.primeCompl
    simp only [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
  have : IsLocalization (algebraMapSubmonoid Sp q.primeCompl) Sq :=
    .isLocalization_of_submonoid_le _ _ (algebraMapSubmonoid S p.primeCompl) _
    (by rintro _ ⟨x, hx, rfl⟩; simp_all [q.over_def p])
  have : FinitePresentation Rp Sp := by
    have : Algebra.IsPushout R Rp S Sp :=
      .symm <| Algebra.isPushout_of_isLocalization p.primeCompl _ _ _
    exact .equiv (Algebra.IsPushout.equiv R Rp S Sp)
  have := FormallySmooth.of_formallySmooth_residueField_tensor
    (R := Rp) (S := Sq) (P := Sp) (algebraMapSubmonoid _ q.primeCompl)
  exact .comp R Rp Sq


-- @@ L65-159 verbatim
open Polynomial in
/-- **Normal points of codimension at most one are smooth.** Let `K` be a field of characteristic
zero, `A` a `K`-algebra of finite type and `q` a prime of `A` such that `A_q` is an integrally
closed domain of dimension at most one. Then `A` is smooth over `K` at `q`. -/
theorem isSmoothAt_of_ringKrullDim_le_one {K A : Type*} [Field K] [CharZero K] [CommRing A]
    [Algebra K A] [FiniteType K A] (q : Ideal A) [q.IsPrime] [IsDomain (Localization.AtPrime q)]
    [IsIntegrallyClosed (Localization.AtPrime q)]
    (h : ringKrullDim (Localization.AtPrime q) ≤ 1) : IsSmoothAt K q := by
  let S := Localization.AtPrime q
  haveI : IsNoetherianRing A := FiniteType.isNoetherianRing K A
  by_cases hS : IsField S
  · letI := hS.toField
    exact FormallySmooth.of_perfectField
  -- `A_q` is a discrete valuation ring; choose `a ∈ A` generating its maximal ideal
  haveI : Ring.KrullDimLE 1 S := Ring.krullDimLE_iff.mpr h
  haveI : Ring.DimensionLEOne S :=
    ⟨fun hp hp' ↦ Ring.krullDimLE_one_iff_of_isPrime_bot.mp inferInstance _ hp hp'⟩
  haveI : IsDedekindDomain S := {}
  obtain ⟨ϖ, hϖ⟩ := ((IsDiscreteValuationRing.TFAE S hS).out 2 4).mp ‹IsDedekindDomain S›
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl ϖ
  have hm : maximalIdeal S = Ideal.span {algebraMap A S a} := by
    rw [hϖ, Ideal.submodule_span_eq, IsLocalization.mk'_eq_mul_mk'_one,
      Ideal.span_singleton_mul_right_unit]
    exact IsUnit.of_mul_eq_one (algebraMap A S s) (by rw [IsLocalization.mk'_spec, map_one])
  have ha0 : algebraMap A S a ≠ 0 := fun h0 ↦ hS <| by
    rw [isField_iff_maximalIdeal_eq, hm, h0, Ideal.span_singleton_eq_bot]
  have ha : a ∈ q := by
    rw [← Localization.AtPrime.under_maximalIdeal (I := q), Ideal.mem_comap, hm]
    exact Ideal.subset_span rfl
  -- `A` as an algebra over `K[X]` with `X ↦ a`
  letI : Algebra K[X] A := (aeval a).toAlgebra
  haveI : IsScalarTower K K[X] A := .of_algebraMap_eq fun r ↦ (aeval_C a r).symm
  haveI : FiniteType K[X] A := .of_restrictScalars_finiteType K K[X] A
  haveI : FinitePresentation K[X] A := FinitePresentation.of_finiteType.mp inferInstance
  let p : Ideal K[X] := Ideal.span {X}
  haveI hpm : p.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible irreducible_X
  haveI : q.LiesOver p := by
    refine ⟨hpm.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩
    rw [Ideal.span_le, Set.singleton_subset_iff]
    change aeval a X ∈ q
    rwa [aeval_X]
  letI := Localization.AtPrime.algebraOfLiesOver p q
  let Rp := Localization.AtPrime p
  have hXS : algebraMap K[X] S X = algebraMap A S a := by
    rw [IsScalarTower.algebraMap_apply K[X] A S]
    exact congrArg _ (aeval_X a)
  -- `K[X] → A_q` is injective
  have hinj : Function.Injective (algebraMap K[X] S) := by
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra hne
    haveI : (RingHom.ker (algebraMap K[X] S)).IsPrime := RingHom.ker_isPrime _
    have hle : RingHom.ker (algebraMap K[X] S) ≤ p := by
      intro x hx
      rw [Ideal.LiesOver.over (P := q) (p := p), Ideal.under, Ideal.mem_comap,
        ← Localization.AtPrime.under_maximalIdeal (I := q), Ideal.mem_comap,
        ← IsScalarTower.algebraMap_apply, RingHom.mem_ker.mp hx]
      exact zero_mem _
    have hX : X ∈ RingHom.ker (algebraMap K[X] S) := by
      rw [(Ideal.IsPrime.isMaximal inferInstance hne).eq_of_le hpm.ne_top hle]
      exact Ideal.subset_span rfl
    exact ha0 (hXS ▸ RingHom.mem_ker.mp hX)
  -- `A_q` is flat over `K[X]_(X)`
  have hflat : Module.Flat Rp S := by
    haveI : Module.IsTorsionFree Rp S := by
      rw [Module.isTorsionFree_iff_algebraMap_injective, injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨r, t, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl x
      have e : algebraMap Rp S (IsLocalization.mk' Rp r t) * algebraMap K[X] S t =
          algebraMap K[X] S r := by
        rw [IsScalarTower.algebraMap_apply K[X] Rp S t, IsScalarTower.algebraMap_apply K[X] Rp S r,
          ← map_mul, IsLocalization.mk'_spec]
      rw [hx, zero_mul, eq_comm, ← map_zero (algebraMap K[X] S)] at e
      rw [hinj e, IsLocalization.mk'_zero]
    infer_instance
  -- the closed fibre is the residue field of `A_q`
  have hmap : (maximalIdeal Rp).map (algebraMap Rp S) = maximalIdeal S := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq,
      Ideal.map_span, Set.image_singleton, hXS, hm]
  have hT : IsField (𝓀[Rp] ⊗[Rp] S) := by
    let e : S ⧸ (maximalIdeal Rp).map (algebraMap Rp S) ≃+* 𝓀[Rp] ⊗[Rp] S :=
      (TensorProduct.quotIdealMapEquivTensorQuot S (maximalIdeal Rp)).toRingEquiv.trans
        (TensorProduct.comm Rp S (Rp ⧸ maximalIdeal Rp)).toRingEquiv
    refine e.symm.toMulEquiv.isField ?_
    rw [hmap]
    exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp inferInstance
  letI := hT.toField
  haveI : CharZero 𝓀[Rp] := charZero_of_injective_ringHom
    (f := (algebraMap Rp 𝓀[Rp]).comp ((algebraMap K[X] Rp).comp (C : K →+* K[X])))
    (RingHom.injective _)
  haveI : EssFiniteType K[X] S := .of_comp K K[X] S
  haveI : EssFiniteType Rp S := .of_comp K[X] Rp S
  haveI : IsSmoothAt K[X] q :=
    isSmoothAt_of_flat_of_formallySmooth_residueField_tensor p q hflat
      FormallySmooth.of_perfectField
  exact FormallySmooth.comp K K[X] S


-- @@ L161-168 verbatim
/-- `Algebra.isSmoothAt_of_ringKrullDim_le_one` over a base ring that is a field of characteristic
zero without a chosen `Field` instance. -/
theorem isSmoothAt_of_ringKrullDim_le_one_of_isField {R A : Type*} [CommRing R] [CharZero R]
    (hR : IsField R) [CommRing A] [Algebra R A] [FiniteType R A] (q : Ideal A) [q.IsPrime]
    [IsDomain (Localization.AtPrime q)] [IsIntegrallyClosed (Localization.AtPrime q)]
    (h : ringKrullDim (Localization.AtPrime q) ≤ 1) : IsSmoothAt R q := by
  letI := hR.toField
  exact isSmoothAt_of_ringKrullDim_le_one q h


-- @@ L170-170 verbatim
end Algebra
