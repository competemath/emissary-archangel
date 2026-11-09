module

public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import BernoulliRegular.Reflection.Local.Endpoint


-- @@ L9-15 verbatim
/-!
# First graded piece of the principal-unit filtration

This file begins the REF-10d2 first graded-piece layer.  It constructs the
standard homomorphism from multiplicative principal units to the additive
cotangent space `I / I^2`, sending `u` to `u - 1`, and identifies its kernel.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
open scoped NumberField


-- @@ L23-23 verbatim
namespace BernoulliRegular


-- @@ L25-25 verbatim
namespace Ideal


-- @@ L27-27 verbatim
section OneUnitsCotangent


-- @@ L29-29 verbatim
variable {R : Type*} [CommRing R] (I : Ideal R)


-- @@ L31-51 verbatim
/-- The first graded map on congruence-one units, `u ↦ u - 1 mod I^2`. -/
noncomputable def oneUnitsCotangentHom :
    oneUnitsSubgroup I →* Multiplicative I.Cotangent where
  toFun u := Multiplicative.ofAdd (I.toCotangent ⟨(u : Rˣ) - 1, u.2⟩)
  map_one' := by
    rw [← ofAdd_zero]
    apply congrArg Multiplicative.ofAdd
    rw [I.toCotangent_eq_zero]
    simp
  map_mul' u v := by
    rw [← ofAdd_add]
    apply congrArg Multiplicative.ofAdd
    rw [← map_add]
    rw [I.toCotangent_eq]
    change (((((u : oneUnitsSubgroup I) : Rˣ) * ((v : oneUnitsSubgroup I) : Rˣ) : Rˣ) :
        R) - 1 - (((u : Rˣ) : R) - 1 + (((v : Rˣ) : R) - 1)) ∈ I ^ 2)
    have hprod : (((u : Rˣ) : R) - 1) * (((v : Rˣ) : R) - 1) ∈ I ^ 2 := by
      simpa [pow_two] using Ideal.mul_mem_mul u.2 v.2
    convert hprod using 1
    simp [Units.val_mul]
    ring


-- @@ L53-57 verbatim
@[simp]
theorem oneUnitsCotangentHom_apply (u : oneUnitsSubgroup I) :
    oneUnitsCotangentHom I u =
      Multiplicative.ofAdd (I.toCotangent ⟨(u : Rˣ) - 1, u.2⟩) :=
  rfl


-- @@ L59-70 verbatim
theorem mem_oneUnitsCotangentHom_ker {u : oneUnitsSubgroup I} :
    u ∈ (oneUnitsCotangentHom I).ker ↔ ((u : Rˣ) : R) - 1 ∈ I ^ 2 := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have hzero : I.toCotangent ⟨((u : Rˣ) : R) - 1, u.2⟩ = 0 :=
      Multiplicative.ofAdd.injective (by simpa [oneUnitsCotangentHom] using h)
    exact (I.toCotangent_eq_zero _).mp hzero
  · intro h
    have hzero : I.toCotangent ⟨((u : Rˣ) : R) - 1, u.2⟩ = 0 :=
      (I.toCotangent_eq_zero _).mpr h
    simp [oneUnitsCotangentHom, hzero]


-- @@ L72-76 verbatim
theorem oneUnitsCotangentHom_ker :
    (oneUnitsCotangentHom I).ker = (oneUnitsSubgroup (I ^ 2)).subgroupOf (oneUnitsSubgroup I) := by
  ext u
  rw [mem_oneUnitsCotangentHom_ker, Subgroup.mem_subgroupOf]
  rfl


-- @@ L78-78 verbatim
end OneUnitsCotangent


-- @@ L80-80 verbatim
end Ideal


-- @@ L82-82 verbatim
namespace Reflection

-- @@ L83-83 verbatim
namespace Local


-- @@ L85-85 verbatim
section CyclotomicSetup


-- @@ L87-88 verbatim
variable (p : ℕ) [Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]


-- @@ L90-93 verbatim
/-- The localized uniformizer `zeta_p - 1` at `lambda`. -/
noncomputable def localCyclotomicUniformizer : localCyclotomicRing p K :=
  algebraMap (𝓞 K) (localCyclotomicRing p K)
    ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger - 1)


-- @@ L95-98 verbatim
theorem localCyclotomicMaximalIdeal_eq_span_uniformizer :
    localCyclotomicMaximalIdeal p K = Ideal.span {localCyclotomicUniformizer p K} := by
  rw [← localCyclotomicMaximalIdeal_eq_map p K]
  simp [localCyclotomicUniformizer, cyclotomicLambda, zetaPrime, Ideal.map_span]


-- @@ L100-104 verbatim
theorem localCyclotomicMaximalIdeal_isPrincipal :
    Submodule.IsPrincipal (localCyclotomicMaximalIdeal p K) := by
  rw [localCyclotomicMaximalIdeal_eq_span_uniformizer]
  rw [Submodule.isPrincipal_iff]
  exact ⟨localCyclotomicUniformizer p K, rfl⟩


-- @@ L106-113 verbatim
theorem localCyclotomicMaximalIdeal_ne_bot :
    localCyclotomicMaximalIdeal p K ≠ ⊥ := by
  intro h
  have hcomap := congrArg (Ideal.comap (algebraMap (𝓞 K) (localCyclotomicRing p K))) h
  rw [localCyclotomicMaximalIdeal_comap] at hcomap
  have hbot : cyclotomicLambda p K = ⊥ := by
    simpa using hcomap
  exact zetaPrime_ne_bot p K (by simpa [cyclotomicLambda] using hbot)


-- @@ L115-119 verbatim
/-- The global cyclotomic prime `lambda` is maximal. -/
theorem cyclotomicLambda_isMaximal :
    (cyclotomicLambda p K).IsMaximal := by
  simpa [cyclotomicLambda] using
    (Ideal.IsPrime.isMaximal (zetaPrime_isPrime p K) (zetaPrime_ne_bot p K))


-- @@ L121-132 verbatim
/-- The global residue ring at `lambda` has cardinality `p`. -/
theorem globalCyclotomicResidueCard :
    Nat.card (𝓞 K ⧸ cyclotomicLambda p K) = p := by
  haveI : IsCyclotomicExtension {p ^ (0 + 1)} ℚ K := by
    simpa using (inferInstance : IsCyclotomicExtension {p} ℚ K)
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) (p ^ (0 + 1)) := by
    simp
  have hAbs : Ideal.absNorm (cyclotomicLambda p K) = p := by
    simpa [cyclotomicLambda, zetaPrime] using
      (IsCyclotomicExtension.Rat.absNorm_span_zeta_sub_one p 0 hζ)
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hAbs
  exact hAbs


-- @@ L134-145 verbatim
/-- The local residue ring at `lambda` has cardinality `p`. -/
theorem localCyclotomicResidueCard :
    Nat.card (localCyclotomicRing p K ⧸ localCyclotomicMaximalIdeal p K) = p := by
  letI : (cyclotomicLambda p K).IsMaximal := cyclotomicLambda_isMaximal (p := p) (K := K)
  have hlocal_global :
      Nat.card (localCyclotomicRing p K ⧸ localCyclotomicMaximalIdeal p K) =
        Nat.card (𝓞 K ⧸ cyclotomicLambda p K) := by
    have hbij := Ideal.bijective_algebraMap_quotient_residueField (cyclotomicLambda p K)
    exact (Nat.card_congr (Equiv.ofBijective
      (algebraMap (𝓞 K ⧸ cyclotomicLambda p K)
        ((cyclotomicLambda p K).ResidueField)) hbij)).symm
  exact hlocal_global.trans (globalCyclotomicResidueCard (p := p) (K := K))


-- @@ L147-156 verbatim
/-- Since the local maximal ideal is principal, its first graded quotient is the residue ring. -/
noncomputable def localCotangentPowOneLinearEquivResidue :
    (localCyclotomicRing p K ⧸ localCyclotomicMaximalIdeal p K) ≃ₗ[localCyclotomicRing p K]
      (localCyclotomicMaximalIdeal p K ^ 1 : Ideal (localCyclotomicRing p K)) ⧸
        localCyclotomicMaximalIdeal p K •
          (⊤ : Submodule (localCyclotomicRing p K)
            (localCyclotomicMaximalIdeal p K ^ 1 : Ideal (localCyclotomicRing p K))) :=
  Ideal.quotEquivPowQuotPowSucc
    (localCyclotomicMaximalIdeal_isPrincipal (p := p) (K := K))
    (localCyclotomicMaximalIdeal_ne_bot (p := p) (K := K)) 1


-- @@ L158-164 verbatim
theorem localCotangentPowOneQuotientCard :
    Nat.card ((localCyclotomicMaximalIdeal p K ^ 1 : Ideal (localCyclotomicRing p K)) ⧸
      localCyclotomicMaximalIdeal p K •
        (⊤ : Submodule (localCyclotomicRing p K)
          (localCyclotomicMaximalIdeal p K ^ 1 : Ideal (localCyclotomicRing p K)))) = p :=
  (Nat.card_congr (localCotangentPowOneLinearEquivResidue (p := p) (K := K)).toEquiv).symm.trans
    (localCyclotomicResidueCard (p := p) (K := K))


-- @@ L166-178 verbatim
/-- Since `m ^ 1 = m`, the raw first-power quotient is the cotangent space. -/
noncomputable def localCotangentLinearEquivPowOneQuotient :
    (localCyclotomicMaximalIdeal p K).Cotangent ≃ₗ[localCyclotomicRing p K]
      ((localCyclotomicMaximalIdeal p K ^ 1 : Ideal (localCyclotomicRing p K)) ⧸
        localCyclotomicMaximalIdeal p K •
          (⊤ : Submodule (localCyclotomicRing p K)
            (localCyclotomicMaximalIdeal p K ^ 1 : Ideal (localCyclotomicRing p K)))) := by
  let R := localCyclotomicRing p K
  let M := localCyclotomicMaximalIdeal p K
  change M.Cotangent ≃ₗ[R] ((M ^ 1 : Ideal R) ⧸ M •
    (⊤ : Submodule R (M ^ 1 : Ideal R)))
  rw [pow_one]
  exact LinearEquiv.refl R M.Cotangent


-- @@ L180-189 verbatim
theorem localCotangentCard :
    Nat.card (localCyclotomicMaximalIdeal p K).Cotangent = p := by
  calc
    Nat.card (localCyclotomicMaximalIdeal p K).Cotangent =
        Nat.card ((localCyclotomicMaximalIdeal p K ^ 1 : Ideal (localCyclotomicRing p K)) ⧸
          localCyclotomicMaximalIdeal p K •
            (⊤ : Submodule (localCyclotomicRing p K)
              (localCyclotomicMaximalIdeal p K ^ 1 : Ideal (localCyclotomicRing p K)))) :=
      Nat.card_congr (localCotangentLinearEquivPowOneQuotient (p := p) (K := K)).toEquiv
    _ = p := localCotangentPowOneQuotientCard (p := p) (K := K)


-- @@ L191-194 verbatim
theorem localCotangentMultiplicativeCard :
    Nat.card (Multiplicative (localCyclotomicMaximalIdeal p K).Cotangent) = p :=
  (Nat.card_congr Multiplicative.toAdd).trans
    (localCotangentCard (p := p) (K := K))


-- @@ L196-210 verbatim
/-- The first graded map `U_1 -> m/m^2`, sending `u` to `u - 1`. -/
noncomputable def principalUnitFirstGradedHom :
    principalUnitSubgroup p K 1 →*
      Multiplicative (localCyclotomicMaximalIdeal p K).Cotangent :=
  let M := localCyclotomicMaximalIdeal p K
  let toOneUnits : principalUnitSubgroup p K 1 →* Ideal.oneUnitsSubgroup M :=
  {
    toFun := fun u ↦ ⟨(u : localCyclotomicUnitGroup p K), by
      have hu := (mem_principalUnitSubgroup_iff (p := p) (K := K) (n := 1)
        (u := (u : localCyclotomicUnitGroup p K))).mp u.2
      simpa [M] using hu⟩
    map_one' := rfl
    map_mul' := fun _ _ ↦ rfl
  }
  (Ideal.oneUnitsCotangentHom M).comp toOneUnits


-- @@ L212-231 verbatim
/-- The kernel of `U_1 -> m/m^2` is `U_2`. -/
theorem mem_principalUnitFirstGradedHom_ker {u : principalUnitSubgroup p K 1} :
    u ∈ (principalUnitFirstGradedHom p K).ker ↔
      (u : localCyclotomicUnitGroup p K) ∈ principalUnitSubgroup p K 2 := by
  let M := localCyclotomicMaximalIdeal p K
  change (⟨(u : localCyclotomicUnitGroup p K), by
      have hu := (mem_principalUnitSubgroup_iff (p := p) (K := K) (n := 1)
        (u := (u : localCyclotomicUnitGroup p K))).mp u.2
      simpa [M] using hu⟩ : Ideal.oneUnitsSubgroup M) ∈
        (Ideal.oneUnitsCotangentHom M).ker ↔
      (u : localCyclotomicUnitGroup p K) ∈ principalUnitSubgroup p K 2
  rw [Ideal.mem_oneUnitsCotangentHom_ker]
  constructor
  · intro h
    rw [mem_principalUnitSubgroup_iff]
    simpa [M] using h
  · intro h
    have hmem := (mem_principalUnitSubgroup_iff (p := p) (K := K) (n := 2)
      (u := (u : localCyclotomicUnitGroup p K))).mp h
    simpa [M] using hmem


-- @@ L233-238 verbatim
theorem principalUnitFirstGradedHom_ker :
    (principalUnitFirstGradedHom p K).ker =
      (principalUnitSubgroup p K 2).subgroupOf (principalUnitSubgroup p K 1) := by
  ext u
  rw [mem_principalUnitFirstGradedHom_ker]
  rw [Subgroup.mem_subgroupOf]


-- @@ L240-272 verbatim
theorem principalUnitFirstGradedHom_surjective :
    Function.Surjective (principalUnitFirstGradedHom p K) := by
  intro y
  let R := localCyclotomicRing p K
  let M := localCyclotomicMaximalIdeal p K
  obtain ⟨x, hx⟩ := M.toCotangent_surjective (Multiplicative.toAdd y)
  have hunit : IsUnit (1 + (x : R)) := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hmem
    have hone : (1 : R) ∈ M := by
      have hxmem : (x : R) ∈ M := x.2
      have hsub : (1 + (x : R)) - (x : R) ∈ M := M.sub_mem hmem hxmem
      simpa using hsub
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top
      ((Ideal.eq_top_iff_one M).2 hone)
  let u0 : localCyclotomicUnitGroup p K := hunit.unit
  have hu0_val : (u0 : R) = 1 + (x : R) := hunit.unit_spec
  have hu1 : u0 ∈ principalUnitSubgroup p K 1 := by
    rw [mem_principalUnitSubgroup_iff]
    change (u0 : R) - 1 ∈ M ^ 1
    rw [hu0_val, add_sub_cancel_left, pow_one]
    exact x.2
  refine ⟨⟨u0, hu1⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  change M.toCotangent ⟨(u0 : R) - 1, by
      have hu := (mem_principalUnitSubgroup_iff (p := p) (K := K) (n := 1)
        (u := u0)).mp hu1
      rw [← pow_one M]
      exact hu⟩ = Multiplicative.toAdd y
  rw [← hx]
  apply congrArg M.toCotangent
  ext
  simp [hu0_val]


-- @@ L274-278 verbatim
/-- The localized cyclotomic root, viewed as an element of `U_1`. -/
noncomputable def localCyclotomicZetaPrincipalUnit :
    principalUnitSubgroup p K 1 :=
  ⟨localCyclotomicZetaUnit p K,
    localCyclotomicZetaUnit_mem_principalUnitSubgroup_one (p := p) (K := K)⟩


-- @@ L280-283 verbatim
@[simp]
theorem localCyclotomicZetaPrincipalUnit_pow_eq_one :
    localCyclotomicZetaPrincipalUnit p K ^ p = 1 :=
  Subtype.ext (localCyclotomicZetaUnit_pow_eq_one p K)


-- @@ L285-296 verbatim
theorem principalUnitFirstGradedHom_zeta_ne_one :
    principalUnitFirstGradedHom p K (localCyclotomicZetaPrincipalUnit p K) ≠ 1 := by
  intro h
  have hker : localCyclotomicZetaPrincipalUnit p K ∈
      (principalUnitFirstGradedHom p K).ker := by
    rw [MonoidHom.mem_ker]
    exact h
  have hzeta_mem_two :
      localCyclotomicZetaUnit p K ∈ principalUnitSubgroup p K 2 :=
    (mem_principalUnitFirstGradedHom_ker (p := p) (K := K)).mp hker
  exact localCyclotomicZetaUnit_not_mem_principalUnitSubgroup_two (p := p) (K := K)
    hzeta_mem_two


-- @@ L298-304 verbatim
theorem principalUnitFirstGradedHom_zeta_orderOf :
    orderOf (principalUnitFirstGradedHom p K (localCyclotomicZetaPrincipalUnit p K)) = p :=
  orderOf_eq_prime
    (by
      rw [← map_pow]
      simp)
    (principalUnitFirstGradedHom_zeta_ne_one (p := p) (K := K))


-- @@ L306-311 verbatim
theorem principalUnitFirstGradedHom_zeta_zpowers_eq_top :
    Subgroup.zpowers
      (principalUnitFirstGradedHom p K (localCyclotomicZetaPrincipalUnit p K)) = ⊤ :=
  zpowers_eq_top_of_prime_card
    (localCotangentMultiplicativeCard (p := p) (K := K))
    (principalUnitFirstGradedHom_zeta_ne_one (p := p) (K := K))


-- @@ L313-339 verbatim
theorem principalUnitSubgroup_one_le_endpointSubgroup :
    principalUnitSubgroup p K 1 ≤ localCyclotomicEndpointSubgroup p K := by
  intro u hu
  let U1 := principalUnitSubgroup p K 1
  let z : U1 := localCyclotomicZetaPrincipalUnit p K
  let f := principalUnitFirstGradedHom p K
  have htop : Subgroup.zpowers (f z) = ⊤ := by
    simpa [f, z] using principalUnitFirstGradedHom_zeta_zpowers_eq_top (p := p) (K := K)
  have hmem : f ⟨u, hu⟩ ∈ Subgroup.zpowers (f z) := by
    rw [htop]
    exact Subgroup.mem_top _
  rcases Subgroup.mem_zpowers_iff.mp hmem with ⟨k, hk⟩
  have hker : (z ^ k)⁻¹ * (⟨u, hu⟩ : U1) ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow, hk, inv_mul_cancel]
  have hU2 : ((((z ^ k)⁻¹ * (⟨u, hu⟩ : U1)) : U1) :
      localCyclotomicUnitGroup p K) ∈ principalUnitSubgroup p K 2 :=
    (mem_principalUnitFirstGradedHom_ker (p := p) (K := K)).mp hker
  rw [localCyclotomicEndpointSubgroup, Subgroup.mem_sup]
  refine ⟨((z ^ k : U1) : localCyclotomicUnitGroup p K), ?_,
    ((((z ^ k)⁻¹ * (⟨u, hu⟩ : U1)) : U1) : localCyclotomicUnitGroup p K), hU2, ?_⟩
  · rw [localCyclotomicMuP]
    change ((localCyclotomicZetaUnit p K) ^ k) ∈
      Subgroup.zpowers (localCyclotomicZetaUnit p K)
    exact Subgroup.zpow_mem_zpowers _ _
  · change ((z ^ k : U1) : localCyclotomicUnitGroup p K) *
        ((((z ^ k)⁻¹ * (⟨u, hu⟩ : U1)) : U1) : localCyclotomicUnitGroup p K) = u
    simp


-- @@ L341-345 verbatim
theorem principalUnitSubgroup_one_eq_endpointSubgroup :
    principalUnitSubgroup p K 1 = localCyclotomicEndpointSubgroup p K :=
  le_antisymm
    (principalUnitSubgroup_one_le_endpointSubgroup (p := p) (K := K))
    (localCyclotomicEndpointSubgroup_le_principalUnitSubgroup_one (p := p) (K := K))


-- @@ L347-351 verbatim
/-- The formal endpoint inclusion `U_1^p <= U_{p+1}` after `U_1 = mu_p * U_2`. -/
theorem principalUnitPowerSubgroup_one_le_p_add_one :
    principalUnitPowerSubgroup p K p 1 ≤ principalUnitSubgroup p K (p + 1) :=
  principalUnitPowerSubgroup_one_le_p_add_one_of_endpoint_eq
    (p := p) (K := K) (principalUnitSubgroup_one_eq_endpointSubgroup (p := p) (K := K))


-- @@ L353-357 verbatim
theorem pow_mem_principalUnitSubgroup_p_add_one_of_mem_one
    {u : localCyclotomicUnitGroup p K}
    (hu : u ∈ principalUnitSubgroup p K 1) :
    u ^ p ∈ principalUnitSubgroup p K (p + 1) :=
  principalUnitPowerSubgroup_one_le_p_add_one (p := p) (K := K) ⟨u, hu, rfl⟩


-- @@ L359-362 verbatim
theorem principalUnitPowerSubgroup_one_eq_p_add_one_of_le
    (h : principalUnitSubgroup p K (p + 1) ≤ principalUnitPowerSubgroup p K p 1) :
    principalUnitPowerSubgroup p K p 1 = principalUnitSubgroup p K (p + 1) :=
  le_antisymm (principalUnitPowerSubgroup_one_le_p_add_one (p := p) (K := K)) h


-- @@ L364-364 verbatim
end CyclotomicSetup


-- @@ L366-366 verbatim
end Local

-- @@ L367-367 verbatim
end Reflection

-- @@ L368-368 verbatim
end BernoulliRegular
