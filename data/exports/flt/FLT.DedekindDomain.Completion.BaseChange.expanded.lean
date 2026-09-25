/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Andrew Yang, Matthew Jasper
-/
module

public import FLT.DedekindDomain.AdicValuation
public import FLT.DedekindDomain.IntegralClosure
public import FLT.Mathlib.Algebra.Algebra.Bilinear
public import FLT.Mathlib.Algebra.Algebra.Pi
public import FLT.Mathlib.Algebra.Module.Submodule.Basic
public import FLT.Mathlib.Topology.Algebra.Module.ModuleTopology
public import FLT.Mathlib.Topology.Algebra.UniformRing
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Valuation.Discrete.RankOne
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import FLT.Mathlib.RingTheory.TensorProduct.Basis
public import FLT.Mathlib.RingTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import FLT.Mathlib.RingTheory.DedekindDomain.AdicValuation


-- @@ L25-47 verbatim
/-!

# Base change of adic completions.

If `A` is a Dedekind domain with field of fractions `K`, if `L/K` is a finite extension
and if `B/A` is also finite then `L ⊗_K K_v ≅ ∏_{w|v} L_w` as `L`-algebras. Further this
map is continuous, `K_v`-linear and restricts to an isomorphism `B ⊗_A 𝓞_v ≅ ∏_{w|v} 𝓞_w`.

## Main definitions

* `IsDedekindDomain.HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv` :
   `L ⊗[K] K_v ≃A[L] ∏_{w|v} L_w`

## Main theorems

* `IsDedekindDomain.HeightOneSpectrum.Extension.valued_adicCompletionSemialgHom A K L B v w pf` :
  If w|v are nonzero primes of B and A, and if x ∈ K_v ⊆ L_w, then w(x)=v(x)^e
  where e is the global ramification index of w/v.

* `IsDedekindDomain.HeightOneSpectrum.adicCompletion.baseChange_bijective A K L B v` :
  The canonical map L ⊗ Kᵥ → ∏_{w|v} L_w is bijective.

-/


-- @@ L49-49 verbatim
@[expose] public section


-- @@ L51-51 verbatim
open scoped WithZero Valued TensorProduct

-- @@ L52-52 verbatim
open Valuation.IsRankOneDiscrete WithZero


-- @@ L54-59 verbatim
/-!

The general "AKLB" set-up. `K` is the field of fractions of the Dedekind domain `A`,
`L/K` is a finite separable extension, and `B` is the integral closure of `A` in `L`.

-/


-- @@ L61-63 verbatim
variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]


-- @@ L65-65 verbatim
section assumptions


-- @@ L67-67 verbatim
variable [IsIntegralClosure B A L] [FiniteDimensional K L]


-- @@ L69-83 verbatim
/-!

Under these hypotheses and `[Algebra.IsSeparable K L]`, we can prove the following:

`[IsDomain B]`
`[Algebra.IsIntegral A B]`
`[Module.Finite A B]`
`[IsDedekindDomain B]`
`[IsFractionRing B L]`

However none of these facts are available to typeclass inference because they all use
variables such as `K` which are not mentioned in the statement so are unfindable by
Lean 4's typeclass system. We thus introduce them as variables when needed.

-/

-- @@ L84-87 verbatim
example : IsDomain B := by
  have foo : Function.Injective (algebraMap B L) := IsIntegralClosure.algebraMap_injective B A _
  have bar : IsDomain L := inferInstance
  exact Function.Injective.isDomain _ foo -- exact? failed


-- @@ L89-89 verbatim
example : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A L


-- @@ L91-92 verbatim
example [IsDomain B] [Algebra.IsSeparable K L] : IsDedekindDomain B :=
  IsIntegralClosure.isDedekindDomain A K L B


-- @@ L94-95 verbatim
example [IsDedekindDomain B] : IsFractionRing B L :=
  IsIntegralClosure.isFractionRing_of_finite_extension A K L B


-- @@ L97-100 verbatim
example [Algebra.IsSeparable K L] : Module.Finite A B :=
  have := IsIntegralClosure.isNoetherian A K L B
  Module.IsNoetherian.finite A B
-- variable [Module.Finite A B] -- we'll need this later


-- @@ L102-103 verbatim
example : FaithfulSMul A B := FaithfulSMul.of_field_isFractionRing A B K L
-- variable [FaithfulSMul A B] -- we'll need this later


-- @@ L105-105 verbatim
end assumptions


-- @@ L107-107 verbatim
variable [Algebra.IsIntegral A B] [IsFractionRing B L] [IsDedekindDomain B]


-- @@ L109-109 verbatim
namespace IsDedekindDomain.HeightOneSpectrum


-- @@ L111-111 verbatim
variable (v : HeightOneSpectrum A) {A B}


-- @@ L113-123 verbatim
/--
If we have an AKLB set-up, and `w` is a valuation on `L` extending `v` on `K`,
then `σ v w` is the ring homomorphism from (K with valuation v) to (L with valuation w).
More precisely, by (K with valuation v) we mean the
type synonym `WithVal (HeightOneSpectrum.valuation K v)`, which is `K` equipped with
the instance `Valued K Γ₀` coming from `v`. In particular this type synonym has
a canonical valuation, topology, and uniform addive group structure. It is shown
that `σ v w` is continuous.
-/
local notation "σ" => fun v w => algebraMap (WithVal (HeightOneSpectrum.valuation K v))
    (WithVal (HeightOneSpectrum.valuation L w))


-- @@ L125-164 verbatim
lemma adicValued.continuous_algebraMap
   (w : HeightOneSpectrum B) (hvw : w.under A = v) :
    Continuous (σ v w) := by
  refine continuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_iff
    (Valued.hasBasis_nhds_zero _ _)]
  intro γL _
  let e := w.asIdeal.ramificationIdx A
  -- push `γL` to `ℤᵐ⁰`
  let σL := WithVal.valueGroupOrderIso₀ (w.valuation L)
  let σw := valueGroup₀_equiv_withZeroMulInt (w.valuation L)
  let m : ℤᵐ⁰ := σw (σL γL)
  -- `ℤᵐ⁰` values in `K` exponentiate by `e` in `L` so take the `e`th root and pull back to `γK`
  let σv := valueGroup₀_equiv_withZeroMulInt (v.valuation K)
  let σK := (WithVal.valueGroupOrderIso₀ (v.valuation K))
  let γK := σK.symm (σv.symm (exp (m.log / e)))
  have hγK : γK ≠ 0 := by simp [γK]
  use .mk0 _ hγK
  simp only [Units.val_mk0, Set.mem_ofPred_eq, true_and]
  intro x hx
  rcases eq_or_ne x 0 with rfl | hx₀; · simp
  rw [σK.lt_symm_apply, ← (valueGroup₀_equiv_withZeroMulInt_strictMono _).lt_iff_lt] at hx
  -- `change` needed after bump to mathlib#34045
  change (valueGroup₀_equiv_withZeroMulInt (valuation K v))
    (σK ((WithVal.valuation (valuation K v)).restrict x)) < _ at hx
  rw [WithVal.valueGroupOrderIso₀_restrict,
    valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective (v.valuation_surjective K),
    OrderMonoidIso.apply_symm_apply, ← log_lt_log (by simp_all) (by simp)] at hx
  rw [← σL.strictMono.lt_iff_lt]
  -- `change` needed after bump to mathlib#34045
  change σL ((WithVal.valuation (w.valuation L)).restrict ((algebraMap (WithVal (valuation K v))
    (WithVal (valuation L w))) x)) < _
  rw [WithVal.valueGroupOrderIso₀_restrict,
    ← (valueGroup₀_equiv_withZeroMulInt_strictMono _).lt_iff_lt,
    valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective (w.valuation_surjective L),
    WithVal.algebraMap_left_apply, WithVal.algebraMap_right_apply, ← valuation_comap A,
    ← log_lt_log (by simp_all) (by simp), log_pow, nsmul_eq_mul, mul_comm]
  subst hvw
  apply Int.mul_lt_of_lt_ediv (mod_cast pos_of_ne_zero (ramificationIdx_ne_zero A B
    (algebraMap_injective_of_field_isFractionRing A B K L) w)) hx


-- @@ L166-166 verbatim
namespace Extension


-- @@ L168-168 verbatim
variable {v} (w : v.Extension B)


-- @@ L170-178 expanded
/-- The map `(R,v) → (S,w)` as a semialgebra map over `R → S` (which is the same map!). -/
@[simps!]
def _root_.WithVal.semialgebraMap {R S Γ₀ Γ₀' : Type*} [CommRing R] [CommRing S]
    [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₀'] [Algebra R S]
    (v : Valuation R Γ₀) (w : Valuation S Γ₀') : SemialgHom (algebraMap R S) (WithVal v) (WithVal w)
    where
  __ := algebraMap (WithVal v) (WithVal w)
  map_smul' r
    x := by simp [WithVal.algebraMap_left_apply, WithVal.algebraMap_right_apply, Algebra.smul_def]


-- @@ L180-188 expanded
/-- If w of L divides v of K, `underSemialgHom v w pf` is the canonical map `Kᵥ → L_w` lying
above `K → L`. Here we actually use the type synonyms `WithVal K` and `WithVal L`. -/
noncomputable def adicCompletionSemialgHom :
    SemialgHom (algebraMap K L) (v.adicCompletion K) (w.1.adicCompletion L) :=
  ((adicCompletion.algEquiv L w.1).symm.toAlgHom.toSemialgHom).comp <|
    (((WithVal.semialgebraMap (v.valuation K) (w.1.valuation L)).restrictScalars <|
          UniformSpace.Completion.mapSemialgHom _ <|
            adicValued.continuous_algebraMap K L v w.1 w.2).comp
      (adicCompletion.algEquiv K v).toAlgHom.toSemialgHom)


-- @@ L190-193 verbatim
/-- The square with sides K → K_v → L_w and K → L → L_w commutes. -/
lemma adicCompletionSemialgHom_coe (x : WithVal (v.valuation K)) :
    w.adicCompletionSemialgHom K L x = algebraMap K L x.ofVal :=
  (w.adicCompletionSemialgHom K L).commutes _


-- @@ L195-198 verbatim
/-- The map K_v → L_w is continuous. -/
lemma adicCompletionSemialgHom_continuous : Continuous (w.adicCompletionSemialgHom K L) :=
  (adicCompletion.continuous_ofCompletion L w.1).comp
    (UniformSpace.Completion.continuous_map.comp (adicCompletion.continuous_toCompletion K v))


-- @@ L200-224 verbatim
open WithZeroTopology in
/--
The local ramification index for the extension L_w/K_v is equal to the global ramification
index for the extension w/v. In other words, if x in K_v and i:K_v->L_w then w(i(x))=v(x)^e
where e is computed globally.
-/
lemma valued_adicCompletionSemialgHom (x) :
    Valued.v (adicCompletionSemialgHom K L w x) = Valued.v x ^
      w.1.asIdeal.ramificationIdx A := by
  revert x
  apply funext_iff.mp
  symm
  apply (adicCompletion.ofCompletion_surjective K v).injective_comp_right
  apply UniformSpace.Completion.ext
  · exact ((Valued.continuous_valuation_of_surjective
      (v.valuedAdicCompletion_surjective K)).pow _).comp
      (adicCompletion.continuous_ofCompletion K v)
  · exact ((Valued.continuous_valuation_of_surjective (w.1.valuedAdicCompletion_surjective L)).comp
      (adicCompletionSemialgHom_continuous K L w)).comp
      (adicCompletion.continuous_ofCompletion K v)
  intro a
  simp only [Function.comp_apply, adicCompletion.valued_ofCompletion,
    Valued.valuedCompletion_apply, w.2, adicCompletionSemialgHom_coe,
    WithVal.equiv_symm_apply, WithVal.valued_toVal, ← valuation_comap A K L B w.1 _]
  rw [WithVal.valued_toVal]


-- @@ L226-234 verbatim
/-- The canonical map K_v → L_w sends 𝓞_v to 𝓞_w. -/
lemma adicCompletionSemialgHom_image_adicCompletionIntegers :
    w.adicCompletionSemialgHom K L '' (v.adicCompletionIntegers K) ⊆
      w.1.adicCompletionIntegers L := by
  rintro y ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, mem_adicCompletionIntegers] at hx ⊢
  rw [w.valued_adicCompletionSemialgHom K L]
  rwa [pow_le_one_iff]
  exact ramificationIdx_ne_zero A B (algebraMap_injective_of_field_isFractionRing A B K L) w.1


-- @@ L236-239 verbatim
/-- The K_v-algebra structure on L_w when w | v. -/
noncomputable
instance : Algebra (v.adicCompletion K) (w.1.adicCompletion L) :=
  (w.adicCompletionSemialgHom K L).toAlgebra


-- @@ L241-245 verbatim
/-- The K_v-action on L_w is continuous. -/
instance : ContinuousSMul (adicCompletion K v) (adicCompletion L w.1) := by
  constructor
  have leftCts := w.adicCompletionSemialgHom_continuous K L
  exact Continuous.mul (Continuous.fst' leftCts) continuous_snd


-- @@ L247-247 verbatim
end Extension


-- @@ L249-249 verbatim
namespace adicCompletion


-- @@ L251-251 verbatim
variable (B)


-- @@ L253-256 expanded
/-- The canonical map `K_v → ∏_{w|v} L_w` extending K → L. -/
noncomputable def semialgHomPi :
    SemialgHom (algebraMap K L) (v.adicCompletion K) (∀ w : v.Extension B, w.1.adicCompletion L) :=
  Pi.semialgHom _ _ fun i ↦ i.adicCompletionSemialgHom K L


-- @@ L258-261 verbatim
/-- The canonical ring homomorphism `L ⊗_K K_v → ∏_{w|v} L_w` as an `L`-algebra map. -/
noncomputable abbrev baseChange :
    L ⊗[K] adicCompletion K v →ₐ[L] Π w : v.Extension B, w.1.adicCompletion L :=
  (semialgHomPi K L B v).baseChangeOfAlgebraMap


-- @@ L263-264 verbatim
lemma baseChange_tmul_apply (x y w) : baseChange K L B v (x ⊗ₜ y) w =
    (algebraMap _ (w.1.adicCompletion L) x) * (algebraMap _ (w.1.adicCompletion L) y) := rfl


-- @@ L266-270 verbatim
open scoped TensorProduct.RightActions in
/-- The canonical ring homomorphism `L ⊗_K K_v → ∏_{w|v} L_w` as an `K_v`-linear map. -/
noncomputable abbrev baseChangeRight :
    L ⊗[K] adicCompletion K v →ₐ[adicCompletion K v] Π w : v.Extension B, w.1.adicCompletion L :=
  (semialgHomPi K L B v).baseChangeRightOfAlgebraMap


-- @@ L272-272 verbatim
section ModuleTopology


-- @@ L274-292 verbatim
open WithZeroMulInt Valued in
-- Make (v.adicCompletion K) a normed field.
-- This exists for number fields in Mathlib, but not for general Dedekind Domains.
-- v.asIdeal.absNorm may be 0, so just use 2 as the base for the norm.
/-- The data of a rank 1 (ℝ-valued) valuation on K_v. -/
noncomputable local instance :
    Valuation.RankOne (Valued.v : Valuation (adicCompletion K v) ℤᵐ⁰) where
  hom' := (toNNReal (by norm_num : (2 : NNReal) ≠ 0)).comp
    (valueGroup₀_equiv_withZeroMulInt _).toMonoidWithZeroHom
  strictMono' := toNNReal_strictMono (by norm_num) |>.comp
    (by simpa using! valueGroup₀_equiv_withZeroMulInt_strictMono _)
  exists_val_nontrivial := by
    obtain ⟨x, hx1, hx2⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    use algebraMap A K x
    rw [valuedAdicCompletion_eq_valuation' v (algebraMap A K x)]
    constructor
    · simpa only [ne_eq, map_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff]
    · apply ne_of_lt
      rwa [valuation_of_algebraMap, intValuation_lt_one_iff_mem]


-- @@ L294-312 verbatim
set_option backward.isDefEq.respectTransparency false in
open scoped TensorProduct.RightActions in
/-- The canonical map `L ⊗[K] K_v → ∏_{w|v} L_w` is surjective. -/
lemma baseChangeRight_surjective [FiniteDimensional K L] :
    Function.Surjective (baseChangeRight K L B v) := by
  let s := (baseChangeRight K L B v).toLinearMap.range
  have isClosed : IsClosed s.carrier :=
    Submodule.closed_of_finiteDimensional (E := (w : Extension B v) → adicCompletion L w.val) s
  rw [← AlgHom.coe_toLinearMap, ← LinearMap.range_eq_top, Submodule.eq_top_iff']
  simp_rw [← Submodule.mem_toAddSubmonoid, ← AddSubmonoid.mem_toSubsemigroup,
      ← AddSubsemigroup.mem_carrier]
  have denseL : DenseRange (algebraMap L ((w : Extension B v) → adicCompletion L w.val)) := by
    have := Extension.finite A K L B v
    exact denseRange_of_prodAlgebraMap _ Subtype.val_injective
  rw [← isClosed.closure_eq]
  apply Dense.mono _ denseL
  rintro _ ⟨l, rfl⟩
  use (l ⊗ₜ 1)
  simp


-- @@ L314-318 verbatim
open scoped TensorProduct.RightActions in
/-- ∏_{w|v} L_w is a finite K_v-module. -/
instance [FiniteDimensional K L] :
    Module.Finite (adicCompletion K v) (Π w : v.Extension B, w.1.adicCompletion L) :=
  .of_surjective (baseChangeRight K L B v).toLinearMap (baseChangeRight_surjective K L B v)


-- @@ L320-323 verbatim
/-- L_w is a finite K_v-module if w | v. -/
instance [FiniteDimensional K L] (w : v.Extension B) :
    Module.Finite (adicCompletion K v) (adicCompletion L w.1) :=
  Module.Finite.of_pi (fun (w : Extension B v) => w.1.adicCompletion L) w


-- @@ L325-332 verbatim
/-- L_w has the K_v-module topology. -/
instance instIsModuleTopology [FiniteDimensional K L] (w : v.Extension B) :
    IsModuleTopology (v.adicCompletion K) (w.1.adicCompletion L) := by
  let Kv := adicCompletion K v
  let Lw := adicCompletion L w.1
  let iso : ((Fin (Module.finrank Kv Lw)) → Kv) ≃L[Kv] Lw :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun Kv)
  apply IsModuleTopology.iso iso


-- @@ L334-339 verbatim
/-- ∏_{w|v} L_w has the K_v-module topology. -/
instance instIsModuleTopologyPi [FiniteDimensional K L] :
    -- the claim that L_w has the module topology.
    IsModuleTopology (v.adicCompletion K) (Π (w : v.Extension B), w.1.adicCompletion L) := by
  let := Extension.finite A K L B v
  exact IsModuleTopology.instPi


-- @@ L341-351 verbatim
open scoped TensorProduct.RightActions in
/-- `tensorAdicCompletionComapLinearMap` is continuous, open and surjective.
  We later show that it's a homeomorphism. -/
lemma baseChangeRight_isOpenQuotientMap [FiniteDimensional K L] :
    IsOpenQuotientMap (baseChangeRight K L B v) := by
  have : T2Space (L ⊗[K] adicCompletion K v) :=
    IsModuleTopology.t2Space' (K := (adicCompletion K v))
  have hsurj := baseChangeRight_surjective K L B v
  rw [← AlgHom.coe_toLinearMap]
  exact ⟨hsurj, LinearMap.continuous_of_finiteDimensional _,
    LinearMap.isOpenMap_of_finiteDimensional _ hsurj⟩


-- @@ L353-353 verbatim
end ModuleTopology


-- @@ L355-355 verbatim
end adicCompletion


-- @@ L357-357 verbatim
section ModuleTopology


-- @@ L359-359 verbatim
open Extension adicCompletion


-- @@ L361-361 verbatim
variable (B)


-- @@ L363-369 verbatim
/-- The canonical B-algebra map `B ⊗[A] 𝓞_v → L ⊗[K] K_v` -/
noncomputable def tensorAdicCompletionIntegersTo :
    B ⊗[A] adicCompletionIntegers K v →ₐ[B] L ⊗[K] adicCompletion K v :=
  Algebra.TensorProduct.lift
    (Algebra.algHom _ _ _)
    ((Algebra.TensorProduct.includeRight.restrictScalars A).comp (IsScalarTower.toAlgHom _ _ _))
    (fun _ _ ↦ .all _ _)


-- @@ L371-376 verbatim
omit [Algebra.IsIntegral A B] [IsDedekindDomain B] [IsFractionRing B L] in
@[simp]
lemma tensorAdicCompletionIntegersTo_tmul (v : HeightOneSpectrum A) (b : B)
    (x : v.adicCompletionIntegers K) : tensorAdicCompletionIntegersTo K L B v (b ⊗ₜ x) =
      (algebraMap B L b) ⊗ₜ x.val := by
  simp [tensorAdicCompletionIntegersTo, Algebra.algHom]


-- @@ L378-430 verbatim
omit [Algebra.IsIntegral A B] [IsDedekindDomain B] [IsFractionRing B L] in
open scoped TensorProduct.RightActions in
/-- The image of `B ⊗[A] 𝓞_v` in `L ⊗[K] K_v` is contained in the closure of the image of `B`. -/
lemma tensorAdicCompletionIntegersTo_range_subset_closure [FiniteDimensional K L] :
  (tensorAdicCompletionIntegersTo K L B v).range.carrier ⊆
    closure (algebraMap B (L ⊗[K] adicCompletion K v)).range := by
  rintro _ ⟨s, rfl⟩
  induction s with
    | zero =>
        apply subset_closure
        use 0
        simp
    | add x y hx hy =>
        -- The closure of a subgroup is a subgroup
        rw [RingHom.map_add]
        apply map_mem_closure₂ _ hx hy _
        · exact (ModuleTopology.continuousAdd _ _).continuous_add
        intro _ ha _ hb
        exact add_mem ha hb
    | tmul b a' =>
        -- Rewrite `tensorAdicCompletionTo (b ⊗ₜ a')` to `b • (1 ⊗ₜ a')`
        simp only [RingHom.coe_range, tensorAdicCompletionIntegersTo,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul,
          AlgHom.coe_comp, AlgHom.coe_restrictScalars', IsScalarTower.coe_toAlgHom',
          Function.comp_apply, ValuationSubring.algebraMap_apply,
          Algebra.TensorProduct.includeRight_apply]
        -- Now, `f : a' ↦ b • (1 ⊗ₜ a')` is continuous
        let f (y : ↥(adicCompletionIntegers K v)) : (L ⊗[K] adicCompletion K v) :=
          (Algebra.ofId B (L ⊗[K] adicCompletion K v)) b * (1 : L) ⊗ₜ[K] (y : adicCompletion K v)
        have hfval : f = fun (y : ↥(adicCompletionIntegers K v)) =>
              (y : adicCompletion K v) • (Algebra.ofId B (L ⊗[K] adicCompletion K v)) b := by
          ext y
          unfold f
          rw [Algebra.smul_def]
          exact mul_comm _ _
        have hcf : ContinuousAt f a' := by
          rw [hfval]
          fun_prop
        -- So, because `A` is dense in `𝒪_v`, `b • (1 ⊗ₜ a') ∈ f '' closure A ⊆ closure f '' A`
        have hy : a' ∈ closure (Set.range (algebraMap A _)) := by
          apply denseRange_of_integerAlgebraMap
        apply mem_closure_image hcf hy
        constructor
        · exact isClosed_closure
        -- Finally, `b • (1 ⊗ₜ a) = (b * a) • (1 ⊗ₜ 1)`, so `f '' A ⊆ algebraMap '' B`
        rintro u ⟨_, ⟨a, rfl⟩, rfl⟩
        apply subset_closure
        use algebraMap A B a * b
        unfold f
        rw [Algebra.algebraMap_eq_smul_one (A := (adicCompletionIntegers K v)) a,
          coe_smul_adicCompletionIntegers, ← TensorProduct.smul_tmul, Algebra.ofId_apply,
          Algebra.TensorProduct.algebraMap_apply, RingHom.map_mul, ← Algebra.smul_def]
        simp


-- @@ L432-483 verbatim
open scoped TensorProduct.RightActions in
omit [Algebra.IsIntegral A B] [IsDedekindDomain B] [IsFractionRing B L]  in
/-- The image of `B ⊗[A] 𝓞_v` in `L ⊗[K] K_v` is clopen. -/
lemma tensorAdicCompletionIntegersTo_isClopen_range
    [IsIntegralClosure B A L] [FiniteDimensional K L] :
    IsClopen (SetLike.coe (tensorAdicCompletionIntegersTo K L B v).range) := by
  -- `B ⊗[A] 𝒪_v` is a subgroup of `L ⊗[K] K_v`, so we can show it's closed
  -- by showing that it's open. **TODO** split into IsOpen + IsClosed lemmas?
  have : SeparatelyContinuousAdd (L ⊗[K] v.adicCompletion K) :=
    instSeparatelyContinuousAddOfContinuousAdd
  rw [← Subalgebra.coe_toSubring, ← Subring.coe_toAddSubgroup]
  refine OpenAddSubgroup.isClopen ⟨_, ?_⟩
  -- Further, we can show `B ⊗[A] 𝒪_v` is open by showing that it contains an
  -- open neighbourhood of 0.
  apply AddSubgroup.isOpen_of_zero_mem_interior
  rw [mem_interior, Subring.coe_toAddSubgroup, Subalgebra.coe_toSubring]
  -- Take a basis `b` of `L` over `K` with elements in `B` and use it to
  -- get a basis `b'` of `L ⊗[K] K_v` over `K_v`.
  obtain ⟨ι, b, hb⟩ := FiniteDimensional.exists_is_basis_integral A K L
  let b' : Module.Basis ι (adicCompletion K v) (L ⊗[K] (adicCompletion K v)) := by
    classical
    exact b.rightBaseChange L
  -- Use the basis to get a continuous equivalence from `L ⊗[K] K_v` to `ι → K_v`.
  let equiv : L ⊗[K] (adicCompletion K v) ≃L[v.adicCompletion K] (ι → adicCompletion K v) :=
    IsModuleTopology.continuousLinearEquiv (b'.equivFun)
  -- Use the preimage of `∏ 𝒪_v` as the open neighbourhood.
  use equiv.symm '' (Set.pi Set.univ (fun _ => SetLike.coe (adicCompletionIntegers K v)))
  refine ⟨?_, ?_, by simp⟩
  · intro t ⟨g, hg, ht⟩
    -- We have `t = equiv g = ∑ i, b i ⊗ g i`, since `g in ∏ 𝒪_v` and
    -- `b i ∈ (algebraMap B L).range`, this is `tensorAdicCompletionTo`
    -- of some element of `B ⊗[A] 𝒪_v`
    have hf : ∀ (i : ι), ∃ (w : B), (algebraMap B L w) = (b i) := by
      intro i
      apply IsIntegralClosure.isIntegral_iff.mp (hb i)
    choose f hf_prop using hf
    let b : B ⊗[A] ↥(adicCompletionIntegers K v) := ∑ (i : ι), (f i) ⊗ₜ ⟨g i, hg i trivial⟩
    use b
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sum, ← ht]
    unfold equiv
    rw [IsModuleTopology.continuousLinearEquiv_symm_apply, Module.Basis.equivFun_symm_apply]
    apply Finset.sum_congr rfl
    intro x
    simp only [Finset.univ_eq_attach, Finset.mem_attach, tensorAdicCompletionIntegersTo_tmul,
      hf_prop, Module.Basis.rightBaseChange_apply, Algebra.smul_def,
      TensorProduct.RightActions.algebraMap_eval, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      mul_one, imp_self, b']
  · rw [ContinuousLinearEquiv.image_symm_eq_preimage]
    apply IsOpen.preimage equiv.continuous
    apply isOpen_set_pi Set.finite_univ
    rintro i -
    exact Valued.isOpen_valuationSubring (v.adicCompletion K)


-- @@ L485-499 verbatim
omit [Algebra.IsIntegral A B] [IsDedekindDomain B] [IsFractionRing B L] in
open scoped TensorProduct.RightActions in
/-- The image of `B ⊗[A] 𝓞_v` in `L ⊗[K] K_v` is the closure of the image of `B`. -/
lemma range_tensorAdicCompletionIntegersTo_eq_closure_range_algebraMap
    [IsIntegralClosure B A L] [FiniteDimensional K L] :
    Set.range (tensorAdicCompletionIntegersTo K L B v) =
      closure (Set.range (algebraMap B (L ⊗[K] adicCompletion K v))) := by
  apply Set.Subset.antisymm
  · apply tensorAdicCompletionIntegersTo_range_subset_closure
  · apply closure_minimal
    · rintro _ ⟨b, rfl⟩
      use b ⊗ₜ[A] 1
      simp
    · apply IsClopen.isClosed
      apply tensorAdicCompletionIntegersTo_isClopen_range


-- @@ L501-510 verbatim
omit [Algebra A L] [IsScalarTower A B L] in
/-- The `B`-subalgebra `∏_{w|v} 𝓞_w` of `∏_{w|v} L_w` is the closure of the image of `B`. -/
lemma pi_adicCompletionIntegers_eq_closure_range_algebraMap :
    (Set.univ.pi (fun (w : Extension B v) ↦ (w.1.adicCompletionIntegers L).carrier)) =
      closure (Set.range (algebraMap B _)) := by
  let val := fun (w : Extension B v) ↦ w.1
  have hinj : Function.Injective val :=
    (Set.injective_codRestrict Subtype.property).mp fun _ _ a ↦ a
  rw [← closureAlgebraMapIntegers_eq_prodIntegers L _ hinj]
  rfl


-- @@ L512-528 verbatim
open scoped TensorProduct.RightActions in
/-- The image of `B ⊗[A] 𝓞_v` (the closure of `B`) in `∏_w L_w` is closed. -/
lemma isClosed_baseChange_image_closure_range_algebraMap [FiniteDimensional K L] :
    IsClosed ((baseChange K L B v) ''
        closure (Set.range (algebraMap B (L ⊗[K] adicCompletion K v)))) := by
  let S := AddSubgroup.map
      (baseChange K L B v).toAddMonoidHom
      (tensorAdicCompletionIntegersTo K L B v).range.toSubring.toAddSubgroup
  have hSclosed : IsClosed S.carrier := by
    apply AddSubgroup.isClosed_of_isOpen
    apply (baseChangeRight_isOpenQuotientMap K L B v).isOpenMap
    apply (tensorAdicCompletionIntegersTo_isClopen_range K L B v).isOpen
  suffices h : (baseChange K L B v) ''
    closure (Set.range (algebraMap B (L ⊗[K] adicCompletion K v))) = S.carrier by
    rwa [h]
  rw [← range_tensorAdicCompletionIntegersTo_eq_closure_range_algebraMap]
  rfl


-- @@ L530-535 verbatim
instance : MulActionHomClass
    (L ⊗[K] adicCompletion K v →ₐ[L] (w : Extension B v) → adicCompletion L w.1) B
    (L ⊗[K] adicCompletion K v) ((w : Extension B v) → adicCompletion L w.1) where
  map_smulₛₗ φ b x := by
    rw [← IsScalarTower.algebraMap_smul L, AlgHom.map_smul_of_tower,
      IsScalarTower.algebraMap_smul, id_def]


-- @@ L537-551 verbatim
open scoped TensorProduct.RightActions in
/-- The image of `B ⊗[A] 𝓞_v` in `∏_w L_w` is `∏_w 𝓞_w`. -/
theorem range_baseChange_comp_tensorAdicCompletionTo_eq_pi [FiniteDimensional K L] :
    Set.range (baseChange K L B v ∘ tensorAdicCompletionIntegersTo K L B v) =
    Set.univ.pi (fun w ↦ (w.1.adicCompletionIntegers L).carrier) := by
  have hrange :
    Set.range (algebraMap B ((w : Extension B v) → adicCompletion L w.1)) =
      (baseChange K L B v) '' (Set.range (algebraMap B (L ⊗[K] adicCompletion K v))) := by
    ext x
    simp [Algebra.algebraMap_eq_smul_one]
  have hrange' := isClosed_baseChange_image_closure_range_algebraMap K L B v
  rw [Set.range_comp, range_tensorAdicCompletionIntegersTo_eq_closure_range_algebraMap,
    pi_adicCompletionIntegers_eq_closure_range_algebraMap, hrange, ← IsClosed.closure_eq hrange']
  exact closure_image_closure
    (baseChangeRight_isOpenQuotientMap K L B v).continuous


-- @@ L553-553 verbatim
namespace Extension


-- @@ L555-555 verbatim
variable {B} (w : v.Extension B)


-- @@ L557-561 verbatim
/-- The restriction of `adicCompletionSemialgHom` to a map `𝓞_v → 𝓞_w`. -/
noncomputable def adicCompletionIntegersRingHom :
    v.adicCompletionIntegers K →+* w.1.adicCompletionIntegers L :=
  RingHom.restrict (w.adicCompletionSemialgHom K L) _ _
    fun x hx ↦ w.adicCompletionSemialgHom_image_adicCompletionIntegers K L ⟨x, hx, rfl⟩


-- @@ L563-565 verbatim
/-- If `w` is an extension of `v`, then `𝓞_w` is naturally an `𝓞_v`-algebra. -/
noncomputable instance : Algebra (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) :=
  (w.adicCompletionIntegersRingHom K L).toAlgebra


-- @@ L567-569 verbatim
lemma integer_algebraMap_apply (x : v.adicCompletionIntegers K) :
    algebraMap (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) x =
      (w.adicCompletionSemialgHom K L) x.val := rfl


-- @@ L571-574 verbatim
variable {v} in
/-- If `w` is an extension of `v`, then `L_w` is naturally an `𝓞_v`-algebra. -/
noncomputable instance : Algebra (v.adicCompletionIntegers K) (w.1.adicCompletion L) :=
  Algebra.compHom (w.1.adicCompletion L) (algebraMap _ (adicCompletion K v))


-- @@ L576-576 verbatim
end Extension


-- @@ L578-584 verbatim
open scoped TensorProduct.RightActions in
instance : IsBiscalar B (v.adicCompletionIntegers K) (tensorAdicCompletionIntegersTo K L B v) where
  map_smul₁ _ _ := map_smul ..
  map_smul₂ _ _ := by
    simp only [tensorAdicCompletionIntegersTo_tmul, Algebra.smul_def,
      TensorProduct.RightActions.algebraMap_eval, map_mul, map_one]
    rfl


-- @@ L586-587 verbatim
instance {w : v.Extension B} : IsScalarTower (adicCompletionIntegers K v) (adicCompletion K v)
    (w.1.adicCompletion L) := Submonoid.instIsScalarTowerSubtypeMem (adicCompletionIntegers K v)


-- @@ L589-595 verbatim
open scoped TensorProduct.RightActions in
/-- The `O_v`-linear map from `B ⊗[A] 𝓞ᵥ` to `Π v ∣ w, L_w` -/
noncomputable def tensorAdicCompletionIntegersToPiRight :
    B ⊗[A] v.adicCompletionIntegers K →ₐ[v.adicCompletionIntegers K]
        Π w : v.Extension B, w.1.adicCompletion L :=
  ((baseChangeRight K L B v).restrictScalars _).comp
    ((tensorAdicCompletionIntegersTo K L B v).changeScalars _)


-- @@ L597-597 verbatim
namespace Extension


-- @@ L599-599 verbatim
variable (w : v.Extension B)


-- @@ L601-605 verbatim
open scoped TensorProduct.RightActions in
/-- The map `B ⊗ 𝓞_v → L_w` for `w` an extension of `v` given by the algebra maps. -/
noncomputable def tensorAdicCompletionIntegersToAdicCompletion :
    B ⊗[A] (adicCompletionIntegers K v) →ₐ[adicCompletionIntegers K v] adicCompletion L w.1 :=
  Pi.evalAlgHom _ _ w |>.comp (tensorAdicCompletionIntegersToPiRight K L B v)


-- @@ L607-630 verbatim
open scoped TensorProduct.RightActions in
/-- The range of `adicCompletionIntegers.tensorToAdicCompletion` is `𝓞_w`. -/
lemma tensorAdicCompletionIntegersToAdicCompletion_range_eq_integers [FiniteDimensional K L] :
    Set.range (w.tensorAdicCompletionIntegersToAdicCompletion K L B v) =
      adicCompletionIntegers L w.1 := by
  ext x
  have memrange := (range_baseChange_comp_tensorAdicCompletionTo_eq_pi K L B v)
  rw [Set.ext_iff] at memrange
  constructor
  · rintro ⟨y, rfl⟩
    exact (memrange _).mp (Set.mem_range_self y) w trivial
  · intro hx
    classical
    set x' : (w : Extension B v) → adicCompletion L w.val := Pi.single w x with hx'
    obtain ⟨y, (hy : _ = x')⟩ : x' ∈ Set.range _ := by
      rw [memrange x', Set.mem_pi]
      intro w' _
      by_cases h : w = w'
      · rw [← h, hx', Pi.single_eq_same]
        exact hx
      · rw [hx', Pi.single_eq_of_ne' h]
        exact Subring.zero_mem _
    use y
    simpa [hx'] using! congr_fun hy w


-- @@ L632-634 verbatim
/-- A shortcut instance for the action of `𝓞ᵥ` on `Kᵥ`. -/
noncomputable local instance : MulAction (v.adicCompletionIntegers K) (v.adicCompletion K) :=
  LieAlgebra.ofAssociativeAlgebra.toMulAction


-- @@ L636-657 verbatim
open scoped TensorProduct.RightActions in
/-- `𝓞_w` is finite over `𝓞_v`. -/
-- This can be proved for finite extensions of complete discretely valued fields without
-- reference to underlying fields being completed, but this is sufficient for our
-- purposes.
noncomputable instance (priority := 1001) [Module.Finite A B] [FiniteDimensional K L] :
    Module.Finite (adicCompletionIntegers K v) (adicCompletionIntegers L w.1) := by
  let integerSubmodule : Submodule (adicCompletionIntegers K v) (adicCompletion L w.1) :=
    let : Algebra (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L).toSubring :=
      inferInstanceAs (Algebra (adicCompletionIntegers K v) (adicCompletionIntegers L w.1))
    have : IsScalarTower (adicCompletionIntegers K v) (adicCompletionIntegers L w.1)
        (adicCompletion L w.1) := .of_algebraMap_smul fun _ _ ↦ rfl
    (adicCompletionIntegers L w.1).toSubmodule.restrictScalars
      (adicCompletionIntegers K v)
  have heq : (w.tensorAdicCompletionIntegersToAdicCompletion K L B v).toLinearMap.range =
      integerSubmodule := by
    ext x
    apply w.tensorAdicCompletionIntegersToAdicCompletion_range_eq_integers K L B v |> Set.ext_iff.mp
  have := Module.Finite.range (w.tensorAdicCompletionIntegersToAdicCompletion K L B v).toLinearMap
  have := w.tensorAdicCompletionIntegersToAdicCompletion_range_eq_integers K L B v
  exact Module.Finite.equiv <| LinearEquiv.ofEq
    (LinearMap.range (w.tensorAdicCompletionIntegersToAdicCompletion K L B v).toLinearMap) _ heq


-- @@ L659-659 verbatim
end Extension


-- @@ L661-661 verbatim
end ModuleTopology


-- @@ L663-663 verbatim
namespace adicCompletion


-- @@ L665-665 verbatim
open Extension


-- @@ L667-667 verbatim
section RamificationInertia


-- @@ L669-669 verbatim
variable {v} (w : v.Extension B)


-- @@ L671-673 verbatim
lemma _root_.WithZero.ofAdd_neg_ofNat_pow (n : ℕ) :
    (WithZero.coe (Multiplicative.ofAdd (-n : ℤ))) = (Multiplicative.ofAdd (-1 : ℤ)) ^ n := by
  rw [← WithZero.coe_pow, ← ofAdd_nsmul, nsmul_eq_mul, Int.mul_neg_one]


-- @@ L675-683 verbatim
/-- The maximal ideal of `𝒪_w` lies over the maximal ideal of `𝒪_v`. -/
lemma liesOver_completionIdeal :
    (w.1.completionIdeal L).LiesOver (v.completionIdeal K) where
  over := by
    rw [Ideal.under_def]
    ext x
    rw [Ideal.mem_comap, mem_completionIdeal_iff, mem_completionIdeal_iff,
      integer_algebraMap_apply, valued_adicCompletionSemialgHom K L, pow_lt_one_iff]
    exact ramificationIdx_ne_zero A B (algebraMap_injective_of_field_isFractionRing A B K L) w.1


-- @@ L685-718 verbatim
/-- The local ramification index of `L_w/K_v` equals the global ramification index of `w/v`. -/
theorem ramificationIdx_eq_ramificationIdx :
    (w.1.completionIdeal L).ramificationIdx (v.adicCompletionIntegers K) =
      w.1.asIdeal.ramificationIdx A := by
  have := liesOver_completionIdeal K L w
  have : IsScalarTower (adicCompletionIntegers K v) (adicCompletionIntegers L w.1)
      (adicCompletion L w.1) := .of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower (adicCompletionIntegers K v) (adicCompletion K v) (adicCompletion L w.1) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  have : FaithfulSMul (adicCompletionIntegers K v) (adicCompletionIntegers L w.1) :=
    FaithfulSMul.of_field_isFractionRing _ _ (adicCompletion K v) (adicCompletion L w.1)
  -- `Ideal.ramificationIdx'` is the one characterised by `map p ≤ P ^ n` and `¬ map p ≤ P ^ (n+1)`,
  -- so we check that characterisation for the global ramification index of `w/v`.
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (v.completionIdeal K) (w.1.completionIdeal L)
      (v.completionIdeal_ne_bot K)]
  apply Ideal.ramificationIdx'_spec
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [mem_completionIdeal_iff'] at hx
    rw [Ideal.mem_comap, adicCompletion.mem_completionIdeal_pow, integer_algebraMap_apply,
      valued_adicCompletionSemialgHom]
    rw [WithZero.ofAdd_neg_ofNat_pow]
    apply pow_le_pow_left' hx
  · obtain ⟨ϖ, hϖ⟩ := adicCompletion.exists_uniformizer K v
    have hϖ' : ϖ ∈ v.completionIdeal K := by
      rw [mem_completionIdeal_iff, hϖ]
      decide
    rw [Ideal.map_le_iff_le_comap]
    intro h
    have hcomap := h hϖ'
    rw [Ideal.mem_comap, adicCompletion.mem_completionIdeal_pow, integer_algebraMap_apply,
      valued_adicCompletionSemialgHom, hϖ, ← WithZero.ofAdd_neg_ofNat_pow,
      WithZero.coe_le_coe, Multiplicative.ofAdd_le] at hcomap
    simp at hcomap


-- @@ L720-752 verbatim
/-- The local inertia degree of `L_w/K_v` equals the global inertia degree of `w/v`. -/
theorem inertiaDeg_eq_inertiaDeg :
    w.1.asIdeal.inertiaDeg A =
      Ideal.inertiaDeg (w.1.completionIdeal L) (v.adicCompletionIntegers K) :=
  letI := Algebra.compHom (adicCompletionIntegers L w.1) (algebraMap A B)
  have : IsScalarTower A B (adicCompletionIntegers L w.1) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A (adicCompletionIntegers K v) (adicCompletionIntegers L w.1) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    ext
    rw [Algebra.compHom_algebraMap_eq, RingHom.coe_comp, Function.comp_apply,
      algebraMap_completionIntegers, integer_algebraMap_apply, algebraMap_completionIntegers,
      IsScalarTower.algebraMap_apply B L (adicCompletion L w.1),
      ← IsScalarTower.algebraMap_apply A B L, IsScalarTower.algebraMap_apply A K L]
    symm
    apply SemialgHom.commutes
  have := liesOver_completionIdeal K L w
  -- Both sides are computed by comparing them with the inertia degree of `𝔪_w` over `A`, using
  -- that inertia degrees are multiplicative in the towers `A ⊆ B ⊆ 𝒪_w` and `A ⊆ 𝒪_v ⊆ 𝒪_w`.
  calc w.1.asIdeal.inertiaDeg A
      = Ideal.inertiaDeg (w.1.completionIdeal L) A := by
        rw [Ideal.inertiaDeg_tower w.1.asIdeal (w.1.completionIdeal L),
          inertiaDeg_asIdeal_completionIdeal, mul_one]
    _ = Ideal.inertiaDeg (w.1.completionIdeal L) (v.adicCompletionIntegers K) := by
        rw [Ideal.inertiaDeg_tower (v.completionIdeal K) (w.1.completionIdeal L),
          inertiaDeg_asIdeal_completionIdeal, one_mul]

-- We use Ideal.ramificationIdx_mul_inertiaDeg_eq_finrank_of_isLocalRing here to show this, but we
-- could make use of the more general results in BGR:
-- - in general e * f <= degree (Prop 3.1.3.2)
-- - equality holds for L/K if L is K-cartesian (Prop 3.6.2.4)
-- - so for example if K is complete and discretely-valued (Cor 2.4.3.11).

-- @@ L753-767 verbatim
theorem ramificationIdx_mul_inertiaDeg_eq_finrank [FiniteDimensional K L] [Module.Finite A B] :
    w.1.asIdeal.ramificationIdx A * w.1.asIdeal.inertiaDeg A =
      Module.finrank (adicCompletion K v) (adicCompletion L w.1) := by
  have : IsScalarTower (adicCompletionIntegers K v) (adicCompletionIntegers L w.1)
      (adicCompletion L w.1) := .of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower (adicCompletionIntegers K v) (adicCompletion K v) (adicCompletion L w.1) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  -- should any of these be more global instances?
  have : FaithfulSMul (adicCompletionIntegers K v) (adicCompletionIntegers L w.1) :=
    FaithfulSMul.of_field_isFractionRing _ _ (adicCompletion K v) (adicCompletion L w.1)
  rw [IsFractionRing.finrank_eq (adicCompletionIntegers K v) (adicCompletion K v)
      (adicCompletionIntegers L w.1) (adicCompletion L w.1),
    ← Ideal.ramificationIdx_mul_inertiaDeg_eq_finrank_of_isLocalRing (adicCompletionIntegers L w.1)
      (p := v.completionIdeal K) (v.completionIdeal_ne_bot K),
    ramificationIdx_eq_ramificationIdx, inertiaDeg_eq_inertiaDeg K L w]


-- @@ L769-769 verbatim
end RamificationInertia


-- @@ L771-771 verbatim
variable [FiniteDimensional K L] [Module.Finite A B] (B)

-- @@ L772-772 verbatim
variable (v : HeightOneSpectrum A) (w : v.Extension B)


-- @@ L774-787 verbatim
open scoped TensorProduct.RightActions in
/-- `L ⊗[K] K_v` and `∏_{w|v} L_w` have equal dimensions -/
lemma finrank_tensorProduct_adicCompletion_eq_finrank_pi_adicCompletion :
    Module.finrank (adicCompletion K v) (L ⊗[K] adicCompletion K v) =
      Module.finrank (adicCompletion K v) ((w : Extension B v) → adicCompletion L w.val) :=
  letI := Extension.fintype A K L B v
  calc Module.finrank (adicCompletion K v) (L ⊗[K] adicCompletion K v)
    _ = Module.finrank K L := by rw [TensorProduct.finrank_rightAlgebra]
    _ = ∑ (w : Extension B v), w.val.asIdeal.ramificationIdx A * w.val.asIdeal.inertiaDeg A := by
        rw [Ideal.sum_ramification_inertia_extensions]
    _ = ∑ (w : Extension B v), Module.finrank (adicCompletion K v) (adicCompletion L w.val) :=
        Finset.sum_congr rfl fun w _ ↦ ramificationIdx_mul_inertiaDeg_eq_finrank K L w
    _ = Module.finrank (adicCompletion K v) ((w : Extension B v) → adicCompletion L w.val) := by
        rw [Module.finrank_pi_fintype (adicCompletion K v)]


-- @@ L789-796 verbatim
open scoped TensorProduct.RightActions in
/-- The canonical map `L ⊗[K] K_v → ∏_{w|v} L_w` is bijective. -/
theorem baseChange_bijective : Function.Bijective (baseChange K L B v) := by
  change Function.Bijective (baseChangeRight K L B v)
  have hsurj := baseChangeRight_surjective K L B v
  refine ⟨?_, hsurj⟩
  have hrank := finrank_tensorProduct_adicCompletion_eq_finrank_pi_adicCompletion K L B v
  rwa [← AlgHom.coe_toLinearMap, LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank]


-- @@ L798-801 verbatim
/-- The L-algebra isomorphism `L ⊗[K] K_v ≅ ∏_{w|v} L_w`. -/
noncomputable def baseChangeAlgEquiv :
    L ⊗[K] v.adicCompletion K ≃ₐ[L] Π w : v.Extension B, w.1.adicCompletion L :=
  AlgEquiv.ofBijective (baseChange K L B v) <| baseChange_bijective K L B v


-- @@ L803-811 verbatim
set_option backward.isDefEq.respectTransparency false in
open scoped TensorProduct.RightActions in
/-- The continuous L-algebra isomorphism `L ⊗[K] K_v ≅ ∏_{w|v} L_w`. -/
noncomputable def baseChangeContinuousAlgEquiv :
    L ⊗[K] v.adicCompletion K ≃A[L] Π w : v.Extension B, w.1.adicCompletion L :=
  have : IsBiscalar L (v.adicCompletion K) (baseChangeAlgEquiv K L B v).toAlgHom :=
    inferInstanceAs (IsBiscalar L (v.adicCompletion K) (baseChange K L B v))
  IsModuleTopology.continuousAlgEquivOfIsBiscalar (v.adicCompletion K)
    (baseChangeAlgEquiv K L B v)


-- @@ L813-817 verbatim
/-- The `B`-module isomorphism `B ⊗[A] K_v ≅ ∏_{w|v} L_w`. -/
noncomputable def integerBaseChangeLinearEquiv :
    B ⊗[A] v.adicCompletion K ≃ₗ[B] ∀ w : v.Extension B, w.1.adicCompletion L :=
  (linearEquivTensorProductModuleLeft A K L B (v.adicCompletion K)).symm.trans
    ((baseChangeAlgEquiv K L B v).toLinearEquiv.restrictScalars B)


-- @@ L819-825 verbatim
@[simp]
lemma integerBaseChangeLinearEquiv_tmul_apply (b x) :
    integerBaseChangeLinearEquiv K L B v (b ⊗ₜ[A] x) w =
      algebraMap B _ b * algebraMap _ _ x := by
  rw [integerBaseChangeLinearEquiv, LinearEquiv.trans_apply,
    linearEquivTensorProductModuleLeft_symm_tmul]
  rfl


-- @@ L827-830 verbatim
/-- `𝓞_v` as an `A`-submodule of `K_v`. -/
noncomputable def integerSubmodule (v : HeightOneSpectrum A) : Submodule A (adicCompletion K v) :=
  let s : Submodule (adicCompletionIntegers K v) _ := (adicCompletionIntegers K v).toSubmodule
  s.restrictScalars A


-- @@ L832-832 verbatim
end adicCompletion


-- @@ L834-834 verbatim
namespace adicCompletionIntegers


-- @@ L836-836 verbatim
open adicCompletion


-- @@ L838-838 verbatim
variable (B)


-- @@ L840-843 verbatim
/-- The canonical `B`-linear map `B ⊗[A] 𝓞_v → B ⊗[A] K_v`. -/
noncomputable def tensorCoe : B ⊗[A] v.adicCompletionIntegers K →ₗ[B] B ⊗[A] v.adicCompletion K :=
  TensorProduct.AlgebraTensorModule.lTensor _ _
    (Algebra.algHom A (adicCompletionIntegers K v) (adicCompletion K v))


-- @@ L845-848 verbatim
omit [Algebra.IsIntegral A B] [IsDedekindDomain B] in
@[simp]
lemma tensorCoe_tmul (b : B) (x : v.adicCompletionIntegers K) :
    tensorCoe K B v (b ⊗ₜ x) = b ⊗ₜ x.val := rfl


-- @@ L850-850 verbatim
end adicCompletionIntegers


-- @@ L852-852 verbatim
namespace adicCompletion


-- @@ L854-854 verbatim
open Extension


-- @@ L856-856 verbatim
variable [FiniteDimensional K L] [Module.Finite A B]


-- @@ L858-872 verbatim
theorem integerBaseChangeLinearEquiv_bijOn (v : HeightOneSpectrum A) :
    Set.BijOn (integerBaseChangeLinearEquiv K L B v)
      (Set.range (adicCompletionIntegers.tensorCoe K B v))
      (Submodule.pi Set.univ fun (w : Extension B v) ↦ integerSubmodule L w.val) := by
  suffices h : ((integerBaseChangeLinearEquiv K L B v) ''
      (LinearMap.range (adicCompletionIntegers.tensorCoe K B v))) =
      Submodule.pi .univ fun (w : Extension B v) ↦ (integerSubmodule L w.val).restrictScalars A from
    h ▸ Equiv.bijOn_image (integerBaseChangeLinearEquiv K L B v).toEquiv
  apply Eq.trans _ (range_baseChange_comp_tensorAdicCompletionTo_eq_pi K L B v)
  rw [LinearMap.coe_range, ← Set.range_comp, ← LinearEquiv.coe_toLinearMap, ← LinearMap.coe_comp]
  rw [← AlgHom.coe_restrictScalars' B (baseChange K L B v), ← AlgHom.coe_comp,
    ← AlgHom.coe_toLinearMap]
  congr
  ext
  simp [baseChange_tmul_apply]


-- @@ L874-874 verbatim
end IsDedekindDomain.HeightOneSpectrum.adicCompletion
