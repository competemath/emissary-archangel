module

public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import FltRegular.NumberTheory.Cyclotomic.MoreLemmas


-- @@ L8-13 verbatim
/-!
# Units in cyclotomic fields

This file records how complex conjugation acts on cyclotomic units and proves that the quotient
of a unit by its conjugate is a square of a root of unity.
-/


-- @@ L15-15 verbatim
@[expose] public section


-- @@ L17-17 verbatim
variable {p : ℕ} [NeZero p] {K : Type*} [Field K]


-- @@ L19-19 verbatim
variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)


-- @@ L21-21 verbatim
open scoped nonZeroDivisors NumberField


-- @@ L23-23 verbatim
open IsCyclotomicExtension NumberField Polynomial IsCMField


-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-27 verbatim
local notation3 "η" => (hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit


-- @@ L29-29 verbatim
set_option quotPrecheck false

-- @@ L30-30 expanded
local notation "I" =>
  (Ideal.span ({((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit - 1 : 𝓞 K)} : Set (𝓞 K)) :
    Ideal (𝓞 K))


-- @@ L32-37 verbatim
theorem eq_one_mod_one_sub {A : Type*} [CommRing A] {t : A} :
    algebraMap A (A ⧸ Ideal.span ({t - 1} : Set A)) t = 1 := by
  rw [← map_one <| algebraMap A <| A ⧸ Ideal.span ({t - 1} : Set A),
    ← sub_eq_zero, ← map_sub,
    Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_singleton _)


-- @@ L39-39 verbatim
variable [NumberField K] [IsCyclotomicExtension {p} ℚ K]


-- @@ L41-53 expanded
include hζ in
/-- Complex conjugation sends a primitive `p`-th root of unity to its inverse. -/
-- The primality instance is retained for compatibility with existing callers.

@[nolint unusedArguments]
theorem complexConj_zeta [Fact (p.Prime)] (hp : 2 < p) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := { p }) K ⟨p, rfl, hp⟩
    complexConj K ζ = ζ⁻¹ :=
  by
  let _ := IsCyclotomicExtension.Rat.isCMField (S := { p }) K ⟨p, rfl, hp⟩
  have hη : (hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit ∈ Units.torsion K :=
    by
    refine (CommGroup.mem_torsion _).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨p, NeZero.pos p, ?_⟩)
    ext
    exact hζ.pow_eq_one
  exact complexConj_torsion (K := K) ⟨(hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit, hη⟩


-- @@ L55-64 expanded
lemma unit_inv_conj_not_neg_zeta_runity_aux (u : (𝓞 K)ˣ) [Fact (p.Prime)] (hp : 2 < p) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := { p }) K ⟨p, rfl, hp⟩
    algebraMap (𝓞 K)
        (𝓞 K ⧸
          (Ideal.span
              ({((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit - 1 : 𝓞 K)} : Set (𝓞 K)) :
            Ideal (𝓞 K)))
        (unitsMulComplexConjInv K u).1 =
      1 :=
  by
  let _ := IsCyclotomicExtension.Rat.isCMField (S := { p }) K ⟨p, rfl, hp⟩
  have hmap :=
    Units.coe_map_inv (N :=
      𝓞 K ⧸
        (Ideal.span
            ({((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit - 1 : 𝓞 K)} : Set (𝓞 K)) :
          Ideal (𝓞 K)))
      (algebraMap (𝓞 K)
        (𝓞 K ⧸
          (Ideal.span
              ({((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit - 1 : 𝓞 K)} : Set (𝓞 K)) :
            Ideal (𝓞 K))))
      (unitsComplexConj K u)
  rw [unitsMulComplexConjInv_apply, Units.val_mul, map_mul, ← MonoidHom.coe_coe, ← hmap,
    Units.mul_inv_eq_one, Units.coe_map, MonoidHom.coe_coe]
  exact
    (RingHom.congr_fun
        (quotient_zero_sub_one_comp_aut hζ (ringOfIntegersComplexConj K).toRingEquiv.toRingHom)
        (u : 𝓞 K)).symm


-- @@ L66-79 expanded
theorem unit_inv_conj_not_neg_zeta_runity (u : (𝓞 K)ˣ) (n : ℕ) [Fact (p.Prime)] (hp : 2 < p) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := { p }) K ⟨p, rfl, hp⟩
    u * (unitsComplexConj K u)⁻¹ ≠ -(hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit ^ n :=
  by
  by_contra H
  have hμ :
    algebraMap (𝓞 K)
        (𝓞 K ⧸
          (Ideal.span
              ({((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit - 1 : 𝓞 K)} : Set (𝓞 K)) :
            Ideal (𝓞 K)))
        (((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit : 𝓞 K) ^ n) =
      1 :=
    by rw [map_pow, eq_one_mod_one_sub, one_pow]
  have hμ' :
    algebraMap (𝓞 K)
        (𝓞 K ⧸
          (Ideal.span
              ({((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit - 1 : 𝓞 K)} : Set (𝓞 K)) :
            Ideal (𝓞 K)))
        (((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit : 𝓞 K) ^ n) =
      -1 :=
    by
    rw [← neg_eq_iff_eq_neg, ← map_neg, ← Units.val_pow_eq_pow_val, ← Units.val_neg, ← H]
    apply unit_inv_conj_not_neg_zeta_runity_aux hζ u hp
  let _ := Fact.mk hp
  apply
    (IsCyclotomicExtension.Rat.two_not_mem_span_zeta_sub_one' _ hζ hp :
      (2 : 𝓞 K) ∉
        (Ideal.span
            ({((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit - 1 : 𝓞 K)} : Set (𝓞 K)) :
          Ideal (𝓞 K)))
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_ofNat, ← one_add_one_eq_two, ← neg_eq_iff_add_eq_zero]
  exact hμ'.symm.trans hμ


-- @@ L81-104 expanded
theorem unit_inv_conj_is_root_of_unity (u : (𝓞 K)ˣ) [H : Fact (p.Prime)] (hp : 2 < p) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := { p }) K ⟨p, rfl, hp⟩
    ∃ m : ℕ,
      u * (unitsComplexConj K u)⁻¹ =
        ((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit ^ m) ^ 2 :=
  by
  let _ := IsCyclotomicExtension.Rat.isCMField (S := { p }) K ⟨p, rfl, hp⟩
  have hpo : Odd p := H.out.odd_of_ne_two hp.ne'
  have hη : ((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit : K) = ζ := by
    rw [IsUnit.unit_spec]; rfl
  have hroot : IsOfFinOrder (u * (unitsComplexConj K u)⁻¹ : K) :=
    by
    have h : IsOfFinOrder (u * (unitsComplexConj K u)⁻¹) :=
      (CommGroup.mem_torsion _).mp (unitsMulComplexConjInv K u).property
    exact
      (Function.Injective.isOfFinOrder_iff (f :=
            (algebraMap (𝓞 K) K).toMonoidHom.comp (Units.coeHom (𝓞 K)))
            (NumberField.Units.coe_injective K)).mpr
        h
  obtain ⟨n, -, hz | hz⟩ := hζ.exists_pow_or_neg_mul_pow_of_isOfFinOrder hpo hroot
  · have hz' :
      u * (unitsComplexConj K u)⁻¹ = (hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit ^ n :=
      by
      apply NumberField.Units.coe_injective
      simpa only [NumberField.Units.coe_mul, NumberField.Units.coe_pow, hη] using hz
    rw [hz']
    simpa only [pow_mul, mul_comm] using
      ((hζ.toInteger_isPrimitiveRoot.isUnit_unit (NeZero.ne p)).exists_pow_eq_pow_two_mul hpo n)
  · exfalso
    apply unit_inv_conj_not_neg_zeta_runity hζ u n hp
    apply NumberField.Units.coe_injective
    simpa only [NumberField.Units.coe_mul, NumberField.Units.coe_pow, Units.val_neg, map_neg,
      hη] using hz

