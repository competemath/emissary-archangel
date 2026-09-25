module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.RingTheory.ClassGroup.Basic

import FltRegular.CaseII.AuxLemmas
import FltRegular.NumberTheory.Cyclotomic.MoreLemmas
import FltRegular.NumberTheory.Cyclotomic.UnitLemmas
import FltRegular.NumberTheory.Hilbert92
import FltRegular.NumberTheory.KummersLemma.KummersLemma


-- @@ L13-18 verbatim
/-!
# The induction step in Case II

This file constructs the ideal and unit data that turn a Case II solution into the next
solution in the induction.
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
open scoped nonZeroDivisors NumberField

-- @@ L23-23 verbatim
open Polynomial IsCyclotomicExtension.Rat


-- @@ L25-25 verbatim
attribute [local implicit_reducible] integralClosure NumberField.RingOfIntegers


-- @@ L27-27 verbatim
variable {K : Type} {p : ℕ} [NeZero p] [Field K] [NumberField K] (hp : p ≠ 2)


-- @@ L29-29 verbatim
variable {ζ : K} (hζ : IsPrimitiveRoot ζ p) {x y z : 𝓞 K} {ε : (𝓞 K)ˣ}


-- @@ L31-31 verbatim
local notation3 "π" => hζ.toInteger - 1

-- @@ L32-32 expanded
local notation3 "𝔭" => Ideal.span {hζ.toInteger - 1}


-- @@ L33-33 verbatim
local notation3 "𝔦" η => Ideal.span {(x + y * η : 𝓞 K)}

-- @@ L34-34 verbatim
local notation3 "𝔵" => Ideal.span {x}

-- @@ L35-35 verbatim
local notation3 "𝔶" => Ideal.span {y}

-- @@ L36-36 verbatim
local notation3 "𝔷" => Ideal.span {z}


-- @@ L38-38 verbatim
variable {m : ℕ} (e : x ^ p + y ^ p = ε * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ p)

-- @@ L39-39 verbatim
variable (hy : ¬ hζ.toInteger - 1 ∣ y) (hz : ¬ hζ.toInteger - 1 ∣ z)

-- @@ L40-40 verbatim
variable (η : nthRootsFinset p (1 : 𝓞 K))


-- @@ L42-49 expanded
include e in
omit [NumberField K] in
lemma zeta_sub_one_dvd : hζ.toInteger - 1 ∣ x ^ p + y ^ p :=
  by
  rw [e, mul_pow, ← pow_mul]
  apply dvd_mul_of_dvd_right
  apply dvd_mul_of_dvd_left
  apply dvd_pow_self
  simp [NeZero.ne]


-- @@ L51-57 expanded
include e in
omit [NumberField K] in
lemma span_pow_add_pow_eq :
    Ideal.span {x ^ p + y ^ p} = (Ideal.span {hζ.toInteger - 1} ^ (m + 1) * Ideal.span { z }) ^ p :=
  by
  simp only [e, ← Ideal.span_singleton_pow, ← Ideal.span_singleton_mul_span_singleton]
  convert one_mul _
  rw [Ideal.one_eq_top, Ideal.span_singleton_eq_top]
  exact «ε».isUnit


-- @@ L59-59 expanded
local notation3 "𝔪" => gcd (Ideal.span { x }) (Ideal.span { y })


-- @@ L61-65 expanded
include hy in
lemma m_ne_zero : gcd (Ideal.span { x }) (Ideal.span { y }) ≠ 0 :=
  by
  simp_rw [Ne, gcd_eq_zero_iff, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  rintro ⟨rfl, rfl⟩
  exact hy (dvd_zero _)


-- @@ L67-67 verbatim
variable [hpri : Fact p.Prime]


-- @@ L69-80 expanded
lemma coprime_c_aux (η₁ η₂ : nthRootsFinset p (1 : 𝓞 K)) (hη : η₁ ≠ η₂) :
    (Ideal.span {(x + y * η₁ : 𝓞 K)}) ⊔ (Ideal.span {(x + y * η₂ : 𝓞 K)}) ∣
      gcd (Ideal.span { x }) (Ideal.span { y }) * Ideal.span {hζ.toInteger - 1} :=
  by
  have : Ideal.span {hζ.toInteger - 1} = Ideal.span (singleton <| (η₁ : 𝓞 K) - η₂) :=
    by
    rw [Ideal.span_singleton_eq_span_singleton]
    exact
      hζ.toInteger_isPrimitiveRoot.nthRootsFinset_pairwise_associated_sub_one_sub_of_prime hpri.out
        η₁.prop η₂.prop (Subtype.coe_injective.ne hη)
  rw [(gcd_mul_right' (Ideal.span {hζ.toInteger - 1}) (Ideal.span { x })
        (Ideal.span { y })).symm.dvd_iff_dvd_right,
    dvd_gcd_iff]
  simp_rw [this, Ideal.span_singleton_mul_span_singleton, Ideal.dvd_span_singleton,
    Ideal.mem_span_singleton_sup, Ideal.mem_span_singleton]
  refine ⟨⟨-η₂, _, ⟨η₁, rfl⟩, ?_⟩, ⟨1, _, ⟨-1, rfl⟩, ?_⟩⟩
  · ring
  · ring


-- @@ L82-95 verbatim
include hp hζ e hz in
omit [NumberField K] in
lemma x_plus_y_mul_ne_zero : x + y * η ≠ 0 := by
  intro hη
  have : x + y * η ∣ x ^ p + y ^ p := by
    rw [hζ.toInteger_isPrimitiveRoot.pow_add_pow_eq_prod_add_mul _ _ <| Nat.odd_iff.2 <|
      hpri.out.eq_two_or_odd.resolve_left hp]
    simp_rw [mul_comm _ y]
    exact Finset.dvd_prod_of_mem _ η.prop
  rw [hη, zero_dvd_iff, e] at this
  simp only [mul_eq_zero, Units.ne_zero, pow_eq_zero_iff (NeZero.ne p), false_or] at this
  rw [this.resolve_left (pow_ne_zero (m + 1)
    (hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero hpri.out.one_lt))] at hz
  exact hz (dvd_zero _)


-- @@ L97-97 verbatim
variable [IsCyclotomicExtension {p} ℚ K]


-- @@ L99-117 expanded
include e hp in
lemma one_sub_zeta_dvd_zeta_pow_sub : hζ.toInteger - 1 ∣ x + y * η :=
  by
  have h := zeta_sub_one_dvd hζ e
  have root_eq_one_mod {ξ : 𝓞 K} (hξ : ξ ∈ nthRootsFinset p (1 : 𝓞 K)) :
    Ideal.Quotient.mk (Ideal.span {hζ.toInteger - 1}) ξ = 1 :=
    by
    obtain ⟨i, -, hi⟩ :=
      hζ.toInteger_isPrimitiveRoot.eq_pow_of_pow_eq_one
        ((Polynomial.mem_nthRootsFinset (NeZero.pos p) 1).1 hξ)
    rw [← hi, map_pow]
    rw [← Ideal.Quotient.algebraMap_eq, eq_one_mod_one_sub, one_pow]
  replace h :
    ∏ _η ∈ nthRootsFinset p (1 : 𝓞 K),
        Ideal.Quotient.mk (Ideal.span {hζ.toInteger - 1}) (x + y * η : 𝓞 K) =
      0 :=
    by
    rw [hζ.toInteger_isPrimitiveRoot.pow_add_pow_eq_prod_add_mul _ _ <|
        Nat.odd_iff.2 <| hpri.out.eq_two_or_odd.resolve_left hp,
      ← Ideal.Quotient.eq_zero_iff_dvd, map_prod] at h
    convert h using 2 with η' hη'
    rw [map_add, map_add, map_mul, map_mul, root_eq_one_mod hη', root_eq_one_mod η.prop, one_mul,
      mul_one]
  rw [Finset.prod_const, ← map_pow, Ideal.Quotient.eq_zero_iff_dvd] at h
  exact hζ.zeta_sub_one_prime'.dvd_of_dvd_pow h


-- @@ L119-124 verbatim
include hp hζ e in
lemma div_one_sub_zeta_mem : IsIntegral ℤ ((x + y * η : 𝓞 K) / (ζ - 1)) := by
  obtain ⟨⟨a, ha⟩, e⟩ := one_sub_zeta_dvd_zeta_pow_sub hp hζ e η
  rw [e, mul_comm]
  simp only [map_mul, NumberField.RingOfIntegers.map_mk, map_sub, map_one]
  rwa [mul_div_cancel_right₀ _ (hζ.sub_one_ne_zero hpri.out.one_lt)]


-- @@ L126-128 verbatim
/-- The integral quotient `(x + y * η) / (ζ - 1)` for a `p`-th root of unity `η`. -/
def divZetaSubOne : nthRootsFinset p (1 : 𝓞 K) → 𝓞 K :=
  fun η ↦ ⟨(x + y * η.1) / (ζ - 1), div_one_sub_zeta_mem hp hζ e η⟩


-- @@ L130-134 expanded
lemma div_zeta_sub_one_mul_zeta_sub_one (η) :
    divZetaSubOne hp hζ e η * (hζ.toInteger - 1) = x + y * η :=
  by
  ext
  change
    ((x : K) + (y : K) * ((η : 𝓞 K) : K)) / (ζ - 1) * (ζ - 1) = (x : K) + (y : K) * ((η : 𝓞 K) : K)
  exact div_mul_cancel₀ _ (hζ.sub_one_ne_zero hpri.out.one_lt)


-- @@ L136-145 expanded
lemma div_zeta_sub_one_sub (η₁ η₂) (hη : η₁ ≠ η₂) :
    Associated y (divZetaSubOne hp hζ e η₁ - divZetaSubOne hp hζ e η₂) :=
  by
  apply
    Associated.of_mul_right _ (Associated.refl (hζ.toInteger - 1))
      (hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero hpri.out.one_lt)
  convert_to! Associated _ (y * (η₁ - η₂))
  · rw [sub_mul, div_zeta_sub_one_mul_zeta_sub_one, div_zeta_sub_one_mul_zeta_sub_one]
    ring
  exact
    Associated.mul_left _
      (hζ.toInteger_isPrimitiveRoot.nthRootsFinset_pairwise_associated_sub_one_sub_of_prime hpri.out
        η₁.prop η₂.prop (Subtype.coe_ne_coe.2 hη))


-- @@ L147-157 expanded
include hy in
lemma div_zeta_sub_one_Injective :
    Function.Injective
      (fun η ↦ Ideal.Quotient.mk (Ideal.span {hζ.toInteger - 1}) (divZetaSubOne hp hζ e η)) :=
  by
  intros η₁ η₂
  contrapose
  intro e₁ e₂
  apply hy
  obtain ⟨u, e⟩ := div_zeta_sub_one_sub hp hζ e η₁ η₂ e₁
  dsimp only at e₂
  rwa [← sub_eq_zero, ← map_sub, ← e, Ideal.Quotient.eq_zero_iff_dvd, u.isUnit.dvd_mul_right] at e₂


-- @@ L159-161 expanded
instance : Finite (𝓞 K ⧸ Ideal.span {hζ.toInteger - 1}) :=
  by
  rw [← Ideal.absNorm_ne_zero_iff, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
  exact hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero hpri.out.one_lt


-- @@ L163-172 expanded
include hy in
lemma div_zeta_sub_one_Bijective :
    Function.Bijective
      (fun η ↦ Ideal.Quotient.mk (Ideal.span {hζ.toInteger - 1}) (divZetaSubOne hp hζ e η)) :=
  by
  let := Fintype.ofFinite (𝓞 K ⧸ Ideal.span {hζ.toInteger - 1})
  rw [Fintype.bijective_iff_injective_and_card]
  use div_zeta_sub_one_Injective hp hζ e hy
  simp only [Fintype.card_coe]
  rw [hζ.toInteger_isPrimitiveRoot.card_nthRootsFinset, ← Nat.card_eq_fintype_card, ←
    Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton]
  simp [show Algebra.norm ℤ (hζ.toInteger - 1) = _ from
        hζ.norm_toInteger_sub_one_of_prime_ne_two' hp]


-- @@ L174-180 expanded
include hy in
lemma gcd_zeta_sub_one_eq_one :
    gcd (gcd (Ideal.span { x }) (Ideal.span { y })) (Ideal.span {hζ.toInteger - 1}) = 1 :=
  by
  rw [gcd_assoc]
  convert gcd_one_right (Ideal.span { x }) using 2
  rwa [gcd_comm, Irreducible.gcd_eq_one_iff, Ideal.dvd_span_singleton, Ideal.mem_span_singleton]
  · rw [irreducible_iff_prime]
    exact Ideal.prime_span_singleton_iff.mpr hζ.zeta_sub_one_prime'


-- @@ L182-191 expanded
include hy in
lemma gcd_div_div_zeta_sub_one (η) :
    gcd (Ideal.span { x }) (Ideal.span { y }) ∣ Ideal.span {divZetaSubOne hp hζ e η} :=
  by
  rw [← mul_one (Ideal.span {divZetaSubOne hp hζ e η}), ←
    gcd_zeta_sub_one_eq_one hζ hy (x := x) (y := y)]
  apply dvd_mul_gcd_of_dvd_mul
  rw [Ideal.span_singleton_mul_span_singleton, div_zeta_sub_one_mul_zeta_sub_one,
    Ideal.dvd_span_singleton, Ideal.gcd_eq_sup]
  refine
    add_mem (Ideal.mem_sup_left (Ideal.subset_span (s := { x }) rfl))
      (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.subset_span (s := { y }) rfl)))


-- @@ L193-195 verbatim
/-- The quotient ideal obtained from the divisibility by `𝔪`. -/
noncomputable def divZetaSubOneDvdGcd : Ideal (𝓞 K) :=
  (gcd_div_div_zeta_sub_one hp hζ e hy η).choose


-- @@ L197-197 verbatim
local notation "𝔠" => fun η ↦ divZetaSubOneDvdGcd hp hζ e hy η


-- @@ L199-201 expanded
lemma div_zeta_sub_one_dvd_gcd_spec :
    gcd (Ideal.span { x }) (Ideal.span { y }) * (fun η ↦ divZetaSubOneDvdGcd hp hζ e hy η) η =
      (Ideal.span <| singleton <| divZetaSubOne hp hζ e η) :=
  (gcd_div_div_zeta_sub_one hp hζ e hy η).choose_spec.symm


-- @@ L203-205 expanded
lemma m_mul_c_mul_p :
    gcd (Ideal.span { x }) (Ideal.span { y }) * (fun η ↦ divZetaSubOneDvdGcd hp hζ e hy η) η *
        Ideal.span {hζ.toInteger - 1} =
      Ideal.span {(x + y * η : 𝓞 K)} :=
  by
  rw [div_zeta_sub_one_dvd_gcd_spec, Ideal.span_singleton_mul_span_singleton,
    div_zeta_sub_one_mul_zeta_sub_one]


-- @@ L207-210 expanded
omit [NumberField K] [IsCyclotomicExtension { p } ℚ K] in
lemma p_ne_zero : Ideal.span {hζ.toInteger - 1} ≠ 0 :=
  by
  rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  exact hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero hpri.out.one_lt


-- @@ L212-217 expanded
lemma coprime_c (η₁ η₂ : nthRootsFinset p (1 : 𝓞 K)) (hη : η₁ ≠ η₂) :
    IsCoprime ((fun η ↦ divZetaSubOneDvdGcd hp hζ e hy η) η₁)
      ((fun η ↦ divZetaSubOneDvdGcd hp hζ e hy η) η₂) :=
  by
  rw [Ideal.isCoprime_iff_codisjoint, codisjoint_iff_le_sup, ← Ideal.dvd_iff_le]
  rw [← mul_dvd_mul_iff_left (m_ne_zero hζ hy), ← mul_dvd_mul_iff_right (p_ne_zero hζ)]
  rw [Ideal.mul_sup, Ideal.sup_mul, m_mul_c_mul_p, m_mul_c_mul_p, Ideal.mul_top]
  exact coprime_c_aux hζ η₁ η₂ hη


-- @@ L219-223 expanded
include hy in
lemma gcd_m_p_pow_eq_one :
    gcd (gcd (Ideal.span { x }) (Ideal.span { y })) (Ideal.span {hζ.toInteger - 1} ^ (m + 1)) = 1 :=
  by
  rw [← Ideal.isCoprime_iff_gcd, IsCoprime.pow_right_iff, Ideal.isCoprime_iff_gcd,
    gcd_zeta_sub_one_eq_one hζ hy]
  simp only [add_pos_iff, or_true, one_pos]


-- @@ L225-232 expanded
include hζ m hy e in
lemma m_dvd_z : gcd (Ideal.span { x }) (Ideal.span { y }) ∣ Ideal.span { z } :=
  by
  rw [← one_mul (Ideal.span { z }), ← gcd_m_p_pow_eq_one hζ hy (x := x) (m := m)]
  apply dvd_gcd_mul_of_dvd_mul
  rw [← UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd hpri.out.ne_zero, ← span_pow_add_pow_eq hζ e,
    Ideal.dvd_span_singleton]
  exact
    add_mem (Ideal.pow_mem_pow (Ideal.mem_sup_left (Ideal.mem_span_singleton_self x)) p)
      (Ideal.pow_mem_pow (Ideal.mem_sup_right (Ideal.mem_span_singleton_self y)) p)


-- @@ L234-236 verbatim
/-- The ideal quotient witnessing `𝔷 = 𝔪 * zDivM`. -/
noncomputable def zDivM : Ideal (𝓞 K) :=
  (m_dvd_z hζ e hy).choose


-- @@ L238-238 verbatim
local notation "𝔷'" => zDivM hζ e hy


-- @@ L240-241 expanded
lemma z_div_m_spec : Ideal.span { z } = gcd (Ideal.span { x }) (Ideal.span { y }) * zDivM hζ e hy :=
  (m_dvd_z hζ e hy).choose_spec


-- @@ L243-246 expanded
lemma exists_ideal_pow_eq_c_aux :
    gcd (Ideal.span { x }) (Ideal.span { y }) ^ p *
          (zDivM hζ e hy * Ideal.span {hζ.toInteger - 1} ^ m) ^ p *
        Ideal.span {hζ.toInteger - 1} ^ p =
      (Ideal.span {hζ.toInteger - 1} ^ (m + 1) * Ideal.span { z }) ^ p :=
  by
  rw [mul_comm _ (Ideal.span { z }), mul_pow, z_div_m_spec hζ e hy, mul_pow, mul_pow, ← pow_mul, ←
    pow_mul, add_mul, one_mul, pow_add, mul_assoc, mul_assoc, mul_assoc]


-- @@ L248-260 expanded
lemma prod_c :
    ∏ η ∈ Finset.attach (nthRootsFinset p (1 : 𝓞 K)), (fun η ↦ divZetaSubOneDvdGcd hp hζ e hy η) η =
      (zDivM hζ e hy * Ideal.span {hζ.toInteger - 1} ^ m) ^ p :=
  by
  have e' := span_pow_add_pow_eq hζ e
  rw [hζ.toInteger_isPrimitiveRoot.pow_add_pow_eq_prod_add_mul _ _ <|
      Nat.odd_iff.2 <| hpri.out.eq_two_or_odd.resolve_left hp] at e'
  rw [← Ideal.prod_span_singleton, ← Finset.prod_attach] at e'
  simp_rw [mul_comm _ y, ← m_mul_c_mul_p hp hζ e hy, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_attach, hζ.toInteger_isPrimitiveRoot.card_nthRootsFinset] at e'
  rw [← mul_right_inj' ((pow_ne_zero_iff hpri.out.ne_zero).mpr (m_ne_zero hζ hy) : _), ←
    mul_left_inj' ((pow_ne_zero_iff hpri.out.ne_zero).mpr (p_ne_zero hζ) : _), e',
    exists_ideal_pow_eq_c_aux]


-- @@ L262-265 expanded
lemma exists_ideal_pow_eq_c :
    ∃ I : Ideal (𝓞 K), ((fun η ↦ divZetaSubOneDvdGcd hp hζ e hy η) η) = I ^ p :=
  Finset.exists_eq_pow_of_mul_eq_pow_of_coprime (fun η₁ _ η₂ _ hη ↦ coprime_c hp hζ e hy η₁ η₂ hη)
    (prod_c hp hζ e hy) η (Finset.mem_attach _ _)


-- @@ L267-269 verbatim
/-- A `p`-th ideal root of `𝔠 η`. -/
noncomputable def rootDivZetaSubOneDvdGcd : Ideal (𝓞 K) :=
  (exists_ideal_pow_eq_c hp hζ e hy η).choose


-- @@ L271-271 verbatim
local notation "𝔞" => rootDivZetaSubOneDvdGcd hp hζ e hy


-- @@ L273-274 expanded
lemma root_div_zeta_sub_one_dvd_gcd_spec :
    ((rootDivZetaSubOneDvdGcd hp hζ e hy) η) ^ p = (fun η ↦ divZetaSubOneDvdGcd hp hζ e hy η) η :=
  (exists_ideal_pow_eq_c hp hζ e hy η).choose_spec.symm


-- @@ L276-283 expanded
lemma c_div_principal_aux (η₁ η₂ : nthRootsFinset p (1 : 𝓞 K)) :
    ((Ideal.span {(x + y * η₁ : 𝓞 K)}) / (Ideal.span {(x + y * η₂ : 𝓞 K)}) :
        FractionalIdeal (𝓞 K)⁰ K) =
      (fun η ↦ divZetaSubOneDvdGcd hp hζ e hy η) η₁ /
        (fun η ↦ divZetaSubOneDvdGcd hp hζ e hy η) η₂ :=
  by
  simp_rw [← m_mul_c_mul_p hp hζ e hy, FractionalIdeal.coeIdeal_mul]
  rw [mul_div_mul_right, mul_div_mul_left]
  · rw [← FractionalIdeal.coeIdeal_bot, (FractionalIdeal.coeIdeal_injective' le_rfl).ne_iff]
    exact m_ne_zero hζ hy
  · rw [← FractionalIdeal.coeIdeal_bot, (FractionalIdeal.coeIdeal_injective' le_rfl).ne_iff]
    exact p_ne_zero hζ


-- @@ L285-290 expanded
lemma c_div_principal (η₁ η₂ : nthRootsFinset p (1 : 𝓞 K)) :
    Submodule.IsPrincipal
      (((fun η ↦ divZetaSubOneDvdGcd hp hζ e hy η) η₁ /
            (fun η ↦ divZetaSubOneDvdGcd hp hζ e hy η) η₂ :
          FractionalIdeal (𝓞 K)⁰ K) :
        Submodule (𝓞 K) K) :=
  by
  rw [← c_div_principal_aux, FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_div_spanSingleton,
    FractionalIdeal.coe_spanSingleton]
  exact ⟨⟨_, rfl⟩⟩


-- @@ L292-294 verbatim
/-- The unique root of unity whose quotient is divisible by `ζ - 1`. -/
noncomputable def zetaSubOneDvdRoot : nthRootsFinset p (1 : 𝓞 K) :=
  (Equiv.ofBijective _ (div_zeta_sub_one_Bijective hp hζ e hy)).symm 0


-- @@ L296-296 verbatim
local notation "η₀" => zetaSubOneDvdRoot hp hζ e hy


-- @@ L298-299 expanded
lemma zeta_sub_one_dvd_root_spec :
    Ideal.Quotient.mk (Ideal.span {hζ.toInteger - 1})
        (divZetaSubOne hp hζ e (zetaSubOneDvdRoot hp hζ e hy)) =
      0 :=
  Equiv.ofBijective_apply_symm_apply _ (div_zeta_sub_one_Bijective hp hζ e hy) 0


-- @@ L301-305 expanded
lemma p_dvd_c_iff :
    Ideal.span {hζ.toInteger - 1} ∣ ((fun η ↦ divZetaSubOneDvdGcd hp hζ e hy η) η) ↔
      η = zetaSubOneDvdRoot hp hζ e hy :=
  by
  rw [← (div_zeta_sub_one_Injective hp hζ e hy).eq_iff, zeta_sub_one_dvd_root_spec,
    Ideal.Quotient.eq_zero_iff_dvd, ← Ideal.mem_span_singleton («α» := 𝓞 K), ←
    Ideal.dvd_span_singleton, ← div_zeta_sub_one_dvd_gcd_spec (hy := hy), ← dvd_gcd_mul_iff_dvd_mul,
    gcd_comm, gcd_zeta_sub_one_eq_one hζ hy, one_mul]


-- @@ L307-317 expanded
lemma p_pow_dvd_c_eta_zero_aux [DecidableEq (𝓞 K)] :
    gcd (Ideal.span {hζ.toInteger - 1} ^ (m * p))
        (∏ η ∈ Finset.attach (nthRootsFinset p (1 : 𝓞 K)) \ {zetaSubOneDvdRoot hp hζ e hy},
          (fun η ↦ divZetaSubOneDvdGcd hp hζ e hy η) η) =
      1 :=
  by
  rw [← Ideal.isCoprime_iff_gcd]
  apply IsCoprime.pow_left
  rw [Ideal.isCoprime_iff_gcd,
    (Ideal.prime_span_singleton_iff.mpr hζ.zeta_sub_one_prime').irreducible.gcd_eq_one_iff,
    (Ideal.prime_span_singleton_iff.mpr hζ.zeta_sub_one_prime').dvd_finsetProd_iff]
  rintro ⟨η, hη, h⟩
  rw [p_dvd_c_iff] at h
  simp only [Finset.mem_sdiff, Finset.mem_singleton] at hη
  exact hη.2 h


-- @@ L319-321 expanded
lemma p_dvd_a_iff :
    Ideal.span {hζ.toInteger - 1} ∣ (rootDivZetaSubOneDvdGcd hp hζ e hy) η ↔
      η = zetaSubOneDvdRoot hp hζ e hy :=
  by
  rw [← p_dvd_c_iff hp hζ e hy, ← root_div_zeta_sub_one_dvd_gcd_spec,
    (Ideal.prime_span_singleton_iff.mpr hζ.zeta_sub_one_prime').dvd_pow_iff_dvd hpri.out.ne_zero]


-- @@ L323-330 expanded
lemma p_pow_dvd_c_eta_zero :
    Ideal.span {hζ.toInteger - 1} ^ (m * p) ∣
      (fun η ↦ divZetaSubOneDvdGcd hp hζ e hy η) (zetaSubOneDvdRoot hp hζ e hy) :=
  by
  classical
  rw [← one_mul ((fun η ↦ divZetaSubOneDvdGcd hp hζ e hy η) (zetaSubOneDvdRoot hp hζ e hy)), ←
    p_pow_dvd_c_eta_zero_aux hp hζ e hy, dvd_gcd_mul_iff_dvd_mul,
    mul_comm _ ((fun η ↦ divZetaSubOneDvdGcd hp hζ e hy η) (zetaSubOneDvdRoot hp hζ e hy))]
  rw [←
    Finset.prod_eq_mul_prod_sdiff_singleton_of_mem
      (Finset.mem_attach _ (zetaSubOneDvdRoot hp hζ e hy)) fun η ↦ divZetaSubOneDvdGcd hp hζ e hy η,
    prod_c, mul_pow]
  apply dvd_mul_of_dvd_right
  rw [pow_mul]


-- @@ L332-335 expanded
lemma p_pow_dvd_a_eta_zero :
    Ideal.span {hζ.toInteger - 1} ^ m ∣
      (rootDivZetaSubOneDvdGcd hp hζ e hy) (zetaSubOneDvdRoot hp hζ e hy) :=
  by
  rw [← UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd hpri.out.ne_zero,
    root_div_zeta_sub_one_dvd_gcd_spec, ← pow_mul]
  exact p_pow_dvd_c_eta_zero hp hζ e hy


-- @@ L337-339 verbatim
/-- The quotient ideal after removing `𝔭 ^ m` from the distinguished ideal root. -/
noncomputable def aEtaZeroDvdPPow : Ideal (𝓞 K) :=
  (p_pow_dvd_a_eta_zero hp hζ e hy).choose


-- @@ L341-341 verbatim
local notation "𝔞₀" => aEtaZeroDvdPPow hp hζ e hy


-- @@ L343-344 expanded
lemma a_eta_zero_dvd_p_pow_spec :
    Ideal.span {hζ.toInteger - 1} ^ m * aEtaZeroDvdPPow hp hζ e hy =
      (rootDivZetaSubOneDvdGcd hp hζ e hy) (zetaSubOneDvdRoot hp hζ e hy) :=
  (p_pow_dvd_a_eta_zero hp hζ e hy).choose_spec.symm


-- @@ L346-360 expanded
include hz in
lemma not_p_div_a_zero : ¬Ideal.span {hζ.toInteger - 1} ∣ aEtaZeroDvdPPow hp hζ e hy :=
  by
  intro h
  have := pow_dvd_pow_of_dvd (mul_dvd_mul (dvd_refl (Ideal.span {hζ.toInteger - 1} ^ m)) h) p
  rw [a_eta_zero_dvd_p_pow_spec, root_div_zeta_sub_one_dvd_gcd_spec] at this
  have :=
    this.trans
      (Finset.dvd_prod_of_mem (fun η ↦ divZetaSubOneDvdGcd hp hζ e hy η)
        (Finset.mem_attach _ (zetaSubOneDvdRoot hp hζ e hy)))
  rw [prod_c, mul_pow, mul_pow, mul_comm, mul_dvd_mul_iff_right,
    UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd hpri.out.ne_zero] at this
  · apply hz
    rw [← Ideal.mem_span_singleton, ← Ideal.dvd_span_singleton, z_div_m_spec hζ e hy]
    exact this.trans (dvd_mul_left _ _)
  · apply mt eq_zero_of_pow_eq_zero
    apply mt eq_zero_of_pow_eq_zero
    rw [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero hpri.out.one_lt


-- @@ L362-369 expanded
include hp hζ e hy hz in
lemma one_le_m : 1 ≤ m := by
  apply Nat.one_le_iff_ne_zero.mpr
  intro hm
  apply not_p_div_a_zero hp hζ e hy hz
  have hdiv := (p_dvd_a_iff hp hζ e hy (zetaSubOneDvdRoot hp hζ e hy)).mpr rfl
  rw [← a_eta_zero_dvd_p_pow_spec] at hdiv
  simpa [hm] using hdiv


-- @@ L371-388 expanded
include hp in
lemma exists_solution'_aux {ε₁ ε₂ : (𝓞 K)ˣ} (hx : ¬hζ.toInteger - 1 ∣ x)
    (h : (p : 𝓞 K) ∣ ε₁ * x ^ p + ε₂ * y ^ p) : ∃ a : 𝓞 K, ↑p ∣ ↑(ε₁ / ε₂) - a ^ p :=
  by
  obtain ⟨a, b, e⟩ : IsCoprime (↑p) x := isCoprime_of_not_zeta_sub_one_dvd _ hζ hx
  have : (p : 𝓞 K) ∣ b * x - 1 := by
    use -a
    rw [← e]
    ring
  have := (this.trans (sub_one_dvd_pow_sub_one _ p)).trans (dvd_mul_left _ ↑(ε₁ / ε₂))
  use -y * b
  replace h := (h.trans (dvd_mul_right _ (b ^ p))).trans (dvd_mul_left _ ↑(ε₂⁻¹))
  rw [add_mul, mul_assoc, mul_assoc, ← mul_pow, ← mul_pow, mul_add] at h
  simp_rw [← mul_assoc, ← Units.val_mul] at h
  rw [← mul_comm ε₁, ← div_eq_mul_inv, inv_mul_cancel, Units.val_one, one_mul] at h
  convert dvd_sub h this using 1
  rw [neg_mul, (Nat.Prime.odd_of_ne_two hpri.out hp).neg_pow, sub_neg_eq_add, mul_sub, mul_one,
    mul_comm x b, add_sub_sub_cancel, add_comm]


-- @@ L390-390 verbatim
variable [Fintype (ClassGroup (𝓞 K))] (hreg : p.Coprime <| Fintype.card <| ClassGroup (𝓞 K))


-- @@ L392-398 expanded
include hreg in
lemma a_div_principal (η₁ η₂ : nthRootsFinset p (1 : 𝓞 K)) :
    Submodule.IsPrincipal
      (((rootDivZetaSubOneDvdGcd hp hζ e hy) η₁ / (rootDivZetaSubOneDvdGcd hp hζ e hy) η₂ :
          FractionalIdeal (𝓞 K)⁰ K) :
        Submodule (𝓞 K) K) :=
  by
  apply FractionalIdeal.isPrincipal.of_isPrincipal_pow_of_coprime hreg
  rw [div_pow, ← FractionalIdeal.coeIdeal_pow, ← FractionalIdeal.coeIdeal_pow,
    root_div_zeta_sub_one_dvd_gcd_spec, root_div_zeta_sub_one_dvd_gcd_spec]
  exact c_div_principal hp hζ e hy η₁ η₂


-- @@ L400-415 expanded
include hreg in
lemma isPrincipal_a_div_a_zero :
    Submodule.IsPrincipal
      (((rootDivZetaSubOneDvdGcd hp hζ e hy) η / aEtaZeroDvdPPow hp hζ e hy :
          FractionalIdeal (𝓞 K)⁰ K) :
        Submodule (𝓞 K) K) :=
  by
  have := a_div_principal hp hζ e hy hreg η (zetaSubOneDvdRoot hp hζ e hy)
  rw [← a_eta_zero_dvd_p_pow_spec, mul_comm, FractionalIdeal.coeIdeal_mul, ← div_div,
    FractionalIdeal.isPrincipal_iff] at this
  obtain ⟨a, ha⟩ := this
  rw [div_eq_iff, Ideal.span_singleton_pow, FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.spanSingleton_mul_spanSingleton] at ha
  · rw [FractionalIdeal.isPrincipal_iff]
    exact ⟨_, ha⟩
  · rw [← FractionalIdeal.coeIdeal_bot,
      (FractionalIdeal.coeIdeal_injective' (le_rfl : (𝓞 K)⁰ ≤ (𝓞 K)⁰)).ne_iff]
    apply mt eq_zero_of_pow_eq_zero
    rw [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero hpri.out.one_lt


-- @@ L417-423 expanded
include hz hreg in
lemma exists_not_dvd_spanSingleton_eq_a_div_a_zero (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy) :
    ∃ a b : 𝓞 K,
      ¬hζ.toInteger - 1 ∣ a ∧
        ¬hζ.toInteger - 1 ∣ b ∧
          FractionalIdeal.spanSingleton (𝓞 K)⁰ (a / b : K) =
            (rootDivZetaSubOneDvdGcd hp hζ e hy) η / aEtaZeroDvdPPow hp hζ e hy :=
  exists_not_dvd_spanSingleton_eq hζ.zeta_sub_one_prime' _ _ ((p_dvd_a_iff hp hζ e hy η).not.mpr hη)
    (not_p_div_a_zero hp hζ e hy hz) (isPrincipal_a_div_a_zero hp hζ e hy η hreg)


-- @@ L425-427 expanded
/-- A numerator for the principal fractional ideal `𝔞 η / 𝔞₀`. -/
noncomputable def aDivAZeroNum (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy) : 𝓞 K :=
  (exists_not_dvd_spanSingleton_eq_a_div_a_zero hp hζ e hy hz η hreg hη).choose


-- @@ L429-431 expanded
/-- A denominator for the principal fractional ideal `𝔞 η / 𝔞₀`. -/
noncomputable def aDivAZeroDenom (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy) : 𝓞 K :=
  (exists_not_dvd_spanSingleton_eq_a_div_a_zero hp hζ e hy hz η hreg hη).choose_spec.choose


-- @@ L433-433 verbatim
local notation "α" => fun η ↦ aDivAZeroNum hp hζ e hy hz η hreg

-- @@ L434-434 verbatim
local notation "β" => fun η ↦ aDivAZeroDenom hp hζ e hy hz η hreg


-- @@ L436-440 expanded
include hreg in
lemma a_div_a_zero_num_spec (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy) :
    ¬hζ.toInteger - 1 ∣ (fun η ↦ aDivAZeroNum hp hζ e hy hz η hreg) η hη :=
  And.left <|
    (exists_not_dvd_spanSingleton_eq_a_div_a_zero hp hζ e hy hz η hreg hη).choose_spec.choose_spec


-- @@ L442-446 expanded
include hreg in
lemma a_div_a_zero_denom_spec (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy) :
    ¬hζ.toInteger - 1 ∣ (fun η ↦ aDivAZeroDenom hp hζ e hy hz η hreg) η hη :=
  And.left <|
    And.right <|
      (exists_not_dvd_spanSingleton_eq_a_div_a_zero hp hζ e hy hz η hreg hη).choose_spec.choose_spec


-- @@ L448-452 expanded
lemma a_div_a_zero_eq (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy) :
    FractionalIdeal.spanSingleton (𝓞 K)⁰
        ((fun η ↦ aDivAZeroNum hp hζ e hy hz η hreg) η hη /
            (fun η ↦ aDivAZeroDenom hp hζ e hy hz η hreg) η hη :
          K) =
      (rootDivZetaSubOneDvdGcd hp hζ e hy) η / aEtaZeroDvdPPow hp hζ e hy :=
  And.right <|
    And.right <|
      (exists_not_dvd_spanSingleton_eq_a_div_a_zero hp hζ e hy hz η hreg hη).choose_spec.choose_spec


-- @@ L454-471 expanded
lemma a_mul_denom_eq_a_zero_mul_num (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy) :
    (rootDivZetaSubOneDvdGcd hp hζ e hy) η *
        Ideal.span {(fun η ↦ aDivAZeroDenom hp hζ e hy hz η hreg) η hη} =
      aEtaZeroDvdPPow hp hζ e hy * Ideal.span {(fun η ↦ aDivAZeroNum hp hζ e hy hz η hreg) η hη} :=
  by
  apply FractionalIdeal.coeIdeal_injective (K := K)
  simp only [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton]
  rw [mul_comm (aEtaZeroDvdPPow hp hζ e hy : FractionalIdeal (𝓞 K)⁰ K), ← div_eq_div_iff, ←
    a_div_a_zero_eq hp hζ e hy hz η hreg hη, FractionalIdeal.spanSingleton_div_spanSingleton]
  · intro ha
    rw [FractionalIdeal.coeIdeal_eq_zero] at ha
    apply not_p_div_a_zero hp hζ e hy hz
    rw [ha]
    exact dvd_zero _
  · rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff, ← (algebraMap (𝓞 K) K).map_zero,
      (IsFractionRing.injective (𝓞 K) K).eq_iff]
    intro hβ
    apply a_div_a_zero_denom_spec hp hζ e hy hz η hreg hη
    simp only
    rw [hβ]
    exact dvd_zero _


-- @@ L473-482 expanded
lemma associated_eta_zero (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy) :
    Associated
      ((x + y * zetaSubOneDvdRoot hp hζ e hy) *
        (fun η ↦ aDivAZeroNum hp hζ e hy hz η hreg) η hη ^ p)
      ((x + y * η) * (hζ.toInteger - 1) ^ (m * p) *
        (fun η ↦ aDivAZeroDenom hp hζ e hy hz η hreg) η hη ^ p) :=
  by
  simp_rw [← Ideal.span_singleton_eq_span_singleton, ← Ideal.span_singleton_mul_span_singleton, ←
    Ideal.span_singleton_pow, ← m_mul_c_mul_p hp hζ e hy, ← root_div_zeta_sub_one_dvd_gcd_spec, ←
    a_eta_zero_dvd_p_pow_spec]
  rw [mul_comm _ (aEtaZeroDvdPPow hp hζ e hy), mul_pow]
  simp only [mul_assoc, mul_left_comm _ (Ideal.span {hζ.toInteger - 1})]
  rw [mul_left_comm ((rootDivZetaSubOneDvdGcd hp hζ e hy) η ^ p),
    mul_left_comm (aEtaZeroDvdPPow hp hζ e hy ^ p), ← pow_mul, ← mul_pow, ← mul_pow,
    a_mul_denom_eq_a_zero_mul_num]


-- @@ L484-486 expanded
/-- The unit witnessing the association in `associated_eta_zero`. -/
noncomputable def associatedEtaZeroUnit (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy) : (𝓞 K)ˣ :=
  (associated_eta_zero hp hζ e hy hz η hreg hη).choose


-- @@ L488-488 verbatim
local notation "ε" => fun η ↦ associatedEtaZeroUnit hp hζ e hy hz η hreg


-- @@ L490-493 expanded
lemma associated_eta_zero_unit_spec (η) (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy) :
    (fun η ↦ associatedEtaZeroUnit hp hζ e hy hz η hreg) η hη *
          (x + y * zetaSubOneDvdRoot hp hζ e hy) *
        (fun η ↦ aDivAZeroNum hp hζ e hy hz η hreg) η hη ^ p =
      (x + y * η) * (hζ.toInteger - 1) ^ (m * p) *
        (fun η ↦ aDivAZeroDenom hp hζ e hy hz η hreg) η hη ^ p :=
  by
  rw [mul_assoc, mul_comm ((fun η ↦ associatedEtaZeroUnit hp hζ e hy hz η hreg) η hη : 𝓞 K)]
  exact (associated_eta_zero hp hζ e hy hz η hreg hη).choose_spec


-- @@ L495-507 expanded
lemma formula (η₁) (hη₁ : η₁ ≠ zetaSubOneDvdRoot hp hζ e hy) (η₂)
    (hη₂ : η₂ ≠ zetaSubOneDvdRoot hp hζ e hy) :
    (η₂ - zetaSubOneDvdRoot hp hζ e hy : 𝓞 K) *
            (fun η ↦ associatedEtaZeroUnit hp hζ e hy hz η hreg) η₁ hη₁ *
          ((fun η ↦ aDivAZeroNum hp hζ e hy hz η hreg) η₁ hη₁ *
              (fun η ↦ aDivAZeroDenom hp hζ e hy hz η hreg) η₂ hη₂) ^
            p +
        (zetaSubOneDvdRoot hp hζ e hy - η₁) *
            (fun η ↦ associatedEtaZeroUnit hp hζ e hy hz η hreg) η₂ hη₂ *
          ((fun η ↦ aDivAZeroNum hp hζ e hy hz η hreg) η₂ hη₂ *
              (fun η ↦ aDivAZeroDenom hp hζ e hy hz η hreg) η₁ hη₁) ^
            p =
      (η₂ - η₁) *
        ((hζ.toInteger - 1) ^ m *
            ((fun η ↦ aDivAZeroDenom hp hζ e hy hz η hreg) η₁ hη₁ *
              (fun η ↦ aDivAZeroDenom hp hζ e hy hz η hreg) η₂ hη₂)) ^
          p :=
  by
  rw [← mul_right_inj' (x_plus_y_mul_ne_zero hp hζ e hz (zetaSubOneDvdRoot hp hζ e hy)), mul_add]
  simp_rw [mul_left_comm (x + y * zetaSubOneDvdRoot hp hζ e hy), mul_pow, mul_assoc,
    mul_left_comm (η₂ - zetaSubOneDvdRoot hp hζ e hy : 𝓞 K),
    mul_left_comm (zetaSubOneDvdRoot hp hζ e hy - η₁ : 𝓞 K), ← mul_assoc,
    associated_eta_zero_unit_spec, mul_assoc, ←
    mul_left_comm (η₂ - zetaSubOneDvdRoot hp hζ e hy : 𝓞 K), ←
    mul_left_comm (zetaSubOneDvdRoot hp hζ e hy - η₁ : 𝓞 K), pow_mul, ← mul_pow,
    mul_comm ((fun η ↦ aDivAZeroDenom hp hζ e hy hz η hreg) η₂ hη₂), ← mul_assoc]
  rw [← add_mul]
  congr 1
  ring


-- @@ L509-566 expanded
include hreg e hy hz hp in
lemma exists_solution :
    ∃ (x' y' z' : 𝓞 K) (ε₁ ε₂ ε₃ : (𝓞 K)ˣ),
      ¬hζ.toInteger - 1 ∣ x' ∧
        ¬hζ.toInteger - 1 ∣ y' ∧
          ¬hζ.toInteger - 1 ∣ z' ∧
            ε₁ * x' ^ p + ε₂ * y' ^ p = ε₃ * ((hζ.toInteger - 1) ^ m * z') ^ p :=
  by
  have h₁ :=
    mul_mem_nthRootsFinset (zetaSubOneDvdRoot hp hζ e hy : _).prop
      (hζ.toInteger_isPrimitiveRoot.mem_nthRootsFinset hpri.out.pos)
  rw [one_mul] at h₁
  let η₁ : nthRootsFinset p (1 : 𝓞 K) := ⟨zetaSubOneDvdRoot hp hζ e hy * hζ.toInteger, h₁⟩
  have h₂ :=
    mul_mem_nthRootsFinset (η₁ : _).prop
      (hζ.toInteger_isPrimitiveRoot.mem_nthRootsFinset hpri.out.pos)
  rw [one_mul] at h₂
  let η₂ : nthRootsFinset p (1 : 𝓞 K) :=
    ⟨zetaSubOneDvdRoot hp hζ e hy * hζ.toInteger * hζ.toInteger, h₂⟩
  have hη₁ : η₁ ≠ zetaSubOneDvdRoot hp hζ e hy :=
    by
    rw [← Subtype.coe_injective.ne_iff]
    change (zetaSubOneDvdRoot hp hζ e hy * hζ.toInteger : 𝓞 K) ≠ zetaSubOneDvdRoot hp hζ e hy
    rw [Ne, mul_right_eq_self₀, not_or]
    exact
      ⟨hζ.toInteger_isPrimitiveRoot.ne_one hpri.out.one_lt,
        ne_zero_of_mem_nthRootsFinset one_ne_zero (zetaSubOneDvdRoot hp hζ e hy : _).prop⟩
  have hη₂ : η₂ ≠ zetaSubOneDvdRoot hp hζ e hy :=
    by
    rw [← Subtype.coe_injective.ne_iff]
    change
      (zetaSubOneDvdRoot hp hζ e hy * hζ.toInteger * hζ.toInteger : 𝓞 K) ≠
        zetaSubOneDvdRoot hp hζ e hy
    rw [Ne, mul_assoc, ← pow_two, mul_right_eq_self₀, not_or]
    exact
      ⟨hζ.toInteger_isPrimitiveRoot.pow_ne_one_of_pos_of_lt (by omega)
          (hpri.out.two_le.lt_or_eq.resolve_right hp.symm),
        ne_zero_of_mem_nthRootsFinset one_ne_zero (zetaSubOneDvdRoot hp hζ e hy : _).prop⟩
  have hη : η₂ ≠ η₁ := by
    rw [← Subtype.coe_injective.ne_iff]
    change
      (zetaSubOneDvdRoot hp hζ e hy * hζ.toInteger * hζ.toInteger : 𝓞 K) ≠
        zetaSubOneDvdRoot hp hζ e hy * hζ.toInteger
    rw [Ne, mul_right_eq_self₀, not_or]
    exact
      ⟨hζ.toInteger_isPrimitiveRoot.ne_one hpri.out.one_lt,
        mul_ne_zero
          (ne_zero_of_mem_nthRootsFinset one_ne_zero (zetaSubOneDvdRoot hp hζ e hy : _).prop)
          (hζ.toInteger_isPrimitiveRoot.ne_zero hpri.out.ne_zero)⟩
  obtain ⟨u₁, hu₁⟩ :=
    hζ.toInteger_isPrimitiveRoot.nthRootsFinset_pairwise_associated_sub_one_sub_of_prime hpri.out
      η₂.prop (zetaSubOneDvdRoot hp hζ e hy : _).prop (Subtype.coe_injective.ne_iff.mpr hη₂)
  obtain ⟨u₂, hu₂⟩ :=
    hζ.toInteger_isPrimitiveRoot.nthRootsFinset_pairwise_associated_sub_one_sub_of_prime hpri.out
      (zetaSubOneDvdRoot hp hζ e hy : _).prop η₁.prop (Subtype.coe_injective.ne_iff.mpr hη₁.symm)
  obtain ⟨u₃, hu₃⟩ :=
    hζ.toInteger_isPrimitiveRoot.nthRootsFinset_pairwise_associated_sub_one_sub_of_prime hpri.out
      η₂.prop (η₁ : _).prop (Subtype.coe_injective.ne_iff.mpr hη)
  have := formula hp hζ e hy hz hreg η₁ hη₁ η₂ hη₂
  rw [← hu₁, ← hu₂, ← hu₃, mul_assoc _ (u₁ : 𝓞 K), mul_assoc _ (u₂ : 𝓞 K), mul_assoc _ (u₃ : 𝓞 K),
    mul_assoc (hζ.toInteger - 1), mul_assoc (hζ.toInteger - 1), ← mul_add,
    mul_right_inj' (hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero hpri.out.one_lt), ← Units.val_mul,
    ← Units.val_mul] at this
  refine ⟨_, _, _, _, _, _, ?_, ?_, ?_, this⟩
  ·
    exact
      hζ.zeta_sub_one_prime'.not_dvd_mul (a_div_a_zero_num_spec hp hζ e hy hz η₁ hreg hη₁)
        (a_div_a_zero_denom_spec hp hζ e hy hz η₂ hreg hη₂)
  ·
    exact
      hζ.zeta_sub_one_prime'.not_dvd_mul (a_div_a_zero_num_spec hp hζ e hy hz η₂ hreg hη₂)
        (a_div_a_zero_denom_spec hp hζ e hy hz η₁ hreg hη₁)
  ·
    exact
      hζ.zeta_sub_one_prime'.not_dvd_mul (a_div_a_zero_denom_spec hp hζ e hy hz η₁ hreg hη₁)
        (a_div_a_zero_denom_spec hp hζ e hy hz η₂ hreg hη₂)


-- @@ L568-592 expanded
include hp hreg e hy hz in
lemma exists_solution' :
    ∃ (x' y' z' : 𝓞 K) (ε₃ : (𝓞 K)ˣ),
      ¬hζ.toInteger - 1 ∣ y' ∧
        ¬hζ.toInteger - 1 ∣ z' ∧ x' ^ p + y' ^ p = ε₃ * ((hζ.toInteger - 1) ^ m * z') ^ p :=
  by
  obtain ⟨x', y', z', ε₁, ε₂, ε₃, hx', hy', hz', e'⟩ := exists_solution hp hζ e hy hz hreg
  obtain ⟨ε', hε'⟩ : ∃ ε', ε₁ / ε₂ = ε' ^ p :=
    by
    apply eq_pow_prime_of_unit_of_congruent hp hreg
    have : p - 1 ≤ m * p :=
      (Nat.sub_le _ _).trans
        ((le_of_eq (one_mul _).symm).trans (Nat.mul_le_mul_right p (one_le_m hp hζ e hy hz)))
    obtain ⟨u, hu⟩ := (associated_zeta_sub_one_pow_prime _ hζ).symm
    rw [mul_pow, ← pow_mul, mul_comm (ε₃ : 𝓞 K), mul_assoc, ← Nat.sub_add_cancel this,
      add_comm _ (p - 1), pow_add, mul_assoc] at e'
    apply_fun Ideal.Quotient.mk (Ideal.span <| singleton (p : 𝓞 K)) at e'
    rw [map_mul,
      (Ideal.Quotient.eq_zero_iff_dvd _ _).mpr (associated_zeta_sub_one_pow_prime _ hζ).symm.dvd,
      zero_mul, Ideal.Quotient.eq_zero_iff_dvd] at e'
    obtain ⟨a, ha⟩ := exists_solution'_aux hp hζ hx' e'
    obtain ⟨b, hb⟩ := exists_dvd_pow_sub_Int_pow hp a
    have := dvd_add ha hb
    rw [sub_add_sub_cancel, ← Int.cast_pow] at this
    exact ⟨b ^ p, this⟩
  refine ⟨ε' * x', y', z', ε₃ / ε₂, hy', hz', ?_⟩
  rwa [mul_pow, ← Units.val_pow_eq_pow_val, ← hε', ← mul_right_inj' ε₂.isUnit.ne_zero, mul_add, ←
    mul_assoc, ← Units.val_mul, mul_div_cancel, ← mul_assoc, ← Units.val_mul, mul_div_cancel]

