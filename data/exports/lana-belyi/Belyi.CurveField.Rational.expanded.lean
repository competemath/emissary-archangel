/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.CurveField.Point
import Belyi.CurveField.Degree
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.RingTheory.Polynomial.IsIntegral


-- @@ L11-42 verbatim
/-!
# The rational function field: the projective line

Let `K` be a field of characteristic `0` and `t ∈ K` transcendental over `ℚ` with
`ℚ⟮t⟯ = K`, i.e. `K = ℚ(t)` is the function field of `ℙ¹_ℚ` with coordinate `t`
(`Belyi.CurveField.IsRationalGenerator t`). We describe the places and the algebraic points
of `ℙ¹` in terms of the coordinate `t`.

Every `f ∈ K` is a reduced fraction `p(t) / q(t)` with `p, q ∈ ℚ[X]` coprime, `q ≠ 0`
(`Belyi.CurveField.IsRationalGenerator.exists_coprime`). For an algebraic point `x` with
`t` regular at `x` and `z = t(x) ∈ ℚ̄`, the function `p(t)/q(t)` is regular at `x` iff
`q(z) ≠ 0`, and then its value is `p(z)/q(z)`. Consequently the points with `t` regular are
in bijection with `ℚ̄` via `x ↦ t(x)`, and `ℚ(x) = ℚ(t(x))`.

## Main definitions and results

* `Belyi.CurveField.IsRationalGenerator t`: `t` is transcendental and `ℚ⟮t⟯ = ⊤`;
  `IsRationalGenerator.isCurveField`: then `K` is a curve field.
* `Belyi.CurveField.QbarPoint.div_mem`, `Belyi.CurveField.QbarPoint.eval_div`: evaluation of
  rational functions `p(t)/q(t)` at points with `q(t(x)) ≠ 0`.
* `Belyi.CurveField.QbarPoint.div_mem_iff`: for coprime `p, q`, `p(t)/q(t)` is regular at `x`
  iff `q(t(x)) ≠ 0`.
* `Belyi.CurveField.QbarPoint.equivQbar t : {x : QbarPoint K // t ∈ x.P.1} ≃ ℚ̄`.
* `Belyi.CurveField.QbarPoint.fieldOf_eq_adjoin`: `ℚ(x) = ℚ(t(x))`.
* `Belyi.CurveField.mem_chartRing_iff`: the chart ring `A_t` is `ℚ[t]`;
  `Belyi.CurveField.forall_mem_iff`: the functions regular at all places containing `t` are
  the polynomials in `t`.
* `Belyi.CurveField.Place.equivMonicIrreducible`: the places containing `t` correspond to the
  monic irreducible polynomials over `ℚ` (the minimal polynomial of the residue of `t`).
* `Belyi.CurveField.infPlace t`: the unique place with `t ∉ O_P` (the point at infinity);
  it has degree one and `ord_∞ t = -1`, and carries exactly one algebraic point.
-/


-- @@ L44-44 verbatim
open Polynomial IsLocalRing

-- @@ L45-45 verbatim
open scoped IntermediateField


-- @@ L47-50 verbatim
local notation "Qbar" => AlgebraicClosure ℚ

/- The instances below exist in Mathlib but are not found by instance search for the
`ℚ`-algebra structure `DivisionRing.toRatAlgebra` of `ℚ̄`. -/

-- @@ L51-51 expanded
local instance : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ


-- @@ L53-54 expanded
local instance : Normal ℚ (AlgebraicClosure ℚ) :=
  @IsAlgClosure.normal ℚ (AlgebraicClosure ℚ) _ _ _ (AlgebraicClosure.instIsAlgClosure ℚ)


-- @@ L56-56 verbatim
namespace Belyi.CurveField


-- @@ L58-58 verbatim
variable {K : Type*} [Field K] [CharZero K]


-- @@ L60-63 verbatim
/-- `t` is a *rational generator* of `K`: `t` is transcendental over `ℚ` and `K = ℚ(t)`. -/
structure IsRationalGenerator (t : K) : Prop where
  transcendental : Transcendental ℚ t
  adjoin_eq_top : ℚ⟮t⟯ = ⊤


-- @@ L65-65 verbatim
namespace IsRationalGenerator


-- @@ L67-67 verbatim
variable {t : K} (ht : IsRationalGenerator t)

-- @@ L68-68 verbatim
include ht


-- @@ L70-71 verbatim
theorem mem_adjoin (f : K) : f ∈ ℚ⟮t⟯ := by
  rw [ht.adjoin_eq_top]; trivial


-- @@ L73-74 verbatim
theorem algebraMap_bijective : Function.Bijective (algebraMap ℚ⟮t⟯ K) :=
  ⟨(algebraMap ℚ⟮t⟯ K).injective, fun f ↦ ⟨⟨f, ht.mem_adjoin f⟩, rfl⟩⟩


-- @@ L76-77 verbatim
theorem finiteDimensional : FiniteDimensional ℚ⟮t⟯ K :=
  Module.Finite.of_surjective (Algebra.linearMap ℚ⟮t⟯ K) ht.algebraMap_bijective.2


-- @@ L79-81 verbatim
theorem finrank_eq_one : Module.finrank ℚ⟮t⟯ K = 1 := by
  rw [← (LinearEquiv.ofBijective (Algebra.linearMap ℚ⟮t⟯ K)
    ht.algebraMap_bijective).finrank_eq, Module.finrank_self]


-- @@ L83-85 verbatim
/-- The rational function field `ℚ(t)` is a curve field. -/
theorem isCurveField : IsCurveField K :=
  ⟨⟨t, ht.transcendental, ht.finiteDimensional⟩⟩


-- @@ L87-87 verbatim
theorem ne_zero : t ≠ 0 := ne_zero_of_transcendental ht.transcendental


-- @@ L89-90 verbatim
theorem aeval_ne_zero {p : ℚ[X]} (hp : p ≠ 0) : aeval t p ≠ 0 :=
  fun h ↦ ht.transcendental ⟨p, hp, h⟩


-- @@ L92-103 verbatim
/-- Every element of `ℚ(t)` is a reduced fraction `p(t) / q(t)`. -/
theorem exists_coprime (f : K) :
    ∃ p q : ℚ[X], q ≠ 0 ∧ IsCoprime p q ∧ f = aeval t p / aeval t q := by
  obtain ⟨r, s, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff (F := ℚ) f).mp (ht.mem_adjoin f)
  rcases eq_or_ne s 0 with rfl | hs
  · exact ⟨0, 1, one_ne_zero, isCoprime_zero_left.mpr isUnit_one, by simp⟩
  obtain ⟨p, q, hr, hs', hu⟩ := extract_gcd r s
  have hg : gcd r s ≠ 0 := fun h ↦ hs ((gcd_eq_zero_iff r s).mp h).2
  have hq : q ≠ 0 := by rintro rfl; exact hs (by rw [hs', mul_zero])
  refine ⟨p, q, hq, (gcd_isUnit_iff_isRelPrime.mp hu).isCoprime, ?_⟩
  set g := gcd r s
  rw [hr, hs', map_mul, map_mul, mul_div_mul_left _ _ (ht.aeval_ne_zero hg)]


-- @@ L105-107 verbatim
/-- `t⁻¹` is a rational generator. -/
theorem inv : IsRationalGenerator t⁻¹ :=
  ⟨transcendental_inv ht.transcendental, by rw [adjoin_inv_eq, ht.adjoin_eq_top]⟩


-- @@ L109-118 verbatim
/-- `t - q` is a rational generator for `q ∈ ℚ`. -/
theorem sub_ratCast (q : ℚ) : IsRationalGenerator (t - q) := by
  refine ⟨?_, ?_⟩
  · have := ht.transcendental.aeval (X - C q) (by rw [natDegree_X_sub_C]; exact one_ne_zero)
      (by rw [leadingCoeff_X_sub_C]; exact one_mem _)
    simpa using this
  · rw [eq_top_iff, ← ht.adjoin_eq_top, IntermediateField.adjoin_simple_le_iff]
    have h := sub_mem (IntermediateField.mem_adjoin_simple_self ℚ (t - q))
      (IntermediateField.algebraMap_mem ℚ⟮t - q⟯ (-q))
    simpa using h


-- @@ L120-121 verbatim
theorem sub_one : IsRationalGenerator (t - 1) := by
  simpa using ht.sub_ratCast 1


-- @@ L123-123 verbatim
end IsRationalGenerator


-- @@ L125-125 verbatim
/-! ### Evaluation of polynomials and rational functions in `t` -/


-- @@ L127-132 verbatim
theorem Place.aeval_mem (P : Place K) {t : K} (ht : t ∈ P.1) (p : ℚ[X]) : aeval t p ∈ P.1 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | monomial n a =>
    rw [aeval_monomial]
    exact mul_mem (P.algebraMap_mem a) (pow_mem ht n)


-- @@ L134-134 verbatim
namespace QbarPoint


-- @@ L136-136 verbatim
variable (x : QbarPoint K) {t : K} (hx : t ∈ x.P.1)

-- @@ L137-137 verbatim
include hx


-- @@ L139-149 verbatim
/-- The value of `p(t)` at `x` is `p(t(x))`. -/
theorem eval_aeval (p : ℚ[X]) :
    x.eval (aeval t p) (x.P.aeval_mem hx p) = aeval (x.eval t hx) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [x.eval_congr (map_add (aeval t) p q), x.eval_add (x.P.aeval_mem hx p)
      (x.P.aeval_mem hx q), hp, hq, map_add]
  | monomial n a =>
    rw [x.eval_congr (aeval_monomial (R := ℚ) (x := t) (n := n) (r := a)),
      x.eval_mul (x.P.algebraMap_mem a) (pow_mem hx n), eval_algebraMap, x.eval_pow hx,
      aeval_monomial]


-- @@ L151-157 verbatim
omit hx in
/-- A regular function with nonzero value is a unit at the point. -/
theorem inv_mem_of_eval_ne_zero {f : K} (hf : f ∈ x.P.1) (h : x.eval f hf ≠ 0) :
    f⁻¹ ∈ x.P.1 := by
  rw [Ne, eval_eq_zero_iff_mem_maximalIdeal, ← ValuationSubring.coe_mem_nonunits_iff,
    ValuationSubring.mem_nonunits_iff_or, not_or, not_not] at h
  exact h.2


-- @@ L159-164 verbatim
/-- `p(t)/q(t)` is regular at `x` if `q(t(x)) ≠ 0`. -/
theorem div_mem {p q : ℚ[X]} (hq : aeval (x.eval t hx) q ≠ 0) :
    aeval t p / aeval t q ∈ x.P.1 := by
  rw [← x.eval_aeval hx q] at hq
  rw [div_eq_mul_inv]
  exact mul_mem (x.P.aeval_mem hx p) (x.inv_mem_of_eval_ne_zero _ hq)


-- @@ L166-174 verbatim
/-- The value of `p(t)/q(t)` at `x` is `p(z)/q(z)`, `z = t(x)`, if `q(z) ≠ 0`. -/
theorem eval_div {p q : ℚ[X]} (hq : aeval (x.eval t hx) q ≠ 0) :
    x.eval (aeval t p / aeval t q) (x.div_mem hx hq) =
      aeval (x.eval t hx) p / aeval (x.eval t hx) q := by
  have hq' := hq
  rw [← x.eval_aeval hx q] at hq'
  have hi := x.inv_mem_of_eval_ne_zero _ hq'
  rw [x.eval_congr (div_eq_mul_inv _ _), x.eval_mul (x.P.aeval_mem hx p) hi,
    x.eval_inv (x.P.aeval_mem hx q) hi, x.eval_aeval hx, x.eval_aeval hx, div_eq_mul_inv]


-- @@ L176-195 verbatim
/-- A reduced fraction `p(t)/q(t)` is not regular at a point where `q(t(x)) = 0`. -/
theorem div_notMem (htr : Transcendental ℚ t) {p q : ℚ[X]} (hq0 : q ≠ 0) (hpq : IsCoprime p q)
    (hq : aeval (x.eval t hx) q = 0) : aeval t p / aeval t q ∉ x.P.1 := by
  set z := x.eval t hx
  obtain ⟨a, b, hab⟩ := hpq
  have hp : aeval z p ≠ 0 := by
    intro hp
    have := congrArg (aeval z) hab
    rw [map_add, map_mul, map_mul, hp, hq, map_one] at this
    simp at this
  have hp0 : p ≠ 0 := by rintro rfl; exact hp (map_zero _)
  have htp : aeval t p ≠ 0 := fun h ↦ htr ⟨p, hp0, h⟩
  have htq : aeval t q ≠ 0 := fun h ↦ htr ⟨q, hq0, h⟩
  intro hf
  have hg := x.div_mem hx (p := q) hp
  have h1 : aeval t p / aeval t q * (aeval t q / aeval t p) = 1 := by
    field_simp
  have := x.eval_mul hf hg
  rw [x.eval_congr h1, eval_one, x.eval_div hx hp, hq, zero_div, mul_zero] at this
  exact one_ne_zero this


-- @@ L197-200 verbatim
/-- A reduced fraction `p(t)/q(t)` is regular at `x` iff `q(t(x)) ≠ 0`. -/
theorem div_mem_iff (htr : Transcendental ℚ t) {p q : ℚ[X]} (hq0 : q ≠ 0)
    (hpq : IsCoprime p q) : aeval t p / aeval t q ∈ x.P.1 ↔ aeval (x.eval t hx) q ≠ 0 :=
  ⟨fun h hq ↦ x.div_notMem hx htr hq0 hpq hq h, x.div_mem hx⟩


-- @@ L202-204 verbatim
theorem eval_inv_self (hz : x.eval t hx ≠ 0) :
    x.eval t⁻¹ (x.inv_mem_of_eval_ne_zero hx hz) = (x.eval t hx)⁻¹ :=
  x.eval_inv hx _


-- @@ L206-209 verbatim
theorem one_sub_mem (hz : x.eval t hx ≠ 1) : (1 - t)⁻¹ ∈ x.P.1 := by
  refine x.inv_mem_of_eval_ne_zero (sub_mem x.P.1.one_mem hx) ?_
  rw [x.eval_sub x.P.1.one_mem hx, eval_one, sub_ne_zero]
  exact hz.symm


-- @@ L211-213 verbatim
theorem eval_one_sub_inv (hz : x.eval t hx ≠ 1) :
    x.eval (1 - t)⁻¹ (x.one_sub_mem hx hz) = (1 - x.eval t hx)⁻¹ := by
  rw [x.eval_inv (sub_mem x.P.1.one_mem hx), x.eval_sub x.P.1.one_mem hx, eval_one]


-- @@ L215-215 verbatim
end QbarPoint


-- @@ L217-217 verbatim
/-! ### Points of the affine line `t ≠ ∞` -/


-- @@ L219-219 verbatim
namespace QbarPoint


-- @@ L221-221 verbatim
variable {t : K} (ht : IsRationalGenerator t)

-- @@ L222-222 verbatim
include ht


-- @@ L224-227 verbatim
theorem mem_iff_of_eval_eq {x y : QbarPoint K} {hx : t ∈ x.P.1} {hy : t ∈ y.P.1}
    (h : x.eval t hx = y.eval t hy) (f : K) : f ∈ x.P.1 ↔ f ∈ y.P.1 := by
  obtain ⟨p, q, hq0, hpq, rfl⟩ := ht.exists_coprime f
  rw [x.div_mem_iff hx ht.transcendental hq0 hpq, y.div_mem_iff hy ht.transcendental hq0 hpq, h]


-- @@ L229-239 verbatim
/-- Two points at which `t` is regular with the same value of `t` coincide. -/
theorem eq_of_eval_eq {x y : QbarPoint K} {hx : t ∈ x.P.1} {hy : t ∈ y.P.1}
    (h : x.eval t hx = y.eval t hy) : x = y := by
  have hP : x.P = y.P := Place.ext (ValuationSubring.ext _ _ (mem_iff_of_eval_eq ht h))
  refine QbarPoint.ext' hP fun a ↦ ?_
  change x.eval a.1 a.2 = y.eval a.1 _
  obtain ⟨p, q, hq0, hpq, hf⟩ := ht.exists_coprime a.1
  have hqx : aeval (x.eval t hx) q ≠ 0 :=
    (x.div_mem_iff hx ht.transcendental hq0 hpq).mp (hf ▸ a.2)
  have hqy : aeval (y.eval t hy) q ≠ 0 := h ▸ hqx
  rw [x.eval_congr hf, x.eval_div hx hqx, y.eval_congr hf, y.eval_div hy hqy, h]


-- @@ L241-273 expanded
/-- For every `z ∈ ℚ̄` there is a point `x` with `t` regular at `x` and `t(x) = z`. -/
theorem exists_eval_eq [IsCurveField K] (z : AlgebraicClosure ℚ) :
    ∃ (x : QbarPoint K) (hx : t ∈ x.P.1), x.eval t hx = z :=
  by
  have hz : IsIntegral ℚ z := (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  set m := minpoly ℚ z
  have hmd : m.natDegree ≠ 0 := (minpoly.natDegree_pos hz).ne'
  have hmm : m.Monic := minpoly.monic hz
  have hf : Transcendental ℚ (aeval t m) :=
    ht.transcendental.aeval m hmd (by rw [hmm.leadingCoeff]; exact one_mem _)
  obtain ⟨P, hP⟩ := Place.exists_ord_pos hf
  have hfP : aeval t m ∈ P.1 := P.mem_of_ord_nonneg hP.le
  have htP : t ∈ P.1 :=
    by
    have : IsIntegrallyClosedIn P.1 K := inferInstanceAs (IsIntegrallyClosedIn P.1 K)
    have hint : IsIntegral P.1 t :=
      by
      refine
        IsIntegral.of_aeval_monic_of_isIntegral_coeff (p := m.map (algebraMap ℚ K)) (hmm.map _)
          (by rwa [natDegree_map]) ?_ fun i ↦ ?_
      · rw [eval_map_algebraMap]
        exact isIntegral_algebraMap (x := (⟨_, hfP⟩ : P.1))
      · rw [coeff_map]
        exact isIntegral_algebraMap (x := (⟨_, P.algebraMap_mem _⟩ : P.1))
    obtain ⟨y, hy⟩ := IsIntegrallyClosedIn.isIntegral_iff.mp hint
    rw [← hy]
    exact y.2
  obtain ⟨x₀, rfl⟩ := QbarPoint.exists_P_eq P
  have hw : aeval (x₀.eval t htP) m = 0 :=
    by
    rw [← x₀.eval_aeval htP m]
    exact (x₀.eval_eq_zero_iff _ (ne_zero_of_transcendental hf)).mpr hP
  have hmin : minpoly ℚ z = minpoly ℚ (x₀.eval t htP) :=
    minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hz) hw hmm
  obtain ⟨τ, hτ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := ℚ) (E := AlgebraicClosure ℚ)).mp hmin
  refine ⟨⟨x₀.P, (τ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp x₀.σ⟩, htP, ?_⟩
  exact hτ


-- @@ L275-279 expanded
/-- The points at which `t` is regular are in bijection with `ℚ̄` via `x ↦ t(x)`. -/
noncomputable def equivQbar [IsCurveField K] :
    { x : QbarPoint K // t ∈ x.P.1 } ≃ AlgebraicClosure ℚ :=
  Equiv.ofBijective (fun x ↦ x.1.eval t x.2)
    ⟨fun _ _ h ↦ Subtype.ext (eq_of_eval_eq ht h), fun z ↦
      let ⟨x, hx, h⟩ := exists_eval_eq ht z;
      ⟨⟨x, hx⟩, h⟩⟩


-- @@ L281-284 verbatim
omit ht in
@[simp]
theorem equivQbar_apply [IsCurveField K] (ht : IsRationalGenerator t)
    (x : {x : QbarPoint K // t ∈ x.P.1}) : equivQbar ht x = x.1.eval t x.2 := rfl


-- @@ L286-290 expanded
omit ht in
@[simp]
theorem eval_equivQbar_symm [IsCurveField K] (ht : IsRationalGenerator t) (z : AlgebraicClosure ℚ) :
    ((equivQbar ht).symm z).1.eval t ((equivQbar ht).symm z).2 = z :=
  (equivQbar ht).apply_symm_apply z


-- @@ L292-303 verbatim
/-- The field of definition of a point with `t` regular is `ℚ(t(x))`. -/
theorem fieldOf_eq_adjoin (x : QbarPoint K) (hx : t ∈ x.P.1) :
    x.fieldOf = ℚ⟮x.eval t hx⟯ := by
  refine le_antisymm ?_ (IntermediateField.adjoin_simple_le_iff.mpr (x.eval_mem_fieldOf hx))
  rintro _ ⟨b, rfl⟩
  obtain ⟨a, rfl⟩ := x.P.residue_surjective b
  change x.eval a.1 a.2 ∈ _
  obtain ⟨p, q, hq0, hpq, hf⟩ := ht.exists_coprime a.1
  have hqx : aeval (x.eval t hx) q ≠ 0 :=
    (x.div_mem_iff hx ht.transcendental hq0 hpq).mp (hf ▸ a.2)
  rw [x.eval_congr hf, x.eval_div hx hqx]
  exact (IntermediateField.mem_adjoin_simple_iff (F := ℚ) _).mpr ⟨p, q, rfl⟩


-- @@ L305-308 verbatim
/-- The degree of a point with `t` regular is `[ℚ(t(x)) : ℚ]`. -/
theorem deg_eq_finrank_adjoin (x : QbarPoint K) (hx : t ∈ x.P.1) :
    x.deg = Module.finrank ℚ ℚ⟮x.eval t hx⟯ := by
  rw [deg, fieldOf_eq_adjoin ht x hx]


-- @@ L310-314 verbatim
/-- The degree of a point with `t` regular is the degree of the minimal polynomial of `t(x)`. -/
theorem deg_eq_natDegree_minpoly (x : QbarPoint K) (hx : t ∈ x.P.1) :
    x.deg = (minpoly ℚ (x.eval t hx)).natDegree := by
  rw [deg_eq_finrank_adjoin ht x hx,
    IntermediateField.adjoin.finrank (Algebra.IsAlgebraic.isAlgebraic _).isIntegral]


-- @@ L316-316 verbatim
end QbarPoint


-- @@ L318-318 verbatim
/-! ### The chart ring `A_t = ℚ[t]` -/


-- @@ L320-320 verbatim
section Chart


-- @@ L322-322 verbatim
variable {t : K} (ht : IsRationalGenerator t)

-- @@ L323-323 verbatim
include ht


-- @@ L325-336 expanded
/-- A function regular at every place containing `t` is a polynomial in `t`. -/
theorem mem_adjoin_of_forall_mem [IsCurveField K] {f : K} (hf : ∀ P : Place K, t ∈ P.1 → f ∈ P.1) :
    f ∈ Algebra.adjoin ℚ { t } :=
  by
  obtain ⟨p, q, hq0, hpq, rfl⟩ := ht.exists_coprime f
  have hdeg : q.degree = 0 := by
    by_contra hd
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero (k := AlgebraicClosure ℚ) q hd
    obtain ⟨x, hx, rfl⟩ := QbarPoint.exists_eval_eq ht z
    exact x.div_notMem hx ht.transcendental hq0 hpq hz (hf x.P hx)
  rw [eq_C_of_degree_eq_zero hdeg, aeval_C, div_eq_mul_inv, ← map_inv₀]
  exact
    mul_mem (Algebra.adjoin_singleton_eq_range_aeval ℚ t ▸ ⟨p, rfl⟩) (Subalgebra.algebraMap_mem _ _)


-- @@ L338-343 verbatim
theorem forall_mem_iff [IsCurveField K] (f : K) :
    (∀ P : Place K, t ∈ P.1 → f ∈ P.1) ↔ f ∈ Algebra.adjoin ℚ {t} := by
  refine ⟨mem_adjoin_of_forall_mem ht, fun hf P hP ↦ ?_⟩
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hf
  obtain ⟨p, rfl⟩ := hf
  exact P.aeval_mem hP p


-- @@ L345-349 verbatim
/-- The chart ring `A_t` (the integral closure of `ℚ[t]` in `K`) is `ℚ[t]`. -/
theorem mem_chartRing_iff (f : K) : f ∈ chartRing t ↔ f ∈ Algebra.adjoin ℚ {t} := by
  have := ht.isCurveField
  refine ⟨fun hf ↦ mem_adjoin_of_forall_mem ht fun P hP ↦ ?_, mem_chartRing_of_mem_adjoin⟩
  exact mem_of_mem_chartRing P.1 P.ratCast_mem hP hf


-- @@ L351-351 verbatim
end Chart


-- @@ L353-353 verbatim
/-! ### The place at infinity -/


-- @@ L355-355 verbatim
namespace Place


-- @@ L357-357 verbatim
variable [IsCurveField K] {s : K} (hs : IsRationalGenerator s)

-- @@ L358-358 verbatim
include hs


-- @@ L360-362 verbatim
omit hs in
private theorem one_le_term {P : Place K} (hP : P.ord s < 0) : 1 ≤ (-P.ord s) * (P.deg : ℤ) :=
  one_le_mul_of_one_le_of_one_le (by omega) (by exact_mod_cast P.deg_pos)


-- @@ L364-366 verbatim
private theorem sum_poles_eq_one :
    ∑ P ∈ (finite_setOf_ord_neg s).toFinset, (-P.ord s) * (P.deg : ℤ) = 1 := by
  rw [sum_ord_mul_deg_poles s hs.transcendental, hs.finrank_eq_one, Nat.cast_one]


-- @@ L368-371 verbatim
omit hs in
private theorem mem_poles {P : Place K} :
    P ∈ (finite_setOf_ord_neg s).toFinset ↔ P.ord s < 0 :=
  Set.Finite.mem_toFinset _


-- @@ L373-376 verbatim
omit hs in
private theorem term_nonneg :
    ∀ P ∈ (finite_setOf_ord_neg s).toFinset, (0 : ℤ) ≤ (-P.ord s) * (P.deg : ℤ) :=
  fun _ hP ↦ zero_le_one.trans (one_le_term (mem_poles.mp hP))


-- @@ L378-382 verbatim
private theorem term_eq_one {P : Place K} (hP : P.ord s < 0) :
    (-P.ord s) * (P.deg : ℤ) = 1 := by
  refine le_antisymm ?_ (one_le_term hP)
  rw [← sum_poles_eq_one hs]
  exact Finset.single_le_sum term_nonneg (mem_poles.mpr hP)


-- @@ L384-389 verbatim
/-- A rational generator `s` has a simple pole at each of its poles, ... -/
theorem ord_eq_neg_one_of_ord_neg {P : Place K} (hP : P.ord s < 0) : P.ord s = -1 := by
  have h := term_eq_one hs hP
  have := P.deg_pos
  have hd : (1 : ℤ) ≤ P.deg := by exact_mod_cast this
  nlinarith


-- @@ L391-395 verbatim
/-- ... each of its poles has degree one, ... -/
theorem deg_eq_one_of_ord_neg {P : Place K} (hP : P.ord s < 0) : P.deg = 1 := by
  have h := term_eq_one hs hP
  rw [ord_eq_neg_one_of_ord_neg hs hP, neg_neg, one_mul] at h
  exact_mod_cast h


-- @@ L397-409 verbatim
/-- ... and it has only one pole. -/
theorem eq_of_ord_neg {P Q : Place K} (hP : P.ord s < 0) (hQ : Q.ord s < 0) : P = Q := by
  classical
  by_contra hne
  have hsub : {P, Q} ⊆ (finite_setOf_ord_neg s).toFinset := by
    intro R hR
    rw [Finset.mem_insert, Finset.mem_singleton] at hR
    rw [mem_poles]
    rcases hR with rfl | rfl
    exacts [hP, hQ]
  have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun R hR _ ↦ term_nonneg R hR)
  rw [Finset.sum_pair hne, sum_poles_eq_one hs, term_eq_one hs hP, term_eq_one hs hQ] at this
  omega


-- @@ L411-413 verbatim
theorem existsUnique_ord_neg : ∃! P : Place K, P.ord s < 0 :=
  let ⟨P, hP⟩ := exists_ord_neg hs.transcendental
  ⟨P, hP, fun _ hQ ↦ eq_of_ord_neg hs hQ hP⟩


-- @@ L415-415 verbatim
end Place


-- @@ L417-417 verbatim
variable [IsCurveField K]


-- @@ L419-421 verbatim
/-- The place at infinity `t = ∞` of the coordinate `t`: the unique place with `t ∉ O_P` if
`t` is a rational generator (junk value otherwise). -/
noncomputable def infPlace (t : K) : Place K := Classical.epsilon fun P : Place K ↦ t ∉ P.1


-- @@ L423-423 verbatim
variable {t : K} (ht : IsRationalGenerator t)

-- @@ L424-424 verbatim
include ht


-- @@ L426-427 verbatim
theorem notMem_infPlace : t ∉ (infPlace t).1 :=
  Classical.epsilon_spec (Place.exists_notMem ht.transcendental)


-- @@ L429-430 verbatim
theorem ord_infPlace_neg : (infPlace t).ord t < 0 :=
  (Place.ord_neg_iff _).mpr (notMem_infPlace ht)


-- @@ L432-435 verbatim
/-- `∞` is the only place at which `t` is not regular. -/
theorem eq_infPlace_iff {P : Place K} : P = infPlace t ↔ t ∉ P.1 :=
  ⟨fun h ↦ h ▸ notMem_infPlace ht, fun h ↦
    Place.eq_of_ord_neg ht ((Place.ord_neg_iff _).mpr h) (ord_infPlace_neg ht)⟩


-- @@ L437-438 verbatim
theorem eq_infPlace_iff_ord_neg {P : Place K} : P = infPlace t ↔ P.ord t < 0 := by
  rw [eq_infPlace_iff ht, Place.ord_neg_iff]


-- @@ L440-441 verbatim
theorem mem_of_ne_infPlace {P : Place K} (hP : P ≠ infPlace t) : t ∈ P.1 :=
  not_not.mp fun h ↦ hP ((eq_infPlace_iff ht).mpr h)


-- @@ L443-445 verbatim
/-- `t` has a simple pole at `∞`. -/
theorem ord_infPlace : (infPlace t).ord t = -1 :=
  Place.ord_eq_neg_one_of_ord_neg ht (ord_infPlace_neg ht)


-- @@ L447-449 verbatim
/-- The place at infinity has degree one. -/
theorem deg_infPlace : (infPlace t).deg = 1 :=
  Place.deg_eq_one_of_ord_neg ht (ord_infPlace_neg ht)


-- @@ L451-452 verbatim
theorem inv_mem_infPlace : t⁻¹ ∈ (infPlace t).1 :=
  ((infPlace t).mem_or_inv_mem t).resolve_left (notMem_infPlace ht)


-- @@ L454-454 verbatim
namespace QbarPoint


-- @@ L456-459 verbatim
theorem eval_inv_eq_zero_of_P_eq {x : QbarPoint K} (hx : x.P = infPlace t) :
    x.eval t⁻¹ (hx ▸ inv_mem_infPlace ht) = 0 := by
  rw [x.eval_eq_zero_iff _ (inv_ne_zero ht.ne_zero), Place.ord_inv, hx, ord_infPlace ht]
  decide


-- @@ L461-466 verbatim
/-- There is exactly one algebraic point at infinity. -/
theorem existsUnique_P_eq_infPlace : ∃! x : QbarPoint K, x.P = infPlace t := by
  obtain ⟨x, hx⟩ := exists_P_eq (infPlace t)
  refine ⟨x, hx, fun y hy ↦ eq_of_eval_eq (hx := hy ▸ inv_mem_infPlace ht)
    (hy := hx ▸ inv_mem_infPlace ht) ht.inv ?_⟩
  rw [eval_inv_eq_zero_of_P_eq ht hy, eval_inv_eq_zero_of_P_eq ht hx]


-- @@ L468-468 verbatim
end QbarPoint


-- @@ L470-470 verbatim
/-! ### Places of the affine line and irreducible polynomials -/


-- @@ L472-472 verbatim
namespace Place


-- @@ L474-477 verbatim
omit ht in
/-- The minimal polynomial over `ℚ` of the residue of `t` at a place containing `t`. -/
noncomputable def minpolyAt (P : Place K) (hP : t ∈ P.1) : ℚ[X] :=
  minpoly ℚ (P.residue ⟨t, hP⟩)


-- @@ L479-481 verbatim
omit ht in
theorem minpolyAt_monic (P : Place K) (hP : t ∈ P.1) : (P.minpolyAt hP).Monic :=
  minpoly.monic (Algebra.IsIntegral.isIntegral _)


-- @@ L483-485 verbatim
omit ht in
theorem minpolyAt_irreducible (P : Place K) (hP : t ∈ P.1) : Irreducible (P.minpolyAt hP) :=
  minpoly.irreducible (Algebra.IsIntegral.isIntegral _)


-- @@ L487-491 verbatim
omit ht [IsCurveField K] in
/-- The minimal polynomial of `t` at `x.P` is the minimal polynomial of `t(x)`. -/
theorem _root_.Belyi.CurveField.QbarPoint.minpolyAt_P (x : QbarPoint K) (hx : t ∈ x.P.1) :
    x.P.minpolyAt hx = minpoly ℚ (x.eval t hx) :=
  (minpoly.algHom_eq x.σ.toRatAlgHom x.σ.injective _).symm


-- @@ L493-504 expanded
omit ht in
/-- A root `z` of the minimal polynomial of `t` at `P` is `t(x)` for a point `x` over `P`. -/
theorem exists_P_eq_eval_eq (P : Place K) (hP : t ∈ P.1) {z : AlgebraicClosure ℚ}
    (hz : aeval z (P.minpolyAt hP) = 0) :
    ∃ x : QbarPoint K, ∃ hx : x.P = P, x.eval t (hx ▸ hP) = z :=
  by
  obtain ⟨x₀, rfl⟩ := QbarPoint.exists_P_eq P
  have hmin : minpoly ℚ z = minpoly ℚ (x₀.eval t hP) :=
    by
    rw [← x₀.minpolyAt_P hP]
    exact
      (minpoly.eq_of_irreducible_of_monic (x₀.P.minpolyAt_irreducible hP) hz
          (x₀.P.minpolyAt_monic hP)).symm
  obtain ⟨τ, hτ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := ℚ) (E := AlgebraicClosure ℚ)).mp hmin
  exact ⟨⟨x₀.P, (τ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp x₀.σ⟩, rfl, hτ⟩


-- @@ L506-535 expanded
/-- The places containing `t` correspond to the monic irreducible polynomials over `ℚ`, via
the minimal polynomial of the residue of `t`. -/
noncomputable def equivMonicIrreducible :
    { P : Place K // t ∈ P.1 } ≃ { m : ℚ[X] // m.Monic ∧ Irreducible m }
    where
  toFun P := ⟨P.1.minpolyAt P.2, P.1.minpolyAt_monic P.2, P.1.minpolyAt_irreducible P.2⟩
  invFun
    m :=
    ⟨((QbarPoint.equivQbar ht).symm
            (IsAlgClosed.exists_aeval_eq_zero (k := AlgebraicClosure ℚ) m.1
                (degree_pos_of_irreducible m.2.2).ne').choose).1.P,
      ((QbarPoint.equivQbar ht).symm _).2⟩
  left_inv
    P := by
    obtain ⟨P, hP⟩ := P
    set z :=
      (IsAlgClosed.exists_aeval_eq_zero (k := AlgebraicClosure ℚ) (P.minpolyAt hP)
          (degree_pos_of_irreducible (P.minpolyAt_irreducible hP)).ne').choose
    have hz : aeval z (P.minpolyAt hP) = 0 :=
      (IsAlgClosed.exists_aeval_eq_zero (k := AlgebraicClosure ℚ) (P.minpolyAt hP)
          (degree_pos_of_irreducible (P.minpolyAt_irreducible hP)).ne').choose_spec
    obtain ⟨x, rfl, hxz⟩ := P.exists_P_eq_eval_eq hP hz
    refine Subtype.ext ?_
    change ((QbarPoint.equivQbar ht).symm z).1.P = x.P
    have : (QbarPoint.equivQbar ht).symm z = ⟨x, hP⟩ :=
      (QbarPoint.equivQbar ht).symm_apply_eq.mpr hxz.symm
    rw [this]
  right_inv
    m := by
    obtain ⟨m, hm, hirr⟩ := m
    refine Subtype.ext ?_
    set h :=
      IsAlgClosed.exists_aeval_eq_zero (k := AlgebraicClosure ℚ) m
        (degree_pos_of_irreducible hirr).ne'
    set x := (QbarPoint.equivQbar ht).symm h.choose
    change x.1.P.minpolyAt x.2 = m
    rw [x.1.minpolyAt_P x.2, QbarPoint.eval_equivQbar_symm]
    exact (minpoly.eq_of_irreducible_of_monic hirr h.choose_spec hm).symm


-- @@ L537-537 verbatim
end Place


-- @@ L539-539 verbatim
end Belyi.CurveField
