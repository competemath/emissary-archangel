/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.GroupTheory.Coxeter.Hecke.Specialization


-- @@ L8-46 verbatim
/-!
# The bar involution of the Iwahori–Hecke algebra

Let `𝓗 = 𝓗_q(W)` be the Iwahori–Hecke algebra over a commutative ring `R` with parameter `q`
(normalization `T_s² = (q - 1) T_s + q`, see `LieLean.GroupTheory.Coxeter.Hecke.Basic`), and let
`σ : R → R` be a ring homomorphism with `σ(q) q = 1` (so `q` is a unit and `σ(q) = q⁻¹`). The
*bar involution* ([KL] §1) is the ring homomorphism `h ↦ h̄` of `𝓗` with
```
  (Σ a_w T_w)‾ = Σ σ(a_w) T_{w⁻¹}⁻¹,
```
in particular `T̄_s = T_s⁻¹` and `ā = σ(a)` for `a ∈ R`. If `σ` is an involution, so is the bar
map. The main example is `R = A[v, v⁻¹]`, `q = v²` and `σ(v) = v⁻¹` (`IwahoriHeckeAlgebra.barL`).

Existence is the non-trivial point: we define the bar map `σ`-semilinearly on the basis and show
`(h T_s)‾ = h̄ T̄_s`, using `T_{(ws)⁻¹}⁻¹ = T_{w⁻¹}⁻¹ T_s⁻¹` when `ℓ(ws) > ℓ(w)` and the quadratic
relation `(T_s⁻¹)² = (q⁻¹ - 1) T_s⁻¹ + q⁻¹`; multiplicativity then follows from
`IwahoriHeckeAlgebra.map_mul_of_map_mul_T_simple`.

## Main definitions

* `IwahoriHeckeAlgebra.TUnit`, `IwahoriHeckeAlgebra.TInv`: `T_w` as a unit of `𝓗` and its
  inverse (for `q` a unit).
* `IwahoriHeckeAlgebra.bar`: the bar involution.
* `IwahoriHeckeAlgebra.barL`: the bar involution of `𝓗_{v²}(W)` over `A[v, v⁻¹]`.

## Main results

* `IwahoriHeckeAlgebra.TInv_simple`, `TInv_mul`: `T_s⁻¹ = q⁻¹ T_s - (1 - q⁻¹)` and
  `T_{xy}⁻¹ = T_y⁻¹ T_x⁻¹` if `ℓ(xy) = ℓ(x) + ℓ(y)`.
* `IwahoriHeckeAlgebra.bar_T`: `T̄_w = T_{w⁻¹}⁻¹`.
* `IwahoriHeckeAlgebra.bar_smul`, `bar_algebraMap`: the bar map is `σ`-semilinear.
* `IwahoriHeckeAlgebra.bar_bar`: the bar map is an involution if `σ` is.
* `IwahoriHeckeAlgebra.barL_C'_simple`: `C'_s = v⁻¹(T_s + 1)` is bar invariant.

## References

* [KL] D. Kazhdan, G. Lusztig, *Representations of Coxeter groups and Hecke algebras*,
  Invent. Math. **53** (1979), 165–184, §1.
-/


-- @@ L48-48 verbatim
open Finsupp


-- @@ L50-50 verbatim
namespace IwahoriHeckeAlgebra


-- @@ L52-52 verbatim
variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

-- @@ L53-53 verbatim
variable {R : Type*} [CommRing R] {q : R}


-- @@ L55-55 verbatim
local prefix:100 "s " => cs.simple

-- @@ L56-56 verbatim
local prefix:100 "ℓ " => cs.length


-- @@ L58-58 verbatim
section Inverse


-- @@ L60-60 verbatim
variable (hq : IsUnit q)


-- @@ L62-63 verbatim
/-- `T_w` as a unit of the Iwahori–Hecke algebra, for `q` a unit. -/
noncomputable def TUnit (w : W) : (IwahoriHeckeAlgebra cs q)ˣ := (isUnit_T cs q hq w).unit


-- @@ L65-66 verbatim
/-- The inverse `T_w⁻¹` of `T_w`, for `q` a unit. -/
noncomputable def TInv (w : W) : IwahoriHeckeAlgebra cs q := ↑(TUnit cs hq w)⁻¹


-- @@ L68-69 verbatim
@[simp]
theorem val_TUnit (w : W) : (TUnit cs hq w : IwahoriHeckeAlgebra cs q) = T cs q w := rfl


-- @@ L71-71 verbatim
theorem T_mul_TInv (w : W) : T cs q w * TInv cs hq w = 1 := (TUnit cs hq w).mul_inv


-- @@ L73-73 verbatim
theorem TInv_mul_T (w : W) : TInv cs hq w * T cs q w = 1 := (TUnit cs hq w).inv_mul


-- @@ L75-77 verbatim
@[simp]
theorem TInv_one : TInv cs hq 1 = 1 := by
  simpa using TInv_mul_T cs hq 1


-- @@ L79-81 verbatim
theorem TUnit_mul {x y : W} (h : ℓ (x * y) = ℓ x + ℓ y) :
    TUnit cs hq (x * y) = TUnit cs hq x * TUnit cs hq y :=
  Units.ext (by simp [T_mul_T cs q h])


-- @@ L83-87 verbatim
/-- `T_{xy}⁻¹ = T_y⁻¹ T_x⁻¹` if `ℓ(xy) = ℓ(x) + ℓ(y)`. -/
theorem TInv_mul {x y : W} (h : ℓ (x * y) = ℓ x + ℓ y) :
    TInv cs hq (x * y) = TInv cs hq y * TInv cs hq x := by
  rw [TInv, TUnit_mul cs hq h, mul_inv_rev, Units.val_mul]
  rfl


-- @@ L89-92 verbatim
/-- `T_s⁻¹ = q⁻¹ T_s - (1 - q⁻¹)` ([KL] §1). -/
theorem TInv_simple (i : B) :
    TInv cs hq (s i) = hq.unit⁻¹.1 • T cs q (s i) - (1 - hq.unit⁻¹.1) • 1 :=
  Units.inv_eq_of_mul_eq_one_right (T_simple_mul_inv cs q hq i)


-- @@ L94-104 verbatim
/-- The quadratic relation for `T_s⁻¹`: `(T_s⁻¹)² = (q⁻¹ - 1) T_s⁻¹ + q⁻¹`. -/
theorem TInv_simple_mul_self (i : B) :
    TInv cs hq (s i) * TInv cs hq (s i) =
      (hq.unit⁻¹.1 - 1) • TInv cs hq (s i) + hq.unit⁻¹.1 • 1 := by
  have e : hq.unit⁻¹.1 * q = 1 := hq.val_inv_mul
  have hT := T_simple_mul_self cs q i
  rw [Algebra.algebraMap_eq_smul_one] at hT
  rw [TInv_simple, sub_mul, mul_sub, mul_sub, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc,
    smul_mul_assoc, mul_smul_comm, mul_smul_comm, mul_smul_comm, mul_smul_comm, hT, mul_one,
    one_mul, one_mul]
  match_scalars <;> linear_combination (hq.unit⁻¹.1) * e


-- @@ L106-106 verbatim
end Inverse


-- @@ L108-108 verbatim
section Bar


-- @@ L110-110 verbatim
variable (σ : R →+* R) (hσ : σ q * q = 1)


-- @@ L112-114 verbatim
include hσ in
theorem isUnit_of_mul_eq_one' : IsUnit q :=
  IsUnit.of_mul_eq_one (σ q) (by rw [mul_comm, hσ])


-- @@ L116-118 verbatim
include hσ in
theorem val_inv_eq : (isUnit_of_mul_eq_one' σ hσ).unit⁻¹.1 = σ q :=
  Units.inv_eq_of_mul_eq_one_left hσ


-- @@ L120-122 verbatim
/-- The image `T_{w⁻¹}⁻¹` of `T_w` under the bar involution. -/
noncomputable def barT (w : W) : IwahoriHeckeAlgebra cs q :=
  TInv cs (isUnit_of_mul_eq_one' σ hσ) w⁻¹


-- @@ L124-125 verbatim
@[simp]
theorem barT_one : barT cs σ hσ 1 = 1 := by simp [barT]


-- @@ L127-131 verbatim
theorem barT_mul {x y : W} (h : ℓ (x * y) = ℓ x + ℓ y) :
    barT cs σ hσ (x * y) = barT cs σ hσ x * barT cs σ hσ y := by
  have h' : ℓ (y⁻¹ * x⁻¹) = ℓ y⁻¹ + ℓ x⁻¹ := by
    rw [← mul_inv_rev, cs.length_inv, cs.length_inv, cs.length_inv, h, add_comm]
  simp only [barT, mul_inv_rev, TInv_mul cs _ h']


-- @@ L133-135 verbatim
theorem barT_simple (i : B) :
    barT cs σ hσ (s i) = σ q • T cs q (s i) - (1 - σ q) • 1 := by
  rw [barT, CoxeterSystem.inv_simple, TInv_simple, val_inv_eq σ hσ]


-- @@ L137-140 verbatim
theorem barT_simple_mul_self (i : B) :
    barT cs σ hσ (s i) * barT cs σ hσ (s i) = (σ q - 1) • barT cs σ hσ (s i) + σ q • 1 := by
  simp only [barT, CoxeterSystem.inv_simple]
  rw [TInv_simple_mul_self, val_inv_eq σ hσ]


-- @@ L142-146 verbatim
/-- The additive map underlying the bar involution: `a T_w ↦ σ(a) T_{w⁻¹}⁻¹`. -/
noncomputable def barAddHom : IwahoriHeckeAlgebra cs q →+ IwahoriHeckeAlgebra cs q :=
  (Finsupp.liftAddHom fun w ↦
      ((smulAddHom R (IwahoriHeckeAlgebra cs q)).flip (barT cs σ hσ w)).comp
        σ.toAddMonoidHom).comp (toFinsupp cs q).toAddEquiv.toAddMonoidHom


-- @@ L148-152 verbatim
theorem barAddHom_smul_T (a : R) (w : W) :
    barAddHom cs σ hσ (a • T cs q w) = σ a • barT cs σ hσ w := by
  have : toFinsupp cs q (a • T cs q w) = single w a := by
    rw [map_smul, toFinsupp_T, smul_single_one]
  simp [barAddHom, this]


-- @@ L154-155 verbatim
theorem barAddHom_T (w : W) : barAddHom cs σ hσ (T cs q w) = barT cs σ hσ w := by
  simpa using barAddHom_smul_T cs σ hσ 1 w


-- @@ L157-162 verbatim
theorem barAddHom_smul (a : R) (h : IwahoriHeckeAlgebra cs q) :
    barAddHom cs σ hσ (a • h) = σ a • barAddHom cs σ hσ h := by
  induction h using induction_on cs q generalizing a with
  | T w => rw [barAddHom_smul_T, barAddHom_T]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
  | smul b x hx => rw [smul_smul, hx, hx, smul_smul, map_mul]


-- @@ L164-184 verbatim
theorem barAddHom_mul_T_simple (h : IwahoriHeckeAlgebra cs q) (i : B) :
    barAddHom cs σ hσ (h * T cs q (s i)) =
      barAddHom cs σ hσ h * barAddHom cs σ hσ (T cs q (s i)) := by
  rw [barAddHom_T]
  induction h using induction_on cs q with
  | T w =>
    rw [T_mul_T_simple, barAddHom_T]
    split_ifs with hlt
    · rw [barAddHom_T, barT_mul cs σ hσ (x := w) (y := s i) (by
        rw [cs.length_simple]; rcases cs.length_mul_simple w i with h | h <;> omega)]
    · -- `w = v s` with `ℓ(v s) = ℓ(v) + 1`.
      obtain ⟨v, rfl⟩ : ∃ v, w = v * s i := ⟨w * s i, by simp⟩
      simp only [CoxeterSystem.simple_mul_simple_cancel_right] at hlt ⊢
      have hlen : ℓ (v * s i) = ℓ v + ℓ (s i) := by
        rw [cs.length_simple]
        rcases cs.length_mul_simple v i with h | h <;> omega
      rw [map_add, barAddHom_smul, barAddHom_smul, barAddHom_T, barAddHom_T,
        barT_mul cs σ hσ hlen, mul_assoc, barT_simple_mul_self, map_sub, map_one, mul_add,
        mul_smul_comm, mul_smul_comm, mul_one]
  | add x y hx hy => rw [add_mul, map_add, hx, hy, map_add, add_mul]
  | smul a x hx => rw [smul_mul_assoc, barAddHom_smul, hx, barAddHom_smul, smul_mul_assoc]


-- @@ L186-193 verbatim
/-- The bar involution `h ↦ h̄` of the Iwahori–Hecke algebra: the ring homomorphism with
`ā = σ(a)` for `a ∈ R` and `T̄_w = T_{w⁻¹}⁻¹` ([KL] §1). -/
noncomputable def bar : IwahoriHeckeAlgebra cs q →+* IwahoriHeckeAlgebra cs q where
  __ := barAddHom cs σ hσ
  map_one' := by simpa using barAddHom_T cs σ hσ 1
  map_mul' := map_mul_of_map_mul_T_simple cs q σ (barAddHom cs σ hσ) (barAddHom_smul cs σ hσ)
    (by simpa using barAddHom_T cs σ hσ 1)
    (barAddHom_mul_T_simple cs σ hσ)


-- @@ L195-198 verbatim
/-- `T̄_w = T_{w⁻¹}⁻¹` ([KL] §1). -/
theorem bar_T (w : W) :
    bar cs σ hσ (T cs q w) = TInv cs (isUnit_of_mul_eq_one' σ hσ) w⁻¹ :=
  barAddHom_T cs σ hσ w


-- @@ L200-202 verbatim
theorem bar_T_simple (i : B) :
    bar cs σ hσ (T cs q (s i)) = σ q • T cs q (s i) - (1 - σ q) • 1 :=
  (barAddHom_T cs σ hσ _).trans (barT_simple cs σ hσ i)


-- @@ L204-205 verbatim
theorem bar_smul (a : R) (h : IwahoriHeckeAlgebra cs q) :
    bar cs σ hσ (a • h) = σ a • bar cs σ hσ h := barAddHom_smul cs σ hσ a h


-- @@ L207-209 verbatim
theorem bar_algebraMap (a : R) :
    bar cs σ hσ (algebraMap R _ a) = algebraMap R _ (σ a) := by
  rw [Algebra.algebraMap_eq_smul_one, bar_smul, map_one, Algebra.algebraMap_eq_smul_one]


-- @@ L211-213 verbatim
/-- `T̄_{xy} = T̄_x T̄_y`, in particular `(T_w)‾ T_{w⁻¹} = 1`. -/
theorem bar_T_mul_T_inv (w : W) : bar cs σ hσ (T cs q w) * T cs q w⁻¹ = 1 := by
  rw [bar_T, TInv_mul_T]


-- @@ L215-220 verbatim
theorem bar_bar_T_simple (hσσ : ∀ a, σ (σ a) = a) (i : B) :
    bar cs σ hσ (bar cs σ hσ (T cs q (s i))) = T cs q (s i) := by
  have e : q * σ q = 1 := by rw [mul_comm, hσ]
  rw [bar_T_simple, map_sub, bar_smul, bar_smul, map_one, bar_T_simple, hσσ, map_sub, map_one,
    hσσ, smul_sub, smul_smul]
  match_scalars <;> linear_combination e


-- @@ L222-234 verbatim
/-- The bar map is an involution if `σ` is ([KL] §1). -/
theorem bar_bar (hσσ : ∀ a, σ (σ a) = a) (h : IwahoriHeckeAlgebra cs q) :
    bar cs σ hσ (bar cs σ hσ h) = h := by
  have hT : ∀ w, bar cs σ hσ (bar cs σ hσ (T cs q w)) = T cs q w := by
    intro w
    induction w using cs.induction_simple_mul with
    | one => simp
    | simple_mul w i hlt ih =>
      rw [← T_simple_mul_T_of_lt cs q hlt, map_mul, map_mul, ih, bar_bar_T_simple cs σ hσ hσσ]
  induction h using induction_on cs q with
  | T w => exact hT w
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | smul a x hx => rw [bar_smul, bar_smul, hσσ, hx]


-- @@ L236-236 verbatim
end Bar


-- @@ L238-238 verbatim
section Laurent


-- @@ L240-240 verbatim
open LaurentPolynomial


-- @@ L242-242 verbatim
variable {A : Type*} [CommRing A]


-- @@ L244-245 verbatim
/-- The ring involution `v ↦ v⁻¹` of `A[v, v⁻¹]`. -/
noncomputable def invertHom : A[T;T⁻¹] →+* A[T;T⁻¹] := (invert (R := A)).toRingEquiv.toRingHom


-- @@ L247-248 verbatim
@[simp]
theorem invertHom_apply (a : A[T;T⁻¹]) : invertHom a = invert a := rfl


-- @@ L250-252 verbatim
theorem invertHom_T_two_mul_T_two :
    invertHom (LaurentPolynomial.T 2 : A[T;T⁻¹]) * LaurentPolynomial.T 2 = 1 := by
  rw [invertHom_apply, invert_T, ← T_add, neg_add_cancel, T_zero]


-- @@ L254-259 verbatim
/-- The bar involution of the generic Iwahori–Hecke algebra `𝓗_{v²}(W)` over `A[v, v⁻¹]`
(`v = LaurentPolynomial.T 1`): `v̄ = v⁻¹`, `T̄_w = T_{w⁻¹}⁻¹` ([KL] §1). -/
noncomputable def barL :
    IwahoriHeckeAlgebra cs (LaurentPolynomial.T 2 : A[T;T⁻¹]) →+*
      IwahoriHeckeAlgebra cs (LaurentPolynomial.T 2 : A[T;T⁻¹]) :=
  bar cs invertHom invertHom_T_two_mul_T_two


-- @@ L261-263 verbatim
theorem barL_smul (a : A[T;T⁻¹]) (h : IwahoriHeckeAlgebra cs (LaurentPolynomial.T 2 : A[T;T⁻¹])) :
    barL cs (a • h) = invert a • barL cs h :=
  bar_smul cs _ _ a h


-- @@ L265-270 verbatim
theorem barL_T_simple (i : B) :
    barL cs (IwahoriHeckeAlgebra.T cs (LaurentPolynomial.T 2 : A[T;T⁻¹]) (cs.simple i)) =
      (LaurentPolynomial.T (-2) : A[T;T⁻¹]) •
          IwahoriHeckeAlgebra.T cs (LaurentPolynomial.T 2 : A[T;T⁻¹]) (cs.simple i) -
        (1 - (LaurentPolynomial.T (-2) : A[T;T⁻¹])) • 1 := by
  rw [barL, bar_T_simple, invertHom_apply, invert_T]


-- @@ L272-284 verbatim
/-- The Kazhdan–Lusztig element `C'_s = v⁻¹ (T_s + 1)` is bar invariant ([KL] §1). -/
theorem barL_C'_simple (i : B) :
    barL cs ((LaurentPolynomial.T (-1) : A[T;T⁻¹]) •
      (IwahoriHeckeAlgebra.T cs (LaurentPolynomial.T 2 : A[T;T⁻¹]) (cs.simple i) + 1)) =
      (LaurentPolynomial.T (-1) : A[T;T⁻¹]) •
        (IwahoriHeckeAlgebra.T cs (LaurentPolynomial.T 2 : A[T;T⁻¹]) (cs.simple i) + 1) := by
  rw [barL_smul, map_add, map_one, barL_T_simple, invert_T, neg_neg]
  have e1 : (LaurentPolynomial.T 1 : A[T;T⁻¹]) * LaurentPolynomial.T (-2) =
      LaurentPolynomial.T (-1) := by rw [← T_add]; norm_num
  have e2 : (LaurentPolynomial.T 1 : A[T;T⁻¹]) * (1 - LaurentPolynomial.T (-2)) =
      LaurentPolynomial.T 1 - LaurentPolynomial.T (-1) := by rw [mul_sub, mul_one, e1]
  rw [smul_add, smul_sub, smul_smul, smul_smul, e1, e2, sub_smul, smul_add]
  abel


-- @@ L286-289 verbatim
/-- The bar involution of `𝓗` over `A[v, v⁻¹]` is an involution ([KL] §1). -/
theorem barL_barL (h : IwahoriHeckeAlgebra cs (LaurentPolynomial.T 2 : A[T;T⁻¹])) :
    barL cs (barL cs h) = h :=
  bar_bar cs _ _ (fun a ↦ involutive_invert a) h


-- @@ L291-291 verbatim
end Laurent


-- @@ L293-293 verbatim
end IwahoriHeckeAlgebra
