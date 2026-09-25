/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Physlib.SpaceAndTime.Time.Basic

-- @@ L11-65 verbatim
/-!
# Time as an inner product space

## i. Overview

In this module we equip the affine type `Time` with a real inner product space structure,
choosing the implicit origin represented by `Time.mk 0`. The units and orientation agree with the
real-valued displacements defined in `Physlib.SpaceAndTime.Time.Basic`.

We note that this is the version of time most often used in undergraduate and
non-mathematical physics.

The choice of units or origin can be made on a case-by-case basis, as
long as they are done consistently. However, since the choice of units and origin is
left implicit, Lean will not catch inconsistencies in the choice of units or origin when
working with `Time`.

For example, for the classical mechanics system corresponding to the harmonic oscillator,
one can take the origin of time to be the time at which the initial conditions are specified,
and the units can be taken as anything as long as the units chosen for time `t` and
the angular frequency `ω` are consistent.

With this choice, `Time` becomes a 1d vector space over `ℝ` with an inner product.

Within other modules e.g. `TimeMan` and `TimeTransMan`, we define
versions of time with less choices made, and relate them to `Time` via a choice of units
or origin.

## ii. Key results

- `toRealCLE` : The continuous linear equivalence from `Time` to `ℝ`.

## iii. Table of contents

- A. Instances on Time
  - A.1. Natural numbers as elements of `Time`
  - A.2. Real numbers as elements of `Time`
  - A.3. Time is inhabited
  - A.4. The order on `Time`
  - A.5. Addition of times
  - A.6. Negation of times
  - A.7. Subtraction of times
  - A.8. Scalar multiplication of time
  - A.9. Module on `Time`
  - A.10. Norm of time
  - A.11. Inner product on `Time`
  - A.12. Decidability of `Time`
  - A.13. Measurability of `Time`
- B. Basis of `Time`
- C. Maps from `Time` to `ℝ`

## iv. References

* None.
-/


-- @@ L67-67 verbatim
@[expose] public section


-- @@ L69-69 verbatim
namespace Time


-- @@ L71-75 verbatim
/-!

## A. Instances on Time

-/


-- @@ L77-81 verbatim
/-!

### A.1. Natural numbers as elements of `Time`

-/


-- @@ L83-84 verbatim
instance : NatCast Time where
  natCast n := ⟨n⟩


-- @@ L86-89 verbatim
/-- The casting of a natural number to an element of `Time`. This corresponds to a choice of
(1) zero point in time, and (2) a choice of metric on time (defining `1`). -/
instance {n : ℕ} : OfNat Time n where
  ofNat := ⟨n⟩


-- @@ L91-92 verbatim
@[simp]
lemma natCast_val {n : ℕ} : val n = n := rfl


-- @@ L94-95 verbatim
@[simp]
lemma natCast_zero : ((0 : ℕ) : Time) = 0 := rfl


-- @@ L97-98 verbatim
@[simp]
lemma natCast_one : ((1 : ℕ) : Time) = 1 := rfl


-- @@ L100-101 verbatim
@[simp]
lemma ofNat_val {n : ℕ} : val (OfNat.ofNat n : Time) = n := rfl


-- @@ L103-104 verbatim
lemma one_ne_zero : (1 : Time) ≠ (0 : Time) :=
  mt (congrArg val) (Nat.cast_injective.ne Nat.one_ne_zero)


-- @@ L106-107 verbatim
@[simp]
lemma zero_val : val 0 = 0 := by exact_mod_cast ofNat_val (n := 0)


-- @@ L109-110 verbatim
@[simp]
lemma eq_zero_iff (t : Time) : t = 0 ↔ t.val = 0 := by simp [Time.ext_iff]


-- @@ L112-113 verbatim
@[simp]
lemma one_val : val 1 = 1 := by exact_mod_cast ofNat_val (n := 1)


-- @@ L115-116 verbatim
@[simp]
lemma eq_one_iff (t : Time) : t = 1 ↔ t.val = 1 := by simp [Time.ext_iff]


-- @@ L118-122 verbatim
/-!

### A.2. Real numbers as elements of `Time`

-/


-- @@ L124-125 verbatim
instance : Coe ℝ Time where
  coe r := ⟨r⟩


-- @@ L127-128 verbatim
instance : Coe Time ℝ where
  coe := Time.val


-- @@ L130-130 verbatim
lemma realCast_val {r : ℝ} : (r : Time).val = r := rfl


-- @@ L132-133 verbatim
@[simp]
lemma realCast_of_natCast {n : ℕ} : ((n : ℝ) : Time) = n := rfl


-- @@ L135-139 verbatim
/-!

### A.3. Time is inhabited

-/


-- @@ L141-142 verbatim
instance : Inhabited Time where
  default := 0


-- @@ L144-145 verbatim
@[simp]
lemma default_eq_zero : default = 0 := rfl


-- @@ L147-151 verbatim
/-!

### A.4. The order on `Time`

-/


-- @@ L153-155 verbatim
/-- The choice of an orientation on `Time`. -/
instance : LE Time where
  le t1 t2 := t1.val ≤ t2.val


-- @@ L157-158 verbatim
lemma le_def (t1 t2 : Time) :
    t1 ≤ t2 ↔ t1.val ≤ t2.val := Iff.rfl


-- @@ L160-163 verbatim
instance : PartialOrder Time where
  le_refl t := by simp [le_def]
  le_trans t1 t2 t3 := by simp [le_def]; exact le_trans
  le_antisymm t1 t2 h1 h2 := by simp_all [le_def]; ext; exact le_antisymm h1 h2


-- @@ L165-166 verbatim
lemma lt_def (t1 t2 : Time) :
    t1 < t2 ↔ t1.val < t2.val := by simp only [lt_iff_le_not_ge, le_def]


-- @@ L168-172 verbatim
/-!

### A.5. Addition of times

-/


-- @@ L174-175 verbatim
instance : Add Time where
  add t1 t2 := ⟨t1.val + t2.val⟩


-- @@ L177-179 verbatim
@[simp]
lemma add_val (t1 t2 : Time) :
    (t1 + t2).val = t1.val + t2.val := rfl


-- @@ L181-185 verbatim
/-!

### A.6. Negation of times

-/


-- @@ L187-188 verbatim
instance : Neg Time where
  neg t := ⟨-t.val⟩


-- @@ L190-192 verbatim
@[simp]
lemma neg_val (t : Time) :
    (-t).val = -t.val := rfl


-- @@ L194-198 verbatim
/-!

### A.7. Subtraction of times

-/


-- @@ L200-201 verbatim
instance : Sub Time where
  sub t1 t2 := ⟨t1.val - t2.val⟩


-- @@ L203-205 verbatim
@[simp]
lemma sub_val (t1 t2 : Time) :
    (t1 - t2).val = t1.val - t2.val := rfl


-- @@ L207-211 verbatim
/-!

### A.8. Scalar multiplication of time

-/


-- @@ L213-214 verbatim
instance : SMul ℝ Time where
  smul k t := ⟨k * t.val⟩


-- @@ L216-218 verbatim
@[simp]
lemma smul_real_val (k : ℝ) (t : Time) :
    (k • t).val = k * t.val := rfl


-- @@ L220-224 verbatim
/-!

### A.9. Module on `Time`

-/


-- @@ L226-232 verbatim
instance : AddGroup Time where
  add_assoc t1 t2 t3 := by ext; simp [add_assoc]
  zero_add t := by ext; simp [zero_add]
  add_zero t := by ext; simp [add_zero]
  neg_add_cancel t := by ext; simp [neg_add_cancel]
  nsmul := nsmulRec
  zsmul := zsmulRec


-- @@ L234-235 verbatim
instance : AddCommGroup Time where
  add_comm := by intros; ext; simp [add_comm]


-- @@ L237-243 verbatim
instance : Module ℝ Time where
  one_smul t := by ext; simp
  smul_add k t1 t2 := by ext; simp [mul_add]
  smul_zero k := by ext; simp [mul_zero]
  add_smul k1 k2 t := by ext; simp [add_mul]
  mul_smul k1 k2 t := by ext; simp [mul_assoc]
  zero_smul t := by ext; simp


-- @@ L245-249 verbatim
/-!

### A.10. Norm of time

-/


-- @@ L251-252 verbatim
instance : Norm Time where
  norm t := ‖t.val‖


-- @@ L254-255 verbatim
lemma norm_eq_val (t : Time) :
    ‖t‖ = ‖t.val‖ := rfl


-- @@ L257-258 verbatim
instance : Dist Time where
  dist t1 t2 := ‖t1 - t2‖


-- @@ L260-261 verbatim
lemma dist_eq_val (t1 t2 : Time) :
    dist t1 t2 = ‖t1.val - t2.val‖ := rfl


-- @@ L263-264 verbatim
lemma dist_eq_real_dist (t1 t2 : Time) :
    dist t1 t2 = dist t1.val t2.val := by rfl


-- @@ L266-273 verbatim
instance : SeminormedAddCommGroup Time where
  dist_self t := by simp [dist_eq_real_dist]
  dist_comm t1 t2 := by simp [dist_eq_real_dist, dist_comm]
  dist_triangle := by simp [dist_eq_real_dist, dist_triangle]
  dist_eq t1 t2 := by
    simp [dist_eq_val, norm_eq_val]
    rw [abs_eq_iff_mul_self_eq]
    ring


-- @@ L275-285 verbatim
instance : NormedAddCommGroup Time where
  eq_of_dist_eq_zero := by
    intro a b h
    simp [dist, norm] at h
    ext
    rw [sub_eq_zero] at h
    exact h
  dist_eq t1 t2 := by
    simp [dist_eq_val, norm_eq_val]
    rw [abs_eq_iff_mul_self_eq]
    ring


-- @@ L287-288 verbatim
instance : NormedSpace ℝ Time where
  norm_smul_le k t := by simp [abs_mul, norm]


-- @@ L290-294 verbatim
/-!

### A.11. Inner product on `Time`

-/


-- @@ L296-296 verbatim
open InnerProductSpace


-- @@ L298-299 verbatim
instance : Inner ℝ Time where
  inner t1 t2 := t1.val * t2.val


-- @@ L301-303 verbatim
@[simp]
lemma inner_def (t1 t2 : Time) :
    ⟪t1, t2⟫_ℝ = t1.val * t2.val := rfl


-- @@ L305-309 verbatim
noncomputable instance : InnerProductSpace ℝ Time where
  norm_sq_eq_re_inner := by intros; simp [norm]; ring
  conj_inner_symm := by intros; simp [inner_def]; ring
  add_left := by intros; simp [inner_def, add_mul]
  smul_left := by intros; simp [inner_def]; ring


-- @@ L311-315 verbatim
/-!

### A.12. Decidability of `Time`

-/


-- @@ L317-318 verbatim
noncomputable instance : DecidableEq Time := fun t1 t2 =>
  decidable_of_iff (t1.val = t2.val) (Time.ext_iff.symm)


-- @@ L320-324 verbatim
/-!

### A.13. Measurability of `Time`

-/

-- @@ L325-325 verbatim
instance : MeasurableSpace Time := borel Time


-- @@ L327-328 verbatim
instance : BorelSpace Time where
  measurable_eq := by rfl


-- @@ L330-334 verbatim
/-!

## B. Basis of `Time`

-/

-- @@ L335-335 verbatim
open MeasureTheory


-- @@ L337-368 verbatim
/-- The orthonomral basis on `Time` defined by `1`. -/
noncomputable def basis : OrthonormalBasis (Fin 1) ℝ Time where
  repr := {
    toFun := fun x => WithLp.toLp 2 (fun _ => x)
    invFun := fun f => ⟨f 0⟩
    left_inv := by
      intro x
      rfl
    right_inv := by
      intro f
      ext i
      fin_cases i
      rfl
    map_add' := by
      intro f g
      ext i
      fin_cases i
      rfl
    map_smul' := by
      intro c f
      ext i
      fin_cases i
      rfl
    norm_map' := by
      intro x
      simp only [Fin.isValue, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
      rw [@PiLp.norm_eq_of_L2]
      simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Real.norm_eq_abs, sq_abs,
        Finset.sum_const, Finset.card_singleton, one_smul]
      rw [Real.sqrt_sq_eq_abs]
      rfl
  }


-- @@ L370-375 verbatim
@[simp]
lemma basis_apply_eq_one (i : Fin 1) :
    basis i = 1 := by
  fin_cases i
  simp [basis]
  rfl


-- @@ L377-379 verbatim
@[simp]
lemma rank_eq_one : Module.rank ℝ Time = 1 :=
  rank_eq_one_iff.mpr ⟨1, one_ne_zero, fun v => ⟨v.val, Time.ext (by simp)⟩⟩


-- @@ L381-383 verbatim
@[simp]
lemma finRank_eq_one : Module.finrank ℝ Time = 1 :=
  Module.rank_eq_one_iff_finrank_eq_one.mp rank_eq_one


-- @@ L385-385 verbatim
instance : FiniteDimensional ℝ Time := Module.finite_of_rank_eq_one rank_eq_one


-- @@ L387-388 verbatim
lemma volume_eq_basis_addHaar :
    (volume (α := Time)) = basis.toBasis.addHaar := basis.addHaar_eq_volume.symm


-- @@ L390-394 verbatim
/-!

## C. Maps from `Time` to `ℝ`

-/


-- @@ L396-401 verbatim
/-- The continuous linear map from `Time` to `ℝ`. -/
noncomputable def toRealCLM : Time →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
  {
  toFun := Time.val
  map_add' := by simp
  map_smul' := by simp }


-- @@ L403-412 verbatim
/-- The continuous linear equivalence from `Time` to `ℝ`. -/
noncomputable def toRealCLE : Time ≃L[ℝ] ℝ := LinearEquiv.toContinuousLinearEquiv
  {
  toFun := Time.val
  invFun := fun x => ⟨x⟩
  left_inv x := by rfl
  right_inv x := by rfl
  map_add' := by simp
  map_smul' := by simp
  }


-- @@ L414-424 verbatim
/-- The linear isometry equivalence from `Time` to `ℝ`. -/
noncomputable def toRealLIE : Time ≃ₗᵢ[ℝ] ℝ where
  toFun := Time.val
  invFun := fun x => ⟨x⟩
  left_inv x := by rfl
  right_inv x := by rfl
  map_add' := by simp
  map_smul' := by simp
  norm_map' x := by
    simp
    rfl


-- @@ L426-427 verbatim
lemma eq_one_smul (t : Time) :
    t = t.val • 1 := Time.ext (by simp)


-- @@ L429-430 verbatim
@[fun_prop]
lemma val_measurable : Measurable Time.val := toRealCLE.continuous.measurable


-- @@ L432-433 verbatim
lemma val_measurableEmbedding : MeasurableEmbedding Time.val :=
  toRealCLE.toHomeomorph.measurableEmbedding


-- @@ L435-436 verbatim
lemma val_measurePreserving : MeasurePreserving Time.val volume volume :=
  LinearIsometryEquiv.measurePreserving toRealLIE


-- @@ L438-439 verbatim
@[fun_prop]
lemma val_differentiable : Differentiable ℝ Time.val := toRealCLM.differentiable


-- @@ L441-444 verbatim
@[simp]
lemma fderiv_val (t : Time) : fderiv ℝ Time.val t 1 = 1 := by
  rw [show Time.val = ⇑toRealCLM from rfl, ContinuousLinearMap.fderiv]
  simp [toRealCLM]


-- @@ L446-446 verbatim
end Time
