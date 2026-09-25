/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Physlib.Meta.TODO.Basic
public import Physlib.SpaceAndTime.Time.InnerProductSpace
public import Physlib.SpaceAndTime.Time.TimeUnit

-- @@ L12-47 verbatim
/-!

# The time manifold with a transitive action of `ℝ`

In this module we define the type `TimeTransMan`. This type physically corresponds to
the manifold of time (diffeomorphic to `ℝ`) with the following additional structure:
1. a transitive action of `ℝ`,
2. a choice of orientation.

The manifold `TimeTransMan` is not equipped with a translationally-invariant metric.
Such metrics are in one-to-one correspondence (to be shown) with positive reals, and
as such we define the type `TimeUnit` (equivalent to the positive reals) to
represent the choice of metric on `TimeTransMan`. This is defined in a different module.

From the point of view of physics, this choice of metric corresponds to a choice of units,
hence the name, and we will use the phrase 'units of time' interchangeably 'choice of metric'.

Given a `x : TimeUnit`, and the structure above, we can define the following
operations on `TimeTransMan`:
- `diff x t1 t2`, for `t1 t2 : TimeTransMan` gives the signed difference between two points in
  time in the units `x`.
- `addTime x r t`, for `r : ℝ` and `t : TimeTransMan`, gives the point in `TimeTransMan`
  that separated from `t`, by `r` in the unit `x`. For example, if `x` is the unit of seconds,
  then `addTime x 1 t` gives the point in `TimeTransMan` that is one second after `t`.
- `neg zero t`, for a given `zero : TimeTransMan`, gives the point in `TimeTransMan`
  that is the same distance away from `zero` as `t` but in the opposite direction.
  This is defined using a choice of units, but is independent of the choice.

Recall that the type `Time` corresponds to the manifold of time with a
given (but arbitrary) choice of units and origin (and therefore has a structure
of a module over `ℝ`). Here we define the homeomorphism:
- `toTime zero x` from `TimeTransMan` to `Time` where
  `zero : TimeTransMan` is the choice of origin and `x : TimeUnit` is the choice of units.
This map is a diffeomorphism (to be shown).

-/


-- @@ L49-49 verbatim
@[expose] public section


-- @@ L51-51 verbatim
TODO "Remove `TimeTransMan` in favor of affine `Time`."


-- @@ L53-57 verbatim
/-- The type `TimeTransMan` represents the time manifold with an orientation and
  a transitive action of the reals. -/
structure TimeTransMan where
  /-- The choice of a map from `TimeTransMan` to `ℝ`. -/
  val : ℝ


-- @@ L59-59 verbatim
namespace TimeTransMan


-- @@ L61-64 verbatim
@[ext]
lemma ext_of {t1 t2 : TimeTransMan} (h : t1.val = t2.val) :
    t1 = t2 := by
  cases t1; cases t2; simp_all


-- @@ L66-73 verbatim
/-!

## The topology on TimeTransMan.

The topology on `TimeTransMan` is induced from the topology on `ℝ`, via the choice
of map `TimeTransMan.val`.

-/


-- @@ L75-77 verbatim
/-- The instance of a topological space on `TimeTransMan` induced by the map `TimeTransMan.val`. -/
instance : TopologicalSpace TimeTransMan := TopologicalSpace.induced TimeTransMan.val
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace


-- @@ L79-81 verbatim
lemma val_surjective : Function.Surjective TimeTransMan.val := by
  intro t
  use { val := t }


-- @@ L83-85 verbatim
@[simp]
lemma val_range : Set.range val = Set.univ := by
  refine Set.range_eq_univ.mpr val_surjective


-- @@ L87-88 verbatim
lemma val_inducing : Topology.IsInducing TimeTransMan.val where
  eq_induced := rfl


-- @@ L90-94 verbatim
lemma val_injective : Function.Injective TimeTransMan.val := by
  intro t1 t2 h
  cases t1
  cases t2
  simp_all


-- @@ L96-100 verbatim
lemma val_isOpenEmbedding : Topology.IsOpenEmbedding TimeTransMan.val where
  eq_induced := rfl
  isOpen_range := by
    simp
  injective := val_injective


-- @@ L102-104 verbatim
lemma isOpen_iff {s : Set TimeTransMan} :
    IsOpen s ↔ IsOpen (TimeTransMan.val '' s) :=
  Topology.IsOpenEmbedding.isOpen_iff_image_isOpen val_isOpenEmbedding


-- @@ L106-127 verbatim
/-- The choice of map `Time.val` from `TimeTransMan` to `ℝ` as a homeomorphism. -/
def valHomeomorphism : TimeTransMan ≃ₜ ℝ where
  toFun := TimeTransMan.val
  invFun := fun t => { val := t }
  left_inv := by
    intro t
    cases t
    rfl
  right_inv := by
    intro t
    rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by
    refine { isOpen_preimage := ?_ }
    intro s hs
    rw [isOpen_iff] at hs
    rw [← Set.image_eq_preimage_of_inverse]
    · exact hs
    · intro t
      rfl
    · intro x
      simp


-- @@ L129-133 verbatim
/-!

## The manifold structure on TimeTransMan

-/


-- @@ L135-143 verbatim
/-- The structure of a charted space on `TimeTransMan` -/
instance : ChartedSpace ℝ TimeTransMan where
  atlas := { valHomeomorphism.toOpenPartialHomeomorph }
  chartAt _ := valHomeomorphism.toOpenPartialHomeomorph
  mem_chart_source := by
    simp
  chart_mem_atlas := by
    intro x
    simp


-- @@ L145-145 verbatim
open Manifold ContDiff


-- @@ L147-153 verbatim
/-- The structure of a manifold on `TimeTransMan` induced by the choice of map `Time.val`. -/
instance : IsManifold 𝓘(ℝ, ℝ) ω TimeTransMan where
  compatible := by
    intro e1 e2 h1 h2
    simp [atlas, ChartedSpace.atlas] at h1 h2
    subst h1 h2
    exact symm_trans_mem_contDiffGroupoid valHomeomorphism.toOpenPartialHomeomorph


-- @@ L155-157 verbatim
lemma val_contDiff : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ω TimeTransMan.val := by
  refine contMDiffOn_univ.mp ?_
  exact contMDiffOn_chart (x := (⟨0⟩ : TimeTransMan))


-- @@ L159-165 verbatim
/-- The choice of map `Time.val` from `TimeTransMan` to `ℝ` as a diffeomorphism. -/
noncomputable def valDiffeomorphism : TimeTransMan ≃ₘ^ω⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ ℝ where
  toEquiv := valHomeomorphism.toEquiv
  contMDiff_toFun := val_contDiff
  contMDiff_invFun := by
    refine contMDiffOn_univ.mp ?_
    exact contMDiffOn_chart_symm (x := (⟨0⟩ : TimeTransMan))


-- @@ L167-171 verbatim
/-!

## The transitive group action on TimeTransMan

-/


-- @@ L173-174 verbatim
instance : VAdd ℝ TimeTransMan where
  vadd p t := { val := p + t.val }


-- @@ L176-178 verbatim
@[simp]
lemma vadd_val (p : ℝ) (t : TimeTransMan) :
    (p +ᵥ t).val = p + t.val := rfl


-- @@ L180-188 verbatim
instance : AddAction ℝ TimeTransMan where
  zero_vadd t := by
    cases t
    ext
    simp
  add_vadd p1 p2 t := by
    ext
    simp only [vadd_val]
    ring


-- @@ L190-194 verbatim
/-!

## A choice of orientation on TimeTransMan

-/


-- @@ L196-197 verbatim
instance : LE TimeTransMan where
  le x y := x.val ≤ y.val


-- @@ L199-200 verbatim
lemma le_def (t1 t2 : TimeTransMan) :
    t1 ≤ t2 ↔ t1.val ≤ t2.val := Iff.rfl


-- @@ L202-202 verbatim
instance : Nonempty TimeTransMan := Nonempty.intro ⟨0⟩


-- @@ L204-208 verbatim
/-!

## Functions based on a choice of unit

-/


-- @@ L210-210 verbatim
open TimeUnit


-- @@ L212-214 verbatim
/-- The distance between two points in `TimeTransMan` in the units of `x : TimeUnit`. -/
noncomputable def dist (x : TimeUnit) (t1 t2 : TimeTransMan) : ℝ :=
  1/x.val * ‖t2.val - t1.val‖


-- @@ L216-220 verbatim
/-!

### Signed difference

-/


-- @@ L222-225 verbatim
/-- The signed difference between two points in on the manifold `TimeTransMan`
  in the units of `x : TimeUnit`. -/
noncomputable def diff (x : TimeUnit) (t2 t1 : TimeTransMan) : ℝ :=
  if t1 ≤ t2 then dist x t1 t2 else - dist x t1 t2


-- @@ L227-237 verbatim
lemma diff_eq_val (x : TimeUnit) (t1 t2 : TimeTransMan) :
    diff x t1 t2 = 1/x.val * (t1.val - t2.val) := by
  by_cases h : t2 ≤ t1
  · simp [diff, dist, h]
    simpa [le_def] using h
  · simp [diff, dist, h]
    simp [le_def] at h
    rw [abs_of_neg]
    have hx : x.val ≠ 0 := x.val_ne_zero
    field_simp
    linarith


-- @@ L239-242 verbatim
@[simp]
lemma diff_self (x : TimeUnit) (t : TimeTransMan) :
    diff x t t = 0 := by
  simp [diff_eq_val]


-- @@ L244-268 verbatim
lemma diff_fst_injective (x : TimeUnit) (t : TimeTransMan) : Function.Injective (diff x · t) := by
  intro t1 t2 h
  simp [diff] at h
  by_cases h1 : t ≤ t1
    <;> by_cases h2 : t ≤ t2
  · simp_all [dist, le_def]
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h
    simp at h
    ext
    exact h
  · simp_all [dist, le_def]
    rw [abs_of_nonneg (by linarith), abs_of_neg (by linarith)] at h
    simp [← mul_neg] at h
    ext
    exact h
  · simp_all [dist, le_def]
    rw [abs_of_neg (by linarith), abs_of_nonneg (by linarith)] at h
    simp [← mul_neg] at h
    ext
    exact h
  · simp_all [dist, le_def]
    rw [abs_of_neg (by linarith), abs_of_neg (by linarith)] at h
    simp at h
    ext
    exact h


-- @@ L270-287 verbatim
lemma diff_fst_surjective (x : TimeUnit) (t : TimeTransMan) :
    Function.Surjective (diff x · t) := by
  intro r
  simp [diff, dist]
  use x.1 * r +ᵥ t
  simp [abs_mul]
  rw [abs_of_nonneg (le_of_lt x.val_pos)]
  simp only [ne_eq, TimeUnit.val_ne_zero, not_false_eq_true, inv_mul_cancel_left₀]
  by_cases h : 0 ≤ r
  · rw [if_pos]
    exact abs_of_nonneg h
    simp [le_def]
    apply mul_nonneg (le_of_lt x.val_pos) h
  · rw [if_neg]
    rw [abs_of_neg (by simpa using h)]
    simp only [neg_neg]
    simp [le_def]
    refine mul_neg_of_pos_of_neg x.val_pos (by simpa using h)


-- @@ L289-291 verbatim
lemma diff_fst_bijective (x : TimeUnit) (t : TimeTransMan) :
    Function.Bijective (diff x · t) :=
  ⟨diff_fst_injective x t, diff_fst_surjective x t⟩


-- @@ L293-297 verbatim
/-!

### Adding time

-/


-- @@ L299-303 verbatim
/-- Given a time unit `x : TimeUnit`, `addTime x r t`, for a real `ℝ` and `t : TimeTransMan`,
  is the point in `TimeTransMan` separated from `t` by a difference of `r` in the units `x`.
  For example, if `x` corresponds to seconds `addTime x 1 t` is the time 1 second more then `t`. -/
noncomputable def addTime (x : TimeUnit) (r : ℝ) (t : TimeTransMan) : TimeTransMan :=
  Function.invFun (diff x · t) r


-- @@ L305-310 verbatim
lemma addTime_eq_val (x : TimeUnit) (r : ℝ) (t : TimeTransMan) :
    (addTime x r t) = ⟨x.1 * r + t.val⟩ := by
  apply diff_fst_injective x t
  change (diff x · t) (Function.invFun ((diff x · t)) r) = _
  rw [Function.rightInverse_invFun (diff_fst_surjective x t)]
  simp [diff_eq_val]


-- @@ L312-314 verbatim
lemma addTime_val (x : TimeUnit) (r : ℝ) (t : TimeTransMan) :
    (addTime x r t).val = x.1 * r + t.val := by
  rw [addTime_eq_val]


-- @@ L316-320 verbatim
/-!

## Negation of time around a zero

-/


-- @@ L322-327 verbatim
/-- Given a `zero` and an `x : TimeUnit`, `negMetric zero x t` is the time the same distance
  away from `zero` as `t` in units `x` but in the opposite direction.
  This does actually depend on `x`, as a result see `neg` and `neg_eq_negMetric`. -/
noncomputable def negMetric (zero : TimeTransMan) (x : TimeUnit)
    (t : TimeTransMan) : TimeTransMan :=
  addTime x (diff x zero t) zero


-- @@ L329-332 verbatim
/-- Given a `zero`, `neg zero t` is the time the same distance
  away from `zero` as `t` in any units but in the opposite direction. -/
noncomputable def neg (zero : TimeTransMan) (t : TimeTransMan) : TimeTransMan :=
  negMetric zero default t


-- @@ L334-338 verbatim
lemma neg_eq_negMetric (zero : TimeTransMan) (x : TimeUnit) (t : TimeTransMan) :
    neg zero t = negMetric zero x t := by
  simp [neg, negMetric]
  ext
  simp [addTime_val, diff_eq_val]


-- @@ L340-344 verbatim
/-!

### The map from TimeTransMan to Time

-/

-- @@ L345-377 verbatim
/-- With a choice of zero `zero : TimeTransMan` and a choice of units `x : TimeUnit`,
  `toTime` is the homeomorphism between the type `TimeTransMan` and `Time`. -/
noncomputable def toTime (zero : TimeTransMan) (x : TimeUnit) : TimeTransMan ≃ₜ Time where
  toFun := fun t => ⟨diff x t zero⟩
  invFun := fun r => addTime x r zero
  left_inv t := by
    ext
    simp [addTime_val, diff_eq_val]
  right_inv r := by
    ext
    simp [addTime_val, diff_eq_val]
  continuous_invFun := by
    rw [← Homeomorph.comp_continuous_iff valHomeomorphism]
    have h1 : (⇑valHomeomorphism ∘ (fun r : Time => addTime x r.val zero)) = fun r =>
        (x.val * r.val + zero.val) := by
      ext
      simp [valHomeomorphism, addTime_val]
    rw [h1]
    · apply Continuous.add
      · apply Continuous.fun_mul
        · fun_prop
        · apply Differentiable.continuous (𝕜 := ℝ)
          fun_prop
      · fun_prop

  continuous_toFun := by
    rw [← Homeomorph.comp_continuous_iff Time.toRealCLE.toHomeomorph]
    have h1 : (⇑Time.toRealCLE.toHomeomorph ∘ (fun t => ⟨diff x t zero⟩)) = fun t =>
        (1/x.val) * (t.val - zero.val) := by
      ext
      simp [Time.toRealCLE, diff_eq_val]
    rw [h1]
    fun_prop


-- @@ L379-383 verbatim
@[simp]
lemma toTime_zero (zero : TimeTransMan) (x : TimeUnit) :
    toTime zero x zero = 0 := by
  ext
  simp [toTime, diff_eq_val]


-- @@ L385-389 verbatim
@[simp]
lemma toTime_symm_zero_add (zero : TimeTransMan) (x : TimeUnit) :
    (toTime zero x).symm 0 = zero := by
  ext
  simp [toTime, addTime_val, diff_eq_val]


-- @@ L391-392 verbatim
lemma toTime_val (zero : TimeTransMan) (x : TimeUnit) (t : TimeTransMan) :
    (toTime zero x t).val = diff x t zero := by rfl


-- @@ L394-397 verbatim
lemma toTime_symm_val (zero : TimeTransMan) (x : TimeUnit) (r : Time) :
    (toTime zero x).symm r = addTime x r zero := by
  ext
  simp [toTime, addTime_val, diff_eq_val]


-- @@ L399-405 verbatim
@[simp]
lemma toTime_addTime (zero : TimeTransMan) (x : TimeUnit) (r : ℝ) (τ : TimeTransMan) :
    toTime zero x (addTime x r τ) = ⟨r⟩ + toTime zero x τ:= by
  ext
  simp [toTime_val, diff_eq_val, addTime_val]
  field_simp
  ring


-- @@ L407-412 verbatim
lemma toTime_symm_add (zero : TimeTransMan) (x : TimeUnit) (t1 t2 : Time) :
    (toTime zero x).symm (t1 + t2) = addTime x (diff x ((toTime zero x).symm t1) zero)
      ((toTime zero x).symm t2) := by
  ext
  simp [addTime_val, diff_eq_val, toTime_symm_val]
  ring


-- @@ L414-419 verbatim
lemma toTime_symm_add' (zero : TimeTransMan) (x : TimeUnit) (t1 t2 : Time) :
    (toTime zero x).symm (t1 + t2) = addTime x (diff x ((toTime zero x).symm t2) zero)
      ((toTime zero x).symm t1) := by
  ext
  simp [addTime_val, diff_eq_val, toTime_symm_val]
  ring


-- @@ L421-425 verbatim
lemma diff_eq_toTime_sub (zero : TimeTransMan) (x : TimeUnit) (t1 t2 : TimeTransMan) :
    diff x t2 t1 = toTime zero x t2 - toTime zero x t1 := by
  simp [toTime_val, diff_eq_val]
  field_simp
  ring


-- @@ L427-433 verbatim
lemma toTime_neg (zero : TimeTransMan) (x : TimeUnit) (t : TimeTransMan) :
    (toTime zero x) (neg zero t) = - toTime zero x t := by
  rw [neg_eq_negMetric zero x]
  ext
  simp only [negMetric, diff_eq_val, one_div, toTime_addTime, toTime_zero,
    add_zero, Time.neg_val, toTime_val]
  ring


-- @@ L435-438 verbatim
lemma toTime_symm_neg (zero : TimeTransMan) (x : TimeUnit) (t : Time) :
    (toTime zero x).symm (- t) = neg zero ((toTime zero x).symm t) := by
  ext
  simp [toTime_symm_val, addTime_val, diff_eq_val, neg, negMetric]


-- @@ L440-446 verbatim
lemma toTime_symm_sub (zero : TimeTransMan) (x : TimeUnit)
    (t1 t2 : Time) : (toTime zero x).symm (t1 - t2) =
      addTime x (diff x zero ((toTime zero x).symm t2))
      ((toTime zero x).symm t1) := by
  ext
  simp [addTime_val, diff_eq_val, toTime_symm_val]
  ring


-- @@ L448-448 verbatim
end TimeTransMan
