/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.SpaceAndTime.SpaceTime.TimeSlice

-- @@ L9-45 verbatim
/-!

# The Lorentz Current Density

## i. Overview

In this module we define the Lorentz current density
and its decomposition into charge density and current density.
The Lorentz current density is often called the four-current and given then the symbol `J`.

The current density is given in terms of the charge density `ρ` and the current density
` \vec j` as `J = (c ρ, \vec j)`.

## ii. Key results

- `LorentzCurrentDensity` : The type of Lorentz current densities.
- `LorentzCurrentDensity.chargeDensity` : The charge density associated with a
  Lorentz current density.
- `LorentzCurrentDensity.currentDensity` : The current density associated with a
  Lorentz current density.

## iii. Table of contents

- A. The Lorentz Current Density
- B. The underlying charge
  - B.1. Charge density of zero Lorentz current density
  - B.2. Differentiability of the charge density
  - B.3. Smoothness of the charge density
- C. The underlying current density
  - C.1. current density of zero Lorentz current density
  - C.2. Differentiability of the current density
  - C.3. Smoothness of the current density

## iv. References

* None.
-/


-- @@ L47-47 verbatim
@[expose] public section


-- @@ L49-49 verbatim
namespace Electromagnetism

-- @@ L50-50 verbatim
open TensorSpecies

-- @@ L51-51 verbatim
open SpaceTime

-- @@ L52-52 verbatim
open TensorProduct

-- @@ L53-53 verbatim
open minkowskiMatrix

-- @@ L54-54 verbatim
open InnerProductSpace


-- @@ L56-56 verbatim
attribute [-simp] Fintype.sum_sum_type

-- @@ L57-57 verbatim
attribute [-simp] Nat.succ_eq_add_one


-- @@ L59-65 verbatim
/-!

## A. The Lorentz Current Density

The Lorentz current density is a Lorentz Vector field on spacetime.

-/


-- @@ L67-68 verbatim
/-- The Lorentz current density, also called four-current. -/
abbrev LorentzCurrentDensity (d : ℕ := 3) := SpaceTime d → Lorentz.Vector d


-- @@ L70-70 verbatim
namespace LorentzCurrentDensity


-- @@ L72-76 verbatim
/-!

## B. The underlying charge

-/


-- @@ L78-81 verbatim
/-- The underlying charge density associated with a Lorentz current density. -/
noncomputable def chargeDensity (c : SpeedOfLight := 1)
    (J : LorentzCurrentDensity d) : Time → Space d → ℝ :=
  fun t x => (1 / (c : ℝ)) * J ((toTimeAndSpace c).symm (t, x)) (Sum.inl 0)


-- @@ L83-84 verbatim
lemma chargeDensity_eq_timeSlice {d : ℕ} {c : SpeedOfLight} {J : LorentzCurrentDensity d} :
    J.chargeDensity c = timeSlice c (fun x => (1 / (c : ℝ)) • J x (Sum.inl 0)) := by rfl


-- @@ L86-90 verbatim
/-!

### B.1. Charge density of zero Lorentz current density

-/


-- @@ L92-96 verbatim
@[simp]
lemma chargeDensity_zero {d : ℕ} {c : SpeedOfLight}:
    chargeDensity c (0 : LorentzCurrentDensity d) = 0 := by
  simp [chargeDensity_eq_timeSlice, timeSlice]
  rfl


-- @@ L98-101 verbatim
/-!

### B.2. Differentiability of the charge density
-/


-- @@ L103-111 verbatim
lemma chargeDensity_differentiable {d : ℕ} {c : SpeedOfLight} {J : LorentzCurrentDensity d}
    (hJ : Differentiable ℝ J) : Differentiable ℝ ↿(J.chargeDensity c) := by
  rw [chargeDensity_eq_timeSlice]
  apply timeSlice_differentiable
  have h1 : ∀ i, Differentiable ℝ (fun x => J x i) := by
    rw [SpaceTime.differentiable_vector]
    exact hJ
  apply Differentiable.fun_const_smul
  exact h1 (Sum.inl 0)


-- @@ L113-119 verbatim
lemma chargeDensity_differentiable_space {d : ℕ} {c : SpeedOfLight} {J : LorentzCurrentDensity d}
    (hJ : Differentiable ℝ J) (t : Time) :
    Differentiable ℝ (fun x => J.chargeDensity c t x) := by
  change Differentiable ℝ (↿(J.chargeDensity c) ∘ fun x => (t, x))
  refine Differentiable.comp ?_ ?_
  · exact chargeDensity_differentiable hJ
  · fun_prop


-- @@ L121-125 verbatim
/-!

### B.3. Smoothness of the charge density

-/


-- @@ L127-135 verbatim
lemma chargeDensity_contDiff {d : ℕ} {c : SpeedOfLight} {J : LorentzCurrentDensity d}
    (hJ : ContDiff ℝ n J) : ContDiff ℝ n ↿(J.chargeDensity c) := by
  rw [chargeDensity_eq_timeSlice]
  apply timeSlice_contDiff
  have h1 : ∀ i, ContDiff ℝ n (fun x => J x i) := by
    rw [SpaceTime.contDiff_vector]
    exact hJ
  apply ContDiff.const_smul
  exact h1 (Sum.inl 0)


-- @@ L137-141 verbatim
/-!

## C. The underlying current density

-/


-- @@ L143-146 verbatim
/-- The underlying (non-Lorentz) current density associated with a Lorentz current density. -/
noncomputable def currentDensity (c : SpeedOfLight := 1) (J : LorentzCurrentDensity d) :
    Time → Space d → EuclideanSpace ℝ (Fin d) :=
  fun t x => WithLp.toLp 2 fun i => J ((toTimeAndSpace c).symm (t, x)) (Sum.inr i)


-- @@ L148-150 verbatim
lemma currentDensity_eq_timeSlice {d : ℕ} {J : LorentzCurrentDensity d} :
    J.currentDensity c = timeSlice c (fun x => WithLp.toLp 2
      fun i => J x (Sum.inr i)) := by rfl


-- @@ L152-156 verbatim
/-!

### C.1. current density of zero Lorentz current density

-/


-- @@ L158-162 verbatim
@[simp]
lemma currentDensity_zero {d : ℕ} {c : SpeedOfLight}:
    currentDensity c (0 : LorentzCurrentDensity d) = 0 := by
  simp [currentDensity_eq_timeSlice, timeSlice]
  rfl

-- @@ L163-167 verbatim
/-!

### C.2. Differentiability of the current density

-/


-- @@ L169-176 verbatim
lemma currentDensity_differentiable {d : ℕ} {c : SpeedOfLight} {J : LorentzCurrentDensity d}
    (hJ : Differentiable ℝ J) : Differentiable ℝ ↿(J.currentDensity c) := by
  rw [currentDensity_eq_timeSlice]
  apply timeSlice_differentiable
  have h1 : ∀ i, Differentiable ℝ (fun x => J x i) := by
    rw [SpaceTime.differentiable_vector]
    exact hJ
  exact differentiable_euclidean.mpr fun i => h1 (Sum.inr i)


-- @@ L178-184 verbatim
lemma currentDensity_apply_differentiable {d : ℕ} {c : SpeedOfLight} {J : LorentzCurrentDensity d}
    (hJ : Differentiable ℝ J) (i : Fin d) :
    Differentiable ℝ ↿(fun t x => J.currentDensity c t x i) := by
  change Differentiable ℝ (EuclideanSpace.proj i ∘ ↿(J.currentDensity c))
  refine Differentiable.comp ?_ ?_
  · exact ContinuousLinearMap.differentiable (𝕜 := ℝ) (EuclideanSpace.proj i)
  · exact currentDensity_differentiable hJ


-- @@ L186-192 verbatim
lemma currentDensity_differentiable_space {d : ℕ} {c : SpeedOfLight} {J : LorentzCurrentDensity d}
    (hJ : Differentiable ℝ J) (t : Time) :
    Differentiable ℝ (fun x => J.currentDensity c t x) := by
  change Differentiable ℝ (↿(J.currentDensity c) ∘ fun x => (t, x))
  refine Differentiable.comp ?_ ?_
  · exact currentDensity_differentiable hJ
  · fun_prop


-- @@ L194-203 verbatim
lemma currentDensity_apply_differentiable_space {d : ℕ} {c : SpeedOfLight}
    {J : LorentzCurrentDensity d}
    (hJ : Differentiable ℝ J) (t : Time) (i : Fin d) :
    Differentiable ℝ (fun x => J.currentDensity c t x i) := by
  change Differentiable ℝ (EuclideanSpace.proj i ∘ (↿(J.currentDensity c) ∘ fun x => (t, x)))
  refine Differentiable.comp ?_ ?_
  · exact ContinuousLinearMap.differentiable (𝕜 := ℝ) _
  · apply Differentiable.comp ?_ ?_
    · exact currentDensity_differentiable hJ
    · fun_prop


-- @@ L205-211 verbatim
lemma currentDensity_differentiable_time {d : ℕ} {c : SpeedOfLight} {J : LorentzCurrentDensity d}
    (hJ : Differentiable ℝ J) (x : Space d) :
    Differentiable ℝ (fun t => J.currentDensity c t x) := by
  change Differentiable ℝ (↿(J.currentDensity c) ∘ fun t => (t, x))
  refine Differentiable.comp ?_ ?_
  · exact currentDensity_differentiable hJ
  · fun_prop


-- @@ L213-222 verbatim
lemma currentDensity_apply_differentiable_time {d : ℕ} {c : SpeedOfLight}
    {J : LorentzCurrentDensity d}
    (hJ : Differentiable ℝ J) (x : Space d) (i : Fin d) :
    Differentiable ℝ (fun t => J.currentDensity c t x i) := by
  change Differentiable ℝ (EuclideanSpace.proj i ∘ (↿(J.currentDensity c) ∘ fun t => (t, x)))
  refine Differentiable.comp ?_ ?_
  · exact ContinuousLinearMap.differentiable (𝕜 := ℝ) _
  · apply Differentiable.comp ?_ ?_
    · exact currentDensity_differentiable hJ
    · fun_prop


-- @@ L224-228 verbatim
/-!

### C.3. Smoothness of the current density

-/


-- @@ L230-237 verbatim
lemma currentDensity_ContDiff {d : ℕ} {c : SpeedOfLight} {J : LorentzCurrentDensity d}
    (hJ : ContDiff ℝ n J) : ContDiff ℝ n ↿(J.currentDensity c) := by
  rw [currentDensity_eq_timeSlice]
  apply timeSlice_contDiff
  have h1 : ∀ i, ContDiff ℝ n (fun x => J x i) := by
    rw [SpaceTime.contDiff_vector]
    exact hJ
  exact contDiff_euclidean.mpr fun i => h1 (Sum.inr i)


-- @@ L239-239 verbatim
end LorentzCurrentDensity


-- @@ L241-241 verbatim
end Electromagnetism
