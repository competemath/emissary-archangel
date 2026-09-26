/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjecturesUtil


-- @@ L19-23 verbatim
/-!
# Moser's Worm

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Moser%27s_worm_problem)
-/


-- @@ L25-25 verbatim
open EuclideanGeometry MeasureTheory


-- @@ L27-27 verbatim
namespace MoserWorm


-- @@ L29-34 expanded
/-- The set of worms is the set of curves of length (at most) 1.
We formalize this as the set of ranges of 1-Lipschitz functions from `[0,1]` to `ℝ²`.
-/
def Worms : Set (Set (EuclideanSpace ℝ (Fin 2))) :=
  {s |
    ∃ f : (Set.Icc (0 : ℝ) (1 : ℝ)) → EuclideanSpace ℝ (Fin 2), LipschitzWith 1 f ∧ Set.range f = s}


-- @@ L36-42 expanded
/-- The set of covers is the set of (measurable) sets
that cover every worm by translation and rotation.
-/
def WormCovers : Set (Set (EuclideanSpace ℝ (Fin 2))) :=
  {X |
    MeasurableSet X ∧
      ∀ w ∈ Worms,
        ∃ (e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)) (v :
          EuclideanSpace ℝ (Fin 2)), e.toLinearEquiv.det = 1 ∧ w ⊆ (fun x => e x + v) '' X}


-- @@ L44-65 verbatim
/--
A disc of radius 1 / 2 is a worm cover.

This follows by translating the center of the disc to the midpoint of the worm.
-/
@[category textbook, AMS 52]
theorem disc_mem_worm_covers : Metric.closedBall 0 0.5 ∈ WormCovers := by
  refine ⟨measurableSet_closedBall, ?_⟩
  rintro w ⟨f, hf, rfl⟩
  refine ⟨LinearIsometryEquiv.refl ℝ _, f ⟨1/2, by constructor <;> norm_num⟩,
    LinearEquiv.det_refl .., ?_⟩
  rintro _ ⟨t, rfl⟩
  refine ⟨f t - f ⟨1/2, by constructor <;> norm_num⟩, ?_, by simp⟩
  simp only [Metric.mem_closedBall, dist_zero_right]
  have h := hf.dist_le_mul t ⟨1/2, by constructor <;> norm_num⟩
  simp only [NNReal.coe_one, one_mul] at h
  rw [dist_eq_norm] at h
  refine h.trans ?_
  obtain ⟨t, ht1, ht2⟩ := t
  simp only [Subtype.dist_eq, Real.dist_eq]
  rw [abs_le]
  constructor <;> linarith


-- @@ L67-75 verbatim
/--
**Moser's Worm Problem**
What is the minimal area (or greatest lower bound on the area)
of a shape that can cover every unit-length curve?
-/
@[category research open, AMS 52]
theorem mosers_worm_problem :
    IsGLB {v | ∃ X ∈ WormCovers, volume X = v} answer(sorry) := by
  sorry


-- @@ L77-87 verbatim
/--
There is a set of area 0.260437 that covers all worms.

*Reference:*
Norwood, Rick; Poole, George (2003), "An improved upper bound for Leo Moser's worm problem",
Discrete and Computational Geometry, 29 (3): 409–417, doi:10.1007/s00454-002-0774-3, MR 1961007.
-/
@[category research solved, AMS 52]
theorem mosers_worm_problem_upper_bound :
    ∃ X ∈ WormCovers, volume X = 0.260437 := by
  sorry


-- @@ L89-97 verbatim
/--
**Convex Moser's Worm Problem**
What is the minimal area (or greatest lower bound on the area)
of a *convex* shape that can cover every unit-length curve?
-/
@[category research open, AMS 52]
theorem convex_mosers_worm_problem :
    IsGLB {v | ∃ X ∈ WormCovers, Convex ℝ X ∧ volume X = v} answer(sorry) := by
  sorry


-- @@ L99-106 verbatim
/--
The minimal area of a convex shape that can cover every unit-length curve is attained.
This follows from the Blaschke selection theorem.
-/
@[category research solved, AMS 52]
theorem convex_mosers_worm_problem_bound_attained :
    ∃ bound, IsLeast {v | ∃ X ∈ WormCovers, Convex ℝ X ∧ volume X = v} bound := by
  sorry


-- @@ L108-119 expanded
/-- There is a convex set of area 0.270911861 that covers all worms.

*Reference:*
Wang, Wei (2006), "An improved upper bound for the worm problem",
Acta Mathematica Sinica, 49 (4): 835–846, MR 2264090.
-/
@[category research solved, AMS 52]
theorem convex_mosers_worm_problem_upper_bound :
    ∃ X : Set (EuclideanSpace ℝ (Fin 2)),
      MeasurableSet X ∧
        Convex ℝ X ∧
          volume X = 0.270911861 ∧
            ∀ w ∈ Worms,
              ∃ (e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)) (v :
                EuclideanSpace ℝ (Fin 2)), e.toLinearEquiv.det = 1 ∧ w ⊆ (fun x => e x + v) '' X :=
  by sorry


-- @@ L121-133 verbatim
/--
0.232239 is a lower bound on the area of a convex set that covers all worms.

*Reference:*
Khandhawit, Tirasan; Pagonakis, Dimitrios; Sriswasdi, Sira (2013),
"Lower Bound for Convex Hull Area and Universal Cover Problems",
International Journal of Computational Geometry & Applications,
23 (3): 197–212, arXiv:1101.5638, doi:10.1142/S0218195913500076, MR 3158583, S2CID 207132316.
-/
@[category research solved, AMS 52]
theorem convex_mosers_worm_problem_lower_bound :
    0.232239 ∈ lowerBounds {v | ∃ X ∈ WormCovers, Convex ℝ X ∧ volume X = v} := by
  sorry


-- @@ L135-135 verbatim
end MoserWorm
