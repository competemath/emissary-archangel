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


-- @@ L18-25 verbatim
/-!
# Erdős Problem 633

*Reference:*
* [erdosproblems.com/633](https://www.erdosproblems.com/633)
* [So09] Soifer, Alexander, How Does One Cut a Triangle? I
* [So09c] Soifer, Alexander, Is there anything beyond the solution?
-/


-- @@ L27-27 verbatim
open Affine

-- @@ L28-28 verbatim
open scoped Congruent EuclideanGeometry Similar


-- @@ L30-30 verbatim
namespace Erdos633

-- @@ L31-31 expanded
variable {n : ℕ} {T : Triangle ℝ (EuclideanSpace ℝ (Fin 2))}


-- @@ L33-39 expanded
variable (n T) in
/-- A triangle is `n`-cuttable if it can be decomposed into `n` congruent triangles. -/
def IsCuttable : Prop :=
  ∃ Ts : Fin n → Triangle ℝ (EuclideanSpace ℝ (Fin 2)),
    (∀ i j, (Ts i).points ≅ (Ts j).points) ∧
      Pairwise (fun i j ↦ Disjoint (Ts i).interior (Ts j).interior) ∧
        ⋃ i, (Ts i).closedInterior = T.closedInterior


-- @@ L41-46 verbatim
/-- A triangle isn't cuttable into zero triangles. -/
@[category API, AMS 5 51]
lemma IsCuttable.ne_zero (hT : IsCuttable n T) : n ≠ 0 := by
  rintro rfl
  obtain ⟨Ts, -, -, hT⟩ := hT
  exact T.closedInterior_nonempty.ne_empty <| by simpa using hT.symm


-- @@ L48-50 verbatim
/-- Every triangle is cuttable into any non-zero square number of congruent triangles. -/
@[category API, AMS 5 51]
protected lemma IsCuttable.sq (hn : n ≠ 0) : IsCuttable (n ^ 2) T := sorry


-- @@ L52-55 verbatim
/-- Every triangle is cuttable into any non-zero square number of congruent triangles. -/
@[category API, AMS 5 51]
lemma IsCuttable.of_isSquare (hn₀ : n ≠ 0) (hn : IsSquare n) : IsCuttable n T := by
  obtain ⟨n, rfl⟩ := hn; rw [← sq]; exact .sq <| by simpa using hn₀


-- @@ L57-70 verbatim
/-- A triangle whose side lengths and angles are integrally independent is cuttable only into
a non-zero square number of congruent triangles. This is proved in [So09c]. -/
@[category research solved, AMS 5 51]
lemma isCuttable_iff_isSquare_of_linearIndependent
    (hTsides : LinearIndependent ℤ
      ![dist (T.points 0) (T.points 1),
        dist (T.points 1) (T.points 2),
        dist (T.points 2) (T.points 0)])
    (hTangles : LinearIndependent ℤ
      ![∠ (T.points 0) (T.points 1) (T.points 2),
        ∠ (T.points 1) (T.points 2) (T.points 0),
        ∠ (T.points 2) (T.points 0) (T.points 1)]) :
    IsCuttable n T ↔ n ≠ 0 ∧ IsSquare n := by
  exact ⟨fun hT ↦ ⟨hT.ne_zero, sorry⟩, fun hn ↦ .of_isSquare hn.1 hn.2⟩


-- @@ L72-75 expanded
/-- Which triangles can only be decomposed into a square number of congruent triangles? -/
@[category research open, AMS 5 51]
lemma erdos_633 :
    T ∈ (answer(sorry) : Set <| Triangle ℝ (EuclideanSpace ℝ (Fin 2))) ↔
      ∀ n, IsCuttable n T → IsSquare n :=
  sorry


-- @@ L77-83 expanded
variable (n T) in
/-- A triangle is `n`-simili-cuttable if it can be decomposed into `n` similar triangles. -/
def IsSimiliCuttable (n : ℕ) (T : Triangle ℝ (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ Ts : Fin n → Triangle ℝ (EuclideanSpace ℝ (Fin 2)),
    (∀ i j, (Ts i).points ∼ (Ts j).points) ∧
      Pairwise (fun i j ↦ Disjoint (Ts i).interior (Ts j).interior) ∧
        ⋃ i, (Ts i).closedInterior = T.closedInterior


-- @@ L85-90 verbatim
/-- A triangle isn't simili-cuttable into zero triangles. -/
@[category API, AMS 5 51]
lemma IsSimiliCuttable.ne_zero (hT : IsSimiliCuttable n T) : n ≠ 0 := by
  rintro rfl
  obtain ⟨Ts, -, -, hT⟩ := hT
  exact T.closedInterior_nonempty.ne_empty <| by simpa using hT.symm


-- @@ L92-96 verbatim
/-- Every triangle is simili-cuttable into any number of similar triangles, except 0, 2, 3, 5.
This is proved in [So09]. -/
@[category research solved, AMS 5 51]
lemma IsSimiliCuttable.of_ne_zero_two_three_five (hn₀ : n ≠ 0) (hn₂ : n ≠ 2) (hn₃ : n ≠ 3)
    (hn₅ : n ≠ 5) : IsSimiliCuttable n T := sorry


-- @@ L98-102 verbatim
/-- There exists a triangle which isn't simili-cuttable into 0, 2, 3, 5 parts.
This is proved in [So09]. -/
@[category research solved, AMS 5 51]
lemma exists_isSimiliCuttable_iff_ne_zero_two_three_five :
    ∃ T, ∀ n, IsSimiliCuttable n T ↔ n ≠ 0 ∧ n ≠ 2 ∧ n ≠ 3 ∧ n ≠ 5 := sorry


-- @@ L104-104 verbatim
end Erdos633
