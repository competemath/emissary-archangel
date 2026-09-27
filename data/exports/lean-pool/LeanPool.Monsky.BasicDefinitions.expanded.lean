/-
Copyright (c) 2026 Dhyan Aranha and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhyan Aranha, contributors
-/
module

public import LeanPool.Monsky.SegmentTriangle
import Mathlib.Tactic.Measurability.Init


-- @@ L11-15 verbatim
/-!
# LeanPool.Monsky.BasicDefinitions

Imported Lean Pool material for `LeanPool.Monsky.BasicDefinitions`.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
namespace LeanPool.Monsky


-- @@ L21-21 verbatim
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

-- @@ L22-22 verbatim
local notation "Triangle" => Fin 3 → ℝ²

-- @@ L23-23 verbatim
local notation "Segment" => Fin 2 → ℝ²


-- @@ L25-25 verbatim
open BigOperators

-- @@ L26-31 verbatim
open Finset


/-
  The closedHulls of the polygons cover X.
-/

-- @@ L32-38 verbatim
/-- `X` equals the union of the closed hulls of the polygons in `S`. -/
def isCover {n : ℕ} (X : Set ℝ²) (S : Set (Fin n → ℝ²)) : Prop :=
  (X = ⋃ (P ∈ S), closedHull P)

/-
  The openHulls of the polygons do not intersect.
-/

-- @@ L39-41 verbatim
/-- The open hulls of distinct polygons in `S` are pairwise disjoint. -/
def isDisjointPolygonSet {n : ℕ} (S : Set (Fin n → ℝ²)) : Prop :=
    (∀ T₁ ∈ S, ∀ T₂ ∈ S, T₁ ≠ T₂ → Disjoint (openHull T₁) (openHull T₂))



-- @@ L44-50 verbatim
/-- `isDisjointCover X S` states that `S` covers `X` and its open hulls are pairwise disjoint. -/
def isDisjointCover {n : ℕ} (X : Set ℝ²) (S : Set (Fin n → ℝ²)) : Prop :=
  isCover X S ∧ isDisjointPolygonSet S



/- For now we use this formula as the definition of the area.-/

-- @@ L51-55 verbatim
/-- The area of a triangle, given by half the absolute value of its determinant. -/
noncomputable def triangleArea (T : Triangle) : ℝ :=
  abs (det T) / 2

/- -/

-- @@ L56-65 verbatim
/-- A disjoint cover of `X` by triangles all having the same area. -/
def isEqualAreaCover (X : Set ℝ²) (S : Set Triangle) : Prop :=
  isDisjointCover X S ∧
  (∃ (area : ℝ), ∀ T, (T ∈ S) → triangleArea T = area)





/- Some theorems involving these definitions. -/


-- @@ L67-71 verbatim
lemma isCover_sub {n : ℕ} {S : Set (Fin n → ℝ²)} {X : Set ℝ²} (hCover : isCover X S) :
    ∀ Δ ∈ S, closedHull Δ ⊆ X := by
  intro _ hΔ
  rw [hCover]
  exact Set.subset_biUnion_of_mem hΔ


-- @@ L73-76 verbatim
lemma isCover_includes {n : ℕ} {S : Set (Fin n → ℝ²)} {X : Set ℝ²} {x : ℝ²}
    (hCover : isCover X S) (hx : x ∈ X) : ∃ P ∈ S, x ∈ closedHull P := by
  rw [hCover] at hx
  simp_all only [Set.mem_iUnion, exists_prop]



-- @@ L79-84 verbatim
lemma isCover_open_el_imp_eq {n : ℕ} {S : Set (Fin n → ℝ²)} (hDisj : isDisjointPolygonSet S)
  {Δ₁ Δ₂ : Fin n → ℝ²} (hΔ₁ : Δ₁ ∈ S) (hΔ₂ : Δ₂ ∈ S) {x : ℝ²} (hx₁ : x ∈ openHull Δ₁)
  (hx₂ : x ∈ openHull Δ₂) : Δ₁ = Δ₂ := by
  by_contra hΔ₁₂
  have hx := Set.mem_inter hx₁ hx₂
  rwa [Disjoint.inter_eq (hDisj Δ₁ hΔ₁ Δ₂ hΔ₂ hΔ₁₂)] at hx


-- @@ L86-94 verbatim
lemma cover_mem_side {S : Set Triangle} {X : Set ℝ²} (hCover : isDisjointCover X S)
    (hArea : ∀ Δ ∈ S, det Δ ≠ 0) {x : ℝ²} (hx : x ∈ X) (hInt : ∀ Δ ∈ S, x ∉ (openHull Δ))
    (hv : ∀ i, ∀ Δ ∈ S, x ≠ Δ i) : ∃ Δ ∈ S, ∃ i : Fin 3, x ∈ openHull (Tside Δ i) := by
  rw [hCover.1, @Set.mem_iUnion₂] at hx
  have ⟨Δ, hΔ, hxΔ⟩ := hx
  have hxBoundary : x ∈ boundary Δ := Set.mem_sdiff_of_mem hxΔ (hInt Δ hΔ)
  have ⟨i,hi⟩ := el_in_boundary_imp_side (hArea Δ hΔ) hxBoundary ?_
  · exact ⟨Δ,hΔ,i,hi⟩
  · exact fun i ↦ hv i Δ hΔ



-- @@ L97-103 verbatim
lemma no_empty_cover {n : ℕ} {S : Finset (Fin n → ℝ²)} {X : Set ℝ²}
    (hCover : isCover X (↑S : Set (Fin n → ℝ²))) (hX : Set.Nonempty X) :
    S.card > 0 := by
  by_contra hS
  apply Set.Nonempty.ne_empty hX
  rw [hCover]
  simp [(by simp_all : S = ∅)]


-- @@ L105-105 verbatim
end Monsky

-- @@ L106-106 verbatim
end LeanPool
