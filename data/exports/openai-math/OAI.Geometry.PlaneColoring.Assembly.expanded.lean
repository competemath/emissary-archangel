import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
namespace Problem160


-- @@ L9-37 verbatim
/-- A covering by small cells, whose equally colored distinct centers are far
apart, gives a proper coloring of the unit-distance graph. The covering need
not form a partition: classical choice assigns boundary points to one cell. -/
theorem exists_unit_distance_coloring_of_center_cover
    {X I : Type*} [PseudoMetricSpace X] {k : ℕ}
    (center : I → X) (color : I → Fin k) (r : ℝ)
    (hcover : ∀ x : X, ∃ i : I, dist x (center i) ≤ r)
    (hdiam : 2 * r < 1)
    (hsep : ∀ i j : I, i ≠ j → color i = color j →
      1 + 2 * r < dist (center i) (center j)) :
    ∃ c : X → Fin k, ∀ x y : X, dist x y = 1 → c x ≠ c y := by
  classical
  choose cell hcell using hcover
  refine ⟨fun x => color (cell x), ?_⟩
  intro x y hdist hcolor
  by_cases hsame : cell x = cell y
  · have htriangle := dist_triangle x (center (cell x)) y
    have hx := hcell x
    have hy := hcell y
    rw [← hsame] at hy
    rw [dist_comm (center (cell x)) y] at htriangle
    linarith
  · have hfar := hsep (cell x) (cell y) hsame hcolor
    have htriangle₁ := dist_triangle (center (cell x)) x (center (cell y))
    have htriangle₂ := dist_triangle x y (center (cell y))
    have hx := hcell x
    have hy := hcell y
    rw [dist_comm (center (cell x)) x] at htriangle₁
    linarith


-- @@ L39-39 verbatim
end Problem160


-- @@ L41-41 verbatim
end


-- @@ L43-43 verbatim
end OAI
