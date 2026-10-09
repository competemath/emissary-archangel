import OAI.Combinatorics.SphericalRamsey.Specification


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace GrahamSpherical


-- @@ L7-16 verbatim
/-- Fixed fifty-color avoidance in every positive dimension contradicts the
ordinary Ramsey quantifier, without assuming any copy exists. -/
theorem not_euclideanRamsey_of_fifty_colorings
    (havoid : ∀ n : ℕ, 0 < n →
      ∃ color : Point n → Fin 50, AvoidsCopy witness color) :
    ¬ EuclideanRamsey witness := by
  intro hRamsey
  obtain ⟨n, hn, hall⟩ := hRamsey 50 (by decide)
  obtain ⟨color, hc⟩ := havoid n hn
  exact hc (hall color)


-- @@ L18-26 verbatim
/-- The geometric and coloring properties jointly imply the spherical
non-Ramsey conclusion. -/
theorem assemble_full_result
    (hcard : witness.ncard = 12)
    (hsphere : witness ⊆ Metric.sphere (0 : Point 2) 1)
    (havoid : ∀ n : ℕ, 0 < n →
      ∃ color : Point n → Fin 50, AvoidsCopy witness color) :
    Specification.FullAuthoredResult :=
  ⟨hcard, hsphere, havoid, not_euclideanRamsey_of_fifty_colorings havoid⟩


-- @@ L28-28 verbatim
end GrahamSpherical


-- @@ L30-30 verbatim
end OAI
