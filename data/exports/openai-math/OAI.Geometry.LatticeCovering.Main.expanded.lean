import OAI.Geometry.LatticeCovering.Assembly


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-7 verbatim
/-! A uniform, unconditional single-lattice covering bound in every dimension at least two.
The eventual bound uses the proved analytic and geometric producers; finite-dimensional
absorption supplies one absolute constant for all dimensions. -/


-- @@ L9-9 verbatim
noncomputable section


-- @@ L11-11 verbatim
namespace SingleLatticeCovering

-- @@ L12-12 verbatim
open MeasureTheory

-- @@ L13-13 verbatim
open scoped Pointwise












-- @@ L25-33 verbatim
theorem single_lattice_covering :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 2 ≤ n →
      ∀ (K : Set (Space n)), IsConvexBody K →
        ∃ (L : Submodule ℤ (Space n)) (_ : DiscreteTopology L),
          IsZLattice ℝ L ∧ LatticeCovers K L ∧
            (volume K).toReal / ZLattice.covolume L ≤ C * (n : ℝ) * Real.log (n : ℝ) := by
  obtain ⟨C,hC,h⟩ := Assembly.eventual_single_lattice_covering
  obtain ⟨C',hC',h'⟩ := FiniteDimensions.absorb_finitely_many_dimensions ⟨C,h⟩
  exact ⟨C',hC',fun n hn K hK => h' n hn K hK.1 hK.2.1 hK.2.2⟩



-- @@ L36-36 verbatim
end SingleLatticeCovering




-- @@ L40-40 verbatim
end


-- @@ L42-42 verbatim
end OAI
