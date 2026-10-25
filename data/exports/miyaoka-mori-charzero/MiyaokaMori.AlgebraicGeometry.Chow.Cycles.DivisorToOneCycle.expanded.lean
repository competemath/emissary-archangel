import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.OneCycle
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.SmoothProjectiveSurface


-- @@ L5-9 verbatim
/-! # The Weil cycle of a Cartier divisor on a surface is a one-cycle

On a surface `dim − 1 = 1`, so the Weil cycle of a Cartier divisor is a one-cycle; this identifies
the target type of the Cartier-to-Weil map with `OneCycle` (the scheme-theoretic fiber
`π_S^*(y) = Σ m_i Γ_i` in the proof of Lemma 5.1 of the paper). -/


-- @@ L11-11 verbatim
set_option autoImplicit false

-- @@ L12-12 verbatim
set_option maxHeartbeats 400000


-- @@ L14-14 verbatim
universe u v w u' v'


-- @@ L16-16 verbatim
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

-- @@ L17-17 verbatim
open scoped AlgebraicGeometry


-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-26 verbatim
theorem SmoothProjectiveSurface.cycleGroup_dim_sub_one_eq_oneCycle {k : Type u} [Field k]
    (S : SmoothProjectiveSurface k) :
    CycleGroup S.toVariety (S.toVariety.dimension - 1) = OneCycle S.toVariety := by
  have hdim : S.toVariety.dimension = 2 :=
    (Variety.dim_eq_scheme_dimension S.toVariety).symm.trans S.dim_eq_two
  rw [hdim]


-- @@ L28-28 verbatim
end
