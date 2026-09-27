/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerStability
public import LeanPool.NavierStokesAndEuler.Euler.SmoothCoefficientTimeRestriction


-- @@ L12-14 verbatim
/-! Restriction of a genuine ordinary Euler evolution to an initial
closed interval. The reference size of the original solution still
bounds every restricted velocity. -/


-- @@ L16-16 verbatim
@[expose] public section



-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
namespace EulerOrdinarySobolev.Evolution


-- @@ L23-23 verbatim
open Set Filter EulerSmoothLimit EulerTimeIntervalRestriction

-- @@ L24-24 verbatim
open scoped Topology


-- @@ L26-27 verbatim
variable {T : ℝ} {hT : 0 ≤ T} (U : Evolution T hT)
  (S : ℝ) (hS : 0 ≤ S) (hST : S ≤ T)


-- @@ L29-45 verbatim
/-- Restrict time, bundling `velocity`, `pressureForce`, `velocity_continuous`,
`pressure_continuous` and the required compatibility proofs. -/
def restrictTime : Evolution S hS where
  velocity t := U.velocity (initialInclusion T S hST t)
  pressureForce t := U.pressureForce (initialInclusion T S hST t)
  velocity_continuous n := (U.velocity_continuous n).comp (initialInclusion T S hST).continuous
  pressure_continuous n := (U.pressure_continuous n).comp (initialInclusion T S hST).continuous
  solenoidal t := U.solenoidal (initialInclusion T S hST t)
  gradient t := U.gradient (initialInclusion T S hST t)
  time_law t ht x := by
    have htT : t ∈ Ioo (0 : ℝ) T := ⟨ht.1,ht.2.trans_le hST⟩
    have hd := U.time_law t htT x
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
    rw [projIcc_of_mem hS ⟨hr.1.le,hr.2.le⟩,
      projIcc_of_mem hT ⟨hr.1.le,hr.2.le.trans hST⟩]
    rfl


-- @@ L47-48 verbatim
theorem restrictTime_velocity (t : Icc (0 : ℝ) S) :
    (U.restrictTime S hS hST).velocity t=U.velocity (initialInclusion T S hST t) := rfl


-- @@ L50-51 verbatim
theorem restrictTime_initial :
    (U.restrictTime S hS hST).velocity ⟨0,le_rfl,hS⟩=U.velocity ⟨0,le_rfl,hT⟩ := rfl


-- @@ L53-55 verbatim
theorem restrictTime_referenceWordBound (t : Icc (0 : ℝ) S) :
    WordBound 4 U.referenceSize ((U.restrictTime S hS hST).velocity t) :=
  U.referenceWordBound (initialInclusion T S hST t)


-- @@ L57-57 verbatim
end EulerOrdinarySobolev.Evolution
