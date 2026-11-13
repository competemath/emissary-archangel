import Mathlib
import Submission.IFTSurfaceCriticality


-- @@ L4-15 verbatim
/-!
# Spatial rank at a Morse critical point

At a time-critical point of a regular framed cobordism, every vector in the
kernel of the full differential has zero time component.  Spatial inclusion
therefore identifies the kernel of the spatial differential with the kernel
of the full differential.  Since the latter has dimension two, the spatial
differential has kernel dimension two and rank `n - 1`.

This is the linear-algebra input needed to choose the unique degenerating
normal row in the rescaled definite-event frame.
-/


-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
open Set Function

-- @@ L20-20 verbatim
open scoped RealInnerProductSpace


-- @@ L22-22 verbatim
namespace Submission


-- @@ L24-24 verbatim
set_option autoImplicit false


-- @@ L26-26 verbatim
variable {n : ℕ}


-- @@ L28-28 verbatim
local notation "E₁" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L29-29 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))

-- @@ L30-30 verbatim
local notation "F" => EuclideanSpace ℝ (Fin n)


-- @@ L32-49 verbatim
/-- Spatial inclusion, restricted to the spatial kernel and corestricted to
the full ambient kernel at a time-critical point. -/
def spatialKerToAmbientKer (C : FramedLevelCobordism n) (v : E')
    (hv : v ∈ timeCritical C.G) :
    LinearMap.ker ((spatialDeriv C.G v).toLinearMap) →ₗ[ℝ]
      LinearMap.ker ((fderiv ℝ C.G v).toLinearMap) :=
  { toFun := fun x => ⟨spaceInclL x.1, by
      rw [LinearMap.mem_ker]
      change spatialDeriv C.G v x.1 = 0
      exact LinearMap.mem_ker.mp x.2⟩
    map_add' := by
      intro x y
      apply Subtype.ext
      exact map_add spaceInclL x.1 y.1
    map_smul' := by
      intro c x
      apply Subtype.ext
      exact map_smul spaceInclL c x.1 }


-- @@ L51-58 verbatim
theorem spatialKerToAmbientKer_injective
    (C : FramedLevelCobordism n) (v : E')
    (hv : v ∈ timeCritical C.G) :
    Function.Injective (spatialKerToAmbientKer C v hv) := by
  intro x y hxy
  apply Subtype.ext
  have h := congrArg (spacePart (n := n)) (congrArg Subtype.val hxy)
  simpa [spatialKerToAmbientKer, spaceInclL_apply] using h


-- @@ L60-79 verbatim
theorem spatialKerToAmbientKer_surjective
    (C : FramedLevelCobordism n) (v : E')
    (hv : v ∈ timeCritical C.G) :
    Function.Surjective (spatialKerToAmbientKer C v hv) := by
  have hregular : Function.Surjective (fderiv ℝ C.G v) :=
    C.regular v hv.1
  have htime : ∀ w : E', fderiv ℝ C.G v w = 0 → tcoord w = 0 :=
    (mem_timeCritical_iff_tcoord_eq_zero_on_ker hv.1 hregular).mp hv
  intro w
  have hwzero : fderiv ℝ C.G v w.1 = 0 := LinearMap.mem_ker.mp w.2
  have hwtime : tcoord w.1 = 0 := htime w.1 hwzero
  let x : LinearMap.ker ((spatialDeriv C.G v).toLinearMap) :=
    ⟨spacePart w.1, by
      rw [LinearMap.mem_ker]
      change spatialDeriv C.G v (spacePart w.1) = 0
      rw [spatialDeriv_apply, spaceInclL_spacePart hwtime]
      exact hwzero⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact spaceInclL_spacePart hwtime


-- @@ L81-89 verbatim
/-- At a time-critical point, spatial inclusion is a linear equivalence
between the spatial kernel and the two-dimensional ambient tangent kernel. -/
def spatialKerEquivAmbientKer (C : FramedLevelCobordism n) (v : E')
    (hv : v ∈ timeCritical C.G) :
    LinearMap.ker ((spatialDeriv C.G v).toLinearMap) ≃ₗ[ℝ]
      LinearMap.ker ((fderiv ℝ C.G v).toLinearMap) :=
  LinearEquiv.ofBijective (spatialKerToAmbientKer C v hv)
    ⟨spatialKerToAmbientKer_injective C v hv,
      spatialKerToAmbientKer_surjective C v hv⟩


-- @@ L91-99 verbatim
/-- The kernel of the spatial differential is exactly two-dimensional at a
time-critical point. -/
theorem finrank_ker_spatialDeriv_of_mem_timeCritical
    (C : FramedLevelCobordism n) {v : E'}
    (hv : v ∈ timeCritical C.G) :
    Module.finrank ℝ
        (LinearMap.ker ((spatialDeriv C.G v).toLinearMap)) = 2 := by
  rw [(spatialKerEquivAmbientKer C v hv).finrank_eq]
  exact LocalIFTSurfaceChart.finrank_ker_fderiv C (C.regular v hv.1)


-- @@ L101-111 verbatim
/-- Rank-nullity leaves exactly `n - 1` independent spatial normal rows. -/
theorem finrank_range_spatialDeriv_of_mem_timeCritical
    (C : FramedLevelCobordism n) {v : E'}
    (hv : v ∈ timeCritical C.G) :
    Module.finrank ℝ
        (LinearMap.range ((spatialDeriv C.G v).toLinearMap)) = n - 1 := by
  have hrank :=
    ((spatialDeriv C.G v).toLinearMap.finrank_range_add_finrank_ker)
  rw [finrank_ker_spatialDeriv_of_mem_timeCritical C hv,
    finrank_euclideanSpace_fin] at hrank
  omega


-- @@ L113-124 verbatim
/-- Equivalently, the adjoint spatial-gradient map has rank `n - 1`. -/
theorem finrank_range_adjoint_spatialDeriv_of_mem_timeCritical
    (C : FramedLevelCobordism n) {v : E'}
    (hv : v ∈ timeCritical C.G) :
    Module.finrank ℝ
        (LinearMap.range
          (ContinuousLinearMap.adjoint (spatialDeriv C.G v)).toLinearMap) =
      n - 1 := by
  change Module.finrank ℝ
      (LinearMap.range ((spatialDeriv C.G v).toLinearMap.adjoint)) = n - 1
  rw [LinearMap.finrank_range_adjoint]
  exact finrank_range_spatialDeriv_of_mem_timeCritical C hv


-- @@ L126-136 verbatim
/-- A genuine time-critical point can only occur when the codomain has
positive dimension. -/
theorem one_le_of_mem_timeCritical
    (C : FramedLevelCobordism n) {v : E'}
    (hv : v ∈ timeCritical C.G) : 1 ≤ n := by
  by_contra hn
  have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
  subst n
  apply hv.2
  intro y
  exact ⟨0, Subsingleton.elim _ _⟩


-- @@ L138-151 verbatim
/-- The missing output-normal direction is a one-dimensional cokernel line. -/
theorem finrank_orthogonal_range_spatialDeriv_of_mem_timeCritical
    (C : FramedLevelCobordism n) {v : E'}
    (hv : v ∈ timeCritical C.G) :
    Module.finrank ℝ
        (LinearMap.range ((spatialDeriv C.G v).toLinearMap))ᗮ = 1 := by
  let K := LinearMap.range ((spatialDeriv C.G v).toLinearMap)
  have hsum := K.finrank_add_finrank_orthogonal
  have hrange : Module.finrank ℝ K = n - 1 :=
    finrank_range_spatialDeriv_of_mem_timeCritical C hv
  have hn : 1 ≤ n := one_le_of_mem_timeCritical C hv
  rw [hrange, finrank_euclideanSpace_fin] at hsum
  have horth : Module.finrank ℝ Kᗮ = 1 := by omega
  simpa [K] using horth


-- @@ L153-166 verbatim
/-- A canonical (choice-based) nonzero vector spanning the missing output
normal line at a time-critical point. -/
def criticalOutputCokernelVector
    (C : FramedLevelCobordism n) (v : E')
    (hv : v ∈ timeCritical C.G) : F := by
  let K := (LinearMap.range ((spatialDeriv C.G v).toLinearMap))ᗮ
  have hK : K ≠ ⊥ := by
    intro hbot
    have hdim :=
      finrank_orthogonal_range_spatialDeriv_of_mem_timeCritical C hv
    change Module.finrank ℝ K = 1 at hdim
    rw [hbot, finrank_bot] at hdim
    omega
  exact Classical.choose (Submodule.exists_mem_ne_zero_of_ne_bot hK)


-- @@ L168-180 verbatim
theorem criticalOutputCokernelVector_mem
    (C : FramedLevelCobordism n) (v : E')
    (hv : v ∈ timeCritical C.G) :
    criticalOutputCokernelVector C v hv ∈
      (LinearMap.range ((spatialDeriv C.G v).toLinearMap))ᗮ := by
  dsimp [criticalOutputCokernelVector]
  exact (Classical.choose_spec (Submodule.exists_mem_ne_zero_of_ne_bot
    (by
      intro hbot
      have hdim :=
        finrank_orthogonal_range_spatialDeriv_of_mem_timeCritical C hv
      rw [hbot, finrank_bot] at hdim
      omega))).1


-- @@ L182-193 verbatim
theorem criticalOutputCokernelVector_ne_zero
    (C : FramedLevelCobordism n) (v : E')
    (hv : v ∈ timeCritical C.G) :
    criticalOutputCokernelVector C v hv ≠ 0 := by
  dsimp [criticalOutputCokernelVector]
  exact (Classical.choose_spec (Submodule.exists_mem_ne_zero_of_ne_bot
    (by
      intro hbot
      have hdim :=
        finrank_orthogonal_range_spatialDeriv_of_mem_timeCritical C hv
      rw [hbot, finrank_bot] at hdim
      omega))).2


-- @@ L195-203 verbatim
/-- The adjoint spatial derivative kills the chosen cokernel vector. -/
theorem adjoint_spatialDeriv_criticalOutputCokernelVector
    (C : FramedLevelCobordism n) (v : E')
    (hv : v ∈ timeCritical C.G) :
    ContinuousLinearMap.adjoint (spatialDeriv C.G v)
        (criticalOutputCokernelVector C v hv) = 0 := by
  have hmem := criticalOutputCokernelVector_mem C v hv
  rw [ContinuousLinearMap.orthogonal_range] at hmem
  exact LinearMap.mem_ker.mp hmem


-- @@ L205-205 verbatim
end Submission
