import Mathlib
import Submission.Delta
import Submission.TubeExplicitBridge


-- @@ L5-11 verbatim
/-!
# The northern orbit of the explicit tube bridge

The special tube bridge has an explicitly parametrized northern fiber.  This
module identifies that circle with a single orbit for every auxiliary tamed
field.  It is the component-counting input for the explicit ledger calculation.
-/


-- @@ L13-13 verbatim
noncomputable section


-- @@ L15-15 verbatim
namespace Submission


-- @@ L17-17 verbatim
open Set Function Metric

-- @@ L18-18 verbatim
open scoped RealInnerProductSpace Topology


-- @@ L20-20 verbatim
variable {m : ℕ}


-- @@ L22-22 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (m + 3))


-- @@ L24-63 verbatim
/-- Every point of the explicit northern circle lies on the flow orbit through
the point at angle zero.  The proof only uses connectedness of `ℝ`, compactness
of the orbit, and the flow-box theorem. -/
theorem tubeExplicitBridge_circle_mem_orbit (k : ℕ)
    (V : TamedField (tubeExplicitBridge (m := m) k).fls) (θ : ℝ) :
    tubeBridgeCirclePoint k (tubeExplicitBridge (m := m) k).y θ ∈
      V.orbit (tubeBridgeCirclePoint k (tubeExplicitBridge (m := m) k).y 0) := by
  let B := tubeExplicitBridge (m := m) k
  let γ : ℝ → E := tubeBridgeCirclePoint k B.y
  change γ θ ∈ V.orbit (γ 0)
  have hγ : Continuous γ := (contDiff_tubeBridgeCirclePoint k B.y).continuous
  have hγnorth : ∀ t, nprep B.approx (WithLp.ofLp (γ t)) = northPoint B.y := by
    intro t
    have ht : γ t ∈ Set.range (tubeBridgeCirclePoint k B.y) := ⟨t, rfl⟩
    rw [← tubeExplicitBridge_north_fiber_eq_range (m := m) k] at ht
    exact ht
  have hγfiber : ∀ t, γ t ∈ B.fls.fiber := by
    intro t
    rw [B.fiber_eq]
    exact Or.inl (hγnorth t)
  let A : Set ℝ := γ ⁻¹' V.orbit (γ 0)
  have hp : γ 0 ∈ B.fls.fiber := hγfiber 0
  have hAS : A ⊆ (Set.univ : Set ℝ) := fun _ _ => Set.mem_univ _
  have hAclosed : IsClosed A :=
    (V.isCompact_orbit hp).isClosed.preimage hγ
  have hAopen : ∀ t ∈ A, ∃ r > 0,
      (Set.univ : Set ℝ) ∩ Metric.ball t r ⊆ A := by
    intro t ht
    obtain ⟨r, hr, hrsub⟩ := V.orbit_isOpen_in_fiber hp ht
    have hopen : IsOpen (γ ⁻¹' Metric.ball (γ t) r) :=
      Metric.isOpen_ball.preimage hγ
    have htmem : t ∈ γ ⁻¹' Metric.ball (γ t) r := Metric.mem_ball_self hr
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hopen t htmem
    refine ⟨ε, hε, ?_⟩
    rintro u ⟨-, hut⟩
    exact hrsub ⟨hγfiber u, hεsub hut⟩
  have hA0 : A.Nonempty := ⟨0, V.mem_orbit_self (γ 0)⟩
  have hAll : (Set.univ : Set ℝ) ⊆ A :=
    subset_of_relOpen_closed isPreconnected_univ hAS hAclosed hAopen hA0
  exact hAll (Set.mem_univ θ)


-- @@ L65-94 verbatim
/-- The whole flow orbit through the explicit northern circle stays on that
circle.  Constancy of the canonical bridge sign excludes the southern sheet. -/
theorem tubeExplicitBridge_orbit_subset_circle (k : ℕ)
    (V : TamedField (tubeExplicitBridge (m := m) k).fls) :
    V.orbit (tubeBridgeCirclePoint k (tubeExplicitBridge (m := m) k).y 0) ⊆
      Set.range (tubeBridgeCirclePoint k (tubeExplicitBridge (m := m) k).y) := by
  let B := tubeExplicitBridge (m := m) k
  let γ : ℝ → E := tubeBridgeCirclePoint k B.y
  change V.orbit (γ 0) ⊆ Set.range γ
  have hγnorth : ∀ t, nprep B.approx (WithLp.ofLp (γ t)) = northPoint B.y := by
    intro t
    have ht : γ t ∈ Set.range (tubeBridgeCirclePoint k B.y) := ⟨t, rfl⟩
    rw [← tubeExplicitBridge_north_fiber_eq_range (m := m) k] at ht
    exact ht
  have hp : γ 0 ∈ B.fls.fiber := by
    rw [B.fiber_eq]
    exact Or.inl (hγnorth 0)
  have hppos : 0 < B.fiberSign (γ 0) := by
    rw [B.fiberSign_apply, hγnorth]
    exact vertC_northPoint_pos B.norm_y_lt_one
  intro x hx
  have hxfiber : x ∈ B.fls.fiber := V.orbit_subset_fiber hp hx
  have hxpos : 0 < B.fiberSign x :=
    (B.fiberSign.pos_iff_of_mem_orbit V hp hx).mp hppos
  have hxnorth : nprep B.approx (WithLp.ofLp x) = northPoint B.y :=
    (B.mem_north_iff hxfiber).mpr (by simpa using hxpos)
  have hxset : x ∈ {z : E |
      nprep B.approx (WithLp.ofLp z) = northPoint B.y} := hxnorth
  rw [tubeExplicitBridge_north_fiber_eq_range (m := m) k] at hxset
  exact hxset


-- @@ L96-104 verbatim
/-- The northern fiber of the explicit bridge is exactly one flow orbit. -/
theorem tubeExplicitBridge_north_orbit_eq_range (k : ℕ)
    (V : TamedField (tubeExplicitBridge (m := m) k).fls) :
    V.orbit (tubeBridgeCirclePoint k (tubeExplicitBridge (m := m) k).y 0) =
      Set.range (tubeBridgeCirclePoint k (tubeExplicitBridge (m := m) k).y) := by
  apply Set.Subset.antisymm
  · exact tubeExplicitBridge_orbit_subset_circle k V
  · rintro x ⟨θ, rfl⟩
    exact tubeExplicitBridge_circle_mem_orbit k V θ


-- @@ L106-130 verbatim
/-- The positive part of the canonical bridge sign is the explicit circle. -/
theorem tubeExplicitBridge_northPart_eq_range (k : ℕ) :
    (tubeExplicitBridge (m := m) k).northPart =
      Set.range
        (tubeBridgeCirclePoint k (tubeExplicitBridge (m := m) k).y) := by
  let B := tubeExplicitBridge (m := m) k
  let γ : ℝ → E := tubeBridgeCirclePoint k B.y
  change B.northPart = Set.range γ
  ext x
  constructor
  · intro hx
    have hxnorth := (B.mem_northPart_iff.mp hx).2
    have hxset : x ∈ {z : E |
        nprep B.approx (WithLp.ofLp z) = northPoint B.y} := hxnorth
    rw [tubeExplicitBridge_north_fiber_eq_range (m := m) k] at hxset
    exact hxset
  · intro hx
    have hxnorth : nprep B.approx (WithLp.ofLp x) = northPoint B.y := by
      have hxset : x ∈ Set.range (tubeBridgeCirclePoint k B.y) := hx
      rw [← tubeExplicitBridge_north_fiber_eq_range (m := m) k] at hxset
      exact hxset
    apply B.mem_northPart_iff.mpr
    refine ⟨?_, hxnorth⟩
    rw [B.fiber_eq]
    exact Or.inl hxnorth


-- @@ L132-140 verbatim
/-- The positive part is one intrinsic flow orbit, independently of the chosen
tamed extension. -/
theorem tubeExplicitBridge_northPart_eq_orbit (k : ℕ)
    (V : TamedField (tubeExplicitBridge (m := m) k).fls) :
    (tubeExplicitBridge (m := m) k).northPart =
      V.orbit
        (tubeBridgeCirclePoint k (tubeExplicitBridge (m := m) k).y 0) := by
  rw [tubeExplicitBridge_northPart_eq_range (m := m) k]
  exact (tubeExplicitBridge_north_orbit_eq_range k V).symm


-- @@ L142-152 verbatim
/-- The canonical orbit index of the northern component. -/
def tubeExplicitBridgeNorthOrbitIndex (k : ℕ)
    (V : TamedField (tubeExplicitBridge (m := m) k).fls) : V.OrbitIndex := by
  let B := tubeExplicitBridge (m := m) k
  let p : E := tubeBridgeCirclePoint k B.y 0
  refine ⟨V.orbit p, V.mem_orbitFinset.mpr ⟨p, ?_, rfl⟩⟩
  rw [B.fiber_eq]
  left
  have hp : p ∈ Set.range (tubeBridgeCirclePoint k B.y) := ⟨0, rfl⟩
  rw [← tubeExplicitBridge_north_fiber_eq_range (m := m) k] at hp
  exact hp


-- @@ L154-159 verbatim
@[simp] theorem tubeExplicitBridgeNorthOrbitIndex_coe (k : ℕ)
    (V : TamedField (tubeExplicitBridge (m := m) k).fls) :
    ((tubeExplicitBridgeNorthOrbitIndex k V : V.OrbitIndex) : Set E) =
      V.orbit
        (tubeBridgeCirclePoint k (tubeExplicitBridge (m := m) k).y 0) :=
  rfl


-- @@ L161-184 verbatim
/-- Among actual orbit indices, membership in the northern collection singles
out exactly the explicit northern orbit. -/
theorem tubeExplicitBridge_mem_northOrbitCollection_iff (k : ℕ)
    (V : TamedField (tubeExplicitBridge (m := m) k).fls) (O : V.OrbitIndex) :
    (O : Set E) ∈
        (tubeExplicitBridge (m := m) k).northOrbitCollection V ↔
      O = tubeExplicitBridgeNorthOrbitIndex k V := by
  let B := tubeExplicitBridge (m := m) k
  let p : E := tubeBridgeCirclePoint k B.y 0
  change (O : Set E) ⊆ B.northPart ↔
    O = tubeExplicitBridgeNorthOrbitIndex k V
  rw [tubeExplicitBridge_northPart_eq_orbit k V]
  constructor
  · intro hO
    apply Subtype.ext
    change (O : Set E) = V.orbit p
    rw [V.orbitPoint_orbit O]
    apply V.orbit_eq_of_mem
    apply hO
    rw [V.orbitPoint_orbit O]
    exact V.mem_orbit_self (V.orbitPoint O)
  · intro hO
    subst O
    exact Set.Subset.rfl


-- @@ L186-195 verbatim
/-- The northern ledger sum of the explicit bridge has a single summand. -/
theorem tubeExplicitBridge_northFramedDelta_eq_orbitContribution (k : ℕ)
    (V : TamedField (tubeExplicitBridge (m := m) k).fls) :
    (tubeExplicitBridge (m := m) k).northFramedDelta V =
      V.orbitContribution (tubeExplicitBridgeNorthOrbitIndex k V) := by
  classical
  rw [(tubeExplicitBridge (m := m) k).northFramedDelta_eq_deltaOn]
  unfold TamedField.deltaOn
  simp_rw [tubeExplicitBridge_mem_northOrbitCollection_iff k V]
  simp


-- @@ L197-197 verbatim
end Submission
