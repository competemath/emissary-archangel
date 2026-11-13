import Mathlib
import Submission.OrbitUnknottingUniformTube


-- @@ L4-12 verbatim
/-!
# A globally injective quotient tube around an intrinsic orbit

Local inverse-function-theorem charts make the quotient tube locally
injective along its compact zero section.  A compact Hausdorff separation
lemma upgrades this to injectivity on one open neighborhood of the entire
zero section.  The generalized tube lemma then extracts a single positive
normal radius.
-/


-- @@ L14-14 verbatim
set_option autoImplicit false

-- @@ L15-15 verbatim
set_option maxHeartbeats 800000


-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
open Set Function

-- @@ L20-20 verbatim
open scoped Topology


-- @@ L22-22 verbatim
namespace Submission

-- @@ L23-23 verbatim
namespace TamedField


-- @@ L25-25 verbatim
variable {n : ℕ} {X : FramedLevelSet n} (V : TamedField X)


-- @@ L27-27 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L28-28 verbatim
local notation "N" => EuclideanSpace ℝ (Fin n)

-- @@ L29-29 verbatim
local notation "C" => AddCircle (1 : ℝ)


-- @@ L31-73 verbatim
/-- The quotient tube is injective on one full constant-radius tube around
the compact intrinsic orbit. -/
theorem exists_orbitTube_global_injOn (O : V.OrbitIndex) :
    ∃ r > 0, Set.InjOn (V.orbitTube O)
      ((Set.univ : Set C) ×ˢ Metric.ball (0 : N) r) := by
  let Z : Set (C × N) := Set.range fun a : C => (a, (0 : N))
  have hZinj : Set.InjOn (V.orbitTube O) Z := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab
    have hab' : V.intrinsicOrbitEmbedding O a =
        V.intrinsicOrbitEmbedding O b := by
      simpa using hab
    have habase : a = b :=
      (V.isEmbedding_intrinsicOrbitEmbedding O).injective hab'
    subst b
    rfl
  have hZcompact : IsCompact Z :=
    isCompact_range (continuous_id.prodMk continuous_const)
  have hlocal : ∀ q ∈ Z, ∃ U ∈ 𝓝 q, Set.InjOn (V.orbitTube O) U := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective a
    exact ⟨V.orbitTubeQuotientBox O u,
      (V.isOpen_orbitTubeQuotientBox O u).mem_nhds
        (V.orbitTube_zero_mem_quotientBox O u),
      V.orbitTube_injOn_quotientBox O u⟩
  obtain ⟨T, hTopen, hZT, hTinj⟩ := hZinj.exists_isOpen_superset
    hZcompact
    (fun _ _ => (V.continuous_orbitTube O).continuousAt)
    hlocal
  have hzeroSection :
      (Set.univ : Set C) ×ˢ ({0} : Set N) ⊆ T := by
    rintro ⟨a, z⟩ ⟨-, hz⟩
    rw [Set.mem_singleton_iff] at hz
    change z = 0 at hz
    subst z
    exact hZT ⟨a, rfl⟩
  obtain ⟨U, W, hUopen, hWopen, hCU, hzeroW, hUWT⟩ :=
    generalized_tube_lemma (X := C) (Y := N)
      isCompact_univ isCompact_singleton hTopen hzeroSection
  have hzero_mem_W : (0 : N) ∈ W := hzeroW (Set.mem_singleton 0)
  rcases (Metric.isOpen_iff.mp hWopen) 0 hzero_mem_W with
    ⟨r, hr, hrW⟩
  refine ⟨r, hr, hTinj.mono ?_⟩
  exact (prod_mono hCU hrW).trans hUWT


-- @@ L75-126 verbatim
/-- After shrinking once, the globally injective open tube is also an
embedded copy of `AddCircle 1 × ball 0 r`.  Compactness is applied first on a
closed half-radius tube, and the result is then restricted to the open tube. -/
theorem exists_orbitTube_global_embedding (O : V.OrbitIndex) :
    ∃ r > 0,
      Set.InjOn (V.orbitTube O)
        ((Set.univ : Set C) ×ˢ Metric.ball (0 : N) r) ∧
      Topology.IsEmbedding
        (fun q : ↥((Set.univ : Set C) ×ˢ Metric.ball (0 : N) r) =>
          V.orbitTube O q.1) := by
  obtain ⟨R, hR, hRinj⟩ := V.exists_orbitTube_global_injOn O
  let r : ℝ := R / 2
  have hr : 0 < r := by
    dsimp [r]
    linarith
  have hrR : r < R := by
    dsimp [r]
    linarith
  let Dopen : Set (C × N) :=
    (Set.univ : Set C) ×ˢ Metric.ball (0 : N) r
  let Dclosed : Set (C × N) :=
    (Set.univ : Set C) ×ˢ Metric.closedBall (0 : N) r
  have hopenClosed : Dopen ⊆ Dclosed := by
    exact prod_mono Subset.rfl Metric.ball_subset_closedBall
  have hclosedBig : Dclosed ⊆
      (Set.univ : Set C) ×ˢ Metric.ball (0 : N) R := by
    exact prod_mono Subset.rfl (Metric.closedBall_subset_ball hrR)
  have hinjClosed : Set.InjOn (V.orbitTube O) Dclosed :=
    hRinj.mono hclosedBig
  have hcompact : IsCompact Dclosed := by
    exact isCompact_univ.prod (isCompact_closedBall (0 : N) r)
  letI : CompactSpace Dclosed := isCompact_iff_compactSpace.mp hcompact
  have hcontClosed : Continuous
      (fun q : Dclosed => V.orbitTube O q.1) :=
    (V.continuous_orbitTube O).comp continuous_subtype_val
  have hinjClosed' : Function.Injective
      (fun q : Dclosed => V.orbitTube O q.1) := by
    intro p q hpq
    apply Subtype.ext
    exact hinjClosed p.property q.property hpq
  have hembClosed : Topology.IsEmbedding
      (fun q : Dclosed => V.orbitTube O q.1) :=
    (hcontClosed.isClosedEmbedding hinjClosed').isEmbedding
  have hembOpen : Topology.IsEmbedding
      (fun q : Dopen => V.orbitTube O q.1) := by
    simpa [Function.comp_def, Set.inclusion] using
      hembClosed.comp (Topology.IsEmbedding.inclusion hopenClosed)
  refine ⟨r, hr, ?_, ?_⟩
  · apply hRinj.mono
    exact prod_mono Subset.rfl
      (Metric.ball_subset_ball (le_of_lt hrR))
  · exact hembOpen


-- @@ L128-128 verbatim
end TamedField

-- @@ L129-129 verbatim
end Submission
