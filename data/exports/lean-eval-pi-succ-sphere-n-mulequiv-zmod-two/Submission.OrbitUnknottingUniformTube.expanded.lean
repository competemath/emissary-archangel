import Mathlib
import Submission.OrbitUnknottingTubularChart


-- @@ L4-10 verbatim
/-!
# Uniform tubular neighborhoods of intrinsic orbits

The inverse function theorem gives a source neighborhood at every point of
the zero section.  This file starts the compactness step by extracting an
explicit phase interval times a normal ball inside each such source.
-/


-- @@ L12-12 verbatim
set_option autoImplicit false

-- @@ L13-13 verbatim
set_option maxHeartbeats 800000


-- @@ L15-15 verbatim
noncomputable section


-- @@ L17-17 verbatim
open Set Function

-- @@ L18-18 verbatim
open scoped Topology


-- @@ L20-20 verbatim
namespace Submission

-- @@ L21-21 verbatim
namespace TamedField


-- @@ L23-23 verbatim
variable {n : ℕ} {X : FramedLevelSet n} (V : TamedField X)


-- @@ L25-25 verbatim
local notation "N" => EuclideanSpace ℝ (Fin n)

-- @@ L26-26 verbatim
local notation "C" => AddCircle (1 : ℝ)


-- @@ L28-31 verbatim
/-- The periodic framed tube descended to the intrinsic quotient circle. -/
def orbitTube (O : V.OrbitIndex) (q : C × N) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  (V.periodic_orbitTubeLift O q.2).lift q.1


-- @@ L33-35 verbatim
@[simp] theorem orbitTube_coe (O : V.OrbitIndex) (u : ℝ) (z : N) :
    V.orbitTube O ((u : C), z) = V.orbitTubeLift O (u, z) := by
  simp [orbitTube]


-- @@ L37-46 verbatim
/-- The quotient tube is jointly continuous in phase and normal
coordinates. -/
theorem continuous_orbitTube (O : V.OrbitIndex) :
    Continuous (V.orbitTube O) := by
  have hq : IsOpenQuotientMap
      (Prod.map (fun u : ℝ => (u : C)) (id : N → N)) :=
    QuotientAddGroup.isOpenQuotientMap_mk.prodMap IsOpenQuotientMap.id
  rw [← hq.continuous_comp_iff]
  simpa [Function.comp_def, Prod.map] using
    (V.contDiff_orbitTubeLift O).continuous


-- @@ L48-52 verbatim
/-- The zero section of the quotient tube is the intrinsic embedded orbit. -/
@[simp] theorem orbitTube_zero (O : V.OrbitIndex) (a : C) :
    V.orbitTube O (a, 0) = V.intrinsicOrbitEmbedding O a := by
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective a
  simp


-- @@ L54-69 verbatim
/-- Around every phase, a genuine phase interval times a positive normal
ball lies in the local inverse-function-theorem source. -/
theorem exists_orbitTube_local_box (O : V.OrbitIndex) (u : ℝ) :
    ∃ ε > 0, ∃ r > 0,
      Ioo (u - ε) (u + ε) ×ˢ Metric.ball (0 : N) r ⊆
        (V.orbitTubeLocalHomeomorph O u).source := by
  have hnhds : (V.orbitTubeLocalHomeomorph O u).source ∈
      𝓝 (u, (0 : N)) :=
    (V.orbitTubeLocalHomeomorph O u).open_source.mem_nhds
      (V.orbitTube_center_mem_localSource O u)
  rcases mem_nhds_prod_iff.mp hnhds with ⟨U, hU, W, hW, hUW⟩
  rcases Metric.mem_nhds_iff.mp hU with ⟨ε, hε, hεU⟩
  rcases Metric.mem_nhds_iff.mp hW with ⟨r, hr, hrW⟩
  refine ⟨ε, hε, r, hr, ?_⟩
  rw [← Real.ball_eq_Ioo]
  exact (prod_mono hεU hrW).trans hUW


-- @@ L71-80 verbatim
/-- Consequently the framed tube is injective on one explicit phase box at
every point of its zero section. -/
theorem exists_orbitTube_injective_local_box (O : V.OrbitIndex) (u : ℝ) :
    ∃ ε > 0, ∃ r > 0,
      Set.InjOn (V.orbitTubeLift O)
        (Ioo (u - ε) (u + ε) ×ˢ Metric.ball (0 : N) r) := by
  rcases V.exists_orbitTube_local_box O u with
    ⟨ε, hε, r, hr, hbox⟩
  exact ⟨ε, hε, r, hr,
    (V.orbitTube_injOn_localSource O u).mono hbox⟩


-- @@ L82-92 verbatim
/-- Chosen local box data, used only to make the compactness argument
canonical enough to state without nested existential witnesses. -/
structure OrbitTubeLocalBoxData (O : V.OrbitIndex) (u : ℝ) where
  phaseRadius : ℝ
  phaseRadius_pos : 0 < phaseRadius
  normalRadius : ℝ
  normalRadius_pos : 0 < normalRadius
  box_subset_source :
    Ioo (u - phaseRadius) (u + phaseRadius) ×ˢ
        Metric.ball (0 : N) normalRadius ⊆
      (V.orbitTubeLocalHomeomorph O u).source


-- @@ L94-105 verbatim
/-- The local IFT result supplies local box data at every phase. -/
theorem nonempty_orbitTubeLocalBoxData (O : V.OrbitIndex) (u : ℝ) :
    Nonempty (V.OrbitTubeLocalBoxData O u) := by
  rcases V.exists_orbitTube_local_box O u with
    ⟨ε, hε, r, hr, hbox⟩
  exact ⟨{
    phaseRadius := ε
    phaseRadius_pos := hε
    normalRadius := r
    normalRadius_pos := hr
    box_subset_source := hbox
  }⟩


-- @@ L107-110 verbatim
/-- A fixed choice of IFT box at every phase. -/
def orbitTubeLocalBoxData (O : V.OrbitIndex) (u : ℝ) :
    V.OrbitTubeLocalBoxData O u :=
  Classical.choice (V.nonempty_orbitTubeLocalBoxData O u)


-- @@ L112-117 verbatim
@[simp] theorem mem_orbitTubeLocalBox_phase (O : V.OrbitIndex) (u : ℝ) :
    u ∈ Ioo
      (u - (V.orbitTubeLocalBoxData O u).phaseRadius)
      (u + (V.orbitTubeLocalBoxData O u).phaseRadius) := by
  constructor <;>
    linarith [(V.orbitTubeLocalBoxData O u).phaseRadius_pos]


-- @@ L119-125 verbatim
/-- The chosen local IFT box after descending the phase coordinate to the
quotient circle. -/
def orbitTubeQuotientBox (O : V.OrbitIndex) (u : ℝ) : Set (C × N) :=
  ((fun t : ℝ => (t : C)) '' Ioo
      (u - (V.orbitTubeLocalBoxData O u).phaseRadius)
      (u + (V.orbitTubeLocalBoxData O u).phaseRadius)) ×ˢ
    Metric.ball (0 : N) (V.orbitTubeLocalBoxData O u).normalRadius


-- @@ L127-131 verbatim
theorem isOpen_orbitTubeQuotientBox (O : V.OrbitIndex) (u : ℝ) :
    IsOpen (V.orbitTubeQuotientBox O u) := by
  apply IsOpen.prod
  · exact QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  · exact Metric.isOpen_ball


-- @@ L133-137 verbatim
@[simp] theorem orbitTube_zero_mem_quotientBox (O : V.OrbitIndex) (u : ℝ) :
    ((u : C), (0 : N)) ∈ V.orbitTubeQuotientBox O u := by
  exact ⟨⟨u, V.mem_orbitTubeLocalBox_phase O u, rfl⟩,
    Metric.mem_ball_self
      (V.orbitTubeLocalBoxData O u).normalRadius_pos⟩


-- @@ L139-155 verbatim
/-- Every chosen quotient box is an actual injectivity neighborhood for the
descended tube map. -/
theorem orbitTube_injOn_quotientBox (O : V.OrbitIndex) (u : ℝ) :
    Set.InjOn (V.orbitTube O) (V.orbitTubeQuotientBox O u) := by
  rintro ⟨a, z⟩ ⟨⟨ua, hua, rfl⟩, hz⟩
    ⟨b, w⟩ ⟨⟨ub, hub, rfl⟩, hw⟩ heq
  have heqLift : V.orbitTubeLift O (ua, z) =
      V.orbitTubeLift O (ub, w) := by
    simpa using heq
  have hmema : (ua, z) ∈ (V.orbitTubeLocalHomeomorph O u).source :=
    (V.orbitTubeLocalBoxData O u).box_subset_source ⟨hua, hz⟩
  have hmemb : (ub, w) ∈ (V.orbitTubeLocalHomeomorph O u).source :=
    (V.orbitTubeLocalBoxData O u).box_subset_source ⟨hub, hw⟩
  have hpair : (ua, z) = (ub, w) :=
    V.orbitTube_injOn_localSource O u hmema hmemb heqLift
  cases hpair
  rfl


-- @@ L157-172 verbatim
/-- The compact zero section has a finite cover by quotient-local injectivity
boxes. -/
theorem exists_finite_orbitTube_quotientBox_cover (O : V.OrbitIndex) :
    ∃ s : Finset ℝ,
      Set.range (fun a : C => (a, (0 : N))) ⊆
        ⋃ u ∈ s, V.orbitTubeQuotientBox O u := by
  have hcompact : IsCompact (Set.range fun a : C => (a, (0 : N))) :=
    isCompact_range (continuous_id.prodMk continuous_const)
  have hcover : Set.range (fun a : C => (a, (0 : N))) ⊆
      ⋃ u : ℝ, V.orbitTubeQuotientBox O u := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective a
    exact mem_iUnion.mpr ⟨u, V.orbitTube_zero_mem_quotientBox O u⟩
  exact hcompact.elim_finite_subcover
    (fun u : ℝ => V.orbitTubeQuotientBox O u)
    (V.isOpen_orbitTubeQuotientBox O) hcover


-- @@ L174-221 verbatim
/-- The finite quotient cover can be shrunk to one common positive normal
radius, while retaining injectivity in every selected chart. -/
theorem exists_finite_orbitTube_uniform_quotientBox_cover
    (O : V.OrbitIndex) :
    ∃ (s : Finset ℝ) (r : ℝ), s.Nonempty ∧ 0 < r ∧
      Set.range (fun a : C => (a, (0 : N))) ⊆
        ⋃ u ∈ s,
          ((fun t : ℝ => (t : C)) '' Ioo
              (u - (V.orbitTubeLocalBoxData O u).phaseRadius)
              (u + (V.orbitTubeLocalBoxData O u).phaseRadius)) ×ˢ
            Metric.ball (0 : N) r ∧
      ∀ u ∈ s, Set.InjOn (V.orbitTube O)
        (((fun t : ℝ => (t : C)) '' Ioo
            (u - (V.orbitTubeLocalBoxData O u).phaseRadius)
            (u + (V.orbitTubeLocalBoxData O u).phaseRadius)) ×ˢ
          Metric.ball (0 : N) r) := by
  classical
  obtain ⟨s, hs⟩ := V.exists_finite_orbitTube_quotientBox_cover O
  have hsne : s.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h] at hs
    have hzero := hs
      (show ((0 : C), (0 : N)) ∈
        Set.range (fun a : C => (a, (0 : N))) by exact ⟨0, rfl⟩)
    simpa using hzero
  let radii : Finset ℝ :=
    s.image fun u => (V.orbitTubeLocalBoxData O u).normalRadius
  have hradii : radii.Nonempty := hsne.image _
  let r : ℝ := radii.min' hradii
  have hrpos : 0 < r := by
    have hrmem : r ∈ radii := radii.min'_mem hradii
    rcases Finset.mem_image.mp hrmem with ⟨u, hu, hur⟩
    rw [← hur]
    exact (V.orbitTubeLocalBoxData O u).normalRadius_pos
  refine ⟨s, r, hsne, hrpos, ?_, ?_⟩
  · intro q hq
    have hq' := hs hq
    rcases mem_iUnion.mp hq' with ⟨u, hq'⟩
    rcases mem_iUnion.mp hq' with ⟨hu, hq'⟩
    rcases hq with ⟨a, rfl⟩
    exact mem_iUnion.mpr ⟨u, mem_iUnion.mpr ⟨hu,
      ⟨hq'.1, Metric.mem_ball_self hrpos⟩⟩⟩
  · intro u hu
    have hrle : r ≤ (V.orbitTubeLocalBoxData O u).normalRadius := by
      apply radii.min'_le
      exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
    apply (V.orbitTube_injOn_quotientBox O u).mono
    exact prod_mono Subset.rfl (Metric.ball_subset_ball hrle)


-- @@ L223-266 verbatim
/-- Compactness of one period gives finitely many phase boxes and a single
positive normal radius that works in every selected IFT chart. -/
theorem exists_finite_orbitTube_box_cover (O : V.OrbitIndex) :
    ∃ (s : Finset ℝ) (r : ℝ), s.Nonempty ∧ 0 < r ∧
      Icc (0 : ℝ) 1 ⊆
        ⋃ u ∈ s, Ioo
          (u - (V.orbitTubeLocalBoxData O u).phaseRadius)
          (u + (V.orbitTubeLocalBoxData O u).phaseRadius) ∧
      ∀ u ∈ s, Set.InjOn (V.orbitTubeLift O)
        (Ioo
            (u - (V.orbitTubeLocalBoxData O u).phaseRadius)
            (u + (V.orbitTubeLocalBoxData O u).phaseRadius) ×ˢ
          Metric.ball (0 : N) r) := by
  classical
  let U : ℝ → Set ℝ := fun u => Ioo
    (u - (V.orbitTubeLocalBoxData O u).phaseRadius)
    (u + (V.orbitTubeLocalBoxData O u).phaseRadius)
  have hcover : Icc (0 : ℝ) 1 ⊆ ⋃ u : ℝ, U u := by
    intro u hu
    exact mem_iUnion.mpr ⟨u, V.mem_orbitTubeLocalBox_phase O u⟩
  obtain ⟨s, hs⟩ := isCompact_Icc.elim_finite_subcover U
    (fun _ => isOpen_Ioo) hcover
  have hsne : s.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h] at hs
    have hzero := hs (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
    simpa using hzero
  let radii : Finset ℝ :=
    s.image fun u => (V.orbitTubeLocalBoxData O u).normalRadius
  have hradii : radii.Nonempty := hsne.image _
  let r : ℝ := radii.min' hradii
  have hrpos : 0 < r := by
    have hrmem : r ∈ radii := radii.min'_mem hradii
    rcases Finset.mem_image.mp hrmem with ⟨u, hu, hur⟩
    rw [← hur]
    exact (V.orbitTubeLocalBoxData O u).normalRadius_pos
  refine ⟨s, r, hsne, hrpos, hs, ?_⟩
  intro u hu
  have hrle : r ≤ (V.orbitTubeLocalBoxData O u).normalRadius := by
    apply radii.min'_le
    exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
  apply (V.orbitTube_injOn_localSource O u).mono
  exact (prod_mono Subset.rfl (Metric.ball_subset_ball hrle)).trans
    (V.orbitTubeLocalBoxData O u).box_subset_source


-- @@ L268-268 verbatim
end TamedField

-- @@ L269-269 verbatim
end Submission
