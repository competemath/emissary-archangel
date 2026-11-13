import Mathlib
import Submission.LevelFrame
import Submission.SOStable
import Submission.FiberSign
import Submission.CobordFlow


-- @@ L7-20 verbatim
/-!
# The framed one--manifold invariant `delta`

For a framed regular level set `X : FramedLevelSet n`, a `TamedField X` orients every
component and writes the compact fiber as a finite disjoint union of periodic flow
orbits.  This file turns those geometric ingredients into the finite `ZMod 2` sum

`delta = sum_O (loopClassZ2 (frame loop of O) + 1)`.

The orbit set, its representatives, and the periods used below are noncomputable, but
the resulting expression is an honest total Lean definition.  In particular, no
externally supplied list of components can contain duplicates or omit a component:
`orbitFinset` is the finite set of orbit *subsets* themselves.
-/


-- @@ L22-22 verbatim
noncomputable section


-- @@ L24-24 verbatim
namespace Submission


-- @@ L26-26 verbatim
open Set Function Topology

-- @@ L27-27 verbatim
open scoped RealInnerProductSpace Topology Matrix unitInterval BigOperators


-- @@ L29-29 verbatim
variable {n : ℕ}


-- @@ L31-31 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L33-33 verbatim
namespace TamedField


-- @@ L35-35 verbatim
variable {X : FramedLevelSet n} (V : TamedField X)


-- @@ L37-37 verbatim
/-! ## The canonical finite set of components -/


-- @@ L39-42 verbatim
/-- The set of flow-orbits occurring in the fiber.  Its elements are subsets of the
ambient Euclidean space, rather than chosen base points. -/
def orbitFamily : Set (Set E) :=
  {O | ∃ p ∈ X.fiber, O = V.orbit p}


-- @@ L44-54 verbatim
/-- Compactness and the flow-box theorem imply that the set of fiber orbits is
finite. -/
theorem finite_orbitFamily : (V.orbitFamily : Set (Set E)).Finite := by
  classical
  obtain ⟨s, hsFiber, hsCover⟩ := V.exists_finite_orbit_cover
  apply (s.finite_toSet.image fun p => V.orbit p).subset
  rintro O ⟨p, hp, rfl⟩
  have hp' : p ∈ ⋃ q ∈ s, V.orbit q := by rwa [← hsCover]
  obtain ⟨q, hqs, hpq⟩ := Set.mem_iUnion₂.mp hp'
  refine ⟨q, hqs, ?_⟩
  exact (V.orbit_eq_of_mem hpq).symm


-- @@ L56-60 verbatim
/-- The finite set of orbit subsets of the fiber.  Since this is a `Finset (Set E)`,
an orbit occurs exactly once, independently of the preliminary finite subcover used
to prove finiteness. -/
def orbitFinset : Finset (Set E) :=
  V.finite_orbitFamily.toFinset


-- @@ L62-65 verbatim
@[simp]
theorem mem_orbitFinset {O : Set E} :
    O ∈ V.orbitFinset ↔ ∃ p ∈ X.fiber, O = V.orbit p := by
  simp [orbitFinset, orbitFamily]


-- @@ L67-78 verbatim
/-- The fiber is exactly the union of the canonical orbit finset. -/
theorem fiber_eq_iUnion_orbitFinset :
    X.fiber = ⋃ O ∈ V.orbitFinset, O := by
  apply Set.Subset.antisymm
  · intro p hp
    have hO : V.orbit p ∈ V.orbitFinset :=
      V.mem_orbitFinset.mpr ⟨p, hp, rfl⟩
    exact Set.mem_iUnion₂.mpr ⟨V.orbit p, hO, V.mem_orbit_self p⟩
  · intro p hp
    obtain ⟨O, hO, hpO⟩ := Set.mem_iUnion₂.mp hp
    obtain ⟨q, hq, rfl⟩ := V.mem_orbitFinset.mp hO
    exact V.orbit_subset_fiber hq hpO


-- @@ L80-88 verbatim
/-- Distinct members of `orbitFinset` are disjoint. -/
theorem orbitFinset_pairwise_disjoint :
    ∀ O ∈ V.orbitFinset, ∀ P ∈ V.orbitFinset, O ≠ P → Disjoint O P := by
  intro O hO P hP hne
  obtain ⟨p, hp, rfl⟩ := V.mem_orbitFinset.mp hO
  obtain ⟨q, hq, rfl⟩ := V.mem_orbitFinset.mp hP
  rcases V.orbit_eq_or_disjoint (p := p) (q := q) with heq | hdisj
  · exact (hne heq).elim
  · exact hdisj


-- @@ L90-91 verbatim
/-- An index for a fiber component.  The underlying value is the orbit as a set. -/
abbrev OrbitIndex := {O : Set E // O ∈ V.orbitFinset}


-- @@ L93-95 verbatim
/-- A (noncomputably) chosen point on an orbit component. -/
def orbitPoint (O : V.OrbitIndex) : E :=
  Classical.choose (V.mem_orbitFinset.mp O.property)


-- @@ L97-98 verbatim
theorem orbitPoint_mem_fiber (O : V.OrbitIndex) : V.orbitPoint O ∈ X.fiber :=
  (Classical.choose_spec (V.mem_orbitFinset.mp O.property)).1


-- @@ L100-102 verbatim
theorem orbitPoint_orbit (O : V.OrbitIndex) :
    (O : Set E) = V.orbit (V.orbitPoint O) :=
  (Classical.choose_spec (V.mem_orbitFinset.mp O.property)).2


-- @@ L104-150 verbatim
/-- A unit-speed fiber flow is injective on some interval around time zero. -/
theorem exists_flow_injective_Ioo {p : E} (hp : p ∈ X.fiber) :
    ∃ ε > 0, Set.InjOn (V.flow p) (Ioo (-ε) ε) := by
  let τ : E := tauField X.g p
  let h : ℝ → ℝ := fun s => ⟪τ, V.flow p s - p⟫
  let h' : ℝ → ℝ := fun s => ⟪τ, V.v (V.flow p s)⟫
  have hder : ∀ s, HasDerivAt h (h' s) s := by
    intro s
    have h1 : HasDerivAt (fun _ : ℝ => τ) 0 s := hasDerivAt_const s τ
    have h2 : HasDerivAt (fun u => V.flow p u - p) (V.v (V.flow p s)) s :=
      (V.hasDerivAt_flow p s).sub_const p
    simpa [h, h'] using h1.inner ℝ h2
  have h'cont : Continuous h' := by
    exact continuous_const.inner (V.smooth.continuous.comp (V.continuous_flow p))
  have h'zero : h' 0 = 1 := by
    dsimp [h']
    rw [V.flow_zero, V.v_eq_tau_of_mem_fiber hp]
    change ⟪tauField X.g p, tauField X.g p⟫ = 1
    rw [real_inner_self_eq_norm_sq, norm_tauField (X.fiber_subset_regularSet hp)]
    norm_num
  have hopen : IsOpen {s : ℝ | 0 < h' s} := isOpen_lt continuous_const h'cont
  have hzero : (0 : ℝ) ∈ {s : ℝ | 0 < h' s} := by
    change 0 < h' 0
    rw [h'zero]
    norm_num
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hopen 0 hzero
  refine ⟨ε, hε, ?_⟩
  have hmono : StrictMonoOn h (Ioo (-ε) ε) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo (-ε) ε)
    · exact fun s hs => (hder s).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Ioo] at hs
      rw [(hder s).deriv]
      apply hεsub
      rw [Metric.mem_ball, Real.dist_eq, sub_zero]
      exact abs_lt.mpr hs
  intro s hs t ht hst
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hlt' := hmono hs ht hlt
    have heq : h s = h t := by dsimp [h]; rw [hst]
    rw [heq] at hlt'
    exact (lt_irrefl _ hlt')
  · have hgt' := hmono ht hs hgt
    have heq : h t = h s := by dsimp [h]; rw [hst]
    rw [heq] at hgt'
    exact (lt_irrefl _ hgt')


-- @@ L152-159 verbatim
/-- The additive subgroup of all periods of the flow through `p`. -/
def flowPeriods (p : E) : AddSubgroup ℝ where
  carrier := {T | Function.Periodic (V.flow p) T}
  zero_mem' := by
    intro t
    simp
  add_mem' hT hS := hT.add_period hS
  neg_mem' hT := hT.neg


-- @@ L161-163 verbatim
@[simp]
theorem mem_flowPeriods {p : E} {T : ℝ} :
    T ∈ V.flowPeriods p ↔ Function.Periodic (V.flow p) T := Iff.rfl


-- @@ L165-182 verbatim
/-- The period subgroup of a fiber flow is discrete. -/
theorem discreteTopology_flowPeriods {p : E} (hp : p ∈ X.fiber) :
    DiscreteTopology (V.flowPeriods p) := by
  obtain ⟨ε, hε, hinj⟩ := V.exists_flow_injective_Ioo hp
  rw [discreteTopology_iff_isOpen_singleton_zero, isOpen_induced_iff]
  refine ⟨Ioo (-ε) ε, isOpen_Ioo, ?_⟩
  ext ⟨T, hT⟩
  change (T ∈ Ioo (-ε) ε) ↔ (⟨T, hT⟩ : V.flowPeriods p) = 0
  constructor
  · intro hTI
    apply Subtype.ext
    have h0I : (0 : ℝ) ∈ Ioo (-ε) ε := by constructor <;> linarith
    apply hinj hTI h0I
    simpa using hT 0
  · intro hEq
    have hT0 : T = 0 := congrArg Subtype.val hEq
    rw [hT0]
    constructor <;> linarith


-- @@ L184-189 verbatim
/-- A generator of the discrete period subgroup. -/
def periodGenerator {p : E} (hp : p ∈ X.fiber) : V.flowPeriods p := by
  letI : DiscreteTopology (V.flowPeriods p) := V.discreteTopology_flowPeriods hp
  have hcyc : IsAddCyclic (V.flowPeriods p) :=
    AddSubgroup.discrete_iff_addCyclic.mpr inferInstance
  exact Classical.choose (isAddCyclic_iff_exists_zmultiples_eq_top.mp hcyc)


-- @@ L191-196 verbatim
theorem zmultiples_periodGenerator {p : E} (hp : p ∈ X.fiber) :
    AddSubgroup.zmultiples (V.periodGenerator hp) = ⊤ := by
  letI : DiscreteTopology (V.flowPeriods p) := V.discreteTopology_flowPeriods hp
  exact Classical.choose_spec (isAddCyclic_iff_exists_zmultiples_eq_top.mp
    (AddSubgroup.discrete_iff_addCyclic.mpr inferInstance :
      IsAddCyclic (V.flowPeriods p)))


-- @@ L198-202 verbatim
/-- The positive fundamental period, obtained from the generator of the discrete
period subgroup.  Taking the absolute value removes the sign ambiguity in the
choice of a cyclic generator. -/
def fundamentalPeriod {p : E} (hp : p ∈ X.fiber) : ℝ :=
  |((V.periodGenerator hp : V.flowPeriods p) : ℝ)|


-- @@ L204-217 verbatim
theorem fundamentalPeriod_pos {p : E} (hp : p ∈ X.fiber) :
    0 < V.fundamentalPeriod hp := by
  rw [fundamentalPeriod, abs_pos]
  intro hgen0
  obtain ⟨T, hT, hper⟩ := V.exists_period hp
  let q : V.flowPeriods p := ⟨T, hper⟩
  have hq : q ∈ AddSubgroup.zmultiples (V.periodGenerator hp) := by
    rw [V.zmultiples_periodGenerator hp]
    exact Set.mem_univ q
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hq
  have hzero : V.periodGenerator hp = 0 := Subtype.ext hgen0
  rw [hzero, smul_zero] at hk
  have hT0 : T = 0 := congrArg Subtype.val hk.symm
  linarith


-- @@ L219-227 verbatim
theorem fundamentalPeriod_periodic {p : E} (hp : p ∈ X.fiber) :
    Function.Periodic (V.flow p) (V.fundamentalPeriod hp) := by
  have hgen : Function.Periodic (V.flow p) ((V.periodGenerator hp : V.flowPeriods p) : ℝ) :=
    (V.periodGenerator hp).property
  unfold fundamentalPeriod
  rcases le_total 0 ((V.periodGenerator hp : V.flowPeriods p) : ℝ) with h | h
  · rwa [abs_of_nonneg h]
  · rw [abs_of_nonpos h]
    exact hgen.neg


-- @@ L229-262 verbatim
/-- The fundamental period is no larger than any positive period. -/
theorem fundamentalPeriod_le_period {p : E} (hp : p ∈ X.fiber) {T : ℝ}
    (hTpos : 0 < T) (hT : Function.Periodic (V.flow p) T) :
    V.fundamentalPeriod hp ≤ T := by
  let q : V.flowPeriods p := ⟨T, hT⟩
  have hq : q ∈ AddSubgroup.zmultiples (V.periodGenerator hp) := by
    rw [V.zmultiples_periodGenerator hp]
    exact Set.mem_univ q
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hq
  have hval : (k : ℝ) * ((V.periodGenerator hp : V.flowPeriods p) : ℝ) = T := by
    simpa using congrArg Subtype.val hk
  have hgenne : ((V.periodGenerator hp : V.flowPeriods p) : ℝ) ≠ 0 := by
    intro h0
    have := V.fundamentalPeriod_pos hp
    rw [fundamentalPeriod, h0, abs_zero] at this
    exact (lt_irrefl 0 this)
  have hkne : k ≠ 0 := by
    intro hk0
    rw [hk0, Int.cast_zero, zero_mul] at hval
    linarith
  have hkabs : (1 : ℝ) ≤ |(k : ℝ)| := by
    calc
      (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
      _ ≤ ((|k| : ℤ) : ℝ) := by exact_mod_cast Int.one_le_abs hkne
      _ = |(k : ℝ)| := Int.cast_abs
  unfold fundamentalPeriod
  calc
    |((V.periodGenerator hp : V.flowPeriods p) : ℝ)|
        ≤ |(k : ℝ)| * |((V.periodGenerator hp : V.flowPeriods p) : ℝ)| :=
      le_mul_of_one_le_left (abs_nonneg _) hkabs
    _ = |(k : ℝ) * ((V.periodGenerator hp : V.flowPeriods p) : ℝ)| :=
      (abs_mul _ _).symm
    _ = |T| := by rw [hval]
    _ = T := abs_of_pos hTpos


-- @@ L264-272 verbatim
/-- Periods are preserved when the base point is shifted along its flow orbit. -/
theorem periodic_flow_of_mem_orbit {p q : E} (hq : q ∈ V.orbit p) {T : ℝ}
    (hT : Function.Periodic (V.flow p) T) :
    Function.Periodic (V.flow q) T := by
  obtain ⟨a, rfl⟩ := hq
  intro t
  rw [congrFun (V.flow_shift p a) (t + T), congrFun (V.flow_shift p a) t]
  have h := hT (a + t)
  convert h using 1 <;> ring


-- @@ L274-286 verbatim
/-- The positive fundamental period is independent of the chosen point on an orbit. -/
theorem fundamentalPeriod_eq_of_mem_orbit {p q : E} (hp : p ∈ X.fiber)
    (hq : q ∈ V.orbit p) :
    V.fundamentalPeriod (V.orbit_subset_fiber hp hq) = V.fundamentalPeriod hp := by
  let hqFiber : q ∈ X.fiber := V.orbit_subset_fiber hp hq
  have hpq : p ∈ V.orbit q := by
    rw [V.orbit_eq_of_mem hq]
    exact V.mem_orbit_self p
  apply le_antisymm
  · exact V.fundamentalPeriod_le_period hqFiber (V.fundamentalPeriod_pos hp)
      (V.periodic_flow_of_mem_orbit hq (V.fundamentalPeriod_periodic hp))
  · exact V.fundamentalPeriod_le_period hp (V.fundamentalPeriod_pos hqFiber)
      (V.periodic_flow_of_mem_orbit hpq (V.fundamentalPeriod_periodic hqFiber))


-- @@ L288-290 verbatim
/-- The positive fundamental period of the unit-speed flow on an orbit component. -/
def orbitPeriod (O : V.OrbitIndex) : ℝ :=
  V.fundamentalPeriod (V.orbitPoint_mem_fiber O)


-- @@ L292-294 verbatim
theorem orbitPeriod_pos (O : V.OrbitIndex) :
    0 < V.orbitPeriod O :=
  V.fundamentalPeriod_pos (V.orbitPoint_mem_fiber O)


-- @@ L296-298 verbatim
theorem flow_periodic_orbitPeriod (O : V.OrbitIndex) :
    Function.Periodic (V.flow (V.orbitPoint O)) (V.orbitPeriod O) :=
  V.fundamentalPeriod_periodic (V.orbitPoint_mem_fiber O)


-- @@ L300-300 verbatim
/-! ## The `SO` loop and its class -/


-- @@ L302-311 verbatim
/-- The frame loop based at an arbitrary fiber point, parametrized by its intrinsic
fundamental period. -/
def fundamentalFrameLoop {p : E} (hp : p ∈ X.fiber) : C(I, SOGroup (n + 1)) where
  toFun u :=
    ⟨frameLoop X (V.flow p) ((u : ℝ) * V.fundamentalPeriod hp),
      frameLoop_mem_specialOrthogonalGroup X (V.flow_mem_fiber hp) _⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_frameLoop X (V.continuous_flow p) (V.flow_mem_fiber hp)).comp
      (continuous_subtype_val.mul continuous_const)


-- @@ L313-319 verbatim
theorem fundamentalFrameLoop_closed {p : E} (hp : p ∈ X.fiber) :
    V.fundamentalFrameLoop hp 0 = V.fundamentalFrameLoop hp 1 := by
  apply Subtype.ext
  change frameLoop X (V.flow p) (0 * V.fundamentalPeriod hp) =
    frameLoop X (V.flow p) (1 * V.fundamentalPeriod hp)
  simpa using
    (frameLoop_periodic X (V.fundamentalPeriod_periodic hp) 0).symm


-- @@ L321-323 verbatim
/-- Intrinsic frame class based at a fiber point. -/
def fundamentalFrameClass {p : E} (hp : p ∈ X.fiber) : ZMod 2 :=
  loopClassZ2 (V.fundamentalFrameLoop hp) (V.fundamentalFrameLoop_closed hp)


-- @@ L325-371 verbatim
/-- The intrinsic frame class is independent of the chosen point on a flow orbit. -/
theorem fundamentalFrameClass_eq_of_mem_orbit {p q : E} (hp : p ∈ X.fiber)
    (hq : q ∈ V.orbit p) :
    V.fundamentalFrameClass (V.orbit_subset_fiber hp hq) =
      V.fundamentalFrameClass hp := by
  obtain ⟨a, rfl⟩ := hq
  let hqFiber : V.flow p a ∈ X.fiber := V.flow_mem_fiber hp a
  have hT : V.fundamentalPeriod hqFiber = V.fundamentalPeriod hp :=
    V.fundamentalPeriod_eq_of_mem_orbit hp (V.flow_mem_orbit p a)
  symm
  apply loopClassZ2_congr
    (V.fundamentalFrameLoop_closed hp) (V.fundamentalFrameLoop_closed hqFiber)
    ({ toFun := fun z =>
        ⟨frameLoop X (V.flow p)
            ((z.1 : ℝ) * a + (z.2 : ℝ) * V.fundamentalPeriod hp),
          frameLoop_mem_specialOrthogonalGroup X (V.flow_mem_fiber hp) _⟩
       continuous_toFun := by
         apply Continuous.subtype_mk
         exact (continuous_frameLoop X (V.continuous_flow p) (V.flow_mem_fiber hp)).comp
           ((continuous_subtype_val.comp continuous_fst).mul continuous_const |>.add
             ((continuous_subtype_val.comp continuous_snd).mul continuous_const))
       map_zero_left := fun u => by
         apply Subtype.ext
         change frameLoop X (V.flow p)
           (((0 : I) : ℝ) * a + (u : ℝ) * V.fundamentalPeriod hp) =
             frameLoop X (V.flow p) ((u : ℝ) * V.fundamentalPeriod hp)
         congr 2
         norm_num
       map_one_left := fun u => by
         apply Subtype.ext
         change frameLoop X (V.flow p)
           (((1 : I) : ℝ) * a + (u : ℝ) * V.fundamentalPeriod hp) =
             frameLoop X (V.flow (V.flow p a))
               ((u : ℝ) * V.fundamentalPeriod hqFiber)
         rw [hT]
         unfold frameLoop
         rw [congrFun (V.flow_shift p a) ((u : ℝ) * V.fundamentalPeriod hp)]
         congr 2
         norm_num })
  intro s
  apply Subtype.ext
  change frameLoop X (V.flow p)
      ((s : ℝ) * a + ((0 : I) : ℝ) * V.fundamentalPeriod hp) =
    frameLoop X (V.flow p)
      ((s : ℝ) * a + ((1 : I) : ℝ) * V.fundamentalPeriod hp)
  simpa using
    (frameLoop_periodic X (V.fundamentalPeriod_periodic hp) ((s : ℝ) * a)).symm


-- @@ L373-376 verbatim
/-- The frame loop of an orbit, parametrized once over the unit interval using the
chosen positive period. -/
def orbitFrameLoop (O : V.OrbitIndex) : C(I, SOGroup (n + 1)) :=
  V.fundamentalFrameLoop (V.orbitPoint_mem_fiber O)


-- @@ L378-381 verbatim
/-- The packaged frame map really is a closed loop. -/
theorem orbitFrameLoop_closed (O : V.OrbitIndex) :
    V.orbitFrameLoop O 0 = V.orbitFrameLoop O 1 :=
  V.fundamentalFrameLoop_closed (V.orbitPoint_mem_fiber O)


-- @@ L383-385 verbatim
/-- The `ZMod 2` frame class of one orbit component. -/
def orbitFrameClass (O : V.OrbitIndex) : ZMod 2 :=
  loopClassZ2 (V.orbitFrameLoop O) (V.orbitFrameLoop_closed O)


-- @@ L387-389 verbatim
theorem orbitFrameClass_eq_fundamental (O : V.OrbitIndex) :
    V.orbitFrameClass O =
      V.fundamentalFrameClass (V.orbitPoint_mem_fiber O) := rfl


-- @@ L391-394 verbatim
/-- The contribution of an oriented framed circle.  The extra `1` is the tangent
line contribution in the Pontryagin--Thom convention. -/
def orbitContribution (O : V.OrbitIndex) : ZMod 2 :=
  V.orbitFrameClass O + 1


-- @@ L396-396 verbatim
/-! ## `delta`, empty fibers, and disjoint additivity -/


-- @@ L398-400 verbatim
/-- The framed one-manifold invariant of the level set. -/
def framedDelta : ZMod 2 :=
  ∑ O : V.OrbitIndex, V.orbitContribution O


-- @@ L402-407 verbatim
/-- Restriction of `delta` to a collection of orbit subsets.  This is useful for
clopen unions of components and for slice transport component-by-component. -/
def deltaOn (A : Set (Set E)) : ZMod 2 := by
  classical
  exact ∑ O : V.OrbitIndex,
    if (O : Set E) ∈ A then V.orbitContribution O else 0


-- @@ L409-411 verbatim
@[simp]
theorem deltaOn_empty : V.deltaOn (∅ : Set (Set E)) = 0 := by
  simp [deltaOn]


-- @@ L413-415 verbatim
@[simp]
theorem deltaOn_univ : V.deltaOn (Set.univ : Set (Set E)) = V.framedDelta := by
  simp [deltaOn, framedDelta]


-- @@ L417-429 verbatim
/-- Additivity on a disjoint union of collections of components. -/
theorem deltaOn_union_of_disjoint {A B : Set (Set E)} (hAB : Disjoint A B) :
    V.deltaOn (A ∪ B) = V.deltaOn A + V.deltaOn B := by
  classical
  rw [deltaOn, deltaOn, deltaOn, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro O hO
  by_cases hA : (O : Set E) ∈ A
  · have hB : (O : Set E) ∉ B := fun hB => Set.disjoint_left.mp hAB hA hB
    simp [hA, hB]
  · by_cases hB : (O : Set E) ∈ B
    · simp [hA, hB]
    · simp [hA, hB]


-- @@ L431-436 verbatim
/-! ## A transport interface

`CobordFlow` produces two pieces of data on a regular slab: a bijection of orbit
components, and a free homotopy of the corresponding frame loops.  The following
small interface isolates exactly what the finite-sum argument needs from that
geometric construction. -/


-- @@ L438-438 verbatim
variable {Y : FramedLevelSet n}


-- @@ L440-446 verbatim
/-- Component-level data sufficient to transport `framedDelta`. -/
structure DeltaTransport (W : TamedField Y) where
  /-- Bijection of orbit components. -/
  orbitEquiv : V.OrbitIndex ≃ W.OrbitIndex
  /-- The framed-circle contribution is preserved componentwise. -/
  contribution_eq :
    ∀ O, V.orbitContribution O = W.orbitContribution (orbitEquiv O)


-- @@ L448-453 verbatim
/-- A component bijection preserving frame classes preserves the total invariant.
This is the finite-sum final step of regular-interval transport. -/
theorem framedDelta_eq_of_transport {W : TamedField Y}
    (T : V.DeltaTransport W) : V.framedDelta = W.framedDelta := by
  unfold framedDelta
  exact Fintype.sum_equiv T.orbitEquiv _ _ T.contribution_eq


-- @@ L455-471 verbatim
/-- Restricted version of `framedDelta_eq_of_transport`: corresponding unions of
components have the same partial invariant. -/
theorem deltaOn_eq_of_transport {W : TamedField Y} (T : V.DeltaTransport W)
    {A B : Set (Set E)}
    (hAB : ∀ O : V.OrbitIndex, (O : Set E) ∈ A ↔
      ((T.orbitEquiv O : W.OrbitIndex) : Set E) ∈ B) :
    V.deltaOn A = W.deltaOn B := by
  classical
  unfold deltaOn
  apply Fintype.sum_equiv T.orbitEquiv
  intro O
  by_cases hA : (O : Set E) ∈ A
  · have hB : ((T.orbitEquiv O : W.OrbitIndex) : Set E) ∈ B := (hAB O).mp hA
    simp [hA, hB, T.contribution_eq O]
  · have hB : ((T.orbitEquiv O : W.OrbitIndex) : Set E) ∉ B :=
      fun hB => hA ((hAB O).mpr hB)
    simp [hA, hB]


-- @@ L473-488 verbatim
/-- The invariant of an empty level set is zero. -/
theorem framedDelta_eq_zero_of_fiber_eq_empty (hX : X.fiber = ∅) :
    V.framedDelta = 0 := by
  classical
  have hOrbit : V.orbitFinset = ∅ := by
    ext O
    constructor
    · intro hO
      obtain ⟨p, hp, hOp⟩ := V.mem_orbitFinset.mp hO
      rw [hX] at hp
      exact hp.elim
    · simp
  unfold framedDelta
  change (∑ O ∈ V.orbitFinset.attach, V.orbitContribution O) = 0
  rw [show V.orbitFinset.attach = ∅ by simp [hOrbit]]
  simp


-- @@ L490-493 verbatim
/-- Equivalent pointwise form of the empty-fiber theorem. -/
theorem framedDelta_eq_zero_of_fiber_empty (hX : X.fiber = (∅ : Set E)) :
    V.framedDelta = 0 :=
  V.framedDelta_eq_zero_of_fiber_eq_empty hX


-- @@ L495-495 verbatim
/-! ### Continuous maps of fibers send flow-orbits into flow-orbits -/


-- @@ L497-531 verbatim
/-- A continuous map between two compact one-dimensional fibers sends each flow
orbit into the flow orbit of the image base point.  This is the connected-component
argument used by slice transport; no compatibility between the two chosen tamed
fields is required. -/
theorem mapsTo_orbit_of_continuous {Y : FramedLevelSet n} (U : TamedField Y)
    {f : E → E} (hf : Continuous f) (hmap : MapsTo f X.fiber Y.fiber)
    {p : E} (hp : p ∈ X.fiber) :
    MapsTo f (V.orbit p) (U.orbit (f p)) := by
  let γ : ℝ → E := fun t => f (V.flow p t)
  let A : Set ℝ := γ ⁻¹' U.orbit (f p)
  have hq : f p ∈ Y.fiber := hmap hp
  have hAS : A ⊆ (Set.univ : Set ℝ) := fun _ _ => Set.mem_univ _
  have hAclosed : IsClosed A :=
    (U.isCompact_orbit hq).isClosed.preimage (hf.comp (V.continuous_flow p))
  have hAopen : ∀ t ∈ A, ∃ r > 0,
      (Set.univ : Set ℝ) ∩ Metric.ball t r ⊆ A := by
    intro t ht
    obtain ⟨r, hr, hrsub⟩ := U.orbit_isOpen_in_fiber hq ht
    have hopen : IsOpen (γ ⁻¹' Metric.ball (γ t) r) :=
      Metric.isOpen_ball.preimage (hf.comp (V.continuous_flow p))
    have htmem : t ∈ γ ⁻¹' Metric.ball (γ t) r := Metric.mem_ball_self hr
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hopen t htmem
    refine ⟨ε, hε, ?_⟩
    rintro u ⟨hu, hut⟩
    apply hrsub
    exact ⟨hmap (V.flow_mem_fiber hp u), hεsub hut⟩
  have hA0 : A.Nonempty := by
    refine ⟨0, ?_⟩
    change f (V.flow p 0) ∈ U.orbit (f p)
    rw [V.flow_zero]
    exact U.mem_orbit_self (f p)
  have hAll : (Set.univ : Set ℝ) ⊆ A :=
    subset_of_relOpen_closed isPreconnected_univ hAS hAclosed hAopen hA0
  rintro x ⟨t, rfl⟩
  exact hAll (Set.mem_univ t)


-- @@ L533-533 verbatim
/-! ### Independence of the auxiliary tamed field -/


-- @@ L535-547 verbatim
/-- Two tamed fields for the same framed level set have identical flows on the
fiber: both solve the intrinsic unit tangent ODE there. -/
theorem flow_eq_of_tamedField (U : TamedField X) {p : E} (hp : p ∈ X.fiber) :
    V.flow p = U.flow p := by
  apply V.solution_unique (t₀ := 0)
  · exact V.hasDerivAt_flow p
  · intro t
    have h := U.hasDerivAt_flow p t
    have ht : U.flow p t ∈ X.fiber := U.flow_mem_fiber hp t
    have hv : V.v (U.flow p t) = U.v (U.flow p t) := by
      rw [V.v_eq_tau_of_mem_fiber ht, U.v_eq_tau_of_mem_fiber ht]
    rwa [hv]
  · rw [V.flow_zero, U.flow_zero]


-- @@ L549-552 verbatim
theorem orbit_eq_of_tamedField (U : TamedField X) {p : E} (hp : p ∈ X.fiber) :
    V.orbit p = U.orbit p := by
  unfold orbit
  rw [V.flow_eq_of_tamedField U hp]


-- @@ L554-563 verbatim
/-- The intrinsic fundamental period does not depend on the cutoff used to extend
the unit tangent field away from the fiber. -/
theorem fundamentalPeriod_eq_of_tamedField (U : TamedField X) {p : E}
    (hp : p ∈ X.fiber) : V.fundamentalPeriod hp = U.fundamentalPeriod hp := by
  have hflow : V.flow p = U.flow p := V.flow_eq_of_tamedField U hp
  apply le_antisymm
  · apply V.fundamentalPeriod_le_period hp (U.fundamentalPeriod_pos hp)
    simpa [hflow] using U.fundamentalPeriod_periodic hp
  · apply U.fundamentalPeriod_le_period hp (V.fundamentalPeriod_pos hp)
    simpa [← hflow] using V.fundamentalPeriod_periodic hp


-- @@ L565-576 verbatim
/-- The point-based frame class is independent of the auxiliary tamed field. -/
theorem fundamentalFrameClass_eq_of_tamedField (U : TamedField X) {p : E}
    (hp : p ∈ X.fiber) :
    V.fundamentalFrameClass hp = U.fundamentalFrameClass hp := by
  apply loopClassZ2_congr_fun
    (V.fundamentalFrameLoop_closed hp) (U.fundamentalFrameLoop_closed hp)
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  change frameLoop X (V.flow p) ((u : ℝ) * V.fundamentalPeriod hp) =
    frameLoop X (U.flow p) ((u : ℝ) * U.fundamentalPeriod hp)
  rw [V.flow_eq_of_tamedField U hp, V.fundamentalPeriod_eq_of_tamedField U hp]


-- @@ L578-588 verbatim
/-- The canonical finite orbit sets are independent of the auxiliary tamed field. -/
theorem orbitFinset_eq_of_tamedField (U : TamedField X) :
    V.orbitFinset = U.orbitFinset := by
  apply Finset.ext
  intro O
  simp only [V.mem_orbitFinset, U.mem_orbitFinset]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, V.orbit_eq_of_tamedField U hp⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, (V.orbit_eq_of_tamedField U hp).symm⟩


-- @@ L590-600 verbatim
/-- Canonical identification of orbit indices for two tamed extensions. -/
def orbitIndexEquivOfTamedField (U : TamedField X) :
    V.OrbitIndex ≃ U.OrbitIndex where
  toFun O := ⟨O.1, by
    rw [← V.orbitFinset_eq_of_tamedField U]
    exact O.2⟩
  invFun O := ⟨O.1, by
    rw [V.orbitFinset_eq_of_tamedField U]
    exact O.2⟩
  left_inv _ := rfl
  right_inv _ := rfl


-- @@ L602-626 verbatim
/-- The total invariant is genuinely independent of the chosen tamed extension. -/
theorem framedDelta_eq_of_tamedField (U : TamedField X) :
    V.framedDelta = U.framedDelta := by
  let e := V.orbitIndexEquivOfTamedField U
  apply Fintype.sum_equiv e
  intro O
  unfold orbitContribution orbitFrameClass
  have hsets : (O : Set E) = (e O : Set E) := rfl
  let p : E := V.orbitPoint O
  let q : E := U.orbitPoint (e O)
  have hp : p ∈ X.fiber := V.orbitPoint_mem_fiber O
  have hq : q ∈ X.fiber := U.orbitPoint_mem_fiber (e O)
  have hqOrbit : q ∈ V.orbit p := by
    have hOp : (O : Set E) = V.orbit p := V.orbitPoint_orbit O
    have hOq : ((e O : U.OrbitIndex) : Set E) = U.orbit q :=
      U.orbitPoint_orbit (e O)
    have hVU : V.orbit q = U.orbit q := V.orbit_eq_of_tamedField U hq
    rw [← hOp, hsets, hOq, ← hVU]
    exact V.mem_orbit_self q
  have hbase : V.fundamentalFrameClass hq = V.fundamentalFrameClass hp :=
    V.fundamentalFrameClass_eq_of_mem_orbit hp hqOrbit
  have hfield : V.fundamentalFrameClass hq = U.fundamentalFrameClass hq :=
    V.fundamentalFrameClass_eq_of_tamedField U hq
  change V.fundamentalFrameClass hp + 1 = U.fundamentalFrameClass hq + 1
  rw [← hfield, hbase]


-- @@ L628-653 verbatim
/-- The canonical component identification for two tamed extensions preserves each
framed-circle contribution.  This is the componentwise form of
`framedDelta_eq_of_tamedField`, useful for labelled subunions of the fiber. -/
theorem orbitContribution_eq_of_tamedField (U : TamedField X) (O : V.OrbitIndex) :
    V.orbitContribution O =
      U.orbitContribution (V.orbitIndexEquivOfTamedField U O) := by
  unfold orbitContribution orbitFrameClass
  let e := V.orbitIndexEquivOfTamedField U
  let p : E := V.orbitPoint O
  let q : E := U.orbitPoint (e O)
  have hp : p ∈ X.fiber := V.orbitPoint_mem_fiber O
  have hq : q ∈ X.fiber := U.orbitPoint_mem_fiber (e O)
  have hsets : (O : Set E) = (e O : Set E) := rfl
  have hqOrbit : q ∈ V.orbit p := by
    have hOp : (O : Set E) = V.orbit p := V.orbitPoint_orbit O
    have hOq : ((e O : U.OrbitIndex) : Set E) = U.orbit q :=
      U.orbitPoint_orbit (e O)
    have hVU : V.orbit q = U.orbit q := V.orbit_eq_of_tamedField U hq
    rw [← hOp, hsets, hOq, ← hVU]
    exact V.mem_orbit_self q
  have hbase : V.fundamentalFrameClass hq = V.fundamentalFrameClass hp :=
    V.fundamentalFrameClass_eq_of_mem_orbit hp hqOrbit
  have hfield : V.fundamentalFrameClass hq = U.fundamentalFrameClass hq :=
    V.fundamentalFrameClass_eq_of_tamedField U hq
  change V.fundamentalFrameClass hp + 1 = U.fundamentalFrameClass hq + 1
  rw [← hfield, hbase]


-- @@ L655-658 verbatim
/-- The intrinsic component identification packaged as a `DeltaTransport`. -/
def deltaTransportOfTamedField (U : TamedField X) : V.DeltaTransport U where
  orbitEquiv := V.orbitIndexEquivOfTamedField U
  contribution_eq := V.orbitContribution_eq_of_tamedField U


-- @@ L660-660 verbatim
end TamedField


-- @@ L662-662 verbatim
/-! ## Framed and signed cobordisms as slice data -/


-- @@ L664-664 verbatim
namespace FramedLevelCobordism


-- @@ L666-675 verbatim
/-- Forget the end collars of a framed cobordism and retain the data needed by the
regular-slab flow construction. -/
def toLevelCobordismData (C : FramedLevelCobordism n) : LevelCobordismData n where
  G := C.G
  smooth := C.smooth
  spatial_bounded := by
    obtain ⟨R, hR⟩ := C.spatial_bounded
    refine ⟨R, fun v hv => ?_⟩
    simpa [spacePart, initCLM, initLM] using hR v hv
  regular := C.regular


-- @@ L677-677 verbatim
end FramedLevelCobordism


-- @@ L679-679 verbatim
/-! ## Concrete time transport on a regular slab -/


-- @@ L681-681 verbatim
namespace SlabTamedField


-- @@ L683-683 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin (n + 2))


-- @@ L685-685 verbatim
variable {C : LevelCobordismData n} {a b : ℝ} (W : SlabTamedField C a b)


-- @@ L687-755 verbatim
/-- Along a segment whose expected time coordinate stays in the regular slab, the
tamed time flow has unit time speed.  The proof bootstraps the local identity over
the whole interval using a relatively open-and-closed argument. -/
theorem tcoord_flow_Icc {p : E₂} (hp : p ∈ C.fiber) {t₀ l u : ℝ}
    (hpt : tcoord p = t₀) (hlu : l ≤ u) (hl : l ≤ 0) (hu : 0 ≤ u)
    (ha : a ≤ t₀ + l) (hb : t₀ + u ≤ b) :
    ∀ s ∈ Icc l u, tcoord (W.flow p s) = t₀ + s := by
  let f : ℝ → ℝ := fun s => tcoord (W.flow p s)
  let g : ℝ → ℝ := fun s => t₀ + s
  let S : Set ℝ := Icc l u
  let A : Set ℝ := {s | s ∈ S ∧ f s = g s}
  have hSpre : IsPreconnected S := convex_Icc l u |>.isPreconnected
  have hAS : A ⊆ S := fun _ hs => hs.1
  have hfcont : Continuous f := continuous_tcoord.comp (W.continuous_flow p)
  have hgcont : Continuous g := continuous_const.add continuous_id
  have hAclosed : IsClosed A := by
    exact isClosed_Icc.inter (isClosed_eq hfcont hgcont)
  have hAopen : ∀ s ∈ A, ∃ r > 0, S ∩ Metric.ball s r ⊆ A := by
    intro s hsA
    have hsS : s ∈ Icc l u := hsA.1
    have hqFiber : W.flow p s ∈ C.fiber := W.flow_mem_fiber hp s
    have hqTime : tcoord (W.flow p s) = t₀ + s := hsA.2
    have hqSlab : W.flow p s ∈ slabFiber C a b := by
      refine ⟨hqFiber, ?_⟩
      change tcoord (W.flow p s) ∈ Icc a b
      rw [hqTime]
      constructor <;> linarith [hsS.1, hsS.2]
    have hopen : IsOpen ((W.flow p) ⁻¹' Metric.ball (W.flow p s) W.delta) :=
      Metric.isOpen_ball.preimage (W.continuous_flow p)
    have hmem : s ∈ (W.flow p) ⁻¹' Metric.ball (W.flow p s) W.delta := by
      exact Metric.mem_ball_self W.delta_pos
    obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp hopen s hmem
    refine ⟨r, hr, ?_⟩
    have hcollar : ∀ u ∈ Metric.ball s r,
        W.flow p u ∈ Metric.cthickening W.delta (slabFiber C a b) := by
      intro u hu
      have huBall : W.flow p u ∈ Metric.ball (W.flow p s) W.delta := hrsub hu
      apply Metric.thickening_subset_cthickening
      exact Metric.mem_thickening_iff.mpr ⟨W.flow p s, hqSlab, huBall⟩
    have hfderiv : ∀ u ∈ Metric.ball s r, HasDerivAt f 1 u := by
      intro u hu
      have hflow := W.hasDerivAt_flow p u
      have hproj := (EuclideanSpace.proj (Fin.last (n + 1)) (𝕜 := ℝ)).hasFDerivAt.comp
        u hflow.hasFDerivAt
      have ht : HasDerivAt f (tcoord (W.w (W.flow p u))) u := by
        simpa [f, tcoord, Function.comp_def] using hproj.hasDerivAt
      have hcu := hcollar u hu
      have hspeed : tcoord (W.w (W.flow p u)) = 1 := by
        rw [W.eq_time _ hcu]
        exact tcoord_timeField (W.subset_slabRegular hcu)
      rwa [hspeed] at ht
    have hfg : Set.EqOn f g (Metric.ball s r) := by
      apply Metric.isOpen_ball.eqOn_of_deriv_eq (convex_ball _ _).isPreconnected
      · intro u hu
        exact (hfderiv u hu).differentiableAt.differentiableWithinAt
      · exact (differentiable_const t₀).add differentiable_id |>.differentiableOn
      · intro u hu
        rw [(hfderiv u hu).deriv]
        simpa [g] using ((hasDerivAt_id u).const_add t₀).deriv
      · exact Metric.mem_ball_self hr
      · exact hsA.2
    rintro u ⟨huS, huBall⟩
    exact ⟨huS, hfg huBall⟩
  have hA0 : A.Nonempty := by
    refine ⟨0, ⟨⟨hl, hu⟩, ?_⟩⟩
    simp [f, g, W.flow_zero, hpt]
  have hSA : S ⊆ A := subset_of_relOpen_closed hSpre hAS hAclosed hAopen hA0
  intro s hs
  exact (hSA hs).2


-- @@ L757-761 verbatim
/-- Forward-time specialization of `tcoord_flow_Icc`. -/
theorem tcoord_flow_segment {p : E₂} (hp : p ∈ C.fiber) {t₀ d : ℝ}
    (hpt : tcoord p = t₀) (hd : 0 ≤ d) (ha : a ≤ t₀) (hb : t₀ + d ≤ b) :
    ∀ s ∈ Icc (0 : ℝ) d, tcoord (W.flow p s) = t₀ + s := by
  exact W.tcoord_flow_Icc hp hpt (by linarith) le_rfl hd (by simpa) hb


-- @@ L763-763 verbatim
/-! ### Transport between two slices -/


-- @@ L765-765 verbatim
local notation "E₁" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L767-770 verbatim
/-- The zero fiber of the time-`t` slice, without choosing a proof that `t` is a
regular value. -/
def sliceFiber (C : LevelCobordismData n) (t : ℝ) : Set E₁ :=
  {x | C.G (cobSpaceTime x t) = 0}


-- @@ L772-775 verbatim
/-- The framed regular level set at a regular slice time. -/
def sliceFLSAt (C : LevelCobordismData n) (t : ℝ) (ht : sliceRegular C.G t) :
    FramedLevelSet n :=
  sliceFLS C.G C.smooth C.spatial_bounded t ht


-- @@ L777-782 verbatim
@[simp]
theorem sliceFLSAt_fiber (C : LevelCobordismData n) (t : ℝ)
    (ht : sliceRegular C.G t) :
    (sliceFLSAt C t ht).fiber = sliceFiber C t := by
  ext x
  rfl


-- @@ L784-786 verbatim
/-- Flow a point from time `t₁` to time `t₂` and retain its spatial coordinate. -/
def sliceTransport (t₁ t₂ : ℝ) (x : E₁) : E₁ :=
  spacePart (W.flow (cobSpaceTime x t₁) (t₂ - t₁))


-- @@ L788-801 verbatim
theorem continuous_sliceTransport (t₁ t₂ : ℝ) :
    Continuous (W.sliceTransport t₁ t₂) := by
  have hst : Continuous fun x : E₁ => cobSpaceTime x t₁ :=
    continuous_iff_continuousAt.mpr fun x =>
      (hasFDerivAt_cobSpaceTime t₁ x).continuousAt
  have hflow : Continuous fun x : E₁ => W.flow (cobSpaceTime x t₁) (t₂ - t₁) :=
    (W.continuous_flow_apply (t₂ - t₁)).comp hst
  have hsp : LipschitzWith 1 (spacePart (n := n)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    change ‖spacePart (x - y)‖ ≤ ‖x - y‖
    exact norm_spacePart_le (x - y)
  exact hsp.continuous.comp hflow


-- @@ L803-831 verbatim
/-- Unit-speed time flow carries a slice fiber into every other slice of a regular
slab. -/
theorem sliceTransport_mapsTo (hreg : regularSlab C.G a b)
    {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b) :
    MapsTo (W.sliceTransport t₁ t₂) (sliceFiber C t₁) (sliceFiber C t₂) := by
  intro x hx
  let p : E₂ := cobSpaceTime x t₁
  let d : ℝ := t₂ - t₁
  have hp : p ∈ C.fiber := hx
  have hpt : tcoord p = t₁ := tcoord_spaceTime x t₁
  have htflow : tcoord (W.flow p d) = t₂ := by
    rcases le_total t₁ t₂ with hle | hle
    · have hd : 0 ≤ d := by dsimp [d]; linarith
      have hb' : t₁ + d ≤ b := by dsimp [d]; linarith [ht₂.2]
      have h := W.tcoord_flow_segment hp hpt hd ht₁.1 hb'
        d ⟨hd, le_rfl⟩
      dsimp [d] at h ⊢
      linarith
    · have hd : d ≤ 0 := by dsimp [d]; linarith
      have ha' : a ≤ t₁ + d := by dsimp [d]; linarith [ht₂.1]
      have hb' : t₁ + 0 ≤ b := by linarith [ht₁.2]
      have h := W.tcoord_flow_Icc hp hpt hd hd le_rfl
        ha' hb' d ⟨le_rfl, hd⟩
      dsimp [d] at h ⊢
      linarith
  have hq : W.flow p d ∈ C.fiber := W.flow_mem_fiber hp d
  change C.G (cobSpaceTime (spacePart (W.flow p d)) t₂) = 0
  rw [← htflow, spaceTime_spacePart]
  exact hq


-- @@ L833-859 verbatim
/-- Reattaching the target time coordinate to a transported spatial point recovers
the actual time-flow point. -/
theorem cobSpaceTime_sliceTransport (hreg : regularSlab C.G a b)
    {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b)
    {x : E₁} (hx : x ∈ sliceFiber C t₁) :
    cobSpaceTime (W.sliceTransport t₁ t₂ x) t₂ =
      W.flow (cobSpaceTime x t₁) (t₂ - t₁) := by
  let p : E₂ := cobSpaceTime x t₁
  let d : ℝ := t₂ - t₁
  have hp : p ∈ C.fiber := hx
  have hpt : tcoord p = t₁ := tcoord_spaceTime x t₁
  have htflow : tcoord (W.flow p d) = t₂ := by
    rcases le_total t₁ t₂ with hle | hle
    · have hd : 0 ≤ d := by dsimp [d]; linarith
      have hb' : t₁ + d ≤ b := by dsimp [d]; linarith [ht₂.2]
      have h := W.tcoord_flow_segment hp hpt hd ht₁.1 hb' d ⟨hd, le_rfl⟩
      dsimp [d] at h ⊢
      linarith
    · have hd : d ≤ 0 := by dsimp [d]; linarith
      have ha' : a ≤ t₁ + d := by dsimp [d]; linarith [ht₂.1]
      have hb' : t₁ + 0 ≤ b := by linarith [ht₁.2]
      have h := W.tcoord_flow_Icc hp hpt hd hd le_rfl ha' hb' d ⟨le_rfl, hd⟩
      dsimp [d] at h ⊢
      linarith
  unfold sliceTransport
  change cobSpaceTime (spacePart (W.flow p d)) t₂ = W.flow p d
  rw [← htflow, spaceTime_spacePart]


-- @@ L861-896 verbatim
/-- Forward transport followed by reverse transport is the identity on the source
slice fiber. -/
theorem sliceTransport_leftInverse (hreg : regularSlab C.G a b)
    {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b)
    {x : E₁} (hx : x ∈ sliceFiber C t₁) :
    W.sliceTransport t₂ t₁ (W.sliceTransport t₁ t₂ x) = x := by
  let p : E₂ := cobSpaceTime x t₁
  let d : ℝ := t₂ - t₁
  have hp : p ∈ C.fiber := hx
  have hpt : tcoord p = t₁ := tcoord_spaceTime x t₁
  have htflow : tcoord (W.flow p d) = t₂ := by
    rcases le_total t₁ t₂ with hle | hle
    · have hd : 0 ≤ d := by dsimp [d]; linarith
      have hb' : t₁ + d ≤ b := by dsimp [d]; linarith [ht₂.2]
      have h := W.tcoord_flow_segment hp hpt hd ht₁.1 hb'
        d ⟨hd, le_rfl⟩
      dsimp [d] at h ⊢
      linarith
    · have hd : d ≤ 0 := by dsimp [d]; linarith
      have ha' : a ≤ t₁ + d := by dsimp [d]; linarith [ht₂.1]
      have hb' : t₁ + 0 ≤ b := by linarith [ht₁.2]
      have h := W.tcoord_flow_Icc hp hpt hd hd le_rfl
        ha' hb' d ⟨le_rfl, hd⟩
      dsimp [d] at h ⊢
      linarith
  have hspace : cobSpaceTime (spacePart (W.flow p d)) t₂ = W.flow p d := by
    rw [← htflow, spaceTime_spacePart]
  unfold sliceTransport
  change spacePart
    (W.flow (cobSpaceTime (spacePart (W.flow p d)) t₂) (t₁ - t₂)) = x
  rw [hspace]
  have hshift := congrFun (W.flow_shift p d) (t₁ - t₂)
  rw [hshift]
  have htime : d + (t₁ - t₂) = 0 := by dsimp [d]; ring
  rw [htime, W.flow_zero]
  exact spacePart_spaceTime x t₁


-- @@ L898-911 verbatim
/-- Slice transport is a bijection between the two slice fibers, with inverse given
by reverse time flow. -/
theorem sliceTransport_bijOn (hreg : regularSlab C.G a b)
    {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b) :
    Set.BijOn (W.sliceTransport t₁ t₂) (sliceFiber C t₁) (sliceFiber C t₂) := by
  refine ⟨W.sliceTransport_mapsTo hreg ht₁ ht₂, ?_, ?_⟩
  · intro x hx y hy hxy
    have h := congrArg (W.sliceTransport t₂ t₁) hxy
    simpa [W.sliceTransport_leftInverse hreg ht₁ ht₂ hx,
      W.sliceTransport_leftInverse hreg ht₁ ht₂ hy] using h
  · intro y hy
    refine ⟨W.sliceTransport t₂ t₁ y,
      W.sliceTransport_mapsTo hreg ht₂ ht₁ hy, ?_⟩
    exact W.sliceTransport_leftInverse hreg ht₂ ht₁ hy


-- @@ L913-913 verbatim
/-! ### The induced map of orbit components -/


-- @@ L915-930 verbatim
/-- The orbit component containing the transported chosen point of a source orbit. -/
def sliceOrbitMap (hreg : regularSlab C.G a b)
    {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b)
    (V₁ : TamedField (sliceFLSAt C t₁ (hreg.sliceRegular ht₁)))
    (V₂ : TamedField (sliceFLSAt C t₂ (hreg.sliceRegular ht₂)))
    (O : V₁.OrbitIndex) : V₂.OrbitIndex := by
  let x : E₁ := V₁.orbitPoint O
  let y : E₁ := W.sliceTransport t₁ t₂ x
  have hx : x ∈ sliceFiber C t₁ := by
    rw [← sliceFLSAt_fiber C t₁ (hreg.sliceRegular ht₁)]
    exact V₁.orbitPoint_mem_fiber O
  have hy : y ∈ sliceFiber C t₂ :=
    W.sliceTransport_mapsTo hreg ht₁ ht₂ hx
  have hy' : y ∈ (sliceFLSAt C t₂ (hreg.sliceRegular ht₂)).fiber := by
    rwa [sliceFLSAt_fiber]
  exact ⟨V₂.orbit y, V₂.mem_orbitFinset.mpr ⟨y, hy', rfl⟩⟩


-- @@ L932-939 verbatim
@[simp]
theorem sliceOrbitMap_val (hreg : regularSlab C.G a b)
    {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b)
    (V₁ : TamedField (sliceFLSAt C t₁ (hreg.sliceRegular ht₁)))
    (V₂ : TamedField (sliceFLSAt C t₂ (hreg.sliceRegular ht₂)))
    (O : V₁.OrbitIndex) :
    ((W.sliceOrbitMap hreg ht₁ ht₂ V₁ V₂ O : V₂.OrbitIndex) : Set E₁) =
      V₂.orbit (W.sliceTransport t₁ t₂ (V₁.orbitPoint O)) := rfl


-- @@ L941-954 verbatim
/-- Slice transport sends every source flow-orbit into the target flow-orbit of its
transported base point. -/
theorem sliceTransport_mapsTo_orbit (hreg : regularSlab C.G a b)
    {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b)
    (V₁ : TamedField (sliceFLSAt C t₁ (hreg.sliceRegular ht₁)))
    (V₂ : TamedField (sliceFLSAt C t₂ (hreg.sliceRegular ht₂)))
    {p : E₁} (hp : p ∈ (sliceFLSAt C t₁ (hreg.sliceRegular ht₁)).fiber) :
    MapsTo (W.sliceTransport t₁ t₂) (V₁.orbit p)
      (V₂.orbit (W.sliceTransport t₁ t₂ p)) := by
  apply V₁.mapsTo_orbit_of_continuous V₂ (W.continuous_sliceTransport t₁ t₂)
  · intro x hx
    rw [sliceFLSAt_fiber] at hx ⊢
    exact W.sliceTransport_mapsTo hreg ht₁ ht₂ hx
  · exact hp


-- @@ L956-988 verbatim
/-- The component maps induced by forward and reverse slice transport are inverse. -/
theorem sliceOrbitMap_leftInverse (hreg : regularSlab C.G a b)
    {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b)
    (V₁ : TamedField (sliceFLSAt C t₁ (hreg.sliceRegular ht₁)))
    (V₂ : TamedField (sliceFLSAt C t₂ (hreg.sliceRegular ht₂)))
    (O : V₁.OrbitIndex) :
    W.sliceOrbitMap hreg ht₂ ht₁ V₂ V₁
        (W.sliceOrbitMap hreg ht₁ ht₂ V₁ V₂ O) = O := by
  apply Subtype.ext
  let p : E₁ := V₁.orbitPoint O
  let q : E₁ := W.sliceTransport t₁ t₂ p
  let O₂ : V₂.OrbitIndex := W.sliceOrbitMap hreg ht₁ ht₂ V₁ V₂ O
  let r : E₁ := V₂.orbitPoint O₂
  have hp : p ∈ (sliceFLSAt C t₁ (hreg.sliceRegular ht₁)).fiber :=
    V₁.orbitPoint_mem_fiber O
  have hq : q ∈ (sliceFLSAt C t₂ (hreg.sliceRegular ht₂)).fiber := by
    rw [sliceFLSAt_fiber] at hp ⊢
    exact W.sliceTransport_mapsTo hreg ht₁ ht₂ hp
  have hrOrbit : r ∈ V₂.orbit q := by
    have hr : r ∈ V₂.orbit r := V₂.mem_orbit_self r
    have hOr : (O₂ : Set E₁) = V₂.orbit r := V₂.orbitPoint_orbit O₂
    have hOq : (O₂ : Set E₁) = V₂.orbit q := by
      rfl
    rw [← hOq, hOr]
    exact hr
  have hback := W.sliceTransport_mapsTo_orbit hreg ht₂ ht₁ V₂ V₁ hq hrOrbit
  have hqp : W.sliceTransport t₂ t₁ q = p := by
    dsimp [q, p]
    exact W.sliceTransport_leftInverse hreg ht₁ ht₂ hp
  have hrSource : W.sliceTransport t₂ t₁ r ∈ V₁.orbit p := by
    rwa [hqp] at hback
  change V₁.orbit (W.sliceTransport t₂ t₁ r) = (O : Set E₁)
  exact (V₁.orbit_eq_of_mem hrSource).trans (V₁.orbitPoint_orbit O).symm


-- @@ L990-999 verbatim
/-- Bijection of the finite orbit-component sets at two regular times. -/
def sliceOrbitEquiv (hreg : regularSlab C.G a b)
    {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b)
    (V₁ : TamedField (sliceFLSAt C t₁ (hreg.sliceRegular ht₁)))
    (V₂ : TamedField (sliceFLSAt C t₂ (hreg.sliceRegular ht₂))) :
    V₁.OrbitIndex ≃ V₂.OrbitIndex where
  toFun := W.sliceOrbitMap hreg ht₁ ht₂ V₁ V₂
  invFun := W.sliceOrbitMap hreg ht₂ ht₁ V₂ V₁
  left_inv := W.sliceOrbitMap_leftInverse hreg ht₁ ht₂ V₁ V₂
  right_inv := W.sliceOrbitMap_leftInverse hreg ht₂ ht₁ V₂ V₁


-- @@ L1001-1001 verbatim
end SlabTamedField


-- @@ L1003-1003 verbatim
namespace SignedFramedLevelCobordism


-- @@ L1005-1006 verbatim
variable {X₀ X₁ : FramedLevelSet n} {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}
  (C : SignedFramedLevelCobordism S₀ S₁)


-- @@ L1008-1019 verbatim
/-- The nonvanishing cobordism label restricted to a regular time slice. -/
def sliceSign (t : ℝ) (ht : sliceRegular C.cobordism.G t) :
    FiberSign (SlabTamedField.sliceFLSAt C.cobordism.toLevelCobordismData t ht) where
  toFun x := C (cobSpaceTime x t)
  continuous := by
    apply C.continuous.comp
    rw [continuous_iff_continuousAt]
    intro x
    exact (hasFDerivAt_cobSpaceTime t x).continuousAt
  nonzero := by
    intro x hx
    exact C.nonzero (cobSpaceTime x t) hx


-- @@ L1021-1045 verbatim
/-- The sign of the cobordism label is constant along a path in its zero fiber. -/
theorem pos_iff_of_zeroFiber_path
    (γ : C(I, EuclideanSpace ℝ (Fin (n + 2))))
    (hγ : ∀ u, C.cobordism.G (γ u) = 0) :
    0 < C (γ 0) ↔ 0 < C (γ 1) := by
  have hcont : Continuous fun u : I => C (γ u) := C.continuous.comp γ.continuous
  constructor
  · intro h₀
    by_contra h₁
    have h₁neg : C (γ 1) < 0 := by
      have hle : C (γ 1) ≤ 0 := le_of_not_gt h₁
      exact lt_of_le_of_ne hle (C.nonzero (γ 1) (hγ 1))
    have hz : (0 : ℝ) ∈ Icc (C (γ 1)) (C (γ 0)) := ⟨h₁neg.le, h₀.le⟩
    obtain ⟨u, -, hu⟩ :=
      intermediate_value_Icc' (show (0 : I) ≤ 1 by simp) hcont.continuousOn hz
    exact C.nonzero (γ u) (hγ u) hu
  · intro h₁
    by_contra h₀
    have h₀neg : C (γ 0) < 0 := by
      have hle : C (γ 0) ≤ 0 := le_of_not_gt h₀
      exact lt_of_le_of_ne hle (C.nonzero (γ 0) (hγ 0))
    have hz : (0 : ℝ) ∈ Icc (C (γ 0)) (C (γ 1)) := ⟨h₀neg.le, h₁.le⟩
    obtain ⟨u, -, hu⟩ :=
      intermediate_value_Icc (show (0 : I) ≤ 1 by simp) hcont.continuousOn hz
    exact C.nonzero (γ u) (hγ u) hu


-- @@ L1047-1074 verbatim
/-- Regular-slab time transport preserves the positive/negative sheet selected by
the nonvanishing cobordism label. -/
theorem sliceSign_transport_pos_iff {a b : ℝ}
    (W : SlabTamedField C.cobordism.toLevelCobordismData a b)
    (hreg : regularSlab C.cobordism.G a b)
    {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b)
    {x : EuclideanSpace ℝ (Fin (n + 1))}
    (hx : x ∈ (SlabTamedField.sliceFLSAt C.cobordism.toLevelCobordismData
      t₁ (hreg.sliceRegular ht₁)).fiber) :
    0 < C.sliceSign t₁ (hreg.sliceRegular ht₁) x ↔
      0 < C.sliceSign t₂ (hreg.sliceRegular ht₂)
        (W.sliceTransport t₁ t₂ x) := by
  let p : EuclideanSpace ℝ (Fin (n + 2)) := cobSpaceTime x t₁
  let d : ℝ := t₂ - t₁
  let γ : C(I, EuclideanSpace ℝ (Fin (n + 2))) :=
    ⟨fun u => W.flow p ((u : ℝ) * d),
      (W.continuous_flow p).comp (continuous_subtype_val.mul continuous_const)⟩
  have hp : p ∈ C.cobordism.toLevelCobordismData.fiber := by
    exact hx
  have hγ : ∀ u, C.cobordism.G (γ u) = 0 := by
    intro u
    exact W.flow_mem_fiber hp ((u : ℝ) * d)
  have hsign := C.pos_iff_of_zeroFiber_path γ hγ
  have htarget := W.cobSpaceTime_sliceTransport hreg ht₁ ht₂ hx
  change 0 < C (cobSpaceTime x t₁) ↔
    0 < C (cobSpaceTime (W.sliceTransport t₁ t₂ x) t₂)
  rw [htarget]
  simpa [γ, p, d] using hsign


-- @@ L1076-1076 verbatim
end SignedFramedLevelCobordism


-- @@ L1078-1078 verbatim
/-! ## Invariants of a labelled union of components -/


-- @@ L1080-1080 verbatim
namespace FiberSign


-- @@ L1082-1082 verbatim
variable {X : FramedLevelSet n} (S : FiberSign X)


-- @@ L1084-1084 verbatim
local notation "Eₛ" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L1086-1088 verbatim
/-- Orbit components contained in the positive part of a fiber label. -/
def positiveOrbitCollection (V : TamedField X) : Set (Set Eₛ) :=
  {O | O ⊆ S.positivePart}


-- @@ L1090-1092 verbatim
/-- The framed invariant restricted to the positively labelled components. -/
def positiveFramedDelta (V : TamedField X) : ZMod 2 :=
  V.deltaOn (S.positiveOrbitCollection V)


-- @@ L1094-1107 verbatim
/-- The label sign is constant on a flow orbit. -/
theorem pos_iff_of_mem_orbit (V : TamedField X) {p q : Eₛ}
    (hp : p ∈ X.fiber) (hq : q ∈ V.orbit p) :
    0 < S p ↔ 0 < S q := by
  obtain ⟨a, rfl⟩ := hq
  let hpath : C(I, Eₛ) :=
    ⟨fun u => V.flow p ((u : ℝ) * a),
      (V.continuous_flow p).comp
        (continuous_subtype_val.mul continuous_const)⟩
  have hpathFiber : ∀ u, hpath u ∈ X.fiber := by
    intro u
    exact V.flow_mem_fiber hp _
  have hsign := S.pos_iff_of_path hpath hpathFiber
  simpa [hpath] using hsign


-- @@ L1109-1134 verbatim
/-- A whole orbit has one sign; hence membership in the positive collection can be
tested at the canonical representative. -/
theorem mem_positiveOrbitCollection_iff (V : TamedField X) (O : V.OrbitIndex) :
    (O : Set Eₛ) ∈ S.positiveOrbitCollection V ↔ 0 < S (V.orbitPoint O) := by
  constructor
  · intro hO
    have hpO : V.orbitPoint O ∈ (O : Set Eₛ) := by
      rw [V.orbitPoint_orbit O]
      exact V.mem_orbit_self (V.orbitPoint O)
    exact (hO hpO).2
  · intro hp x hx
    rw [V.orbitPoint_orbit O] at hx
    obtain ⟨a, rfl⟩ := hx
    let hpath : C(I, Eₛ) :=
      ⟨fun u => V.flow (V.orbitPoint O) ((u : ℝ) * a),
        (V.continuous_flow (V.orbitPoint O)).comp
          (continuous_subtype_val.mul continuous_const)⟩
    have hpathFiber : ∀ u, hpath u ∈ X.fiber := by
      intro u
      change V.flow (V.orbitPoint O) ((u : ℝ) * a) ∈ X.fiber
      exact V.flow_mem_fiber (V.orbitPoint_mem_fiber O) _
    have hp0 : 0 < S (hpath 0) := by
      simpa [hpath] using hp
    have hpos := (S.pos_iff_of_path hpath hpathFiber).mp hp0
    refine ⟨V.flow_mem_fiber (V.orbitPoint_mem_fiber O) _, ?_⟩
    simpa [hpath] using hpos


-- @@ L1136-1145 verbatim
/-- The positive-sheet invariant is independent of the auxiliary cutoff used to
extend the intrinsic tangent field away from the fiber. -/
theorem positiveFramedDelta_eq_of_tamedField (V U : TamedField X) :
    S.positiveFramedDelta V = S.positiveFramedDelta U := by
  let T := V.deltaTransportOfTamedField U
  apply V.deltaOn_eq_of_transport T
  intro O
  change (O : Set Eₛ) ⊆ S.positivePart ↔
    ((T.orbitEquiv O : U.OrbitIndex) : Set Eₛ) ⊆ S.positivePart
  rfl


-- @@ L1147-1147 verbatim
end FiberSign


-- @@ L1149-1149 verbatim
namespace SignedFramedLevelCobordism


-- @@ L1151-1152 verbatim
variable {X₀ X₁ : FramedLevelSet n} {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}
  (C : SignedFramedLevelCobordism S₀ S₁)


-- @@ L1154-1192 verbatim
/-- The concrete orbit bijection induced by regular-slab time flow preserves the
positive component collection of the signed slices. -/
theorem sliceOrbitEquiv_mem_positive_iff {a b : ℝ}
    (W : SlabTamedField C.cobordism.toLevelCobordismData a b)
    (hreg : regularSlab C.cobordism.G a b)
    {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b)
    (V₁ : TamedField (SlabTamedField.sliceFLSAt C.cobordism.toLevelCobordismData
      t₁ (hreg.sliceRegular ht₁)))
    (V₂ : TamedField (SlabTamedField.sliceFLSAt C.cobordism.toLevelCobordismData
      t₂ (hreg.sliceRegular ht₂)))
    (O : V₁.OrbitIndex) :
    (O : Set (EuclideanSpace ℝ (Fin (n + 1)))) ∈
        (C.sliceSign t₁ (hreg.sliceRegular ht₁)).positiveOrbitCollection V₁ ↔
      ((W.sliceOrbitEquiv hreg ht₁ ht₂ V₁ V₂ O : V₂.OrbitIndex) :
          Set (EuclideanSpace ℝ (Fin (n + 1)))) ∈
        (C.sliceSign t₂ (hreg.sliceRegular ht₂)).positiveOrbitCollection V₂ := by
  let e := W.sliceOrbitEquiv hreg ht₁ ht₂ V₁ V₂
  let p := V₁.orbitPoint O
  let y := W.sliceTransport t₁ t₂ p
  let q := V₂.orbitPoint (e O)
  have hp : p ∈ (SlabTamedField.sliceFLSAt C.cobordism.toLevelCobordismData
      t₁ (hreg.sliceRegular ht₁)).fiber := V₁.orbitPoint_mem_fiber O
  have hy : y ∈ (SlabTamedField.sliceFLSAt C.cobordism.toLevelCobordismData
      t₂ (hreg.sliceRegular ht₂)).fiber := by
    rw [SlabTamedField.sliceFLSAt_fiber] at hp ⊢
    exact W.sliceTransport_mapsTo hreg ht₁ ht₂ hp
  have hqOrbit : q ∈ V₂.orbit y := by
    have hqmem : q ∈ ((e O : V₂.OrbitIndex) :
        Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
      rw [V₂.orbitPoint_orbit (e O)]
      exact V₂.mem_orbit_self q
    exact hqmem
  rw [(C.sliceSign t₁ (hreg.sliceRegular ht₁)).mem_positiveOrbitCollection_iff,
    (C.sliceSign t₂ (hreg.sliceRegular ht₂)).mem_positiveOrbitCollection_iff]
  change 0 < C.sliceSign t₁ (hreg.sliceRegular ht₁) p ↔
    0 < C.sliceSign t₂ (hreg.sliceRegular ht₂) q
  exact (C.sliceSign_transport_pos_iff W hreg ht₁ ht₂ hp).trans
    ((C.sliceSign t₂ (hreg.sliceRegular ht₂)).pos_iff_of_mem_orbit
      V₂ hy hqOrbit)


-- @@ L1194-1207 verbatim
/-- The one remaining framed input on a regular slab: the frame class of each
transported component agrees with that of its source.  Orbit bijectivity and signed
sheet preservation are already consequences of the time flow above. -/
structure RegularSlabFrameTransport {a b : ℝ}
    (W : SlabTamedField C.cobordism.toLevelCobordismData a b)
    (hreg : regularSlab C.cobordism.G a b)
    {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b)
    (V₁ : TamedField (SlabTamedField.sliceFLSAt C.cobordism.toLevelCobordismData
      t₁ (hreg.sliceRegular ht₁)))
    (V₂ : TamedField (SlabTamedField.sliceFLSAt C.cobordism.toLevelCobordismData
      t₂ (hreg.sliceRegular ht₂))) : Prop where
  frameClass_eq : ∀ O : V₁.OrbitIndex,
    V₁.orbitFrameClass O =
      V₂.orbitFrameClass (W.sliceOrbitEquiv hreg ht₁ ht₂ V₁ V₂ O)


-- @@ L1209-1223 verbatim
/-- A geometric version of `RegularSlabFrameTransport`: corresponding canonical
frame loops are joined by a homotopy through closed loops. -/
structure RegularSlabFrameHomotopy {a b : ℝ}
    (W : SlabTamedField C.cobordism.toLevelCobordismData a b)
    (hreg : regularSlab C.cobordism.G a b)
    {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b)
    (V₁ : TamedField (SlabTamedField.sliceFLSAt C.cobordism.toLevelCobordismData
      t₁ (hreg.sliceRegular ht₁)))
    (V₂ : TamedField (SlabTamedField.sliceFLSAt C.cobordism.toLevelCobordismData
      t₂ (hreg.sliceRegular ht₂))) where
  homotopy : ∀ O : V₁.OrbitIndex, ContinuousMap.Homotopy
    (V₁.orbitFrameLoop O)
    (V₂.orbitFrameLoop (W.sliceOrbitEquiv hreg ht₁ ht₂ V₁ V₂ O))
  closed : ∀ (O : V₁.OrbitIndex) (s : I),
    homotopy O (s, 0) = homotopy O (s, 1)


-- @@ L1225-1225 verbatim
namespace RegularSlabFrameHomotopy


-- @@ L1227-1234 verbatim
variable {a b t₁ t₂ : ℝ}
  {W : SlabTamedField C.cobordism.toLevelCobordismData a b}
  {hreg : regularSlab C.cobordism.G a b}
  {ht₁ : t₁ ∈ Icc a b} {ht₂ : t₂ ∈ Icc a b}
  {V₁ : TamedField (SlabTamedField.sliceFLSAt C.cobordism.toLevelCobordismData
    t₁ (hreg.sliceRegular ht₁))}
  {V₂ : TamedField (SlabTamedField.sliceFLSAt C.cobordism.toLevelCobordismData
    t₂ (hreg.sliceRegular ht₂))}


-- @@ L1236-1246 verbatim
/-- Free-homotopy invariance turns the geometric witness into componentwise frame
class transport. -/
theorem toFrameTransport
    (H : C.RegularSlabFrameHomotopy W hreg ht₁ ht₂ V₁ V₂) :
    C.RegularSlabFrameTransport W hreg ht₁ ht₂ V₁ V₂ where
  frameClass_eq := by
    intro O
    exact loopClassZ2_congr (V₁.orbitFrameLoop_closed O)
      (V₂.orbitFrameLoop_closed
        (W.sliceOrbitEquiv hreg ht₁ ht₂ V₁ V₂ O))
      (H.homotopy O) (H.closed O)


-- @@ L1248-1248 verbatim
end RegularSlabFrameHomotopy


-- @@ L1250-1250 verbatim
namespace RegularSlabFrameTransport


-- @@ L1252-1259 verbatim
variable {a b t₁ t₂ : ℝ}
  {W : SlabTamedField C.cobordism.toLevelCobordismData a b}
  {hreg : regularSlab C.cobordism.G a b}
  {ht₁ : t₁ ∈ Icc a b} {ht₂ : t₂ ∈ Icc a b}
  {V₁ : TamedField (SlabTamedField.sliceFLSAt C.cobordism.toLevelCobordismData
    t₁ (hreg.sliceRegular ht₁))}
  {V₂ : TamedField (SlabTamedField.sliceFLSAt C.cobordism.toLevelCobordismData
    t₂ (hreg.sliceRegular ht₂))}


-- @@ L1261-1269 verbatim
/-- Package regular-slab orbit and frame transport as the finite-sum interface. -/
def toDeltaTransport
    (H : C.RegularSlabFrameTransport W hreg ht₁ ht₂ V₁ V₂) :
    V₁.DeltaTransport V₂ where
  orbitEquiv := W.sliceOrbitEquiv hreg ht₁ ht₂ V₁ V₂
  contribution_eq := by
    intro O
    unfold TamedField.orbitContribution
    rw [H.frameClass_eq O]


-- @@ L1271-1275 verbatim
/-- The total framed invariant is constant across a regular slab. -/
theorem framedDelta_eq
    (H : C.RegularSlabFrameTransport W hreg ht₁ ht₂ V₁ V₂) :
    V₁.framedDelta = V₂.framedDelta :=
  V₁.framedDelta_eq_of_transport (toDeltaTransport C H)


-- @@ L1277-1284 verbatim
/-- The signed positive-sheet invariant is constant across a regular slab. -/
theorem positiveFramedDelta_eq :
    C.RegularSlabFrameTransport W hreg ht₁ ht₂ V₁ V₂ →
    (C.sliceSign t₁ (hreg.sliceRegular ht₁)).positiveFramedDelta V₁ =
      (C.sliceSign t₂ (hreg.sliceRegular ht₂)).positiveFramedDelta V₂ := by
  intro H
  apply V₁.deltaOn_eq_of_transport (toDeltaTransport C H)
  exact C.sliceOrbitEquiv_mem_positive_iff W hreg ht₁ ht₂ V₁ V₂


-- @@ L1286-1286 verbatim
end RegularSlabFrameTransport


-- @@ L1288-1288 verbatim
end SignedFramedLevelCobordism


-- @@ L1290-1294 verbatim
/-! ## The northern invariant of bridge level sets

The horizontal-coordinate bridge has two kinds of fiber components, lying over the
northern and southern points of the sphere.  Pontryagin--Thom recovers the original
class from the northern components only. -/


-- @@ L1296-1296 verbatim
namespace BridgeData


-- @@ L1298-1299 verbatim
variable {z : HomotopyGroup (Fin (n + 1)) (UnitSphere
    (EuclideanSpace ℝ (Fin (n + 1)))) (southPole n)}


-- @@ L1301-1301 verbatim
local notation "Eₙ" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L1303-1305 verbatim
/-- The northern part is the positive part of the canonical bridge sign. -/
def northPart (B : BridgeData n z) : Set Eₙ :=
  B.fiberSign.positivePart


-- @@ L1307-1311 verbatim
theorem mem_northPart_iff (B : BridgeData n z) {x : Eₙ} :
    x ∈ B.northPart ↔ x ∈ B.fls.fiber ∧
      nprep B.approx (WithLp.ofLp x) = northPoint B.y := by
  rw [northPart, B.fiberSign_positivePart]
  rfl


-- @@ L1313-1315 verbatim
theorem northPart_subset_fiber (B : BridgeData n z) :
    B.northPart ⊆ B.fls.fiber :=
  B.fiberSign.positivePart_subset_fiber


-- @@ L1317-1322 verbatim
/-- The collection of flow-orbit components contained in the northern part.  Using
containment (rather than merely testing a representative) makes the definition
independent of every representative choice. -/
def northOrbitCollection (B : BridgeData n z) (V : TamedField B.fls) :
    Set (Set Eₙ) :=
  B.fiberSign.positiveOrbitCollection V


-- @@ L1324-1327 verbatim
/-- The framed invariant associated to the original homotopy class: sum only over
the northern orbit components of the two-point bridge fiber. -/
def northFramedDelta (B : BridgeData n z) (V : TamedField B.fls) : ZMod 2 :=
  B.fiberSign.positiveFramedDelta V


-- @@ L1329-1331 verbatim
@[simp]
theorem northFramedDelta_eq_deltaOn (B : BridgeData n z) (V : TamedField B.fls) :
    B.northFramedDelta V = V.deltaOn (B.northOrbitCollection V) := rfl


-- @@ L1333-1337 verbatim
/-- The bridge invariant does not depend on the chosen tamed extension. -/
theorem northFramedDelta_eq_of_tamedField (B : BridgeData n z)
    (V U : TamedField B.fls) :
    B.northFramedDelta V = B.northFramedDelta U :=
  B.fiberSign.positiveFramedDelta_eq_of_tamedField V U


-- @@ L1339-1353 verbatim
/-- A transport of bridge fibers preserves the northern invariant once it preserves
both the component contribution and the northern/southern separation.  The latter
is the exact interface needed from the M2c event calculation. -/
theorem northFramedDelta_eq_of_transport
    {z' : HomotopyGroup (Fin (n + 1)) (UnitSphere
      (EuclideanSpace ℝ (Fin (n + 1)))) (southPole n)}
    {B₀ : BridgeData n z} {B₁ : BridgeData n z'}
    {V₀ : TamedField B₀.fls} {V₁ : TamedField B₁.fls}
    (T : V₀.DeltaTransport V₁)
    (hNorth : ∀ O : V₀.OrbitIndex,
      (O : Set Eₙ) ∈ B₀.northOrbitCollection V₀ ↔
        ((T.orbitEquiv O : V₁.OrbitIndex) : Set Eₙ) ∈
          B₁.northOrbitCollection V₁) :
    B₀.northFramedDelta V₀ = B₁.northFramedDelta V₁ := by
  exact V₀.deltaOn_eq_of_transport T hNorth


-- @@ L1355-1355 verbatim
end BridgeData


-- @@ L1357-1357 verbatim
end Submission
