/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

/-
Blueprint unit: mapping-degree. Basics: nonconstancy bridges, fibers, `fiberMultSum`.
-/
module

public import LeanPool.JacobianDiffgeo.LocalMultiplicity.Multiplicity
import LeanPool.JacobianDiffgeo.Surface.Identity
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic


-- @@ L18-35 verbatim
/-!
# Mapping-degree basics

* `RS.fiberMultSum F y` — the total multiplicity of `F` over `y` (a `finsum`; junk `0` for
  constant or non-holomorphic `F` by CC4's junk conventions) with its `Finset` bridge
  `fiberMultSum_eq_finset_sum` and junk lemma `fiberMultSum_of_forall_eq`.
* `RS.not_eventuallyConst` — globally nonconstant holomorphic maps on connected surfaces are
  nowhere locally constant (identity theorem); THE bridge to every local-multiplicity
  hypothesis. `RS.one_le_multiplicity_of_not_const` is its multiplicity corollary.
* Fibers of nonconstant holomorphic maps on compact surfaces are closed, discrete and finite:
  `RS.isDiscrete_fiber`, `RS.fiber_finite`.
* Re-exports (one-import convenience for downstream): `RS.isOpenMap_of_not_const'`,
  `RS.surjective_of_not_const'`; bounds `RS.multiplicity_le_fiberMultSum`,
  `RS.one_le_fiberMultSum`.

Surface perfectness (`(𝓝[≠] x).NeBot`) is NOT re-proved here: surfaces-and-charts already
provides the instance `RS.nhdsNE_neBot` for any `ChartedSpace ℂ` space.
-/


-- @@ L37-37 verbatim
@[expose] public section


-- @@ L39-39 verbatim
open Filter Set Function

-- @@ L40-40 verbatim
open scoped ContDiff Manifold Topology


-- @@ L42-42 verbatim
namespace RS


-- @@ L44-44 verbatim
/-! ### `fiberMultSum` (minimal instances) -/


-- @@ L46-46 verbatim
section FiberMultSumDef


-- @@ L48-49 verbatim
variable {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y]


-- @@ L51-55 verbatim
/-- Total multiplicity of `F` over `y` (the fiber-sum). Junk-free by convention: for
holomorphic nonconstant `F` on compact `X` the fiber is finite and every summand is `≥ 1`; for
constant `F` all summands are junk `0` (CC4), so the value is `0`. -/
noncomputable def fiberMultSum (F : X → Y) (y : Y) : ℕ :=
  ∑ᶠ x ∈ F ⁻¹' {y}, multiplicity F x


-- @@ L57-58 verbatim
theorem fiberMultSum_def (F : X → Y) (y : Y) :
    fiberMultSum F y = ∑ᶠ x ∈ F ⁻¹' {y}, multiplicity F x := rfl


-- @@ L60-62 verbatim
theorem fiberMultSum_eq_finset_sum {F : X → Y} {y : Y} (hfin : (F ⁻¹' {y}).Finite) :
    fiberMultSum F y = ∑ x ∈ hfin.toFinset, multiplicity F x :=
  finsum_mem_eq_finite_toFinset_sum _ hfin


-- @@ L64-70 verbatim
/-- Junk convention: constant maps have `fiberMultSum ≡ 0` (every summand is junk `0`). -/
theorem fiberMultSum_of_forall_eq {y : Y} (c : Y) : fiberMultSum (fun _ : X ↦ c) y = 0 := by
  rw [fiberMultSum_def]
  apply finsum_mem_of_eqOn_zero
  intro x _
  exact multiplicity_of_eventuallyConst
    (eventuallyConst_nhds_iff.mpr (Eventually.of_forall fun _ ↦ rfl))


-- @@ L72-72 verbatim
end FiberMultSumDef


-- @@ L74-74 verbatim
/-! ### Nonconstancy bridges and fibers (standing surface hypotheses) -/


-- @@ L76-77 verbatim
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

-- @@ L78-79 verbatim
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

-- @@ L80-80 verbatim
variable {F : X → Y}


-- @@ L82-91 verbatim
omit [T2Space X] [CompactSpace X] in
/-- Globally nonconstant holomorphic maps on connected surfaces are nowhere locally constant
(identity theorem). THE bridge to every local-multiplicity hypothesis. -/
theorem not_eventuallyConst (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hne : ¬ ∃ c, ∀ x, F x = c) (x : X) : ¬ EventuallyConst F (𝓝 x) := by
  intro h
  apply hne
  rw [eventuallyConst_nhds_iff] at h
  refine ⟨F x, fun z ↦ congrFun (eq_of_frequently_eq hF contMDiff_const (z₀ := x) ?_) z⟩
  exact (h.filter_mono (nhdsWithin_le_nhds (s := {x}ᶜ))).frequently


-- @@ L93-97 verbatim
omit [T2Space X] [CompactSpace X] in
/-- Pointwise multiplicity is `≥ 1` under the global hypotheses. -/
theorem one_le_multiplicity_of_not_const (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hne : ¬ ∃ c, ∀ x, F x = c) (x : X) : 1 ≤ multiplicity F x :=
  one_le_multiplicity (hF x) (not_eventuallyConst hF hne x)


-- @@ L99-110 verbatim
omit [T2Space X] [CompactSpace X] in
/-- Fibers of nonconstant holomorphic maps are discrete. -/
theorem isDiscrete_fiber (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F) (hne : ¬ ∃ c, ∀ x, F x = c)
    (y : Y) : IsDiscrete (F ⁻¹' {y}) := by
  rw [isDiscrete_iff_nhdsNE]
  intro x hx
  rw [inf_principal_eq_bot]
  have hxy : F x = y := hx
  filter_upwards [eventually_ne (hF x) (not_eventuallyConst hF hne x)] with z hz
  simp only [mem_compl_iff, mem_preimage, mem_singleton_iff]
  rw [← hxy]
  exact hz


-- @@ L112-117 verbatim
omit [T2Space X] in
/-- Fibers of nonconstant holomorphic maps on a compact surface are finite. -/
theorem fiber_finite (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F) (hne : ¬ ∃ c, ∀ x, F x = c)
    (y : Y) : (F ⁻¹' {y}).Finite := by
  have hclosed : IsClosed (F ⁻¹' {y}) := isClosed_singleton.preimage hF.continuous
  exact hclosed.isCompact.finite (isDiscrete_fiber hF hne y)


-- @@ L119-123 verbatim
omit [T2Space X] [CompactSpace X] in
/-- Re-export of surfaces-and-charts' open mapping theorem (one-import convenience). -/
theorem isOpenMap_of_not_const' (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hne : ¬ ∃ c, ∀ x, F x = c) : IsOpenMap F :=
  isOpenMap_of_not_const hF hne


-- @@ L125-129 verbatim
omit [T2Space X] in
/-- Re-export of surfaces-and-charts' surjectivity theorem (one-import convenience). -/
theorem surjective_of_not_const' [PreconnectedSpace Y] (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hne : ¬ ∃ c, ∀ x, F x = c) : Function.Surjective F :=
  surjective_of_not_const hF hne


-- @@ L131-138 verbatim
omit [T2Space X] in
/-- Each local multiplicity is bounded by the fiber-sum over its own value. -/
theorem multiplicity_le_fiberMultSum (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hne : ¬ ∃ c, ∀ x, F x = c) {x : X} :
    multiplicity F x ≤ fiberMultSum F (F x) := by
  have hfin := fiber_finite hF hne (F x)
  rw [fiberMultSum_eq_finset_sum hfin]
  exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (hfin.mem_toFinset.mpr rfl)


-- @@ L140-148 verbatim
omit [T2Space X] in
/-- Fiber-sums of nonconstant maps are positive (fibers are nonempty by surjectivity and
every summand is `≥ 1`). -/
theorem one_le_fiberMultSum [PreconnectedSpace Y] (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hne : ¬ ∃ c, ∀ x, F x = c) (y : Y) : 1 ≤ fiberMultSum F y := by
  obtain ⟨x, hx⟩ := surjective_of_not_const hF hne y
  calc 1 ≤ multiplicity F x := one_le_multiplicity_of_not_const hF hne x
    _ ≤ fiberMultSum F (F x) := multiplicity_le_fiberMultSum hF hne
    _ = fiberMultSum F y := by rw [hx]


-- @@ L150-150 verbatim
end RS
