/-
Copyright (c) 2026 Jeremy Parker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy P Parker
-/
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Measure
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar


-- @@ L16-16 verbatim
set_option linter.unusedSectionVars false

-- @@ L17-17 verbatim
set_option linter.unusedFintypeInType false

-- @@ L18-18 verbatim
set_option linter.unusedDecidableInType false


-- @@ L20-20 verbatim
open scoped BigOperators Pointwise

-- @@ L21-21 verbatim
open Set

-- @@ L22-22 verbatim
open MeasureTheory

-- @@ L23-23 verbatim
open SimpleGraph


-- @@ L25-25 verbatim
universe u v w


-- @@ L27-27 verbatim
namespace HansenCograph


-- @@ L29-31 verbatim
/-!
## Basic graph operations
-/


-- @@ L33-37 verbatim
/-- Graph join, defined by De Morgan duality from Mathlib's disjoint sum. -/
def graphJoin {V : Type u} {W : Type v}
    (G : SimpleGraph V) (H : SimpleGraph W) :
    SimpleGraph (V ⊕ W) :=
  (Gᶜ ⊕g Hᶜ)ᶜ


-- @@ L39-39 verbatim
infixl:60 " ⊗g " => graphJoin


-- @@ L41-45 expanded
@[simp]
theorem compl_sum_eq_join {V : Type u} {W : Type v} (G : SimpleGraph V) (H : SimpleGraph W) :
    (G ⊕g H)ᶜ = graphJoin Gᶜ Hᶜ := by simp [graphJoin]


-- @@ L47-52 expanded
@[simp]
theorem compl_join_eq_sum {V : Type u} {W : Type v} (G : SimpleGraph V) (H : SimpleGraph W) :
    (graphJoin G H)ᶜ = Gᶜ ⊕g Hᶜ := by
  unfold graphJoin
  exact compl_compl (Gᶜ ⊕g Hᶜ)


-- @@ L54-58 verbatim
/-!
## Stable-set polytope

Vectors are represented by `V → ℝ`.
-/


-- @@ L60-60 verbatim
section StableSetPolytope


-- @@ L62-62 verbatim
variable {V : Type u} [DecidableEq V]


-- @@ L64-66 verbatim
/-- 0/1 indicator vector of a finite set of vertices. -/
def indicator (s : Finset V) : V → ℝ :=
  fun v => if v ∈ s then 1 else 0


-- @@ L68-71 verbatim
@[simp]
theorem indicator_empty : indicator (∅ : Finset V) = 0 := by
  ext v
  simp [indicator]


-- @@ L73-76 verbatim
@[simp]
theorem indicator_apply_mem {s : Finset V} {v : V} (hv : v ∈ s) :
    indicator s v = 1 := by
  simp [indicator, hv]


-- @@ L78-81 verbatim
@[simp]
theorem indicator_apply_not_mem {s : Finset V} {v : V} (hv : v ∉ s) :
    indicator s v = 0 := by
  simp [indicator, hv]


-- @@ L83-87 verbatim
/-- Stable 0/1 vectors. -/
def stableIndicators (G : SimpleGraph V) : Set (V → ℝ) :=
  {x | ∃ s : Finset V,
      G.IsIndepSet (↑s : Set V) ∧
      x = indicator s}


-- @@ L89-91 verbatim
/-- The stable-set polytope `STAB(G)`. -/
def stab (G : SimpleGraph V) : Set (V → ℝ) :=
  convexHull ℝ (stableIndicators G)


-- @@ L93-95 verbatim
theorem convex_stab (G : SimpleGraph V) :
    Convex ℝ (stab G) := by
  exact convex_convexHull ℝ _


-- @@ L97-101 verbatim
theorem indicator_mem_stab (G : SimpleGraph V)
    {s : Finset V} (hs : G.IsIndepSet (↑s : Set V)) :
    indicator s ∈ stab G := by
  apply subset_convexHull ℝ
  exact ⟨s, hs, rfl⟩


-- @@ L103-109 verbatim
theorem zero_mem_stab (G : SimpleGraph V) : (0 : V → ℝ) ∈ stab G := by
  have h0 : G.IsIndepSet (↑(∅ : Finset V) : Set V) := by
    simp
  have h := indicator_mem_stab G h0
  convert h using 1
  ext v
  simp [indicator]


-- @@ L111-125 verbatim
/-- Every coordinate of a point of `STAB(G)` is nonnegative. -/
theorem stab_coordinate_nonneg (G : SimpleGraph V)
    {x : V → ℝ} (hx : x ∈ stab G) (v : V) :
    0 ≤ x v := by
  change x ∈ {y : V → ℝ | 0 ≤ y v}
  apply (convexHull_min ?_ ?_) hx
  · rintro y ⟨s, hs, rfl⟩
    change 0 ≤ indicator s v
    by_cases hv : v ∈ s <;> simp [indicator, hv]
  · intro y hy z hz a b ha hb hab
    change 0 ≤ y v at hy
    change 0 ≤ z v at hz
    change 0 ≤ (a • y + b • z) v
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith


-- @@ L127-141 verbatim
/-- Every coordinate of a point of `STAB(G)` is at most one. -/
theorem stab_coordinate_le_one (G : SimpleGraph V)
    {x : V → ℝ} (hx : x ∈ stab G) (v : V) :
    x v ≤ 1 := by
  change x ∈ {y : V → ℝ | y v ≤ 1}
  apply (convexHull_min ?_ ?_) hx
  · rintro y ⟨s, hs, rfl⟩
    change indicator s v ≤ 1
    by_cases hv : v ∈ s <;> simp [indicator, hv]
  · intro y hy z hz a b ha hb hab
    change y v ≤ 1 at hy
    change z v ≤ 1 at hz
    change (a • y + b • z) v ≤ 1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith


-- @@ L143-170 verbatim
/--
If `u ~ v`, every stable-set vector satisfies `x_u + x_v ≤ 1`.

This is the key elementary lemma needed at the very end of the
central-symmetry equality analysis.
-/
theorem stab_edge_ineq (G : SimpleGraph V)
    {x : V → ℝ} (hx : x ∈ stab G)
    {u v : V} (huv : G.Adj u v) :
    x u + x v ≤ 1 := by
  change x ∈ {y : V → ℝ | y u + y v ≤ 1}
  apply (convexHull_min ?_ ?_) hx
  · rintro y ⟨s, hs, rfl⟩
    change indicator s u + indicator s v ≤ 1
    by_cases hu : u ∈ s
    · have hv : v ∉ s := by
        intro hvs
        have hn : ¬G.Adj u v :=
          hs (by simpa using hu) (by simpa using hvs) huv.ne
        exact hn huv
      simp [indicator, hu, hv]
    · by_cases hv : v ∈ s <;> simp [indicator, hu, hv]
  · intro y hy z hz a b ha hb hab
    change y u + y v ≤ 1 at hy
    change z u + z v ≤ 1 at hz
    change (a • y + b • z) u + (a • y + b • z) v ≤ 1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith


-- @@ L172-172 verbatim
end StableSetPolytope


-- @@ L174-184 verbatim
/-!
## Normalized stable-set volume

Mathematically:

    nu(G) = |V(G)|! * vol(STAB(G)).

We use Mathlib's product Lebesgue measure on the finite Pi-space.  Thus the
coordinate cube `[0,1]^V` has volume one, fixing the normalization required by
the graph formulas below.
-/


-- @@ L186-186 verbatim
section NormalizedVolume


-- @@ L188-188 verbatim
variable {V : Type u} [Fintype V] [DecidableEq V]


-- @@ L190-191 verbatim
noncomputable def nu (G : SimpleGraph V) : ℝ :=
  (Fintype.card V).factorial * (volume (stab G)).toReal


-- @@ L193-196 verbatim
theorem nu_nonneg (G : SimpleGraph V) :
    0 ≤ nu G := by
  unfold nu
  positivity


-- @@ L198-254 verbatim
/--
`STAB(G)` contains a uniform cube of side `1 / (|V|+1)`.

For a point `x` in that cube, use coefficient `x v` on the stable indicator
of `{v}` and put the remaining coefficient on the zero vector.
-/
theorem smallCube_subset_stab (G : SimpleGraph V) :
    Set.Icc (0 : V → ℝ)
        (fun _ => 1 / ((Fintype.card V : ℝ) + 1)) ⊆ stab G := by
  intro x hx
  let c : ℝ := 1 / ((Fintype.card V : ℝ) + 1)
  have hsum : ∑ v : V, x v ≤ 1 := by
    calc
      ∑ v : V, x v ≤ ∑ _v : V, c := by
        apply Finset.sum_le_sum
        intro v hv
        exact hx.2 v
      _ = (Fintype.card V : ℝ) * c := by simp
      _ ≤ 1 := by
        dsimp [c]
        calc
          (Fintype.card V : ℝ) *
                (1 / ((Fintype.card V : ℝ) + 1))
              ≤ ((Fintype.card V : ℝ) + 1) *
                (1 / ((Fintype.card V : ℝ) + 1)) := by
                  apply mul_le_mul_of_nonneg_right
                  · norm_num
                  · positivity
          _ = 1 := by field_simp
  let weight : Option V → ℝ
    | none => 1 - ∑ v : V, x v
    | some v => x v
  let point : Option V → (V → ℝ)
    | none => 0
    | some v => indicator {v}
  have hweight : ∀ i ∈ (Finset.univ : Finset (Option V)), 0 ≤ weight i := by
    intro i hi
    cases i with
    | none =>
        dsimp [weight]
        linarith
    | some v =>
        exact hx.1 v
  have hweight_sum : ∑ i : Option V, weight i = 1 := by
    simp [weight]
  have hpoint : ∀ i ∈ (Finset.univ : Finset (Option V)), point i ∈ stab G := by
    intro i hi
    cases i with
    | none => exact zero_mem_stab G
    | some v =>
        dsimp [point]
        apply indicator_mem_stab
        simp
  have hconv := (convex_stab G).sum_mem hweight hweight_sum hpoint
  convert hconv using 1
  ext v
  simp [weight, point, indicator]


-- @@ L256-263 verbatim
theorem stab_subset_unitCube (G : SimpleGraph V) :
    stab G ⊆ Set.Icc (0 : V → ℝ) (1 : V → ℝ) := by
  intro x hx
  constructor
  · intro v
    exact stab_coordinate_nonneg G hx v
  · intro v
    exact stab_coordinate_le_one G hx v


-- @@ L265-287 verbatim
theorem stableIndicators_bot :
    stableIndicators (⊥ : SimpleGraph V) =
      Set.univ.pi (fun _ : V => ({0, 1} : Set ℝ)) := by
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    intro v hv
    by_cases hvs : v ∈ s
    · simp [indicator, hvs]
    · simp [indicator, hvs]
  · intro hx
    let s : Finset V := Finset.univ.filter (fun v => x v = 1)
    refine ⟨s, ?_, ?_⟩
    · intro u hu v hv huv hadj
      exact hadj
    ext v
    have hv := hx v (by simp)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with hv | hv
    · have hvs : v ∉ s := by simp [s, hv]
      simp [indicator, hvs, hv]
    · have hvs : v ∈ s := by simp [s, hv]
      simp [indicator, hvs, hv]


-- @@ L289-297 verbatim
theorem stab_bot :
    stab (⊥ : SimpleGraph V) =
      Set.Icc (0 : V → ℝ) (1 : V → ℝ) := by
  unfold stab
  rw [stableIndicators_bot, convexHull_pi]
  simp_rw [convexHull_pair,
    segment_eq_Icc (by norm_num : (0 : ℝ) ≤ 1)]
  ext x
  simp [Pi.le_def]


-- @@ L299-304 verbatim
@[simp]
theorem nu_bot :
    nu (⊥ : SimpleGraph V) = (Fintype.card V).factorial := by
  unfold nu
  rw [stab_bot, Real.volume_Icc_pi_toReal (by intro v; norm_num)]
  simp


-- @@ L306-341 verbatim
theorem nu_pos (G : SimpleGraph V) :
    0 < nu G := by
  let c : ℝ := 1 / ((Fintype.card V : ℝ) + 1)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  let U : Set (V → ℝ) :=
    {x | ∀ v, x v ∈ Set.Ioo (0 : ℝ) c}
  have hUopen : IsOpen U := by
    rw [show U = ⋂ v : V,
        (fun x : V → ℝ => x v) ⁻¹' Set.Ioo (0 : ℝ) c by
      ext x
      simp [U]]
    apply isOpen_iInter_of_finite
    intro v
    exact isOpen_Ioo.preimage (continuous_apply v)
  have hUne : U.Nonempty := by
    refine ⟨fun _ => c / 2, ?_⟩
    intro v
    constructor <;> dsimp <;> linarith
  have hUstab : U ⊆ stab G := by
    intro x hx
    apply smallCube_subset_stab G
    constructor
    · intro v
      exact le_of_lt (hx v).1
    · intro v
      exact le_of_lt (hx v).2
  have hvol_pos : 0 < volume (stab G) :=
    lt_of_lt_of_le (hUopen.measure_pos volume hUne) (measure_mono hUstab)
  have hvol_lt_top : volume (stab G) < ⊤ :=
    lt_of_le_of_lt (measure_mono (stab_subset_unitCube G))
      (isCompact_Icc.measure_lt_top)
  unfold nu
  exact mul_pos (by positivity)
    (ENNReal.toReal_pos hvol_pos.ne' hvol_lt_top.ne)


-- @@ L343-343 verbatim
end NormalizedVolume


-- @@ L345-347 verbatim
/-!
## Isomorphism invariance
-/


-- @@ L349-349 verbatim
section IsoInvariance


-- @@ L351-351 verbatim
variable {V : Type u} [Fintype V] [DecidableEq V]

-- @@ L352-352 verbatim
variable {W : Type v} [Fintype W] [DecidableEq W]


-- @@ L354-369 verbatim
/-- Reindex coordinate functions along a vertex equivalence. -/
def coordinateRelabel (e : V ≃ W) : (V → ℝ) ≃ₗ[ℝ] (W → ℝ) where
  toFun x w := x (e.symm w)
  invFun y v := y (e v)
  left_inv x := by
    funext v
    simp
  right_inv y := by
    funext w
    simp
  map_add' x y := by
    funext w
    rfl
  map_smul' a x := by
    funext w
    rfl


-- @@ L371-373 verbatim
@[simp]
theorem coordinateRelabel_apply (e : V ≃ W) (x : V → ℝ) (w : W) :
    coordinateRelabel e x w = x (e.symm w) := rfl


-- @@ L375-377 verbatim
/-- Relabel a finite vertex set along an equivalence. -/
def relabelFinset (e : V ≃ W) (s : Finset V) : Finset W :=
  s.map e.toEmbedding


-- @@ L379-382 verbatim
@[simp]
theorem mem_relabelFinset (e : V ≃ W) (s : Finset V) (w : W) :
    w ∈ relabelFinset e s ↔ e.symm w ∈ s := by
  simp [relabelFinset]


-- @@ L384-401 verbatim
theorem isIndepSet_relabel
    {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) {s : Finset V}
    (hs : G.IsIndepSet (↑s : Set V)) :
    H.IsIndepSet (↑(relabelFinset e.toEquiv s) : Set W) := by
  intro w hw z hz hwz
  have hw' : e.symm w ∈ s := by
    exact (mem_relabelFinset e.toEquiv s w).mp hw
  have hz' : e.symm z ∈ s := by
    exact (mem_relabelFinset e.toEquiv s z).mp hz
  have hwz' : e.symm w ≠ e.symm z := by
    intro h
    apply hwz
    simpa using congrArg e h
  have hn := hs hw' hz' hwz'
  intro hadj
  apply hn
  exact (e.symm.map_rel_iff).mpr hadj


-- @@ L403-408 verbatim
@[simp]
theorem coordinateRelabel_indicator
    (e : V ≃ W) (s : Finset V) :
    coordinateRelabel e (indicator s) = indicator (relabelFinset e s) := by
  funext w
  simp [indicator]


-- @@ L410-420 verbatim
theorem coordinateRelabel_mem_stab
    {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) {x : V → ℝ} (hx : x ∈ stab G) :
    coordinateRelabel e.toEquiv x ∈ stab H := by
  change x ∈ (coordinateRelabel e.toEquiv : (V → ℝ) → (W → ℝ)) ⁻¹' stab H
  apply (convexHull_min ?_ ((convex_stab H).linear_preimage
    (coordinateRelabel e.toEquiv).toLinearMap)) hx
  rintro y ⟨s, hs, rfl⟩
  change coordinateRelabel e.toEquiv (indicator s) ∈ stab H
  rw [coordinateRelabel_indicator]
  exact indicator_mem_stab H (isIndepSet_relabel e hs)


-- @@ L422-437 verbatim
theorem stab_eq_coordinateRelabel_preimage
    {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) :
    stab G = (coordinateRelabel e.toEquiv : (V → ℝ) → (W → ℝ)) ⁻¹' stab H := by
  apply Set.Subset.antisymm
  · intro x hx
    exact coordinateRelabel_mem_stab e hx
  · intro x hx
    have hback := coordinateRelabel_mem_stab e.symm hx
    have heq : coordinateRelabel e.symm.toEquiv
        (coordinateRelabel e.toEquiv x) = x := by
      ext v
      change x (e.symm (e v)) = x v
      rw [e.symm_apply_apply]
    rw [heq] at hback
    exact hback


-- @@ L439-464 verbatim
/-- Coordinate reindexing preserves product Lebesgue measure. -/
theorem coordinateRelabel_measurePreserving (e : V ≃ W) :
    MeasurePreserving (coordinateRelabel e) := by
  refine ⟨?_, ?_⟩
  · change Measurable (fun x : V → ℝ => fun w => x (e.symm w))
    fun_prop
  · symm
    rw [volume_pi]
    apply Measure.pi_eq
    intro s hs
    rw [Measure.map_apply (by
      change Measurable (fun x : V → ℝ => fun w => x (e.symm w))
      fun_prop) (MeasurableSet.univ_pi hs)]
    rw [show (coordinateRelabel e : (V → ℝ) → (W → ℝ)) ⁻¹' Set.univ.pi s =
        Set.univ.pi (fun v => s (e v)) by
      ext x
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const,
        coordinateRelabel_apply]
      constructor
      · intro h v
        simpa using h (e v)
      · intro h w
        simpa using h (e.symm w)]
    rw [volume_pi_pi]
    exact Fintype.prod_equiv e
      (fun v => volume (s (e v))) (fun w => volume (s w)) (fun v => rfl)


-- @@ L466-475 verbatim
/-- The measurable equivalence underlying coordinate reindexing. -/
def coordinateRelabelMeasurableEquiv (e : V ≃ W) :
    (V → ℝ) ≃ᵐ (W → ℝ) where
  toEquiv := (coordinateRelabel e).toEquiv
  measurable_toFun := by
    change Measurable (fun x : V → ℝ => fun w => x (e.symm w))
    fun_prop
  measurable_invFun := by
    change Measurable (fun y : W → ℝ => fun v => y (e v))
    fun_prop


-- @@ L477-488 verbatim
theorem nu_iso
    {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) :
    nu G = nu H := by
  have hpre :=
    (coordinateRelabel_measurePreserving e.toEquiv).measure_preimage_emb
      (coordinateRelabelMeasurableEquiv e.toEquiv).measurableEmbedding (stab H)
  have hvol : volume (stab G) = volume (stab H) := by
    rw [stab_eq_coordinateRelabel_preimage e]
    exact hpre
  unfold nu
  rw [Fintype.card_congr e.toEquiv, hvol]


-- @@ L490-490 verbatim
end IsoInvariance


-- @@ L492-492 verbatim
end HansenCograph
