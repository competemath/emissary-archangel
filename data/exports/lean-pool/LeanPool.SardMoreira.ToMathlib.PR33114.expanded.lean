/-
Copyright (c) 2026 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular


-- @@ L13-39 verbatim
/-!
# A copy of a metric space with metric given by `d x y = dist x y ^ α`

Given a (pseudo) (extended) metric space `X` and a number `0 < α < 1`,
one can consider the metric given by `d x y = (dist x y) ^ α`.
In this file we define `WithRPowDist X α hα₀ hα₁` to be a one-field structure wrapper around `X`
with metric given by this formula.

One of the reasons to introduce this definition is the following.
In the proof of his version of the Morse-Sard theorem,
Moreira [Moreira2001] studies maps of two variables that are Lipschitz continuous in one variable,
but satisfy a stronger assumption `‖f (a, y) - f (a, b)‖ = O(‖y - b‖ ^ α)`
along the second variable, as long as `(a, b)` is one of the "interesting" points.

If we want to apply Vitali family in this context, we need to cover the set by products
`closedBall a (R ^ α) ×ˢ closedBall b R` so that both components make a similar contribution
to `‖f (x, y) - f (a, b)‖`. These sets aren't balls in the original metric
(or even subsets of balls that occupy at least a fixed fraction of the volume,
as we require in our version of Vitali theorem).

However, if we change the metric on the first component to the one introduced in this file,
then these sets become balls, and we can apply Vitali theorem.

## References
* [Carlos Gustavo T. de A. Moreira, _Hausdorff measures and the Morse-Sard theorem_]
  [Moreira2001]
-/


-- @@ L41-41 verbatim
@[expose] public section



-- @@ L44-44 verbatim
open scoped ENNReal NNReal Filter Uniformity Topology

-- @@ L45-45 verbatim
open Function


-- @@ L47-47 verbatim
noncomputable section


-- @@ L49-55 verbatim
/-- A copy of a type with metric given by `dist x y = (dist x.val y.val) ^ α`.

This is defined as a one-field structure. -/
@[ext]
structure WithRPowDist (X : Type*) (α : ℝ) (hα₀ : 0 < α) (hα₁ : α ≤ 1) where
  /-- The value wrapped in `x : WithRPowDist X α hα₀ hα₁`. -/
  val : X


-- @@ L57-57 verbatim
namespace WithRPowDist


-- @@ L59-59 verbatim
variable {X : Type*} {α : ℝ} {hα₀ : 0 < α} {hα₁ : α ≤ 1}


-- @@ L61-67 verbatim
/-- The natural equivalence between `WithRPowDist X α hr₀ hr₁` and `X`. -/
@[simps -fullyApplied apply symm_apply]
def equiv (X : Type*) (α : ℝ) (hr₀ : 0 < α) (hr₁ : α ≤ 1) : WithRPowDist X α hr₀ hr₁ ≃ X where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl


-- @@ L69-70 verbatim
@[simp]
theorem val_comp_mk : (val : WithRPowDist X α hα₀ hα₁ → X) ∘ mk = id := rfl


-- @@ L72-73 verbatim
@[simp]
theorem mk_comp_val : (mk : X → WithRPowDist X α hα₀ hα₁) ∘ val = id := rfl


-- @@ L75-77 verbatim
theorem image_mk_eq_preimage (s : Set X) :
    (mk '' s : Set (WithRPowDist X α hα₀ hα₁)) = val ⁻¹' s :=
  (equiv X α hα₀ hα₁).symm.image_eq_preimage_symm _


-- @@ L79-81 verbatim
theorem image_val_eq_preimage (s : Set (WithRPowDist X α hα₀ hα₁)) :
    val '' s = mk ⁻¹' s :=
  (equiv X α hα₀ hα₁).image_eq_preimage_symm _


-- @@ L83-86 verbatim
@[simp]
theorem image_mk_image_val (s : Set (WithRPowDist X α hα₀ hα₁)) :
    mk '' (val '' s) = s :=
  (equiv X α hα₀ hα₁).symm_image_image _


-- @@ L88-90 verbatim
@[simp]
theorem image_val_image_mk (s : Set X) : val '' (mk '' s : Set (WithRPowDist X α hα₀ hα₁)) = s :=
  (equiv X α hα₀ hα₁).image_symm_image _


-- @@ L92-93 verbatim
theorem surjective_val : Surjective (val : WithRPowDist X α hα₀ hα₁ → X) :=
  equiv _ _ _ _ |>.surjective


-- @@ L95-96 verbatim
theorem surjective_mk : Surjective (mk :  X → WithRPowDist X α hα₀ hα₁) :=
  equiv _ _ _ _ |>.symm |>.surjective


-- @@ L98-98 verbatim
theorem injective_mk : Injective (mk : X → WithRPowDist X α hα₀ hα₁) := by simp [Injective]


-- @@ L100-104 verbatim
/-!
### Topological space structure

The topology on `WithRPowDist X α hα₀ hα₁` is induced from `X`.
-/


-- @@ L106-106 verbatim
section TopologicalSpace


-- @@ L108-108 verbatim
variable [TopologicalSpace X]


-- @@ L110-111 verbatim
/-- The topological space structure on `WithRPowDist X α _ _` is induced from the original space. -/
instance : TopologicalSpace (WithRPowDist X α hα₀ hα₁) := .induced WithRPowDist.val ‹_›


-- @@ L113-115 verbatim
@[fun_prop]
theorem continuous_val : Continuous (val : WithRPowDist X α hα₀ hα₁ → X) :=
  continuous_induced_dom


-- @@ L117-119 verbatim
@[fun_prop]
theorem continuous_mk : Continuous (mk : X → WithRPowDist X α hα₀ hα₁) :=
  continuous_induced_rng.2 continuous_id


-- @@ L121-124 verbatim
/-- The natural homeomorphism between `WithRPowDist X α hα₀ hα₁` and `X`. -/
@[simps! -fullyApplied toEquiv apply symm_apply]
def homeomorph : WithRPowDist X α hα₀ hα₁ ≃ₜ X where
  toEquiv := WithRPowDist.equiv X α hα₀ hα₁


-- @@ L126-130 verbatim
/-!
We copy some instances from the underlying space `X` to `WithRPowDist X α hα₀ hα₁`.
In the future, we can add more of them, if needed,
or even copy all the topology-related classes, if we get a tactic to do it automatically.
-/


-- @@ L132-133 verbatim
instance [T0Space X] : T0Space (WithRPowDist X α hα₀ hα₁) :=
  homeomorph.symm.t0Space


-- @@ L135-136 verbatim
instance [T2Space X] : T2Space (WithRPowDist X α hα₀ hα₁) :=
  homeomorph.symm.t2Space


-- @@ L138-139 verbatim
instance [SecondCountableTopology X] : SecondCountableTopology (WithRPowDist X α hα₀ hα₁) :=
  homeomorph.secondCountableTopology


-- @@ L141-141 verbatim
end TopologicalSpace


-- @@ L143-147 verbatim
/-!
### Bornology

The bornology on `WithRPowDist X α hα₀ hα₁` is induced from `X`.
-/


-- @@ L149-149 verbatim
section Bornology


-- @@ L151-151 verbatim
variable [Bornology X]


-- @@ L153-153 verbatim
instance : Bornology (WithRPowDist X α hα₀ hα₁) := .induced val


-- @@ L155-155 verbatim
open Bornology


-- @@ L157-160 verbatim
@[simp]
theorem _root_.WithRPowDist.isBounded_image_val_iff {s : Set (WithRPowDist X α hα₀ hα₁)} :
    IsBounded (val '' s) ↔ IsBounded s :=
  isBounded_induced.symm


-- @@ L162-164 verbatim
@[simp]
theorem _root_.WithRPowDist.isBounded_preimage_mk_iff {s : Set (WithRPowDist X α hα₀ hα₁)} :
    IsBounded (mk ⁻¹' s) ↔ IsBounded s := by rw [← image_val_eq_preimage, isBounded_image_val_iff]


-- @@ L166-169 verbatim
@[simp]
theorem _root_.WithRPowDist.isBounded_image_mk_iff {s : Set X} :
    IsBounded (mk '' s : Set (WithRPowDist X α hα₀ hα₁)) ↔ IsBounded s := by
  rw [← isBounded_image_val_iff, image_val_image_mk]


-- @@ L171-174 verbatim
@[simp]
theorem _root_.WithRPowDist.isBounded_preimage_val_iff {s : Set X} :
    IsBounded (val ⁻¹' s : Set (WithRPowDist X α hα₀ hα₁)) ↔ IsBounded s := by
  rw [← image_mk_eq_preimage, isBounded_image_mk_iff]


-- @@ L176-176 verbatim
end Bornology


-- @@ L178-182 verbatim
/-!
### Uniform space structure

The uniform space structure on `WithRPowDist X α hα₀ hα₁` is induced from `X`.
-/


-- @@ L184-184 verbatim
section UniformSpace


-- @@ L186-186 verbatim
variable [UniformSpace X]


-- @@ L188-189 verbatim
instance : UniformSpace (WithRPowDist X α hα₀ hα₁) :=
  UniformSpace.comap WithRPowDist.val ‹_›


-- @@ L191-193 verbatim
theorem _root_.WithRPowDist.uniformContinuous_val :
    UniformContinuous (val : WithRPowDist X α hα₀ hα₁ → X) :=
  uniformContinuous_comap


-- @@ L195-197 verbatim
theorem _root_.WithRPowDist.uniformContinuous_mk :
    UniformContinuous (mk : X → WithRPowDist X α hα₀ hα₁) :=
  uniformContinuous_comap' uniformContinuous_id


-- @@ L199-204 verbatim
/-- The natural uniform equivalence between `WithRPowDist X α hα₀ hα₁` and `X`. -/
@[simps! toEquiv apply symm_apply]
def _root_.WithRPowDist.uniformEquiv : WithRPowDist X α hα₀ hα₁ ≃ᵤ X where
  toEquiv := WithRPowDist.equiv X α hα₀ hα₁
  uniformContinuous_toFun := uniformContinuous_val
  uniformContinuous_invFun := uniformContinuous_mk


-- @@ L206-206 verbatim
end UniformSpace


-- @@ L208-215 verbatim
/-!
### Extended distance and a (pseudo) extended metric space structure

Th extended distance on `WithRPowDist X α hα₀ hα₁`
is given by `edist x y = (edist x.val y.val) ^ α`.

If the original space is a (pseudo) extended metric space, then so is `WithRPowDist X α hα₀ hα₁`.
-/


-- @@ L217-217 verbatim
section EDist


-- @@ L219-219 verbatim
variable [EDist X]


-- @@ L221-222 verbatim
instance : EDist (WithRPowDist X α hα₀ hα₁) where
  edist x y := edist x.val y.val ^ α


-- @@ L224-225 verbatim
theorem _root_.WithRPowDist.edist_def (x y : WithRPowDist X α hα₀ hα₁) :
    edist x y = edist x.val y.val ^ α := rfl


-- @@ L227-230 verbatim
@[simp]
theorem _root_.WithRPowDist.edist_mk_mk (x y : X) :
    edist (mk x : WithRPowDist X α hα₀ hα₁) (mk y) = edist x y ^ α :=
  rfl


-- @@ L232-234 verbatim
@[simp]
theorem _root_.WithRPowDist.edist_val_val (x y : WithRPowDist X α hα₀ hα₁) :
    edist x.val y.val = edist x y ^ α⁻¹ := by rw [edist_def, ENNReal.rpow_rpow_inv hα₀.ne']


-- @@ L236-236 verbatim
end EDist


-- @@ L238-238 verbatim
section PseudoEMetricSpace


-- @@ L240-240 verbatim
variable [PseudoEMetricSpace X]


-- @@ L242-242 verbatim
open Metric


-- @@ L244-256 verbatim
instance : PseudoEMetricSpace (WithRPowDist X α hα₀ hα₁) where
  edist_self x := by simp [edist_def, hα₀]
  edist_comm x y := by rw [edist_def, edist_def, edist_comm]
  edist_triangle x y z := by
    simp only [edist_def]
    grw [edist_triangle x.val y.val z.val, ENNReal.rpow_add_le_add_rpow _ _ hα₀.le hα₁]
  toUniformSpace := inferInstance
  uniformity_edist := by
    have H : (𝓤 X).HasBasis (0 < ·) fun x => {p | edist p.1 p.2 < x ^ (α⁻¹)} := by
      refine EMetric.mk_uniformity_basis (fun _ _ ↦ by positivity) fun ε hε ↦
        ⟨ε ^ α, by positivity, ?_⟩
      rw [ENNReal.rpow_rpow_inv hα₀.ne']
    simp (disch := positivity) [uniformity_comap, H.eq_biInf, ENNReal.rpow_lt_rpow_iff]


-- @@ L258-262 verbatim
@[simp]
theorem _root_.WithRPowDist.preimage_val_emetricBall (x : X) (r : ℝ≥0∞) :
    val ⁻¹' eball x r = eball (mk x : WithRPowDist X α hα₀ hα₁) (r ^ α) := by
  ext ⟨y⟩
  simp (disch := positivity) [ENNReal.rpow_lt_rpow_iff]


-- @@ L264-267 verbatim
@[simp]
theorem _root_.WithRPowDist.image_mk_emetricBall (x : X) (r : ℝ≥0∞) :
    mk '' eball x r = eball (mk x : WithRPowDist X α hα₀ hα₁) (r ^ α) := by
  rw [image_mk_eq_preimage, preimage_val_emetricBall]


-- @@ L269-274 verbatim
@[simp]
theorem _root_.WithRPowDist.preimage_mk_emetricBall
    (x : WithRPowDist X α hα₀ hα₁) (d : ℝ≥0∞) :
    mk ⁻¹' eball x d = eball x.val (d ^ α⁻¹) := by
  apply injective_mk.image_injective
  rw [image_mk_emetricBall, Set.image_preimage_eq _ surjective_mk, ENNReal.rpow_inv_rpow hα₀.ne']


-- @@ L276-280 verbatim
@[simp]
theorem _root_.WithRPowDist.image_val_emetricBall
    (x : WithRPowDist X α hα₀ hα₁) (d : ℝ≥0∞) :
    val '' eball x d = eball x.val (d ^ α⁻¹) := by
  rw [image_val_eq_preimage, preimage_mk_emetricBall]


-- @@ L282-286 verbatim
@[simp]
theorem _root_.WithRPowDist.preimage_val_emetricClosedBall (x : X) (r : ℝ≥0∞) :
    val ⁻¹' closedEBall x r = closedEBall (mk x : WithRPowDist X α hα₀ hα₁) (r ^ α) := by
  ext ⟨y⟩
  simp (disch := positivity) [ENNReal.rpow_le_rpow_iff]


-- @@ L288-291 verbatim
@[simp]
theorem _root_.WithRPowDist.image_mk_emetricClosedBall (x : X) (r : ℝ≥0∞) :
    mk '' closedEBall x r = closedEBall (mk x : WithRPowDist X α hα₀ hα₁) (r ^ α) := by
  rw [image_mk_eq_preimage, preimage_val_emetricClosedBall]


-- @@ L293-299 verbatim
@[simp]
theorem _root_.WithRPowDist.preimage_mk_emetricClosedBall
    (x : WithRPowDist X α hα₀ hα₁) (d : ℝ≥0∞) :
    mk ⁻¹' closedEBall x d = closedEBall x.val (d ^ α⁻¹) := by
  apply injective_mk.image_injective
  rw [image_mk_emetricClosedBall, Set.image_preimage_eq _ surjective_mk,
    ENNReal.rpow_inv_rpow hα₀.ne']


-- @@ L301-305 verbatim
@[simp]
theorem _root_.WithRPowDist.image_val_emetricClosedBall
    (x : WithRPowDist X α hα₀ hα₁) (d : ℝ≥0∞) :
    val '' closedEBall x d = closedEBall x.val (d ^ α⁻¹) := by
  rw [image_val_eq_preimage, preimage_mk_emetricClosedBall]


-- @@ L307-311 verbatim
@[simp]
theorem _root_.WithRPowDist.ediam_image_val (s : Set (WithRPowDist X α hα₀ hα₁)) :
    ediam (val '' s) = ediam s ^ α⁻¹ := by
  refine eq_of_forall_ge_iff fun c ↦ ?_
  simp [ediam_le_iff, ENNReal.rpow_inv_le_iff hα₀]


-- @@ L313-315 verbatim
@[simp]
theorem _root_.WithRPowDist.ediam_preimage_mk (s : Set (WithRPowDist X α hα₀ hα₁)) :
    ediam (mk ⁻¹' s) = ediam s ^ α⁻¹ := by rw [← image_val_eq_preimage, ediam_image_val]


-- @@ L317-321 verbatim
@[simp]
theorem _root_.WithRPowDist.ediam_preimage_val (s : Set X) :
    ediam (val ⁻¹' s : Set (WithRPowDist X α hα₀ hα₁)) = ediam s ^ α := by
  rw [← ENNReal.rpow_inv_rpow hα₀.ne' (ediam _), ← ediam_preimage_mk,
    ← Set.preimage_comp, val_comp_mk, Set.preimage_id]


-- @@ L323-326 verbatim
@[simp]
theorem _root_.WithRPowDist.ediam_image_mk (s : Set X) :
    ediam (mk '' s : Set (WithRPowDist X α hα₀ hα₁)) = ediam s ^ α := by
  simp [image_mk_eq_preimage]


-- @@ L328-328 verbatim
end PseudoEMetricSpace


-- @@ L330-331 verbatim
instance [EMetricSpace X] : EMetricSpace (WithRPowDist X α hα₀ hα₁) :=
  .ofT0PseudoEMetricSpace _


-- @@ L333-340 verbatim
/-!
### Distance and a (pseudo) metric space structure

Th extended distance on `WithRPowDist X α hα₀ hα₁`
is given by `dist x y = (dist x.val y.val) ^ α`.

If the original space is a (pseudo) metric space, then so is `WithRPowDist X α hα₀ hα₁`.
-/


-- @@ L342-343 verbatim
instance [Dist X] : Dist (WithRPowDist X α hα₀ hα₁) where
  dist x y := dist x.val y.val ^ α


-- @@ L345-348 verbatim
@[simp]
theorem _root_.WithRPowDist.dist_mk_mk [Dist X] (x y : X) :
    dist (mk x : WithRPowDist X α hα₀ hα₁) (mk y) = dist x y ^ α :=
  rfl


-- @@ L350-350 verbatim
section PseudoMetricSpace


-- @@ L352-352 verbatim
variable [PseudoMetricSpace X]


-- @@ L354-371 verbatim
instance : PseudoMetricSpace (WithRPowDist X α hα₀ hα₁) :=
  letI aux : PseudoMetricSpace (WithRPowDist X α hα₀ hα₁) :=
    PseudoEMetricSpace.toPseudoMetricSpaceOfDist dist
      (by rintro ⟨x⟩ ⟨y⟩; rw [dist_mk_mk]; positivity)
      (by
        rintro ⟨x⟩ ⟨y⟩
        rw [edist_mk_mk, dist_mk_mk, ← ENNReal.ofReal_rpow_of_nonneg, ← edist_dist] <;> positivity)
  aux.replaceBornology fun s ↦ by
    rw [← isBounded_preimage_mk_iff, Metric.isBounded_iff, Metric.isBounded_iff]
    constructor
    · rintro ⟨C, hC⟩
      use C ^ α
      rintro ⟨x⟩ hx ⟨y⟩ hy
      grw [dist_mk_mk, hC hx hy]
    · rintro ⟨C, hC⟩
      use C ^ α⁻¹
      intro x hx y hy
      grw [← hC hx hy, dist_mk_mk, Real.rpow_rpow_inv (by positivity) hα₀.ne']


-- @@ L373-373 verbatim
open Metric


-- @@ L375-379 verbatim
@[simp]
theorem _root_.WithRPowDist.dist_val_val (x y : WithRPowDist X α hα₀ hα₁) :
    dist x.val y.val = dist x y ^ α⁻¹ := by
  cases x; cases y
  rw [dist_mk_mk, Real.rpow_rpow_inv dist_nonneg hα₀.ne']


-- @@ L381-385 verbatim
@[simp]
theorem _root_.WithRPowDist.preimage_val_ball (x : X) {r : ℝ} (hr : 0 ≤ r) :
    val ⁻¹' ball x r = ball (mk x : WithRPowDist X α hα₀ hα₁) (r ^ α) := by
  ext ⟨y⟩
  simp (disch := positivity) [Real.rpow_lt_rpow_iff]


-- @@ L387-390 verbatim
@[simp]
theorem _root_.WithRPowDist.image_mk_ball (x : X) {r : ℝ} (hr : 0 ≤ r) :
    mk '' ball x r = ball (mk x : WithRPowDist X α hα₀ hα₁) (r ^ α) := by
  rw [image_mk_eq_preimage, preimage_val_ball x hr]


-- @@ L392-398 verbatim
@[simp]
theorem _root_.WithRPowDist.preimage_mk_ball
    (x : WithRPowDist X α hα₀ hα₁) {r : ℝ} (hr : 0 ≤ r) :
    mk ⁻¹' ball x r = ball x.val (r ^ α⁻¹) := by
  apply injective_mk.image_injective
  rw [image_mk_ball _ (by positivity), Set.image_preimage_eq _ surjective_mk,
    Real.rpow_inv_rpow hr hα₀.ne']


-- @@ L400-403 verbatim
@[simp]
theorem _root_.WithRPowDist.image_val_ball
    (x : WithRPowDist X α hα₀ hα₁) {r : ℝ} (hr : 0 ≤ r) :
    val '' ball x r = ball x.val (r ^ α⁻¹) := by rw [image_val_eq_preimage, preimage_mk_ball _ hr]


-- @@ L405-409 verbatim
@[simp]
theorem _root_.WithRPowDist.preimage_val_closedBall (x : X) {r : ℝ} (hr : 0 ≤ r) :
    val ⁻¹' closedBall x r = closedBall (mk x : WithRPowDist X α hα₀ hα₁) (r ^ α) := by
  ext ⟨y⟩
  simp (disch := positivity) [Real.rpow_le_rpow_iff]


-- @@ L411-414 verbatim
@[simp]
theorem _root_.WithRPowDist.image_mk_closedBall (x : X) {r : ℝ} (hr : 0 ≤ r) :
    mk '' closedBall x r = closedBall (mk x : WithRPowDist X α hα₀ hα₁) (r ^ α) := by
  rw [image_mk_eq_preimage, preimage_val_closedBall x hr]


-- @@ L416-422 verbatim
@[simp]
theorem _root_.WithRPowDist.preimage_mk_closedBall
    (x : WithRPowDist X α hα₀ hα₁) {r : ℝ} (hr : 0 ≤ r) :
    mk ⁻¹' closedBall x r = closedBall x.val (r ^ α⁻¹) := by
  apply injective_mk.image_injective
  rw [image_mk_closedBall _ (by positivity), Set.image_preimage_eq _ surjective_mk,
    Real.rpow_inv_rpow hr hα₀.ne']


-- @@ L424-428 verbatim
@[simp]
theorem _root_.WithRPowDist.image_val_closedBall
    (x : WithRPowDist X α hα₀ hα₁) {r : ℝ} (hr : 0 ≤ r) :
    val '' closedBall x r = closedBall x.val (r ^ α⁻¹) := by
  rw [image_val_eq_preimage, preimage_mk_closedBall _ hr]


-- @@ L430-430 verbatim
end PseudoMetricSpace


-- @@ L432-433 verbatim
instance [MetricSpace X] : MetricSpace (WithRPowDist X α hα₀ hα₁) :=
  .ofT0PseudoMetricSpace _


-- @@ L435-435 verbatim
end WithRPowDist
