import Mathlib
import Submission.PTTransverseHomotopyCobordism


-- @@ L4-21 verbatim
/-!
# Relative Sard transversality for collared sphere homotopies

This file supplies the Sard step immediately upstream of
`PTTransverseHomotopyData`.  A smooth sphere-valued map on space-time which is
constant in the time direction on both end collars and equal to the south pole
at spatial infinity has a nonzero small regular horizontal value.  The two end
level sets and their signs induced by that value are honest framed level sets,
and the original sphere homotopy produces an exact signed framed cobordism
between them.

The end presentations here are deliberately *induced* by the selected value.
For a general pre-existing `FramedLevelSet`, identifying its defining map on an
entire collar with the horizontal coordinates of a unit-sphere-valued map would
impose an extraneous pointwise unit-norm identity.  The induced formulation is
the satisfiable relative-transversality core; comparison with an independently
specified endpoint is a separate value-change/collar-splicing problem.
-/


-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
namespace Submission


-- @@ L27-27 verbatim
open Set Function Metric

-- @@ L28-28 verbatim
open scoped Topology RealInnerProductSpace ContDiff


-- @@ L30-30 verbatim
variable {n : ℕ}


-- @@ L32-32 verbatim
local notation "A" => EuclideanSpace ℝ (Fin (n + 1 + 1))

-- @@ L33-33 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L34-34 verbatim
local notation "F" => EuclideanSpace ℝ (Fin n)


-- @@ L36-36 verbatim
namespace PTTransverseHomotopyData


-- @@ L38-39 verbatim
variable {X₀ X₁ : FramedLevelSet n} {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}
  (D : PTTransverseHomotopyData S₀ S₁)


-- @@ L41-59 verbatim
/-- The current downstream contract forces this unit-norm identity on every
incoming collar point.  This records precisely why that contract cannot be
filled directly from an arbitrary independently specified defining map and
sign field. -/
theorem source_collar_unit_constraint (x : E) :
    ‖X₀.g x + D.target‖ ^ 2 + S₀ x ^ 2 = 1 := by
  have hh := D.horizontal_collar_zero x 0 (by norm_num)
  have hinit : initCLM n (D.sphere (spaceTime x 0) : E) = X₀.g x + D.target := by
    have := congrArg (fun z : F => z + D.target) hh
    simpa using this
  have hvert := D.vertical_collar_zero x 0 (by norm_num)
  calc
    ‖X₀.g x + D.target‖ ^ 2 + S₀ x ^ 2 =
        ‖initCLM n (D.sphere (spaceTime x 0) : E)‖ ^ 2 +
          vertC (D.sphere (spaceTime x 0) : E) ^ 2 := by
            rw [hinit, hvert]
    _ = ‖(D.sphere (spaceTime x 0) : E)‖ ^ 2 :=
      (norm_sq_split _).symm
    _ = 1 := by rw [UnitSphere.norm_coe]; norm_num


-- @@ L61-76 verbatim
/-- Outgoing analogue of `source_collar_unit_constraint`. -/
theorem target_collar_unit_constraint (x : E) :
    ‖X₁.g x + D.target‖ ^ 2 + S₁ x ^ 2 = 1 := by
  have hh := D.horizontal_collar_one x 1 (by norm_num)
  have hinit : initCLM n (D.sphere (spaceTime x 1) : E) = X₁.g x + D.target := by
    have := congrArg (fun z : F => z + D.target) hh
    simpa using this
  have hvert := D.vertical_collar_one x 1 (by norm_num)
  calc
    ‖X₁.g x + D.target‖ ^ 2 + S₁ x ^ 2 =
        ‖initCLM n (D.sphere (spaceTime x 1) : E)‖ ^ 2 +
          vertC (D.sphere (spaceTime x 1) : E) ^ 2 := by
            rw [hinit, hvert]
    _ = ‖(D.sphere (spaceTime x 1) : E)‖ ^ 2 :=
      (norm_sq_split _).symm
    _ = 1 := by rw [UnitSphere.norm_coe]; norm_num


-- @@ L78-78 verbatim
end PTTransverseHomotopyData


-- @@ L80-93 verbatim
/-- A smooth sphere homotopy with exact time collars and a spatially uniform
south-pole exterior.  No transversality is postulated here. -/
structure CollaredSphereHomotopy (n : ℕ) where
  sphere : EuclideanSpace ℝ (Fin (n + 1 + 1)) →
    UnitSphere (EuclideanSpace ℝ (Fin (n + 1)))
  smooth : ContDiff ℝ ∞ fun v =>
    (sphere v : EuclideanSpace ℝ (Fin (n + 1)))
  exterior_south : ∃ R : ℝ,
    ∀ v : EuclideanSpace ℝ (Fin (n + 1 + 1)),
    R < ‖initCLM (n + 1) v‖ → sphere v = southPole n
  collar_zero : ∀ x : EuclideanSpace ℝ (Fin (n + 1)), ∀ t : ℝ, t ≤ 1 / 4 →
    sphere (spaceTime x t) = sphere (spaceTime x 0)
  collar_one : ∀ x : EuclideanSpace ℝ (Fin (n + 1)), ∀ t : ℝ, 3 / 4 ≤ t →
    sphere (spaceTime x t) = sphere (spaceTime x 1)


-- @@ L95-95 verbatim
namespace CollaredSphereHomotopy


-- @@ L97-97 verbatim
variable (H : CollaredSphereHomotopy n)


-- @@ L99-101 verbatim
/-- Horizontal coordinates of the whole space-time sphere map. -/
def horizontal (v : A) : F :=
  initCLM n (H.sphere v : E)


-- @@ L103-104 verbatim
lemma contDiff_horizontal : ContDiff ℝ ∞ H.horizontal :=
  (initCLM n).contDiff.comp H.smooth


-- @@ L106-113 verbatim
private lemma contDiff_spaceTimeSlice (t : ℝ) :
    ContDiff ℝ ∞ (fun x : E => spaceTime x t) := by
  have heq : (fun x : E => spaceTime x t) =
      fun x => embedCLM (n + 1) x + t • eLast (n + 1) := by
    funext x
    exact spaceTime_eq_affine x t
  rw [heq]
  exact (embedCLM (n + 1)).contDiff.add contDiff_const


-- @@ L115-116 verbatim
/-- Incoming horizontal map. -/
def sourceHorizontal (x : E) : F := H.horizontal (spaceTime x 0)


-- @@ L118-119 verbatim
/-- Outgoing horizontal map. -/
def targetHorizontal (x : E) : F := H.horizontal (spaceTime x 1)


-- @@ L121-122 verbatim
lemma contDiff_sourceHorizontal : ContDiff ℝ ∞ H.sourceHorizontal := by
  exact H.contDiff_horizontal.comp (contDiff_spaceTimeSlice (n := n) 0)


-- @@ L124-125 verbatim
lemma contDiff_targetHorizontal : ContDiff ℝ ∞ H.targetHorizontal := by
  exact H.contDiff_horizontal.comp (contDiff_spaceTimeSlice (n := n) 1)


-- @@ L127-130 verbatim
lemma horizontal_collar_zero (x : E) {t : ℝ} (ht : t ≤ 1 / 4) :
    H.horizontal (spaceTime x t) = H.sourceHorizontal x := by
  simp only [horizontal, sourceHorizontal]
  rw [H.collar_zero x t ht]


-- @@ L132-135 verbatim
lemma horizontal_collar_one (x : E) {t : ℝ} (ht : 3 / 4 ≤ t) :
    H.horizontal (spaceTime x t) = H.targetHorizontal x := by
  simp only [horizontal, targetHorizontal]
  rw [H.collar_one x t ht]


-- @@ L137-174 verbatim
/-- A regular value of the joint horizontal map is regular for its incoming
slice, because the map is locally constant in the time direction there. -/
theorem isRegularValue_source {y : F} (hy : IsRegularValue H.horizontal y) :
    IsRegularValue H.sourceHorizontal y := by
  intro x hx
  let X : A := spaceTime x 0
  have hXt : vertC X = 0 := vertC_spaceTime x 0
  have hslab : ∀ X' : A, vertC X' < 1 / 4 →
      H.horizontal X' = H.sourceHorizontal (initCLM (n + 1) X') := by
    intro X' hX'
    calc
      H.horizontal X' = H.horizontal
          (spaceTime (initCLM (n + 1) X') (vertC X')) :=
        congrArg H.horizontal (spaceTime_init_vert X').symm
      _ = H.sourceHorizontal (initCLM (n + 1) X') :=
        H.horizontal_collar_zero _ (le_of_lt hX')
  have hval : H.horizontal X = y := by
    rw [hslab X (by rw [hXt]; norm_num), initCLM_spaceTime]
    exact hx
  have hsurj := hy X hval
  have hEv : H.horizontal =ᶠ[𝓝 X]
      fun X' => H.sourceHorizontal (initCLM (n + 1) X') :=
    Filter.eventuallyEq_of_mem
      ((isOpen_vert_lt (1 / 4)).mem_nhds
        (by rw [mem_setOf_eq, hXt]; norm_num))
      fun X' hX' => hslab X' hX'
  have hgd : HasFDerivAt H.sourceHorizontal
      (fderiv ℝ H.sourceHorizontal (initCLM (n + 1) X))
      (initCLM (n + 1) X) :=
    (H.contDiff_sourceHorizontal.differentiable infty_ne_zero _).hasFDerivAt
  have hfd : fderiv ℝ H.horizontal X =
      (fderiv ℝ H.sourceHorizontal (initCLM (n + 1) X)).comp
        (initCLM (n + 1)) := by
    rw [hEv.fderiv_eq]
    exact (hgd.comp X (initCLM (n + 1)).hasFDerivAt).fderiv
  rw [hfd, ContinuousLinearMap.coe_comp] at hsurj
  have hs := hsurj.of_comp
  simpa [X, initCLM_spaceTime] using hs


-- @@ L176-212 verbatim
/-- Outgoing counterpart of `isRegularValue_source`. -/
theorem isRegularValue_target {y : F} (hy : IsRegularValue H.horizontal y) :
    IsRegularValue H.targetHorizontal y := by
  intro x hx
  let X : A := spaceTime x 1
  have hXt : vertC X = 1 := vertC_spaceTime x 1
  have hslab : ∀ X' : A, 3 / 4 < vertC X' →
      H.horizontal X' = H.targetHorizontal (initCLM (n + 1) X') := by
    intro X' hX'
    calc
      H.horizontal X' = H.horizontal
          (spaceTime (initCLM (n + 1) X') (vertC X')) :=
        congrArg H.horizontal (spaceTime_init_vert X').symm
      _ = H.targetHorizontal (initCLM (n + 1) X') :=
        H.horizontal_collar_one _ (le_of_lt hX')
  have hval : H.horizontal X = y := by
    rw [hslab X (by rw [hXt]; norm_num), initCLM_spaceTime]
    exact hx
  have hsurj := hy X hval
  have hEv : H.horizontal =ᶠ[𝓝 X]
      fun X' => H.targetHorizontal (initCLM (n + 1) X') :=
    Filter.eventuallyEq_of_mem
      ((isOpen_lt_vert (3 / 4)).mem_nhds
        (by rw [mem_setOf_eq, hXt]; norm_num))
      fun X' hX' => hslab X' hX'
  have hgd : HasFDerivAt H.targetHorizontal
      (fderiv ℝ H.targetHorizontal (initCLM (n + 1) X))
      (initCLM (n + 1) X) :=
    (H.contDiff_targetHorizontal.differentiable infty_ne_zero _).hasFDerivAt
  have hfd : fderiv ℝ H.horizontal X =
      (fderiv ℝ H.targetHorizontal (initCLM (n + 1) X)).comp
        (initCLM (n + 1)) := by
    rw [hEv.fderiv_eq]
    exact (hgd.comp X (initCLM (n + 1)).hasFDerivAt).fderiv
  rw [hfd, ContinuousLinearMap.coe_comp] at hsurj
  have hs := hsurj.of_comp
  simpa [X, initCLM_spaceTime] using hs


-- @@ L214-231 verbatim
lemma sourceFiber_bounded {y : F} (hy0 : y ≠ 0) :
    Bornology.IsBounded {x : E | H.sourceHorizontal x - y = 0} := by
  obtain ⟨R, hR⟩ := H.exterior_south
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨max R 0, ?_⟩
  intro x hx
  rw [mem_closedBall, dist_zero_right]
  have hxy : H.sourceHorizontal x = y := sub_eq_zero.mp hx
  have hxR : ‖x‖ ≤ R := by
    by_contra hnot
    have hfar : R < ‖initCLM (n + 1) (spaceTime x 0)‖ := by
      rw [initCLM_spaceTime]
      exact lt_of_not_ge hnot
    have hsouth := hR (spaceTime x 0) hfar
    apply hy0
    rw [← hxy, sourceHorizontal, horizontal, hsouth, southPole_coe,
      map_neg, initCLM_eLast, neg_zero]
  exact hxR.trans (le_max_left _ _)


-- @@ L233-250 verbatim
lemma targetFiber_bounded {y : F} (hy0 : y ≠ 0) :
    Bornology.IsBounded {x : E | H.targetHorizontal x - y = 0} := by
  obtain ⟨R, hR⟩ := H.exterior_south
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨max R 0, ?_⟩
  intro x hx
  rw [mem_closedBall, dist_zero_right]
  have hxy : H.targetHorizontal x = y := sub_eq_zero.mp hx
  have hxR : ‖x‖ ≤ R := by
    by_contra hnot
    have hfar : R < ‖initCLM (n + 1) (spaceTime x 1)‖ := by
      rw [initCLM_spaceTime]
      exact lt_of_not_ge hnot
    have hsouth := hR (spaceTime x 1) hfar
    apply hy0
    rw [← hxy, targetHorizontal, horizontal, hsouth, southPole_coe,
      map_neg, initCLM_eLast, neg_zero]
  exact hxR.trans (le_max_left _ _)


-- @@ L252-261 verbatim
/-- Incoming framed level set induced by a regular horizontal value. -/
def sourceLevelSet (y : F) (hy0 : y ≠ 0)
    (hy : IsRegularValue H.horizontal y) : FramedLevelSet n where
  g x := H.sourceHorizontal x - y
  smooth := H.contDiff_sourceHorizontal.sub contDiff_const
  fiber_bounded := H.sourceFiber_bounded hy0
  regular := by
    intro x hx
    have hs := H.isRegularValue_source hy x (sub_eq_zero.mp hx)
    rwa [fderiv_sub_const]


-- @@ L263-272 verbatim
/-- Outgoing framed level set induced by the same regular value. -/
def targetLevelSet (y : F) (hy0 : y ≠ 0)
    (hy : IsRegularValue H.horizontal y) : FramedLevelSet n where
  g x := H.targetHorizontal x - y
  smooth := H.contDiff_targetHorizontal.sub contDiff_const
  fiber_bounded := H.targetFiber_bounded hy0
  regular := by
    intro x hx
    have hs := H.isRegularValue_target hy x (sub_eq_zero.mp hx)
    rwa [fderiv_sub_const]


-- @@ L274-281 verbatim
lemma vertical_ne_zero_of_horizontal_eq {v : A} {y : F}
    (hy : ‖y‖ < 1) (hv : H.horizontal v = y) :
    vertC (H.sphere v : E) ≠ 0 := by
  intro hz
  have hsplit := norm_sq_split (H.sphere v : E)
  rw [UnitSphere.norm_coe, show initCLM n (H.sphere v : E) = y from hv,
    hz] at hsplit
  nlinarith [norm_nonneg y]


-- @@ L283-295 verbatim
/-- Incoming north/south sheet label. -/
def sourceSign (y : F) (hy0 : y ≠ 0)
    (hreg : IsRegularValue H.horizontal y) (hy : ‖y‖ < 1) :
    FiberSign (H.sourceLevelSet y hy0 hreg) where
  toFun x := vertC (H.sphere (spaceTime x 0) : E)
  continuous := by
    exact (EuclideanSpace.proj (Fin.last n) (𝕜 := ℝ)).continuous.comp
      (H.smooth.continuous.comp
        (contDiff_spaceTimeSlice (n := n) 0).continuous)
  nonzero := by
    intro x hx
    apply H.vertical_ne_zero_of_horizontal_eq hy
    exact sub_eq_zero.mp hx


-- @@ L297-309 verbatim
/-- Outgoing north/south sheet label. -/
def targetSign (y : F) (hy0 : y ≠ 0)
    (hreg : IsRegularValue H.horizontal y) (hy : ‖y‖ < 1) :
    FiberSign (H.targetLevelSet y hy0 hreg) where
  toFun x := vertC (H.sphere (spaceTime x 1) : E)
  continuous := by
    exact (EuclideanSpace.proj (Fin.last n) (𝕜 := ℝ)).continuous.comp
      (H.smooth.continuous.comp
        (contDiff_spaceTimeSlice (n := n) 1).continuous)
  nonzero := by
    intro x hx
    apply H.vertical_ne_zero_of_horizontal_eq hy
    exact sub_eq_zero.mp hx


-- @@ L311-339 verbatim
/-- Package the collared sphere homotopy, at any nonzero small joint regular
value, into the downstream transverse PT contract. -/
def toPTTransverseHomotopyData (y : F) (hy0 : y ≠ 0)
    (hreg : IsRegularValue H.horizontal y) (hy : ‖y‖ < 1) :
    PTTransverseHomotopyData (H.sourceSign y hy0 hreg hy)
      (H.targetSign y hy0 hreg hy) where
  sphere := H.sphere
  smooth := H.smooth
  target := y
  target_ne_zero := hy0
  target_norm_lt_one := hy
  exterior_south := H.exterior_south
  regular := hreg
  horizontal_collar_zero := by
    intro x t ht
    exact congrArg (fun z : F => z - y) (H.horizontal_collar_zero x ht)
  horizontal_collar_one := by
    intro x t ht
    exact congrArg (fun z : F => z - y) (H.horizontal_collar_one x ht)
  vertical_collar_zero := by
    intro x t ht
    change vertC (H.sphere (spaceTime x t) : E) =
      vertC (H.sphere (spaceTime x 0) : E)
    rw [H.collar_zero x t ht]
  vertical_collar_one := by
    intro x t ht
    change vertC (H.sphere (spaceTime x t) : E) =
      vertC (H.sphere (spaceTime x 1) : E)
    rw [H.collar_one x t ht]


-- @@ L341-356 verbatim
/-- Relative Sard transversality: a collared sphere homotopy has a common
nonzero target of norm `< 1/8`, and therefore an actual signed framed
cobordism between the two induced signed endpoint presentations. -/
theorem exists_small_transverse_signedCobordism (hn : 0 < n) :
    ∃ (y : F) (hy0 : y ≠ 0)
      (hreg : IsRegularValue H.horizontal y) (hy : ‖y‖ < 1),
      0 < ‖y‖ ∧ ‖y‖ < 1 / 8 ∧
      Nonempty (SignedFramedLevelCobordism
        (H.sourceSign y hy0 hreg hy) (H.targetSign y hy0 hreg hy)) := by
  obtain ⟨y, hypos, hy8, -, hreg⟩ :=
    exists_small_regular_value hn H.contDiff_horizontal
  have hy0 : y ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hypos)
  have hy : ‖y‖ < 1 := hy8.trans (by norm_num)
  exact ⟨y, hy0, hreg, hy, hypos, hy8,
    PTTransverseHomotopyData.nonempty_signedFramedLevelCobordism
      (H.toPTTransverseHomotopyData y hy0 hreg hy)⟩


-- @@ L358-358 verbatim
end CollaredSphereHomotopy


-- @@ L360-360 verbatim
end Submission
