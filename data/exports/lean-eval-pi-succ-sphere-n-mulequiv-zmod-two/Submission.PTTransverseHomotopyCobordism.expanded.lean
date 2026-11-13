import Mathlib
import Submission.EndpointPTCutoffExistence


-- @@ L4-23 verbatim
/-!
# A transverse PT homotopy produces a signed framed cobordism

This file isolates the differential-topological output needed from parametric
transversality.  Suppose that a jointly smooth sphere-valued map on space-time
is collar-flat at its two ends and is the south pole outside a spatially bounded
region.  If a nonzero horizontal value `y`, of norm less than one, is regular for
the whole space-time map, then the equation

`initCLM n (Phi v) - y = 0`

is an actual framed level cobordism.  The last sphere coordinate is a continuous
nonvanishing sign on its zero fiber.  Its positive and negative pieces are
exactly the inverse images of `northPoint y` and `southPointOf y`.

Thus callers do not have to postulate a `SignedFramedLevelCobordism`: after
producing the transverse collar-flat PT homotopy and a common regular value, the
structure is constructed here, including spatial boundedness, regularity, both
collars, and the sign field.
-/


-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-27 verbatim
namespace Submission


-- @@ L29-29 verbatim
open Set Function Metric

-- @@ L30-30 verbatim
open scoped Topology RealInnerProductSpace ContDiff


-- @@ L32-32 verbatim
variable {n : ℕ}


-- @@ L34-34 verbatim
local notation "A" => EuclideanSpace ℝ (Fin (n + 1 + 1))

-- @@ L35-35 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L36-36 verbatim
local notation "F" => EuclideanSpace ℝ (Fin n)


-- @@ L38-75 verbatim
/-- The precise analytic output required from a transverse PT homotopy.

The target value is required to be nonzero because the map is the south pole at
spatial infinity, whose horizontal projection is zero.  This is exactly what
makes the selected horizontal fiber spatially bounded.  The collar equations
also record endpoint framing and endpoint sign *exactly*, rather than merely up
to equality of their zero sets. -/
structure PTTransverseHomotopyData
    {X₀ X₁ : FramedLevelSet n} (S₀ : FiberSign X₀) (S₁ : FiberSign X₁) where
  /-- The sphere-valued space-time homotopy, extended over all real times. -/
  sphere : A → UnitSphere E
  /-- Joint smoothness of its ambient-vector representative. -/
  smooth : ContDiff ℝ ∞ fun v => (sphere v : E)
  /-- The common horizontal value selected by parametric transversality. -/
  target : F
  /-- The selected value avoids the horizontal projection of the south pole. -/
  target_ne_zero : target ≠ 0
  /-- The two sphere points over the target have nonzero last coordinate. -/
  target_norm_lt_one : ‖target‖ < 1
  /-- Outside a spatial ball the homotopy is identically the south pole. -/
  exterior_south : ∃ R : ℝ, ∀ v : A,
    R < ‖initCLM (n + 1) v‖ → sphere v = southPole n
  /-- The target is regular for the joint horizontal space-time map. -/
  regular : ∀ v : A, initCLM n (sphere v : E) = target →
    Function.Surjective
      (fderiv ℝ (fun q => initCLM n (sphere q : E)) v)
  /-- Exact incoming framing collar. -/
  horizontal_collar_zero : ∀ x : E, ∀ t : ℝ, t ≤ 1 / 4 →
    initCLM n (sphere (spaceTime x t) : E) - target = X₀.g x
  /-- Exact outgoing framing collar. -/
  horizontal_collar_one : ∀ x : E, ∀ t : ℝ, 3 / 4 ≤ t →
    initCLM n (sphere (spaceTime x t) : E) - target = X₁.g x
  /-- Exact incoming sign collar. -/
  vertical_collar_zero : ∀ x : E, ∀ t : ℝ, t ≤ 1 / 4 →
    vertC (sphere (spaceTime x t) : E) = S₀ x
  /-- Exact outgoing sign collar. -/
  vertical_collar_one : ∀ x : E, ∀ t : ℝ, 3 / 4 ≤ t →
    vertC (sphere (spaceTime x t) : E) = S₁ x


-- @@ L77-77 verbatim
namespace PTTransverseHomotopyData


-- @@ L79-80 verbatim
variable {X₀ X₁ : FramedLevelSet n} {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}
  (D : PTTransverseHomotopyData S₀ S₁)


-- @@ L82-84 verbatim
/-- The regular horizontal level equation cut out by the sphere homotopy. -/
def levelMap (v : A) : F :=
  initCLM n (D.sphere v : E) - D.target


-- @@ L86-88 verbatim
/-- The north/south label supplied by the last sphere coordinate. -/
def vertical (v : A) : ℝ :=
  vertC (D.sphere v : E)


-- @@ L90-91 verbatim
lemma contDiff_levelMap : ContDiff ℝ ∞ D.levelMap := by
  exact ((initCLM n).contDiff.comp D.smooth).sub contDiff_const


-- @@ L93-94 verbatim
lemma contDiff_vertical : ContDiff ℝ ∞ D.vertical := by
  exact contDiff_vertC.comp D.smooth


-- @@ L96-97 verbatim
lemma continuous_vertical : Continuous D.vertical :=
  D.contDiff_vertical.continuous


-- @@ L99-101 verbatim
lemma levelMap_eq_zero_iff (v : A) :
    D.levelMap v = 0 ↔ initCLM n (D.sphere v : E) = D.target := by
  exact sub_eq_zero


-- @@ L103-123 verbatim
/-- A zero of the horizontal level equation cannot escape to spatial infinity.
This is where both `target_ne_zero` and the exterior south-pole condition are
used. -/
lemma spatial_bounded_levelMap :
    ∃ R : ℝ, ∀ v : A, D.levelMap v = 0 → ‖initCLM (n + 1) v‖ ≤ R := by
  obtain ⟨R, hR⟩ := D.exterior_south
  refine ⟨R, ?_⟩
  intro v hv
  by_contra hout
  have hfar : R < ‖initCLM (n + 1) v‖ := lt_of_not_ge hout
  have hsouth : D.sphere v = southPole n := hR v hfar
  have hhoriz : initCLM n (D.sphere v : E) = 0 := by
    have hsouth' := congrArg Subtype.val hsouth
    rw [hsouth']
    rw [show ((southPole n : UnitSphere E) : E) = -eLast n from rfl,
      map_neg, initCLM_eLast]
    exact neg_zero
  have htarget : D.target = 0 := by
    rw [← (D.levelMap_eq_zero_iff v).mp hv]
    exact hhoriz
  exact D.target_ne_zero htarget


-- @@ L125-133 verbatim
/-- Regularity of the selected value is precisely regularity of the shifted
level equation. -/
lemma regular_levelMap (v : A) (hv : D.levelMap v = 0) :
    Function.Surjective (fderiv ℝ D.levelMap v) := by
  have hreg := D.regular v ((D.levelMap_eq_zero_iff v).mp hv)
  have hfd : fderiv ℝ D.levelMap v =
      fderiv ℝ (fun q => initCLM n (D.sphere q : E)) v := by
    exact fderiv_sub_const D.target
  rwa [hfd]


-- @@ L135-146 verbatim
/-- On the selected horizontal fiber the last coordinate is nonzero.  This is
derived from the unit-sphere equation and `‖target‖ < 1`; it is not an additional
sign assumption. -/
lemma vertical_ne_zero_of_levelMap_eq_zero (v : A)
    (hv : D.levelMap v = 0) : D.vertical v ≠ 0 := by
  intro hz
  have hsplit := norm_sq_split (D.sphere v : E)
  have hhoriz := (D.levelMap_eq_zero_iff v).mp hv
  change vertC (D.sphere v : E) = 0 at hz
  rw [UnitSphere.norm_coe, hhoriz, hz] at hsplit
  have hnorm0 : 0 ≤ ‖D.target‖ := norm_nonneg _
  nlinarith [D.target_norm_lt_one]


-- @@ L148-157 verbatim
/-- The actual framed cobordism cut out by the transverse horizontal value. -/
def toFramedLevelCobordism : FramedLevelCobordism n where
  X₀ := X₀
  X₁ := X₁
  G := D.levelMap
  smooth := D.contDiff_levelMap
  spatial_bounded := D.spatial_bounded_levelMap
  regular := D.regular_levelMap
  collar_zero := D.horizontal_collar_zero
  collar_one := D.horizontal_collar_one


-- @@ L159-160 verbatim
@[simp] theorem toFramedLevelCobordism_G (v : A) :
    D.toFramedLevelCobordism.G v = D.levelMap v := rfl


-- @@ L162-171 verbatim
/-- The signed framed cobordism obtained from the last-coordinate sheet label. -/
def toSignedFramedLevelCobordism : SignedFramedLevelCobordism S₀ S₁ where
  cobordism := D.toFramedLevelCobordism
  source_eq := rfl
  target_eq := rfl
  toFun := D.vertical
  continuous := D.continuous_vertical
  nonzero := D.vertical_ne_zero_of_levelMap_eq_zero
  collar_zero := D.vertical_collar_zero
  collar_one := D.vertical_collar_one


-- @@ L173-174 verbatim
@[simp] theorem toSignedFramedLevelCobordism_apply (v : A) :
    D.toSignedFramedLevelCobordism v = D.vertical v := rfl


-- @@ L176-181 verbatim
/-- Public existence form: once the transverse PT data is supplied, no further
cobordism existence principle is needed. -/
theorem nonempty_signedFramedLevelCobordism
    (D : PTTransverseHomotopyData S₀ S₁) :
    Nonempty (SignedFramedLevelCobordism S₀ S₁) :=
  ⟨toSignedFramedLevelCobordism D⟩


-- @@ L183-183 verbatim
/-! ## Exact north/south fibers -/


-- @@ L185-208 verbatim
/-- The positive part of the selected horizontal fiber is exactly the inverse
image of the northern sphere point over the chosen target. -/
theorem sphere_eq_northPoint_iff (v : A) :
    (D.sphere v : E) = northPoint D.target ↔
      D.levelMap v = 0 ∧ 0 < D.vertical v := by
  constructor
  · intro hnorth
    constructor
    · apply (D.levelMap_eq_zero_iff v).mpr
      rw [hnorth, initCLM_northPoint]
    · change 0 < vertC (D.sphere v : E)
      rw [hnorth]
      exact vertC_northPoint_pos D.target_norm_lt_one
  · rintro ⟨hlevel, hpos⟩
    have hinit := (D.levelMap_eq_zero_iff v).mp hlevel
    have hsheets :=
      (init_eq_iff (UnitSphere.norm_coe (D.sphere v)) D.target).mp hinit
    rcases hsheets with hnorth | hsouth
    · exact hnorth
    · have hneg : D.vertical v < 0 := by
        change vertC (D.sphere v : E) < 0
        rw [hsouth]
        exact vertC_southPointOf_neg D.target_norm_lt_one
      linarith


-- @@ L210-233 verbatim
/-- The negative part is exactly the inverse image of the southern sphere point
over the same horizontal target. -/
theorem sphere_eq_southPoint_iff (v : A) :
    (D.sphere v : E) = southPointOf D.target ↔
      D.levelMap v = 0 ∧ D.vertical v < 0 := by
  constructor
  · intro hsouth
    constructor
    · apply (D.levelMap_eq_zero_iff v).mpr
      rw [hsouth, initCLM_southPointOf]
    · change vertC (D.sphere v : E) < 0
      rw [hsouth]
      exact vertC_southPointOf_neg D.target_norm_lt_one
  · rintro ⟨hlevel, hneg⟩
    have hinit := (D.levelMap_eq_zero_iff v).mp hlevel
    have hsheets :=
      (init_eq_iff (UnitSphere.norm_coe (D.sphere v)) D.target).mp hinit
    rcases hsheets with hnorth | hsouth
    · have hpos : 0 < D.vertical v := by
        change 0 < vertC (D.sphere v : E)
        rw [hnorth]
        exact vertC_northPoint_pos D.target_norm_lt_one
      linarith
    · exact hsouth


-- @@ L235-241 verbatim
/-- Set-level exactness of the positive/northern cobordism fiber. -/
theorem northFiber_eq_positiveFiber :
    {v : A | (D.sphere v : E) = northPoint D.target} =
      D.toSignedFramedLevelCobordism.positiveFiber := by
  ext v
  rw [mem_setOf_eq, D.sphere_eq_northPoint_iff]
  rfl


-- @@ L243-250 verbatim
/-- Set-level exactness of the negative/southern cobordism fiber. -/
theorem southFiber_eq_negativeFiber :
    {v : A | (D.sphere v : E) = southPointOf D.target} =
      {v : A | D.toSignedFramedLevelCobordism.cobordism.G v = 0 ∧
        D.toSignedFramedLevelCobordism v < 0} := by
  ext v
  rw [mem_setOf_eq, mem_setOf_eq, D.sphere_eq_southPoint_iff]
  rfl


-- @@ L252-264 verbatim
/-- The incoming positive fiber is the incoming north-point inverse image. -/
theorem source_northFiber_eq_positivePart :
    {x : E | (D.sphere (spaceTime x 0) : E) = northPoint D.target} =
      S₀.positivePart := by
  ext x
  rw [mem_setOf_eq, D.sphere_eq_northPoint_iff]
  change
    (initCLM n (D.sphere (spaceTime x 0) : E) - D.target = 0 ∧
      0 < vertC (D.sphere (spaceTime x 0) : E)) ↔
      X₀.g x = 0 ∧ 0 < S₀ x
  rw [
    D.horizontal_collar_zero x 0 (by norm_num),
    D.vertical_collar_zero x 0 (by norm_num)]


-- @@ L266-278 verbatim
/-- The outgoing positive fiber is the outgoing north-point inverse image. -/
theorem target_northFiber_eq_positivePart :
    {x : E | (D.sphere (spaceTime x 1) : E) = northPoint D.target} =
      S₁.positivePart := by
  ext x
  rw [mem_setOf_eq, D.sphere_eq_northPoint_iff]
  change
    (initCLM n (D.sphere (spaceTime x 1) : E) - D.target = 0 ∧
      0 < vertC (D.sphere (spaceTime x 1) : E)) ↔
      X₁.g x = 0 ∧ 0 < S₁ x
  rw [
    D.horizontal_collar_one x 1 (by norm_num),
    D.vertical_collar_one x 1 (by norm_num)]


-- @@ L280-280 verbatim
end PTTransverseHomotopyData


-- @@ L282-282 verbatim
end Submission
