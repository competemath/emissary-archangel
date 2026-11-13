import Mathlib
import Submission.BridgeCobordism


-- @@ L4-15 verbatim
/-!
# A nonvanishing sign label on framed level-set fibers

The forward bridge has two sheets over a horizontal regular value.  The sheet
belonging to the original Pontryagin preimage is distinguished by the sign of the
last sphere coordinate.  This file packages that distinction without building a
general theory of labelled manifolds.

The key reusable fact is elementary but important: a continuous path in the fiber
cannot change the sign of a label which is nonzero everywhere on the fiber.  It is
proved directly by the intermediate value theorem.
-/


-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
namespace Submission


-- @@ L21-21 verbatim
open Set Function Metric Topology.Homotopy

-- @@ L22-22 verbatim
open scoped Topology unitInterval RealInnerProductSpace


-- @@ L24-24 verbatim
variable {n : ℕ}


-- @@ L26-26 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L28-33 verbatim
/-- A continuous real label which does not vanish on the zero fiber of a framed
level-set presentation. -/
structure FiberSign (X : FramedLevelSet n) where
  toFun : E → ℝ
  continuous : Continuous toFun
  nonzero : ∀ x, x ∈ X.fiber → toFun x ≠ 0


-- @@ L35-35 verbatim
namespace FiberSign


-- @@ L37-37 verbatim
variable {X : FramedLevelSet n} (S : FiberSign X)


-- @@ L39-39 verbatim
instance : CoeFun (FiberSign X) fun _ => E → ℝ := ⟨FiberSign.toFun⟩


-- @@ L41-42 verbatim
/-- The positively labelled union of fiber components. -/
def positivePart : Set E := {x | x ∈ X.fiber ∧ 0 < S x}


-- @@ L44-45 verbatim
theorem positivePart_subset_fiber : S.positivePart ⊆ X.fiber :=
  fun _ hx => hx.1


-- @@ L47-70 verbatim
/-- A continuous path contained in the fiber has the same label sign at its two
ends. -/
theorem pos_iff_of_path (γ : C(I, E)) (hγ : ∀ t, γ t ∈ X.fiber) :
    0 < S (γ 0) ↔ 0 < S (γ 1) := by
  have hcont : Continuous fun t : I => S (γ t) := S.continuous.comp γ.continuous
  constructor
  · intro h0
    by_contra h1
    have h1neg : S (γ 1) < 0 := by
      have hle : S (γ 1) ≤ 0 := le_of_not_gt h1
      exact lt_of_le_of_ne hle (S.nonzero (γ 1) (hγ 1))
    have hz : (0 : ℝ) ∈ Icc (S (γ 1)) (S (γ 0)) := ⟨h1neg.le, h0.le⟩
    obtain ⟨t, -, ht⟩ :=
      intermediate_value_Icc' (show (0 : I) ≤ 1 by simp) hcont.continuousOn hz
    exact S.nonzero (γ t) (hγ t) ht
  · intro h1
    by_contra h0
    have h0neg : S (γ 0) < 0 := by
      have hle : S (γ 0) ≤ 0 := le_of_not_gt h0
      exact lt_of_le_of_ne hle (S.nonzero (γ 0) (hγ 0))
    have hz : (0 : ℝ) ∈ Icc (S (γ 0)) (S (γ 1)) := ⟨h0neg.le, h1.le⟩
    obtain ⟨t, -, ht⟩ :=
      intermediate_value_Icc (show (0 : I) ≤ 1 by simp) hcont.continuousOn hz
    exact S.nonzero (γ t) (hγ t) ht


-- @@ L72-72 verbatim
end FiberSign


-- @@ L74-74 verbatim
/-! ## Signed framed level cobordisms -/


-- @@ L76-88 verbatim
/-- A framed level cobordism together with a continuous nonvanishing extension of
the two end labels.  This is the precise extra datum needed to apply the Morse-event
argument to only the positive (northern) union of components. -/
structure SignedFramedLevelCobordism
    {X₀ X₁ : FramedLevelSet n} (S₀ : FiberSign X₀) (S₁ : FiberSign X₁) where
  cobordism : FramedLevelCobordism n
  source_eq : cobordism.X₀ = X₀
  target_eq : cobordism.X₁ = X₁
  toFun : EuclideanSpace ℝ (Fin (n + 1 + 1)) → ℝ
  continuous : Continuous toFun
  nonzero : ∀ v, cobordism.G v = 0 → toFun v ≠ 0
  collar_zero : ∀ x t, t ≤ 1 / 4 → toFun (spaceTime x t) = S₀ x
  collar_one : ∀ x t, 3 / 4 ≤ t → toFun (spaceTime x t) = S₁ x


-- @@ L90-90 verbatim
namespace SignedFramedLevelCobordism


-- @@ L92-93 verbatim
variable {X₀ X₁ : FramedLevelSet n} {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}
  (C : SignedFramedLevelCobordism S₀ S₁)


-- @@ L95-97 verbatim
instance : CoeFun (SignedFramedLevelCobordism S₀ S₁) fun _ =>
    EuclideanSpace ℝ (Fin (n + 1 + 1)) → ℝ :=
  ⟨SignedFramedLevelCobordism.toFun⟩


-- @@ L99-101 verbatim
/-- The positive union of components of the cobordism zero fiber. -/
def positiveFiber : Set (EuclideanSpace ℝ (Fin (n + 1 + 1))) :=
  {v | C.cobordism.G v = 0 ∧ 0 < C v}


-- @@ L103-105 verbatim
theorem positiveFiber_subset_zeroFiber :
    C.positiveFiber ⊆ {v | C.cobordism.G v = 0} :=
  fun _ hv => hv.1


-- @@ L107-115 verbatim
/-- The label underlying the gluing of two signed cobordisms.  It uses exactly the
same triple-speed reparametrizations as `FramedLevelCobordism.trans`. -/
def transFun
    {X₂ : FramedLevelSet n} {S₂ : FiberSign X₂}
    (C₁ : SignedFramedLevelCobordism S₀ S₁)
    (C₂ : SignedFramedLevelCobordism S₁ S₂) :
    EuclideanSpace ℝ (Fin (n + 1 + 1)) → ℝ :=
  fun v => if vertC v < 1 / 2 then C₁ (reparamMap n 3 (-(1 / 2)) v)
    else C₂ (reparamMap n 3 (-(3 / 2)) v)


-- @@ L117-137 verbatim
lemma transFun_middle
    {X₂ : FramedLevelSet n} {S₂ : FiberSign X₂}
    (C₁ : SignedFramedLevelCobordism S₀ S₁)
    (C₂ : SignedFramedLevelCobordism S₁ S₂)
    {v : EuclideanSpace ℝ (Fin (n + 1 + 1))}
    (h1 : 5 / 12 < vertC v) (h2 : vertC v < 7 / 12) :
    transFun C₁ C₂ v = S₁ (initCLM (n + 1) v) := by
  rw [transFun]
  by_cases hv : vertC v < 1 / 2
  · rw [if_pos hv]
    have hcol := C₁.collar_one (initCLM (n + 1) v)
      (3 * vertC v + -(1 / 2)) (by linarith)
    change C₁ (spaceTime (initCLM (n + 1) v)
      (3 * vertC v + -(1 / 2))) = S₁ (initCLM (n + 1) v)
    exact hcol
  · rw [if_neg hv]
    have hcol := C₂.collar_zero (initCLM (n + 1) v)
      (3 * vertC v + -(3 / 2)) (by linarith)
    change C₂ (spaceTime (initCLM (n + 1) v)
      (3 * vertC v + -(3 / 2))) = S₁ (initCLM (n + 1) v)
    exact hcol


-- @@ L139-160 verbatim
lemma continuous_transFun
    {X₂ : FramedLevelSet n} {S₂ : FiberSign X₂}
    (C₁ : SignedFramedLevelCobordism S₀ S₁)
    (C₂ : SignedFramedLevelCobordism S₁ S₂) :
    Continuous (transFun C₁ C₂) := by
  rw [continuous_iff_continuousAt]
  intro v
  rcases lt_trichotomy (vertC v) (1 / 2) with hv | hv | hv
  · refine (C₁.continuous.comp
      (contDiff_reparamMap 3 (-(1 / 2))).continuous).continuousAt.congr_of_eventuallyEq ?_
    exact Filter.eventuallyEq_of_mem ((isOpen_vert_lt (1 / 2)).mem_nhds hv)
      fun w hw => if_pos hw
  · refine (S₁.continuous.comp (initCLM (n + 1)).continuous).continuousAt.congr_of_eventuallyEq ?_
    refine Filter.eventuallyEq_of_mem
      ((isOpen_vert_between (5 / 12) (7 / 12)).mem_nhds
        ⟨by rw [hv]; norm_num, by rw [hv]; norm_num⟩) ?_
    intro w hw
    exact transFun_middle C₁ C₂ hw.1 hw.2
  · refine (C₂.continuous.comp
      (contDiff_reparamMap 3 (-(3 / 2))).continuous).continuousAt.congr_of_eventuallyEq ?_
    exact Filter.eventuallyEq_of_mem ((isOpen_lt_vert (1 / 2)).mem_nhds hv)
      fun w hw => if_neg (not_lt.mpr (le_of_lt hw))


-- @@ L162-197 verbatim
/-- Gluing of signed cobordisms preserves the nonvanishing label and its end
restrictions. -/
def trans
    {X₂ : FramedLevelSet n} {S₂ : FiberSign X₂}
    (C₁ : SignedFramedLevelCobordism S₀ S₁)
    (C₂ : SignedFramedLevelCobordism S₁ S₂) :
    SignedFramedLevelCobordism S₀ S₂ where
  cobordism := C₁.cobordism.trans C₂.cobordism
    (C₁.target_eq.trans C₂.source_eq.symm)
  source_eq := C₁.source_eq
  target_eq := C₂.target_eq
  toFun := transFun C₁ C₂
  continuous := continuous_transFun C₁ C₂
  nonzero := by
    intro v hv
    by_cases hlt : vertC v < 1 / 2
    · rw [transFun, if_pos hlt]
      apply C₁.nonzero (reparamMap n 3 (-(1 / 2)) v)
      change Submission.transFun C₁.cobordism C₂.cobordism v = 0 at hv
      rwa [Submission.transFun, if_pos hlt] at hv
    · rw [transFun, if_neg hlt]
      apply C₂.nonzero (reparamMap n 3 (-(3 / 2)) v)
      change Submission.transFun C₁.cobordism C₂.cobordism v = 0 at hv
      rwa [Submission.transFun, if_neg hlt] at hv
  collar_zero := by
    intro x t ht
    have hlt : t < 1 / 2 := by linarith
    rw [transFun, vertC_spaceTime, if_pos hlt, reparamMap,
      initCLM_spaceTime, vertC_spaceTime]
    exact C₁.collar_zero x (3 * t + -(1 / 2)) (by linarith)
  collar_one := by
    intro x t ht
    have hlt : ¬t < 1 / 2 := by linarith
    rw [transFun, vertC_spaceTime, if_neg hlt, reparamMap,
      initCLM_spaceTime, vertC_spaceTime]
    exact C₂.collar_one x (3 * t + -(3 / 2)) (by linarith)


-- @@ L199-199 verbatim
end SignedFramedLevelCobordism


-- @@ L201-201 verbatim
/-! ## The canonical sign on a bridge presentation -/


-- @@ L203-224 verbatim
/-- The last sphere coordinate labels the two sheets of any bridge level set at a
value of norm less than one. -/
def bridgeFiberSignOf
    {p : Ω^ (Fin (n + 1))
      (UnitSphere (EuclideanSpace ℝ (Fin (n + 1)))) (southPole n)}
    (a : Approximation p) (y : EuclideanSpace ℝ (Fin n))
    (hy0 : y ≠ 0) (hreg : IsRegularValue (bridgeHMapE a) y)
    (hylt : ‖y‖ < 1) : FiberSign (bridgeFLS a y hy0 hreg) where
  toFun x := vertC (nprep a (WithLp.ofLp x))
  continuous := by
    exact (EuclideanSpace.proj (Fin.last n) (𝕜 := ℝ)).continuous.comp
      ((contDiff_nprep a).continuous.comp
        (EuclideanSpace.equiv (Fin (n + 1)) ℝ).continuous)
  nonzero := by
    intro x hx hzero
    have hfib : bridgeHMapE a x = y := sub_eq_zero.mp hx
    have hsplit := norm_sq_split (nprep a (WithLp.ofLp x))
    have hinit : initCLM n (nprep a (WithLp.ofLp x)) = y := hfib
    rw [norm_nprep a, hinit, hzero] at hsplit
    norm_num at hsplit
    have hy0' := norm_nonneg y
    nlinarith


-- @@ L226-226 verbatim
namespace BridgeData


-- @@ L228-229 verbatim
variable {z : HomotopyGroup (Fin (n + 1))
    (UnitSphere (EuclideanSpace ℝ (Fin (n + 1)))) (southPole n)}


-- @@ L231-234 verbatim
/-- The canonical sheet label of a bridge level set: the last coordinate of the
plateaued sphere representative. -/
def fiberSign (B : BridgeData n z) : FiberSign B.fls :=
  bridgeFiberSignOf B.approx B.y B.y_ne_zero B.regular_y B.norm_y_lt_one


-- @@ L236-239 verbatim
@[simp]
theorem fiberSign_apply (B : BridgeData n z) (x : E) :
    B.fiberSign x = vertC (nprep B.approx (WithLp.ofLp x)) :=
  rfl


-- @@ L241-252 verbatim
/-- The positive part of the canonical bridge label is exactly the northern sheet. -/
theorem fiberSign_positivePart (B : BridgeData n z) :
    B.fiberSign.positivePart =
      {x | x ∈ B.fls.fiber ∧
        nprep B.approx (WithLp.ofLp x) = northPoint B.y} := by
  ext x
  simp only [FiberSign.positivePart, mem_setOf_eq, fiberSign_apply]
  constructor
  · rintro ⟨hx, hpos⟩
    exact ⟨hx, (B.mem_north_iff hx).mpr hpos⟩
  · rintro ⟨hx, hnorth⟩
    exact ⟨hx, (B.mem_north_iff hx).mp hnorth⟩


-- @@ L254-254 verbatim
end BridgeData


-- @@ L256-256 verbatim
end Submission
