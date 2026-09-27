/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPeriodicPotential
public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderRectangular
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevCoefficient
import LeanPool.NavierStokesAndEuler.Euler.AnglePrimitiveMap
import LeanPool.NavierStokesAndEuler.Euler.ClassicalPressureCurl
import LeanPool.NavierStokesAndEuler.Euler.LpCylinderRectangularRegularity
public import LeanPool.NavierStokesAndEuler.Euler.CylinderTimeRegularity
public import LeanPool.NavierStokesAndEuler.Euler.AngleMeanZeroPrimitive
import LeanPool.NavierStokesAndEuler.Euler.CylinderAngleRepresentative
public import LeanPool.NavierStokesAndEuler.Euler.CylinderAnglePrimitive
public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderTranslation
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevBlocks
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevLinear


-- @@ L22-22 verbatim
/-! The literal periodic vector potential as an actual continuous cylinder L² path. -/


-- @@ L24-24 verbatim
section


-- @@ L26-26 verbatim
/-! Time differentiation of the actual normalized angular integral on the cylinder. -/


-- @@ L28-28 verbatim
section


-- @@ L30-30 verbatim
/-! Same-radius mixed-word and continuous-time estimates for the actual angular operator. -/


-- @@ L32-32 verbatim
@[expose] public section


-- @@ L34-34 verbatim
noncomputable section


-- @@ L36-36 verbatim
namespace EulerCylinderAnglePrimitive


-- @@ L38-39 verbatim
open Set MeasureTheory EulerLiftedGradientSpace EulerParameterWordGevrey EulerGevrey
  EulerLpCylinderTranslation

-- @@ L40-40 verbatim
open scoped ContDiff


-- @@ L42-42 verbatim
variable (P : ℝ) [Fact (0 < P)]


-- @@ L44-47 verbatim
theorem primitive_hasDerivWithinAt (s : Set ℝ) (t : ℝ) (u : ℝ → LiftL2 P)
    (ut : LiftL2 P) (hu : HasDerivWithinAt u ut s t) :
    HasDerivWithinAt (fun r => primitive P (u r)) (primitive P ut) s t :=
  (primitive P).hasFDerivAt.comp_hasDerivWithinAt t hu


-- @@ L49-51 verbatim
theorem primitive_mixed_translation (a : LiftTangent) (u : LiftL2 P) :
    primitive P (translate P a u) = translate P a (primitive P u) :=
  primitive_translation P _ u


-- @@ L53-53 verbatim
variable {X ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [Fintype ι]


-- @@ L55-59 verbatim
theorem primitive_block_bound (directions : ι → X) (q : ℕ)
    (f : X → LiftL2 P) (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : X) :
    block directions q (fun y => primitive P (f y)) n x ≤ P*block directions q f n x :=
  (block_comp_clm_le directions q (primitive P) f hf n x).trans
    (mul_le_mul_of_nonneg_right (primitive_norm P) (block_nonneg directions q f n x))


-- @@ L61-67 verbatim
theorem primitive_block_majorant (directions : ι → X) (q : ℕ)
    (f : X → LiftL2 P) (hf : ContDiff ℝ ∞ f) (R C : ℝ) (d : ℕ)
    (hb : ∀ n x, block directions q f n x ≤ C * majorant R d n) (n : ℕ) (x : X) :
    block directions q (fun y => primitive P (f y)) n x ≤ (P*C)*majorant R d n :=
  (primitive_block_bound P directions q f hf n x).trans
    ((mul_le_mul_of_nonneg_left (hb n x) (le_of_lt (Fact.out : 0 < P))).trans_eq
      (mul_assoc P C _).symm)


-- @@ L69-69 verbatim
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]


-- @@ L71-73 verbatim
/-- Cache the standard `NormedAddCommGroup C(K,LiftL2 P)` instance to shorten typeclass
synthesis. -/
local instance instCylinderAngleWordBounds1 : NormedAddCommGroup C(K,LiftL2 P) := inferInstance

-- @@ L74-75 verbatim
/-- Cache the standard `NormedSpace ℝ C(K,LiftL2 P)` instance to shorten typeclass synthesis. -/
local instance instCylinderAngleWordBounds2 : NormedSpace ℝ C(K,LiftL2 P) := inferInstance

-- @@ L76-79 verbatim
/-- Cache the standard `NormedAddCommGroup (C(K,LiftL2 P) →L[ℝ] C(K,LiftL2 P))` instance to
shorten typeclass synthesis. -/
local instance instCylinderAngleWordBounds3 : NormedAddCommGroup (C(K,LiftL2 P) →L[ℝ] C(K,LiftL2
    P)) := inferInstance

-- @@ L80-83 verbatim
/-- Cache the standard `NormedSpace ℝ (C(K,LiftL2 P) →L[ℝ] C(K,LiftL2 P))` instance to shorten
typeclass synthesis. -/
local instance instCylinderAngleWordBounds4 : NormedSpace ℝ (C(K,LiftL2 P) →L[ℝ] C(K,LiftL2 P)) :=
    inferInstance


-- @@ L85-87 verbatim
/-- Path primitive, given by `(primitive P).compLeftContinuous ℝ K`. -/
def pathPrimitive : C(K,LiftL2 P) →L[ℝ] C(K,LiftL2 P) :=
  (primitive P).compLeftContinuous ℝ K


-- @@ L89-91 verbatim
omit [CompactSpace K] in
@[simp] theorem pathPrimitive_apply (u : C(K, LiftL2 P)) (t : K) :
    pathPrimitive P u t = primitive P (u t) := rfl


-- @@ L93-100 verbatim
theorem pathPrimitive_norm : ‖pathPrimitive (K := K) P‖ ≤ P := by
  have hP : 0 ≤ P := le_of_lt (Fact.out : 0 < P)
  apply ContinuousLinearMap.opNorm_le_bound _ hP
  intro u
  apply (ContinuousMap.norm_le _ (mul_nonneg hP (norm_nonneg u))).mpr
  intro t
  exact ((primitive P).le_of_opNorm_le (primitive_norm P) (u t)).trans
    (mul_le_mul_of_nonneg_left (u.norm_coe_le_norm t) hP)


-- @@ L102-110 verbatim
/-- The angular operation preserves the same fixed base order and radius in the true time supremum.
-/
theorem pathPrimitive_block_bound (directions : ι → X) (q : ℕ)
    (f : X → C(K, LiftL2 P)) (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : X) :
    block directions q (fun y => pathPrimitive P (f y)) n x ≤ P*block directions q f n x := by
  have h := block_comp_clm_le (E := C(K,LiftL2 P)) (F := C(K,LiftL2 P))
    directions q (pathPrimitive (K := K) P) f hf n x
  have hn : ‖pathPrimitive (K := K) P‖ ≤ P := pathPrimitive_norm P
  exact h.trans (mul_le_mul_of_nonneg_right hn (block_nonneg directions q f n x))


-- @@ L112-118 verbatim
theorem pathPrimitive_block_majorant (directions : ι → X) (q : ℕ)
    (f : X → C(K, LiftL2 P)) (hf : ContDiff ℝ ∞ f) (R C : ℝ) (d : ℕ)
    (hb : ∀ n x, block directions q f n x ≤ C * majorant R d n) (n : ℕ) (x : X) :
    block directions q (fun y => pathPrimitive P (f y)) n x ≤ (P*C)*majorant R d n :=
  (pathPrimitive_block_bound P directions q f hf n x).trans
    ((mul_le_mul_of_nonneg_left (hb n x) (le_of_lt (Fact.out : 0 < P))).trans_eq
      (mul_assoc P C _).symm)


-- @@ L120-120 verbatim
end EulerCylinderAnglePrimitive


-- @@ L122-122 verbatim
end

-- @@ L123-123 verbatim
end


-- @@ L125-125 verbatim
end


-- @@ L127-127 verbatim
@[expose] public section


-- @@ L129-129 verbatim
noncomputable section


-- @@ L131-131 verbatim
namespace EulerCylinderAnglePrimitive


-- @@ L133-135 verbatim
open Set MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCylinderSmoothOrbit EulerLpCylinderTranslation EulerMetricTransport
  EulerVolterraConvolution

-- @@ L136-136 verbatim
open scoped ContDiff


-- @@ L138-139 verbatim
variable (P : ℝ) [Fact (0 < P)]
  {K : Type*} [TopologicalSpace K] [CompactSpace K]


-- @@ L141-146 verbatim
omit [CompactSpace K] in
theorem pathPrimitive_translation (p : C(K, LiftL2 P)) (a : LiftTangent) :
    pathPrimitive P (pathTranslate P a p) = pathTranslate P a (pathPrimitive P p) := by
  apply ContinuousMap.ext
  intro t
  exact primitive_mixed_translation P a (p t)


-- @@ L148-152 verbatim
theorem pathPrimitive_orbit_contDiff (p : C(K, LiftL2 P))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p)) :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (pathPrimitive P p)) := by
  simpa only [Function.comp_def, pathPrimitive_translation] using
    (pathPrimitive (K := K) P).contDiff.comp hp


-- @@ L154-162 verbatim
theorem primitive_sobolevPath (p : C(K, LiftL2 P))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p)) (q : ℕ) (t : K) :
    sobolevPath P q (pathPrimitive P p) (pathPrimitive_orbit_contDiff P p hp) t =
      sobolevPrimitive P q (sobolevPath P q p hp t) := by
  apply value_injective P
  change value P (sobolevPath P q (pathPrimitive P p) _ t) =
    primitive P (value P (sobolevPath P q p hp t))
  rw [sobolevPath_value, sobolevPath_value]
  rfl


-- @@ L164-178 verbatim
/-- The representative of the time-dependent L² primitive is the same explicit angular integral. -/
theorem pointField_primitive_formula (p : C(K, LiftL2 P))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
    (hmean : ∀ t y, (∫ s in (0 : ℝ)..P, pointField P p hp t (y,(s : AddCircle P)))=0)
    (t : K) (y : Vector3) (θ : ℝ) :
    pointField P (pathPrimitive P p) (pathPrimitive_orbit_contDiff P p hp) t (y,(θ : AddCircle P)) =
      EulerAngleMeanZeroPrimitive.primitive P
        (fun s => pointField P p hp t (y,(s : AddCircle P))) θ := by
  unfold pointField
  rw [primitive_sobolevPath P p hp 3 t]
  apply pointEvaluation_primitive_classical P (sobolevPath P 3 p hp t)
    (pointField P p hp t)
    (smoothField_continuous P _ (pointField_smooth P p hp t))
  · simpa only [sobolevPath_value] using pointField_ae P p hp t
  · exact hmean t


-- @@ L180-180 verbatim
section Time


-- @@ L182-185 verbatim
variable (T : ℝ) (hT : 0 ≤ T) (p f : C(Icc (0 : ℝ) T, LiftL2 P))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
  (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a f))
  (hd : ∀ t : Icc (0 : ℝ) T, HasDerivWithinAt (extendPath T hT p) (f t) (Icc (0 : ℝ) T) t)


-- @@ L187-191 verbatim
include hd in
theorem pathPrimitive_time_derivative (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (pathPrimitive P p)) (pathPrimitive P f t)
      (Icc (0 : ℝ) T) t :=
  primitive_hasDerivWithinAt P _ t (extendPath T hT p) (f t) (hd t)


-- @@ L193-209 verbatim
include hd in
/-- The literal primitive differentiates within the closed time interval at every angle. -/
theorem classicalPrimitive_time_derivative
    (hpm : ∀ t y, (∫ s in (0 : ℝ)..P, pointField P p hp t (y, (s : AddCircle P))) = 0)
    (hfm : ∀ t y, (∫ s in (0 : ℝ)..P, pointField P f hf t (y, (s : AddCircle P))) = 0)
    (t : Icc (0 : ℝ) T) (y : Vector3) (θ : ℝ) :
    HasDerivWithinAt (fun r => EulerAngleMeanZeroPrimitive.primitive P
        (fun s => pointField P p hp (projIcc 0 T hT r) (y,(s : AddCircle P))) θ)
      (EulerAngleMeanZeroPrimitive.primitive P
        (fun s => pointField P f hf t (y,(s : AddCircle P))) θ) (Icc (0 : ℝ) T) t := by
  have h := pointField_hasDerivWithinAt P T hT (pathPrimitive P p) (pathPrimitive P f)
    (pathPrimitive_orbit_contDiff P p hp) (pathPrimitive_orbit_contDiff P f hf)
    (pathPrimitive_time_derivative P T hT p f hd) t (y,(θ : AddCircle P))
  rw [pointField_primitive_formula P f hf hfm t y θ] at h
  apply h.congr_of_mem _ t.property
  intro r _
  exact (pointField_primitive_formula P p hp hpm (projIcc 0 T hT r) y θ).symm


-- @@ L211-211 verbatim
end Time

-- @@ L212-212 verbatim
end EulerCylinderAnglePrimitive


-- @@ L214-214 verbatim
end

-- @@ L215-215 verbatim
end


-- @@ L217-217 verbatim
end


-- @@ L219-219 verbatim
@[expose] public section


-- @@ L221-221 verbatim
noncomputable section


-- @@ L223-223 verbatim
namespace EulerCylinderPotential


-- @@ L225-228 verbatim
open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerMetricTransport EulerCylinderSmoothOrbit EulerLpCylinderTranslation
  EulerLpCylinderRectangular EulerCylinderAnglePrimitive EulerMeanCoefficients
  EulerPacketCrossProduct EulerParameterWordGevrey EulerGevrey

-- @@ L229-229 verbatim
open scoped ContDiff BoundedContinuousFunction


-- @@ L231-235 verbatim
variable (P : ℝ) [Fact (0 < P)]
  {K : Type*} [TopologicalSpace K] [CompactSpace K]
  (B : C(K, Space →ᵇ Space →L[ℝ] Space))
  (hB : ContDiff ℝ ∞ (translateCoefficientPath B))
  (p : C(K, LiftL2 P)) (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))


-- @@ L237-238 verbatim
/-- Potential path, given by `fullMultiplierMap P B (pathPrimitive P p)`. -/
def potentialPath : C(K,LiftL2 P) := fullMultiplierMap P B (pathPrimitive P p)


-- @@ L240-243 verbatim
include hB hp in
theorem potentialPath_orbit :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (potentialPath P B p)) :=
  product_orbit_contDiff P B hB (pathPrimitive P p) (pathPrimitive_orbit_contDiff P p hp)


-- @@ L245-248 verbatim
/-- Potential field, given by `pointField P (potentialPath P B p) (potentialPath_orbit P B hB p
hp) t`. -/
def potentialField (t : K) : LiftDomain P → Space :=
  pointField P (potentialPath P B p) (potentialPath_orbit P B hB p hp) t


-- @@ L250-257 verbatim
theorem potentialPath_ae (t : K) :
    (potentialPath P B p t : LiftDomain P → Space) =ᵐ[liftMeasure P]
      fun x => B t x.1 (pointField P (pathPrimitive P p) (pathPrimitive_orbit_contDiff P p hp) t x)
          := by
  filter_upwards [EulerLpOperatorField.full_ae (liftMeasure P) (fieldLift P (B t))
      (pathPrimitive P p t),
    pointField_ae P (pathPrimitive P p) (pathPrimitive_orbit_contDiff P p hp) t] with x hB hp
  exact hB.trans (congrArg (B t x.1) hp)


-- @@ L259-277 verbatim
/-- The canonical representative is the coefficient times the literal angular primitive. -/
theorem potentialField_formula
    (hmean : ∀ t y, (∫ s in (0 : ℝ)..P, pointField P p hp t (y, (s : AddCircle P))) = 0)
    (t : K) (y : Space) (θ : ℝ) :
    potentialField P B hB p hp t (y,(θ : AddCircle P)) =
      B t y (EulerAngleMeanZeroPrimitive.primitive P
        (fun s => pointField P p hp t (y,(s : AddCircle P))) θ) := by
  have he : potentialField P B hB p hp t = fun x =>
      B t x.1 (pointField P (pathPrimitive P p) (pathPrimitive_orbit_contDiff P p hp) t x) := by
    apply Measure.eq_of_ae_eq
      ((pointField_ae P (potentialPath P B p) (potentialPath_orbit P B hB p hp) t).symm.trans
        (potentialPath_ae P B p hp t))
    · exact smoothField_continuous P _ (pointField_smooth P _ _ t)
    · exact ((B t).continuous.comp continuous_fst).clm_apply
        (smoothField_continuous P _ (pointField_smooth P _ _ t))
  rw [he]
  change B t y (pointField P (pathPrimitive P p)
    (pathPrimitive_orbit_contDiff P p hp) t (y,(θ : AddCircle P))) = _
  rw [pointField_primitive_formula P p hp hmean t y θ]


-- @@ L279-289 verbatim
theorem potentialField_source_formula
    (hmean : ∀ t y, (∫ s in (0 : ℝ)..P, pointField P p hp t (y, (s : AddCircle P))) = 0)
    (m : K → Space → Space) (hBm : ∀ t y, B t y = potentialMultiplier (m t y))
    (t : K) (y : Space) (θ : ℝ) :
    potentialField P B hB p hp t (y,(θ : AddCircle P)) =
      EulerPacketAngularPotential.potential P (m t y)
        (fun s => pointField P p hp t (y,(s : AddCircle P))) θ := by
  rw [potentialField_formula P B hB p hp hmean t y θ, hBm]
  exact EulerAngleMeanZeroPrimitive.primitive_map _ P _
    ((smoothField_continuous P _ (pointField_smooth P p hp t)).comp
      (continuous_const.prodMk (AddCircle.continuous_mk' P))) θ


-- @@ L291-308 verbatim
/-- The L² construction is the same actual field used in the compact Piola construction. -/
theorem potentialField_eq_periodic
    (hmean : ∀ t y, (∫ s in (0 : ℝ)..P, pointField P p hp t (y, (s : AddCircle P))) = 0)
    (m : K → Space → Space) (hBm : ∀ t y, B t y = potentialMultiplier (m t y))
    (t : K) :
    potentialField P B hB p hp t = EulerPacketPeriodicPotential.field P (m t) (pointField P p hp t)
        := by
  funext x
  obtain ⟨θ,hθ⟩ := QuotientAddGroup.mk_surjective x.2
  have hx : x=(x.1,(θ : AddCircle P)) := by
    apply Prod.ext
    · rfl
    · exact hθ.symm
  rw [hx, potentialField_source_formula P B hB p hp hmean m hBm t x.1 θ]
  have h := EulerPacketPeriodicPotential.field_cover P (m t) (pointField P p hp t)
    (smoothField_continuous P _ (pointField_smooth P p hp t)) (hmean t) (x.1,θ)
  simpa only [coveringMap, EulerPacketPiola.coveringPotential, localFieldLift,
    Prod.fst_zero, Prod.snd_zero, zero_add] using h.symm


-- @@ L310-329 verbatim
include hB hp in
/-- Angular integration and multiplication retain the input radius and external shift. -/
theorem potentialPath_block_bound {ι : Type*} [Fintype ι]
    (directions : ι → LiftTangent) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
    (Rc C R D : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hR : sobolevCoefficientRadius ι Rc ≤ R)
    (hbB : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath B) a‖ ≤ C * majorant Rc 0 n)
    (d : ℕ) (hbp : ∀ n, block directions q (fun a : LiftTangent => pathTranslate P a p) n 0 ≤
      D*majorant R d n) (n : ℕ) :
    block directions q (fun a : LiftTangent => pathTranslate P a (potentialPath P B p)) n 0 ≤
      (3*sobolevCoefficientAmplitude ι q Rc C*(P*D))*majorant R d n := by
  apply product_orbit_block_bound P B hB directions hd q (pathPrimitive P p)
    (pathPrimitive_orbit_contDiff P p hp) Rc C R (P*D) hRc hC
    (mul_nonneg (le_of_lt (Fact.out : 0 < P)) hD) hR hbB d _ n
  intro j
  have h := pathPrimitive_block_bound P directions q
    (fun a : LiftTangent => pathTranslate P a p) hp j 0
  simp only [pathPrimitive_translation] at h
  exact h.trans ((mul_le_mul_of_nonneg_left (hbp j) (le_of_lt (Fact.out : 0 < P))).trans_eq
    (mul_assoc P D _).symm)


-- @@ L331-331 verbatim
end EulerCylinderPotential
