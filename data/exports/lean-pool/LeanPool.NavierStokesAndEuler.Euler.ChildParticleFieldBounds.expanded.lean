/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothL2GevreyCalculus
import Mathlib.Algebra.Order.Star.Real
public import LeanPool.NavierStokesAndEuler.Euler.SmoothL2Gevrey
import LeanPool.NavierStokesAndEuler.Euler.GevreyProductLp
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder


-- @@ L14-17 verbatim
/-! The actual three fields in the chain rule for X(t,Y(t,a)) have
Gevrey L² bounds. The parent is controlled by its physical-label H⁶
norm, and Y preserves volume. The new radius is linear in the inner
radius, with only polynomial dependence on the parent and amplitudes. -/


-- @@ L19-19 verbatim
section


-- @@ L21-23 verbatim
/-! The classical label Sobolev norm also bounds the actual L² tensor
jets, so a parent satisfying (21) supplies every outer L² input needed
by the volume-preserving composition estimate. -/


-- @@ L25-25 verbatim
@[expose] public section


-- @@ L27-27 verbatim
noncomputable section


-- @@ L29-29 verbatim
namespace EulerLpTranslation.SmoothL2Field


-- @@ L31-33 verbatim
open MeasureTheory Filter Finset EulerSmoothLimit EulerMeanSmoothRepresentative
  EulerMeanClassicalWordBounds EulerParameterWordGevrey EulerPacketParentLabelBounds
  EulerGevreyProductLp

-- @@ L34-34 verbatim
open scoped ContDiff


-- @@ L36-57 verbatim
theorem norm_jetLp_le_wordSum (A : SmoothL2Field Space) (n : ℕ) :
    ‖A.jetLp n‖ ≤ wordSum direction (fun a : Space => translation a A.toLp) n 0 := by
  have he : representative A.toLp A.translation_contDiff = A.field :=
    representative_unique A.toLp A.translation_contDiff A.field A.smooth.continuous A.toLp_ae
  have ha (w : Fin n → Fin 3) :
      (ordinaryWord direction A.toLp w : Space → Space) =ᵐ[volume] wordDerivative direction A.field
          w := by
    simpa only [he] using ordinaryWord_ae direction A.toLp A.translation_contDiff w
  have hm (w : Fin n → Fin 3) : MemLp (wordDerivative direction A.field w) 2 volume :=
    (Lp.memLp (ordinaryWord direction A.toLp w)).ae_eq (ha w)
  let H : (Fin n → Fin 3) → Space → ℝ := fun w x => ‖wordDerivative direction A.field w x‖
  have hn (w : Fin n → Fin 3) : (eLpNorm (H w) 2 volume).toReal = ‖ordinaryWord direction A.toLp w‖
      := by
    rw [show H w = fun x => ‖wordDerivative direction A.field w x‖ from rfl,
      eLpNorm_norm _ (hm w).aestronglyMeasurable]
    rw [← eLpNorm_congr_ae (ha w),Lp.norm_def]
  have hb := (finite_domination volume (univ : Finset (Fin n → Fin 3)) (iteratedFDeriv ℝ n A.field)
    ((A.smooth.continuous_iteratedFDeriv (m := n) (by simp)).aestronglyMeasurable)
    H (fun w _ => (hm w).norm) (fun x => tensor_le_wordSum A.field n x)).2
  rw [norm_jetLp]
  simpa only [hn,wordSum,ordinaryWord,EulerMeanSolenoidal.translation,
    EulerLpTranslation.translation] using hb


-- @@ L59-65 verbatim
theorem norm_jetLp_le_classicalBlock (A : SmoothL2Field Space) (q n : ℕ) :
    ‖A.jetLp n‖ ≤ classicalBlockSize direction q A.toLp A.translation_contDiff n := by
  apply (norm_jetLp_le_wordSum A n).trans
  refine le_trans ?_ (le_of_eq
    (classicalBlockSize_eq direction q A.toLp A.translation_contDiff n).symm)
  unfold wordSum block
  exact sum_le_sum (fun w _ => norm_le_baseSize direction q _ 0)


-- @@ L67-71 verbatim
theorem hasJetBound_of_labelBound (A : SmoothL2Field Space) (K : ℝ)
    (h : HasLabelBound K A) : A.HasJetBound K K := by
  intro n
  exact (norm_jetLp_le_classicalBlock A 6 n).trans
    ((h n).trans_eq (by rw [pow_succ]; ring))


-- @@ L73-78 verbatim
theorem sup_bound_of_labelBound (A : SmoothL2Field Space) (K : ℝ)
    (h : HasLabelBound K A) (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n A.field x‖ ≤ (embeddingCost*K)*K^n*(n.factorial : ℝ)^2 := by
  have hb := field_tensor_gevrey A.toLp A.translation_contDiff A.field A.smooth.continuous A.toLp_ae
    6 (by norm_num) K K (source_block_bound A.toLp A.translation_contDiff K h) n x
  simpa only [EulerGevrey.majorant,Nat.add_zero,mul_assoc] using hb


-- @@ L80-80 verbatim
end EulerLpTranslation.SmoothL2Field


-- @@ L82-82 verbatim
end

-- @@ L83-83 verbatim
end


-- @@ L85-85 verbatim
end


-- @@ L87-87 verbatim
@[expose] public section


-- @@ L89-89 verbatim
noncomputable section


-- @@ L91-91 verbatim
namespace EulerChildParticleFieldBounds


-- @@ L93-94 verbatim
open MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerPacketParentLabelBounds EulerGevrey

-- @@ L95-95 verbatim
open scoped ContDiff


-- @@ L97-129 verbatim
/-- Data, collecting `parentDisplacement`, `parentVelocity`, `parentAcceleration`, `K`, `K_one`,
`parentDisplacement_bound` and their compatibility conditions. -/
structure Data where
  /-- Parent displacement of `Data`, of type `SmoothL2Field Space`. -/
  parentDisplacement : SmoothL2Field Space
  /-- Parent velocity of `Data`, of type `SmoothL2Field Space`. -/
  parentVelocity : SmoothL2Field Space
  /-- Parent acceleration of `Data`, of type `SmoothL2Field Space`. -/
  parentAcceleration : SmoothL2Field Space
  /-- K of `Data`, of type `ℝ`. -/
  K : ℝ
  K_one : 1 ≤ K
  parentDisplacement_bound : HasLabelBound K parentDisplacement
  parentVelocity_bound : HasLabelBound K parentVelocity
  parentAcceleration_bound : HasLabelBound K parentAcceleration
  /-- Displacement of `Data`, of type `SmoothL2Field Space`. -/
  displacement : SmoothL2Field Space
  /-- Velocity field of `Data`, of type `SmoothL2Field Space`. -/
  velocity : SmoothL2Field Space
  /-- Acceleration of `Data`, of type `SmoothL2Field Space`. -/
  acceleration : SmoothL2Field Space
  /-- Amp of `Data`, of type `ℝ`. -/
  amp : ℝ
  /-- Rad of `Data`, of type `ℝ`. -/
  rad : ℝ
  amp_one : 1 ≤ amp
  rad_one : 1 ≤ rad
  displacement_bound : displacement.HasJetBound amp rad
  velocity_bound : velocity.HasJetBound amp rad
  acceleration_bound : acceleration.HasJetBound amp rad
  displacement_sup : HasSupBound displacement.field amp rad
  velocity_sup : HasSupBound velocity.field amp rad
  volume_preserving : MeasurePreserving (fun x => x+displacement.field x) volume volume


-- @@ L131-131 verbatim
namespace Data


-- @@ L133-133 verbatim
variable (G : Data)


-- @@ L135-136 verbatim
/-- Inner, given by `x+G.displacement.field x`. -/
def inner (x : Space) : Space := x+G.displacement.field x

-- @@ L137-138 verbatim
/-- Composition radius, given by `(1+G.rad)*((1+G.amp)*s+2)`. -/
def compositionRadius (s : ℝ) : ℝ := (1+G.rad)*((1+G.amp)*s+2)

-- @@ L139-140 verbatim
/-- Radius, given by `G.compositionRadius (16*G.K)+G.rad`. -/
def radius : ℝ := G.compositionRadius (16*G.K)+G.rad

-- @@ L141-142 verbatim
/-- First amplitude, given by `(embeddingCost*G.K)*G.K`. -/
def firstAmplitude : ℝ := (embeddingCost*G.K)*G.K

-- @@ L143-144 verbatim
/-- Second amplitude, given by `G.firstAmplitude*(4*G.K)`. -/
def secondAmplitude : ℝ := G.firstAmplitude*(4*G.K)

-- @@ L145-146 verbatim
/-- Amplitude, given by `G.K+G.amp+9*G.firstAmplitude*G.amp+9*G.secondAmplitude*G.amp^2`. -/
def amplitude : ℝ := G.K+G.amp+9*G.firstAmplitude*G.amp+9*G.secondAmplitude*G.amp^2


-- @@ L148-148 verbatim
theorem K_nonneg : 0 ≤ G.K := le_trans zero_le_one G.K_one

-- @@ L149-149 verbatim
theorem amp_nonneg : 0 ≤ G.amp := le_trans zero_le_one G.amp_one

-- @@ L150-150 verbatim
theorem rad_nonneg : 0 ≤ G.rad := le_trans zero_le_one G.rad_one

-- @@ L151-155 verbatim
theorem compositionRadius_nonneg (s : ℝ) (hs : 0 ≤ s) : 0 ≤ G.compositionRadius s := by
  have := G.amp_nonneg
  have := G.rad_nonneg
  unfold compositionRadius
  positivity

-- @@ L156-157 verbatim
theorem radius_nonneg : 0 ≤ G.radius :=
  add_nonneg (G.compositionRadius_nonneg _ (mul_nonneg (by norm_num) G.K_nonneg)) G.rad_nonneg

-- @@ L158-159 verbatim
theorem rad_le_radius : G.rad ≤ G.radius :=
  le_add_of_nonneg_left (G.compositionRadius_nonneg _ (mul_nonneg (by norm_num) G.K_nonneg))

-- @@ L160-161 verbatim
theorem firstAmplitude_nonneg : 0 ≤ G.firstAmplitude :=
  mul_nonneg (mul_nonneg embeddingCost_nonneg G.K_nonneg) G.K_nonneg

-- @@ L162-163 verbatim
theorem secondAmplitude_nonneg : 0 ≤ G.secondAmplitude :=
  mul_nonneg G.firstAmplitude_nonneg (mul_nonneg (by norm_num) G.K_nonneg)

-- @@ L164-170 verbatim
theorem amplitude_nonneg : 0 ≤ G.amplitude := by
  have := G.K_nonneg
  have := G.amp_nonneg
  have := G.firstAmplitude_nonneg
  have := G.secondAmplitude_nonneg
  unfold amplitude
  positivity


-- @@ L172-182 verbatim
theorem compositionRadius_le_radius (s : ℝ) (hs : s ≤ 16 * G.K) : G.compositionRadius s ≤ G.radius
    :=
    by
  calc
    G.compositionRadius s ≤ G.compositionRadius (16*G.K) := by
      unfold compositionRadius
      exact mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hs (add_nonneg zero_le_one G.amp_nonneg)) (le_refl
            (2 : ℝ)))
        (add_nonneg zero_le_one G.rad_nonneg)
    _ ≤ G.radius := le_add_of_nonneg_right G.rad_nonneg


-- @@ L184-184 verbatim
theorem inner_smooth : ContDiff ℝ ∞ G.inner := contDiff_id.add G.displacement.smooth

-- @@ L185-188 verbatim
theorem inner_positive (n : ℕ) (hn : 0 < n) (x : Space) :
    ‖iteratedFDeriv ℝ n G.inner x‖ ≤ (1+G.amp)*(1+G.rad)^n*(n.factorial : ℝ)^2 :=
  positive_id_add_bound G.displacement.field G.displacement.smooth G.amp G.rad
    G.amp_nonneg G.rad_nonneg G.displacement_sup n hn x


-- @@ L190-194 verbatim
/-- Parent composed, constructed using `composeField`. -/
def parentComposed (U : SmoothL2Field Space) (hU : HasLabelBound G.K U) : SmoothL2Field Space :=
  composeField G.inner G.inner_smooth G.volume_preserving (1+G.amp) (1+G.rad)
    (by linarith [G.amp_nonneg]) (by linarith [G.rad_nonneg]) G.inner_positive
    U G.K G.K G.K_nonneg G.K_nonneg (hasJetBound_of_labelBound U G.K hU)


-- @@ L196-202 verbatim
theorem parentComposed_bound (U : SmoothL2Field Space) (hU : HasLabelBound G.K U) :
    (G.parentComposed U hU).HasJetBound G.K G.radius := by
  have h := composeField_bound G.inner G.inner_smooth G.volume_preserving (1+G.amp) (1+G.rad)
    (by linarith [G.amp_nonneg]) (by linarith [G.rad_nonneg]) G.inner_positive
    U G.K G.K G.K_nonneg G.K_nonneg (hasJetBound_of_labelBound U G.K hU)
  exact h.mono G.K_nonneg (G.compositionRadius_nonneg G.K G.K_nonneg) le_rfl
    (G.compositionRadius_le_radius G.K (by nlinarith [G.K_nonneg]))


-- @@ L204-206 verbatim
/-- First coefficient, given by `fderiv ℝ U.field (G.inner x)`. -/
def firstCoefficient (U : SmoothL2Field Space) (x : Space) : Space →L[ℝ] Space :=
  fderiv ℝ U.field (G.inner x)

-- @@ L207-209 verbatim
/-- Second coefficient, given by `fderiv ℝ (fderiv ℝ U.field) (G.inner x)`. -/
def secondCoefficient (U : SmoothL2Field Space) (x : Space) : Space →L[ℝ] Space →L[ℝ] Space :=
  fderiv ℝ (fderiv ℝ U.field) (G.inner x)


-- @@ L211-212 verbatim
theorem firstCoefficient_smooth (U : SmoothL2Field Space) : ContDiff ℝ ∞ (G.firstCoefficient U) :=
  (U.smooth.fderiv_right (m := ∞) (by simp)).comp G.inner_smooth

-- @@ L213-214 verbatim
theorem secondCoefficient_smooth (U : SmoothL2Field Space) : ContDiff ℝ ∞ (G.secondCoefficient U) :=
  ((U.smooth.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).comp G.inner_smooth


-- @@ L216-224 verbatim
theorem firstCoefficient_bound (U : SmoothL2Field Space) (hU : HasLabelBound G.K U) :
    HasSupBound (G.firstCoefficient U) G.firstAmplitude G.radius := by
  have hu : HasSupBound U.field (embeddingCost*G.K) G.K := sup_bound_of_labelBound U G.K hU
  have hd := hu.derivative (mul_nonneg embeddingCost_nonneg G.K_nonneg) G.K_nonneg
  have hc := hd.comp G.inner_smooth (U.smooth.fderiv_right (m := ∞) (by simp))
    G.firstAmplitude_nonneg (by linarith [G.amp_nonneg]) (by linarith [G.rad_nonneg])
    (mul_nonneg (by norm_num) G.K_nonneg) G.inner_positive
  exact hc.mono G.firstAmplitude_nonneg (G.compositionRadius_nonneg _ (by nlinarith [G.K_nonneg]))
    le_rfl (G.compositionRadius_le_radius (4*G.K) (by nlinarith [G.K_nonneg]))


-- @@ L226-238 verbatim
theorem secondCoefficient_bound (U : SmoothL2Field Space) (hU : HasLabelBound G.K U) :
    HasSupBound (G.secondCoefficient U) G.secondAmplitude G.radius := by
  have hu : HasSupBound U.field (embeddingCost*G.K) G.K := sup_bound_of_labelBound U G.K hU
  have hd := (hu.derivative (mul_nonneg embeddingCost_nonneg G.K_nonneg) G.K_nonneg).derivative
    G.firstAmplitude_nonneg (mul_nonneg (by norm_num) G.K_nonneg)
  have hc := hd.comp G.inner_smooth
    ((U.smooth.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp))
    G.secondAmplitude_nonneg (by linarith [G.amp_nonneg]) (by linarith [G.rad_nonneg])
    (by nlinarith [G.K_nonneg]) G.inner_positive
  have he : (4 : ℝ)*(4*G.K)=16*G.K := by ring
  rw [he] at hc
  exact hc.mono G.secondAmplitude_nonneg (G.compositionRadius_nonneg _ (by nlinarith [G.K_nonneg]))
    le_rfl (G.compositionRadius_le_radius (16*G.K) le_rfl)


-- @@ L240-241 verbatim
theorem velocity_bound_radius : G.velocity.HasJetBound G.amp G.radius :=
  G.velocity_bound.mono G.amp_nonneg G.rad_nonneg le_rfl G.rad_le_radius

-- @@ L242-243 verbatim
theorem acceleration_bound_radius : G.acceleration.HasJetBound G.amp G.radius :=
  G.acceleration_bound.mono G.amp_nonneg G.rad_nonneg le_rfl G.rad_le_radius

-- @@ L244-245 verbatim
theorem displacement_bound_radius : G.displacement.HasJetBound G.amp G.radius :=
  G.displacement_bound.mono G.amp_nonneg G.rad_nonneg le_rfl G.rad_le_radius

-- @@ L246-247 verbatim
theorem velocity_sup_radius : HasSupBound G.velocity.field G.amp G.radius :=
  G.velocity_sup.mono G.amp_nonneg G.rad_nonneg le_rfl G.rad_le_radius


-- @@ L249-253 verbatim
/-- First term, constructed using `productField`. -/
def firstTerm (U : SmoothL2Field Space) (hU : HasLabelBound G.K U) : SmoothL2Field Space :=
  productField (G.firstCoefficient U) (G.firstCoefficient_smooth U) G.velocity
    G.firstAmplitude G.amp G.radius G.firstAmplitude_nonneg G.amp_nonneg G.radius_nonneg
    (G.firstCoefficient_bound U hU) G.velocity_bound_radius


-- @@ L255-259 verbatim
theorem firstTerm_bound (U : SmoothL2Field Space) (hU : HasLabelBound G.K U) :
    (G.firstTerm U hU).HasJetBound (3*G.firstAmplitude*G.amp) G.radius :=
  productField_bound (G.firstCoefficient U) (G.firstCoefficient_smooth U) G.velocity
    G.firstAmplitude G.amp G.radius G.firstAmplitude_nonneg G.amp_nonneg G.radius_nonneg
    (G.firstCoefficient_bound U hU) G.velocity_bound_radius


-- @@ L261-264 verbatim
/-- Quadratic coefficient, given by `G.secondCoefficient G.parentDisplacement x
(G.velocity.field x)`. -/
def quadraticCoefficient (x : Space) : Space →L[ℝ] Space :=
  G.secondCoefficient G.parentDisplacement x (G.velocity.field x)


-- @@ L266-267 verbatim
theorem quadraticCoefficient_smooth : ContDiff ℝ ∞ G.quadraticCoefficient :=
  (G.secondCoefficient_smooth G.parentDisplacement).clm_apply G.velocity.smooth


-- @@ L269-274 verbatim
theorem quadraticCoefficient_bound :
    HasSupBound G.quadraticCoefficient (3*G.secondAmplitude*G.amp) G.radius :=
  (G.secondCoefficient_bound G.parentDisplacement G.parentDisplacement_bound).apply
      G.velocity_sup_radius
    (G.secondCoefficient_smooth G.parentDisplacement) G.velocity.smooth G.secondAmplitude_nonneg
    G.amp_nonneg G.radius_nonneg


-- @@ L276-282 verbatim
/-- Quadratic term, constructed using `productField`. -/
def quadraticTerm : SmoothL2Field Space :=
  productField G.quadraticCoefficient G.quadraticCoefficient_smooth G.velocity
    (3*G.secondAmplitude*G.amp) G.amp G.radius
    (mul_nonneg (mul_nonneg (by
        norm_num) G.secondAmplitude_nonneg) G.amp_nonneg) G.amp_nonneg G.radius_nonneg
    G.quadraticCoefficient_bound G.velocity_bound_radius


-- @@ L284-293 verbatim
theorem quadraticTerm_bound :
    G.quadraticTerm.HasJetBound (9*G.secondAmplitude*G.amp^2) G.radius := by
  have h := productField_bound G.quadraticCoefficient G.quadraticCoefficient_smooth G.velocity
    (3*G.secondAmplitude*G.amp) G.amp G.radius
    (mul_nonneg (mul_nonneg (by
        norm_num) G.secondAmplitude_nonneg) G.amp_nonneg) G.amp_nonneg G.radius_nonneg
    G.quadraticCoefficient_bound G.velocity_bound_radius
  have he : 3*(3*G.secondAmplitude*G.amp)*G.amp = 9*G.secondAmplitude*G.amp^2 := by ring
  rw [he] at h
  exact h


-- @@ L295-302 verbatim
/-- Acceleration term, constructed using `productField`. -/
def accelerationTerm : SmoothL2Field Space :=
  productField (G.firstCoefficient G.parentDisplacement) (G.firstCoefficient_smooth
      G.parentDisplacement)
    G.acceleration G.firstAmplitude G.amp G.radius G.firstAmplitude_nonneg G.amp_nonneg
        G.radius_nonneg
    (G.firstCoefficient_bound G.parentDisplacement G.parentDisplacement_bound)
        G.acceleration_bound_radius


-- @@ L304-311 verbatim
theorem accelerationTerm_bound :
    G.accelerationTerm.HasJetBound (3*G.firstAmplitude*G.amp) G.radius :=
  productField_bound (G.firstCoefficient G.parentDisplacement) (G.firstCoefficient_smooth
      G.parentDisplacement)
    G.acceleration G.firstAmplitude G.amp G.radius G.firstAmplitude_nonneg G.amp_nonneg
        G.radius_nonneg
    (G.firstCoefficient_bound G.parentDisplacement G.parentDisplacement_bound)
        G.acceleration_bound_radius


-- @@ L313-316 verbatim
/-- Child displacement, given by `addField (G.parentComposed G.parentDisplacement
G.parentDisplacement_bound) G.displacement`. -/
def childDisplacement : SmoothL2Field Space :=
  addField (G.parentComposed G.parentDisplacement G.parentDisplacement_bound) G.displacement

-- @@ L317-320 verbatim
/-- Child velocity, constructed using `addField`. -/
def childVelocity : SmoothL2Field Space :=
  addField (addField (G.parentComposed G.parentVelocity G.parentVelocity_bound) G.velocity)
    (G.firstTerm G.parentDisplacement G.parentDisplacement_bound)

-- @@ L321-327 verbatim
/-- Child acceleration, constructed using `addField`. -/
def childAcceleration : SmoothL2Field Space :=
  addField (addField (addField (addField (addField
    (G.parentComposed G.parentAcceleration G.parentAcceleration_bound)
    (G.firstTerm G.parentVelocity G.parentVelocity_bound))
    (G.firstTerm G.parentVelocity G.parentVelocity_bound)) G.quadraticTerm) G.acceleration)
        G.accelerationTerm


-- @@ L329-336 verbatim
theorem childDisplacement_bound : G.childDisplacement.HasJetBound G.amplitude G.radius := by
  have h := (G.parentComposed_bound G.parentDisplacement G.parentDisplacement_bound).add
      G.displacement_bound_radius
  apply h.mono (add_nonneg G.K_nonneg G.amp_nonneg) G.radius_nonneg _ le_rfl
  have h₁ := mul_nonneg G.firstAmplitude_nonneg G.amp_nonneg
  have h₂ := mul_nonneg G.secondAmplitude_nonneg (sq_nonneg G.amp)
  unfold amplitude
  nlinarith


-- @@ L338-346 verbatim
theorem childVelocity_bound : G.childVelocity.HasJetBound G.amplitude G.radius := by
  have h := ((G.parentComposed_bound G.parentVelocity G.parentVelocity_bound).add
      G.velocity_bound_radius).add
    (G.firstTerm_bound G.parentDisplacement G.parentDisplacement_bound)
  have h₁ := mul_nonneg G.firstAmplitude_nonneg G.amp_nonneg
  have h₂ := mul_nonneg G.secondAmplitude_nonneg (sq_nonneg G.amp)
  apply h.mono (by nlinarith [G.K_nonneg,G.amp_nonneg]) G.radius_nonneg _ le_rfl
  unfold amplitude
  nlinarith


-- @@ L348-358 verbatim
theorem childAcceleration_bound : G.childAcceleration.HasJetBound G.amplitude G.radius := by
  have h := (((((G.parentComposed_bound G.parentAcceleration G.parentAcceleration_bound).add
    (G.firstTerm_bound G.parentVelocity G.parentVelocity_bound)).add
    (G.firstTerm_bound G.parentVelocity G.parentVelocity_bound)).add G.quadraticTerm_bound).add
    G.acceleration_bound_radius).add G.accelerationTerm_bound
  have he : G.K+3*G.firstAmplitude*G.amp+3*G.firstAmplitude*G.amp +
      9*G.secondAmplitude*G.amp^2+G.amp+3*G.firstAmplitude*G.amp = G.amplitude := by
    unfold amplitude
    ring
  rw [he] at h
  exact h


-- @@ L360-362 verbatim
theorem childDisplacement_apply (x : Space) :
    G.childDisplacement.field x = G.parentDisplacement.field (G.inner x)+G.displacement.field x :=
        rfl


-- @@ L364-366 verbatim
theorem childVelocity_apply (x : Space) :
    G.childVelocity.field x = G.parentVelocity.field (G.inner x)+G.velocity.field x +
      fderiv ℝ G.parentDisplacement.field (G.inner x) (G.velocity.field x) := rfl


-- @@ L368-375 verbatim
theorem childAcceleration_apply (x : Space) :
    G.childAcceleration.field x = G.parentAcceleration.field (G.inner x) +
      fderiv ℝ G.parentVelocity.field (G.inner x) (G.velocity.field x) +
      fderiv ℝ G.parentVelocity.field (G.inner x) (G.velocity.field x) +
      fderiv ℝ (fderiv ℝ G.parentDisplacement.field) (G.inner x) (G.velocity.field x)
          (G.velocity.field x) +
      G.acceleration.field x+fderiv ℝ G.parentDisplacement.field (G.inner x) (G.acceleration.field
          x) := rfl


-- @@ L377-387 verbatim
theorem child_label_bounds (K : ℝ)
    (ha : EulerParameterWordGevrey.sobolevCoefficientAmplitude (Fin 3) 6 G.radius G.amplitude ≤ K)
    (hr : EulerParameterWordGevrey.sobolevCoefficientRadius (Fin 3) G.radius ≤ K) :
    HasLabelBound K G.childDisplacement ∧ HasLabelBound K G.childVelocity ∧ HasLabelBound K
        G.childAcceleration :=
  ⟨hasLabelBound_of_jet_bound _ _ _ K G.amplitude_nonneg G.radius_nonneg G.childDisplacement_bound
      ha hr,
   hasLabelBound_of_jet_bound _ _ _ K G.amplitude_nonneg G.radius_nonneg G.childVelocity_bound ha
       hr,
   hasLabelBound_of_jet_bound _ _ _ K G.amplitude_nonneg G.radius_nonneg G.childAcceleration_bound
       ha hr⟩


-- @@ L389-389 verbatim
end Data

-- @@ L390-390 verbatim
end EulerChildParticleFieldBounds
