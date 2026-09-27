/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SignedMeanGain
import LeanPool.NavierStokesAndEuler.NavierStokes.MovingMomentBounds


-- @@ L12-18 verbatim
/-!
# Measured debt changes for actual gauge updates

The debt is the three actual radial moments stored by `CorrectionState`.
The change estimates use the actual velocity and covariance increments;
no improved bound on the whole updated covariance or debt is assumed.
-/


-- @@ L20-20 verbatim
@[expose] public section



-- @@ L23-23 verbatim
namespace NavierStokes.GaugeDebtIncrement


-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-27 verbatim
open Set Function Filter MeasureTheory

-- @@ L28-28 verbatim
open scoped ContDiff Topology Interval BigOperators

-- @@ L29-29 verbatim
open WeightedClasses MeanIncrementBounds CorrectionState LocalSignedRequest


-- @@ L31-32 verbatim
/-- Plane: an abbreviation for `PressureStream.Plane`. -/
abbrev Plane := PressureStream.Plane

-- @@ L33-34 verbatim
/-- Point: an abbreviation for `PressureStream.Lift Plane`. -/
abbrev Point := PressureStream.Lift Plane

-- @@ L35-36 verbatim
/-- Scalar: an abbreviation for `MeanIncrementBounds.Field Point`. -/
abbrev Scalar := MeanIncrementBounds.Field Point

-- @@ L37-38 verbatim
/-- Tensor: an abbreviation for `Fin 3 → Fin 3 → Scalar`. -/
abbrev Tensor := Fin 3 → Fin 3 → Scalar


-- @@ L40-44 verbatim
/-- Primitive local smoothness and actual support, without a class estimate. -/
structure Regular {coord : ℝ} (U : SlowRegion coord) (a b : ℝ) (f : Scalar) : Prop where
  smooth : SmoothOn (PhysicalMeanDomain.slowDomain U.carrier) f
  supported : ∀ n, VariableGaugeMean.SupportedGauge a b (VariableGaugeMean.qLength coord) U.carrier
      (f n)


-- @@ L46-46 verbatim
namespace Regular


-- @@ L48-48 verbatim
variable {coord a b : ℝ} {U : SlowRegion coord} {f g : Scalar}


-- @@ L50-55 verbatim
theorem containing (hf : Regular U a b f) {lo hi : ℝ}
    (hl : ∀ x ∈ U.carrier, lo ≤ VariableGaugeMean.qLength coord x * a)
    (hr : ∀ x ∈ U.carrier, VariableGaugeMean.qLength coord x * b ≤ hi) :
    LocalRankDefect.LocalShell lo hi U.carrier f :=
  ⟨hf.smooth, fun n x hx hn => ⟨(hl _ hx).trans (hf.supported n x hx hn).1,
    (hf.supported n x hx hn).2.trans (hr _ hx)⟩⟩


-- @@ L57-58 verbatim
theorem zero : Regular U a b (0 : Scalar) :=
  ⟨fun _ => contDiffOn_const, fun _ _ _ hn => (hn rfl).elim⟩


-- @@ L60-65 verbatim
theorem add (hf : Regular U a b f) (hg : Regular U a b g) : Regular U a b (f + g) := by
  refine ⟨hf.smooth.add hg.smooth, ?_⟩
  intro n x hx hn
  by_cases hz : f n x = 0
  · exact hg.supported n x hx (fun hz' => hn (by simp [hz, hz']))
  · exact hf.supported n x hx hz


-- @@ L67-68 verbatim
theorem neg (hf : Regular U a b f) : Regular U a b (-f) :=
  ⟨hf.smooth.neg, fun n x hx hn => hf.supported n x hx (neg_ne_zero.mp hn)⟩


-- @@ L70-71 verbatim
theorem sub (hf : Regular U a b f) (hg : Regular U a b g) : Regular U a b (f - g) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg


-- @@ L73-74 verbatim
theorem mul (hf : Regular U a b f) (hg : Regular U a b g) : Regular U a b (f * g) :=
  ⟨hf.smooth.mul hg.smooth, fun n x hx hn => hf.supported n x hx (left_ne_zero_of_mul hn)⟩


-- @@ L76-77 verbatim
theorem smul (hf : Regular U a b f) (c : ℝ) : Regular U a b (c • f) :=
  ⟨hf.smooth.smul c, fun n x hx hn => hf.supported n x hx (right_ne_zero_of_mul hn)⟩


-- @@ L79-82 verbatim
theorem band_mul (hf : Regular U a b f) (c : ℕ → ℝ) :
    Regular U a b (fun n x => c n * f n x) :=
  ⟨fun n => contDiffOn_const.mul (hf.smooth n),
    fun n x hx hn => hf.supported n x hx (right_ne_zero_of_mul hn)⟩


-- @@ L84-89 verbatim
theorem directional (hf : Regular U a b f) (v : Point) :
    Regular U a b (fun n x => fderiv ℝ (f n) x v) := by
  refine ⟨hf.smooth.directional (PhysicalMeanDomain.slowDomain_open U.isOpen) v, ?_⟩
  exact fun n => VariableGaugeMean.fderiv_apply_supportedGauge U.isOpen
    ((VariableGaugeMean.qLength_contDiffOn U.coord_pos U.coord_lt_one).mono
      (fun x hx => U.time_pos x hx)).continuousOn (hf.supported n) (fun _ => v)


-- @@ L91-95 verbatim
theorem coefficient_mul (hf : Regular U a b f) (ha : 0 < a) (hab : a < b)
    (hg : SmoothOn (LocalRankDefect.positiveDomain U.carrier) g) : Regular U a b (g * f) := by
  obtain ⟨lo, hi, _, hlo, _, _, _, hl, hr, _⟩ := VariableGaugeMean.qLength_reference_bounds U ha hab
  exact ⟨((hf.containing hl hr).coefficient_mul hlo U.isOpen hg).smooth,
    fun n x hx hn => hf.supported n x hx (right_ne_zero_of_mul hn)⟩


-- @@ L97-99 verbatim
theorem mul_coefficient (hf : Regular U a b f) (ha : 0 < a) (hab : a < b)
    (hg : SmoothOn (LocalRankDefect.positiveDomain U.carrier) g) : Regular U a b (f * g) := by
  simpa only [mul_comm] using hf.coefficient_mul ha hab hg


-- @@ L101-105 verbatim
theorem dr (hf : Regular U a b f) (ha : 0 < a) (hab : a < b) {o : Operators Point}
    (ho : LocalRankDefect.LocalOperators U.carrier o) : Regular U a b (o.dr f) := by
  exact (hf.directional o.eR).add
    (((hf.directional o.vR).coefficient_mul ha hab (fun _ => ho.radialProfile)).band_mul
        o.radialFrequency)


-- @@ L107-108 verbatim
theorem dz (hf : Regular U a b f) (o : Operators Point) : Regular U a b (o.dz f) :=
  (hf.directional o.eZ).band_mul o.epsilon


-- @@ L110-112 verbatim
theorem time (hf : Regular U a b f) (o : Operators Point) : Regular U a b (o.time f) :=
  ((hf.directional o.eT).band_mul o.epsilon).neg.add
    ((hf.directional o.vT).band_mul o.fastCoefficient)


-- @@ L114-116 verbatim
theorem inv_mul (hf : Regular U a b f) (ha : 0 < a) (hab : a < b) {o : Operators Point}
    (ho : LocalRankDefect.LocalOperators U.carrier o) : Regular U a b (o.invRadius * f) :=
  hf.coefficient_mul ha hab ho.invRadius_smooth


-- @@ L118-120 verbatim
theorem radialDiv (hf : Regular U a b f) (ha : 0 < a) (hab : a < b) {o : Operators Point}
    (ho : LocalRankDefect.LocalOperators U.carrier o) (c : ℝ) : Regular U a b (o.radialDiv c f) :=
  (hf.dr ha hab ho).add ((hf.inv_mul ha hab ho).smul c)


-- @@ L122-125 verbatim
theorem viscosity (hf : Regular U a b f) (ha : 0 < a) (hab : a < b) {o : Operators Point}
    (ho : LocalRankDefect.LocalOperators U.carrier o) (c : ℝ) : Regular U a b (o.viscosity c f) :=
  (((((hf.dr ha hab ho).dr ha hab ho).add ((hf.dr ha hab ho).inv_mul ha hab ho)).add
    ((hf.dz o).dz o)).sub (((hf.inv_mul ha hab ho).inv_mul ha hab ho).smul c)).band_mul o.epsilon


-- @@ L127-127 verbatim
end Regular


-- @@ L129-133 verbatim
/-- Regular triple data, collecting `radial`, `angular`, `axial`. -/
structure RegularTriple {coord : ℝ} (U : SlowRegion coord) (a b : ℝ) (m : Triple Point) : Prop where
  radial : Regular U a b m.radial
  angular : Regular U a b m.angular
  axial : Regular U a b m.axial


-- @@ L135-135 verbatim
namespace RegularTriple


-- @@ L137-137 verbatim
variable {coord a b : ℝ} {U : SlowRegion coord} {m h base : Triple Point}


-- @@ L139-141 verbatim
theorem smooth (hm : RegularTriple U a b m) : SmoothTriple (PhysicalMeanDomain.slowDomain
    U.carrier) m :=
  ⟨hm.radial.smooth, hm.angular.smooth, hm.axial.smooth⟩


-- @@ L143-145 verbatim
theorem updated (hm : RegularTriple U a b m) (hh : RegularTriple U a b h) :
    RegularTriple U a b (MeanIncrementBounds.updated m h) :=
  ⟨hm.radial.add hh.radial, hm.angular.add hh.angular, hm.axial.add hh.axial⟩


-- @@ L147-151 verbatim
theorem thetaAxial (hm : RegularTriple U a b m) (ha : 0 < a) (hab : a < b)
    (hb : SmoothTriple (LocalRankDefect.positiveDomain U.carrier) base) :
    Regular U a b (MeanIncrementBounds.thetaAxial base m) :=
  ((hm.angular.coefficient_mul ha hab hb.axial).add
    (hm.axial.coefficient_mul ha hab hb.angular)).add (hm.axial.mul hm.angular)


-- @@ L153-156 verbatim
theorem axialAxial (hm : RegularTriple U a b m) (ha : 0 < a) (hab : a < b)
    (hb : SmoothTriple (LocalRankDefect.positiveDomain U.carrier) base) :
    Regular U a b (MeanIncrementBounds.axialAxial base m) :=
  ((hm.axial.coefficient_mul ha hab hb.axial).smul 2).add (hm.axial.mul hm.axial)


-- @@ L158-162 verbatim
theorem axialRadial (hm : RegularTriple U a b m) (ha : 0 < a) (hab : a < b)
    (hb : SmoothTriple (LocalRankDefect.positiveDomain U.carrier) base) :
    Regular U a b (MeanIncrementBounds.axialRadial base m) :=
  ((hm.axial.coefficient_mul ha hab hb.radial).add
    (hm.radial.mul_coefficient ha hab hb.axial)).add (hm.radial.mul hm.axial)


-- @@ L164-167 verbatim
theorem radialRadial (hm : RegularTriple U a b m) (ha : 0 < a) (hab : a < b)
    (hb : SmoothTriple (LocalRankDefect.positiveDomain U.carrier) base) :
    Regular U a b (MeanIncrementBounds.radialRadial base m) :=
  ((hm.radial.coefficient_mul ha hab hb.radial).smul 2).add (hm.radial.mul hm.radial)


-- @@ L169-172 verbatim
theorem radialAngular (hm : RegularTriple U a b m) (ha : 0 < a) (hab : a < b)
    (hb : SmoothTriple (LocalRankDefect.positiveDomain U.carrier) base) :
    Regular U a b (MeanIncrementBounds.radialAngular base m) :=
  ((hm.angular.coefficient_mul ha hab hb.angular).smul 2).add (hm.angular.mul hm.angular)


-- @@ L174-182 verbatim
theorem gr (hm : RegularTriple U a b m) (ha : 0 < a) (hab : a < b)
    (hb : SmoothTriple (LocalRankDefect.positiveDomain U.carrier) base) {o : Operators Point}
    (ho : LocalRankDefect.LocalOperators U.carrier o) (W : Tensor)
    (hW : ∀ i j, Regular U a b (W i j)) : Regular U a b (MeanIncrementBounds.gr o base m W) :=
  (((((hm.radial.time o).add
    (((hm.radialRadial ha hab hb).add (hW 0 0)).radialDiv ha hab ho 1)).add
    (((hm.axialRadial ha hab hb).add (hW 2 0)).dz o)).sub
    (((hm.radialAngular ha hab hb).add (hW 1 1)).inv_mul ha hab ho)).sub
    (hm.radial.viscosity ha hab ho 1)).neg


-- @@ L184-184 verbatim
end RegularTriple


-- @@ L186-186 verbatim
/-! ## Exact moments and their class bounds -/


-- @@ L188-188 verbatim
section Moments


-- @@ L190-190 verbatim
variable {coord a b cL cR : ℝ} (U : SlowRegion coord) (ha : 0 < a) (hab : a < b)


-- @@ L192-192 verbatim
include ha hab


-- @@ L194-198 verbatim
theorem radialMoment_sub_on {f g : Scalar} (hf : Regular U a b f) (hg : Regular U a b g)
    (k n : ℕ) {x : Plane} (hx : x ∈ U.carrier) :
    radialMoment k (f - g) n x = radialMoment k f n x - radialMoment k g n x := by
  obtain ⟨lo, hi, _, _, _, _, _, hl, hr, _⟩ := VariableGaugeMean.qLength_reference_bounds U ha hab
  exact LocalRankDefect.barMoment_sub_on U.isOpen (hf.containing hl hr) (hg.containing hl hr) k n hx


-- @@ L200-204 verbatim
theorem radialMoment_add_on {f g : Scalar} (hf : Regular U a b f) (hg : Regular U a b g)
    (k n : ℕ) {x : Plane} (hx : x ∈ U.carrier) :
    radialMoment k (f + g) n x = radialMoment k f n x + radialMoment k g n x := by
  obtain ⟨lo, hi, _, _, _, _, _, hl, hr, _⟩ := VariableGaugeMean.qLength_reference_bounds U ha hab
  exact LocalRankDefect.barMoment_add_on U.isOpen (hf.containing hl hr) (hg.containing hl hr) k n hx


-- @@ L206-206 verbatim
end Moments


-- @@ L208-212 verbatim
/-- Moment change, defined pointwise by `![radialMoment 0 G n x, radialMoment 2 T n x,
radialMoment 1 Z n x - (1 / 2 : ℝ) * radialMoment 2 G n x]`. -/
noncomputable def momentChange (G T Z : Scalar) : ℕ → Plane → Fin 3 → ℝ :=
  fun n x => ![radialMoment 0 G n x, radialMoment 2 T n x,
    radialMoment 1 Z n x - (1 / 2 : ℝ) * radialMoment 2 G n x]


-- @@ L214-214 verbatim
section DebtIdentity


-- @@ L216-222 verbatim
variable {coord a b : ℝ} (U : SlowRegion coord) (ha : 0 < a) (hab : a < b)
    (c : Context Point) (u v : State Point)
    (hgu : Regular U a b (u.gr c)) (hgv : Regular U a b (v.gr c))
    (htu : Regular U a b (thetaAxial c.base u.mean + u.covariance 2 1))
    (htv : Regular U a b (thetaAxial c.base v.mean + v.covariance 2 1))
    (hzu : Regular U a b (axialAxial c.base u.mean + u.covariance 2 2))
    (hzv : Regular U a b (axialAxial c.base v.mean + v.covariance 2 2))


-- @@ L224-245 verbatim
include ha hab hgu hgv htu htv hzu hzv in
/-- The actual State debt difference consists of the three actual moment
changes, with the pressure-source contribution in the axial row retained. -/
theorem debt_sub_eq (n : ℕ) {x : Plane} (hx : x ∈ U.carrier) :
    debt c v n x - debt c u n x =
      momentChange (v.gr c - u.gr c)
        ((thetaAxial c.base v.mean + v.covariance 2 1) - (thetaAxial c.base u.mean + u.covariance 2
            1))
        ((axialAxial c.base v.mean + v.covariance 2 2) - (axialAxial c.base u.mean + u.covariance 2
            2)) n x := by
  funext i
  fin_cases i
  · exact (radialMoment_sub_on U ha hab hgv hgu 0 n hx).symm
  · exact (radialMoment_sub_on U ha hab htv htu 2 n hx).symm
  · change (radialMoment 1 _ n x - (1 / 2 : ℝ) * radialMoment 2 _ n x) -
        (radialMoment 1 _ n x - (1 / 2 : ℝ) * radialMoment 2 _ n x) =
      radialMoment 1 ((axialAxial c.base v.mean + v.covariance 2 2) -
        (axialAxial c.base u.mean + u.covariance 2 2)) n x -
      (1 / 2 : ℝ) * radialMoment 2 (v.gr c - u.gr c) n x
    rw [radialMoment_sub_on U ha hab hzv hzu 1 n hx,
      radialMoment_sub_on U ha hab hgv hgu 2 n hx]
    ring


-- @@ L247-247 verbatim
end DebtIdentity


-- @@ L249-249 verbatim
section MomentClasses


-- @@ L251-253 verbatim
variable {coord a b cL cR : ℝ} (U : SlowRegion coord)
    (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)


-- @@ L255-255 verbatim
include hab


-- @@ L257-275 verbatim
theorem momentChange_mem {H : ℝ} {G T Z : Scalar}
    (hG : Regular U a b G) (hT : Regular U a b T) (hZ : Regular U a b Z)
    (hcG : MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) H G)
    (hcT : MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) H T)
    (hcZ : MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) H Z) (i : Fin 3) :
    UnweightedClass (PhysicalMeanDomain.localSlowStripData U.carrier U.isOpen ε L hε hεone hL) H
      (fun n x => momentChange G T Z n x i) := by
  have h0 := MovingMomentBounds.radialMoment_mem U ha hab hcL hcR ε L hε hεone hL hG.smooth
      hG.supported hcG 0
  have h1 := MovingMomentBounds.radialMoment_mem U ha hab hcL hcR ε L hε hεone hL hT.smooth
      hT.supported hcT 2
  have h2 := MovingMomentBounds.radialMoment_mem U ha hab hcL hcR ε L hε hεone hL hZ.smooth
      hZ.supported hcZ 1
  have h3 := MovingMomentBounds.radialMoment_mem U ha hab hcL hcR ε L hε hεone hL hG.smooth
      hG.supported hcG 2
  fin_cases i
  · exact h0
  · exact h1
  · exact Class.sub h2 (Class.smul h3 (1 / 2))


-- @@ L277-295 verbatim
theorem debt_change_mem {H : ℝ} (c : Context Point) (u v : State Point)
    (hgu : Regular U a b (u.gr c)) (hgv : Regular U a b (v.gr c))
    (htu : Regular U a b (thetaAxial c.base u.mean + u.covariance 2 1))
    (htv : Regular U a b (thetaAxial c.base v.mean + v.covariance 2 1))
    (hzu : Regular U a b (axialAxial c.base u.mean + u.covariance 2 2))
    (hzv : Regular U a b (axialAxial c.base v.mean + v.covariance 2 2))
    (hcG : MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) H (v.gr c - u.gr c))
    (hcT : MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) H
      ((thetaAxial c.base v.mean + v.covariance 2 1) - (thetaAxial c.base u.mean + u.covariance 2
          1)))
    (hcZ : MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) H
      ((axialAxial c.base v.mean + v.covariance 2 2) - (axialAxial c.base u.mean + u.covariance 2
          2))) (i : Fin 3) :
    UnweightedClass (PhysicalMeanDomain.localSlowStripData U.carrier U.isOpen ε L hε hεone hL) H
      (fun n x => debt c v n x i - debt c u n x i) := by
  apply class_congr (momentChange_mem U ha hab hcL hcR ε L hε hεone hL
    (hgv.sub hgu) (htv.sub htu) (hzv.sub hzu) hcG hcT hcZ i)
  intro n x hx
  exact congrFun (debt_sub_eq U ha hab c u v hgu hgv htu htv hzu hzv n hx) i


-- @@ L297-297 verbatim
end MomentClasses


-- @@ L299-299 verbatim
section DomainTools


-- @@ L301-304 verbatim
theorem smoothTriple_mono {V W : Set Point} {m : Triple Point}
    (hm : SmoothTriple W m) (hVW : V ⊆ W) : SmoothTriple V m :=
  ⟨fun n => (hm.radial n).mono hVW, fun n => (hm.angular n).mono hVW,
    fun n => (hm.axial n).mono hVW⟩


-- @@ L306-312 verbatim
theorem Regular.zero_of_nonpositive {coord a b : ℝ} {U : SlowRegion coord} {f : Scalar}
    (hf : Regular U a b f) (ha : 0 < a) (n : ℕ) {z : Point}
    (hz : z.2.1 ∈ U.carrier) (hR : z.1 ≤ 0) : f n z = 0 := by
  by_contra hn
  have hs := hf.supported n z hz hn
  have hp := mul_pos (VariableGaugeMean.qLength_pos U.coord_pos U.coord_lt_one (U.time_pos _ hz)) ha
  exact (not_lt_of_ge hR) (hp.trans_le hs.1)


-- @@ L314-322 verbatim
theorem agree_slow_of_positive {coord a b : ℝ} {U : SlowRegion coord} {f g : Scalar}
    (ha : 0 < a) (hf : Regular U a b f) (hg : Regular U a b g)
    (he : Agree (LocalRankDefect.positiveDomain U.carrier) f g) :
    Agree (PhysicalMeanDomain.slowDomain U.carrier) f g := by
  intro n z hz
  by_cases hR : 0 < z.1
  · exact he n ⟨hR, hz⟩
  · rw [hf.zero_of_nonpositive ha n hz (le_of_not_gt hR),
      hg.zero_of_nonpositive ha n hz (le_of_not_gt hR)]


-- @@ L324-336 verbatim
theorem moving_subset_positive {coord a b cL cR : ℝ} (U : SlowRegion coord)
    (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n) :
    (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL).domain ⊆
      LocalRankDefect.positiveDomain U.carrier := by
  intro z hz
  have hh := (movingStrip_domain U a b cL cR ha hcL hcR ε L hε hεone hL z).mp hz
  refine ⟨?_, hh.1⟩
  have hpos := VariableGaugeMean.qLength_pos U.coord_pos U.coord_lt_one (U.time_pos _ hh.1)
  have hr : 0 < z.1 / VariableGaugeMean.qLength coord z.2.1 := ha.trans hh.2.1
  have he := (lt_div_iff₀ hpos).mp hr
  simp only [zero_mul] at he
  exact he


-- @@ L338-344 verbatim
theorem radialMoment_congr_on {U : Set Plane} {f g : Scalar}
    (he : Agree (PhysicalMeanDomain.slowDomain U) f g) (k n : ℕ) {x : Plane} (hx : x ∈ U) :
    radialMoment k f n x = radialMoment k g n x := by
  exact PhysicalMeanDomain.liftedPressureMass_fiberLocal
    (fun z => z.1 ^ k * f n z) (fun z => z.1 ^ k * g n z) x
    (fun R Y => congrArg (fun q : ℝ => R ^ k * q) (show f n (R, (x, Y)) = g n (R, (x, Y)) from he n
        hx)) 0 0


-- @@ L346-346 verbatim
end DomainTools


-- @@ L348-348 verbatim
section WaveAlgebra


-- @@ L350-351 verbatim
variable (g : VariableGaugeMean.GaugeData Plane) (c : Context Point) (u : State Point)
    (w : Oscillation Point) (q : OscillatoryScalar Point) (gaussian : Oscillation Point)


-- @@ L353-360 verbatim
theorem wave_thetaFlux_change :
    (thetaAxial c.base (SignedMeanGain.waveStage g c u w q gaussian).mean +
      (SignedMeanGain.waveStage g c u w q gaussian).covariance 2 1) -
        (thetaAxial c.base u.mean + u.covariance 2 1) =
      SignedMeanGain.covarianceIncrement u.oscillation w 2 1 := by
  rw [SignedMeanGain.waveStage_mean, SignedMeanGain.waveStage_covariance]
  change (thetaAxial c.base u.mean + (u.covariance 2 1 + _)) - _ = _
  abel


-- @@ L362-369 verbatim
theorem wave_axialFlux_change :
    (axialAxial c.base (SignedMeanGain.waveStage g c u w q gaussian).mean +
      (SignedMeanGain.waveStage g c u w q gaussian).covariance 2 2) -
        (axialAxial c.base u.mean + u.covariance 2 2) =
      SignedMeanGain.covarianceIncrement u.oscillation w 2 2 := by
  rw [SignedMeanGain.waveStage_mean, SignedMeanGain.waveStage_covariance]
  change (axialAxial c.base u.mean + (u.covariance 2 2 + _)) - _ = _
  abel


-- @@ L371-371 verbatim
end WaveAlgebra


-- @@ L373-373 verbatim
section WaveRegularity


-- @@ L375-382 verbatim
variable {coord a b : ℝ} (U : SlowRegion coord) (ha : 0 < a) (hab : a < b)
    (g : VariableGaugeMean.GaugeData Plane) (c : Context Point) (u : State Point)
    (w : Oscillation Point) (q : OscillatoryScalar Point) (gaussian : Oscillation Point)
    (hop : LocalRankDefect.LocalOperators U.carrier c.operators)
    (hb : SmoothTriple (LocalRankDefect.positiveDomain U.carrier) c.base)
    (hm : RegularTriple U a b u.mean)
    (hW : ∀ i j, Regular U a b (u.covariance i j))
    (hX : ∀ i j, Regular U a b (SignedMeanGain.covarianceIncrement u.oscillation w i j))


-- @@ L384-388 verbatim
include hm in
theorem waveStage_mean_regular : RegularTriple U a b (SignedMeanGain.waveStage g c u w q
    gaussian).mean := by
  rw [SignedMeanGain.waveStage_mean]
  exact hm


-- @@ L390-394 verbatim
include hW hX in
theorem waveStage_covariance_regular (i j : Fin 3) :
    Regular U a b ((SignedMeanGain.waveStage g c u w q gaussian).covariance i j) := by
  rw [SignedMeanGain.waveStage_covariance]
  exact (hW i j).add (hX i j)


-- @@ L396-396 verbatim
include ha hab hop hb hm hW hX


-- @@ L398-416 verbatim
theorem waveStage_gr_agree :
    Agree (PhysicalMeanDomain.slowDomain U.carrier)
      ((SignedMeanGain.waveStage g c u w q gaussian).gr c - u.gr c)
      (SignedMeanGain.radialCovarianceChange c.operators (SignedMeanGain.covarianceIncrement
          u.oscillation w)) := by
  have hmu := waveStage_mean_regular U g c u w q gaussian hm
  have hWv := waveStage_covariance_regular U g c u w q gaussian hW hX
  have hgu := hm.gr ha hab hb hop u.covariance hW
  have hgv := hmu.gr ha hab hb hop (SignedMeanGain.waveStage g c u w q gaussian).covariance hWv
  have hR : Regular U a b (SignedMeanGain.radialCovarianceChange c.operators
      (SignedMeanGain.covarianceIncrement u.oscillation w)) :=
    (((hX 0 0).radialDiv ha hab hop 1).neg.sub ((hX 2 0).dz c.operators)).add
      ((hX 1 1).inv_mul ha hab hop)
  apply agree_slow_of_positive ha (hgv.sub hgu) hR
  exact SignedMeanGain.waveStage_gr_change (LocalRankDefect.positiveDomain_open U.isOpen) g c u w q
      gaussian
    hb (smoothTriple_mono hm.smooth (fun _ hx => hx.2))
    (fun i j n => ((hW i j).smooth n).mono (fun _ hx => hx.2))
    (fun i j n => ((hX i j).smooth n).mono (fun _ hx => hx.2))


-- @@ L418-438 verbatim
/-- The wave adds exactly the covariance moments; pressure recomputation
adds no term to the definition of measured debt. -/
theorem waveStage_debt_change_formula (n : ℕ) {x : Plane} (hx : x ∈ U.carrier) :
    debt c (SignedMeanGain.waveStage g c u w q gaussian) n x - debt c u n x =
      momentChange
        (SignedMeanGain.radialCovarianceChange c.operators (SignedMeanGain.covarianceIncrement
            u.oscillation w))
        (SignedMeanGain.covarianceIncrement u.oscillation w 2 1)
        (SignedMeanGain.covarianceIncrement u.oscillation w 2 2) n x := by
  have hmu := waveStage_mean_regular U g c u w q gaussian hm
  have hWv := waveStage_covariance_regular U g c u w q gaussian hW hX
  have he := debt_sub_eq U ha hab c u (SignedMeanGain.waveStage g c u w q gaussian)
    (hm.gr ha hab hb hop u.covariance hW)
    (hmu.gr ha hab hb hop (SignedMeanGain.waveStage g c u w q gaussian).covariance hWv)
    ((hm.thetaAxial ha hab hb).add (hW 2 1)) ((hmu.thetaAxial ha hab hb).add (hWv 2 1))
    ((hm.axialAxial ha hab hb).add (hW 2 2)) ((hmu.axialAxial ha hab hb).add (hWv 2 2)) n hx
  rw [wave_thetaFlux_change, wave_axialFlux_change] at he
  have hg := waveStage_gr_agree U ha hab g c u w q gaussian hop hb hm hW hX
  have h0 := radialMoment_congr_on hg 0 n hx
  have h2 := radialMoment_congr_on hg 2 n hx
  simpa only [momentChange, h0, h2] using he


-- @@ L440-440 verbatim
end WaveRegularity


-- @@ L442-442 verbatim
section WaveBounds


-- @@ L444-453 verbatim
variable {coord a b cL cR : ℝ} (U : SlowRegion coord)
    (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (g : VariableGaugeMean.GaugeData Plane) (c : Context Point) (u : State Point)
    (w : Oscillation Point) (q : OscillatoryScalar Point) (gaussian : Oscillation Point)
    (hop : LocalRankDefect.LocalOperators U.carrier c.operators)
    (hb : SmoothTriple (LocalRankDefect.positiveDomain U.carrier) c.base)
    (hm : RegularTriple U a b u.mean)
    (hW : ∀ i j, Regular U a b (u.covariance i j))
    (hX : ∀ i j, Regular U a b (SignedMeanGain.covarianceIncrement u.oscillation w i j))


-- @@ L455-455 verbatim
include hab hop hb hm hW hX


-- @@ L457-474 verbatim
theorem waveStage_debt_change_mem {κ α : ℝ}
    (ho : OperatorBounds (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) c.operators κ)
    (hcX : SignedMeanGain.TensorClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α
      (SignedMeanGain.covarianceIncrement u.oscillation w)) (i : Fin 3) :
    UnweightedClass (PhysicalMeanDomain.localSlowStripData U.carrier U.isOpen ε L hε hεone hL) (α -
        κ)
      (fun n x => debt c (SignedMeanGain.waveStage g c u w q gaussian) n x i - debt c u n x i) := by
  have hR : Regular U a b (SignedMeanGain.radialCovarianceChange c.operators
      (SignedMeanGain.covarianceIncrement u.oscillation w)) :=
    (((hX 0 0).radialDiv ha hab hop 1).neg.sub ((hX 2 0).dz c.operators)).add
      ((hX 1 1).inv_mul ha hab hop)
  have hclass := momentChange_mem U ha hab hcL hcR ε L hε hεone hL hR (hX 2 1) (hX 2 2)
    (SignedMeanGain.radialCovarianceChange_mem ho hcX)
    ((hcX 2 1).mono_exponent (by linarith [ho.kappa_nonneg]))
    ((hcX 2 2).mono_exponent (by linarith [ho.kappa_nonneg])) i
  apply class_congr hclass
  intro n x hx
  exact congrFun (waveStage_debt_change_formula U ha hab g c u w q gaussian hop hb hm hW hX n hx) i


-- @@ L476-476 verbatim
end WaveBounds


-- @@ L478-478 verbatim
section TemporalAlgebra


-- @@ L480-481 verbatim
variable (g : VariableGaugeMean.GaugeData Plane) (h : ℝ) (index : ℕ → ℕ)
    (axial : Plane × Plane) (c : Context Point) (u : State Point)


-- @@ L483-485 verbatim
theorem temporalStage_mean :
    (VariableGaugeMean.temporalStageState g h index axial c u).mean =
      updated u.mean (VariableGaugeMean.temporalIncrementState g h index axial c u) := rfl


-- @@ L487-491 verbatim
theorem temporalStage_covariance :
    (VariableGaugeMean.temporalStageState g h index axial c u).covariance = u.covariance := by
  change bilinearCovariance (u.oscillation + 0) (u.oscillation + 0) =
    bilinearCovariance u.oscillation u.oscillation
  simp only [add_zero]


-- @@ L493-500 verbatim
theorem temporal_thetaFlux_change :
    (thetaAxial c.base (VariableGaugeMean.temporalStageState g h index axial c u).mean +
      (VariableGaugeMean.temporalStageState g h index axial c u).covariance 2 1) -
        (thetaAxial c.base u.mean + u.covariance 2 1) =
      deltaThetaAxial c.base u.mean (VariableGaugeMean.temporalIncrementState g h index axial c u)
          := by
  rw [temporalStage_mean, temporalStage_covariance, thetaAxial_updated]
  abel


-- @@ L502-509 verbatim
theorem temporal_axialFlux_change :
    (axialAxial c.base (VariableGaugeMean.temporalStageState g h index axial c u).mean +
      (VariableGaugeMean.temporalStageState g h index axial c u).covariance 2 2) -
        (axialAxial c.base u.mean + u.covariance 2 2) =
      deltaAxialAxial c.base u.mean (VariableGaugeMean.temporalIncrementState g h index axial c u)
          := by
  rw [temporalStage_mean, temporalStage_covariance, axialAxial_updated]
  abel


-- @@ L511-511 verbatim
end TemporalAlgebra


-- @@ L513-513 verbatim
section TemporalRegularity


-- @@ L515-522 verbatim
variable {coord a b : ℝ} (U : SlowRegion coord) (ha : 0 < a) (hab : a < b)
    (g : VariableGaugeMean.GaugeData Plane) (h : ℝ) (index : ℕ → ℕ)
    (axial : Plane × Plane) (c : Context Point) (u : State Point)
    (hop : LocalRankDefect.LocalOperators U.carrier c.operators)
    (hb : SmoothTriple (LocalRankDefect.positiveDomain U.carrier) c.base)
    (hm : RegularTriple U a b u.mean)
    (hi : RegularTriple U a b (VariableGaugeMean.temporalIncrementState g h index axial c u))
    (hW : ∀ i j, Regular U a b (u.covariance i j))


-- @@ L524-528 verbatim
include hm hi in
theorem temporalStage_mean_regular :
    RegularTriple U a b (VariableGaugeMean.temporalStageState g h index axial c u).mean := by
  rw [temporalStage_mean]
  exact hm.updated hi


-- @@ L530-534 verbatim
include hW in
theorem temporalStage_covariance_regular (i j : Fin 3) :
    Regular U a b ((VariableGaugeMean.temporalStageState g h index axial c u).covariance i j) := by
  rw [temporalStage_covariance]
  exact hW i j


-- @@ L536-554 verbatim
include ha hab hop hb hm hi hW in
/-- Only the actual mean increment contributes to the temporal flux change;
the covariance remains the same actual angular integral. -/
theorem temporalStage_debt_change_formula (n : ℕ) {x : Plane} (hx : x ∈ U.carrier) :
    debt c (VariableGaugeMean.temporalStageState g h index axial c u) n x - debt c u n x =
      momentChange
        ((VariableGaugeMean.temporalStageState g h index axial c u).gr c - u.gr c)
        (deltaThetaAxial c.base u.mean (VariableGaugeMean.temporalIncrementState g h index axial c
            u))
        (deltaAxialAxial c.base u.mean (VariableGaugeMean.temporalIncrementState g h index axial c
            u)) n x := by
  have hmu := temporalStage_mean_regular U g h index axial c u hm hi
  have hWv := temporalStage_covariance_regular U g h index axial c u hW
  have he := debt_sub_eq U ha hab c u (VariableGaugeMean.temporalStageState g h index axial c u)
    (hm.gr ha hab hb hop u.covariance hW)
    (hmu.gr ha hab hb hop (VariableGaugeMean.temporalStageState g h index axial c u).covariance hWv)
    ((hm.thetaAxial ha hab hb).add (hW 2 1)) ((hmu.thetaAxial ha hab hb).add (hWv 2 1))
    ((hm.axialAxial ha hab hb).add (hW 2 2)) ((hmu.axialAxial ha hab hb).add (hWv 2 2)) n hx
  rwa [temporal_thetaFlux_change, temporal_axialFlux_change] at he


-- @@ L556-556 verbatim
end TemporalRegularity


-- @@ L558-558 verbatim
section TemporalBounds


-- @@ L560-569 verbatim
variable {coord a b cL cR : ℝ} (U : SlowRegion coord)
    (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (g : VariableGaugeMean.GaugeData Plane) (h : ℝ) (index : ℕ → ℕ)
    (axial : Plane × Plane) (c : Context Point) (u : State Point)
    (hop : LocalRankDefect.LocalOperators U.carrier c.operators)
    (hb : SmoothTriple (LocalRankDefect.positiveDomain U.carrier) c.base)
    (hm : RegularTriple U a b u.mean)
    (hi : RegularTriple U a b (VariableGaugeMean.temporalIncrementState g h index axial c u))
    (hW : ∀ i j, Regular U a b (u.covariance i j))


-- @@ L571-571 verbatim
include hab hop hb hm hi hW


-- @@ L573-612 verbatim
theorem temporalStage_debt_change_mem {κ H : ℝ}
    (ho : OperatorBounds (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) c.operators κ)
    (hbC : BaseBounds (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) c.base)
    (hmC : MeanIncrementBounds.CumulativeBounds (movingStripData U a b cL cR ha hcL hcR ε L hε
        hεone hL) u.mean)
    (hiC : IncrementBounds (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) H
      (VariableGaugeMean.temporalIncrementState g h index axial c u))
    (hH : 9 / 10 ≤ H) (hκ : 2 * κ ≤ 9 / 10) (i : Fin 3) :
    UnweightedClass (PhysicalMeanDomain.localSlowStripData U.carrier U.isOpen ε L hε hεone hL) H
      (fun n x => debt c (VariableGaugeMean.temporalStageState g h index axial c u) n x i - debt c
          u n x i) := by
  let st := movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL
  have hsub : st.domain ⊆ PhysicalMeanDomain.slowDomain U.carrier := fun z hz =>
    ((movingStrip_domain U a b cL cR ha hcL hcR ε L hε hεone hL z).mp hz).1
  have hmu := temporalStage_mean_regular U g h index axial c u hm hi
  have hWv := temporalStage_covariance_regular U g h index axial c u hW
  have hcg : MeanClass st H ((VariableGaugeMean.temporalStageState g h index axial c u).gr c - u.gr
      c) := by
    simpa only [State.gr, temporalStage_mean, temporalStage_covariance] using
      gr_change_mem ho hbC hmC hiC hH u.covariance
        (fun i j n => ((hW i j).smooth n).mono hsub) hκ
  have hct : MeanClass st H
      ((thetaAxial c.base (VariableGaugeMean.temporalStageState g h index axial c u).mean +
        (VariableGaugeMean.temporalStageState g h index axial c u).covariance 2 1) -
          (thetaAxial c.base u.mean + u.covariance 2 1)) := by
    rw [temporal_thetaFlux_change]
    exact deltaThetaAxial_mem ho hbC hmC hiC hH
  have hcz : MeanClass st H
      ((axialAxial c.base (VariableGaugeMean.temporalStageState g h index axial c u).mean +
        (VariableGaugeMean.temporalStageState g h index axial c u).covariance 2 2) -
          (axialAxial c.base u.mean + u.covariance 2 2)) := by
    rw [temporal_axialFlux_change]
    exact deltaAxialAxial_mem ho hbC hmC hiC hH
  exact debt_change_mem U ha hab hcL hcR ε L hε hεone hL c u
    (VariableGaugeMean.temporalStageState g h index axial c u)
    (hm.gr ha hab hb hop u.covariance hW)
    (hmu.gr ha hab hb hop (VariableGaugeMean.temporalStageState g h index axial c u).covariance hWv)
    ((hm.thetaAxial ha hab hb).add (hW 2 1)) ((hmu.thetaAxial ha hab hb).add (hWv 2 1))
    ((hm.axialAxial ha hab hb).add (hW 2 2)) ((hmu.axialAxial ha hab hb).add (hWv 2 2)) hcg hct hcz
        i


-- @@ L614-614 verbatim
end TemporalBounds


-- @@ L616-616 verbatim
section DebtPropagation


-- @@ L618-629 verbatim
/-- Old measured debt plus the proved actual change controls the next debt.
The two input exponents may be weakened to a common requested exponent. -/
theorem debt_mem_after_change (s : StripData Plane) (c : Context Point) (u v : State Point)
    {α β H : ℝ} (hα : H ≤ α) (hβ : H ≤ β)
    (hold : ∀ i : Fin 3, UnweightedClass s α (fun n x => debt c u n x i))
    (hchange : ∀ i : Fin 3, UnweightedClass s β (fun n x => debt c v n x i - debt c u n x i)) :
    ∀ i : Fin 3, UnweightedClass s H (fun n x => debt c v n x i) := by
  intro i
  apply class_congr (((hold i).mono_exponent hα).add ((hchange i).mono_exponent hβ))
  intro n x hx
  change debt c v n x i = debt c u n x i + (debt c v n x i - debt c u n x i)
  ring


-- @@ L631-636 verbatim
theorem defectBounds_after_change (s : StripData Plane) (c : Context Point) (u v : State Point)
    {σ τ β : ℝ} (hσ : τ ≤ σ) (hβ : 1 + τ ≤ β)
    (hold : DefectBounds s σ c u)
    (hchange : ∀ i : Fin 3, UnweightedClass s β (fun n x => debt c v n x i - debt c u n x i)) :
    DefectBounds s τ c v :=
  debt_mem_after_change s c u v (by linarith) hβ hold hchange


-- @@ L638-638 verbatim
end DebtPropagation


-- @@ L640-640 verbatim
section WaveNextDebt


-- @@ L642-655 verbatim
variable {coord a b cL cR : ℝ} (U : SlowRegion coord)
    (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (g : VariableGaugeMean.GaugeData Plane) (c : Context Point) (u : State Point)
    (w : Oscillation Point) (q : OscillatoryScalar Point) (gaussian : Oscillation Point)
    (hop : LocalRankDefect.LocalOperators U.carrier c.operators)
    (hb : SmoothTriple (LocalRankDefect.positiveDomain U.carrier) c.base)
    (hm : RegularTriple U a b u.mean)
    (hW : ∀ i j, Regular U a b (u.covariance i j))
    (hX : ∀ i j, Regular U a b (SignedMeanGain.covarianceIncrement u.oscillation w i j))
    {κ α : ℝ}
    (ho : OperatorBounds (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) c.operators κ)
    (hcX : SignedMeanGain.TensorClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α
      (SignedMeanGain.covarianceIncrement u.oscillation w))


-- @@ L657-657 verbatim
include hab hop hb hm hW hX ho hcX


-- @@ L659-667 verbatim
theorem waveStage_debt_mem {β : ℝ} (hβ : α - κ ≤ β)
    (hold : ∀ i : Fin 3, UnweightedClass (PhysicalMeanDomain.localSlowStripData U.carrier U.isOpen
      ε L hε hεone hL) β (fun n x => debt c u n x i)) :
    ∀ i : Fin 3, UnweightedClass (PhysicalMeanDomain.localSlowStripData U.carrier U.isOpen
      ε L hε hεone hL) (α - κ)
      (fun n x => debt c (SignedMeanGain.waveStage g c u w q gaussian) n x i) :=
  debt_mem_after_change _ c u _ hβ le_rfl hold
    (waveStage_debt_change_mem U ha hab hcL hcR ε L hε hεone hL g c u w q gaussian hop hb hm hW hX
        ho hcX)


-- @@ L669-676 verbatim
theorem waveStage_defectBounds {σ τ : ℝ} (hσ : τ ≤ σ) (hτ : 1 + τ ≤ α - κ)
    (hold : DefectBounds (PhysicalMeanDomain.localSlowStripData U.carrier U.isOpen
      ε L hε hεone hL) σ c u) :
    DefectBounds (PhysicalMeanDomain.localSlowStripData U.carrier U.isOpen
      ε L hε hεone hL) τ c (SignedMeanGain.waveStage g c u w q gaussian) :=
  defectBounds_after_change _ c u _ hσ hτ hold
    (waveStage_debt_change_mem U ha hab hcL hcR ε L hε hεone hL g c u w q gaussian hop hb hm hW hX
        ho hcX)


-- @@ L678-678 verbatim
end WaveNextDebt


-- @@ L680-680 verbatim
section TemporalNextDebt


-- @@ L682-699 verbatim
variable {coord a b cL cR : ℝ} (U : SlowRegion coord)
    (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (g : VariableGaugeMean.GaugeData Plane) (h : ℝ) (index : ℕ → ℕ)
    (axial : Plane × Plane) (c : Context Point) (u : State Point)
    (hop : LocalRankDefect.LocalOperators U.carrier c.operators)
    (hb : SmoothTriple (LocalRankDefect.positiveDomain U.carrier) c.base)
    (hm : RegularTriple U a b u.mean)
    (hi : RegularTriple U a b (VariableGaugeMean.temporalIncrementState g h index axial c u))
    (hW : ∀ i j, Regular U a b (u.covariance i j))
    {κ H : ℝ}
    (ho : OperatorBounds (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) c.operators κ)
    (hbC : BaseBounds (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) c.base)
    (hmC : MeanIncrementBounds.CumulativeBounds (movingStripData U a b cL cR ha hcL hcR ε L hε
        hεone hL) u.mean)
    (hiC : IncrementBounds (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) H
      (VariableGaugeMean.temporalIncrementState g h index axial c u))
    (hH : 9 / 10 ≤ H) (hκ : 2 * κ ≤ 9 / 10)


-- @@ L701-701 verbatim
include hab hop hb hm hi hW ho hbC hmC hiC hH hκ


-- @@ L703-711 verbatim
theorem temporalStage_debt_mem {β : ℝ} (hβ : H ≤ β)
    (hold : ∀ i : Fin 3, UnweightedClass (PhysicalMeanDomain.localSlowStripData U.carrier U.isOpen
      ε L hε hεone hL) β (fun n x => debt c u n x i)) :
    ∀ i : Fin 3, UnweightedClass (PhysicalMeanDomain.localSlowStripData U.carrier U.isOpen
      ε L hε hεone hL) H
      (fun n x => debt c (VariableGaugeMean.temporalStageState g h index axial c u) n x i) :=
  debt_mem_after_change _ c u _ hβ le_rfl hold
    (temporalStage_debt_change_mem U ha hab hcL hcR ε L hε hεone hL g h index axial c u
      hop hb hm hi hW ho hbC hmC hiC hH hκ)


-- @@ L713-720 verbatim
theorem temporalStage_defectBounds {σ τ : ℝ} (hσ : τ ≤ σ) (hτ : 1 + τ ≤ H)
    (hold : DefectBounds (PhysicalMeanDomain.localSlowStripData U.carrier U.isOpen
      ε L hε hεone hL) σ c u) :
    DefectBounds (PhysicalMeanDomain.localSlowStripData U.carrier U.isOpen
      ε L hε hεone hL) τ c (VariableGaugeMean.temporalStageState g h index axial c u) :=
  defectBounds_after_change _ c u _ hσ hτ hold
    (temporalStage_debt_change_mem U ha hab hcL hcR ε L hε hεone hL g h index axial c u
      hop hb hm hi hW ho hbC hmC hiC hH hκ)


-- @@ L722-722 verbatim
end TemporalNextDebt


-- @@ L724-724 verbatim
end


-- @@ L726-726 verbatim
end NavierStokes.GaugeDebtIncrement
