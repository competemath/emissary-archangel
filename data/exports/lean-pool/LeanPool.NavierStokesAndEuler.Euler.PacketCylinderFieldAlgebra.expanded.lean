/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderField
public import LeanPool.NavierStokesAndEuler.Euler.ClassicalPressureCurl


-- @@ L12-12 verbatim
/-! Finite algebra on actual cylinder-path witnesses of raw packet fields. -/


-- @@ L14-14 verbatim
@[expose] public section



-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
namespace EulerPacketCylinderField.Field


-- @@ L21-23 verbatim
open Set MeasureTheory ContinuousLinearMap Finset EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSmoothOrbit EulerLpCylinderTranslation EulerMetricTransport
      EulerPacketProfileRecursion

-- @@ L24-24 verbatim
open scoped ContDiff


-- @@ L26-26 verbatim
variable {P T : ℝ} [Fact (0 < P)] {raw raw' : VectorField}


-- @@ L28-39 verbatim
/-- Recover a raw witness from an actual continuous representative of its L² path. -/
def ofLifted (p : C(Icc (0 : ℝ) T, LiftL2 P))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
    (f : Icc (0 : ℝ) T → LiftDomain P → Space) (hc : ∀ t, Continuous (f t))
    (hrep : ∀ t, (p t : LiftDomain P → Space) =ᵐ[liftMeasure P] f t)
    (he : ∀ (t : Icc (0 : ℝ) T) x θ, raw (t,(x,θ)) = f t (x,(θ : AddCircle P))) :
    Field P T raw where
  path := p
  orbit := hp
  raw_eq t x θ := (he t x θ).trans (congrFun
    (Measure.eq_of_ae_eq ((hrep t).symm.trans (pointField_ae P p hp t))
      (hc t) (smoothField_continuous P _ (pointField_smooth P p hp t))) (x,(θ : AddCircle P)))


-- @@ L41-47 verbatim
/-- Equality is needed only on the actual closed time interval. -/
def congr (G : Field P T raw)
    (he : ∀ (t : Icc (0 : ℝ) T) x θ, raw' (t, (x, θ)) = raw (t, (x, θ))) :
    Field P T raw' where
  path := G.path
  orbit := G.orbit
  raw_eq t x θ := (he t x θ).trans (G.raw_eq t x θ)


-- @@ L49-54 verbatim
/-- Zero, constructed using `ofLifted`. -/
def zero (P T : ℝ) [Fact (0 < P)] : Field P T (0 : VectorField) :=
  ofLifted 0 (by simpa only [map_zero] using (contDiff_const :
      ContDiff ℝ ∞ (fun _ : LiftTangent => (0 : C(Icc (0 : ℝ) T,LiftL2 P)))))
    (fun _ _ => 0) (fun _ => continuous_const)
    (fun _ => Lp.coeFn_zero Space 2 (liftMeasure P)) (fun _ _ _ => rfl)


-- @@ L56-66 verbatim
/-- Add, constructed using `ofLifted`. -/
def add (G : Field P T raw) (H : Field P T raw') : Field P T (raw+raw') :=
  ofLifted (G.path+H.path) (by simpa only [map_add] using G.orbit.add H.orbit)
    (fun t x => pointField P G.path G.orbit t x+pointField P H.path H.orbit t x)
    (fun t => (smoothField_continuous P _ (pointField_smooth P G.path G.orbit t)).add
      (smoothField_continuous P _ (pointField_smooth P H.path H.orbit t)))
    (fun t => by
      filter_upwards [Lp.coeFn_add (G.path t) (H.path t),pointField_ae P G.path G.orbit t,
        pointField_ae P H.path H.orbit t] with x ha hg hh
      exact ha.trans (congrArg₂ (·+·) hg hh))
    (fun t x θ => by simp only [Pi.add_apply,G.raw_eq,H.raw_eq])


-- @@ L68-76 verbatim
/-- Neg, constructed using `ofLifted`. -/
def neg (G : Field P T raw) : Field P T (-raw) :=
  ofLifted (-G.path) (by simpa only [map_neg] using G.orbit.neg)
    (fun t x => -pointField P G.path G.orbit t x)
    (fun t => (smoothField_continuous P _ (pointField_smooth P G.path G.orbit t)).neg)
    (fun t => by
      filter_upwards [Lp.coeFn_neg (G.path t),pointField_ae P G.path G.orbit t] with x hn hg
      exact hn.trans (congrArg Neg.neg hg))
    (fun t x θ => by simp only [Pi.neg_apply,G.raw_eq])


-- @@ L78-80 verbatim
/-- Sub, given by `(G.add H.neg).congr (fun t x θ => by simp only [sub_eq_add_neg])`. -/
def sub (G : Field P T raw) (H : Field P T raw') : Field P T (raw-raw') :=
  (G.add H.neg).congr (fun t x θ => by simp only [sub_eq_add_neg])


-- @@ L82-90 verbatim
/-- Smul, constructed using `ofLifted`. -/
def smul (G : Field P T raw) (c : ℝ) : Field P T (c • raw) :=
  ofLifted (c • G.path) (by simpa only [map_smul] using G.orbit.const_smul c)
    (fun t x => c • pointField P G.path G.orbit t x)
    (fun t => (smoothField_continuous P _ (pointField_smooth P G.path G.orbit t)).const_smul c)
    (fun t => by
      filter_upwards [Lp.coeFn_smul c (G.path t),pointField_ae P G.path G.orbit t] with x hs hg
      exact hs.trans (congrArg (c • ·) hg))
    (fun t x θ => by simp only [Pi.smul_apply,G.raw_eq])


-- @@ L92-111 verbatim
/-- Literal finite raw sums have a single actual continuous L² witness. -/
def finsetSum {ι : Type*} (s : Finset ι) (f : ι → VectorField)
    (G : ∀ i, Field P T (f i)) : Field P T (∑ i ∈ s, f i) :=
  ofLifted (∑ i ∈ s, (G i).path)
    (by simpa only [map_sum] using ContDiff.sum (fun i _ => (G i).orbit))
    (fun t x => ∑ i ∈ s, pointField P (G i).path (G i).orbit t x)
    (fun t => continuous_finsetSum s (fun i _ =>
      smoothField_continuous P _ (pointField_smooth P (G i).path (G i).orbit t)))
    (fun t => by
      have he : (∑ i ∈ s, (G i).path) t = ∑ i ∈ s, (G i).path t :=
        map_sum (ContinuousMap.evalCLM ℝ t) (fun i => (G i).path) s
      have hall : ∀ᵐ x ∂liftMeasure P, ∀ i ∈ s,
          (G i).path t x = pointField P (G i).path (G i).orbit t x :=
        (Filter.eventually_all_finset s).mpr (fun i _ => pointField_ae P (G i).path (G i).orbit t)
      filter_upwards [Lp.coeFn_fun_finsetSum s (fun i => (G i).path t),hall] with x hs hg
      exact (congrArg (fun u : LiftL2 P => u x) he).trans
        (hs.trans (sum_congr rfl (fun i hi => hg i hi))))
    (fun t x θ => by
      rw [Finset.sum_apply]
      exact sum_congr rfl (fun i _ => (G i).raw_eq t x θ))


-- @@ L113-114 verbatim
@[simp] theorem add_path (G : Field P T raw) (H : Field P T raw') :
    (G.add H).path = G.path+H.path := rfl


-- @@ L116-116 verbatim
@[simp] theorem neg_path (G : Field P T raw) : (G.neg).path = -G.path := rfl


-- @@ L118-118 verbatim
@[simp] theorem smul_path (G : Field P T raw) (c : ℝ) : (G.smul c).path = c • G.path := rfl


-- @@ L120-120 verbatim
end EulerPacketCylinderField.Field
