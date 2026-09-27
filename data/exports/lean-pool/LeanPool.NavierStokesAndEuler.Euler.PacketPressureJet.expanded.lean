/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPointJets
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul


-- @@ L12-12 verbatim
/-! The pressure entry contains only actual space/angle derivatives used by the PDE. -/


-- @@ L14-14 verbatim
section


-- @@ L16-20 verbatim
/-!
Actual PDE jets on a closed time interval.  Time derivatives are within the
interval, while space and angle derivatives are ordinary Fréchet derivatives.
No smooth extension across a time endpoint is assumed.
-/


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
noncomputable section


-- @@ L26-26 verbatim
namespace EulerPacketPointJets


-- @@ L28-28 verbatim
open EulerSmoothLimit EulerFiniteGrades Finset Set


-- @@ L30-31 verbatim
/-- Spatial domain: an abbreviation for `Space × ℝ`. -/
abbrev SpatialDomain := Space × ℝ


-- @@ L33-33 verbatim
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


-- @@ L35-39 verbatim
/-- Join derivative, given by `(ContinuousLinearMap.fst ℝ ℝ SpatialDomain).smulRight v + D.comp
(ContinuousLinearMap.snd ℝ ℝ SpatialDomain)`. -/
def joinDerivative (v : E) (D : SpatialDomain →L[ℝ] E) : Domain →L[ℝ] E :=
  (ContinuousLinearMap.fst ℝ ℝ SpatialDomain).smulRight v +
    D.comp (ContinuousLinearMap.snd ℝ ℝ SpatialDomain)


-- @@ L41-42 verbatim
theorem joinDerivative_apply (v : E) (D : SpatialDomain →L[ℝ] E) (h : Domain) :
    joinDerivative v D h=h.1 • v+D h.2 := rfl


-- @@ L44-48 verbatim
/-- Sliced jet, given by `(f z, joinDerivative (derivWithin (fun t => f (t,z.2)) s z.1) (fderiv
ℝ (fun y => f (z.1,y)) z.2))`. -/
def slicedJet (s : Set ℝ) (f : Domain → E) (z : Domain) : Jet E :=
  (f z, joinDerivative (derivWithin (fun t => f (t,z.2)) s z.1)
    (fderiv ℝ (fun y => f (z.1,y)) z.2))


-- @@ L50-54 verbatim
theorem slicedJet_time (s : Set ℝ) (f : Domain → E) (z : Domain) :
    (slicedJet s f z).2 timeDirection=derivWithin (fun t => f (t,z.2)) s z.1 := by
  change (1 : ℝ) • derivWithin (fun t => f (t,z.2)) s z.1 +
    (fderiv ℝ (fun y => f (z.1,y)) z.2) (0 : SpatialDomain)=_
  simp


-- @@ L56-58 verbatim
theorem slicedJet_space (s : Set ℝ) (f : Domain → E) (z : Domain) (v : Space) :
    (slicedJet s f z).2 (spatialInjection v)=fderiv ℝ (fun y => f (z.1,y)) z.2 (v,0) := by
  simp [slicedJet, joinDerivative, spatialInjection]


-- @@ L60-62 verbatim
theorem slicedJet_angle (s : Set ℝ) (f : Domain → E) (z : Domain) :
    (slicedJet s f z).2 angleDirection=fderiv ℝ (fun y => f (z.1,y)) z.2 (0,1) := by
  simp [slicedJet, joinDerivative, angleDirection]


-- @@ L64-68 verbatim
/-- The time entry is the derivative furnished by the actual interval evolution. -/
theorem slicedJet_time_eq (s : Set ℝ) (f : Domain → E) (z : Domain) (v : E)
    (hs : UniqueDiffWithinAt ℝ s z.1) (ht : HasDerivWithinAt (fun t => f (t, z.2)) v s z.1) :
    (slicedJet s f z).2 timeDirection=v := by
  rw [slicedJet_time, ht.derivWithin hs]


-- @@ L70-103 verbatim
theorem slicedJet_fieldSum (s : Set ℝ) (M : ℕ) (κ : ℝ) (u : ℕ → Domain → E) (z : Domain)
    (hs : UniqueDiffWithinAt ℝ s z.1)
    (ht : ∀ n ≤ M, DifferentiableWithinAt ℝ (fun t => u n (t, z.2)) s z.1)
    (hx : ∀ n ≤ M, DifferentiableAt ℝ (fun y => u n (z.1, y)) z.2) :
    slicedJet s (fieldSum M κ u) z=evaluate M κ (fun n => slicedJet s (u n) z) := by
  have htime := HasDerivWithinAt.fun_sum (u := range (M+1))
    (fun n hn => ((ht n (by have h := mem_range.mp hn; omega)).hasDerivWithinAt).const_smul (κ^n))
  have hspace := HasFDerivAt.fun_sum (u := range (M+1))
    (fun n hn => ((hx n (by have h := mem_range.mp hn; omega)).hasFDerivAt).const_smul (κ^n))
  have hdt : derivWithin (fun t => fieldSum M κ u (t,z.2)) s z.1 =
      ∑ n ∈ range (M+1), κ^n • derivWithin (fun t => u n (t,z.2)) s z.1 := htime.derivWithin hs
  have hdx : fderiv ℝ (fun y => fieldSum M κ u (z.1,y)) z.2 =
      ∑ n ∈ range (M+1), κ^n • fderiv ℝ (fun y => u n (z.1,y)) z.2 := hspace.fderiv
  apply Prod.ext
  · change (∑ n ∈ range (M+1), κ^n • u n z) =
      (AddMonoidHom.fst E (Domain →L[ℝ] E)) (∑ n ∈ range (M+1), κ^n • slicedJet s (u n) z)
    rw [map_sum]
    rfl
  · change joinDerivative _ _ =
      (AddMonoidHom.snd E (Domain →L[ℝ] E)) (∑ n ∈ range (M+1), κ^n • slicedJet s (u n) z)
    rw [hdt, hdx, map_sum]
    change joinDerivative
      (∑ n ∈ range (M+1), κ^n • derivWithin (fun t => u n (t,z.2)) s z.1)
      (∑ n ∈ range (M+1), κ^n • fderiv ℝ (fun y => u n (z.1,y)) z.2) =
      ∑ n ∈ range (M+1), κ^n • joinDerivative
        (derivWithin (fun t => u n (t,z.2)) s z.1) (fderiv ℝ (fun y => u n (z.1,y)) z.2)
    apply ContinuousLinearMap.ext
    intro h
    simp only [joinDerivative_apply, Finset.smul_sum, _root_.sum_apply,
      smul_apply, smul_smul, sum_add_distrib, smul_add]
    congr 1
    apply sum_congr rfl
    intro n _
    rw [mul_comm]


-- @@ L105-105 verbatim
end EulerPacketPointJets


-- @@ L107-107 verbatim
end

-- @@ L108-108 verbatim
end


-- @@ L110-110 verbatim
end


-- @@ L112-112 verbatim
@[expose] public section


-- @@ L114-114 verbatim
noncomputable section


-- @@ L116-116 verbatim
namespace EulerPacketPointJets


-- @@ L118-118 verbatim
open EulerFiniteGrades Finset


-- @@ L120-122 verbatim
/-- The unused time slot is zero: no time derivative of the scalar potential is required. -/
def pressureJet (p : Domain → ℝ) (z : Domain) : ScalarJet :=
  (p z, joinDerivative 0 (fderiv ℝ (fun y => p (z.1,y)) z.2))


-- @@ L124-126 verbatim
theorem pressureJet_space (p : Domain → ℝ) (z : Domain) (v : EulerSmoothLimit.Space) :
    (pressureJet p z).2 (spatialInjection v)=fderiv ℝ (fun y => p (z.1,y)) z.2 (v,0) := by
  simp [pressureJet, joinDerivative, spatialInjection]


-- @@ L128-130 verbatim
theorem pressureJet_angle (p : Domain → ℝ) (z : Domain) :
    (pressureJet p z).2 angleDirection=fderiv ℝ (fun y => p (z.1,y)) z.2 (0,1) := by
  simp [pressureJet, joinDerivative, angleDirection]


-- @@ L132-151 verbatim
theorem pressureJet_fieldSum (M : ℕ) (κ : ℝ) (p : ℕ → Domain → ℝ) (z : Domain)
    (hp : ∀ n ≤ M, DifferentiableAt ℝ (fun y => p n (z.1, y)) z.2) :
    pressureJet (fieldSum M κ p) z=evaluate M κ (fun n => pressureJet (p n) z) := by
  have hspace := HasFDerivAt.fun_sum (u := range (M+1))
    (fun n hn => ((hp n (by have h := mem_range.mp hn; omega)).hasFDerivAt).const_smul (κ^n))
  have hdx : fderiv ℝ (fun y => fieldSum M κ p (z.1,y)) z.2 =
      ∑ n ∈ range (M+1), κ^n • fderiv ℝ (fun y => p n (z.1,y)) z.2 := hspace.fderiv
  apply Prod.ext
  · change (∑ n ∈ range (M+1), κ^n • p n z) =
      (AddMonoidHom.fst ℝ (Domain →L[ℝ] ℝ)) (∑ n ∈ range (M+1), κ^n • pressureJet (p n) z)
    rw [map_sum]
    rfl
  · change joinDerivative 0 _ =
      (AddMonoidHom.snd ℝ (Domain →L[ℝ] ℝ)) (∑ n ∈ range (M+1), κ^n • pressureJet (p n) z)
    rw [hdx, map_sum]
    change joinDerivative 0 (∑ n ∈ range (M+1), κ^n • fderiv ℝ (fun y => p n (z.1,y)) z.2) =
      ∑ n ∈ range (M+1), κ^n • joinDerivative 0 (fderiv ℝ (fun y => p n (z.1,y)) z.2)
    apply ContinuousLinearMap.ext
    intro h
    simp only [joinDerivative_apply, smul_zero, zero_add, _root_.sum_apply, smul_apply]


-- @@ L153-153 verbatim
end EulerPacketPointJets
