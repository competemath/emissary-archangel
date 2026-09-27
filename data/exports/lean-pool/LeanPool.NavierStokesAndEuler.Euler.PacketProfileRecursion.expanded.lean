/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPressureJet
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import LeanPool.NavierStokesAndEuler.Euler.PeriodicDerivativeMean
public import LeanPool.NavierStokesAndEuler.Euler.PacketPointJets
public import LeanPool.NavierStokesAndEuler.Euler.FiniteGradeAlgebra
import LeanPool.NavierStokesAndEuler.Euler.FiniteGradeDiagonal
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise


-- @@ L16-21 verbatim
/-!
The well-founded profile recursion in (14), on literal time/space/angle fields.
Every new mean is computed before the new high coefficient.  The supplied
linear inverse maps are the interface to the analytic source constructions;
this file proves the recursion and its dependence only on earlier grades.
-/


-- @@ L23-23 verbatim
section


-- @@ L25-25 verbatim
/-! The actual nonlinear packet operators have the triangular dependence claimed in (14). -/


-- @@ L27-27 verbatim
section


-- @@ L29-29 verbatim
/-! Which unknown coefficients can enter the slow and fast quadratic terms. -/


-- @@ L31-31 verbatim
@[expose] public section


-- @@ L33-33 verbatim
noncomputable section


-- @@ L35-35 verbatim
namespace EulerFiniteGrades


-- @@ L37-37 verbatim
open Finset


-- @@ L39-40 verbatim
variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]


-- @@ L42-55 verbatim
/-- With zero constant coefficient, the slow grade p depends only on grades below p. -/
theorem convolution_strict_congr (M p : ℕ) (hp : 0 < p) (hMp : p ≤ M)
    (B : V →ₗ[ℝ] V →ₗ[ℝ] W) (u u' : ℕ → V) (hu0 : u 0 = 0)
    (hu : ∀ i < p, u' i = u i) :
    convolution M B u' u' p = convolution M B u u p := by
  rw [convolution_eq_range M p hMp, convolution_eq_range M p hMp]
  apply sum_congr rfl
  intro i hi
  have hi' : i ≤ p := by have h := mem_range.mp hi; omega
  by_cases hi0 : i=0
  · simp only [hi0, hu 0 hp, hu0, map_zero, LinearMap.zero_apply]
  by_cases hip : i=p
  · simp only [hip, Nat.sub_self, hu 0 hp, hu0, map_zero]
  rw [hu i (by omega), hu (p-i) (by omega)]


-- @@ L57-87 verbatim
/-- The fast grade p has exactly two possible dependencies on the new grade p. -/
theorem convolution_next_delta (M p : ℕ) (hp : 2 ≤ p) (hMp : p + 1 ≤ M)
    (B : V →ₗ[ℝ] V →ₗ[ℝ] W) (u u' : ℕ → V) (δ : V) (hu0 : u 0 = 0)
    (hu : ∀ i < p, u' i = u i) (hδ : u' p = u p + δ) :
    convolution M B u' u' (p+1) = convolution M B u u (p+1) +
      B δ (u 1) + B (u 1) δ := by
  rw [convolution_eq_range M (p+1) hMp, convolution_eq_range M (p+1) hMp]
  have hterm : ∀ i ∈ range (p+2),
      B (u' i) (u' (p+1-i)) = B (u i) (u (p+1-i)) +
        (if i=p then B δ (u 1) else 0) + (if i=1 then B (u 1) δ else 0) := by
    intro i hi
    have hi' : i ≤ p+1 := by have h := mem_range.mp hi; omega
    by_cases hi0 : i=0
    · simp [hi0, hu 0 (by omega), hu0, show (0 : ℕ) ≠ p by omega]
    by_cases hiend : i=p+1
    · simp [hiend, hu 0 (by omega), hu0, show p ≠ 0 by omega]
    by_cases hip : i=p
    · simp [hip, hδ, hu 1 (by omega), show p ≠ 1 by omega, map_add,
        LinearMap.add_apply]
    by_cases hi1 : i=1
    · simp [hi1, hδ, hu 1 (by omega), show 1 ≠ p by omega, map_add]
    rw [hu i (by omega), hu (p+1-i) (by omega)]
    simp [hip, hi1]
  calc
    _ = ∑ i ∈ range (p+2),
        (B (u i) (u (p+1-i)) + (if i=p then B δ (u 1) else 0) +
          (if i=1 then B (u 1) δ else 0)) := sum_congr rfl hterm
    _ = _ := by
      rw [sum_add_distrib, sum_add_distrib]
      simp only [sum_ite_eq', mem_range, show p < p+2 by omega,
        show 1 < p+2 by omega, ite_true]


-- @@ L89-89 verbatim
end EulerFiniteGrades


-- @@ L91-91 verbatim
end

-- @@ L92-92 verbatim
end


-- @@ L94-94 verbatim
end


-- @@ L96-96 verbatim
@[expose] public section


-- @@ L98-98 verbatim
noncomputable section


-- @@ L100-100 verbatim
namespace EulerPacketPointJets


-- @@ L102-102 verbatim
open EulerSmoothLimit EulerFiniteGrades InnerProductSpace


-- @@ L104-106 verbatim
theorem fastAdvection_tangent_left (m : Space) (J K : VectorJet)
    (hJ : ⟪m, J.1⟫_ℝ = 0) : fastAdvection m J K=0 := by
  simp [fastAdvection, hJ]


-- @@ L108-110 verbatim
theorem fastAdvection_angleConstant_right (m : Space) (J K : VectorJet)
    (hK : K.2 angleDirection = 0) : fastAdvection m J K=0 := by
  simp [fastAdvection, hK]


-- @@ L112-116 verbatim
/-- Nonlinear grade, given by `convolution M (slowAdvection FInv) u u p + convolution M
(fastAdvection m) u u (p+1)`. -/
def nonlinearGrade (M p : ℕ) (FInv : Space →L[ℝ] Space) (m : Space)
    (u : ℕ → VectorJet) : Space :=
  convolution M (slowAdvection FInv) u u p + convolution M (fastAdvection m) u u (p+1)


-- @@ L118-132 verbatim
/-- Changing the new high coefficient and mean coefficient leaves just the mean-primary interaction.
-/
theorem nonlinearGrade_update (M p : ℕ) (hp : 2 ≤ p) (hMp : p + 1 ≤ M)
    (FInv : Space →L[ℝ] Space) (m : Space) (u u' : ℕ → VectorJet)
    (A B : VectorJet) (hu0 : u 0 = 0) (hu : ∀ i < p, u' i = u i)
    (hnew : u' p = u p + (A + B)) (hprimary : ⟪m, (u 1).1⟫_ℝ = 0)
    (hA : ⟪m, A.1⟫_ℝ = 0) :
    nonlinearGrade M p FInv m u' = nonlinearGrade M p FInv m u + fastAdvection m B (u 1) := by
  unfold nonlinearGrade
  rw [convolution_strict_congr M p (by omega) (by omega) _ u u' hu0 hu,
    convolution_next_delta M p hp hMp _ u u' (A+B) hu0 hu hnew]
  rw [map_add, LinearMap.add_apply,
    fastAdvection_tangent_left m A (u 1) hA,
    fastAdvection_tangent_left m (u 1) (A+B) hprimary]
  simp only [zero_add, add_zero, add_assoc]


-- @@ L134-142 verbatim
/-- The surviving unknown term is literally (m dot B) times the primary angular derivative. -/
theorem nonlinearGrade_update_formula (M p : ℕ) (hp : 2 ≤ p) (hMp : p + 1 ≤ M)
    (FInv : Space →L[ℝ] Space) (m : Space) (u u' : ℕ → VectorJet)
    (A B : VectorJet) (hu0 : u 0 = 0) (hu : ∀ i < p, u' i = u i)
    (hnew : u' p = u p + (A + B)) (hprimary : ⟪m, (u 1).1⟫_ℝ = 0)
    (hA : ⟪m, A.1⟫_ℝ = 0) :
    nonlinearGrade M p FInv m u' = nonlinearGrade M p FInv m u +
      ⟪m, B.1⟫_ℝ • (u 1).2 angleDirection :=
  nonlinearGrade_update M p hp hMp FInv m u u' A B hu0 hu hnew hprimary hA


-- @@ L144-144 verbatim
end EulerPacketPointJets


-- @@ L146-146 verbatim
end

-- @@ L147-147 verbatim
end


-- @@ L149-149 verbatim
end


-- @@ L151-151 verbatim
section


-- @@ L153-153 verbatim
/-! The known forcing at a recursive grade uses only previously constructed coefficients. -/


-- @@ L155-155 verbatim
@[expose] public section


-- @@ L157-157 verbatim
noncomputable section


-- @@ L159-159 verbatim
namespace EulerPacketPointJets


-- @@ L161-161 verbatim
open EulerSmoothLimit EulerFiniteGrades InnerProductSpace


-- @@ L163-165 verbatim
/-- History, with branches according to `i<p`. -/
def history (p : ℕ) (u : ℕ → VectorJet) (previousCorrector : VectorJet) (i : ℕ) : VectorJet :=
  if i<p then u i else if i=p then previousCorrector else 0


-- @@ L167-173 verbatim
/-- No unspecified coefficient at or above p enters the known part. -/
theorem history_congr (p : ℕ) (u v : ℕ → VectorJet) (c : VectorJet)
    (huv : ∀ i < p, u i = v i) : history p u c=history p v c := by
  funext i
  by_cases hi : i<p
  · simp only [history, hi, ite_true, huv i hi]
  · simp only [history, hi, ite_false]


-- @@ L175-189 verbatim
/-- The only new nonlinear term is the mean coefficient against the primary angular derivative. -/
theorem nonlinearGrade_eq_history (M p : ℕ) (hp : 2 ≤ p) (hMp : p + 1 ≤ M)
    (FInv : Space →L[ℝ] Space) (m : Space) (u : ℕ → VectorJet)
    (A B c : VectorJet) (hu0 : u 0 = 0) (hnew : u p = c + (A + B))
    (hprimary : ⟪m, (u 1).1⟫_ℝ = 0) (hA : ⟪m, A.1⟫_ℝ = 0) :
    nonlinearGrade M p FInv m u = nonlinearGrade M p FInv m (history p u c) +
      fastAdvection m B (u 1) := by
  have h0 : history p u c 0=0 := by simp [history, show 0<p by omega, hu0]
  have h1 : history p u c 1=u 1 := by simp [history, show 1<p by omega]
  have hsame : ∀ i<p, u i=history p u c i := by
    intro i hi
    simp [history, hi]
  have hnew' : u p=history p u c p+(A+B) := by simpa [history] using hnew
  simpa only [h1] using nonlinearGrade_update M p hp hMp FInv m (history p u c) u A B
    h0 hsame hnew' (by simpa only [h1] using hprimary) hA


-- @@ L191-197 verbatim
/-- The unknown mean-primary interaction has exactly zero angular mean. -/
theorem mean_primary_interaction_zero (P : ℝ) (m B : Space) (A Aθ : ℝ → Space)
    (hA : ∀ θ, HasDerivAt A (Aθ θ) θ) (hAθ : Continuous Aθ)
    (hper : Function.Periodic A P) :
    (∫ θ in 0..P, ⟪m,B⟫_ℝ • Aθ θ)=0 :=
  EulerPeriodicDerivativeMean.integral_constant_smul_derivative_eq_zero P ⟪m,B⟫_ℝ
    A Aθ hA hAθ hper


-- @@ L199-199 verbatim
end EulerPacketPointJets


-- @@ L201-201 verbatim
end

-- @@ L202-202 verbatim
end


-- @@ L204-204 verbatim
end


-- @@ L206-206 verbatim
@[expose] public section


-- @@ L208-208 verbatim
noncomputable section


-- @@ L210-210 verbatim
namespace EulerPacketProfileRecursion


-- @@ L212-212 verbatim
open EulerSmoothLimit EulerPacketPointJets Set


-- @@ L214-215 verbatim
/-- Vector field: an abbreviation for `Domain → Space`. -/
abbrev VectorField := Domain → Space

-- @@ L216-217 verbatim
/-- Scalar field: an abbreviation for `Domain → ℝ`. -/
abbrev ScalarField := Domain → ℝ


-- @@ L219-231 verbatim
/-- Profile data, collecting `high`, `mean`, `corrector`, `highPressure`, `meanPressure`,
`instance`. -/
structure Profile where
  /-- High-frequency field of `Profile`, of type `VectorField`. -/
  high : VectorField
  /-- Mean field of `Profile`, of type `VectorField`. -/
  mean : VectorField
  /-- Correction field of `Profile`, of type `VectorField`. -/
  corrector : VectorField
  /-- High-frequency pressure of `Profile`, of type `ScalarField`. -/
  highPressure : ScalarField
  /-- Mean pressure of `Profile`, of type `ScalarField`. -/
  meanPressure : ScalarField


-- @@ L233-233 verbatim
instance : Zero Profile := ⟨⟨0,0,0,0,0⟩⟩


-- @@ L235-253 verbatim
/-- Operators data, collecting `interval`, `period`, `inverseFrame`, `strain`, `normal`,
`meanSolve` and their compatibility conditions. -/
structure Operators where
  /-- Interval of `Operators`, of type `Set ℝ`. -/
  interval : Set ℝ
  /-- Period of `Operators`, of type `ℝ`. -/
  period : ℝ
  /-- Inverse frame of `Operators`, of type `Domain → Space →L[ℝ] Space`. -/
  inverseFrame : Domain → Space →L[ℝ] Space
  /-- Strain of `Operators`, of type `Domain → Space →L[ℝ] Space`. -/
  strain : Domain → Space →L[ℝ] Space
  /-- Normal of `Operators`, of type `VectorField`. -/
  normal : VectorField
  /-- Mean solve of `Operators`, of type `VectorField → VectorField × ScalarField`. -/
  meanSolve : VectorField → VectorField × ScalarField
  /-- High solve of `Operators`, of type `VectorField → VectorField × ScalarField`. -/
  highSolve : VectorField → VectorField × ScalarField
  /-- Curl corrector of `Operators`, of type `VectorField → VectorField`. -/
  curlCorrector : VectorField → VectorField


-- @@ L255-257 verbatim
/-- Literal angular averaging at each time and spatial label. -/
def angleMean (P : ℝ) (f : VectorField) : VectorField :=
  fun z => P⁻¹ • ∫ θ in 0..P, f (z.1,(z.2.1,θ))


-- @@ L259-262 verbatim
/-- The stored coefficients determine the jets of V_i=A_i+B_i+C_{i-1}. -/
def velocityJet (s : Set ℝ) (a : ℕ → Profile) (z : Domain) (i : ℕ) : VectorJet :=
  if i=0 then 0 else slicedJet s (a i).high z+slicedJet s (a i).mean z +
    slicedJet s (a (i-1)).corrector z


-- @@ L264-267 verbatim
/-- Known jets, given by `history p (velocityJet O.interval a z) (slicedJet O.interval (a
(p-1)).corrector z)`. -/
def knownJets (O : Operators) (p : ℕ) (a : ℕ → Profile) (z : Domain) : ℕ → VectorJet :=
  history p (velocityJet O.interval a z) (slicedJet O.interval (a (p-1)).corrector z)


-- @@ L269-273 verbatim
/-- All terms of the grade-p forcing that are already determined. -/
def knownForce (O : Operators) (p : ℕ) (a : ℕ → Profile) : VectorField :=
  fun z => -(linearPart (O.strain z) (slicedJet O.interval (a (p-1)).corrector z) +
    slowPressure (O.inverseFrame z) (pressureJet (a (p-1)).highPressure z) +
    nonlinearGrade (p+1) p (O.inverseFrame z) (O.normal z) (knownJets O p a z))


-- @@ L275-277 verbatim
/-- Mean force, given by `angleMean O.period (knownForce O p a)`. -/
def meanForce (O : Operators) (p : ℕ) (a : ℕ → Profile) : VectorField :=
  angleMean O.period (knownForce O p a)


-- @@ L279-281 verbatim
/-- Mean result, given by `O.meanSolve (meanForce O p a)`. -/
def meanResult (O : Operators) (p : ℕ) (a : ℕ → Profile) : VectorField × ScalarField :=
  O.meanSolve (meanForce O p a)


-- @@ L283-287 verbatim
/-- The sole new mean-primary interaction is added after solving the mean. -/
def highForce (O : Operators) (p : ℕ) (a : ℕ → Profile) : VectorField :=
  fun z => knownForce O p a z-meanForce O p a z -
    fastAdvection (O.normal z) (slicedJet O.interval (meanResult O p a).1 z)
      (slicedJet O.interval (a 1).high z)


-- @@ L289-294 verbatim
/-- Step, given by `let b := meanResult O p a let h := O.highSolve (highForce O p a)
⟨h.1,b.1,O.curlCorrector h.1,h.2,b.2⟩`. -/
def step (O : Operators) (p : ℕ) (a : ℕ → Profile) : Profile :=
  let b := meanResult O p a
  let h := O.highSolve (highForce O p a)
  ⟨h.1,b.1,O.curlCorrector h.1,h.2,b.2⟩


-- @@ L296-301 verbatim
theorem velocityJet_congr (s : Set ℝ) (p : ℕ) (a b : ℕ → Profile)
    (h : ∀ i < p, a i = b i) (z : Domain) (i : ℕ) (hi : i < p) :
    velocityJet s a z i=velocityJet s b z i := by
  by_cases hz : i=0
  · simp only [velocityJet, hz, ite_true]
  · simp only [velocityJet, hz, ite_false, h i hi, h (i-1) (by omega)]


-- @@ L303-307 verbatim
theorem knownJets_congr (O : Operators) (p : ℕ) (hp : 1 ≤ p) (a b : ℕ → Profile)
    (h : ∀ i < p, a i = b i) (z : Domain) : knownJets O p a z=knownJets O p b z := by
  unfold knownJets
  rw [h (p-1) (by omega)]
  exact history_congr p _ _ _ (fun i hi => velocityJet_congr O.interval p a b h z i hi)


-- @@ L309-313 verbatim
theorem knownForce_congr (O : Operators) (p : ℕ) (hp : 1 ≤ p) (a b : ℕ → Profile)
    (h : ∀ i < p, a i = b i) : knownForce O p a=knownForce O p b := by
  funext z
  unfold knownForce
  rw [h (p-1) (by omega), knownJets_congr O p hp a b h z]


-- @@ L315-323 verbatim
/-- At p≥2 the complete new profile depends only on the strict prefix. -/
theorem step_congr (O : Operators) (p : ℕ) (hp : 2 ≤ p) (a b : ℕ → Profile)
    (h : ∀ i < p, a i = b i) : step O p a=step O p b := by
  have hf := knownForce_congr O p (by omega) a b h
  have h₁ := h 1 (by omega)
  have hh : highForce O p a=highForce O p b := by
    funext z
    simp only [highForce, meanResult, meanForce, hf, h₁]
  simp only [step, meanResult, meanForce, hf, hh]


-- @@ L325-329 verbatim
/-- Recursion step, with branches according to `p=0`. -/
def recursionStep (O : Operators) (primary : Profile) (p : ℕ)
    (a : (i : ℕ) → i < p → Profile) : Profile :=
  if p=0 then 0 else if p=1 then primary else
    step O p (fun i => if hi : i<p then a i hi else 0)


-- @@ L331-333 verbatim
/-- All finite profile families are restrictions of this one well-founded sequence. -/
def profiles (O : Operators) (primary : Profile) : ℕ → Profile :=
  Nat.strongRec (recursionStep O primary)


-- @@ L335-337 verbatim
theorem profiles_unfold (O : Operators) (primary : Profile) (p : ℕ) :
    profiles O primary p=recursionStep O primary p (fun i _ => profiles O primary i) :=
  Nat.strongRec_eq (recursionStep O primary) p


-- @@ L339-341 verbatim
@[simp] theorem profiles_zero (O : Operators) (primary : Profile) : profiles O primary 0=0 := by
  rw [profiles_unfold]
  simp only [recursionStep, ite_true]


-- @@ L343-346 verbatim
@[simp] theorem profiles_one (O : Operators) (primary : Profile) : profiles O primary 1=primary :=
    by
  rw [profiles_unfold]
  simp only [recursionStep, one_ne_zero, ite_false, ite_true]


-- @@ L348-355 verbatim
/-- This is an actual recursive construction, not an existence assumption on profiles. -/
theorem profiles_step (O : Operators) (primary : Profile) (p : ℕ) (hp : 2 ≤ p) :
    profiles O primary p=step O p (profiles O primary) := by
  rw [profiles_unfold]
  simp only [recursionStep, show p ≠ 0 by omega, show p ≠ 1 by omega, ite_false]
  apply step_congr O p hp
  intro i hi
  simp only [dite_eq_left hi]


-- @@ L357-360 verbatim
theorem profiles_mean (O : Operators) (primary : Profile) (p : ℕ) (hp : 2 ≤ p) :
    (profiles O primary p).mean=(meanResult O p (profiles O primary)).1 := by
  rw [profiles_step O primary p hp]
  rfl


-- @@ L362-365 verbatim
theorem profiles_high (O : Operators) (primary : Profile) (p : ℕ) (hp : 2 ≤ p) :
    (profiles O primary p).high=(O.highSolve (highForce O p (profiles O primary))).1 := by
  rw [profiles_step O primary p hp]
  rfl


-- @@ L367-370 verbatim
theorem profiles_corrector (O : Operators) (primary : Profile) (p : ℕ) (hp : 2 ≤ p) :
    (profiles O primary p).corrector=O.curlCorrector (profiles O primary p).high := by
  rw [profiles_step O primary p hp]
  rfl


-- @@ L372-372 verbatim
end EulerPacketProfileRecursion
