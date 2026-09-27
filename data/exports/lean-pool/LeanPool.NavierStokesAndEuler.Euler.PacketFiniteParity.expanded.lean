/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileParity
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderHighParity
public import LeanPool.NavierStokesAndEuler.Euler.PacketRecursiveCancellation
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderTimeParity
import LeanPool.NavierStokesAndEuler.Euler.PacketResidualTailFields


-- @@ L15-16 verbatim
/-! Actual finite packet velocities and residual tails preserve the joint
odd parity of the constructed profiles. -/


-- @@ L18-18 verbatim
@[expose] public section



-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
namespace EulerPacketCylinderField


-- @@ L25-26 verbatim
open Set Finset ContinuousLinearMap EulerSmoothLimit EulerPacketPointJets
  EulerPacketProfileRecursion EulerFiniteGrades


-- @@ L28-28 verbatim
namespace JointOdd


-- @@ L30-30 verbatim
variable {T : ℝ} {f : VectorField}


-- @@ L32-35 verbatim
theorem smul (hf : JointOdd T f) (c : ℝ) : JointOdd T (c • f) := by
  intro t x θ
  change c • f (t,(-x,-θ)) = -(c • f (t,(x,θ)))
  rw [hf,smul_neg]


-- @@ L37-41 verbatim
theorem sum {ι : Type*} (s : Finset ι) (f : ι → VectorField)
    (hf : ∀ i ∈ s, JointOdd T (f i)) : JointOdd T (fun z => ∑ i ∈ s, f i z) := by
  intro t x θ
  rw [← sum_neg_distrib]
  exact sum_congr rfl (fun i hi => hf i hi t x θ)


-- @@ L43-48 verbatim
theorem matrix_apply (hf : JointOdd T f) (A : Domain → Space →L[ℝ] Space)
    (hA : ∀ (t : Icc (0 : ℝ) T) x θ, A (t, (-x, -θ)) = A (t, (x, θ))) :
    JointOdd T (fun z => A z (f z)) := by
  intro t x θ
  change A (t,(-x,-θ)) (f (t,(-x,-θ))) = -(A (t,(x,θ)) (f (t,(x,θ))))
  rw [hA,hf,map_neg]


-- @@ L50-57 verbatim
theorem truncate (N : ℕ) (f : ℕ → VectorField)
    (hf : ∀ i, i ≤ N → JointOdd T (f i)) (i : ℕ) :
    JointOdd T (EulerFiniteGrades.truncate N f i) := by
  by_cases hi : i ≤ N
  · rw [truncate_of_le N i f hi]
    exact hf i hi
  · rw [truncate_of_gt N i f (by omega)]
    exact JointOdd.zero T


-- @@ L59-66 verbatim
theorem assemble (N : ℕ) (f c : ℕ → VectorField)
    (hf : ∀ i, i ≤ N → JointOdd T (f i)) (hc : ∀ i, i ≤ N → JointOdd T (c i))
    (i : ℕ) : JointOdd T (EulerFiniteGrades.assemble N f c i) := by
  cases i with
  | zero =>
    simpa only [EulerFiniteGrades.assemble,shiftUp,add_zero] using JointOdd.truncate N f hf 0
  | succ i =>
    exact (JointOdd.truncate N f hf (i+1)).add (JointOdd.truncate N c hc i)


-- @@ L68-71 verbatim
theorem fieldSum (N : ℕ) (κ : ℝ) (f : ℕ → VectorField)
    (hf : ∀ i, i ≤ N → JointOdd T (f i)) : JointOdd T (EulerPacketPointJets.fieldSum N κ f) :=
  JointOdd.sum (range (N+1)) (fun i => κ^i • f i)
    (fun i hi => (hf i (by have := mem_range.mp hi; omega)).smul (κ^i))


-- @@ L73-73 verbatim
end JointOdd


-- @@ L75-75 verbatim
variable {P T : ℝ} [Fact (0 < P)]


-- @@ L77-88 verbatim
theorem Field.linearPart_odd {f ft : VectorField} (G : Field P T f)
    (Gt : Field P T ft) (hT : 0 < T) (hdt : TimeDerivative hT.le G Gt)
    (hf : JointOdd T f) (M : Domain → Space →L[ℝ] Space)
    (hM : ∀ (t : Icc (0 : ℝ) T) x θ, M (t, (-x, -θ)) = M (t, (x, θ))) :
    JointOdd T (fun z => EulerPacketPointJets.linearPart (M z) (slicedJet (Icc (0 : ℝ) T) f z)) :=
        by
  have ht := G.timeDerivative_odd Gt hT hdt hf
  intro t x θ
  change (slicedJet (Icc (0 : ℝ) T) f (t,(-x,-θ))).2 timeDirection +
      M (t,(-x,-θ)) (f (t,(-x,-θ))) =
    -((slicedJet (Icc (0 : ℝ) T) f (t,(x,θ))).2 timeDirection + M (t,(x,θ)) (f (t,(x,θ))))
  simp only [G.slicedJet_temporal hT Gt hdt,ht t x θ,hM t x θ,hf t x θ,map_neg,neg_add]


-- @@ L90-97 verbatim
theorem slowPressure_odd (f : ScalarField) (I : Domain → Space →L[ℝ] Space)
    (hf : JointOdd T (pressureGradient f))
    (hI : ∀ (t : Icc (0 : ℝ) T) x θ, I (t, (-x, -θ)) = I (t, (x, θ))) :
    JointOdd T (fun z => slowPressure (I z) (pressureJet f z)) := by
  intro t x θ
  change (I (t,(-x,-θ))).adjoint (pressureGradient f (t,(-x,-θ))) =
    -((I (t,(x,θ))).adjoint (pressureGradient f (t,(x,θ))))
  rw [hI,hf,map_neg]


-- @@ L99-99 verbatim
variable {O : Operators} {p : ℕ} {a : ℕ → Profile}


-- @@ L101-109 verbatim
theorem PrefixFields.nonlinearGrade_odd (F : PrefixFields P T p a) (H : PrefixOdd T p a)
    (hp : 1 ≤ p) (E : CoefficientEven T O) (M n : ℕ) :
    JointOdd T (fun z => nonlinearGrade M n (O.inverseFrame z) (O.normal z) (knownJets O p a z)) :=
        by
  have hs (i j : ℕ) := (F.knownJet O hp j).slowAdvection_odd O.inverseFrame E.inverse
    (H.knownJet_value_odd (O := O) hp i) (H.knownJet_value_odd (O := O) hp j)
  have ha (i j : ℕ) := (F.knownJet O hp j).fastAdvection_odd O.normal E.normal
    (H.knownJet_value_odd (O := O) hp i) (H.knownJet_value_odd (O := O) hp j)
  exact (JointOdd.convolution M n _ hs).add (JointOdd.convolution M (n+1) _ ha)


-- @@ L111-111 verbatim
namespace ProfileParity


-- @@ L113-113 verbatim
variable {N : ℕ} (H : ∀ i, i ≤ N → ProfileParity T (a i))


-- @@ L115-115 verbatim
include H


-- @@ L117-119 verbatim
theorem assembledVelocity_odd (i : ℕ) : JointOdd T (assembledVelocity N a i) :=
  JointOdd.assemble N _ _ (fun j hj => (H j hj).high.add (H j hj).mean)
    (fun j hj => (H j hj).corrector) i


-- @@ L121-122 verbatim
theorem velocity_odd (κ : ℝ) : JointOdd T (fieldSum (N+1) κ (assembledVelocity N a)) :=
  JointOdd.fieldSum (N+1) κ _ (fun i _ => assembledVelocity_odd H i)


-- @@ L124-124 verbatim
end ProfileParity


-- @@ L126-126 verbatim
namespace ProfileRegularity


-- @@ L128-131 verbatim
variable {N : ℕ} {S : Set Space} (hT : 0 < T)
  (G : ∀ i, i ≤ N → ProfileRegularity P T hT.le S (a i))
  (H : ∀ i, i ≤ N → ProfileParity T (a i)) (C : CoefficientData P T O)
  (E : CoefficientEven T O) (ha : a 0 = 0)


-- @@ L133-133 verbatim
include hT G H C E ha


-- @@ L135-156 verbatim
theorem recursiveTail_odd (n : ℕ) (hn : N + 1 ≤ n) :
    JointOdd T (fun z => recursiveGrade O N a z n) := by
  let F := prefixThrough hT G
  let Hpre : PrefixOdd T (N+1) a :=
    ProfileParity.prefixOdd (fun i (hi : i < N+1) => H i (by omega))
  have hL : JointOdd T (fun z =>
      linearPart (O.strain z) (slicedJet O.interval (a N).corrector z)) := by
    rw [C.interval_eq]
    exact (G N le_rfl).corrector.linearPart_odd (G N le_rfl).correctorDerivative hT
      (G N le_rfl).corrector_time (H N le_rfl).corrector O.strain E.strain
  have hQ := slowPressure_odd (a N).highPressure O.inverseFrame (H N le_rfl).pressure E.inverse
  have hlinear : JointOdd T (fun z => if n=N+1 then
      linearPart (O.strain z) (slicedJet O.interval (a N).corrector z) +
      slowPressure (O.inverseFrame z) (pressureJet (a N).highPressure z) else 0) := by
    intro t x θ
    by_cases he : n=N+1
    · simp only [he,ite_true]
      exact (hL.add hQ) t x θ
    · simp only [he,ite_false,neg_zero]
  have hnonlinear := F.nonlinearGrade_odd Hpre (by omega) E (N+1) n
  exact (hlinear.add hnonlinear).congr
    (fun t x θ => recursiveGrade_tail O N n hn a ha (t,(x,θ)))


-- @@ L158-161 verbatim
theorem residualTail_odd (κ : ℝ) :
    JointOdd T (fun z => ∑ n ∈ Ico (N+1) (2*N+3), κ^n • recursiveGrade O N a z n) :=
  JointOdd.sum (Ico (N+1) (2*N+3)) (fun n => κ^n • (fun z => recursiveGrade O N a z n))
    (fun n hn => (recursiveTail_odd hT G H C E ha n (mem_Ico.mp hn).1).smul (κ^n))


-- @@ L163-163 verbatim
end ProfileRegularity

-- @@ L164-164 verbatim
end EulerPacketCylinderField
