/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketScaledVelocity
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketBridge
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketRay
import LeanPool.NavierStokesAndEuler.Euler.ClosedIntervalDerivativeExtension


-- @@ L17-17 verbatim
/-! Related estimates used together by the same construction modules. -/


-- @@ L19-19 verbatim
section


-- @@ L21-25 verbatim
/-!
The actual scaled velocity supplies the first two equations and the scalar
flux equation used in amplification.  Only the first two transport rows are
relevant; the auxiliary third row in the scalar estimate is filled explicitly.
-/


-- @@ L27-27 verbatim
@[expose] public section


-- @@ L29-29 verbatim
noncomputable section


-- @@ L31-31 verbatim
namespace EulerPacketMovingFrame


-- @@ L33-34 verbatim
open Set EulerSmoothLimit EulerPacketNormalizedPrimary EulerPacketRay
  EulerPacketBridge InnerProductSpace


-- @@ L36-38 verbatim
/-- A harmless third-row extension of a two-row transport matrix. -/
def firstTwoRows (C : Fin 3 → Fin 3 → ℝ) (i j : Fin 3) : ℝ :=
  if i = 0 then C 0 j else C 1 j


-- @@ L40-44 verbatim
theorem velocityFirstRhs_firstTwoRows (A C : Fin 3 → Fin 3 → ℝ)
    (ε P Q N U V : ℝ) :
    velocityFirstRhs A (firstTwoRows C) ε P Q N U V =
      velocityFirstRhs A C ε P Q N U V := by
  simp [velocityFirstRhs, firstTwoRows]


-- @@ L46-50 verbatim
theorem velocitySecondRhs_firstTwoRows (A C : Fin 3 → Fin 3 → ℝ)
    (ε P Q N U V : ℝ) :
    velocitySecondRhs A (firstTwoRows C) ε P Q N U V =
      velocitySecondRhs A C ε P Q N U V := by
  simp [velocitySecondRhs, firstTwoRows]


-- @@ L52-76 verbatim
/-- The scalar error estimate needs no assumption on the physical third
transport row. -/
theorem velocity_rhs_error_firstTwo
    {A C : Fin 3 → Fin 3 → ℝ} {Θ e ε β P Q N P₀ Q₀ U V : ℝ}
    (hΘ : 1 ≤ Θ) (he : 0 ≤ e) (hε : 0 ≤ ε) (hεe : ε ≤ e)
    (hsmall : 10000 * e * Θ ^ 5 ≤ 1) (hβ : |β| ≤ 1)
    (hA : ∀ i j, |A i j - idealVelocityEntry β i j| ≤ 3 * e)
    (hC : ∀ j, |C 0 j - idealUnprojectedEntry 0 j| ≤ 5 * e ∧
      |C 1 j - idealUnprojectedEntry 1 j| ≤ 5 * e)
    (hP₀ : |P₀| ≤ Θ ^ 2) (hQ₀ : |Q₀| ≤ 2 * Θ ^ 2)
    (hP : |P - P₀| ≤ 800 * e * Θ ^ 5)
    (hQ : |Q - Q₀| ≤ 800 * e * Θ ^ 5)
    (hN : |N - 1| ≤ 800 * e * Θ ^ 5) :
    |velocityFirstRhs A C ε P Q N U V -
        (-2 * V + 2 * P₀ * ((P₀ + β) * V + Q₀ * U) / (1 + P₀ ^ 2))| +
      |velocitySecondRhs A C ε P Q N U V + U| ≤
        200000 * e * Θ ^ 12 * (|U| + |V|) := by
  have hC' : ∀ i j, |firstTwoRows C i j - idealUnprojectedEntry i j| ≤ 5 * e := by
    intro i j
    fin_cases i
    · simpa [firstTwoRows] using (hC j).1
    · simpa [firstTwoRows] using (hC j).2
    · simpa [firstTwoRows, idealUnprojectedEntry] using (hC j).2
  simpa only [velocityFirstRhs_firstTwoRows, velocitySecondRhs_firstTwoRows] using
    velocity_rhs_error hΘ he hε hεe hsmall hβ hA hC' hP₀ hQ₀ hP hQ hN


-- @@ L78-111 verbatim
/-- The actual tangency constraint removes the third scaled coordinate. -/
theorem scaledVelocity_firstTwo_hasDerivWithinAt (B M : Space →L[ℝ] Space)
    {m v r w : ℝ → Space} {s₀ t₀ a ε τ : ℝ} {S U : Set ℝ}
    (ha : a ≠ 0) (hε : ε ≠ 0) (hs₀ : s₀ ≠ 0)
    (hmap : MapsTo (physicalTime t₀ a ε) U S)
    (hm : HasDerivWithinAt m (-B.adjoint (m (physicalTime t₀ a ε τ))) S (physicalTime t₀ a ε τ))
    (hv : HasDerivWithinAt v (-B (v (physicalTime t₀ a ε τ)) +
      (2 * ⟪m (physicalTime t₀ a ε τ), B (v (physicalTime t₀ a ε τ))⟫_ℝ /
        ‖m (physicalTime t₀ a ε τ)‖ ^ 2) • m (physicalTime t₀ a ε τ)) S (physicalTime t₀ a ε τ))
    (hw : HasDerivWithinAt w (-M (w (physicalTime t₀ a ε τ)) +
      (2 * ⟪r (physicalTime t₀ a ε τ), M (w (physicalTime t₀ a ε τ))⟫_ℝ /
        ‖r (physicalTime t₀ a ε τ)‖ ^ 2) • r (physicalTime t₀ a ε τ)) S (physicalTime t₀ a ε τ))
    (hm0 : m (physicalTime t₀ a ε τ) ≠ 0) (hv0 : v (physicalTime t₀ a ε τ) ≠ 0)
    (hmv : ⟪m (physicalTime t₀ a ε τ), v (physicalTime t₀ a ε τ)⟫_ℝ = 0)
    (hr0 : r (physicalTime t₀ a ε τ) ≠ 0)
    (hrw : ⟪r (physicalTime t₀ a ε τ), w (physicalTime t₀ a ε τ)⟫_ℝ = 0)
    (hN : scaledRay m v r s₀ t₀ a ε τ 2 ≠ 0) :
    let R := scaledRay m v r s₀ t₀ a ε τ
    let V := scaledVelocity m v w t₀ a ε τ
    let A := scaledAction M m v a ε (physicalTime t₀ a ε τ)
    let C := scaledTransport B M m v a ε (physicalTime t₀ a ε τ)
    HasDerivWithinAt (fun σ => scaledVelocity m v w t₀ a ε σ 0)
      (velocityFirstRhs A C ε (R 0) (R 1) (R 2) (V 0) (V 1)) U τ ∧
    HasDerivWithinAt (fun σ => scaledVelocity m v w t₀ a ε σ 1)
      (velocitySecondRhs A C ε (R 0) (R 1) (R 2) (V 0) (V 1)) U τ := by
  have hthird := thirdVelocity_of_pairing _ _ hN
    (scaled_pairing_zero m v r w hs₀ hε hm0 hv0 hmv hrw)
  constructor
  · have h := scaledVelocity_hasDerivWithinAt B M ha hε hs₀ hmap hm hv hw hm0 hv0 hmv hr0 0
    rw [scaledVelocityRhs_first _ _ _ _ _ hthird] at h
    exact h
  · have h := scaledVelocity_hasDerivWithinAt B M ha hε hs₀ hmap hm hv hw hm0 hv0 hmv hr0 1
    rw [scaledVelocityRhs_second _ _ _ _ _ hthird] at h
    exact h


-- @@ L113-131 verbatim
/-- The flux identity is valid with the actual one-sided endpoint derivatives
of packet paths, as well as in the interior. -/
theorem velocity_scalar_flux_within
    {β t u₁ v₁ : ℝ} {U V : ℝ → ℝ} {S : Set ℝ}
    (hU : HasDerivWithinAt U u₁ S t) (hV : HasDerivWithinAt V v₁ S t) :
    HasDerivWithinAt V (-U t + (v₁ + U t)) S t ∧
    HasDerivWithinAt (fun s => (1 + (β * s ^ 2) ^ 2) * (-U s))
      (2 * (1 - β * (β * t ^ 2)) * V t + (1 + (β * t ^ 2) ^ 2) *
        (-u₁ + idealVelocityFirst β t (U t) (V t))) S t := by
  refine ⟨hV.congr_deriv (by ring), ?_⟩
  have hD : HasDerivAt (fun s : ℝ => 1 + (β * s ^ 2) ^ 2) (4 * β ^ 2 * t ^ 3) t := by
    convert! ((((hasDerivAt_id t).pow 2).const_mul β).pow 2).const_add 1 using 1
    simp only [Pi.pow_apply, id_eq]
    ring
  apply (hD.hasDerivWithinAt.mul hU.neg).congr_deriv
  have hden : 1 + (β * t ^ 2) ^ 2 ≠ 0 := by positivity
  dsimp [idealVelocityFirst]
  field_simp
  ring


-- @@ L133-133 verbatim
end EulerPacketMovingFrame


-- @@ L135-135 verbatim
end

-- @@ L136-136 verbatim
end


-- @@ L138-138 verbatim
end


-- @@ L140-140 verbatim
section


-- @@ L142-142 verbatim
/-! Ray control for the genuine within-interval packet equations. -/


-- @@ L144-144 verbatim
@[expose] public section


-- @@ L146-146 verbatim
noncomputable section


-- @@ L148-148 verbatim
namespace EulerPacketMovingFrame


-- @@ L150-150 verbatim
open Set EulerPacketRay EulerClosedIntervalDerivativeExtension


-- @@ L152-188 verbatim
theorem ray_closeness_within
    {β Θ T e : ℝ} {A : ℝ → Fin 3 → Fin 3 → ℝ} {P Q N : ℝ → ℝ}
    (hβ : 0 ≤ β) (hβupper : β ≤ 1) (hΘ : 1 ≤ Θ) (hT0 : 0 < T) (hT : T ≤ Θ)
    (he : 0 ≤ e) (hsmall : 400 * e * Θ ^ 5 ≤ 1)
    (hAc : ∀ i j, ContinuousOn (fun t => A t i j) (Icc 0 T))
    (hP : ∀ t ∈ Icc 0 T, HasDerivWithinAt P
      (A t 0 0 * P t + A t 0 1 * Q t + A t 0 2 * N t) (Icc 0 T) t)
    (hQ : ∀ t ∈ Icc 0 T, HasDerivWithinAt Q
      (A t 1 0 * P t + A t 1 1 * Q t + A t 1 2 * N t) (Icc 0 T) t)
    (hN : ∀ t ∈ Icc 0 T, HasDerivWithinAt N
      (A t 2 0 * P t + A t 2 1 * Q t + A t 2 2 * N t) (Icc 0 T) t)
    (hclose : ∀ t ∈ Icc 0 T, ∀ i j, |A t i j - idealRayEntry β i j| ≤ e)
    (hinitial : norm3 (P 0) (Q 0) (N 0 - 1) ≤ e) :
    ∀ t ∈ Icc 0 T,
      norm3 (P t-β*t^2) (Q t+2*β*t) (N t-1) ≤ 200*e*Θ^5 ∧ 1/2 ≤ N t := by
  obtain ⟨P', hPeq, hP'⟩ := exists_extension hT0 hP
  obtain ⟨Q', hQeq, hQ'⟩ := exists_extension hT0 hQ
  obtain ⟨N', hNeq, hN'⟩ := exists_extension hT0 hN
  have hPe : ∀ t ∈ Icc 0 T, HasDerivAt P'
      (A t 0 0*P' t+A t 0 1*Q' t+A t 0 2*N' t) t := by
    intro t ht
    simpa only [hPeq ht, hQeq ht, hNeq ht] using hP' t ht
  have hQe : ∀ t ∈ Icc 0 T, HasDerivAt Q'
      (A t 1 0*P' t+A t 1 1*Q' t+A t 1 2*N' t) t := by
    intro t ht
    simpa only [hPeq ht, hQeq ht, hNeq ht] using hQ' t ht
  have hNe : ∀ t ∈ Icc 0 T, HasDerivAt N'
      (A t 2 0*P' t+A t 2 1*Q' t+A t 2 2*N' t) t := by
    intro t ht
    simpa only [hPeq ht, hQeq ht, hNeq ht] using hN' t ht
  have h0 : (0:ℝ) ∈ Icc 0 T := ⟨le_rfl, hT0.le⟩
  have hi : norm3 (P' 0) (Q' 0) (N' 0-1) ≤ e := by
    simpa only [hPeq h0, hQeq h0, hNeq h0] using hinitial
  have h := ray_closeness_of_coefficient_error hβ hβupper hΘ hT0.le hT he hsmall
    hAc hPe hQe hNe hclose hi
  intro t ht
  simpa only [hPeq ht, hQeq ht, hNeq ht] using h t ht


-- @@ L190-190 verbatim
end EulerPacketMovingFrame


-- @@ L192-192 verbatim
end

-- @@ L193-193 verbatim
end


-- @@ L195-195 verbatim
end
