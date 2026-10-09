import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe uE uF


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
namespace LipschitzCounterexample


-- @@ L10-10 verbatim
abbrev RealL2 := lp (fun _ : ℕ => ℝ) 2

-- @@ L11-11 verbatim
abbrev C0L2 := ZeroAtInftyContinuousMap ℕ RealL2


-- @@ L13-18 verbatim
structure SeparableRealBanach where
  Carrier : Type
  [normedAddCommGroup : NormedAddCommGroup Carrier]
  [normedSpace : NormedSpace ℝ Carrier]
  [completeSpace : CompleteSpace Carrier]
  [separableSpace : TopologicalSpace.SeparableSpace Carrier]


-- @@ L20-22 verbatim
attribute [instance] SeparableRealBanach.normedAddCommGroup
  SeparableRealBanach.normedSpace SeparableRealBanach.completeSpace
  SeparableRealBanach.separableSpace


-- @@ L24-26 verbatim
def ContainsLinearCopy (E : Type uE) (F : Type uF) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] : Prop :=
  ∃ (T : E →L[ℝ] F) (a : ℝ), 0 < a ∧ ∀ x : E, a * ‖x‖ ≤ ‖T x‖


-- @@ L28-36 verbatim
def MainClaim : Prop :=
  ∃ X Y : SeparableRealBanach,
    ∃ Ψ : X.Carrier ≃ Y.Carrier,
      (∀ s t : X.Carrier,
        (4 / 21 : ℝ) * ‖s - t‖ ≤ ‖Ψ s - Ψ t‖ ∧
        ‖Ψ s - Ψ t‖ ≤ (76 / 25 : ℝ) * ‖s - t‖) ∧
      IsEmpty (X.Carrier ≃L[ℝ] Y.Carrier) ∧
      Nonempty (C0L2 →ₗᵢ[ℝ] X.Carrier) ∧
      ¬ ContainsLinearCopy C0L2 Y.Carrier


-- @@ L38-38 verbatim
end LipschitzCounterexample

-- @@ L39-39 verbatim
end


-- @@ L41-41 verbatim
end OAI
