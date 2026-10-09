import Mathlib
import OAI.Probability.Subsphere.Model


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
section

-- @@ L7-7 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L8-8 verbatim
open scoped ENNReal NNReal RealInnerProductSpace

-- @@ L9-9 verbatim
noncomputable section

-- @@ L10-10 verbatim
universe u

-- @@ L11-11 verbatim
namespace SubsphereCurrent


-- @@ L13-13 verbatim
namespace KernelLearner


-- @@ L15-17 verbatim
/-- Borel probabilities, including counterfactual states. -/
def BorelRules {d M T : ℕ} (L : KernelLearner d M T) : Prop :=
  ∀ t q dest, Measurable (fun obs => L.transition t q obs dest)


-- @@ L19-19 verbatim
end KernelLearner


-- @@ L21-21 verbatim
namespace SeededLearner


-- @@ L23-23 verbatim
end SeededLearner


-- @@ L25-25 verbatim
end SubsphereCurrent

-- @@ L26-26 verbatim
end

-- @@ L27-27 verbatim
end

-- @@ L28-28 verbatim
section

-- @@ L29-29 verbatim
open MeasureTheory ProbabilityTheory Set

-- @@ L30-30 verbatim
open scoped ENNReal NNReal RealInnerProductSpace

-- @@ L31-31 verbatim
noncomputable section

-- @@ L32-32 verbatim
universe u v

-- @@ L33-33 verbatim
namespace SubsphereCurrent.Affine


-- @@ L35-35 verbatim
end SubsphereCurrent.Affine

-- @@ L36-36 verbatim
end

-- @@ L37-37 verbatim
end

-- @@ L38-38 verbatim
section

-- @@ L39-39 verbatim
open MeasureTheory ProbabilityTheory Set

-- @@ L40-40 verbatim
open scoped ENNReal NNReal RealInnerProductSpace

-- @@ L41-41 verbatim
noncomputable section

-- @@ L42-42 verbatim
universe v

-- @@ L43-43 verbatim
namespace SubsphereCurrent.Weighted


-- @@ L45-59 verbatim
def RadiusWeightedEstimate : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    (∀ W : ℝ, 1 ≤ W → ∀ (V : Type v) [Fintype V] [Nonempty V],
      (Fintype.card V : ℝ) ≤ W →
      ∀ κ : V → Observation d (d/16) → ℝ≥0∞,
      (∀ v, Measurable (κ v)) → (∀ obs, ∑ v, κ v obs ≤ 1) →
      ∀ g : V → Sphere d → ℝ≥0∞,
      (∀ v, Measurable (g v)) → (∀ v s, g v s ≤ 1) →
      ∀ n : ℕ, (d : ℝ)/2 ≤ n → n ≤ d →
      norm d n (blockInput κ g) ≤
        (ENNReal.ofReal W)^(1/((d/16 : ℕ) : ℝ))*ENNReal.ofReal (C^d)*(⨆ v, norm d (n-2) (g v))) ∧
    (∀ n : ℕ, (d : ℝ)/2 ≤ n → n ≤ d →
      ∀ π : Measure (Sphere d), IsProbabilityMeasure π →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1/10 →
      norm d n (terminalInput π ε) ≤ ENNReal.ofReal (C^d)*(ENNReal.ofReal ε)^((d : ℝ)/16))


-- @@ L61-61 verbatim
end SubsphereCurrent.Weighted

-- @@ L62-62 verbatim
end

-- @@ L63-63 verbatim
end

-- @@ L64-64 verbatim
section

-- @@ L65-65 verbatim
open MeasureTheory ProbabilityTheory Set

-- @@ L66-66 verbatim
open scoped ENNReal NNReal RealInnerProductSpace

-- @@ L67-67 verbatim
noncomputable section

-- @@ L68-68 verbatim
universe v

-- @@ L69-69 verbatim
namespace SubsphereCurrent.Weighted


-- @@ L71-71 verbatim
end SubsphereCurrent.Weighted

-- @@ L72-72 verbatim
end

-- @@ L73-73 verbatim
end

-- @@ L74-74 verbatim
section

-- @@ L75-75 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L76-76 verbatim
open scoped ENNReal NNReal RealInnerProductSpace

-- @@ L77-77 verbatim
noncomputable section

-- @@ L78-78 verbatim
universe u

-- @@ L79-79 verbatim
namespace SubsphereCurrent


-- @@ L81-81 verbatim
end SubsphereCurrent

-- @@ L82-82 verbatim
end

-- @@ L83-83 verbatim
end

-- @@ L84-84 verbatim
section

-- @@ L85-85 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L86-86 verbatim
open scoped ENNReal NNReal RealInnerProductSpace

-- @@ L87-87 verbatim
noncomputable section

-- @@ L88-88 verbatim
universe u v

-- @@ L89-89 verbatim
namespace SubsphereCurrent

-- @@ L90-90 verbatim
namespace Fixed


-- @@ L92-92 verbatim
namespace Stream

-- @@ L93-95 verbatim
variable {E J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [MeasurableSpace J] [Fintype J] [MeasurableSingletonClass J]
  {T : ℕ}


-- @@ L97-97 verbatim
end Stream


-- @@ L99-99 verbatim
end Fixed

-- @@ L100-100 verbatim
end SubsphereCurrent

-- @@ L101-101 verbatim
end

-- @@ L102-102 verbatim
end

-- @@ L103-103 verbatim
section

-- @@ L104-104 verbatim
open MeasureTheory ProbabilityTheory Set

-- @@ L105-105 verbatim
open scoped ENNReal NNReal RealInnerProductSpace

-- @@ L106-106 verbatim
noncomputable section

-- @@ L107-107 verbatim
universe u v

-- @@ L108-108 verbatim
namespace SubsphereCurrent.Affine


-- @@ L110-110 verbatim
end SubsphereCurrent.Affine

-- @@ L111-111 verbatim
end

-- @@ L112-112 verbatim
end


-- @@ L114-114 verbatim
end OAI
