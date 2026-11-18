import OAI.NumberTheory.DirichletL.Reflection.WeightedSourceSum
import OAI.NumberTheory.DirichletL.Descent.CommonMeasure


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
namespace SevenEighths.InverseReflectedPhase

-- @@ L7-7 verbatim
open scoped Classical BigOperators

-- @@ L8-8 verbatim
open MeasureTheory ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment

-- @@ L9-9 verbatim
noncomputable section

-- @@ L10-10 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L11-11 verbatim
variable {Ω φ σ : Type*} [MeasurableSpace Ω] [Fintype φ] [Fintype σ]

-- @@ L12-12 verbatim
variable {N a c : Eis} {mode : Bool}


-- @@ L14-39 verbatim
lemma weightedReflectedBranchHybridRow_aestronglyMeasurable
    (μ : Measure Ω) (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
    (S : Ideal Eis → PrimeFamily σ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (κ : ℂ) (A : Ideal Eis → Ideal Eis → ℂ)
    (r aw : Ω → Ideal Eis → ℂ) (w : Ω → Ideal Eis → Ideal Eis → ℂ)
    (u : Eisˣ) (m : ℕ) (Pset nset bset : Finset (Ideal Eis)) (K : Ideal Eis)
    (hr : AEStronglyMeasurable (fun t => r t K) μ)
    (ha : ∀ P ∈ Pset, AEStronglyMeasurable (fun t => aw t P) μ)
    (hw : ∀ n ∈ nset, ∀ b ∈ bset, AEStronglyMeasurable (fun t => w t n b) μ) :
    AEStronglyMeasurable (fun t => weightedReflectedBranchHybridRow F jF e S s κ A
      (r t) (aw t) (w t) u m Pset nset bset K) μ := by
  unfold weightedReflectedBranchHybridRow
  apply (hr.const_mul _).mul
  unfold hybridRow
  apply Finset.aestronglyMeasurable_fun_sum
  intro P hP
  simp only [div_eq_mul_inv]
  apply (((ha P hP).const_mul _).mul_const _ |>.mul_const _).mul
  unfold hybridInner
  apply Finset.aestronglyMeasurable_fun_sum
  intro n hn
  apply Finset.aestronglyMeasurable_fun_sum
  intro b hb
  unfold frozenBranchColumn
  exact (((((hw n hn b hb).const_mul _).mul_const _).mul_const _).mul_const _).mul_const _


-- @@ L41-41 verbatim
end

-- @@ L42-42 verbatim
end SevenEighths.InverseReflectedPhase


-- @@ L44-44 verbatim
end OAI
