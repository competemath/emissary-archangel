import OAI.NumberTheory.DirichletL.Reflection.ActualWeightedEnergy


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace SevenEighths.InverseReflectedPhase

-- @@ L6-6 verbatim
open scoped Classical BigOperators

-- @@ L7-7 verbatim
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment

-- @@ L8-8 verbatim
noncomputable section

-- @@ L9-9 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L10-10 verbatim
variable {φ σ ι : Type*} [Fintype φ] [Fintype σ] [Fintype ι]

-- @@ L11-11 verbatim
variable {N a c : Eis} {mode : Bool}


-- @@ L13-21 verbatim
def weightedPhysicalReflectedRow (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis → PrimeFamily σ) (jF : φ → ℕ) (Pset nset bset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (r aw : Ideal Eis → ℂ) (w : Ideal Eis → Ideal Eis → ℂ) (u : Eisˣ) (m : ℕ) : ℂ :=
  ∑ P : Pset, ∑ n ∈ nset, ∑ b ∈ bset,
    r K*aw P.val*w n b*(if h : IsCoprime K P.val then
      actualMixedCoefficient F K hK (S P.val) jF (D P h) s hc u m n b else 0)


-- @@ L23-58 verbatim
theorem weightedPhysicalReflectedRow_eq_branches (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis → PrimeFamily σ) (jF : φ → ℕ) (Pset nset bset : Finset (Ideal Eis))
    (hprod : ∀ P ∈ Pset, (∏ i, (S P).ideal i)=P)
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (hcop : ∀ P : Pset, IsCoprime K P.val →
      Pairwise (Function.onFun IsCoprime (F.reflected K hK (S P.val)).ideal))
    (G0 : PrimeFamily ι) (D0 : ControlledStratumArithmetic G0.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (hκ : ∀ P h, (D P h).fixedFactor = D0.fixedFactor)
    (hA : ∀ P h u m n b, actualCuspColumn (D P h) s hc u m n b = actualCuspColumn D0 s hc u m n b)
    (hb : ∀ b ∈ bset, primaryGenerator b ≠ 0)
    (r aw : Ideal Eis → ℂ) (w : Ideal Eis → Ideal Eis → ℂ) (u : Eisˣ) (m : ℕ) :
    weightedPhysicalReflectedRow F K hK S jF Pset nset bset D s hc r aw w u m =
      ∑ e : φ → Fin 3, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
        (actualCuspColumn D0 s hc u m) r aw w u m Pset nset bset K := by
  unfold weightedPhysicalReflectedRow
  have he (P : Pset) (n : Ideal Eis) (b : Ideal Eis) (hb' : b ∈ bset) :=
    masked_actual_coefficient F K hK (S P.val) P.val (hprod P.val P.property) jF
      (D P) (hcop P) G0 D0 s hc (hκ P) (hA P) u m n b (hb b hb')
  simp_rw [weightedReflectedBranchHybridRow,hybridRow,hybridInner,Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  rw [← Finset.sum_coe_sort Pset]
  apply Finset.sum_congr rfl
  intro P hP
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb'
  rw [he P n b hb',Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he'
  unfold frozenBranchColumn
  ring


-- @@ L60-60 verbatim
end

-- @@ L61-61 verbatim
end SevenEighths.InverseReflectedPhase


-- @@ L63-63 verbatim
end OAI
