import OAI.NumberTheory.DirichletL.Reflection.Actual


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace SevenEighths.InverseReflectedPhase

-- @@ L6-6 verbatim
open scoped Classical BigOperators

-- @@ L7-7 verbatim
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve LocalReflectionBrackets

-- @@ L8-8 verbatim
noncomputable section

-- @@ L9-9 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L10-10 verbatim
variable {ι φ σ : Type*} [Fintype ι] [Fintype φ] [Fintype σ]

-- @@ L11-11 verbatim
variable {p : ι → Eis} {N a c : Eis} {mode : Bool}


-- @@ L13-18 verbatim
def actualCuspColumn (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) : ℂ :=
  fixedCuspArrayWithPhase s.index u
    (s.reflectionStaticPhase c hc (Ideal.Quotient.mk _ (-(D.matrix (fun _ => 1) 1 1)*D.U))
      (s.modelDualNumerator u) u) m n b


-- @@ L20-24 verbatim
lemma actualCuspColumn_norm_le_one (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) : ‖actualCuspColumn D s hc u m n b‖ ≤ 1 :=
  fixedCuspArrayWithPhase_norm_le_one s.index u _
    (s.reflectionStaticPhase_norm_le_one c hc _ _ u) m n b


-- @@ L26-29 verbatim
def frozenBranchColumn (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Ideal Eis → Ideal Eis → ℂ) (n b : Ideal Eis) : ℂ :=
  A n b * reflectedBranch (fun i => Ideal.span {F.generator i}) F.generator_good jF e
    (primaryGenerator n) (primaryGenerator b)


-- @@ L31-32 verbatim
def frozenExtracted (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3) (v : Fin 3) : Ideal Eis :=
  reflectionExtractedDivisor (fun i => Ideal.span {F.generator i}) jF e v


-- @@ L34-37 verbatim
def frozenBranchScale (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3) : ℝ :=
  Real.sqrt (Ideal.absNorm (frozenExtracted F jF e 1):ℝ)*
    Real.sqrt (Ideal.absNorm (frozenExtracted F jF e 2):ℝ)/
    Real.sqrt (Ideal.absNorm (frozenExtracted F jF e 0):ℝ)


-- @@ L39-56 verbatim
theorem sourceColumn_eq_sum_frozenBranches (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ → ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) :
    sourceColumn D s hc (F.reflected K hK S).generator_good (reflectedExponent jF)
      (frozenIndices φ (PrimeIndex K) σ) u m n b =
      ∑ e : φ → Fin 3, frozenBranchColumn F jF e (actualCuspColumn D s hc u m) n b := by
  classical
  let : DecidableEq (φ ⊕ (PrimeIndex K ⊕ σ)) := Classical.decEq _
  unfold sourceColumn frozenIndices
  rw [Finset.prod_image Sum.inl_injective.injOn]
  change actualCuspColumn D s hc u m n b *
    (∏ i, bracket (actualSextic (Ideal.span {F.generator i}) (F.generator_good i)) (jF i)
      (Ideal.Quotient.mk _ (primaryGenerator n*(primaryGenerator b)^3))) = _
  exact (congrArg (actualCuspColumn D s hc u m n b * ·)
    (prod_bracket_eq_full_branches (fun i => Ideal.span {F.generator i}) F.generator_good
      jF (primaryGenerator n) (primaryGenerator b))).trans (Finset.mul_sum _ _ _)


-- @@ L58-67 verbatim
theorem frozenBranchColumn_norm_le (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Ideal Eis → Ideal Eis → ℂ) (hA : ∀ n b, ‖A n b‖ ≤ 1) (n b : Ideal Eis) :
    ‖frozenBranchColumn F jF e A n b‖ ≤ frozenBranchScale F jF e := by
  rw [frozenBranchColumn,norm_mul]
  calc
    _ ≤ 1*‖reflectedBranch (fun i => Ideal.span {F.generator i}) F.generator_good jF e
        (primaryGenerator n) (primaryGenerator b)‖ := mul_le_mul_of_nonneg_right (hA n b) (norm_nonneg _)
    _ ≤ _ := by
      rw [one_mul]
      exact reflectedBranch_norm_bound _ F.generator_good jF e _ _


-- @@ L69-81 verbatim
theorem frozenBranchColumn_normalized_bound (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Ideal Eis → Ideal Eis → ℂ) (hA : ∀ n b, ‖A n b‖ ≤ 1)
    (n b : Ideal Eis) (U B : ℝ) (hU : 0<U) (hB : 0<B) :
    ‖frozenBranchColumn F jF e A n b‖ /
      (Real.sqrt ((Ideal.absNorm (frozenExtracted F jF e 1):ℝ)*U)*
        ((Ideal.absNorm (frozenExtracted F jF e 2):ℝ)*B)) ≤
      1/(Real.sqrt U*B*Real.sqrt ((Ideal.absNorm (frozenExtracted F jF e 0):ℝ)*
        (Ideal.absNorm (frozenExtracted F jF e 2):ℝ))) := by
  apply (div_le_div_of_nonneg_right ?_ (by positivity)).trans
    (reflectedBranch_normalized_bound (fun i => Ideal.span {F.generator i}) F.generator_good
      jF e (primaryGenerator n) (primaryGenerator b) U B hU hB)
  rw [frozenBranchColumn,norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hA n b)


-- @@ L83-83 verbatim
end

-- @@ L84-84 verbatim
end SevenEighths.InverseReflectedPhase


-- @@ L86-86 verbatim
end OAI
