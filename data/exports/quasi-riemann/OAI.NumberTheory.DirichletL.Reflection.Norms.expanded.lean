import OAI.NumberTheory.DirichletL.Reflection.Ramified


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace SevenEighths.InverseReflectedPhase

-- @@ L6-6 verbatim
open scoped Classical BigOperators

-- @@ L7-7 verbatim
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT CompletedGauss LocalReflectionBrackets

-- @@ L8-8 verbatim
noncomputable section

-- @@ L9-9 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L10-10 verbatim
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

-- @@ L11-11 verbatim
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a c : Eis} {mode : Bool}

-- @@ L12-12 verbatim
noncomputable local instance phaseNormField (P : Ideal Eis) [P.IsMaximal] : Field (Eis ⧸ P) := Ideal.Quotient.field P

-- @@ L13-13 verbatim
noncomputable local instance phaseNormFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _


-- @@ L15-31 verbatim
omit [Fintype ι] in
theorem crossSymbol_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (i k : ι) (hik : i ≠ k) : ‖MixedCrossSeparation.crossSymbol p hg i k‖ = 1 := by
  have hnot : p k ∉ Ideal.span {p i} := by
    intro hm
    have hle : Ideal.span {p k} ≤ Ideal.span {p i} :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hm)
    have ht := (hcop hik).sup_eq
    rw [sup_eq_left.mpr hle] at ht
    exact (inferInstance : (Ideal.span {p i}).IsMaximal).ne_top ht
  have h6 : MixedCrossSeparation.crossSymbol p hg i k ^ 6 = 1 := by
    simpa only [MixedCrossSeparation.crossSymbol,map_pow,ite_eq_right hnot] using
      canonicalSextic_sixth_power_mask (Ideal.span {p i}) (hg i) (p k)
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : (6:ℕ) ≠ 0)).mp
  simpa only [norm_pow,norm_one] using congrArg norm h6


-- @@ L33-42 verbatim
theorem local_phase_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (i : ι) (j : ℕ) (hj : j < 6) :
    ‖(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
      phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) j (D.epsilon i)‖ = 1 := by
  rw [norm_mul,FiniteRayExpansion.norm_char_unit,one_mul]
  exact canonical_phase_norm (Ideal.span {p i}) (hg i) (hchar i) (quotientTrace (p i) (hp i))
    (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive (p i) (hp i)) j hj (D.epsilon i)


-- @@ L44-56 verbatim
theorem markedPrimeScalar_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i}))) (i : ι) :
    ‖markedPrimeScalar (p i) c (hp i) (hg i)‖ = 1 := by
  have h := local_phase_norm D hp hg hchar i 0 (by decide)
  rw [controlled_marked_phase,norm_mul,norm_prod] at h
  have he : (∏ k ∈ Finset.univ.erase i, ‖MixedCrossSeparation.crossSymbol p hg i k^2‖) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    rw [norm_pow,crossSymbol_norm hg hcop i k (Finset.mem_erase.mp hk).1.symm,one_pow]
  simpa only [he,mul_one] using h


-- @@ L58-70 verbatim
theorem residualPrimeScalar_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i}))) (i : ι) :
    ‖residualPrimeScalar (p i) c (hp i) (hg i)‖ = 1 := by
  have h := local_phase_norm D hp hg hchar i 1 (by decide)
  rw [controlled_residual_phase,norm_mul,norm_prod] at h
  have he : (∏ k ∈ Finset.univ.erase i, ‖MixedCrossSeparation.crossSymbol p hg i k^4‖) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    rw [norm_pow,crossSymbol_norm hg hcop i k (Finset.mem_erase.mp hk).1.symm,one_pow]
  simpa only [he,mul_one] using h


-- @@ L72-91 verbatim
theorem residualWithFrozen_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (R F : Finset ι) (hd : Disjoint R F) : ‖residualWithFrozen hp hg c R F‖ = 1 := by
  unfold residualWithFrozen
  rw [norm_prod]
  apply Finset.prod_eq_one
  intro i hi
  simp only [norm_mul,norm_prod,norm_pow,residualPrimeScalar_norm D hp hg hchar hcop i,one_mul]
  have hR : (∏ k ∈ R.erase i, ‖MixedCrossSeparation.crossSymbol p hg i k‖^4) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    rw [crossSymbol_norm hg hcop i k (Finset.mem_erase.mp hk).1.symm,one_pow]
  have hF : (∏ k ∈ F, ‖MixedCrossSeparation.crossSymbol p hg i k‖^4) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    rw [crossSymbol_norm hg hcop i k (fun h => Finset.disjoint_left.mp hd hi (h ▸ hk)),one_pow]
  rw [hR,hF,one_mul]


-- @@ L93-112 verbatim
theorem markedWithFrozen_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (P F : Finset ι) (hd : Disjoint P F) : ‖markedWithFrozen hp hg c P F‖ = 1 := by
  unfold markedWithFrozen
  rw [norm_prod]
  apply Finset.prod_eq_one
  intro i hi
  simp only [norm_mul,norm_prod,norm_pow,markedPrimeScalar_norm D hp hg hchar hcop i,one_mul]
  have hP : (∏ k ∈ P.erase i, ‖MixedCrossSeparation.crossSymbol p hg i k‖^2) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    rw [crossSymbol_norm hg hcop i k (Finset.mem_erase.mp hk).1.symm,one_pow]
  have hF : (∏ k ∈ F, ‖MixedCrossSeparation.crossSymbol p hg i k‖^2) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    rw [crossSymbol_norm hg hcop i k (fun h => Finset.disjoint_left.mp hd hi (h ▸ hk)),one_pow]
  rw [hP,hF,one_mul]


-- @@ L114-114 verbatim
end

-- @@ L115-115 verbatim
end SevenEighths.InverseReflectedPhase


-- @@ L117-117 verbatim
end OAI
