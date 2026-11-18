import OAI.NumberTheory.DirichletL.PrimeRows.WeightedTuple
import Mathlib.MeasureTheory.Constructions.Polish.Basic


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators

-- @@ L8-8 verbatim
open MeasureTheory Set

-- @@ L9-9 verbatim
namespace SevenEighths.ProbeHighRowFamily

-- @@ L10-10 verbatim
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler

-- @@ L11-11 verbatim
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss

-- @@ L12-12 verbatim
local notation "O" => HeckeFamily.O


-- @@ L14-16 verbatim
@[fun_prop] lemma measurable_const_cpow {α : Type*} [MeasurableSpace α]
    (Q : ℂ) (hQ : Q≠0) (f : α→ℂ) (hf : Measurable f) : Measurable (fun t=>Q^(f t)) :=
  ((continuous_id.const_cpow (Or.inl hQ)).measurable).comp hf


-- @@ L18-25 verbatim
lemma rowClosedMarked_measurable {α : Type*} [MeasurableSpace α]
    (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : ConcretePrimeRowBridge.goodLambda∉Ideal.span {p}) (η a ρ : ℂ) (j : ℕ)
    (X W V : α→ℂ) (hX : Measurable X) (hW : Measurable W) (hV : Measurable V) :
    Measurable (fun t=>rowClosedMarked p hp hg η a (X t) (W t) (V t) ρ j) := by
  unfold rowClosedMarked rowBaseFinite rowMarkedTerm rowWeightedScalar weightedScalar evenRatio
  simp only [Nat.reduceAdd,Nat.reduceMul,OfNat.ofNat_ne_zero,Nat.one_ne_zero,ite_false]
  fun_prop


-- @@ L27-41 verbatim
lemma continuedMarkedLocal_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (u : FreeRow) (P : PrimeIdeal) (hs : Supported P.val)
    (x w z : α→ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t=>continuedMarkedLocal η u P hs (x t) (w t) (z t)) := by
  have hQ : (P.val.absNorm:ℂ)≠0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  let : (Ideal.span {primaryGenerator P.val}:Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (supported_primeGenerator_prime P hs).irreducible
  unfold continuedMarkedLocal
  apply rowClosedMarked_measurable
  · exact measurable_const_cpow _ hQ _ hx.neg
  · exact measurable_const_cpow _ hQ _ hw.neg
  · unfold coordV
    apply measurable_const_cpow _ (by exact_mod_cast hQ)
    fun_prop


-- @@ L43-52 verbatim
lemma ramifiedCorrection_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (u : FreeRow) (P : PrimeIdeal) (hs : Supported P.val)
    (x w z : α→ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t=>ramifiedCorrection η u P hs (x t) (w t) (z t)) := by
  have hm := continuedMarkedLocal_measurable η u P hs x w z hx hw hz
  have hQ : ((P.val.absNorm:ℝ):ℂ)≠0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  simp_rw [ramifiedCorrection_eq_marked]
  unfold coordV
  fun_prop (disch := exact hQ)


-- @@ L54-62 verbatim
lemma idealUnramifiedCorrection_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (x w z : α→ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t=>idealUnramifiedCorrection η u P (x t) (w t) (z t)) := by
  have hQ : ((P.val.absNorm:ℝ):ℂ)≠0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  unfold idealUnramifiedCorrection unramifiedClosed ProbeLocal.continuedCorrection markedFactor
    coordV coordR coordW coordD coordK
  fun_prop (disch := exact hQ)


-- @@ L64-78 verbatim
lemma continuedCorrection_measurable {α : Type*} [MeasurableSpace α]
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (η : Character) (u : FreeRow)
    (x w z : α→ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t=>continuedCorrection S hS η u (x t) (w t) (z t)) := by
  unfold continuedCorrection ramifiedProduct unramifiedProduct
  apply Measurable.mul
  · apply Finset.measurable_prod
    intro P hP
    exact ramifiedCorrection_measurable η u P.val _ x w z hx hw hz
  · apply Measurable.tprod
    intro P
    unfold unramifiedFactor
    split_ifs
    · exact measurable_const
    · exact idealUnramifiedCorrection_measurable η u P.val x w z hx hw hz


-- @@ L80-89 verbatim
lemma continuedCompensatedLocal_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (u : FreeRow) (P : PrimeIdeal) (hs : Supported P.val)
    (x w z B q : α→ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z)
    (hB : Measurable B) (hq : Measurable q) :
    Measurable (fun t=>continuedCompensatedLocal η u P hs (x t) (w t) (z t) (B t) (q t)) := by
  have hM := continuedMarkedLocal_measurable η u P hs x w z hx hw hz
  have hQ : ((P.val.absNorm:ℝ):ℂ)≠0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  unfold continuedCompensatedLocal ProbeLocal.compensatedReplacement coordV coordW coordD
  fun_prop (disch := exact hQ)


-- @@ L91-98 verbatim
lemma LFunction_measurable (χ : Character) : Measurable (LFunction χ) := by
  apply measurable_of_countable_not_continuousAt
  apply ((Set.finite_singleton (1:ℂ)).insert 0).countable.mono
  intro s hs
  by_contra hn
  have h0 : s≠0 := fun h=>hn (by simp [h])
  have h1 : s≠1 := fun h=>hn (by simp [h])
  exact hs (LFunction_differentiableAt χ h0 (Or.inl h1)).continuousAt


-- @@ L100-105 verbatim
lemma regularizedL_measurable (χ : Character) : Measurable (HeckeReciprocal.regularizedL χ) := by
  apply measurable_of_countable_not_continuousAt
  apply (Set.countable_singleton (0:ℂ)).mono
  intro s hs
  by_contra hn
  exact hs (HeckeReciprocal.regularizedL_differentiableAt χ (by simpa using hn)).continuousAt


-- @@ L107-111 verbatim
lemma reciprocal_measurable (χ : Character) : Measurable (HeckeReciprocal.reciprocal χ) := by
  have hL := LFunction_measurable χ
  have hR := regularizedL_measurable χ
  unfold HeckeReciprocal.reciprocal
  split_ifs <;> fun_prop


-- @@ L113-117 verbatim
lemma continuedL_measurable (χ : Character) : Measurable (HeckeOrigin.continued χ) := by
  have hL := LFunction_measurable χ
  have hR := (HeckeOrigin.poleRemoved_entire χ).continuous.measurable
  unfold HeckeOrigin.continued
  split_ifs <;> fun_prop


-- @@ L119-136 verbatim
lemma physicalCompensatedRow_measurable {α : Type*} [MeasurableSpace α]
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow)
    (x w z : α→ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t=>physicalCompensatedRow S hS T hT η u (x t) (w t) (z t)) := by
  unfold physicalCompensatedRow continuedCompensatedRow
  apply Measurable.mul
  · exact (((LFunction_measurable _).comp (by fun_prop)).mul
      ((continuedL_measurable _).comp hw)).mul ((reciprocal_measurable _).comp hx)
  · apply Measurable.mul
    · exact continuedCorrection_measurable _ _ η u x w z hx hw hz
    · apply Finset.measurable_prod
      intro P hP
      have hQ : (P.val.val.absNorm:ℂ)≠0 := by
        exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr P.val.property.ne_zero)
      apply continuedCompensatedLocal_measurable _ _ _ _ x w z _ _ hx hw hz
      · exact (measurable_const_cpow _ hQ x hx).const_mul _
      · exact measurable_const_cpow _ hQ _ hw.neg


-- @@ L138-152 verbatim
lemma calibratedTupleValue_measurable {α : Type*} [MeasurableSpace α] {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (u : FreeRow) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ)
    (x w z : α→ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t=>calibratedTupleValue S hS hmax η u P hPS W Y (x t) (w t) (z t)) := by
  unfold calibratedTupleValue
  apply Measurable.mul
  · apply Measurable.const_mul
    apply Finset.measurable_prod
    intro i hi
    apply Measurable.const_mul
    apply measurable_const_cpow _ _ _ (hz.sub measurable_const)
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr (P i).property.ne_zero)
  · exact physicalCompensatedRow_measurable S hS _ _ η u x w z hx hw hz


-- @@ L154-163 verbatim
lemma calibratedTupleValue_onLines_aestronglyMeasurable {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (u : FreeRow) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (σ υ ξ : ℝ)
    (μ : Measure ((ℝ×ℝ)×ℝ)) :
    AEStronglyMeasurable (fun t : (ℝ×ℝ)×ℝ=>
      calibratedTupleValue S hS hmax η u P hPS W Y
        ((σ:ℂ)+t.1.1*Complex.I) ((υ:ℂ)+t.2*Complex.I) ((ξ:ℂ)+t.1.2*Complex.I)) μ :=
  (calibratedTupleValue_measurable S hS hmax η u P hPS W Y _ _ _
    (by fun_prop) (by fun_prop) (by fun_prop)).aestronglyMeasurable


-- @@ L165-165 verbatim
end SevenEighths.ProbeHighRowFamily


-- @@ L167-167 verbatim
end


-- @@ L169-169 verbatim
end OAI
