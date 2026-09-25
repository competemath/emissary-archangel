module

public import APAP.Prereqs.Mu
public import Mathlib.Analysis.RCLike.Inner


-- @@ L6-6 verbatim
public section


-- @@ L8-8 verbatim
open Finset RCLike

-- @@ L9-9 verbatim
open scoped BigOperators ComplexConjugate Indicator mu


-- @@ L11-11 verbatim
variable {ι 𝕜 : Type*} [Fintype ι] [RCLike 𝕜]


-- @@ L13-14 verbatim
lemma indicator_one_wInner_one (s : Finset ι) (f : ι → 𝕜) : ⟪𝟭_[s], f⟫_[𝕜] = ∑ i ∈ s, f i := by
  classical simp [wInner_one_eq_sum, Set.indicator_apply]


-- @@ L16-18 verbatim
lemma wInner_one_indicator_one (f : ι → 𝕜) (s : Finset ι) :
    ⟪f, 𝟭_[s]⟫_[𝕜] = ∑ i ∈ s, conj (f i) := by
  classical simp [wInner_one_eq_sum, Set.indicator_apply]


-- @@ L20-23 expanded
lemma mu_wInner_one (s : Finset ι) (f : ι → 𝕜) : ⟪mu s, f⟫_[𝕜] = 𝔼 i ∈ s, f i := by
  classical
  simp [wInner_one_eq_sum]
  simp [mu_apply, expect_eq_sum_div_card, sum_mul, div_eq_mul_inv]


-- @@ L25-26 expanded
lemma wInner_one_mu (f : ι → 𝕜) (s : Finset ι) : ⟪f, mu s⟫_[𝕜] = 𝔼 i ∈ s, conj (f i) := by
  classical simp [wInner_one_eq_sum, mu_apply, expect_eq_sum_div_card, mul_sum, div_eq_inv_mul]

