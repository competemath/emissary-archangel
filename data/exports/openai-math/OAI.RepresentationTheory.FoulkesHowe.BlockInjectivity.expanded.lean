import OAI.RepresentationTheory.FoulkesHowe.DerivationInjectivity
import OAI.RepresentationTheory.FoulkesHowe.PolynomialShift
import OAI.RepresentationTheory.FoulkesHowe.BlockWeight


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
noncomputable section


-- @@ L9-9 verbatim
namespace Problem346

-- @@ L10-10 verbatim
namespace PolynomialShift


-- @@ L12-12 verbatim
open MvPolynomial PolynomialWeights


-- @@ L14-14 verbatim
variable {B I : Type*} [Fintype B] [Fintype I] [DecidableEq B]


-- @@ L16-40 verbatim
/-- A polynomial block shift is injective in strictly positive source-minus-destination
weight. All other variable blocks are arbitrary spectators. -/
theorem eq_zero_of_shift_eq_zero (src dst : B) (hsd : src ≠ dst)
    {f : MvPolynomial (B × I) ℂ} {p q : ℕ} (hpq : q < p)
    (hp : IsBlockHomogeneous src f p) (hq : IsBlockHomogeneous dst f q)
    (hDf : shift src dst f = 0) : f = 0 := by
  refine derivation_eq_zero_of_positive_weight
    (derivation src dst) (derivation dst src)
    (derivation src src - derivation dst dst)
    (commutator src dst hsd) (weight_commutator src dst hsd) ?_
    f p q hpq ?_ hDf
  · rintro ⟨b, i⟩
    by_cases hb : b = dst
    · subst b
      simp [hsd]
    · simp [hb]
  · apply block_difference_eigenvalue src dst _ _ _ _ hp hq
    · intro b i
      by_cases hb : b = src
      · subst b; simp
      · simp [hb]
    · intro b i
      by_cases hb : b = dst
      · subst b; simp
      · simp [hb]


-- @@ L42-51 verbatim
/-- Injectivity on the intersection of two specified block-homogeneous pieces. -/
theorem shift_injOn (src dst : B) (hsd : src ≠ dst) (p q : ℕ) (hpq : q < p) :
    Set.InjOn (shift (K := ℂ) (I := I) src dst)
      {f | IsBlockHomogeneous src f p ∧ IsBlockHomogeneous dst f q} := by
  intro f hf g hg hfg
  apply sub_eq_zero.mp
  apply eq_zero_of_shift_eq_zero src dst hsd hpq
  · exact (weightedHomogeneousSubmodule ℂ (blockWeight src) p).sub_mem hf.1 hg.1
  · exact (weightedHomogeneousSubmodule ℂ (blockWeight dst) q).sub_mem hf.2 hg.2
  · rw [map_sub, hfg, sub_self]


-- @@ L53-53 verbatim
end PolynomialShift

-- @@ L54-54 verbatim
end Problem346


-- @@ L56-56 verbatim
end


-- @@ L58-58 verbatim
end OAI
