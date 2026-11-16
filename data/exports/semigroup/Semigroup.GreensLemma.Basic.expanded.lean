/-
Copyright (c) 2026 Timothy Harvey and James Mitchell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timothy Harvey
-/
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Data.Set.Function
import Mathlib.Logic.Equiv.Set
import Semigroup.GreensRelations.Idempotents
import Semigroup.GreensTheorem.Subgroups.Basic


-- @@ L12-45 verbatim
/-!
# Green's Lemma and its Consequences

This file proves Green's lemma: the translation maps between the L-classes
(resp. R-classes) of R-related (resp. L-related) elements are mutually inverse
bijections. It then derives the linking pairs of D-related idempotents and the
induced isomorphism of their H-class groups.

## Main results

* `greens_lemma_right`: if `b = a * u` and `a = b * v`, then `· * u` is a bijection from
  the L-class of `a` onto the L-class of `b`.
* `greens_lemma_left`: if `b = u * a` and `a = v * b`, then `u * ·` is a bijection from
  the R-class of `a` onto the R-class of `b`.
* `greens_lemma_right_hClass`, `greens_lemma_left_hClass`: the translation maps of
  Green's lemma restrict to bijections between H-classes.
* `IsGreenD.exists_hClass_bijOn`, `IsGreenD.nonempty_hClass_equiv`: **corollary of
  Green's lemma** — the H-classes of D-related elements are in bijection; in particular
  all H-classes within a D-class have the same cardinality.
* `IsGreenD.exists_linking_pair`: D-related idempotents `e` and `f` admit a linking pair
  `p`, `q` with `p * q = e` and `q * p = f`.
* `exists_hClass_mulEquiv`: the H-class groups of D-related idempotents are isomorphic
  (as a `MulEquiv` of the groups `IsIdempotentElem.hClassGroup`).

## References

* [J. M. Howie, *Fundamentals of Semigroup Theory*][howie1995]

The proofs formalized in this module closely follow the structure and logic
from lecture notes:

* J. D. Mitchell, *MT5863 Semigroup Theory* (lecture notes,
  University of St Andrews, 2026).
-/


-- @@ L47-47 verbatim
open scoped GreensRelations


-- @@ L49-49 verbatim
variable {S : Type*} [Semigroup S]


-- @@ L51-51 verbatim
/-! ### Green's lemma -/


-- @@ L53-53 verbatim
section GreensLemma


-- @@ L55-71 expanded
/-- **Green's lemma (right translation)**: if `b = a * u` and `a = b * v`,
then `· * u` is a bijection from the L-class of `a` onto the L-class of `b`. -/
theorem greens_lemma_right {a b u v : S} (hu : b = a * u) (hv : a = b * v) :
    Set.BijOn (· * u) (IsGreenL.eqvClass a) (IsGreenL.eqvClass b) :=
  by
  have hcancel : a * u * v = a := by rw [← hu, ← hv]
  have hcancel' : b * v * u = b := by rw [← hv, ← hu]
  refine ⟨fun x hx => ?_, fun x hx y hy hxy => ?_, fun y hy => ?_⟩
  · have h1 : IsGreenL (x * u) (a * u) := IsGreenL.mul_right u hx
    rwa [← hu] at h1
  · have hxy' : x * u = y * u := hxy
    have hx' : x * u * v = x := IsGreenL.cancellation hx hcancel
    have hy' : y * u * v = y := IsGreenL.cancellation hy hcancel
    rw [← hx', ← hy', hxy']
  · refine ⟨y * v, ?_, ?_⟩
    · have h1 : IsGreenL (y * v) (b * v) := IsGreenL.mul_right v hy
      rwa [← hv] at h1
    · exact IsGreenL.cancellation hy hcancel'


-- @@ L74-92 expanded
/-- **Green's lemma (left translation)**: if `b = u * a` and `a = v * b`,
then `u * ·` is a bijection from the R-class of `a` onto the R-class of `b`. -/
theorem greens_lemma_left {a b u v : S} (hu : b = u * a) (hv : a = v * b) :
    Set.BijOn (u * ·) (IsGreenR.eqvClass a) (IsGreenR.eqvClass b) :=
  by
  have hcancel : v * u * a = a := by rw [mul_assoc, ← hu, ← hv]
  have hcancel' : u * v * b = b := by rw [mul_assoc, ← hv, ← hu]
  refine ⟨fun x hx => ?_, fun x hx y hy hxy => ?_, fun y hy => ?_⟩
  · have h1 : IsGreenR (u * x) (u * a) := IsGreenR.mul_left u hx
    rwa [← hu] at h1
  · have hxy' : u * x = u * y := hxy
    have hx' : v * u * x = x := IsGreenR.cancellation hx hcancel
    have hy' : v * u * y = y := IsGreenR.cancellation hy hcancel
    rw [← hx', ← hy', mul_assoc, mul_assoc, hxy']
  · refine ⟨v * y, ?_, ?_⟩
    · have h1 : IsGreenR (v * y) (v * b) := IsGreenR.mul_left v hy
      rwa [← hv] at h1
    · change u * (v * y) = y
      rw [← mul_assoc]
      exact IsGreenR.cancellation hy hcancel'


-- @@ L94-115 expanded
/-- The right translation of Green's lemma preserves H-classes: if `b = a * u` and
`a = b * v`, then `· * u` is a bijection from the H-class of `a` onto the H-class
of `b`. -/
theorem greens_lemma_right_hClass {a b u v : S} (hu : b = a * u) (hv : a = b * v) :
    Set.BijOn (· * u) (IsGreenH.eqvClass a) (IsGreenH.eqvClass b) :=
  by
  have hcancel' : b * v * u = b := by
    rw [← hv, ← hu]
      -- the map sends the H-class of `a` into the H-class of `b`; stated for arbitrary
        -- translations so that it also applies with the roles of `a` and `b` exchanged
      
  have hmaps :
    ∀ {a' b' u' v' : S},
      b' = a' * u' → a' = b' * v' → ∀ x ∈ IsGreenH.eqvClass a', x * u' ∈ IsGreenH.eqvClass b' :=
    by
    intro a' b' u' v' hu' hv' x hx
    have hab' : IsGreenR a' b' := ⟨Or.inr ⟨v', hv'⟩, Or.inr ⟨u', hu'⟩⟩
    have hcancel : a' * u' * v' = a' := by rw [← hu', ← hv']
    have hxL : IsGreenL (x * u') b' :=
      by
      have h1 : IsGreenL (x * u') (a' * u') := IsGreenL.mul_right u' hx.1
      rwa [← hu'] at h1
    have hxuv : x * u' * v' = x := IsGreenL.cancellation hx.1 hcancel
    have hxR : IsGreenR (x * u') x := ⟨Or.inr ⟨u', rfl⟩, Or.inr ⟨v', hxuv.symm⟩⟩
    exact ⟨hxL, hxR.trans (hx.2.trans hab')⟩
  refine ⟨fun x hx => hmaps hu hv x hx, ?_, fun y hy => ⟨y * v, hmaps hv hu y hy, ?_⟩⟩
  · exact ((greens_lemma_right hu hv).2.1).mono fun x hx => hx.1
  · exact IsGreenL.cancellation hy.1 hcancel'


-- @@ L117-139 expanded
/-- The left translation of Green's lemma preserves H-classes: if `b = u * a` and
`a = v * b`, then `u * ·` is a bijection from the H-class of `a` onto the H-class
of `b`. -/
theorem greens_lemma_left_hClass {a b u v : S} (hu : b = u * a) (hv : a = v * b) :
    Set.BijOn (u * ·) (IsGreenH.eqvClass a) (IsGreenH.eqvClass b) :=
  by
  have hcancel' : u * v * b = b := by rw [mul_assoc, ← hv, ← hu]
  have hmaps :
    ∀ {a' b' u' v' : S},
      b' = u' * a' → a' = v' * b' → ∀ x ∈ IsGreenH.eqvClass a', u' * x ∈ IsGreenH.eqvClass b' :=
    by
    intro a' b' u' v' hu' hv' x hx
    have hab' : IsGreenL a' b' := ⟨Or.inr ⟨v', hv'⟩, Or.inr ⟨u', hu'⟩⟩
    have hcancel : v' * u' * a' = a' := by rw [mul_assoc, ← hu', ← hv']
    have hxR : IsGreenR (u' * x) b' :=
      by
      have h1 : IsGreenR (u' * x) (u' * a') := IsGreenR.mul_left u' hx.2
      rwa [← hu'] at h1
    have hxvu : v' * u' * x = x := IsGreenR.cancellation hx.2 hcancel
    have hxL : IsGreenL (u' * x) x := ⟨Or.inr ⟨u', rfl⟩, Or.inr ⟨v', by rw [← mul_assoc, hxvu]⟩⟩
    exact ⟨hxL.trans (hx.1.trans hab'), hxR⟩
  refine ⟨fun x hx => hmaps hu hv x hx, ?_, fun y hy => ⟨v * y, hmaps hv hu y hy, ?_⟩⟩
  · exact ((greens_lemma_left hu hv).2.1).mono fun x hx => hx.2
  · change u * (v * y) = y
    rw [← mul_assoc]
    exact IsGreenR.cancellation hy.2 hcancel'


-- @@ L141-149 expanded
/-- L-related elements have H-classes in bijection (via a left translation of
Green's lemma, or the identity when the elements are equal). -/
theorem IsGreenL.exists_hClass_bijOn {a b : S} (h : IsGreenL a b) :
    ∃ φ : S → S, Set.BijOn φ (IsGreenH.eqvClass a) (IsGreenH.eqvClass b) :=
  by
  rcases h.1 with rfl | ⟨u, hu⟩
  · exact ⟨id, Set.bijOn_id _⟩
  rcases h.2 with rfl | ⟨w, hw⟩
  · exact ⟨id, Set.bijOn_id _⟩
  exact ⟨(w * ·), greens_lemma_left_hClass hw hu⟩


-- @@ L151-159 expanded
/-- R-related elements have H-classes in bijection (via a right translation of
Green's lemma, or the identity when the elements are equal). -/
theorem IsGreenR.exists_hClass_bijOn {a b : S} (h : IsGreenR a b) :
    ∃ φ : S → S, Set.BijOn φ (IsGreenH.eqvClass a) (IsGreenH.eqvClass b) :=
  by
  rcases h.1 with rfl | ⟨u, hu⟩
  · exact ⟨id, Set.bijOn_id _⟩
  rcases h.2 with rfl | ⟨w, hw⟩
  · exact ⟨id, Set.bijOn_id _⟩
  exact ⟨(· * w), greens_lemma_right_hClass hw hu⟩


-- @@ L161-169 expanded
/-- **Corollary of Green's lemma**: the H-classes of D-related elements are in
bijection, by composing the two translation bijections through an intermediate
element of the D-class. -/
theorem IsGreenD.exists_hClass_bijOn {a b : S} (hD : IsGreenD a b) :
    ∃ φ : S → S, Set.BijOn φ (IsGreenH.eqvClass a) (IsGreenH.eqvClass b) :=
  by
  obtain ⟨z, hL, hR⟩ := hD
  obtain ⟨φ, hφ⟩ := hL.exists_hClass_bijOn
  obtain ⟨ψ, hψ⟩ := hR.exists_hClass_bijOn
  exact ⟨ψ ∘ φ, hψ.comp hφ⟩


-- @@ L171-176 expanded
/-- **Corollary of Green's lemma**: D-related elements have equinumerous
H-classes. -/
theorem IsGreenD.nonempty_hClass_equiv {a b : S} (hD : IsGreenD a b) :
    Nonempty (IsGreenH.eqvClass a ≃ IsGreenH.eqvClass b) :=
  by
  obtain ⟨φ, hφ⟩ := hD.exists_hClass_bijOn
  exact ⟨hφ.equiv φ⟩


-- @@ L178-178 verbatim
end GreensLemma


-- @@ L180-180 verbatim
/-! ### The isomorphism of H-class groups of D-related idempotents -/


-- @@ L182-182 verbatim
section IsomorphismTheorem


-- @@ L184-205 expanded
/-- **Linking pair** for D-related idempotents: if `e` and `f` are D-related idempotents,
there are `p` and `q` with `p * q = e` and `q * p = f`, satisfying the absorption
identities `e * p = p`, `p * f = p`, `f * q = q`, and `q * e = q`. -/
theorem IsGreenD.exists_linking_pair {e f : S} (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (hD : IsGreenD e f) :
    ∃ p q : S, p * q = e ∧ q * p = f ∧ e * p = p ∧ p * f = p ∧ f * q = q ∧ q * e = q :=
  by
  obtain ⟨p, hpL, hpR⟩ := hD.symm
  have hep : e * p = p := IsGreenRightDvd.idem_mul_eq_self he hpR.1
  have hpf : p * f = p := IsGreenLeftDvd.mul_idem_eq_self hf hpL.2
  obtain ⟨q₁, hq₁⟩ := IsGreenRightDvd.exists_eq_mul_of_idem he hpR.2
  obtain ⟨q₂, hq₂⟩ := IsGreenLeftDvd.exists_eq_mul_of_idem hf hpL.1
  refine ⟨p, f * q₁ * e, ?_, ?_, hep, hpf, ?_, ?_⟩
  · rw [← mul_assoc, ← mul_assoc, hpf, ← hq₁, he.eq]
  ·
    calc
      f * q₁ * e * p = f * (q₁ * p) := by rw [mul_assoc, hep, mul_assoc]
      _ = q₂ * p * (q₁ * p) := by rw [← hq₂]
      _ = q₂ * (p * q₁) * p := by simp only [mul_assoc]
      _ = q₂ * e * p := by rw [← hq₁]
      _ = q₂ * p := by rw [mul_assoc, hep]
      _ = f := hq₂.symm
  · rw [← mul_assoc, ← mul_assoc, hf.eq]
  · rw [mul_assoc, he.eq]


-- @@ L207-228 expanded
/-- Conjugation by a linking pair maps the H-class of `e` into the H-class of `f`:
if `x H e`, then `q * x * p H f`. -/
theorem IsGreenH.conj_mem {e f p q : S} (he : IsIdempotentElem e) (hpq : p * q = e)
    (hqp : q * p = f) (hpf : p * f = p) (hfq : f * q = q) (hqe : q * e = q) {x : S}
    (hx : IsGreenH x e) : IsGreenH (q * x * p) f :=
  by
  obtain ⟨x', hx', hxx', hx'x⟩ := IsGreenH.exists_inv he hx
  have hxe : x * e = x := IsGreenH.mul_right_eq_self he hx
  have hx'e : x' * e = x' := IsGreenH.mul_right_eq_self he hx'
  have hmid : ∀ a b : S, q * a * p * (q * b * p) = q * (a * e * b) * p :=
    by
    intro a b
    calc
      q * a * p * (q * b * p) = q * a * (p * q) * b * p := by simp only [mul_assoc]
      _ = q * (a * e * b) * p := by rw [hpq];
        simp only [mul_assoc]
          -- `q * x * p` is a two-sided multiple of `f`
          
  have h1 : q * x * p * f = q * x * p := by rw [mul_assoc, hpf]
  have h2 : f * (q * x * p) = q * x * p := by
    rw [← mul_assoc, ← mul_assoc, hfq]
      -- and `f` is recovered from `q * x * p` via the conjugated inverse `q * x' * p`
      
  have hA : q * x' * p * (q * x * p) = f := by rw [hmid, hx'e, hx'x, hqe, hqp]
  have hB : q * x * p * (q * x' * p) = f := by rw [hmid, hxe, hxx', hqe, hqp]
  exact
    ⟨⟨Or.inr ⟨q * x * p, h1.symm⟩, Or.inr ⟨q * x' * p, hA.symm⟩⟩,
      ⟨Or.inr ⟨q * x * p, h2.symm⟩, Or.inr ⟨q * x' * p, hB.symm⟩⟩⟩


-- @@ L230-264 expanded
/-- **The H-class groups of D-related idempotents are isomorphic**: with the group
structures `IsIdempotentElem.hClassGroup`, conjugation `x ↦ q * x * p` by a linking
pair is a multiplicative equivalence from the H-class of `e` onto the H-class of `f`. -/
theorem exists_hClass_mulEquiv {e f : S} (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (hD : IsGreenD e f) :
    letI := he.hClassGroup
    letI := hf.hClassGroup
    Nonempty (IsGreenH.eqvClass e ≃* IsGreenH.eqvClass f) :=
  by
  letI := he.hClassGroup
  letI := hf.hClassGroup
  obtain ⟨p, q, hpq, hqp, hep, hpf, hfq, hqe⟩ := hD.exists_linking_pair he hf
  refine
    ⟨⟨⟨fun x => ⟨q * x.1 * p, IsGreenH.conj_mem he hpq hqp hpf hfq hqe x.2⟩, fun y =>
          ⟨p * y.1 * q, IsGreenH.conj_mem hf hqp hpq hqe hep hpf y.2⟩, fun x => ?_, fun y => ?_⟩,
        fun x y => ?_⟩⟩
  · apply Subtype.ext
    change p * (q * x.1 * p) * q = x.1
    have hex : e * x.1 = x.1 := IsGreenH.mul_left_eq_self he x.2
    have hxe : x.1 * e = x.1 := IsGreenH.mul_right_eq_self he x.2
    calc
      p * (q * x.1 * p) * q = p * q * x.1 * (p * q) := by simp only [mul_assoc]
      _ = x.1 := by rw [hpq, hex, hxe]
  · apply Subtype.ext
    change q * (p * y.1 * q) * p = y.1
    have hfy : f * y.1 = y.1 := IsGreenH.mul_left_eq_self hf y.2
    have hyf : y.1 * f = y.1 := IsGreenH.mul_right_eq_self hf y.2
    calc
      q * (p * y.1 * q) * p = q * p * y.1 * (q * p) := by simp only [mul_assoc]
      _ = y.1 := by rw [hqp, hfy, hyf]
  · apply Subtype.ext
    change q * (x.1 * y.1) * p = q * x.1 * p * (q * y.1 * p)
    have hey : e * y.1 = y.1 := IsGreenH.mul_left_eq_self he y.2
    calc
      q * (x.1 * y.1) * p = q * (x.1 * (e * y.1)) * p := by rw [hey]
      _ = q * x.1 * p * (q * y.1 * p) := by
        symm
        calc
          q * x.1 * p * (q * y.1 * p) = q * (x.1 * (p * q * y.1)) * p := by simp only [mul_assoc]
          _ = q * (x.1 * (e * y.1)) * p := by rw [hpq]


-- @@ L266-266 verbatim
end IsomorphismTheorem
