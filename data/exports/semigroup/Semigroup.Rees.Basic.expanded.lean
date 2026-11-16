/-
Copyright (c) 2026 Timothy Harvey and James Mitchell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timothy Harvey
-/
import Semigroup.GreensRelations.Idempotents
import Semigroup.GreensTheorem.HClass.Basic
import Semigroup.Rees.Defs


-- @@ L10-39 verbatim
/-!
# Rees Coordinates: Helper Lemmas

This file collects the helper machinery supporting the Rees theorem
(`Semigroup.ZeroSimple.ReesTheorem`): retraction and factorization lemmas at an
idempotent, location and cancellation facts for `r * g * q` decompositions, and
the lemmas about the chosen D-class representatives `rowRep`/`colRep` defined
in `Semigroup.Rees.Defs`.

## Main results

* `IsGreenL.exists_left_retraction`, `IsGreenR.exists_right_retraction`: retractions
  onto an idempotent from L-related (resp. R-related) elements.
* `exists_factor_right`, `exists_factor_left`: factorizations of one-sided multiples
  through an idempotent.
* `hClass_coord_unique`: the middle H-class coordinate of a decomposition `r * g * q`
  is uniquely determined.
* `isGreenR_left_of_repr`, `isGreenL_right_of_repr`: in a decomposition `x = r * g * q`,
  the element `x` is R-related to `r` and L-related to `q`.

## References

* [J. M. Howie, *Fundamentals of Semigroup Theory*][howie1995]

The proofs formalized in this module closely follow the structure and logic
from lecture notes:

* J. D. Mitchell, *MT5863 Semigroup Theory* (lecture notes,
  University of St Andrews, 2026).
-/


-- @@ L41-41 verbatim
open scoped GreensRelations


-- @@ L43-43 verbatim
variable {S : Type*} [Semigroup S]


-- @@ L45-45 verbatim
/-! ### Retraction and factorization helpers -/


-- @@ L47-47 verbatim
section Retraction


-- @@ L49-53 expanded
/-- From `r L e` (`e` idempotent) extract `ř` with `ř * r = e` and `e * ř = ř`. -/
theorem IsGreenL.exists_left_retraction {r e : S} (he : IsIdempotentElem e) (h : IsGreenL r e) :
    ∃ w, w * r = e ∧ e * w = w :=
  by
  obtain ⟨u, hu⟩ := IsGreenLeftDvd.exists_eq_mul_of_idem he h.2
  exact ⟨e * u, by rw [mul_assoc, ← hu, he.eq], by rw [← mul_assoc, he.eq]⟩


-- @@ L55-59 expanded
/-- From `c R e` (`e` idempotent) extract `ĉ` with `c * ĉ = e` and `ĉ * e = ĉ`. -/
theorem IsGreenR.exists_right_retraction {c e : S} (he : IsIdempotentElem e) (h : IsGreenR c e) :
    ∃ w, c * w = e ∧ w * e = w :=
  by
  obtain ⟨d, hd⟩ := IsGreenRightDvd.exists_eq_mul_of_idem he h.2
  exact ⟨d * e, by rw [← mul_assoc, ← hd, he.eq], by rw [mul_assoc, he.eq]⟩


-- @@ L61-67 expanded
/-- If `x` is a right multiple of `r` (in the `S¹` sense) and `r * e = r`,
then `x = r * m` for some `m` absorbed by `e` on the left. -/
theorem exists_factor_right {r x e : S} (he : IsIdempotentElem e) (hre : r * e = r)
    (h : IsGreenRightDvd x r) : ∃ m, x = r * m ∧ e * m = m :=
  by
  rcases h with rfl | ⟨a, ha⟩
  · exact ⟨e, hre.symm, he.eq⟩
  · exact ⟨e * a, by rw [ha, ← mul_assoc, hre], by rw [← mul_assoc, he.eq]⟩


-- @@ L69-75 expanded
/-- If `x` is a left multiple of `c` (in the `S¹` sense) and `e * c = c`,
then `x = n * c` for some `n` absorbed by `e` on the right. -/
theorem exists_factor_left {c x e : S} (he : IsIdempotentElem e) (hec : e * c = c)
    (h : IsGreenLeftDvd x c) : ∃ n, x = n * c ∧ n * e = n :=
  by
  rcases h with rfl | ⟨a, ha⟩
  · exact ⟨e, hec.symm, he.eq⟩
  · exact ⟨a * e, by rw [ha, mul_assoc, hec], by rw [mul_assoc, he.eq]⟩


-- @@ L77-77 verbatim
end Retraction


-- @@ L79-79 verbatim
/-! ### Location and cancellation for `r * g * q` decompositions -/


-- @@ L81-81 verbatim
section Location


-- @@ L83-98 expanded
/-- If `r` is L-related and `g` is H-related to the idempotent `e`, then the
product `r * g` is again L-related to `e`. -/
theorem isGreenL_mul_of_isGreenL_of_isGreenH {e r g : S} (he : IsIdempotentElem e)
    (hr : IsGreenL r e) (hg : IsGreenH g e) : IsGreenL (r * g) e :=
  by
  obtain ⟨w, hwr, _⟩ := hr.exists_left_retraction he
  obtain ⟨g', _, _, hg'g⟩ := IsGreenH.exists_inv he hg
  constructor
  · rcases hg.1.1 with rfl | ⟨c, rfl⟩
    · exact Or.inr ⟨r, rfl⟩
    · exact Or.inr ⟨r * c, (mul_assoc r c e).symm⟩
  · refine Or.inr ⟨g' * w, ?_⟩
    have hge : e * g = g := IsGreenH.mul_left_eq_self he hg
    calc
      e = g' * g := hg'g.symm
      _ = g' * (e * g) := by rw [hge]
      _ = g' * (w * r * g) := by rw [hwr]
      _ = g' * w * (r * g) := by simp only [mul_assoc]


-- @@ L100-115 expanded
/-- If `g` is H-related and `q` is R-related to the idempotent `e`, then the
product `g * q` is again R-related to `e`. -/
theorem isGreenR_mul_of_isGreenH_of_isGreenR {e g q : S} (he : IsIdempotentElem e)
    (hg : IsGreenH g e) (hq : IsGreenR q e) : IsGreenR (g * q) e :=
  by
  obtain ⟨w, hqw, _⟩ := hq.exists_right_retraction he
  obtain ⟨g', _, hgg', _⟩ := IsGreenH.exists_inv he hg
  constructor
  · rcases hg.2.1 with rfl | ⟨c, rfl⟩
    · exact Or.inr ⟨q, rfl⟩
    · exact Or.inr ⟨c * q, mul_assoc e c q⟩
  · refine Or.inr ⟨w * g', ?_⟩
    have hge : g * e = g := IsGreenH.mul_right_eq_self he hg
    calc
      e = g * g' := hgg'.symm
      _ = g * e * g' := by rw [hge]
      _ = g * (q * w) * g' := by rw [hqw]
      _ = g * q * (w * g') := by simp only [mul_assoc]


-- @@ L117-133 expanded
/-- Green's-lemma cancellation for Rees coordinates: the middle H-class
coordinate of a decomposition `r * g * q` (with `r L e`, `q R e`) is
uniquely determined. -/
theorem hClass_coord_unique {e r q g₁ g₂ : S} (he : IsIdempotentElem e) (hr : IsGreenL r e)
    (hq : IsGreenR q e) (hg₁ : IsGreenH g₁ e) (hg₂ : IsGreenH g₂ e) (h : r * g₁ * q = r * g₂ * q) :
    g₁ = g₂ := by
  obtain ⟨w, hwr, _⟩ := hr.exists_left_retraction he
  obtain ⟨w', hqw', _⟩ := hq.exists_right_retraction he
  have cancel : ∀ g : S, IsGreenH g e → w * (r * g * q) * w' = g :=
    by
    intro g hg
    calc
      w * (r * g * q) * w' = w * r * g * (q * w') := by simp only [mul_assoc]
      _ = e * g * e := by rw [hwr, hqw']
      _ = g := by rw [IsGreenH.mul_left_eq_self he hg, IsGreenH.mul_right_eq_self he hg]
  calc
    g₁ = w * (r * g₁ * q) * w' := (cancel g₁ hg₁).symm
    _ = w * (r * g₂ * q) * w' := by rw [h]
    _ = g₂ := cancel g₂ hg₂


-- @@ L135-152 expanded
/-- In a decomposition `x = r * g * q` with `r L e`, `g H e`, `q R e`, the
element `x` is R-related to the left factor `r`. -/
theorem isGreenR_left_of_repr {e r g q x : S} (he : IsIdempotentElem e) (hr : IsGreenL r e)
    (hg : IsGreenH g e) (hq : IsGreenR q e) (hrep : x = r * g * q) : IsGreenR x r :=
  by
  have hre : r * e = r := IsGreenLeftDvd.mul_idem_eq_self he hr.1
  have hgq : IsGreenR (g * q) e := isGreenR_mul_of_isGreenH_of_isGreenR he hg hq
  constructor
  · exact Or.inr ⟨g * q, by rw [hrep]; simp only [mul_assoc]⟩
  · rcases hgq.2 with hgqe | ⟨c, hc⟩
    ·
      exact
        Or.inl
          (by
            calc
              r = r * e := hre.symm
              _ = r * (g * q) := by rw [hgqe]
              _ = x := by rw [hrep]; simp only [mul_assoc])
    · refine Or.inr ⟨c, ?_⟩
      calc
        r = r * e := hre.symm
        _ = r * (g * q * c) := by rw [hc]
        _ = x * c := by rw [hrep]; simp only [mul_assoc]


-- @@ L154-171 expanded
/-- In a decomposition `x = r * g * q` with `r L e`, `g H e`, `q R e`, the
element `x` is L-related to the right factor `q`. -/
theorem isGreenL_right_of_repr {e r g q x : S} (he : IsIdempotentElem e) (hr : IsGreenL r e)
    (hg : IsGreenH g e) (hq : IsGreenR q e) (hrep : x = r * g * q) : IsGreenL x q :=
  by
  have heq : e * q = q := IsGreenRightDvd.idem_mul_eq_self he hq.1
  have hrg : IsGreenL (r * g) e := isGreenL_mul_of_isGreenL_of_isGreenH he hr hg
  constructor
  · exact Or.inr ⟨r * g, hrep⟩
  · rcases hrg.2 with hrge | ⟨c, hc⟩
    ·
      exact
        Or.inl
          (by
            calc
              q = e * q := heq.symm
              _ = r * g * q := by rw [hrge]
              _ = x := hrep.symm)
    · refine Or.inr ⟨c, ?_⟩
      calc
        q = e * q := heq.symm
        _ = c * (r * g) * q := by rw [hc]
        _ = c * x := by rw [hrep]; simp only [mul_assoc]


-- @@ L173-173 verbatim
end Location


-- @@ L175-175 verbatim
/-! ### Lemmas about the chosen D-class representatives -/


-- @@ L177-177 verbatim
section DClassRepresentatives


-- @@ L179-181 verbatim
/-- The representative `rowRep e i` lies in the R-class `i`. -/
theorem rowRep_mk (e : S) (i : ReesRIndex e) : GreenRClass.mk (rowRep e i) = i.1 :=
  (exists_rowRep e i).choose_spec.1


-- @@ L183-185 expanded
/-- The representative `rowRep e i` is L-related to `e`. -/
theorem rowRep_isGreenL (e : S) (i : ReesRIndex e) : IsGreenL (rowRep e i) e :=
  (exists_rowRep e i).choose_spec.2


-- @@ L187-189 verbatim
/-- The representative `colRep e l` lies in the L-class `l`. -/
theorem colRep_mk (e : S) (l : ReesLIndex e) : GreenLClass.mk (colRep e l) = l.1 :=
  (exists_colRep e l).choose_spec.1


-- @@ L191-193 expanded
/-- The representative `colRep e l` is R-related to `e`. -/
theorem colRep_isGreenR (e : S) (l : ReesLIndex e) : IsGreenR (colRep e l) e :=
  (exists_colRep e l).choose_spec.2


-- @@ L195-199 verbatim
/-- The idempotent `e` is a right identity for `rowRep e i`, since `rowRep e i` is
L-related to `e`. -/
theorem rowRep_mul_idem {e : S} (he : IsIdempotentElem e) (i : ReesRIndex e) :
    rowRep e i * e = rowRep e i :=
  IsGreenLeftDvd.mul_idem_eq_self he (rowRep_isGreenL e i).1


-- @@ L201-205 verbatim
/-- The idempotent `e` is a left identity for `colRep e l`, since `colRep e l` is
R-related to `e`. -/
theorem idem_mul_colRep {e : S} (he : IsIdempotentElem e) (l : ReesLIndex e) :
    e * colRep e l = colRep e l :=
  IsGreenRightDvd.idem_mul_eq_self he (colRep_isGreenR e l).1


-- @@ L207-207 verbatim
end DClassRepresentatives
