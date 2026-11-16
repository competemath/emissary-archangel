/-
Copyright (c) 2026 Timothy Harvey and James Mitchell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timothy Harvey
-/
import Semigroup.GreensRelations.Classes


-- @@ L8-35 verbatim
/-!
# Rees Coordinates: D-Class Representatives

The index types and chosen representatives used by the Rees construction:
`ReesRIndex e` (resp. `ReesLIndex e`) enumerates the R-classes (resp.
L-classes) meeting the D-class of `e`, and `rowRep`/`colRep` choose in each
such class an element L-related (resp. R-related) to `e` — such elements
exist by Green's lemma applied inside the D-class. The existence lemmas
`exists_rowRep`/`exists_colRep` live here because the definitions choose
from them; the lemmas about the chosen representatives live in
`Semigroup.Rees.Basic`.

## Main definitions

* `ReesRIndex`, `ReesLIndex`: the R-classes (resp. L-classes) meeting the D-class of `e`.
* `rowRep`, `colRep`: chosen elements of these classes that are L-related
  (resp. R-related) to `e`.

## References

* [J. M. Howie, *Fundamentals of Semigroup Theory*][howie1995]

The proofs formalized in this module closely follow the structure and logic
from lecture notes:

* J. D. Mitchell, *MT5863 Semigroup Theory* (lecture notes,
  University of St Andrews, 2026).
-/


-- @@ L37-37 verbatim
open scoped GreensRelations


-- @@ L39-39 verbatim
variable {S : Type*} [Semigroup S]


-- @@ L41-41 verbatim
section DClassRepresentatives


-- @@ L43-45 expanded
/-- The R-classes meeting the D-class of `e`. -/
def ReesRIndex (e : S) : Type _ :=
  { c : GreenRClass S // ∃ a : S, c = GreenRClass.mk a ∧ IsGreenD a e }


-- @@ L47-49 expanded
/-- The L-classes meeting the D-class of `e`. -/
def ReesLIndex (e : S) : Type _ :=
  { c : GreenLClass S // ∃ a : S, c = GreenLClass.mk a ∧ IsGreenD a e }


-- @@ L51-56 expanded
/-- Every R-class meeting the D-class of `e` contains an element L-related to `e`. -/
theorem exists_rowRep (e : S) (i : ReesRIndex e) : ∃ r : S, GreenRClass.mk r = i.1 ∧ IsGreenL r e :=
  by
  obtain ⟨c, a, rfl, haD⟩ := i
  obtain ⟨z, hzL, hzR⟩ := haD.symm
  exact ⟨z, GreenRClass.mk_eq_mk_iff.mpr hzR, hzL.symm⟩


-- @@ L58-63 expanded
/-- Every L-class meeting the D-class of `e` contains an element R-related to `e`. -/
theorem exists_colRep (e : S) (l : ReesLIndex e) : ∃ q : S, GreenLClass.mk q = l.1 ∧ IsGreenR q e :=
  by
  obtain ⟨c, a, rfl, haD⟩ := l
  obtain ⟨z, hzL, hzR⟩ := haD
  exact ⟨z, GreenLClass.mk_eq_mk_iff.mpr hzL.symm, hzR⟩


-- @@ L65-67 verbatim
/-- A chosen element of the R-class `i` that is L-related to `e`. -/
noncomputable def rowRep (e : S) (i : ReesRIndex e) : S :=
  (exists_rowRep e i).choose


-- @@ L69-71 verbatim
/-- A chosen element of the L-class `l` that is R-related to `e`. -/
noncomputable def colRep (e : S) (l : ReesLIndex e) : S :=
  (exists_colRep e l).choose


-- @@ L73-73 verbatim
end DClassRepresentatives
