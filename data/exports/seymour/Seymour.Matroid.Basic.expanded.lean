import Mathlib.Data.Matroid.Sum
import Seymour.Basic.Basic


-- @@ L4-8 verbatim
/-!
# Basic stuff about matroids

This file provides lemmas about matroids that are not present in Mathlib.
-/


-- @@ L10-10 verbatim
variable {α : Type*}


-- @@ L12-16 expanded
/--
The sum of two matroids on disjoint ground sets of the same type is a matroid whose ground set is a union of the ground sets
    of the summands, in which a subset of said ground set is independent iff its intersections with respective ground set are
    independent in each matroid. -/
abbrev Disjoint.matroidSum {Mₗ Mᵣ : Matroid α} (hEE : Disjoint Mₗ.E Mᵣ.E) : Matroid α :=
  Matroid.disjointSum Mₗ Mᵣ hEE


-- @@ L19-19 verbatim
variable {M : Matroid α} {G I : Set α}


-- @@ L21-22 expanded
lemma Matroid.IsBase.not_ssubset_indep (hMG : M.IsBase G) (hMI : M.Indep I) : ¬(G ⊂ I) :=
  ((Iff.mp M.isBase_iff_maximal_indep) hMG).not_ssuperset hMI


-- @@ L24-27 verbatim
lemma Matroid.Indep.finite_of_finite_base (hMI : M.Indep I) (hMG : M.IsBase G) (hG : Finite G) :
    Finite I := by
  have ⟨_, hM, hI⟩ := hMI.exists_isBase_superset
  exact (hMG.finite_of_finite hG hM).subset hI
