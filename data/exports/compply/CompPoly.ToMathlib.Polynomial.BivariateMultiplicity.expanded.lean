/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import CompPoly.ToMathlib.Polynomial.BivariateDegree
public import Mathlib.RingTheory.Polynomial.Resultant.Basic


-- @@ L11-16 verbatim
/-!
# Mathlib-Facing Bivariate Multiplicity Helpers

This file collects multiplicity- and discriminant-oriented helpers for Mathlib's
bivariate polynomial surface `R[X][Y]`.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
open Polynomial

-- @@ L21-21 verbatim
open scoped Polynomial.Bivariate


-- @@ L23-23 verbatim
namespace Polynomial.Bivariate


-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-27 verbatim
variable {F : Type*}


-- @@ L29-29 verbatim
section Semiring


-- @@ L31-31 verbatim
variable [Semiring F]


-- @@ L33-42 verbatim
/-- Root multiplicity of a bivariate polynomial at the origin. -/
def rootMultiplicity₀ [DecidableEq F] (f : F[X][Y]) : Option ℕ :=
  let deg := weightedDegree f 1 1
  match deg with
  | none => none
  | some deg =>
      List.min? <|
        List.filterMap
          (fun (i, j) ↦ if coeff f i j = 0 then none else some (i + j))
          (List.product (List.range deg.succ) (List.range deg.succ))


-- @@ L44-44 verbatim
end Semiring


-- @@ L46-46 verbatim
section CommSemiring


-- @@ L48-48 verbatim
variable [CommSemiring F]


-- @@ L50-52 verbatim
/-- Shift a bivariate polynomial by `(x, y)`. -/
def shift (f : F[X][Y]) (x y : F) : F[X][Y] :=
  (f.comp (Y + C (C y))).map (Polynomial.compRingHom (X + C x : F[X]))


-- @@ L54-54 verbatim
variable [DecidableEq F]


-- @@ L56-58 verbatim
/-- Root multiplicity (order of vanishing) of a bivariate polynomial at `(x, y)`. -/
def rootMultiplicity (f : F[X][Y]) (x y : F) : Option ℕ :=
  rootMultiplicity₀ (shift f x y)


-- @@ L60-106 verbatim
/-- `rootMultiplicity₀ g` is at least `r` (vacuously so when `g = 0`, where it is `none`)
iff every coefficient of total degree `< r` vanishes. -/
theorem rootMultiplicity₀_ge_iff (g : F[X][Y]) (r : ℕ) :
    (∀ i j, i + j < r → coeff g i j = 0) ↔ ∀ m ∈ rootMultiplicity₀ g, r ≤ m := by
  obtain ⟨deg, hdeg⟩ : ∃ d, weightedDegree g 1 1 = some d :=
    ⟨natWeightedDegree g 1 1, weightedDegree_eq_natWeightedDegree⟩
  have hdegval : deg = natWeightedDegree g 1 1 := by
    have h := weightedDegree_eq_natWeightedDegree (f := g) (u := 1) (v := 1)
    rw [hdeg] at h; exact Option.some.inj h
  have hroot : rootMultiplicity₀ g =
      (List.filterMap (fun p : ℕ × ℕ ↦ if coeff g p.1 p.2 = 0 then none else some (p.1 + p.2))
        (List.range (deg + 1) ×ˢ List.range (deg + 1))).min? := by
    simp only [rootMultiplicity₀, hdeg]; rfl
  have grid_mem : ∀ i j, coeff g i j ≠ 0 →
      (i, j) ∈ List.range (deg + 1) ×ˢ List.range (deg + 1) := by
    intro i j hne
    have hi : i ≤ (g.coeff j).natDegree := le_natDegree_of_ne_zero (by simpa [coeff] using hne)
    have hbound : (g.coeff j).natDegree + j ≤ deg := by
      rw [hdegval]
      simpa [natWeightedDegree] using
        Finset.le_sup (f := fun m => 1 * (g.coeff m).natDegree + 1 * m)
          (Polynomial.mem_support_iff.mpr fun h => hne (by simp [coeff, h]))
    simp only [List.mem_product, List.mem_range]; omega
  rw [hroot]
  set L := List.filterMap (fun p : ℕ × ℕ ↦ if coeff g p.1 p.2 = 0 then none else some (p.1 + p.2))
      (List.range (deg + 1) ×ˢ List.range (deg + 1)) with hL
  constructor
  · intro H m hm
    rw [Option.mem_def] at hm
    have hmem := List.min?_mem hm
    rw [hL, List.mem_filterMap] at hmem
    obtain ⟨⟨i, j⟩, _, hsome⟩ := hmem
    by_cases hz : coeff g i j = 0
    · simp [hz] at hsome
    · simp only [hz, if_false, Option.some.injEq] at hsome
      subst hsome; by_contra hlt; exact hz (H i j (by omega))
  · intro H i j hij
    by_contra hne
    have hmem : i + j ∈ L := by
      rw [hL, List.mem_filterMap]; exact ⟨(i, j), grid_mem i j hne, by simp [hne]⟩
    obtain ⟨m₀, hm₀⟩ : ∃ m₀, L.min? = some m₀ := by
      cases hc : L.min? with
      | none => simp [List.min?_eq_none_iff.mp hc] at hmem
      | some m₀ => exact ⟨m₀, rfl⟩
    have hr := H m₀ (Option.mem_def.mpr hm₀)
    have hle := (List.min?_eq_some_iff.mp hm₀).2 _ hmem
    omega


-- @@ L108-108 verbatim
end CommSemiring


-- @@ L110-110 verbatim
section CommRing


-- @@ L112-112 verbatim
variable [CommRing F]


-- @@ L114-121 verbatim
/-- A discriminant-like helper in the outer `Y` variable.

Unlike Mathlib's univariate `discr`, this returns `0` for constant bivariate polynomials. -/
def discr_y (f : F[X][Y]) : F[X] :=
  if 0 < f.degree then
    (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.discr
  else
    0


-- @@ L123-123 verbatim
end CommRing


-- @@ L125-125 verbatim
end

-- @@ L126-126 verbatim
end Polynomial.Bivariate
