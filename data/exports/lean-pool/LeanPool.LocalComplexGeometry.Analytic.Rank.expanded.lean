/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/
module

public import LeanPool.LocalComplexGeometry.Germs.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Tactic.Positivity.Finset


-- @@ L16-23 verbatim
/-!
# Complex rank in finite-dimensional coordinate spaces

This file defines the complex rank of a continuous complex-linear map and the
standard rank-`r` coordinate map from `ℂⁿ` to `ℂᵐ`.  The latter is a total
definition for arbitrary `n`, `m`, and `r`; its rank is exactly `r` when
`r ≤ n` and `r ≤ m`.
-/


-- @@ L25-25 verbatim
@[expose] public section



-- @@ L28-28 verbatim
namespace LocalComplexGeometry


-- @@ L30-30 verbatim
noncomputable section


-- @@ L32-35 verbatim
/-- The complex dimension of the range of a continuous complex-linear map. -/
def complexRank {n m : ℕ}
    (A : ComplexEuclidean n →L[ℂ] ComplexEuclidean m) : ℕ :=
  Module.finrank ℂ (LinearMap.range A.toLinearMap)


-- @@ L37-43 verbatim
/-- Complex rank is bounded by the dimension of the source. -/
theorem complexRank_le_source {n m : ℕ}
    (A : ComplexEuclidean n →L[ℂ] ComplexEuclidean m) :
    complexRank A ≤ n := by
  change Module.finrank ℂ (LinearMap.range A.toLinearMap) ≤ n
  simpa only [Module.finrank_fin_fun] using
    (LinearMap.finrank_range_le A.toLinearMap)


-- @@ L45-51 verbatim
/-- Complex rank is bounded by the dimension of the target. -/
theorem complexRank_le_target {n m : ℕ}
    (A : ComplexEuclidean n →L[ℂ] ComplexEuclidean m) :
    complexRank A ≤ m := by
  change Module.finrank ℂ (LinearMap.range A.toLinearMap) ≤ m
  simpa only [Module.finrank_fin_fun] using
    (LinearMap.range A.toLinearMap).finrank_le


-- @@ L53-60 verbatim
/-- The standard rank map: retain a coordinate precisely when its index is
available in the source and is strictly less than `r`, and put zero elsewhere. -/
def standardRankContinuousLinearMap (n m r : ℕ) :
    ComplexEuclidean n →L[ℂ] ComplexEuclidean m :=
  ContinuousLinearMap.pi fun j ↦
    if h : j.1 < n ∧ j.1 < r then
      ContinuousLinearMap.proj (R := ℂ) (i := ⟨j.1, h.1⟩)
    else 0


-- @@ L62-65 verbatim
/-- The underlying function of `standardRankContinuousLinearMap`. -/
def standardRankMap (n m r : ℕ) :
    ComplexEuclidean n → ComplexEuclidean m :=
  standardRankContinuousLinearMap n m r


-- @@ L67-73 verbatim
@[simp]
theorem standardRankContinuousLinearMap_apply (n m r : ℕ)
    (x : ComplexEuclidean n) (j : Fin m) :
    standardRankContinuousLinearMap n m r x j =
      if h : j.1 < n ∧ j.1 < r then x ⟨j.1, h.1⟩ else 0 := by
  simp only [standardRankContinuousLinearMap, ContinuousLinearMap.pi_apply]
  split_ifs <;> rfl


-- @@ L75-80 verbatim
@[simp]
theorem standardRankMap_apply (n m r : ℕ)
    (x : ComplexEuclidean n) (j : Fin m) :
    standardRankMap n m r x j =
      if h : j.1 < n ∧ j.1 < r then x ⟨j.1, h.1⟩ else 0 := by
  simp [standardRankMap]


-- @@ L82-86 verbatim
/-- Restrict a coordinate vector to its first `r` coordinates. -/
def takeFirstContinuousLinearMap {n r : ℕ} (hrn : r ≤ n) :
    ComplexEuclidean n →L[ℂ] ComplexEuclidean r :=
  ContinuousLinearMap.pi fun j ↦
    ContinuousLinearMap.proj (R := ℂ) (i := Fin.castLE hrn j)


-- @@ L88-92 verbatim
@[simp]
theorem takeFirstContinuousLinearMap_apply {n r : ℕ} (hrn : r ≤ n)
    (x : ComplexEuclidean n) (j : Fin r) :
    takeFirstContinuousLinearMap hrn x j = x (Fin.castLE hrn j) :=
  rfl


-- @@ L94-100 verbatim
/-- Extend an `r`-tuple by zero to an `m`-tuple. -/
def includeFirstContinuousLinearMap (m r : ℕ) :
    ComplexEuclidean r →L[ℂ] ComplexEuclidean m :=
  ContinuousLinearMap.pi fun j ↦
    if h : j.1 < r then
      ContinuousLinearMap.proj (R := ℂ) (i := ⟨j.1, h⟩)
    else 0


-- @@ L102-108 verbatim
@[simp]
theorem includeFirstContinuousLinearMap_apply (m r : ℕ)
    (x : ComplexEuclidean r) (j : Fin m) :
    includeFirstContinuousLinearMap m r x j =
      if h : j.1 < r then x ⟨j.1, h⟩ else 0 := by
  simp only [includeFirstContinuousLinearMap, ContinuousLinearMap.pi_apply]
  split_ifs <;> rfl


-- @@ L110-118 verbatim
/-- Restriction to the first `r` coordinates is onto when `r ≤ n`. -/
theorem takeFirstContinuousLinearMap_surjective {n r : ℕ} (hrn : r ≤ n) :
    Function.Surjective (takeFirstContinuousLinearMap hrn) := by
  intro y
  let x : ComplexEuclidean n := fun i ↦
    if h : i.1 < r then y ⟨i.1, h⟩ else 0
  refine ⟨x, ?_⟩
  funext j
  simp [x, takeFirstContinuousLinearMap_apply]


-- @@ L120-126 verbatim
/-- Zero-extension of the first `r` coordinates is injective when `r ≤ m`. -/
theorem includeFirstContinuousLinearMap_injective {m r : ℕ} (hrm : r ≤ m) :
    Function.Injective (includeFirstContinuousLinearMap m r) := by
  intro x y hxy
  funext j
  have h := congrFun hxy (Fin.castLE hrm j)
  simpa using h


-- @@ L128-141 verbatim
/-- Under `r ≤ n`, the standard map factors as restriction to `ℂʳ`
followed by zero-extension. -/
theorem standardRankContinuousLinearMap_eq_comp {n m r : ℕ} (hrn : r ≤ n) :
    standardRankContinuousLinearMap n m r =
      (includeFirstContinuousLinearMap m r).comp
        (takeFirstContinuousLinearMap hrn) := by
  ext x j
  by_cases hj : j.1 < r
  · have hjn : j.1 < n := lt_of_lt_of_le hj hrn
    simp [standardRankContinuousLinearMap_apply,
      includeFirstContinuousLinearMap_apply,
      takeFirstContinuousLinearMap_apply, hj, hjn]
  · simp [standardRankContinuousLinearMap_apply,
      includeFirstContinuousLinearMap_apply, hj]


-- @@ L143-155 verbatim
/-- The standard coordinate map has complex rank `r` whenever `r` fits in
both source and target.  This includes the zero-dimensional cases. -/
theorem complexRank_standardRankContinuousLinearMap {n m r : ℕ}
    (hrn : r ≤ n) (hrm : r ≤ m) :
    complexRank (standardRankContinuousLinearMap n m r) = r := by
  rw [standardRankContinuousLinearMap_eq_comp hrn]
  unfold complexRank
  rw [ContinuousLinearMap.toLinearMap_comp]
  rw [LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (takeFirstContinuousLinearMap_surjective hrn))]
  rw [LinearMap.finrank_range_of_inj
    (includeFirstContinuousLinearMap_injective hrm)]
  exact Module.finrank_fin_fun ℂ


-- @@ L157-164 verbatim
/-- The Fréchet derivative of the standard coordinate map is the standard
continuous linear map itself. -/
@[simp]
theorem fderiv_standardRankMap (n m r : ℕ) (x : ComplexEuclidean n) :
    fderiv ℂ (standardRankMap n m r) x =
      standardRankContinuousLinearMap n m r := by
  simpa only [standardRankMap] using
    (standardRankContinuousLinearMap n m r).fderiv


-- @@ L166-171 verbatim
/-- Pointwise formulation of the exact-rank calculation. -/
theorem complexRank_fderiv_standardRankMap {n m r : ℕ}
    (hrn : r ≤ n) (hrm : r ≤ m) (x : ComplexEuclidean n) :
    complexRank (fderiv ℂ (standardRankMap n m r) x) = r := by
  rw [fderiv_standardRankMap]
  exact complexRank_standardRankContinuousLinearMap hrn hrm


-- @@ L173-173 verbatim
end


-- @@ L175-175 verbatim
end LocalComplexGeometry
