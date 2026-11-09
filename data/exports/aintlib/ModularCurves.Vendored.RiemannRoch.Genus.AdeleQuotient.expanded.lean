/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
module

public import ModularCurves.Vendored.RiemannRoch.AdeleSpace.FilterChain
public import ModularCurves.Vendored.RiemannRoch.Genus.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring


-- @@ L16-20 verbatim
/-!
# Adele quotient rank and the index of specialty
This file proves Stichtenoth 1.5.4: the rank of `𝒜_K/(A(D)+K̃)` equals the specialty
index `i(D)`.
-/


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
open scoped nonZeroDivisors Polynomial RatFunc WithZero

-- @@ L25-25 verbatim
open Filter


-- @@ L27-27 verbatim
noncomputable section


-- @@ L29-29 verbatim
namespace FunctionField.Chart


-- @@ L31-31 verbatim
variable (k K : Type*) [Field k] [Field K]


-- @@ L33-35 verbatim
variable [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K] [IsScalarTower k k[X] K]
  [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]


-- @@ L37-37 verbatim
variable [IsFullConstantField k K]


-- @@ L39-40 verbatim
/-- The classical decidable equality on coordinate places used for adele surgery. -/
local instance instDecidableEqPlaceAAdeleQuotient : DecidableEq (PlaceA k K) := Classical.decEq _


-- @@ L42-43 verbatim
/-- The top submodule of the adele space (avoids `↥⊤` notation pitfalls). -/
def topAdeleSubmodule : Submodule k (AdeleSpace k K) := ⊤


-- @@ L45-52 verbatim
omit [IsFullConstantField k K] in
/-- Finite set of finite places where an adele component is not integral. -/
theorem exceptionalFinite (α : AdeleSpace k K) :
    {v : PlaceA k K | ¬placeValuation k K v (α.val v) ≤ 1}.Finite :=
  (Filter.eventually_cofinite.mp α.property).subset (by
    intro v hv
    change α.val v ∉ placeValuationSubring k K v
    simpa [placeValuationSubring, Valuation.mem_valuationSubring_iff] using hv)


-- @@ L54-56 verbatim
/-- Finset of finite places where an adele component is not integral. -/
def exceptionalPlaces (α : AdeleSpace k K) : Finset (PlaceA k K) :=
  (exceptionalFinite k K α).toFinset


-- @@ L58-70 verbatim
/-- Every adele lies in some filtration piece `A(D)`. -/
noncomputable def divisorOfAdele (α : AdeleSpace k K) : DivisorA k K :=
  Finsupp.onFinset (exceptionalPlaces k K α)
    (fun v =>
      if 1 < placeValuation k K v (α.val v) then
        WithZero.log (placeValuation k K v (α.val v))
      else 0)
    (by
      intro v hvne
      by_cases hlt : 1 < placeValuation k K v (α.val v)
      · dsimp [exceptionalPlaces]
        exact (exceptionalFinite k K α).mem_toFinset.mpr (not_le.mpr hlt)
      · simp [hlt] at hvne)


-- @@ L72-99 verbatim
omit [IsFullConstantField k K] in
theorem mem_adeleFilt_divisorOfAdele (α : AdeleSpace k K) :
    α ∈ adeleFilt k K (divisorOfAdele k K α) := by
  intro v
  show placeValuation k K v (α.val v) ≤ WithZero.exp ((divisorOfAdele k K α) v)
  simp only [divisorOfAdele, exceptionalPlaces, Finsupp.onFinset_apply]
  by_cases hv : placeValuation k K v (α.val v) ≤ 1
  · have hnotlt : ¬1 < placeValuation k K v (α.val v) := not_lt.mpr hv
    have hnotmem : v ∉ exceptionalPlaces k K α := by
      intro hmem
      have hgt := (exceptionalFinite k K α).mem_toFinset.mp (by
        dsimp [exceptionalPlaces] at hmem ⊢
        exact hmem)
      have hnotle : ¬placeValuation k K v (α.val v) ≤ 1 := by simpa using hgt
      exact absurd hv hnotle
    split_ifs with hlt
    · exfalso
      exact hnotlt hlt
    · simpa [WithZero.exp_zero] using hv
  · have hlt : 1 < placeValuation k K v (α.val v) := not_le.mp hv
    have hmem : v ∈ exceptionalPlaces k K α := by
      dsimp [exceptionalPlaces]
      exact (exceptionalFinite k K α).mem_toFinset.mpr (not_le.mpr hlt)
    have hval : placeValuation k K v (α.val v) ≠ 0 := ne_of_gt (zero_lt_one.trans hlt)
    split_ifs with hlt'
    · simp [WithZero.exp_log hval]
    · exfalso
      exact hlt' hlt


-- @@ L101-104 verbatim
omit [IsFullConstantField k K] in
theorem exists_adeleFilt_mem (α : AdeleSpace k K) :
    ∃ D : DivisorA k K, α ∈ adeleFilt k K D :=
  ⟨divisorOfAdele k K α, mem_adeleFilt_divisorOfAdele k K α⟩


-- @@ L106-110 verbatim
theorem defect_eq_genus_of_ge {D D' : DivisorA k K} (hle : D ≤ D')
    (hD : defect k K D = genus k K) : defect k K D' = genus k K := by
  have hle' : defect k K D ≤ defect k K D' := defect_mono' (k := k) (K := K) hle
  have hgen : defect k K D' ≤ genus k K := defect_le k K D'
  omega


-- @@ L112-119 verbatim
theorem sandwichRank_eq_zero_of_defect_eq {D D' : DivisorA k K} (hle : D ≤ D')
    (hD : defect k K D = genus k K) :
    sandwichRank k K D D' hle = 0 := by
  have hD' : defect k K D' = genus k K := defect_eq_genus_of_ge (k := k) (K := K) hle hD
  have hs := sandwich (k := k) (K := K) hle
  dsimp only [defect] at hD hD' ⊢
  rw [hs]
  omega


-- @@ L121-125 verbatim
omit [IsFullConstantField k K] in
theorem adeleFilt_add_diagonal_eq_of_sandwich_zero {D D' : DivisorA k K} (hle : D ≤ D')
    (h0 : sandwichRank k K D D' hle = 0) :
    adeleFilt k K D' + diagonalSubmodule k K = adeleFilt k K D + diagonalSubmodule k K :=
  sandwichDiagonalSubmodule_eq_of_rank_zero (k := k) (K := K) hle h0


-- @@ L127-144 verbatim
theorem adeleSubmodule_top_eq_adeleFilt_add_diagonal {D : DivisorA k K}
    (hD : defect k K D = genus k K) :
    topAdeleSubmodule k K = adeleFilt k K D + diagonalSubmodule k K := by
  apply le_antisymm
  · intro α _
    obtain ⟨Dα, hDα⟩ := exists_adeleFilt_mem (k := k) (K := K) α
    let D' := D ⊔ Dα
    have hD' : defect k K D' = genus k K :=
      defect_eq_genus_of_ge (k := k) (K := K) (le_sup_left (a := D) (b := Dα)) hD
    have h0 := sandwichRank_eq_zero_of_defect_eq (k := k) (K := K) (D := D) (D' := D')
      (le_sup_left (a := D) (b := Dα)) hD
    have heq := adeleFilt_add_diagonal_eq_of_sandwich_zero (k := k) (K := K) (D := D) (D' := D')
      (le_sup_left (a := D) (b := Dα)) h0
    have hmem : α ∈ adeleFilt k K D' + diagonalSubmodule k K :=
      Submodule.mem_sup_left (adeleFilt_mono (k := k) (K := K) le_sup_right hDα)
    rw [heq] at hmem
    exact hmem
  · exact le_top


-- @@ L146-172 verbatim
omit [IsFullConstantField k K] in
theorem finrankAdeleQuotient_eq_sandwichRank {D D' : DivisorA k K} (hle : D ≤ D')
    (hfull : topAdeleSubmodule k K = adeleFilt k K D' + diagonalSubmodule k K) :
    finrankAdeleQuotient k K D = (sandwichRank k K D D' hle).toNat := by
  classical
  let ssum := adeleFilt k K D + diagonalSubmodule k K
  let topMod := topAdeleSubmodule k K
  letI : AddCommGroup ↥topMod := Submodule.addCommGroup _
  letI : Module k ↥topMod := Submodule.module _
  let p := Submodule.comap topMod.subtype ssum
  let e : ↥topMod ≃ₗ[k] AdeleSpace k K :=
    Submodule.topEquiv (R := k) (M := AdeleSpace k K)
  have hmap := Submodule.map_comap_subtype (p := topMod) (p' := ssum)
  have heq_lm : (e : ↥topMod →ₗ[k] AdeleSpace k K) = topMod.subtype := by
    apply LinearMap.ext
    rintro ⟨f, _⟩
    apply Subtype.ext
    funext v
    rfl
  have hf : p.map (e : ↥topMod →ₗ[k] AdeleSpace k K) = ssum := by
    rw [show p.map (e : ↥topMod →ₗ[k] AdeleSpace k K) = p.map topMod.subtype from by
      rw [heq_lm], hmap, inf_eq_right]
    exact le_top
  dsimp only [finrankAdeleQuotient, sandwichRank, ssum]
  rw [← (Submodule.Quotient.equiv p ssum e hf).finrank_eq, hfull.symm]
  simp only [topMod, topAdeleSubmodule, ssum, p]
  simp


-- @@ L174-198 verbatim
theorem finrank_adele_quotient (D : DivisorA k K) :
    finrankAdeleQuotient k K D = indexOfSpecialty k K D := by
  obtain ⟨D₁, hD₁⟩ := exists_defect_eq (k := k) (K := K)
  let D' := D ⊔ D₁
  have hle : D ≤ D' := le_sup_left (a := D) (b := D₁)
  have hD' : defect k K D' = genus k K :=
    defect_eq_genus_of_ge (k := k) (K := K) (le_sup_right (a := D) (b := D₁)) hD₁
  have hfull := adeleSubmodule_top_eq_adeleFilt_add_diagonal (k := k) (K := K) hD'
  have hsand := sandwich (k := k) (K := K) hle
  have hfin := finrankAdeleQuotient_eq_sandwichRank (k := k) (K := K) hle hfull
  have hdef : sandwichRank k K D D' hle = defect k K D' - defect k K D := by
    dsimp only [defect]
    rw [hsand]
    omega
  have hidx : (indexOfSpecialty k K D : ℤ) = genus k K - defect k K D := by
    have := indexOfSpecialty_eq (k := k) (K := K) D
    dsimp only [defect] at this ⊢
    omega
  have hD'gen : defect k K D' = genus k K := hD'
  calc finrankAdeleQuotient k K D
      _ = (sandwichRank k K D D' hle).toNat := hfin
      _ = (genus k K - defect k K D).toNat := by rw [hdef, hD'gen]
      _ = indexOfSpecialty k K D := by
        rw [← hidx]
        simp only [Int.toNat_natCast]


-- @@ L200-200 verbatim
end FunctionField.Chart


-- @@ L202-202 verbatim
end
