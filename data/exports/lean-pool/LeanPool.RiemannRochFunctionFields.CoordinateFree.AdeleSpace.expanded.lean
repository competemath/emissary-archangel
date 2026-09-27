/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
module

public import LeanPool.RiemannRochFunctionFields.AdeleSpace.Basic
public import LeanPool.RiemannRochFunctionFields.CoordinateFree.Divisor
import Mathlib.Analysis.SpecialFunctions.Pow.Real


-- @@ L12-18 verbatim
/-!
# Adeles indexed by intrinsic places

This file defines the function-field adele space directly as a restricted product over
coordinate-free places. The equivalence `adeleEquivChart` identifies it with the two-chart
construction and transports the filtration and diagonal embedding.
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
open scoped nonZeroDivisors Polynomial RatFunc WithZero

-- @@ L23-23 verbatim
open Filter


-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-27 verbatim
namespace FunctionField


-- @@ L29-29 verbatim
open Chart


-- @@ L31-31 verbatim
variable (k K : Type*) [Field k] [Field K]

-- @@ L32-34 verbatim
variable [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K]
  [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]


-- @@ L36-52 verbatim
/-- The `k`-submodule of tuples over intrinsic places that are integral almost everywhere. -/
def adeleSubmodule : Submodule k (Place k K → K) where
  carrier := {a | ∀ᶠ v in cofinite, a v ∈ v.toValuationSubring}
  zero_mem' := by
    change ∀ᶠ v : Place k K in cofinite, (0 : K) ∈ v.toValuationSubring
    exact Filter.Eventually.of_forall fun v => v.toValuationSubring.zero_mem
  add_mem' {a b} ha hb := by
    change ∀ᶠ v in cofinite, a v ∈ v.toValuationSubring at ha
    change ∀ᶠ v in cofinite, b v ∈ v.toValuationSubring at hb
    change ∀ᶠ v in cofinite, (a + b) v ∈ v.toValuationSubring
    exact (ha.and hb).mono fun _ h => add_mem h.1 h.2
  smul_mem' c a ha := by
    change ∀ᶠ v in cofinite, a v ∈ v.toValuationSubring at ha
    change ∀ᶠ v in cofinite, (c • a) v ∈ v.toValuationSubring
    filter_upwards [ha] with v hv
    rw [Pi.smul_apply, Algebra.smul_def]
    exact mul_mem (v.triv_on_k c) hv


-- @@ L54-55 verbatim
/-- The intrinsic, `K`-valued adele space. -/
abbrev AdeleSpace := adeleSubmodule k K


-- @@ L57-65 verbatim
/-- Every element of the function field is integral at all but finitely many intrinsic places. -/
theorem eventually_mem_place (f : K) :
    ∀ᶠ v : Place k K in cofinite, f ∈ v.toValuationSubring := by
  have h := Chart.eventually_mem_placeValuationSubring k K f
  have h' := (chartToPlace k K).symm.injective.tendsto_cofinite.eventually h
  filter_upwards [h'] with v hv
  rw [← (chartToPlace k K).apply_symm_apply v, chartToPlace_apply,
    Place.ofChart_toValuationSubring]
  exact hv


-- @@ L67-93 verbatim
/-- Reindex an intrinsic adele along the equivalence between chart and intrinsic places. -/
noncomputable def adeleEquivChart : AdeleSpace k K ≃ₗ[k] Chart.AdeleSpace k K where
  toFun a := ⟨fun w => a.1 (chartToPlace k K w), by
    have ha := (chartToPlace k K).injective.tendsto_cofinite.eventually a.property
    filter_upwards [ha] with w hw
    rw [placeValuationSubring, ← Place.ofChart_toValuationSubring]
    exact hw⟩
  invFun a := ⟨fun v => a.1 ((chartToPlace k K).symm v), by
    have ha := (chartToPlace k K).symm.injective.tendsto_cofinite.eventually a.property
    filter_upwards [ha] with v hv
    have hs : v.toValuationSubring =
        placeValuationSubring k K ((chartToPlace k K).symm v) := by
      rw [placeValuationSubring, ← Place.ofChart_toValuationSubring]
      exact congrArg Place.toValuationSubring
        ((chartToPlace k K).apply_symm_apply v).symm
    rw [hs]
    exact hv⟩
  left_inv a := by
    apply Subtype.ext
    funext v
    exact congrArg a.1 ((chartToPlace k K).apply_symm_apply v)
  right_inv a := by
    apply Subtype.ext
    funext w
    exact congrArg a.1 ((chartToPlace k K).symm_apply_apply w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


-- @@ L95-98 verbatim
@[simp]
theorem adeleEquivChart_apply (a : AdeleSpace k K) (w : PlaceA k K) :
    (adeleEquivChart k K a).1 w = a.1 (chartToPlace k K w) :=
  rfl


-- @@ L100-103 verbatim
@[simp]
theorem adeleEquivChart_symm_apply (a : Chart.AdeleSpace k K) (v : Place k K) :
    ((adeleEquivChart k K).symm a).1 v = a.1 ((chartToPlace k K).symm v) :=
  rfl


-- @@ L105-108 verbatim
/-- Pointwise multiplication of an intrinsic adele by an element of `K`. -/
def smulAdele (x : K) (a : AdeleSpace k K) : AdeleSpace k K :=
  ⟨fun v => x * a.1 v, (eventually_mem_place k K x).and a.property |>.mono
    fun _ h => mul_mem h.1 h.2⟩


-- @@ L110-110 verbatim
instance : SMul K (AdeleSpace k K) := ⟨smulAdele k K⟩


-- @@ L112-117 verbatim
instance : Module K (AdeleSpace k K) :=
  Module.ofMinimalAxioms
    (fun _ _ _ => Subtype.ext <| funext fun _ => mul_add _ _ _)
    (fun _ _ _ => Subtype.ext <| funext fun _ => add_mul _ _ _)
    (fun _ _ _ => Subtype.ext <| funext fun _ => mul_assoc _ _ _)
    (fun _ => Subtype.ext <| funext fun _ => one_mul _)


-- @@ L119-125 verbatim
/-- The intrinsic-to-chart adele equivalence commutes with multiplication by `K`. -/
@[simp]
theorem adeleEquivChart_smul (x : K) (a : AdeleSpace k K) :
    adeleEquivChart k K (x • a) = x • adeleEquivChart k K a := by
  ext w
  change x * a.1 (chartToPlace k K w) = x * a.1 (chartToPlace k K w)
  rfl


-- @@ L127-135 verbatim
/-- Multiplication by an element of `K` as a `k`-linear endomorphism of intrinsic adeles. -/
def mulAdeleLinear (x : K) : AdeleSpace k K →ₗ[k] AdeleSpace k K where
  toFun a := x • a
  map_add' _ _ := smul_add x _ _
  map_smul' c a := by
    ext v
    change x * (c • a.1 v) = c • (x * a.1 v)
    simp only [Algebra.smul_def]
    ring


-- @@ L137-139 verbatim
/-- An intrinsic adele satisfies the bound prescribed by a divisor. -/
def memAdeleFilt (D : Divisor k K) (a : AdeleSpace k K) : Prop :=
  ∀ v, v.valuation (a.1 v) ≤ WithZero.exp (D v)


-- @@ L141-154 verbatim
/-- The intrinsic adele filtration piece `A(D)`. -/
def adeleFilt (D : Divisor k K) : Submodule k (AdeleSpace k K) where
  carrier := {a | memAdeleFilt k K D a}
  zero_mem' := fun _ => by simp
  add_mem' {a b} ha hb := fun v =>
    (v.valuation.map_add (a.1 v) (b.1 v)).trans (max_le (ha v) (hb v))
  smul_mem' c a ha := by
    intro v
    change v.valuation (c • a.1 v) ≤ _
    rw [Algebra.smul_def, map_mul]
    have hc : v.valuation (algebraMap k K c) ≤ 1 := by
      rw [← Valuation.mem_valuationSubring_iff, Place.valuationSubring_valuation]
      exact v.triv_on_k c
    exact (mul_le_mul' hc (ha v)).trans_eq (one_mul _)


-- @@ L156-170 verbatim
/-- Membership in the intrinsic filtration agrees with chart filtration membership. -/
theorem mem_adeleFilt_equivChart (D : Divisor k K) (a : AdeleSpace k K) :
    adeleEquivChart k K a ∈
        Chart.adeleFilt k K ((divisorEquivChart k K).symm D) ↔
      a ∈ adeleFilt k K D := by
  constructor
  · intro ha v
    let w := (chartToPlace k K).symm v
    have hw := ha w
    rw [← placeValuation_eq] at hw
    simpa [w, divisorEquivChart, Finsupp.domCongr_apply] using hw
  · intro ha w
    have hv := ha (chartToPlace k K w)
    rw [placeValuation_eq] at hv
    simpa [divisorEquivChart, Finsupp.domCongr_apply] using hv


-- @@ L172-179 verbatim
omit [Algebra k[X] K] [Algebra k⟮X⟯ K] [IsScalarTower k k[X] K]
    [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K]
    [Algebra.IsSeparable k⟮X⟯ K] in
/-- The intrinsic adele filtration is monotone in the divisor. -/
theorem adeleFilt_mono {D E : Divisor k K} (h : D ≤ E) :
    adeleFilt k K D ≤ adeleFilt k K E := by
  intro a ha v
  exact (ha v).trans (WithZero.exp_le_exp.mpr (h v))


-- @@ L181-185 verbatim
/-- The diagonal embedding of the function field into intrinsic adeles. -/
def diagonal : K →ₗ[k] AdeleSpace k K where
  toFun f := ⟨fun _ => f, eventually_mem_place k K f⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


-- @@ L187-189 verbatim
/-- The image of the intrinsic diagonal embedding. -/
def diagonalSubmodule : Submodule k (AdeleSpace k K) :=
  LinearMap.range (diagonal k K)


-- @@ L191-196 verbatim
@[simp]
theorem adeleEquivChart_diagonal (f : K) :
    adeleEquivChart k K (diagonal k K f) = Chart.diagonal k K f := by
  ext w
  change f = f
  rfl


-- @@ L198-208 verbatim
/-- The chart equivalence maps the intrinsic filtration onto the chart filtration. -/
theorem map_adeleFilt_equivChart (D : Divisor k K) :
    Submodule.map (adeleEquivChart k K).toLinearMap (adeleFilt k K D) =
      Chart.adeleFilt k K ((divisorEquivChart k K).symm D) := by
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact (mem_adeleFilt_equivChart k K D b).2 hb
  · intro ha
    refine ⟨(adeleEquivChart k K).symm a, ?_, by simp⟩
    exact (mem_adeleFilt_equivChart k K D _).1 (by simpa using ha)


-- @@ L210-219 verbatim
/-- The chart equivalence maps the intrinsic diagonal submodule onto the chart diagonal. -/
theorem map_diagonalSubmodule_equivChart :
    Submodule.map (adeleEquivChart k K).toLinearMap (diagonalSubmodule k K) =
      Chart.diagonalSubmodule k K := by
  ext a
  constructor
  · rintro ⟨b, ⟨f, rfl⟩, rfl⟩
    exact ⟨f, (adeleEquivChart_diagonal k K f).symm⟩
  · rintro ⟨f, rfl⟩
    exact ⟨diagonal k K f, ⟨f, rfl⟩, adeleEquivChart_diagonal k K f⟩


-- @@ L221-231 verbatim
/-- The chart equivalence maps `A(D)` plus the diagonal onto the corresponding chart submodule. -/
theorem map_adeleFilt_add_diagonal_equivChart (D : Divisor k K) :
    Submodule.map (adeleEquivChart k K).toLinearMap
        (adeleFilt k K D + diagonalSubmodule k K) =
      Chart.adeleFilt k K ((divisorEquivChart k K).symm D) +
        Chart.diagonalSubmodule k K := by
  rw [Submodule.add_eq_sup,
    Submodule.map_sup (adeleFilt k K D) (diagonalSubmodule k K)
      (adeleEquivChart k K).toLinearMap,
    map_adeleFilt_equivChart,
    map_diagonalSubmodule_equivChart, ← Submodule.add_eq_sup]


-- @@ L233-244 verbatim
/-- Membership in `A(D)` plus the diagonal is preserved by the chart equivalence. -/
theorem mem_adeleFilt_add_diagonal_equivChart (D : Divisor k K) (a : AdeleSpace k K) :
    adeleEquivChart k K a ∈
        Chart.adeleFilt k K ((divisorEquivChart k K).symm D) +
          Chart.diagonalSubmodule k K ↔
      a ∈ adeleFilt k K D + diagonalSubmodule k K := by
  rw [← map_adeleFilt_add_diagonal_equivChart k K D]
  constructor
  · rintro ⟨b, hb, hba⟩
    exact (adeleEquivChart k K).injective hba |>.symm ▸ hb
  · intro ha
    exact ⟨a, ha, rfl⟩


-- @@ L246-246 verbatim
end FunctionField
