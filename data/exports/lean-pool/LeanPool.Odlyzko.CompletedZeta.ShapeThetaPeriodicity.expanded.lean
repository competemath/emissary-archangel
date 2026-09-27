/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.FractionalShapeTheta


-- @@ L10-10 verbatim
/-! TODO: Add doc-string. -/


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
noncomputable section


-- @@ L16-17 verbatim
open Complex NumberField NumberField.InfinitePlace NumberField.Units
  dirichletUnitTheorem

-- @@ L18-18 verbatim
open scoped nonZeroDivisors


-- @@ L20-20 verbatim
namespace NumberField.Odlyzko


-- @@ L22-22 verbatim
open mixedEmbedding mixedEmbedding.fundamentalCone


-- @@ L24-24 verbatim
variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]


-- @@ L26-49 verbatim
open Classical in
/-- A fractional ideal element unit mul equiv used in the Odlyzko-bound argument. -/
noncomputable def fractionalIdealElementUnitMulEquiv
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (u : (𝓞 K)ˣ) :
    ↥((I : FractionalIdeal (𝓞 K)⁰ K) :
      Submodule (𝓞 K) K) ≃
      ↥((I : FractionalIdeal (𝓞 K)⁰ K) :
        Submodule (𝓞 K) K) where
  toFun x :=
    ⟨((u : 𝓞 K) : K) * (x : K), by
      change (u : 𝓞 K) • (x : K) ∈
        ((I : FractionalIdeal (𝓞 K)⁰ K) :
          Submodule (𝓞 K) K)
      simp⟩
  invFun x :=
    ⟨((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (x : K), by
      change (u⁻¹ : (𝓞 K)ˣ) • (x : K) ∈
        ((I : FractionalIdeal (𝓞 K)⁰ K) :
          Submodule (𝓞 K) K)
      simp⟩
  left_inv x := by
    simp
  right_inv x := by
    simp


-- @@ L51-65 verbatim
omit [IsTotallyComplex K] in
open Classical in
theorem complexPlaceGaussian_mul_unit
    (u : (𝓞 K)ˣ) (x : K) (q : InfinitePlace K → ℝ) :
    complexPlaceGaussian K x
        ((fun w ↦ w (((u : 𝓞 K) : K))) * q) =
      complexPlaceGaussian K (((u : 𝓞 K) : K) * x) q := by
  rw [complexPlaceGaussian, complexPlaceGaussian]
  congr 1
  norm_cast
  apply congrArg (fun t : ℝ ↦ -(2 * Real.pi * t))
  apply Finset.sum_congr rfl
  intro w _
  simp only [Pi.mul_apply, map_mul]
  ring


-- @@ L67-94 verbatim
open Classical in
theorem fractionalShapeIdealTheta_add_unitCoordinateShift
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (y : mixedEmbedding.realSpace K)
    (z : {w : InfinitePlace K // w ≠ w₀} → ℤ) :
    fractionalShapeIdealTheta K I
        (expMapBasis (y + unitCoordinateShift z))
        (fun w ↦ (expMapBasis_pos (y + unitCoordinateShift z) w).ne') =
      fractionalShapeIdealTheta K I (expMapBasis y)
        (fun w ↦ (expMapBasis_pos y w).ne') := by
  rw [fractionalShapeIdealTheta_eq_tsum,
    fractionalShapeIdealTheta_eq_tsum,
    expMapBasis_add_unitCoordinateShift]
  let u := fundamentalUnitForShift z
  let e := fractionalIdealElementUnitMulEquiv K I u
  calc
    (∑' x : ↥((I : FractionalIdeal (𝓞 K)⁰ K) :
        Submodule (𝓞 K) K),
      complexPlaceGaussian K (x : K)
        ((fun w ↦ w (((u : 𝓞 K) : K))) * expMapBasis y)) =
        ∑' x : ↥((I : FractionalIdeal (𝓞 K)⁰ K) :
          Submodule (𝓞 K) K),
          complexPlaceGaussian K (e x : K) (expMapBasis y) := by
      apply tsum_congr
      intro x
      exact complexPlaceGaussian_mul_unit K u (x : K) (expMapBasis y)
    _ = _ := e.tsum_eq
      (fun x ↦ complexPlaceGaussian K (x : K) (expMapBasis y))


-- @@ L96-96 verbatim
end NumberField.Odlyzko
