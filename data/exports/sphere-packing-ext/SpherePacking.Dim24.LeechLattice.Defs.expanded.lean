module
public import SpherePacking.Basic.PeriodicPacking.Aux
public import SpherePacking.Basic.PeriodicPacking.Theorem22
public import SpherePacking.Basic.PeriodicPacking.DensityFormula
public import SpherePacking.Basic.PeriodicPacking.PeriodicConstant
public import SpherePacking.Basic.PeriodicPacking.BoundaryControl



-- @@ L9-22 verbatim
/-!
# Leech lattice definition

This file defines the Leech lattice in `ℝ²⁴` from an explicit integer generator matrix
(in row convention) together with a scaling by `1 / √8`.

Paper context: `dim_24.tex` (CKMRV), Theorem 1.1 and surrounding discussion.

## Main definitions
* `leechGeneratorMatrixInt`
* `leechGeneratorRowsUnscaled`
* `leechGeneratorRows`
* `LeechLattice`
-/



-- @@ L25-25 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)


-- @@ L27-27 verbatim
namespace SpherePacking.Dim24


-- @@ L29-64 verbatim
/-- Integer generator matrix for the Leech lattice (row convention).

The Leech lattice is defined as the `ℤ`-span of the scaled rows of this matrix.

Faithfulness note:
The paper uses the Leech lattice normalized to be unimodular with minimal norm `2`. In this
development this is achieved by scaling the rows by `1 / √8` (see `leechGeneratorRows`) and is
characterized by results such as `leech_fundamentalDomain_volume` and `leech_norm_lower_bound`.
-/
@[expose] public def leechGeneratorMatrixInt : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![4, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![4, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![4, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![4, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![4, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![4, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![4, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![2, 2, 2, 2, 0, 0, 0, 0, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0],
    ![4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0],
    ![2, 0, 2, 0, 2, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0],
    ![2, 0, 0, 2, 2, 2, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0],
    ![2, 2, 0, 0, 2, 0, 2, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0],
    ![0, 2, 2, 2, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0],
    ![-3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  ]


-- @@ L66-68 expanded
/-- Rows of `leechGeneratorMatrixInt`, interpreted as vectors in `ℝ²⁴`. -/
@[expose]
public noncomputable def leechGeneratorRowsUnscaled (i : Fin 24) : EuclideanSpace ℝ (Fin 24) :=
  WithLp.toLp 2 fun j : Fin 24 => (leechGeneratorMatrixInt i j : ℝ)


-- @@ L70-72 expanded
/-- Scaled generator rows defining the Leech lattice (normalization factor `1 / √8`). -/
@[expose]
public noncomputable def leechGeneratorRows (i : Fin 24) : EuclideanSpace ℝ (Fin 24) :=
  ((Real.sqrt 8)⁻¹ : ℝ) • leechGeneratorRowsUnscaled i


-- @@ L74-76 expanded
/-- The Leech lattice in `ℝ²⁴`, defined as the `ℤ`-span of the scaled generator rows. -/
@[expose]
public noncomputable def LeechLattice : Submodule ℤ (EuclideanSpace ℝ (Fin 24)) :=
  Submodule.span ℤ (Set.range leechGeneratorRows)


-- @@ L78-78 verbatim
end SpherePacking.Dim24
