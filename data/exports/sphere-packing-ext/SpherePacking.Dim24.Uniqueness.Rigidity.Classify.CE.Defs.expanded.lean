module
public import SpherePacking.Dim24.Uniqueness.Defs
public import SpherePacking.Dim24.LeechLattice.Defs
import SpherePacking.Dim24.LeechLattice.Instances
import SpherePacking.Dim24.LeechLattice.Norm


-- @@ L7-21 verbatim
/-!
# Core definitions for the CE Section 8 route

This folder hosts the components of the uniqueness argument among periodic packings in `ℝ²⁴`
following Cohn-Elkies (2003), Section 8, as used in `dim_24.tex`.

This file contains only definitions (no theorems), so other modules can import it without
creating heavy dependencies.

## Main definitions
* `Uniqueness.RigidityClassify.CE.leechKissingVectors`
* `Uniqueness.RigidityClassify.CE.contactSet`
* `Uniqueness.RigidityClassify.CE.dualLatticeSet`
* `Uniqueness.RigidityClassify.CE.IsKissingConfiguration`
-/


-- @@ L23-23 verbatim
namespace SpherePacking.Dim24.Uniqueness.RigidityClassify.CE


-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-27 verbatim
open scoped RealInnerProductSpace


-- @@ L29-29 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)


-- @@ L31-39 verbatim
/--
The Leech kissing configuration (vectors of norm `2`) as a set in `ℝ²⁴`.

This deliberately avoids depending on any min-shell API: it is just the subset of the Leech
lattice with Euclidean norm `2` (equivalently, squared norm `4`).
-/
@[expose]
public def leechKissingVectors : Set ℝ²⁴ :=
  {v : ℝ²⁴ | v ∈ (LeechLattice : Set ℝ²⁴) ∧ ‖v‖ = (2 : ℝ)}


-- @@ L41-45 verbatim
/-- Contact vectors at a center `x0`: differences `(y - x0)` of norm `2`. -/
@[expose]
public def contactSet (S : PeriodicSpherePacking 24) (x0 : S.centers) : Set ℝ²⁴ :=
  {v : ℝ²⁴ | ∃ y : S.centers, y ≠ x0 ∧ (y : ℝ²⁴) - (x0 : ℝ²⁴) = v ∧
      ‖v‖ = (2 : ℝ)}


-- @@ L47-52 verbatim
/-- A naive dual-lattice set: vectors with integer inner products with all lattice translations.

This is a convenient interface for the Fourier-side slack constraints in CE §8. -/
@[expose]
public def dualLatticeSet (S : PeriodicSpherePacking 24) : Set ℝ²⁴ :=
  {y : ℝ²⁴ | ∀ v : ℝ²⁴, v ∈ S.lattice → ∃ m : ℤ, ⟪y, v⟫ = (m : ℝ)}


-- @@ L54-63 verbatim
/--
A kissing configuration in `ℝ²⁴` (radius/separation `2`), presented as a set of vectors.

This is the shape needed for the external uniqueness input (Bannai-Sloane).
-/
@[expose]
public def IsKissingConfiguration (X : Set ℝ²⁴) : Prop :=
  Finite X ∧
    (∀ x ∈ X, ‖x‖ = (2 : ℝ)) ∧
      (∀ ⦃x y⦄, x ∈ X → y ∈ X → x ≠ y → ‖x - y‖ ≥ (2 : ℝ))


-- @@ L65-65 verbatim
end

-- @@ L66-66 verbatim
end SpherePacking.Dim24.Uniqueness.RigidityClassify.CE
