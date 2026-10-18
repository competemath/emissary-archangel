import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Basic.Complex.Basic


-- @@ L6-6 verbatim
namespace OAI


-- @@ L8-20 verbatim
/-!
# The four-variable complex polynomial

Variables are zero-indexed internally: `X 0, X 1, X 2, X 3` mean the
paper's `x₁, x₂, x₃, x₄`.  The stabilization uses `Fin.castSucc`,
so its fifth independent variable is `X 4`; no subring-preservation condition
is imposed on its automorphism.

Affine fibers are encoded by their complex coordinate algebras, not by sets.
An algebra equivalence to the three-variable polynomial algebra is precisely
the algebraic affine-space conclusion.  Rectifiability is encoded by the
ambient algebra automorphism carrying the defining ideal to `(X 0)`.
-/


-- @@ L22-22 verbatim
namespace StableCoordinate


-- @@ L24-24 verbatim
open MvPolynomial


-- @@ L26-26 verbatim
abbrev R (n : ℕ) := MvPolynomial (Fin n) ℂ


-- @@ L28-29 verbatim
noncomputable def Q : R 4 :=
  X 1 ^ 2 - X 3 ^ 2 + X 0 * X 2


-- @@ L31-32 verbatim
noncomputable def f : R 4 :=
  X 0 - 2 * Q * (Q * (X 1 + X 3) + X 0 * X 3)


-- @@ L34-36 verbatim
/-- A coordinate is sent to the first variable by some complex algebra automorphism. -/
def IsCoordinate {n : ℕ} (hn : 0 < n) (g : R n) : Prop :=
  ∃ φ : R n ≃ₐ[ℂ] R n, φ g = X ⟨0, hn⟩


-- @@ L38-40 verbatim
/-- Adjoin one independent variable; the original variables retain their indices. -/
noncomputable def stabilize : R 4 →ₐ[ℂ] R 5 :=
  rename (Fin.castSucc : Fin 4 → Fin 5)


-- @@ L42-44 verbatim
/-- No requirement to preserve the original four-variable subring is imposed. -/
def IsOneStableCoordinate (g : R 4) : Prop :=
  ∃ φ : R 5 ≃ₐ[ℂ] R 5, φ (stabilize g) = X 0


-- @@ L46-47 verbatim
noncomputable def fiberIdeal (t : ℂ) : Ideal (R 4) :=
  Ideal.span ({f - C t} : Set (R 4))


-- @@ L49-49 verbatim
abbrev FiberRing (t : ℂ) := R 4 ⧸ fiberIdeal t


-- @@ L51-53 verbatim
/-- An isomorphism of affine coordinate algebras, not a set-theoretic bijection. -/
def IsAffineThreeSpaceFiber (t : ℂ) : Prop :=
  Nonempty (FiberRing t ≃ₐ[ℂ] R 3)


-- @@ L55-58 verbatim
/-- Algebraic rectifiability of the closed hypersurface embedding. -/
def IsRectifiableFiber (t : ℂ) : Prop :=
  ∃ φ : R 4 ≃ₐ[ℂ] R 4,
    Ideal.map φ.toRingHom (fiberIdeal t) = Ideal.span ({X 0} : Set (R 4))


-- @@ L60-64 verbatim
/-- Complete first principal group, with the advertised exact total degree. -/
def PolynomialPackage : Prop :=
  f.totalDegree = 5 ∧
  IsOneStableCoordinate f ∧
  ¬ IsCoordinate (by decide : 0 < 4) f


-- @@ L66-68 verbatim
/-- Complete second principal group, universally including the zero fiber. -/
def FiberPackage : Prop :=
  ∀ t : ℂ, IsAffineThreeSpaceFiber t ∧ ¬ IsRectifiableFiber t


-- @@ L70-71 verbatim
/-- Both principal groups must be proved together, without additional hypotheses. -/
def PrincipalPackage : Prop := PolynomialPackage ∧ FiberPackage


-- @@ L73-73 verbatim
end StableCoordinate


-- @@ L75-75 verbatim
end OAI
