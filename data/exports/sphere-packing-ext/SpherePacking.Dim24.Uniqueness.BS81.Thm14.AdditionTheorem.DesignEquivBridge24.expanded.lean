module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.DoubleSumsToHarmonics24
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.MeanZeroHarmonics24.Basic
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.FischerReduction24.Basic
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.BS81ToHarmonic24
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.Defs


-- @@ L8-23 verbatim
/-!
# Bridge between BS81 and Gegenbauer designs

This file provides the final interface used by `.../Thm14/Design/DesignEquiv.lean`:

* `isBS81SphericalDesign24_of_isGegenbauerDesign24`
* `isGegenbauerDesign24_of_isBS81SphericalDesign24`

The standard proof goes through the intermediate harmonic condition:

`IsGegenbauerDesign24`  ↔  `IsHarmonicDesign24`
                         ↔  all harmonic moments vanish
                         ↔  `IsBS81SphericalDesign24`.

The heavy steps are decomposed into small lemmas across the `AdditionTheorem/Bridge24/` subfolder.
-/


-- @@ L25-25 verbatim
namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem


-- @@ L27-27 verbatim
noncomputable section


-- @@ L29-29 verbatim
open scoped BigOperators RealInnerProductSpace


-- @@ L31-31 verbatim
open Uniqueness.BS81.LP


-- @@ L33-33 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)


-- @@ L35-52 verbatim
/-!
## Harmonic moments imply BS81 design identity

BS81's design axiom is:

`finsetAvg C (p.eval ·) = sphereAvg24 (p.eval ·)` for every homogeneous `MvPolynomial p` of degree
`k ≤ t`.

Standard proof strategy:
1. Use Fischer decomposition: every homogeneous polynomial of degree `k` can be written uniquely as
   `p = h₀ + r² * q` where `h₀` is harmonic of degree `k` and `q` is homogeneous of degree `k-2`.
2. Restrict to the unit sphere: `r² = 1`, so `p|_{S} = h₀|_{S} + q|_{S}`.
3. Iterate to express `p|_{S}` as a sum of harmonic restrictions of degrees `k, k-2, k-4, ...`,
   plus possibly a constant.
4. The sphere average of a non-constant harmonic restriction is `0`.
5. The finite average is `0` for those harmonics by `IsHarmonicDesign24`.
6. Conclude equality of averages for all homogeneous polynomials up to degree `t`.
-/


-- @@ L54-61 verbatim
/-!
### Algebraic lemma: restriction to `S` is spanned by harmonics

This is the core Fischer decomposition / harmonic projection statement.

The exact formulation in terms of `MvPolynomial` is somewhat flexible; we record it as a black box
that produces the required averaging identity.
-/


-- @@ L63-78 verbatim
theorem finsetAvg_eq_sphereAvg_of_isHarmonicDesign24
    (t : ℕ) (C : Finset ℝ²⁴) (hC : ∀ u ∈ C, ‖u‖ = (1 : ℝ))
    (hH : IsHarmonicDesign24 t C) (hCne : C.Nonempty)
    (k : ℕ) (p : MvPolynomial (Fin 24) ℝ)
    (hk : k ≤ t) (hp : p.IsHomogeneous k) :
    finsetAvg C (mvPolyEval24 p) = sphereAvg24 (mvPolyEval24 p) := by
  -- Outline:
  -- * Decompose `p` into harmonic pieces on the unit sphere.
  -- * Use `hH` for finite averages and mean-zero harmonics for the sphere average.
  -- We convert `p` to the homogeneous piece `Pk k` and apply the Fischer-induction lemma.
  let pk : Uniqueness.BS81.LP.Gegenbauer24.PSD.Fischer.Pk k := ⟨p, hp⟩
  have havg :
      finsetAvg C (fun x : ℝ²⁴ => evalPk24 (k := k) (y := x) pk) =
        sphereAvg24 (fun x : ℝ²⁴ => evalPk24 (k := k) (y := x) pk) :=
    Bridge24.finsetAvg_eq_sphereAvg_of_isHarmonicDesign24_Pk (t := t) (C := C) hC hH hCne k hk pk
  simpa [Bridge24.mvPolyEval24_eq_evalPk24_of_memPk (p := pk)] using havg


-- @@ L80-86 verbatim
theorem isBS81SphericalDesign24_of_isHarmonicDesign24
    (t : ℕ) (C : Finset ℝ²⁴) (hC : ∀ u ∈ C, ‖u‖ = (1 : ℝ))
    (hH : IsHarmonicDesign24 t C) (hCne : C.Nonempty) :
    IsBS81SphericalDesign24 t C := by
  refine ⟨hC, ?_⟩
  intro k p hk hp
  exact finsetAvg_eq_sphereAvg_of_isHarmonicDesign24 (t := t) (C := C) hC hH hCne k p hk hp


-- @@ L88-90 verbatim
/-!
## Main bridge theorems
-/


-- @@ L92-99 verbatim
/-- A Gegenbauer design satisfies the BS81 spherical-design axiom (equation (14)). -/
public theorem isBS81SphericalDesign24_of_isGegenbauerDesign24
    (t : ℕ) (C : Finset ℝ²⁴)
    (hC : ∀ u ∈ C, ‖u‖ = (1 : ℝ))
    (hG : IsGegenbauerDesign24 t C) (hCne : C.Nonempty) :
    IsBS81SphericalDesign24 t C :=
  isBS81SphericalDesign24_of_isHarmonicDesign24 (t := t) (C := C) hC
    (isHarmonicDesign24_of_isGegenbauerDesign24 (t := t) (C := C) hC hG) hCne


-- @@ L101-112 verbatim
/-- The BS81 spherical-design axiom (equation (14)) implies vanishing of Gegenbauer double sums. -/
public theorem isGegenbauerDesign24_of_isBS81SphericalDesign24
    (t : ℕ) (C : Finset ℝ²⁴)
    (hD : IsBS81SphericalDesign24 t C) :
    IsGegenbauerDesign24 t C := by
  -- BS81 equation (14) implies all harmonic moments vanish (by choosing harmonic polynomials),
  -- hence `IsHarmonicDesign24`; then convert to `IsGegenbauerDesign24` via the Gram identity.
  -- Extract `hC` from `hD`.
  have hC : ∀ u ∈ C, ‖u‖ = (1 : ℝ) := hD.1
  -- Convert BS81 design to harmonic design (missing lemma).
  exact isGegenbauerDesign24_of_isHarmonicDesign24 (t := t) (C := C) hC
    (Bridge24.isHarmonicDesign24_of_isBS81SphericalDesign24 (t := t) (C := C) hD)


-- @@ L114-114 verbatim
end


-- @@ L116-116 verbatim
end SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem
