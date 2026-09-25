module
public import SpherePacking.Dim24.LeechLattice.Defs
public import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse



-- @@ L9-21 verbatim
/-!
# Leech lattice instances

This file constructs an explicit real basis `LeechLattice.leechRBasis` and derives topological and
`IsZLattice` structure instances for `LeechLattice`.

## Main definitions
* `LeechLattice.leechRBasis`

## Main instances
* `instDiscreteLeechLattice`
* `instIsZLatticeLeechLattice`
-/



-- @@ L24-24 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)


-- @@ L26-26 verbatim
namespace SpherePacking.Dim24


-- @@ L28-28 verbatim
open Module


-- @@ L30-30 verbatim
namespace LeechLattice


-- @@ L32-33 verbatim
def leechMatrixRat : Matrix (Fin 24) (Fin 24) ℚ :=
  leechGeneratorMatrixInt.map (Int.castRingHom ℚ)


-- @@ L35-36 verbatim
def leechMatrixReal : Matrix (Fin 24) (Fin 24) ℝ :=
  leechGeneratorMatrixInt.map (Int.castRingHom ℝ)


-- @@ L38-88 verbatim
def leechInverseRat : Matrix (Fin 24) (Fin 24) ℚ :=
  ![
    ![(1 : ℚ) / 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![(-1 : ℚ) / 8, (1 : ℚ) / 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![(-1 : ℚ) / 8, 0, (1 : ℚ) / 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![(-1 : ℚ) / 8, 0, 0, (1 : ℚ) / 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![(-1 : ℚ) / 8, 0, 0, 0, (1 : ℚ) / 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![(-1 : ℚ) / 8, 0, 0, 0, 0, (1 : ℚ) / 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![(-1 : ℚ) / 8, 0, 0, 0, 0, 0, (1 : ℚ) / 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![(5 : ℚ) / 8, (-1 : ℚ) / 4, (-1 : ℚ) / 4, (-1 : ℚ) / 4, (-1 : ℚ) / 4, (-1 : ℚ) / 4,
      (-1 : ℚ) / 4, (1 : ℚ) / 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![(-1 : ℚ) / 8, 0, 0, 0, 0, 0, 0, 0, (1 : ℚ) / 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0],
    ![(-1 : ℚ) / 8, 0, 0, 0, 0, 0, 0, 0, 0, (1 : ℚ) / 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0],
    ![(-1 : ℚ) / 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1 : ℚ) / 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0],
    ![(5 : ℚ) / 8, (-1 : ℚ) / 4, (-1 : ℚ) / 4, (-1 : ℚ) / 4, 0, 0, 0, 0, (-1 : ℚ) / 4,
      (-1 : ℚ) / 4, (-1 : ℚ) / 4, (1 : ℚ) / 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![(-1 : ℚ) / 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1 : ℚ) / 4, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0],
    ![(5 : ℚ) / 8, (-1 : ℚ) / 4, 0, 0, (-1 : ℚ) / 4, (-1 : ℚ) / 4, 0, 0, (-1 : ℚ) / 4,
      (-1 : ℚ) / 4, 0, 0, (-1 : ℚ) / 4, (1 : ℚ) / 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![(5 : ℚ) / 8, 0, (-1 : ℚ) / 4, 0, (-1 : ℚ) / 4, 0, (-1 : ℚ) / 4, 0, (-1 : ℚ) / 4, 0,
      (-1 : ℚ) / 4, 0, (-1 : ℚ) / 4, 0, (1 : ℚ) / 2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![(-7 : ℚ) / 8, (1 : ℚ) / 2, (1 : ℚ) / 2, (1 : ℚ) / 4, 0, (1 : ℚ) / 4, (1 : ℚ) / 4,
      (-1 : ℚ) / 2, 0, (1 : ℚ) / 4, (1 : ℚ) / 4, (-1 : ℚ) / 2, (-1 : ℚ) / 4, 0, 0,
      (1 : ℚ) / 2, 0, 0, 0, 0, 0, 0, 0, 0],
    ![(-1 : ℚ) / 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1 : ℚ) / 4, 0, 0, 0, 0,
      0, 0, 0],
    ![(-1 : ℚ) / 8, (1 : ℚ) / 4, 0, (1 : ℚ) / 4, 0, (1 : ℚ) / 4, (1 : ℚ) / 4, (-1 : ℚ) / 2,
      (-1 : ℚ) / 4, (-1 : ℚ) / 4, 0, 0, 0, 0, 0, 0, (-1 : ℚ) / 4, (1 : ℚ) / 2, 0, 0, 0, 0,
      0, 0],
    ![(5 : ℚ) / 8, 0, 0, (-1 : ℚ) / 4, (-1 : ℚ) / 4, (-1 : ℚ) / 4, 0, 0, (-1 : ℚ) / 4, 0,
      (-1 : ℚ) / 4, 0, 0, 0, 0, 0, (-1 : ℚ) / 4, 0, (1 : ℚ) / 2, 0, 0, 0, 0, 0],
    ![(-1 : ℚ) / 8, 0, (1 : ℚ) / 4, (1 : ℚ) / 4, (-1 : ℚ) / 4, 0, (-1 : ℚ) / 4, 0, 0,
      (1 : ℚ) / 4, (1 : ℚ) / 4, (-1 : ℚ) / 2, 0, 0, 0, 0, (-1 : ℚ) / 4, 0, 0, (1 : ℚ) / 2,
      0, 0, 0, 0],
    ![(7 : ℚ) / 8, (-1 : ℚ) / 4, (-1 : ℚ) / 4, (-1 : ℚ) / 4, (-1 : ℚ) / 4, 0, 0, 0,
      (-1 : ℚ) / 4, 0, 0, 0, (-1 : ℚ) / 4, 0, 0, 0, (-1 : ℚ) / 4, 0, 0, 0, (1 : ℚ) / 2, 0,
      0, 0],
    ![(-7 : ℚ) / 8, (1 : ℚ) / 4, (1 : ℚ) / 4, 0, (1 : ℚ) / 2, 0, (-1 : ℚ) / 4, (1 : ℚ) / 2,
      (1 : ℚ) / 2, (1 : ℚ) / 4, 0, 0, (1 : ℚ) / 4, (-1 : ℚ) / 2, 0, 0, (1 : ℚ) / 4,
      (-1 : ℚ) / 2, 0, 0, (-1 : ℚ) / 2, (1 : ℚ) / 2, 0, 0],
    ![(-13 : ℚ) / 8, (1 : ℚ) / 4, (1 : ℚ) / 2, (1 : ℚ) / 2, (3 : ℚ) / 4, (1 : ℚ) / 4,
      (1 : ℚ) / 4, 0, (1 : ℚ) / 2, 0, (1 : ℚ) / 4, 0, (1 : ℚ) / 4, 0, (-1 : ℚ) / 2, 0,
      (1 : ℚ) / 4, 0, (-1 : ℚ) / 2, 0, (-1 : ℚ) / 2, 0, (1 : ℚ) / 2, 0],
    ![(11 : ℚ) / 8, (-1 : ℚ) / 2, (-3 : ℚ) / 4, (-1 : ℚ) / 2, 0, (-1 : ℚ) / 4, 0, 0,
      (1 : ℚ) / 4, (-1 : ℚ) / 4, (-1 : ℚ) / 4, (1 : ℚ) / 2, (1 : ℚ) / 4, 0, 0, (-1 : ℚ) / 2,
      (1 : ℚ) / 4, 0, 0, (-1 : ℚ) / 2, (1 : ℚ) / 2, (-1 : ℚ) / 2, (-1 : ℚ) / 2, 1]
  ]


-- @@ L90-91 verbatim
lemma leechInverse_mul_leechMatrix_rat : leechInverseRat * leechMatrixRat = 1 := by
  decide +kernel


-- @@ L93-94 verbatim
lemma leechMatrix_mul_leechInverse_rat : leechMatrixRat * leechInverseRat = 1 := by
  decide +kernel


-- @@ L96-99 verbatim
lemma leechMatrixReal_eq_cast :
    leechMatrixReal = leechMatrixRat.map (Rat.castHom ℝ) := by
  ext i j
  simp [leechMatrixReal, leechMatrixRat]


-- @@ L101-115 verbatim
lemma leechInverse_mul_leechMatrix_real :
    (leechInverseRat.map (Rat.castHom ℝ)) * leechMatrixReal = 1 := by
  have h0 :
      (leechInverseRat * leechMatrixRat).map (Rat.castHom ℝ) = 1 := by
    simpa using
      congrArg (fun A : Matrix (Fin 24) (Fin 24) ℚ => A.map (Rat.castHom ℝ))
        leechInverse_mul_leechMatrix_rat
  have hm :
      (leechInverseRat * leechMatrixRat).map (Rat.castHom ℝ) =
        (leechInverseRat.map (Rat.castHom ℝ)) * (leechMatrixRat.map (Rat.castHom ℝ)) := by
    simpa using
      (Matrix.map_mul (L := leechInverseRat) (M := leechMatrixRat) (f := Rat.castHom ℝ))
  have h1 := h0
  rw [hm] at h1
  simpa [leechMatrixReal_eq_cast] using h1


-- @@ L117-129 verbatim
lemma leechMatrix_mul_leechInverse_real :
    leechMatrixReal * (leechInverseRat.map (Rat.castHom ℝ)) = 1 := by
  have h0 : (leechMatrixRat * leechInverseRat).map (Rat.castHom ℝ) = 1 := by
    simpa using
      congrArg (fun A : Matrix (Fin 24) (Fin 24) ℚ => A.map (Rat.castHom ℝ))
        leechMatrix_mul_leechInverse_rat
  have hm :
      (leechMatrixRat * leechInverseRat).map (Rat.castHom ℝ) =
        (leechMatrixRat.map (Rat.castHom ℝ)) * (leechInverseRat.map (Rat.castHom ℝ)) := by
    simpa using (Matrix.map_mul (L := leechMatrixRat) (M := leechInverseRat) (f := Rat.castHom ℝ))
  have h1 := h0
  rw [hm] at h1
  simpa [leechMatrixReal_eq_cast] using h1


-- @@ L131-137 verbatim
lemma linearIndependent_leechMatrixReal_rows :
    LinearIndependent ℝ leechMatrixReal.row := by
  haveI : Invertible leechMatrixReal :=
    { invOf := leechInverseRat.map (Rat.castHom ℝ)
      invOf_mul_self := leechInverse_mul_leechMatrix_real
      mul_invOf_self := leechMatrix_mul_leechInverse_real }
  simpa using Matrix.linearIndependent_rows_of_invertible (K := ℝ) leechMatrixReal


-- @@ L139-144 verbatim
lemma linearIndependent_leechGeneratorRowsUnscaled :
    LinearIndependent ℝ leechGeneratorRowsUnscaled := by
  have hrows : LinearIndependent ℝ leechMatrixReal.row := linearIndependent_leechMatrixReal_rows
  simpa [leechGeneratorRowsUnscaled, leechMatrixReal, Function.comp,
    WithLp.coe_symm_linearEquiv] using
    (hrows.map' (WithLp.linearEquiv 2 ℝ (Fin 24 → ℝ)).symm.toLinearMap (by simp))


-- @@ L146-152 verbatim
lemma linearIndependent_leechGeneratorRows :
    LinearIndependent ℝ leechGeneratorRows := by
  let u : ℝˣ :=
    Units.mk0 ((Real.sqrt 8)⁻¹ : ℝ)
      (inv_ne_zero (Real.sqrt_ne_zero'.2 (by positivity : (0 : ℝ) < (8 : ℝ))))
  have hUnits := (linearIndependent_leechGeneratorRowsUnscaled).units_smul (fun _ : Fin 24 => u)
  assumption


-- @@ L154-156 expanded
/-- An explicit `ℝ`-basis of `ℝ²⁴` given by the generator rows of the Leech lattice. -/
public noncomputable def leechRBasis : Basis (Fin 24) ℝ (EuclideanSpace ℝ (Fin 24)) :=
  basisOfLinearIndependentOfCardEqFinrank linearIndependent_leechGeneratorRows (by simp)


-- @@ L158-161 verbatim
/-- The basis `leechRBasis` evaluates to the generator rows. -/
@[simp] public lemma leechRBasis_apply (i : Fin 24) :
    LeechLattice.leechRBasis i = leechGeneratorRows i := by
  simp [leechRBasis]


-- @@ L163-166 expanded
lemma range_leechRBasis :
    Set.range (LeechLattice.leechRBasis : Fin 24 → EuclideanSpace ℝ (Fin 24)) =
      Set.range leechGeneratorRows :=
  by
  ext x
  constructor <;> rintro ⟨i, rfl⟩ <;> exact ⟨i, by simp⟩


-- @@ L168-168 verbatim
end LeechLattice


-- @@ L170-185 expanded
/-- The Leech lattice is discrete in the ambient Euclidean space. -/
public instance instDiscreteLeechLattice : DiscreteTopology LeechLattice :=
  by
  let L : Submodule ℤ (EuclideanSpace ℝ (Fin 24)) :=
    Submodule.span ℤ (Set.range LeechLattice.leechRBasis)
  have hEq : (LeechLattice : Submodule ℤ (EuclideanSpace ℝ (Fin 24))) = L := by
    simp [LeechLattice, L, LeechLattice.range_leechRBasis]
  have hmem : ∀ x : LeechLattice, (x : EuclideanSpace ℝ (Fin 24)) ∈ L :=
    by
    intro x
    simpa [hEq] using x.property
  let f : LeechLattice → L := fun x => ⟨(x : EuclideanSpace ℝ (Fin 24)), hmem x⟩
  have hf : Continuous f := by
    -- `f` is the inclusion map, hence continuous.
    simpa [f] using (continuous_subtype_val.subtype_mk hmem)
  have hinj : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (by simpa [f] using congrArg Subtype.val hxy)
  exact DiscreteTopology.of_continuous_injective hf hinj


-- @@ L187-200 expanded
/-- The Leech lattice is a `ZLattice` over `ℝ`. -/
public instance instIsZLatticeLeechLattice : IsZLattice ℝ LeechLattice :=
  by
  refine
    ⟨?_⟩
      -- The ℝ-span of the Leech lattice is all of `ℝ²⁴` because it contains an ℝ-basis.
      
  have hbSpan : Submodule.span ℝ (Set.range LeechLattice.leechRBasis) = ⊤ :=
    LeechLattice.leechRBasis.span_eq
  have hgenSubset :
    Set.range leechGeneratorRows ⊆ (LeechLattice : Set (EuclideanSpace ℝ (Fin 24))) :=
    by
    rintro _ ⟨i, rfl⟩
    change leechGeneratorRows i ∈ Submodule.span ℤ (Set.range leechGeneratorRows)
    exact Submodule.subset_span ⟨i, rfl⟩
  have hbSubset :
    Set.range LeechLattice.leechRBasis ⊆ (LeechLattice : Set (EuclideanSpace ℝ (Fin 24))) := by
    simpa [LeechLattice.range_leechRBasis] using hgenSubset
  refine eq_top_iff.mpr ?_
  simpa [hbSpan] using (Submodule.span_mono (R := ℝ) hbSubset)


-- @@ L202-202 verbatim
end SpherePacking.Dim24
