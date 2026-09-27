/-
Copyright (c) 2026 Utensil Song, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song, OpenAI
-/
/-

Derived in part from Apache-2.0 `deancureton/ten-proofs`,
`ConnesRigidity/SymplecticData.lean` at
66af8383b1dbc53e21ceefc917a503b9bd88df51, lines 32-166.
Modifications: isolated the arithmetic carriers, narrowed imports, and changed
the namespace for the Zhou §2 and §5 interfaces. See the upstream PORT_MAP.md.
-/
module

public import Mathlib.LinearAlgebra.SymplecticGroup


-- @@ L18-20 verbatim
/-!
The arithmetic symplectic component of the Connes rigidity formalization.
-/


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
namespace Connes

-- @@ L25-25 verbatim
namespace OpenAIPort


-- @@ L27-27 verbatim
open Matrix


-- @@ L29-31 verbatim
universe u

/- The following carriers follow the public source naming. -/


-- @@ L33-36 verbatim
/--
The `SymplecticIndex` construction used in the Connes rigidity formalization.
-/
abbrev SymplecticIndex := Fin 2 ⊕ Fin 2


-- @@ L38-41 verbatim
/--
The `IntegralLattice` construction used in the Connes rigidity formalization.
-/
abbrev IntegralLattice := SymplecticIndex → ℤ


-- @@ L43-46 verbatim
/--
The `ModTwoSpace` construction used in the Connes rigidity formalization.
-/
abbrev ModTwoSpace := SymplecticIndex → ZMod 2


-- @@ L48-51 verbatim
/--
The `IntegralSymplecticGroup` construction used in the Connes rigidity formalization.
-/
abbrev IntegralSymplecticGroup := Matrix.symplecticGroup (Fin 2) ℤ


-- @@ L53-60 verbatim
instance : Countable IntegralSymplecticGroup := by
  let f : IntegralSymplecticGroup → SymplecticIndex → SymplecticIndex → ℤ :=
    fun g i j ↦ g.1 i j
  apply (show Function.Injective f by
    intro g h hgh
    apply Subtype.ext
    funext i j
    exact congr_fun (congr_fun hgh i) j).countable


-- @@ L62-67 verbatim
instance : DistribMulAction IntegralSymplecticGroup IntegralLattice :=
  DistribMulAction.compHom IntegralLattice
    (Matrix.symplecticGroup (Fin 2) ℤ).subtype

/- Reduction of the integral matrix action. Paper: §2.
-/

-- @@ L68-79 verbatim
/--
The `reducedMatrixHom` construction used in the Connes rigidity formalization.
-/
def reducedMatrixHom :
    IntegralSymplecticGroup →* Matrix SymplecticIndex SymplecticIndex (ZMod 2) where
  toFun g := (g.1 : Matrix SymplecticIndex SymplecticIndex ℤ).map
    (Int.castRingHom (ZMod 2))
  map_one' :=
    Matrix.map_one (Int.castRingHom (ZMod 2)) (map_zero _) (map_one _)
  map_mul' g h := by
    ext i j
    simp [Matrix.mul_apply]


-- @@ L81-82 verbatim
instance : DistribMulAction IntegralSymplecticGroup ModTwoSpace :=
  DistribMulAction.compHom ModTwoSpace reducedMatrixHom


-- @@ L84-93 verbatim
/-- Coordinatewise reduction. Paper: §2.
-/
def reduceVector : IntegralLattice →+ ModTwoSpace where
  toFun v i := (v i : ZMod 2)
  map_zero' := by
    funext i
    simp
  map_add' v w := by
    funext i
    simp


-- @@ L95-100 verbatim
/-- Evaluation of coordinatewise reduction. Paper: §2. -/
@[simp] theorem reduceVector_apply (v : IntegralLattice) (i : SymplecticIndex) :
    reduceVector v i = (v i : ZMod 2) := rfl

/- A canonical integral lift. Paper: §2.
-/

-- @@ L101-105 verbatim
/--
The `liftVector` construction used in the Connes rigidity formalization.
-/
def liftVector (w : ModTwoSpace) : IntegralLattice :=
  fun i ↦ ZMod.cast (w i)


-- @@ L107-114 verbatim
/-- Reduction recovers the canonical lift. Paper: §2. -/
@[simp] theorem reduceVector_liftVector (w : ModTwoSpace) :
    reduceVector (liftVector w) = w := by
  funext i
  change ((ZMod.cast (w i) : ℤ) : ZMod 2) = w i
  exact ZMod.intCast_zmod_cast _

/- The lift of zero is zero. Paper: §2. -/

-- @@ L115-119 verbatim
@[simp] theorem liftVector_zero : liftVector (0 : ModTwoSpace) = 0 := by
  funext i
  simp [liftVector]

/- Reduction commutes with the symplectic action. Paper: §2. -/

-- @@ L120-125 verbatim
theorem reduceVector_smul (g : IntegralSymplecticGroup) (v : IntegralLattice) :
    reduceVector (g • v) = g • reduceVector v := by
  funext i
  exact RingHom.map_mulVec (Int.castRingHom (ZMod 2)) g.1 v i

/- The mod-two carrier has exponent two. Paper: §2. -/

-- @@ L126-133 verbatim
theorem modTwoSpace_exponent_two (w : ModTwoSpace) :
    (2 : ℕ) • w = 0 := by
  funext i
  change (2 : ℕ) • w i = 0
  rw [two_nsmul]
  exact CharTwo.add_self_eq_zero _

/- Vanishing reduction admits an integral half. Paper: §2. -/

-- @@ L134-148 verbatim
theorem exists_half_of_reduceVector_eq_zero
    (v : IntegralLattice) (hv : reduceVector v = 0) :
    ∃ u : IntegralLattice, (2 : ℕ) • u = v := by
  have hdiv : ∀ i, (2 : ℤ) ∣ v i := by
    intro i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (v i) 2).mp
    have hi := congr_fun hv i
    simpa using hi
  choose u hu using hdiv
  refine ⟨u, ?_⟩
  funext i
  change (2 : ℕ) • u i = v i
  simpa [nsmul_eq_mul] using (hu i).symm

/- Doubling is injective on the integral lattice. Paper: §2. -/

-- @@ L149-154 verbatim
theorem two_nsmul_integralLattice_injective :
    Function.Injective (fun v : IntegralLattice ↦ (2 : ℕ) • v) := by
  exact nsmul_right_injective (by norm_num : (2 : ℕ) ≠ 0)

/- The alternating form used by the quadratic refinement. Paper: §2.
-/

-- @@ L155-160 verbatim
/--
The `modTwoSymplecticForm` construction used in the Connes rigidity formalization.
-/
def modTwoSymplecticForm (x y : ModTwoSpace) : ZMod 2 :=
  ∑ i : Fin 2, (x (Sum.inl i) * y (Sum.inr i) +
    x (Sum.inr i) * y (Sum.inl i))


-- @@ L162-167 verbatim
/-- The standard quadratic refinement. Paper: §2.
-/
def standardQuadraticForm (x : ModTwoSpace) : ZMod 2 :=
  ∑ i : Fin 2, x (Sum.inl i) * x (Sum.inr i)

/- Polarization of the standard quadratic refinement. Paper: §2. -/

-- @@ L168-181 verbatim
theorem standardQuadraticForm_add (x y : ModTwoSpace) :
    standardQuadraticForm (x + y) =
      standardQuadraticForm x + standardQuadraticForm y + modTwoSymplecticForm x y := by
  classical
  simp only [standardQuadraticForm, modTwoSymplecticForm, Pi.add_apply, add_mul, mul_add,
    Finset.sum_add_distrib]
  have hcross :
      (∑ i : Fin 2, y (Sum.inl i) * x (Sum.inr i)) =
        ∑ i : Fin 2, x (Sum.inr i) * y (Sum.inl i) := by
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  rw [hcross]
  abel


-- @@ L183-183 verbatim
end OpenAIPort

-- @@ L184-184 verbatim
end Connes
