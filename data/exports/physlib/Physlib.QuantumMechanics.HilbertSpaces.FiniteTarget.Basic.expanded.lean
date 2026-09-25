/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Physlib.Meta.TODO.Basic

-- @@ L10-28 verbatim
/-!

# The Hilbert space of a finite target quantum mechanical system

A finite target quantum mechanical system is one whose states live in a finite
dimensional Hilbert space, with the basis states labelled by a finite type `d`
(for example the sites of a finite lattice, or the levels of a qudit).

This file contains
- the definition of `FiniteHilbertSpace d`, the Hilbert space of such a system,
  as a structure wrapping `EuclideanSpace ℂ d`, together with the notation `𝓗[d]`;
- its vector space structure (`AddCommGroup` and `Module ℂ`), transferred from
  `EuclideanSpace ℂ d` along the equivalence `equivEuclidean`;
- its Hilbert space structure (`NormedAddCommGroup`, `InnerProductSpace ℂ`,
  `FiniteDimensional ℂ` and `CompleteSpace`), induced along `linearEquivEuclidean`;
- the standard orthonormal basis `basisFun`, whose elements are the states
  localized at the points of `d`.

-/


-- @@ L30-30 verbatim
@[expose] public section


-- @@ L32-32 verbatim
namespace QuantumMechanics


-- @@ L34-48 verbatim
TODO "To match this with the results currently in the `QuantumInfo` part of the library,
  we should:
  1. Define `FiniteHilbertSpace` as a structure with a single entry `val`, this
    should take as an input a finite and decidable type `d`. Below this type is
    taken as default to be `Fin n`.
  2. On this type we should then define the structure of an inner-product space, and a
    Hilbert space.
  3. We could then define the notation `𝓗[d]` to denote the Hilbert space corresponding
    to the type `d`.
  4. The results from `QuantumInfo/Finite/Braket.lean` can then be moved over
    to Physlib, and related to the definition of the Hilbert space here.
  Optional. Maybe it is worth moving these files to a directory called `States`, with
  the idea that it includes this definition of the Hilbert space, the
  definition of bras and kets, and the definition of mixed states. Maybe also
  parts of `./ResourceTheory/FreeState`."


-- @@ L50-64 verbatim
/-- The Hilbert space of a finite target quantum mechanical system whose target is
  a finite type `d` with decidable equality.

  It is defined as a structure with a single field `val`, wrapping an element of
  `EuclideanSpace ℂ d` — the space of functions `d → ℂ` carrying the `L²` inner
  product `⟪ψ, φ⟫ = ∑ i, conj (ψ i) * φ i`. Using a structure in preference to
  `EuclideanSpace ℂ d` itself makes the Hilbert space of states a type of its own,
  with its own API and the notation `𝓗[d]`.

  Being finite dimensional, it is automatically a complete inner product space,
  that is, a genuine Hilbert space. -/
@[ext]
structure FiniteHilbertSpace (d : Type*) [Fintype d] [DecidableEq d] where
  /-- The underlying element of `EuclideanSpace ℂ d`. -/
  val : EuclideanSpace ℂ d


-- @@ L66-67 verbatim
@[inherit_doc FiniteHilbertSpace]
scoped notation "𝓗[" d "]" => FiniteHilbertSpace d


-- @@ L69-69 verbatim
namespace FiniteHilbertSpace


-- @@ L71-71 verbatim
variable {d : Type*} [Fintype d] [DecidableEq d]


-- @@ L73-79 verbatim
/-- The equivalence between `FiniteHilbertSpace d` and `EuclideanSpace ℂ d`
  given by `val`. -/
def equivEuclidean : FiniteHilbertSpace d ≃ EuclideanSpace ℂ d where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl


-- @@ L81-88 verbatim
/-!

## The vector space structure on `FiniteHilbertSpace d`

The vector space structure is transferred from `EuclideanSpace ℂ d`
along the equivalence `equivEuclidean`.

-/


-- @@ L90-90 verbatim
noncomputable instance : AddCommGroup (FiniteHilbertSpace d) := equivEuclidean.addCommGroup


-- @@ L92-92 verbatim
noncomputable instance : Module ℂ (FiniteHilbertSpace d) := equivEuclidean.module ℂ


-- @@ L94-95 verbatim
@[simp]
lemma val_add (ψ φ : FiniteHilbertSpace d) : (ψ + φ).val = ψ.val + φ.val := rfl


-- @@ L97-98 verbatim
@[simp]
lemma val_smul (c : ℂ) (ψ : FiniteHilbertSpace d) : (c • ψ).val = c • ψ.val := rfl


-- @@ L100-101 verbatim
@[simp]
lemma val_zero : (0 : FiniteHilbertSpace d).val = 0 := rfl


-- @@ L103-108 verbatim
/-- The equivalence between `FiniteHilbertSpace d` and `EuclideanSpace ℂ d`
  as a `ℂ`-linear equivalence, upgrading `equivEuclidean`. -/
noncomputable def linearEquivEuclidean : FiniteHilbertSpace d ≃ₗ[ℂ] EuclideanSpace ℂ d :=
  { equivEuclidean with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }


-- @@ L110-118 verbatim
/-!

## The Hilbert space structure on `FiniteHilbertSpace d`

The norm and inner product are induced from `EuclideanSpace ℂ d` along
`linearEquivEuclidean`, making `FiniteHilbertSpace d` a finite dimensional
(and hence complete) inner product space, that is, a Hilbert space.

-/


-- @@ L120-121 verbatim
noncomputable instance : NormedAddCommGroup (FiniteHilbertSpace d) :=
  NormedAddCommGroup.induced _ _ linearEquivEuclidean.toLinearMap linearEquivEuclidean.injective


-- @@ L123-124 verbatim
@[simp]
lemma norm_eq_val (ψ : FiniteHilbertSpace d) : ‖ψ‖ = ‖ψ.val‖ := rfl


-- @@ L126-127 verbatim
noncomputable instance : InnerProductSpace ℂ (FiniteHilbertSpace d) :=
  InnerProductSpace.induced linearEquivEuclidean.toLinearMap


-- @@ L129-130 verbatim
@[simp]
lemma inner_eq_val (ψ φ : FiniteHilbertSpace d) : inner ℂ ψ φ = inner ℂ ψ.val φ.val := rfl


-- @@ L132-133 verbatim
instance : FiniteDimensional ℂ (FiniteHilbertSpace d) :=
  Module.Finite.equiv linearEquivEuclidean.symm


-- @@ L135-135 verbatim
instance : CompleteSpace (FiniteHilbertSpace d) := FiniteDimensional.complete ℂ _


-- @@ L137-141 verbatim
/-- The equivalence between `FiniteHilbertSpace d` and `EuclideanSpace ℂ d`
  as a linear isometry equivalence, upgrading `linearEquivEuclidean`. -/
noncomputable def isometryEquivEuclidean : FiniteHilbertSpace d ≃ₗᵢ[ℂ] EuclideanSpace ℂ d where
  toLinearEquiv := linearEquivEuclidean
  norm_map' _ := rfl


-- @@ L143-147 verbatim
/-!

## The standard orthonormal basis of `FiniteHilbertSpace d`

-/


-- @@ L149-152 verbatim
/-- The standard orthonormal basis of `FiniteHilbertSpace d`, indexed by `d`. -/
noncomputable def basisFun (d : Type*) [Fintype d] [DecidableEq d] :
    OrthonormalBasis d ℂ (FiniteHilbertSpace d) :=
  (EuclideanSpace.basisFun d ℂ).map isometryEquivEuclidean.symm


-- @@ L154-155 verbatim
lemma basisFun_apply (i : d) : basisFun d i = ⟨EuclideanSpace.single i 1⟩ := by
  rw [basisFun, OrthonormalBasis.map_apply, EuclideanSpace.basisFun_apply]; rfl


-- @@ L157-157 verbatim
end FiniteHilbertSpace


-- @@ L159-159 verbatim
end QuantumMechanics
