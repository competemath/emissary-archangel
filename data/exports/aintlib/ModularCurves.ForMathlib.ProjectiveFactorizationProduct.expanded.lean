/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import ModularCurves.ForMathlib.ProjectiveFactorization
import ModularCurves.ForMathlib.SegreEmbedding


-- @@ L11-17 verbatim
/-!
# Binary products of projective factorizations

The fibre product of two schemes embedded in polynomial projective spaces embeds as a closed
subscheme of the product of those spaces. The Segre embedding then gives one polynomial
projective-space factorization over the original affine base.
-/


-- @@ L19-19 verbatim
open CategoryTheory Limits


-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
universe u


-- @@ L25-25 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra


-- @@ L27-27 verbatim
namespace AlgebraicGeometry


-- @@ L29-41 verbatim
/-- The map on fibre products induced by two compatible projective embeddings. -/
def projectiveFiberProductMap {R : Type u} [CommRing R]
    {X Y : Scheme.{u}} {f : X ⟶ Spec (.of R)} {g : Y ⟶ Spec (.of R)}
    {m n : ℕ}
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) R))
    (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
    (hi : i ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (m + 1)) = f)
    (hj : j ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n + 1)) = g) :
    pullback f g ⟶ MvPolynomial.segreProductProj R m n :=
  pullback.map f g
    (MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (m + 1)))
    (MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n + 1)))
    i j (𝟙 _) (by simpa using hi.symm) (by simpa using hj.symm)


-- @@ L43-57 verbatim
@[reassoc]
lemma projectiveFiberProductMap_fst {R : Type u} [CommRing R]
    {X Y : Scheme.{u}} {f : X ⟶ Spec (.of R)} {g : Y ⟶ Spec (.of R)}
    {m n : ℕ}
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) R))
    (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
    (hi : i ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (m + 1)) = f)
    (hj : j ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n + 1)) = g) :
    projectiveFiberProductMap i j hi hj ≫
        pullback.fst
          (MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (m + 1)))
          (MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n + 1))) =
      pullback.fst f g ≫ i := by
  dsimp only [projectiveFiberProductMap, pullback.map]
  exact pullback.lift_fst _ _ _


-- @@ L59-73 verbatim
@[reassoc]
lemma projectiveFiberProductMap_snd {R : Type u} [CommRing R]
    {X Y : Scheme.{u}} {f : X ⟶ Spec (.of R)} {g : Y ⟶ Spec (.of R)}
    {m n : ℕ}
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) R))
    (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
    (hi : i ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (m + 1)) = f)
    (hj : j ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n + 1)) = g) :
    projectiveFiberProductMap i j hi hj ≫
        pullback.snd
          (MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (m + 1)))
          (MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n + 1))) =
      pullback.snd f g ≫ j := by
  dsimp only [projectiveFiberProductMap, pullback.map]
  exact pullback.lift_snd _ _ _


-- @@ L75-89 verbatim
/-- The map induced by two closed projective embeddings is a closed immersion. -/
lemma projectiveFiberProductMap_isClosedImmersion {R : Type u} [CommRing R]
    {X Y : Scheme.{u}} {f : X ⟶ Spec (.of R)} {g : Y ⟶ Spec (.of R)}
    {m n : ℕ}
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) R))
    (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
    (hi : i ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (m + 1)) = f)
    (hj : j ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n + 1)) = g)
    (hiClosed : IsClosedImmersion i) (hjClosed : IsClosedImmersion j) :
    IsClosedImmersion (projectiveFiberProductMap i j hi hj) := by
  letI : MorphismProperty.IsStableUnderComposition @IsClosedImmersion :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  exact MorphismProperty.pullbackMap
    (P := @IsClosedImmersion) hiClosed hjClosed
    (by simpa using hi.symm) (by simpa using hj.symm)


-- @@ L91-91 verbatim
namespace IsProjectiveFactorization


-- @@ L93-93 verbatim
variable {R : Type u} [CommRing R]

-- @@ L94-94 verbatim
variable {X Y : Scheme.{u}} {f : X ⟶ Spec (.of R)} {g : Y ⟶ Spec (.of R)}


-- @@ L96-115 verbatim
/-- Fibre products of projective factorizations are projective over the common base. -/
lemma pullback (hf : IsProjectiveFactorization f)
    (hg : IsProjectiveFactorization g) :
    IsProjectiveFactorization (pullback.fst f g ≫ f) := by
  obtain ⟨m, i, hi, hif⟩ := hf
  obtain ⟨n, j, hj, hjg⟩ := hg
  let productMap := projectiveFiberProductMap i j hif hjg
  have hproductMap : IsClosedImmersion productMap :=
    projectiveFiberProductMap_isClosedImmersion i j hif hjg hi hj
  letI : IsClosedImmersion productMap := hproductMap
  letI : IsClosedImmersion (MvPolynomial.segreProductEmbedding R m n) :=
    MvPolynomial.segreProductEmbedding_isClosedImmersion R m n
  refine ⟨MvPolynomial.segreDimension m n,
    productMap ≫ MvPolynomial.segreProductEmbedding R m n, inferInstance, ?_⟩
  rw [Category.assoc,
    MvPolynomial.segreProductEmbedding_comp_homogeneousProjπ,
    MvPolynomial.segreProductπ,
    ← Category.assoc,
    projectiveFiberProductMap_fst,
    Category.assoc, hif]


-- @@ L117-117 verbatim
end IsProjectiveFactorization


-- @@ L119-119 verbatim
end AlgebraicGeometry
