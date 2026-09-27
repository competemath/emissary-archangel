/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-
-/
module

public import LeanPool.ConnesRigidity.Construction


-- @@ L12-15 verbatim
/-!
Algebraic part of Zhou §3 for the concrete tensor kernel, including the
quadratic fiber shear and its characteristic-two involutivity.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
namespace Connes

-- @@ L20-20 verbatim
namespace PaperFactorIsomorphism


-- @@ L22-22 verbatim
noncomputable section


-- @@ L24-27 verbatim
/--
The `k` construction used in the Connes rigidity formalization.
-/
abbrev k := Construction.k

-- @@ L28-31 verbatim
/--
The `A` construction used in the Connes rigidity formalization.
-/
abbrev A := Construction.A

-- @@ L32-35 verbatim
/--
The `PaperV` construction used in the Connes rigidity formalization.
-/
abbrev PaperV := Construction.PaperKernel.PaperV

-- @@ L36-39 verbatim
/--
The `SymplecticIndex` construction used in the Connes rigidity formalization.
-/
abbrev SymplecticIndex := OpenAIPort.SymplecticIndex

-- @@ L40-43 verbatim
/--
The `C` construction used in the Connes rigidity formalization.
-/
abbrev C := Construction.PaperKernel.C

-- @@ L44-47 verbatim
/--
The `TensorAA` construction used in the Connes rigidity formalization.
-/
abbrev TensorAA := Construction.PaperKernel.TensorAA

-- @@ L48-51 verbatim
/--
The `H` construction used in the Connes rigidity formalization.
-/
abbrev H := Construction.H


-- @@ L53-55 verbatim
/-- The algebraic dual coordinates used by Zhou's fiber model. Paper: §3. -/
abbrev DualCoordinates :=
  (A →ₗ[k] PaperV) × (C →ₗ[k] k)


-- @@ L57-61 verbatim
/-- One finite coordinate of a map `A → V`. Paper: §3. -/
def coordinate (z : A →ₗ[k] PaperV) (i : SymplecticIndex) : A →ₗ[k] k where
  toFun a := z a i
  map_add' a b := by simp
  map_smul' r a := by simp


-- @@ L63-84 verbatim
/-- Bilinear evaluation on a pure tensor. Paper: §3. -/
def tensorFunctional (f g : A →ₗ[k] k) : TensorAA →ₗ[k] k :=
  TensorProduct.lift
    { toFun := fun a =>
        { toFun := fun b => f a * g b
          map_add' := by
            intro b c
            simp [mul_add]
          map_smul' := by
            intro r b
            simp [smul_eq_mul]
            ring }
      map_add' := by
        intro a b
        apply LinearMap.ext
        intro c
        simp [add_mul]
      map_smul' := by
        intro r a
        apply LinearMap.ext
        intro b
        simp [smul_eq_mul, mul_assoc] }


-- @@ L86-88 verbatim
/-- Restriction of tensor evaluation to the flip-fixed carrier. Paper: §3. -/
def tensorFunctionalOnC (f g : A →ₗ[k] k) : C →ₗ[k] k :=
  (tensorFunctional f g).domRestrict C


-- @@ L90-95 verbatim
@[simp] theorem tensorFunctionalOnC_diagonal
    (f g : A →ₗ[k] k) (a : A) :
    tensorFunctionalOnC f g (Construction.PaperKernel.diagonal a) =
      f a * g a := by
  simp [tensorFunctionalOnC, tensorFunctional,
    Construction.PaperKernel.diagonal]


-- @@ L97-100 verbatim
/-- Zhou's quadratic functional on the symmetric tensor dual. Paper: §3. -/
def quadraticMap (z : A →ₗ[k] PaperV) : C →ₗ[k] k :=
  tensorFunctionalOnC (coordinate z (Sum.inl 0)) (coordinate z (Sum.inr 0)) +
    tensorFunctionalOnC (coordinate z (Sum.inl 1)) (coordinate z (Sum.inr 1))


-- @@ L102-105 verbatim
@[simp] theorem quadraticMap_diagonal (z : A →ₗ[k] PaperV) (a : A) :
    quadraticMap z (Construction.PaperKernel.diagonal a) =
      OpenAIPort.standardQuadraticForm (z a) := by
  simp [quadraticMap, coordinate, OpenAIPort.standardQuadraticForm]


-- @@ L107-109 verbatim
/-- The nontrivial fiber shear from Zhou Proposition 3.2. Paper: §3. -/
def fiberShear : DualCoordinates → DualCoordinates := fun p =>
  (p.1, p.2 + quadraticMap p.1)


-- @@ L111-119 verbatim
/-- The characteristic-two cancellation behind the fiber shear. Paper: §3. -/
theorem fiberShear_involutive (p : DualCoordinates) :
    fiberShear (fiberShear p) = p := by
  apply Prod.ext
  · rfl
  · apply LinearMap.ext
    intro c
    change (p.2 c + quadraticMap p.1 c) + quadraticMap p.1 c = p.2 c
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]


-- @@ L121-121 verbatim
end

-- @@ L122-122 verbatim
end PaperFactorIsomorphism

-- @@ L123-123 verbatim
end Connes
