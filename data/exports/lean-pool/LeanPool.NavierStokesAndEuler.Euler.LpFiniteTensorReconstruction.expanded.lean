/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.SmoothLimit


-- @@ L11-17 verbatim
/-!
# Reconstructing actual L² tensors from finitely many coordinate fields

This qualitative finite-dimensional construction supplies literal tensor-valued
L² derivatives. Quantitative Gevrey estimates continue to use the ordered-word
norms directly, and do not pass through these coordinate norm equivalences.
-/


-- @@ L19-19 verbatim
@[expose] public section



-- @@ L22-22 verbatim
noncomputable section


-- @@ L24-24 verbatim
namespace EulerLpFiniteTensor


-- @@ L26-26 verbatim
open MeasureTheory ContinuousLinearMap EulerSmoothLimit


-- @@ L28-29 verbatim
variable {X V : Type*} [MeasurableSpace X]
  [NormedAddCommGroup V] [NormedSpace ℝ V]


-- @@ L31-31 verbatim
section Tuple


-- @@ L33-33 verbatim
variable (μ : Measure X) {ι : Type*} [Fintype ι]


-- @@ L35-39 verbatim
/-- A finite tuple of L² classes gives its literal product-valued L² class. -/
def tupleLp : (ι → Lp V 2 μ) →L[ℝ] Lp (ι → V) 2 μ := by
  classical
  exact ∑ i : ι, ((ContinuousLinearMap.single ℝ (fun _ : ι => V) i).compLpL 2 μ).comp
    (ContinuousLinearMap.proj i)


-- @@ L41-55 verbatim
theorem tupleLp_ae (u : ι → Lp V 2 μ) :
    (tupleLp (V := V) (ι := ι) μ u : X → (ι → V)) =ᵐ[μ] fun x i => u i x := by
  classical
  let L (i : ι) : V →L[ℝ] (ι → V) := ContinuousLinearMap.single ℝ (fun _ : ι => V) i
  have hu : ∀ᵐ x ∂μ, ∀ i : ι, (L i).compLpL 2 μ (u i) x = L i (u i x) :=
    ae_all_iff.mpr (fun i => (L i).coeFn_compLpL (u i))
  have hs := Lp.coeFn_fun_finsetSum Finset.univ (fun i : ι => (L i).compLpL 2 μ (u i))
  have he : tupleLp (V := V) (ι := ι) μ u = ∑ i : ι, (L i).compLpL 2 μ (u i) := by
    simp only [tupleLp, sum_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, L]
  filter_upwards [hu, hs] with x hx hsum
  rw [he, hsum]
  simp only [hx]
  ext j
  simp [L]


-- @@ L57-57 verbatim
end Tuple


-- @@ L59-60 verbatim
/-- Coordinate directions in the ordinary spatial domain. -/
def direction (i : Fin 3) : Space := EuclideanSpace.single i 1


-- @@ L62-67 verbatim
/-- Tensor coordinates, given by `ContinuousLinearMap.pi (fun w => (ContinuousLinearMap.id ℝ
(Space [×n]→L[ℝ] V)).flipMultilinear (fun i => direction (w i)))`. -/
def tensorCoordinates (n : ℕ) :
    (Space [×n]→L[ℝ] V) →L[ℝ] ((Fin n → Fin 3) → V) :=
  ContinuousLinearMap.pi (fun w =>
    (ContinuousLinearMap.id ℝ (Space [×n]→L[ℝ] V)).flipMultilinear (fun i => direction (w i)))


-- @@ L69-70 verbatim
@[simp] theorem tensorCoordinates_apply (n : ℕ) (A : Space [×n]→L[ℝ] V)
    (w : Fin n → Fin 3) : tensorCoordinates n A w = A (fun i => direction (w i)) := rfl


-- @@ L72-81 verbatim
theorem tensorCoordinates_injective (n : ℕ) :
    Function.Injective (tensorCoordinates (V := V) n) := by
  intro A B h
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear (fun _ : Fin n => (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis)
  intro w
  have hw := congrFun h w
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  change A (fun i => direction (w i)) = B (fun i => direction (w i))
  exact hw


-- @@ L83-83 verbatim
variable [FiniteDimensional ℝ V]


-- @@ L85-88 verbatim
/-- A fixed bounded left inverse of the finite coordinate evaluation map. -/
def tensorReassembly (n : ℕ) :
    ((Fin n → Fin 3) → V) →L[ℝ] (Space [×n]→L[ℝ] V) :=
  ((tensorCoordinates (V := V) n).toLinearMap.leftInverse).toContinuousLinearMap


-- @@ L90-92 verbatim
@[simp] theorem tensorReassembly_coordinates (n : ℕ) (A : Space [×n]→L[ℝ] V) :
    tensorReassembly n (tensorCoordinates n A) = A :=
  LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr (tensorCoordinates_injective n)) A


-- @@ L94-97 verbatim
/-- Reconstruction is a genuine bounded map on the finite tuple of L² classes. -/
def tensorLpReassembly (μ : Measure X) (n : ℕ) :
    ((Fin n → Fin 3) → Lp V 2 μ) →L[ℝ] Lp (Space [×n]→L[ℝ] V) 2 μ :=
  ((tensorReassembly (V := V) n).compLpL 2 μ).comp (tupleLp (V := V) (ι := Fin n → Fin 3) μ)


-- @@ L99-107 verbatim
theorem tensorLpReassembly_ae (μ : Measure X) (n : ℕ)
    (u : (Fin n → Fin 3) → Lp V 2 μ) :
    (tensorLpReassembly μ n u : X → (Space [×n]→L[ℝ] V)) =ᵐ[μ]
      fun x => tensorReassembly n (fun w => u w x) := by
  filter_upwards [(tensorReassembly (V := V) n).coeFn_compLpL (tupleLp (V := V) (ι := Fin n → Fin
      3) μ u),
    tupleLp_ae μ u]
    with x h₁ h₂
  exact h₁.trans (congrArg (tensorReassembly n) h₂)


-- @@ L109-119 verbatim
/-- If the coordinate L² classes represent a literal tensor field, their
reconstruction represents that field, with no integrability assumption on it. -/
theorem tensorLpReassembly_eq_ae (μ : Measure X) (n : ℕ)
    (u : (Fin n → Fin 3) → Lp V 2 μ) (f : X → (Space [×n]→L[ℝ] V))
    (h : ∀ w, (u w : X → V) =ᵐ[μ] fun x => f x (fun i => direction (w i))) :
    (tensorLpReassembly μ n u : X → (Space [×n]→L[ℝ] V)) =ᵐ[μ] f := by
  have ha : ∀ᵐ x ∂μ, ∀ w, u w x = f x (fun i => direction (w i)) := ae_all_iff.mpr h
  filter_upwards [tensorLpReassembly_ae μ n u, ha] with x hx hw
  rw [hx]
  have he : (fun w => u w x) = tensorCoordinates n (f x) := funext hw
  rw [he, tensorReassembly_coordinates]


-- @@ L121-121 verbatim
end EulerLpFiniteTensor
