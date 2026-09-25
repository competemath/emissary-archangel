/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.IsManifold.Basic

-- @@ L10-17 verbatim
/-!

# Lorentz Vectors

In this module we define Lorentz vectors as real Lorentz tensors with a single up index.
We create an API around Lorentz vectors to make working with them as easy as possible.

-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
open Module

-- @@ L22-22 verbatim
open Matrix

-- @@ L23-23 verbatim
open MatrixGroups

-- @@ L24-24 verbatim
open Complex

-- @@ L25-25 verbatim
open TensorProduct


-- @@ L27-27 verbatim
noncomputable section


-- @@ L29-29 verbatim
namespace Lorentz


-- @@ L31-38 verbatim
/-- Real contravariant Lorentz vector. -/
@[implicit_reducible]
def Vector (d : ℕ := 3) := Fin 1 ⊕ Fin d → ℝ

/- `Vector d` is applied directly as a function throughout the library. Marking it
  implicit-reducible lets such applications typecheck at implicit transparency, so that
  `rw` and `simp` can match patterns containing them (see the Lean 4.33 release notes on
  `backward.isDefEq.respectTransparency.types`). -/


-- @@ L40-40 verbatim
namespace Vector


-- @@ L42-43 verbatim
instance {d} : AddCommMonoid (Vector d) :=
  inferInstanceAs (AddCommMonoid (Fin 1 ⊕ Fin d → ℝ))


-- @@ L45-46 verbatim
instance {d} : Module ℝ (Vector d) :=
  inferInstanceAs (Module ℝ (Fin 1 ⊕ Fin d → ℝ))


-- @@ L48-49 verbatim
instance {d} : AddCommGroup (Vector d) :=
  inferInstanceAs (AddCommGroup (Fin 1 ⊕ Fin d → ℝ))


-- @@ L51-52 verbatim
instance {d} : FiniteDimensional ℝ (Vector d) :=
  inferInstanceAs (FiniteDimensional ℝ (Fin 1 ⊕ Fin d → ℝ))


-- @@ L54-57 verbatim
/-- The equivalence between `Vector d` and `EuclideanSpace ℝ (Fin 1 ⊕ Fin d)`. -/
def equivEuclid (d : ℕ) :
    Vector d ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 1 ⊕ Fin d) :=
  (WithLp.linearEquiv _ _ _).symm


-- @@ L59-61 verbatim
@[simp]
lemma equivEuclid_apply (d : ℕ) (v : Vector d) (i : Fin 1 ⊕ Fin d) :
    equivEuclid d v i = v i := rfl


-- @@ L63-67 verbatim
@[ext]
lemma eq_of_apply_eq {d : ℕ} {v w : Vector d} (h : ∀ i, v i = w i) : v = w := by
  apply (equivEuclid d).injective
  ext i
  simpa using h i


-- @@ L69-70 verbatim
instance (d : ℕ) : Norm (Vector d) where
  norm := fun v => ‖equivEuclid d v‖


-- @@ L72-73 verbatim
lemma norm_eq_equivEuclid (d : ℕ) (v : Vector d) :
    ‖v‖ = ‖equivEuclid d v‖ := rfl


-- @@ L75-82 verbatim
@[simp]
lemma abs_component_le_norm {d : ℕ} (v : Vector d) (i : Fin 1 ⊕ Fin d) :
    |v i| ≤ ‖v‖ := by
  simp [norm_eq_equivEuclid, PiLp.norm_eq_of_L2, -Fintype.sum_sum_type]
  refine Real.abs_le_sqrt ?_
  trans ∑ j ∈ {i}, (v j) ^ 2
  · simp
  refine Finset.sum_le_univ_sum_of_nonneg (fun i => by positivity)


-- @@ L84-96 verbatim
instance isNormedAddCommGroup (d : ℕ) : NormedAddCommGroup (Vector d) where
  dist_self x := by simp [norm_eq_equivEuclid]
  dist_comm x y := by
    simpa [norm_eq_equivEuclid, dist_eq_norm_neg_add] using dist_comm ((equivEuclid d) x) _
  dist_triangle x y z := by
    simpa [norm_eq_equivEuclid, dist_eq_norm_neg_add] using dist_triangle
      ((equivEuclid d) x) ((equivEuclid d) y) ((equivEuclid d) z)
  eq_of_dist_eq_zero {x y} := by
    simp only [norm_eq_equivEuclid, map_add]
    intro h
    apply (equivEuclid d).injective
    simp at h
    rw [← neg_add_eq_zero, h]


-- @@ L98-101 verbatim
instance isNormedSpace (d : ℕ) : NormedSpace ℝ (Vector d) where
  norm_smul_le c v := by
    simp only [norm_eq_equivEuclid, map_smul]
    exact norm_smul_le c (equivEuclid d v)

-- @@ L102-102 verbatim
open InnerProductSpace


-- @@ L104-105 verbatim
instance (d : ℕ) : Inner ℝ (Vector d) where
  inner := fun v w => ⟪equivEuclid d v, equivEuclid d w⟫_ℝ


-- @@ L107-108 verbatim
lemma inner_eq_equivEuclid (d : ℕ) (v w : Vector d) :
    ⟪v, w⟫_ℝ = ⟪equivEuclid d v, equivEuclid d w⟫_ℝ := rfl


-- @@ L110-123 verbatim
/-- The Euclidean inner product structure on `CoVector`. -/
instance innerProductSpace (d : ℕ) : InnerProductSpace ℝ (Vector d) where
  norm_sq_eq_re_inner v := by
    simp only [inner_eq_equivEuclid, norm_eq_equivEuclid]
    exact InnerProductSpace.norm_sq_eq_re_inner (equivEuclid d v)
  conj_inner_symm x y := by
    simp only [inner_eq_equivEuclid]
    exact InnerProductSpace.conj_inner_symm (equivEuclid d x) (equivEuclid d y)
  add_left x y z := by
    simp only [inner_eq_equivEuclid, map_add]
    exact InnerProductSpace.add_left (equivEuclid d x) (equivEuclid d y) (equivEuclid d z)
  smul_left x y r := by
    simp only [inner_eq_equivEuclid, map_smul]
    exact InnerProductSpace.smul_left (equivEuclid d x) (equivEuclid d y) r


-- @@ L125-128 verbatim
/-- The inner product on `Vector d` as a sum over components. -/
lemma inner_eq_sum {d : ℕ} (v w : Vector d) : ⟪v, w⟫_ℝ = ∑ μ, v μ * w μ := by
  rw [inner_eq_equivEuclid, PiLp.inner_apply]
  simp [mul_comm]


-- @@ L130-131 verbatim
/-- The instance of a `ChartedSpace` on `Vector d`. -/
instance : ChartedSpace (Vector d) (Vector d) := chartedSpaceSelf (Vector d)


-- @@ L133-134 verbatim
instance {d} : CoeFun (Vector d) (fun _ => Fin 1 ⊕ Fin d → ℝ) where
  coe := fun v => v


-- @@ L136-139 verbatim
lemma ext_of_apply {d} {v w : Vector d} (h : ∀ i, v i = w i) : v = w := by
  apply (equivEuclid d).injective
  ext i
  simpa using h i


-- @@ L141-143 verbatim
@[simp]
lemma apply_smul {d : ℕ} (c : ℝ) (v : Vector d) (i : Fin 1 ⊕ Fin d) :
    (c • v) i = c * v i := rfl


-- @@ L145-147 verbatim
@[simp]
lemma apply_add {d : ℕ} (v w : Vector d) (i : Fin 1 ⊕ Fin d) :
    (v + w) i = v i + w i := rfl


-- @@ L149-151 verbatim
@[simp]
lemma apply_sub {d : ℕ} (v w : Vector d) (i : Fin 1 ⊕ Fin d) :
    (v - w) i = v i - w i := by rfl


-- @@ L153-170 verbatim
lemma apply_sum {d : ℕ} {ι : Type} [Fintype ι] (f : ι → Vector d) (i : Fin 1 ⊕ Fin d) :
    (∑ j, f j) i = ∑ j, f j i := by
  let P (ι : Type) [Fintype ι] := ∀ (f : ι → Vector d) (i : Fin 1 ⊕ Fin d),
    (∑ j : ι, f j) i = ∑ j, f j i
  revert i f
  change P ι
  apply Fintype.induction_empty_option
  · intro ι1 ι2 _ e h1
    dsimp [P]
    intro f i
    have h' := h1 (f ∘ e) i
    simp at h'
    rw [← @e.sum_comp, ← @e.sum_comp, h']
  · intro f i
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    rfl
  · intro ι _ h f i
    rw [Fintype.sum_option, apply_add, h, Fintype.sum_option]


-- @@ L172-174 verbatim
@[simp]
lemma neg_apply {d : ℕ} (v : Vector d) (i : Fin 1 ⊕ Fin d) :
    (-v) i = - v i := rfl


-- @@ L176-178 verbatim
@[simp]
lemma zero_apply {d : ℕ} (i : Fin 1 ⊕ Fin d) :
    (0 : Vector d) i = 0 := rfl


-- @@ L180-184 verbatim
/-- The continuous linear map from a Lorentz vector to one of its coordinates. -/
def coordCLM {d : ℕ} (i : Fin 1 ⊕ Fin d) : Vector d →L[ℝ] ℝ := LinearMap.toContinuousLinearMap {
  toFun v := v i
  map_add' := by simp
  map_smul' := by simp}


-- @@ L186-187 verbatim
lemma coordCLM_apply {d : ℕ} (i : Fin 1 ⊕ Fin d) (v : Vector d) :
    coordCLM i v = v i := rfl


-- @@ L189-192 verbatim
@[fun_prop]
lemma coord_continuous {d : ℕ} (i : Fin 1 ⊕ Fin d) :
    Continuous (fun v : Vector d => v i) :=
  (coordCLM i).continuous


-- @@ L194-197 verbatim
@[fun_prop]
lemma coord_contDiff {n} {d : ℕ} (i : Fin 1 ⊕ Fin d) :
    ContDiff ℝ n (fun v : Vector d => v i) :=
  (coordCLM i).contDiff


-- @@ L199-202 verbatim
@[fun_prop]
lemma coord_differentiable {d : ℕ} (i : Fin 1 ⊕ Fin d) :
    Differentiable ℝ (fun v : Vector d => v i) :=
  (coordCLM i).differentiable


-- @@ L204-207 verbatim
@[fun_prop]
lemma coord_differentiableAt {d : ℕ} (i : Fin 1 ⊕ Fin d) (v : Vector d) :
    DifferentiableAt ℝ (fun v : Vector d => v i) v :=
  (coordCLM i).differentiableAt


-- @@ L209-211 verbatim
/-- The continuous linear equivalence between `Vector d` and Euclidean space. -/
def euclidCLE (d : ℕ) : Vector d ≃L[ℝ] EuclideanSpace ℝ (Fin 1 ⊕ Fin d) :=
  LinearEquiv.toContinuousLinearEquiv (equivEuclid d)


-- @@ L213-216 verbatim
/-- The continuous linear equivalence between `Vector d` and the corresponding `Pi` type. -/
def equivPi (d : ℕ) :
    Vector d ≃L[ℝ] Π (_ : Fin 1 ⊕ Fin d), ℝ :=
  LinearEquiv.toContinuousLinearEquiv (LinearEquiv.refl _ _)


-- @@ L218-220 verbatim
@[simp]
lemma equivPi_apply {d : ℕ} (v : Vector d) (i : Fin 1 ⊕ Fin d) :
    equivPi d v i = v i := rfl


-- @@ L222-231 verbatim
@[fun_prop]
lemma continuous_of_apply {d : ℕ} {α : Type*} [TopologicalSpace α]
    (f : α → Vector d)
    (h : ∀ i : Fin 1 ⊕ Fin d, Continuous (fun x => f x i)) :
    Continuous f := by
  rw [← (equivPi d).comp_continuous_iff]
  apply continuous_pi
  intro i
  simp only [Function.comp_apply, equivPi_apply]
  fun_prop


-- @@ L233-244 verbatim
lemma differentiable_apply {d : ℕ} {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]
    (f : α → Vector d) :
    (∀ i : Fin 1 ⊕ Fin d, Differentiable ℝ (fun x => f x i)) ↔ Differentiable ℝ f := by
  apply Iff.intro
  · intro h
    rw [← (Lorentz.Vector.equivPi d).comp_differentiable_iff]
    exact differentiable_pi'' h
  · intro h ν
    change Differentiable ℝ (Lorentz.Vector.coordCLM ν ∘ f)
    apply Differentiable.comp
    · fun_prop
    · exact h


-- @@ L246-260 verbatim
lemma contDiff_apply {n : WithTop ℕ∞} {d : ℕ} {α : Type*}
    [NormedAddCommGroup α] [NormedSpace ℝ α]
    (f : α → Vector d) :
    (∀ i : Fin 1 ⊕ Fin d, ContDiff ℝ n (fun x => f x i)) ↔ ContDiff ℝ n f := by
  apply Iff.intro
  · intro h
    rw [← (Lorentz.Vector.equivPi d).comp_contDiff_iff]
    apply contDiff_pi'
    intro ν
    exact h ν
  · intro h ν
    change ContDiff ℝ n (Lorentz.Vector.coordCLM ν ∘ f)
    apply ContDiff.comp
    · fun_prop
    · exact h


-- @@ L262-270 verbatim
lemma fderiv_apply {d : ℕ} {α : Type*}
    [NormedAddCommGroup α] [NormedSpace ℝ α]
    (f : α → Vector d) (h : Differentiable ℝ f)
    (x : α) (dt : α) (ν : Fin 1 ⊕ Fin d) :
    fderiv ℝ f x dt ν = fderiv ℝ (fun y => f y ν) x dt := by
  change _ = (fderiv ℝ (Lorentz.Vector.coordCLM ν ∘ f) x) dt
  rw [fderiv_comp _ (by fun_prop) (by fun_prop)]
  simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.coe_comp, Function.comp_apply]
  rfl


-- @@ L272-276 verbatim
@[simp]
lemma fderiv_coord {d : ℕ} (μ : Fin 1 ⊕ Fin d) (x : Vector d) :
    fderiv ℝ (fun v : Vector d => v μ) x = coordCLM μ := by
  change fderiv ℝ (coordCLM μ) x = coordCLM μ
  simp


-- @@ L278-282 verbatim
/-!

## Basis

-/


-- @@ L284-286 verbatim
/-- The basis on `Vector d` indexed by `Fin 1 ⊕ Fin d`. -/
def basis {d : ℕ} : Basis (Fin 1 ⊕ Fin d) ℝ (Vector d) :=
  Pi.basisFun ℝ _


-- @@ L288-294 verbatim
@[simp]
lemma basis_apply {d : ℕ} (μ ν : Fin 1 ⊕ Fin d) :
    basis μ ν = if μ = ν then 1 else 0 := by
  simp [basis]
  rw [Pi.basisFun_apply, Pi.single_apply]
  congr 1
  exact Lean.Grind.eq_congr' rfl rfl


-- @@ L296-299 verbatim
lemma basis_repr_apply {d : ℕ} (p : Vector d) (μ : Fin 1 ⊕ Fin d) :
    basis.repr p μ = p μ := by
  simp [basis]
  rw [Pi.basisFun_repr]


-- @@ L301-303 verbatim
lemma map_apply_eq_basis_mulVec {d : ℕ} (f : Vector d →ₗ[ℝ] Vector d) (p : Vector d) :
    (f p) = (LinearMap.toMatrix basis basis) f *ᵥ p := by
  exact Eq.symm (LinearMap.toMatrix_mulVec_repr basis basis f p)


-- @@ L305-313 verbatim
lemma sum_basis_eq_zero_iff {d : ℕ} (f : Fin 1 ⊕ Fin d → ℝ) :
    (∑ μ, f μ • basis μ) = 0 ↔ ∀ μ, f μ = 0 := by
  apply Iff.intro
  · intro h
    have h1 := (linearIndependent_iff').mp basis.linearIndependent Finset.univ f h
    intro μ
    exact h1 μ (by simp)
  · intro h
    simp [h]


-- @@ L315-325 verbatim
lemma sum_inl_inr_basis_eq_zero_iff {d : ℕ} (f₀ : ℝ) (f : Fin d → ℝ) :
    f₀ • basis (Sum.inl 0) + (∑ i, f i • basis (Sum.inr i)) = 0 ↔
    f₀ = 0 ∧ ∀ i, f i = 0 := by
  let f' : Fin 1 ⊕ Fin d → ℝ := fun μ =>
    match μ with
    | Sum.inl 0 => f₀
    | Sum.inr i => f i
  have h1 : f₀ • basis (Sum.inl 0) + (∑ i, f i • basis (Sum.inr i))
    = ∑ μ, f' μ • basis μ := by simp [f']
  rw [h1, sum_basis_eq_zero_iff]
  simp [f']


-- @@ L327-331 verbatim
/-!

## C. The Spatial part

-/


-- @@ L333-336 verbatim
/-- Extract spatial components from a Lorentz vector,
    returning them as a vector in Euclidean space. -/
abbrev spatialPart {d : ℕ} (v : Vector d) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun i => v (Sum.inr i)


-- @@ L338-339 verbatim
lemma spatialPart_apply_eq_toCoord {d : ℕ} (v : Vector d) (i : Fin d) :
    spatialPart v i = v (Sum.inr i) := rfl


-- @@ L341-346 verbatim
lemma spatialPart_basis_sum_inr {d : ℕ} (i : Fin d) (j : Fin d) :
    spatialPart (basis (Sum.inr i)) j =
      (Finsupp.single (Sum.inr i : Fin 1 ⊕ Fin d) 1) (Sum.inr j) := by
  simp [basis_apply]
  rw [Finsupp.single_apply]
  simp


-- @@ L348-349 verbatim
lemma spatialPart_basis_sum_inl {d : ℕ} (i : Fin d) :
    spatialPart (basis (Sum.inl 0)) i = 0 := by simp


-- @@ L351-356 verbatim
/-- The spatial part of a Lorentz vector as a continuous linear map. -/
def spatialCLM (d : ℕ) : Vector d →L[ℝ] EuclideanSpace ℝ (Fin d) where
  toFun v := WithLp.toLp 2 fun i => v (Sum.inr i)
  map_add' v1 v2 := by rfl
  map_smul' c v := by rfl
  cont := by fun_prop


-- @@ L358-359 verbatim
lemma spatialCLM_apply_eq_spatialPart {d : ℕ} (v : Vector d) (i : Fin d) :
    spatialCLM d v i = spatialPart v i := rfl


-- @@ L361-365 verbatim
@[simp]
lemma spatialCLM_basis_sum_inl {d : ℕ} :
    spatialCLM d (basis (Sum.inl 0)) = 0 := by
  ext i
  exact spatialPart_basis_sum_inl i


-- @@ L367-374 verbatim
@[simp]
lemma spatialCLM_basis_sum_inr {d : ℕ} (i : Fin d) :
    spatialCLM d (basis (Sum.inr i)) = EuclideanSpace.basisFun (Fin d) ℝ i := by
  ext j
  rw [spatialCLM_apply_eq_spatialPart, spatialPart_basis_sum_inr i j]
  simp [Finsupp.single_apply]
  congr 1
  exact Eq.propIntro (fun a => id (Eq.symm a)) fun a => id (Eq.symm a)


-- @@ L376-380 verbatim
/-!

## The Temporal component

-/


-- @@ L382-384 verbatim
/-- Extract time component from a Lorentz vector -/
abbrev timeComponent {d : ℕ} (v : Vector d) : ℝ :=
  v (Sum.inl 0)


-- @@ L386-387 verbatim
lemma timeComponent_basis_sum_inr {d : ℕ} (i : Fin d) :
    timeComponent (basis (Sum.inr i)) = 0 := by simp


-- @@ L389-390 verbatim
lemma timeComponent_basis_sum_inl {d : ℕ} :
    timeComponent (d := d) (basis (Sum.inl 0)) = 1 := by simp


-- @@ L392-397 verbatim
/-- The temporal part of a Lorentz vector as a continuous linear map. -/
def temporalCLM (d : ℕ) : Vector d →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun v => v (Sum.inl 0)
    map_add' := by simp
    map_smul' := by simp}


-- @@ L399-400 verbatim
lemma temporalCLM_apply_eq_timeComponent {d : ℕ} (v : Vector d) :
    temporalCLM d v = timeComponent v := rfl


-- @@ L402-405 verbatim
@[simp]
lemma temporalCLM_basis_sum_inr {d : ℕ} (i : Fin d) :
    temporalCLM d (basis (Sum.inr i)) = 0 := by
  simp [temporalCLM_apply_eq_timeComponent, basis_apply]


-- @@ L407-410 verbatim
@[simp]
lemma temporalCLM_basis_sum_inl {d : ℕ} :
    temporalCLM d (basis (Sum.inl 0)) = 1 := by
  simp [temporalCLM_apply_eq_timeComponent, basis_apply]


-- @@ L412-417 verbatim
/-- The continuous linear map corresponding to the creation of a
  Lorentz Vector with only a non-zero temporal component. -/
def ofTemporalComponent {d : ℕ} : ℝ →L[ℝ] Vector d where
  toFun xt := xt • basis (Sum.inl 0)
  map_add' := by simp [add_smul]
  map_smul' := by simp [smul_smul]


-- @@ L419-426 verbatim
/-- The continuous linear map corresponding to the creation of a
  Lorentz Vector with only non-zero spatial components. -/
def ofSpatialComponent {d : ℕ} : EuclideanSpace ℝ (Fin d) →L[ℝ] Vector d where
  toFun xs := ∑ i, xs i • basis (Sum.inr i)
  map_add' xs ys := by
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' c xs := by
    simp [smul_smul, Finset.smul_sum]


-- @@ L428-432 verbatim
/-!

## Smoothness

-/


-- @@ L434-436 verbatim
open Manifold in
/-- The structure of a smooth manifold on Vector . -/
def asSmoothManifold (d : ℕ) : ModelWithCorners ℝ (Vector d) (Vector d) := 𝓘(ℝ, Vector d)


-- @@ L438-442 verbatim
/-!

## Properties of the inner product (note not the Minkowski product)

-/

-- @@ L443-443 verbatim
open InnerProductSpace


-- @@ L445-447 verbatim
lemma basis_inner {d : ℕ} (μ : Fin 1 ⊕ Fin d) (p : Lorentz.Vector d) :
    ⟪Lorentz.Vector.basis μ, p⟫_ℝ = p μ := by
  simp [inner_eq_sum]


-- @@ L449-451 verbatim
lemma inner_basis {d : ℕ} (p : Lorentz.Vector d) (μ : Fin 1 ⊕ Fin d) :
    ⟪p, Lorentz.Vector.basis μ⟫_ℝ = p μ := by
  simp [inner_eq_sum]


-- @@ L453-453 verbatim
end Vector


-- @@ L455-455 verbatim
end Lorentz
