/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.SpaceAndTime.TimeAndSpace.ConstantTimeDist
public import Physlib.Mathematics.VariationalCalculus.HasVarAdjDeriv
public import Physlib.SpaceAndTime.Space.DistOfFunction
public import Physlib.SpaceAndTime.SpaceTime.TimeSlice


-- @@ L13-41 verbatim
/-!

# The Electromagnetic Potential

## i. Overview

The electromagnetic potential `A^μ` is the fundamental objects in
electromagnetism. Mathematically it is related to a connection
on a `U(1)`-bundle.

We define the electromagnetic potential as a distribution from
spacetime to contravariant Lorentz vectors.

## ii. Key results

- `DistElectromagneticPotential` : the type of electromagnetic potentials as distributions.

## iii. Table of contents

- A. The electromagnetic potential as a distribution
  - A.1. Constructors
  - A.2. The derivative of the electromagnetic potential as a distribution
  - A.3. The derivative in terms of the basis

## iv. References

* https://quantummechanics.ucsd.edu/ph130a/130_notes/node452.html. [ref: ucsd_ph130a_node452]
* https://ph.qmul.ac.uk/sites/default/files/EMT10new.pdf. [ref: qmul_emt10_notes]
-/


-- @@ L43-43 verbatim
@[expose] public section


-- @@ L45-45 verbatim
namespace Electromagnetism

-- @@ L46-46 verbatim
open Module realLorentzTensor

-- @@ L47-47 verbatim
open TensorSpecies

-- @@ L48-48 verbatim
open Tensor


-- @@ L50-54 verbatim
/-!

## A. The electromagnetic potential as a distribution

-/


-- @@ L56-58 expanded
/-- The electromagnetic potential as a distribution and as a tensor `A^μ`. -/
noncomputable abbrev DistElectromagneticPotential (d : ℕ := 3) :=
  Distribution ℝ (SpaceTime d) (Lorentz.Vector d)


-- @@ L60-60 verbatim
namespace DistElectromagneticPotential

-- @@ L61-61 verbatim
open TensorSpecies

-- @@ L62-62 verbatim
open Tensor

-- @@ L63-63 verbatim
open SpaceTime

-- @@ L64-64 verbatim
open TensorProduct

-- @@ L65-65 verbatim
open minkowskiMatrix SchwartzMap

-- @@ L66-66 verbatim
attribute [-simp] Fintype.sum_sum_type

-- @@ L67-67 verbatim
attribute [-simp] Nat.succ_eq_add_one


-- @@ L69-73 verbatim
/-!

### A.1. Constructors

-/


-- @@ L75-87 expanded
/-- The creation of an electromagnetic potential from a scalar potential. -/
noncomputable def ofScalarPotential {d} (c : SpeedOfLight) :
    (Distribution ℝ (Time × Space d) ℝ) →ₗ[ℝ] DistElectromagneticPotential d
    where
  toFun φ := Lorentz.Vector.ofTemporalComponent ∘L (distTimeSlice c).symm (((1 : ℝ) / c.val) • φ)
  map_add' φ₁
    φ₂ := by
    ext ε
    simp
  map_smul' r
    φ := by
    ext ε
    simp only [one_div, map_smul, ContinuousLinearMap.comp_smulₛₗ, map_inv₀, RingHom.id_apply,
      FunLike.coe_smul, ContinuousLinearMap.coe_comp, Pi.smul_apply, Function.comp_apply]
    rw [smul_comm]


-- @@ L89-92 expanded
/-- The creation of an electromagnetic potential from a static scalar potential. -/
noncomputable def ofStaticScalarPotential {d} (c : SpeedOfLight) :
    (Distribution ℝ (Space d) ℝ) →ₗ[ℝ] DistElectromagneticPotential d :=
  ofScalarPotential c ∘ₗ Space.constantTime


-- @@ L94-102 verbatim
/-- The creation of an electromagnetic potential from a static scalar-potential function.

If the function is distribution-bounded, it is first promoted to a distribution using
`Space.distOfFunction`. Otherwise the constructor returns zero. -/
noncomputable def ofStaticScalarPotentialFunction {d} (c : SpeedOfLight)
    (φ : Space d → ℝ) : DistElectromagneticPotential d := by
  classical
  exact if hφ : Space.IsDistBounded φ then
    ofStaticScalarPotential c (Space.distOfFunction φ hφ) else 0


-- @@ L104-110 verbatim
@[simp]
lemma ofStaticScalarPotentialFunction_of_isDistBounded {d} (c : SpeedOfLight)
    (φ : Space d → ℝ) (hφ : Space.IsDistBounded φ) :
    ofStaticScalarPotentialFunction c φ =
      ofStaticScalarPotential c (Space.distOfFunction φ hφ) := by
  classical
  simp [ofStaticScalarPotentialFunction, hφ]


-- @@ L112-117 verbatim
@[simp]
lemma ofStaticScalarPotentialFunction_eq_zero_of_not_isDistBounded {d}
    (c : SpeedOfLight) (φ : Space d → ℝ) (hφ : ¬ Space.IsDistBounded φ) :
    ofStaticScalarPotentialFunction c φ = 0 := by
  classical
  simp [ofStaticScalarPotentialFunction, hφ]


-- @@ L119-129 expanded
/-- The creation of an electromagnetic potential from a vector potential. -/
noncomputable def ofVectorPotential {d} (c : SpeedOfLight) :
    (Distribution ℝ (Time × Space d) (EuclideanSpace ℝ (Fin d))) →ₗ[ℝ]
      DistElectromagneticPotential d
    where
  toFun A := (distTimeSlice c).symm (Lorentz.Vector.ofSpatialComponent ∘L A)
  map_add' A₁
    A₂ := by
    ext ε
    simp
  map_smul' r
    A := by
    ext ε
    simp


-- @@ L131-134 expanded
/-- The creation of an electromagnetic potential from a static vector potential. -/
noncomputable def ofStaticVectorPotential {d} (c : SpeedOfLight) :
    (Distribution ℝ (Space d) (EuclideanSpace ℝ (Fin d))) →ₗ[ℝ] DistElectromagneticPotential d :=
  ofVectorPotential c ∘ₗ Space.constantTime


-- @@ L136-137 verbatim
TODO "Add a constructor for DistElectromagneticPotential from electric and
  magnetic fields."


-- @@ L139-143 verbatim
/-!

### A.2. The derivative of the electromagnetic potential as a distribution

-/


-- @@ L145-157 verbatim
lemma distTensorDeriv_eq_sum_sum {d} (A : DistElectromagneticPotential d)
    (ε : 𝓢(SpaceTime d, ℝ)) :
    distTensorDeriv A ε =∑ μ, ∑ ν, (SpaceTime.distDeriv μ A ε ν) •
      Lorentz.CoVector.basis μ ⊗ₜ[ℝ] Lorentz.Vector.basis ν := by
  simp [distTensorDeriv_apply]
  congr
  funext μ
  conv_lhs => rw [← Lorentz.Vector.basis.sum_repr (SpaceTime.distDeriv μ A ε)]
  rw [tmul_sum]
  congr
  funext ν
  simp
  rfl


-- @@ L159-163 verbatim
/-!

### A.3. The derivative in terms of the basis

-/


-- @@ L165-183 verbatim
@[simp]
lemma distTensorDeriv_basis_repr_apply {d} {μν : (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)}
    (A : DistElectromagneticPotential d)
    (ε : 𝓢(SpaceTime d, ℝ)) :
    (Lorentz.CoVector.basis.tensorProduct Lorentz.Vector.basis).repr (distTensorDeriv A ε) μν =
    distDeriv μν.1 A ε μν.2 := by
  match μν with
  | (μ, ν) =>
  rw [distTensorDeriv_eq_sum_sum]
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul, Finset.sum_apply,
    Pi.smul_apply, Basis.tensorProduct_repr_tmul_apply, Basis.repr_self, smul_eq_mul]
  rw [Finset.sum_eq_single μ, Finset.sum_eq_single ν]
  · simp
  · intro μ' _ h
    simp [h]
  · simp
  · intro ν' _ h
    simp [h]
  · simp


-- @@ L185-207 verbatim
lemma toTensor_distTensorDeriv_basis_repr_apply {d} (A : DistElectromagneticPotential d)
    (ε : 𝓢(SpaceTime d, ℝ)) (b : ComponentIdx (S := realLorentzTensor d)
      (Fin.append ![Color.down] ![Color.up])) :
    (Tensor.basis _).repr (Tensorial.toTensor (distTensorDeriv A ε)) b =
    distDeriv (b 0) A ε (b 1) := by
  rw [Tensorial.basis_toTensor_apply]
  rw [Tensorial.basis_map_prod]
  simp only [Nat.reduceSucc, Nat.reduceAdd, Basis.repr_reindex, Finsupp.mapDomain_equiv_apply,
    Equiv.symm_symm, Fin.isValue]
  rw [Lorentz.Vector.tensor_basis_map_eq_basis_reindex,
    Lorentz.CoVector.tensor_basis_map_eq_basis_reindex]
  have hb : (((Lorentz.CoVector.basis (d := d)).reindex
      Lorentz.CoVector.indexEquiv.symm).tensorProduct
      (Lorentz.Vector.basis.reindex Lorentz.Vector.indexEquiv.symm)) =
      ((Lorentz.CoVector.basis (d := d)).tensorProduct (Lorentz.Vector.basis (d := d))).reindex
      (Lorentz.CoVector.indexEquiv.symm.prodCongr Lorentz.Vector.indexEquiv.symm) := by
    ext b
    match b with
    | ⟨i, j⟩ =>
    simp
  rw [hb]
  rw [Module.Basis.repr_reindex_apply, distTensorDeriv_basis_repr_apply]
  rfl


-- @@ L209-209 verbatim
end DistElectromagneticPotential


-- @@ L211-211 verbatim
end Electromagnetism
