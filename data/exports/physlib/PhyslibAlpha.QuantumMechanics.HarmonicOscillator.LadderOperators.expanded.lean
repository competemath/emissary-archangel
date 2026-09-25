/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges, Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.HarmonicOscillator.Basic
public import Physlib.QuantumMechanics.Operators.Commutation
public import PhyslibAlpha.Mathematics.LadderSystem.SymmetricPower

-- @@ L11-58 verbatim
/-!

# Ladder operators

## i. Overview

The raising/lowering (creation/annihilation) operators of the `d`-dimensional quantum harmonic
oscillator, and the number operators built from them, at the level of Schwartz maps `𝓢(Space d, ℂ)`
-- the same level `Position.lean`/`Momentum.lean`/`AngularMomentum.lean` define `𝐱`, `𝐩`, `𝐋` at.

Not `†`: the creation operator is named `creationCLM`, not notated with `†`, since `†` is reserved
elsewhere (`Operators/Unbounded.lean`) for a *proved* formal adjoint, and `annihilationCLM`/
`creationCLM` being mutually adjoint is exactly the TODO left open below -- these operators are
defined only at the Schwartz level (as `𝐱`, `𝐩`, `𝐋` are in `Operators/`), not yet promoted to
(partial) operators on `Q.HS` itself.

The canonical commutation relations in section A define the `LadderSystem` instance
`toLadderSystem`. Section B obtains the number operator and its commutation relations from the
general `LadderSystem` API.

## ii. Key results

Definitions:
- `annihilationCLM` : the annihilation operator for mode `i`,
    `𝐚ᵢ ≔ (√2)⁻¹(ξᵢ⁻¹𝐱ᵢ + i(ξᵢ/ℏ)𝐩ᵢ)`.
- `creationCLM` : the creation operator for mode `i`, `𝐚ᵢ⁺ ≔ (√2)⁻¹(ξᵢ⁻¹𝐱ᵢ - i(ξᵢ/ℏ)𝐩ᵢ)`.
- `toLadderSystem` : `annihilationCLM`/`creationCLM` bundled as a genuine
    `Physlib.Mathematics.LadderSystem` instance.
- `numberCLM` : the number operator for mode `i`, `𝐍ᵢ ≔ 𝐚ᵢ⁺∘𝐚ᵢ`, via `toLadderSystem.N`.

Theorems:
- `annihilationCLM_comm_creationCLM` : the canonical commutation relations, `[𝐚ᵢ, 𝐚ⱼ⁺] = δᵢⱼ`.
- `numberCLM_comm_numberCLM` : the number operators commute among themselves, `[𝐍ᵢ, 𝐍ⱼ] = 0`.
- `numberCLM_comm_annihilationCLM`, `numberCLM_comm_creationCLM` : `[𝐍ᵢ, 𝐚ⱼ] = -δᵢⱼ𝐚ᵢ` and
    `[𝐍ᵢ, 𝐚ⱼ⁺] = δᵢⱼ𝐚ᵢ⁺`.

## iii. Table of contents

- A. Ladder operators
  - A.1. Canonical commutation relations
- B. Number operators
  - B.1. Commutation relations
- C. Hamiltonian

## iv. References

* None.
-/


-- @@ L60-60 verbatim
@[expose] public section


-- @@ L62-63 verbatim
TODO "Prove that the raising/lowering operators are mutually adjoint with respect to the L² inner
  product (tag as simp?)."


-- @@ L65-67 verbatim
TODO "Promote `annihilationCLM`/`creationCLM`/`numberCLM` from continuous linear maps on
  `𝓢(Space d, ℂ)` to (partial) operators on `Q.HS`, as `Position.lean`/`Momentum.lean` do for
  `𝐱`/`𝐩`."


-- @@ L69-70 verbatim
TODO "Prove that the number operators are symmetric/self-adjoint (needs
  annihilationCLM/creationCLM's adjointness, promoted to `Q.HS`)."


-- @@ L72-72 verbatim
TODO "Define a Hamiltonian in terms of the number operators."


-- @@ L74-74 verbatim
TODO "Prove the commutation relations between the Hamiltonian and ladder/number operators."


-- @@ L76-77 verbatim
TODO "Relate the 'number operator' Hamiltonian to the 'K + T' Hamiltonian
  (=/≤/≥ depending on their domains)."


-- @@ L79-79 verbatim
TODO "Prove that the two Hamiltonians define the same quantum system."


-- @@ L81-81 verbatim
namespace QuantumMechanics

-- @@ L82-82 verbatim
namespace HarmonicOscillator

-- @@ L83-83 verbatim
noncomputable section

-- @@ L84-84 verbatim
open Complex Constants

-- @@ L85-85 verbatim
open KroneckerDelta

-- @@ L86-86 verbatim
open ContinuousLinearMap SchwartzMap


-- @@ L88-88 verbatim
variable {d : ℕ} (Q : HarmonicOscillator d) (i j : Fin d)


-- @@ L90-90 verbatim
attribute [local instance 100] LieRing.ofAssociativeRing


-- @@ L92-96 verbatim
/-!

## A. Ladder operators

-/


-- @@ L98-102 expanded
/-- The annihilation operator for mode `i`, `𝐚ᵢ ≔ (√2)⁻¹(ξᵢ⁻¹𝐱ᵢ + i(ξᵢ/ℏ)𝐩ᵢ)`, where `ξᵢ` is the
characteristic length of that mode (`HarmonicOscillator.ξ`). -/
def annihilationCLM (Q : HarmonicOscillator d) (i : Fin d) : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  (√2 : ℂ)⁻¹ • ((Q.ξ i : ℂ)⁻¹ • positionCLM i + (I * Q.ξ i / ℏ) • momentumCLM i)


-- @@ L104-106 expanded
lemma annihilationCLM_apply_fun (Q : HarmonicOscillator d) (i : Fin d) (ψ : 𝓢(Space d, ℂ)) :
    Q.annihilationCLM i ψ =
      (√2 : ℂ)⁻¹ • ((Q.ξ i : ℂ)⁻¹ • positionCLM i ψ + (I * Q.ξ i / ℏ) • momentumCLM i ψ) :=
  rfl


-- @@ L108-111 expanded
/-- The creation operator for mode `i`, `𝐚ᵢ⁺ ≔ (√2)⁻¹(ξᵢ⁻¹𝐱ᵢ - i(ξᵢ/ℏ)𝐩ᵢ)`. -/
def creationCLM (Q : HarmonicOscillator d) (i : Fin d) : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  (√2 : ℂ)⁻¹ • ((Q.ξ i : ℂ)⁻¹ • positionCLM i - (I * Q.ξ i / ℏ) • momentumCLM i)


-- @@ L113-115 expanded
lemma creationCLM_apply_fun (Q : HarmonicOscillator d) (i : Fin d) (ψ : 𝓢(Space d, ℂ)) :
    Q.creationCLM i ψ =
      (√2 : ℂ)⁻¹ • ((Q.ξ i : ℂ)⁻¹ • positionCLM i ψ - (I * Q.ξ i / ℏ) • momentumCLM i ψ) :=
  rfl


-- @@ L117-121 verbatim
/-!

### A.1. Canonical commutation relations

-/


-- @@ L123-132 expanded
/-- `[𝐚ᵢ, 𝐚ⱼ] = 0`. -/
@[simp]
theorem annihilationCLM_comm_annihilationCLM (Q : HarmonicOscillator d) (i j : Fin d) :
    (⁅Q.annihilationCLM i, Q.annihilationCLM j⁆ : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) = 0 :=
  by
  rcases eq_or_ne i j with rfl | hij
  · exact lie_self _
  · unfold annihilationCLM
    simp [smul_lie, lie_smul, add_lie, lie_add, position_commutation_position,
      position_commutation_momentum, momentum_commutation_momentum,
      ← lie_skew ((momentumCLM (d := d)) _) (positionCLM _), KroneckerDelta.symm j i,
      eq_zero_of_ne hij]


-- @@ L134-143 expanded
/-- `[𝐚ᵢ⁺, 𝐚ⱼ⁺] = 0`. -/
@[simp]
theorem creationCLM_comm_creationCLM (Q : HarmonicOscillator d) (i j : Fin d) :
    (⁅Q.creationCLM i, Q.creationCLM j⁆ : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) = 0 :=
  by
  rcases eq_or_ne i j with rfl | hij
  · exact lie_self _
  · unfold creationCLM
    simp [smul_lie, lie_smul, sub_lie, lie_sub, position_commutation_position,
      position_commutation_momentum, momentum_commutation_momentum,
      ← lie_skew ((momentumCLM (d := d)) _) (positionCLM _), KroneckerDelta.symm j i,
      eq_zero_of_ne hij]


-- @@ L145-171 expanded
/-- The canonical commutation relations for the ladder operators, `[𝐚ᵢ, 𝐚ⱼ⁺] = δᵢⱼ`. -/
theorem annihilationCLM_comm_creationCLM (Q : HarmonicOscillator d) (i j : Fin d) :
    (⁅Q.annihilationCLM i, Q.creationCLM j⁆ : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) =
      (kroneckerDelta i j : ℂ) • (ContinuousLinearMap.id ℂ 𝓢(Space d, ℂ)) :=
  by
  have hℏ : (ℏ : ℂ) ≠ 0 := by exact_mod_cast Constants.ℏ_ne_zero
  have hsqrt2 : ((√2 : ℝ) : ℂ) ^ 2 = 2 :=
    by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rcases eq_or_ne i j with rfl | hij
  · have hξ : (Q.ξ i : ℂ) ≠ 0 := by exact_mod_cast Q.ξ_ne_zero i
    rw [eq_one_of_same, Nat.cast_one, one_smul]
    unfold annihilationCLM creationCLM
    simp only [smul_lie, lie_smul, add_lie, lie_sub, position_commutation_position,
      position_commutation_momentum, momentum_commutation_momentum,
      ← lie_skew ((momentumCLM (d := d)) _) (positionCLM _), smul_zero, add_zero, smul_neg,
      smul_smul]
    ext ψ x
    simp only [sub_apply, add_apply, neg_apply, zero_apply, smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, eq_one_of_same]
    field_simp
    ring_nf
    rw [Complex.I_sq, hsqrt2]
    ring
  · rw [eq_zero_of_ne hij, Nat.cast_zero, zero_smul]
    unfold annihilationCLM creationCLM
    simp [smul_lie, lie_smul, add_lie, lie_sub, position_commutation_position,
      position_commutation_momentum, momentum_commutation_momentum,
      ← lie_skew ((momentumCLM (d := d)) _) (positionCLM _), KroneckerDelta.symm j i,
      eq_zero_of_ne hij]


-- @@ L173-177 verbatim
/-!

## B. Number operators

-/


-- @@ L179-203 verbatim
/-- The annihilation and creation operators on Schwartz space, bundled as a `LadderSystem`.
The number operator and its commutation relations below are obtained from this structure. -/
def toLadderSystem (Q : HarmonicOscillator d) : LadderSystem ℂ (𝓢(Space d, ℂ)) d where
  a i := (Q.annihilationCLM i).toLinearMap
  ac i := (Q.creationCLM i).toLinearMap
  comm_a_ac i j := by
    have h := Q.annihilationCLM_comm_creationCLM i j
    apply_fun ContinuousLinearMap.toLinearMap at h
    rcases eq_or_ne i j with rfl | hij
    · simpa [LieRing.of_associative_ring_bracket, ContinuousLinearMap.mul_def,
        ContinuousLinearMap.coe_comp, Module.End.mul_eq_comp, Module.End.one_eq_id,
        ContinuousLinearMap.one_def] using h
    · simpa [LieRing.of_associative_ring_bracket, ContinuousLinearMap.mul_def,
        ContinuousLinearMap.coe_comp, Module.End.mul_eq_comp, hij,
        KroneckerDelta.eq_zero_of_ne hij] using h
  comm_a_a i j := by
    have h := Q.annihilationCLM_comm_annihilationCLM i j
    apply_fun ContinuousLinearMap.toLinearMap at h
    simpa [LieRing.of_associative_ring_bracket, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.coe_comp, Module.End.mul_eq_comp] using h
  comm_ac_ac i j := by
    have h := Q.creationCLM_comm_creationCLM i j
    apply_fun ContinuousLinearMap.toLinearMap at h
    simpa [LieRing.of_associative_ring_bracket, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.coe_comp, Module.End.mul_eq_comp] using h


-- @@ L205-207 verbatim
/-- The number operator for mode `i`, `𝐍ᵢ ≔ 𝐚ᵢ⁺ ∘ 𝐚ᵢ`, via `toLadderSystem.N`. -/
def numberCLM (Q : HarmonicOscillator d) (i : Fin d) :
    𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) := Q.creationCLM i ∘L Q.annihilationCLM i


-- @@ L209-210 verbatim
theorem toLadderSystem_N_toLinearMap (Q : HarmonicOscillator d) (i : Fin d) :
    Q.toLadderSystem.N i = (Q.numberCLM i).toLinearMap := rfl


-- @@ L212-216 verbatim
/-!

### B.1. Commutation relations

-/


-- @@ L218-227 expanded
/-- `[𝐍ᵢ, 𝐚ⱼ] = -δᵢⱼ𝐚ᵢ`, from the general `LadderSystem.lie_N_a` applied to `toLadderSystem`. -/
theorem numberCLM_comm_annihilationCLM (Q : HarmonicOscillator d) (i j : Fin d) :
    (⁅Q.numberCLM i, Q.annihilationCLM j⁆ : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) =
      (-kroneckerDelta i j : ℂ) • Q.annihilationCLM i :=
  by
  have h := Q.toLadderSystem.lie_N_a i j
  rw [toLadderSystem_N_toLinearMap] at h
  refine ContinuousLinearMap.ext fun ψ => ?_
  have hx := LinearMap.congr_fun h ψ
  simpa [toLadderSystem, LieRing.of_associative_ring_bracket, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.coe_comp, Module.End.mul_apply] using hx


-- @@ L229-234 expanded
/-- `[𝐍ᵢ, 𝐚ⱼ⁺] = δᵢⱼ𝐚ᵢ⁺`, from the general `LadderSystem.lie_N_ac` applied to `toLadderSystem`. -/
theorem numberCLM_comm_creationCLM (Q : HarmonicOscillator d) (i j : Fin d) :
    (⁅Q.numberCLM i, Q.creationCLM j⁆ : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) =
      (kroneckerDelta i j : ℂ) • Q.creationCLM i :=
  by
  rw [numberCLM, leibniz_lie, creationCLM_comm_creationCLM, zero_comp, add_zero,
    annihilationCLM_comm_creationCLM, comp_smul, comp_id]


-- @@ L236-247 verbatim
/-- `[𝐍ᵢ, 𝐍ⱼ] = 0`, from the general `LadderSystem.lie_N_N` applied to `toLadderSystem`. -/
@[simp]
theorem numberCLM_comm_numberCLM (Q : HarmonicOscillator d) (i j : Fin d) :
    (⁅Q.numberCLM i, Q.numberCLM j⁆ : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) = 0 := by
  rcases eq_or_ne i j with rfl | hij
  · exact lie_self _
  · show (⁅Q.creationCLM i ∘L Q.annihilationCLM i, Q.numberCLM j⁆ :
        𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) = _
    rw [leibniz_lie, ← lie_skew (Q.annihilationCLM i) (Q.numberCLM j),
      numberCLM_comm_annihilationCLM, ← lie_skew (Q.creationCLM i) (Q.numberCLM j),
      numberCLM_comm_creationCLM, KroneckerDelta.symm j i, eq_zero_of_ne hij]
    simp


-- @@ L249-249 verbatim
end

-- @@ L250-250 verbatim
end HarmonicOscillator

-- @@ L251-251 verbatim
end QuantumMechanics
