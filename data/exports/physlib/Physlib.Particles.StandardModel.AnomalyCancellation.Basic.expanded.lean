/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.AnomalyCancellation.Basic
public import Mathlib.Tactic.LinearCombination

-- @@ L10-15 verbatim
/-!
# Anomaly cancellation conditions for the n-family SM.

We define the ACC system for the Standard Model with`n`-families and no RHN.

-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
open Nat

-- @@ L20-20 verbatim
open BigOperators


-- @@ L22-24 verbatim
/-- Associate to each (including RHN) SM fermion a set of charges-/
@[simps!]
def SMCharges (n : ℕ) : ACCSystemCharges := ⟨5 * n⟩


-- @@ L26-28 verbatim
/-- The vector space associated with a single species of fermions. -/
@[simps!]
def SMSpecies (n : ℕ) : ACCSystemCharges := ⟨n⟩


-- @@ L30-30 verbatim
namespace SMCharges


-- @@ L32-32 verbatim
variable {n : ℕ}


-- @@ L34-40 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma sum_SMSpecies_numberCharges_one {M} [AddCommMonoid M]
    (f : Fin (SMSpecies 1).numberCharges → M) :
    ∑ i, f i = f ⟨0, by simp⟩ := by
  change ∑ (i : Fin 1), f i = _
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton]
  rfl


-- @@ L42-47 verbatim
/-- An equivalence between the set `(SMCharges n).charges` and the set
  `(Fin 5 → Fin n → ℚ)`. -/
@[simps!]
def toSpeciesEquiv : (SMCharges n).Charges ≃ (Fin 5 → Fin (SMSpecies n).numberCharges → ℚ) :=
  ((Equiv.curry _ _ _).symm.trans ((@finProdFinEquiv 5
    (SMSpecies n).numberCharges).arrowCongr (Equiv.refl ℚ))).symm


-- @@ L49-54 verbatim
/-- For a given `i ∈ Fin 5`, the projection of a charge onto that species. -/
@[simps!]
def toSpecies (i : Fin 5) : (SMCharges n).Charges →ₗ[ℚ] (SMSpecies n).Charges where
  toFun S := toSpeciesEquiv S i
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl


-- @@ L56-57 verbatim
lemma toSpecies_apply_eq (i : Fin 5) (S : (SMCharges n).Charges) :
    toSpecies i S = fun j => toSpeciesEquiv S i j := by rfl


-- @@ L59-63 verbatim
lemma charges_eq_toSpecies_eq (S T : (SMCharges n).Charges) :
    S = T ↔ ∀ i, toSpecies i S = toSpecies i T := by
  refine Iff.intro (fun a i => congrArg (⇑(toSpecies i)) a) (fun h => ?_)
  apply toSpeciesEquiv.injective
  exact (Set.eqOn_univ (toSpeciesEquiv S) (toSpeciesEquiv T)).mp fun ⦃x⦄ _ => h x


-- @@ L65-69 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma toSMSpecies_toSpecies_inv (i : Fin 5) (f : Fin 5 → Fin n → ℚ) :
    (toSpecies i) (toSpeciesEquiv.symm f) = f i := by
  change (toSpeciesEquiv ∘ toSpeciesEquiv.symm) _ i= f i
  simp


-- @@ L71-72 verbatim
/-- The `Q` charges as a map `Fin n → ℚ`. -/
abbrev Q := @toSpecies n 0


-- @@ L74-75 verbatim
/-- The `U` charges as a map `Fin n → ℚ`. -/
abbrev U := @toSpecies n 1


-- @@ L77-78 verbatim
/-- The `D` charges as a map `Fin n → ℚ`. -/
abbrev D := @toSpecies n 2


-- @@ L80-81 verbatim
/-- The `L` charges as a map `Fin n → ℚ`. -/
abbrev L := @toSpecies n 3


-- @@ L83-84 verbatim
/-- The `E` charges as a map `Fin n → ℚ`. -/
abbrev E := @toSpecies n 4


-- @@ L86-86 verbatim
end SMCharges


-- @@ L88-88 verbatim
namespace SMACCs


-- @@ L90-90 verbatim
open SMCharges


-- @@ L92-92 verbatim
variable {n : ℕ}


-- @@ L94-111 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The gravitational anomaly equation. -/
def accGrav : (SMCharges n).Charges →ₗ[ℚ] ℚ where
  toFun S := ∑ i, (6 * Q S i + 3 * U S i + 3 * D S i + 2 * L S i + E S i)
  map_add' S T := by
    repeat rw [map_add]
    simp only [ACCSystemCharges.chargesAddCommMonoid_add, toSpecies_apply,
      Fin.isValue, mul_add]
    repeat rw [Finset.sum_add_distrib]
    ring
  map_smul' a S := by
    repeat rw [map_smul]
    simp only [HSMul.hSMul, SMul.smul, toSpecies_apply, Fin.isValue,
      eq_ratCast, Rat.cast_eq_id, id_eq]
    repeat rw [Finset.sum_add_distrib]
    repeat rw [← Finset.mul_sum]
    --rw [show Rat.cast a = a from rfl]
    ring


-- @@ L113-122 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- Extensionality lemma for `accGrav`. -/
lemma accGrav_ext {S T : (SMCharges n).Charges}
    (hj : ∀ (j : Fin 5), ∑ i, (toSpecies j) S i = ∑ i, (toSpecies j) T i) :
    accGrav S = accGrav T := by
  simp only [accGrav, toSpecies_apply, Fin.isValue, LinearMap.coe_mk,
    AddHom.coe_mk]
  repeat rw [Finset.sum_add_distrib]
  repeat rw [← Finset.mul_sum]
  simp_all


-- @@ L124-141 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The `SU(2)` anomaly equation. -/
def accSU2 : (SMCharges n).Charges →ₗ[ℚ] ℚ where
  toFun S := ∑ i, (3 * Q S i + L S i)
  map_add' S T := by
    repeat rw [map_add]
    simp only [ACCSystemCharges.chargesAddCommMonoid_add, toSpecies_apply,
      Fin.isValue, mul_add]
    repeat rw [Finset.sum_add_distrib]
    ring
  map_smul' a S := by
    repeat rw [map_smul]
    simp only [ HSMul.hSMul, SMul.smul, toSpecies_apply, Fin.isValue,
      eq_ratCast, Rat.cast_eq_id, id_eq]
    repeat rw [Finset.sum_add_distrib]
    repeat rw [← Finset.mul_sum]
    --rw [show Rat.cast a = a from rfl]
    ring


-- @@ L143-152 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- Extensionality lemma for `accSU2`. -/
lemma accSU2_ext {S T : (SMCharges n).Charges}
    (hj : ∀ (j : Fin 5), ∑ i, (toSpecies j) S i = ∑ i, (toSpecies j) T i) :
    accSU2 S = accSU2 T := by
  simp only [accSU2, toSpecies_apply, Fin.isValue, LinearMap.coe_mk,
    AddHom.coe_mk]
  repeat rw [Finset.sum_add_distrib]
  repeat rw [← Finset.mul_sum]
  exact Mathlib.Tactic.LinearCombination.add_eq_eq (congrArg (HMul.hMul 3) (hj 0)) (hj 3)


-- @@ L154-171 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The `SU(3)` anomaly equations. -/
def accSU3 : (SMCharges n).Charges →ₗ[ℚ] ℚ where
  toFun S := ∑ i, (2 * Q S i + U S i + D S i)
  map_add' S T := by
    repeat rw [map_add]
    simp only [ACCSystemCharges.chargesAddCommMonoid_add, toSpecies_apply,
      Fin.isValue, mul_add]
    repeat rw [Finset.sum_add_distrib]
    ring
  map_smul' a S := by
    repeat rw [map_smul]
    simp only [HSMul.hSMul, SMul.smul, toSpecies_apply, Fin.isValue,
      eq_ratCast, Rat.cast_eq_id, id_eq]
    repeat rw [Finset.sum_add_distrib]
    repeat rw [← Finset.mul_sum]
    --rw [show Rat.cast a = a from rfl]
    ring


-- @@ L173-182 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- Extensionality lemma for `accSU3`. -/
lemma accSU3_ext {S T : (SMCharges n).Charges}
    (hj : ∀ (j : Fin 5), ∑ i, (toSpecies j) S i = ∑ i, (toSpecies j) T i) :
    accSU3 S = accSU3 T := by
  simp only [accSU3, toSpecies_apply, Fin.isValue, LinearMap.coe_mk,
    AddHom.coe_mk]
  repeat rw [Finset.sum_add_distrib]
  repeat rw [← Finset.mul_sum]
  simp_all


-- @@ L184-201 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The `Y²` anomaly equation. -/
def accYY : (SMCharges n).Charges →ₗ[ℚ] ℚ where
  toFun S := ∑ i, (Q S i + 8 * U S i + 2 * D S i + 3 * L S i
    + 6 * E S i)
  map_add' S T := by
    repeat rw [map_add]
    simp only [ACCSystemCharges.chargesAddCommMonoid_add, toSpecies_apply,
      Fin.isValue, mul_add]
    repeat rw [Finset.sum_add_distrib]
    ring
  map_smul' a S := by
    repeat rw [map_smul]
    simp only [HSMul.hSMul, SMul.smul, toSpecies_apply, Fin.isValue,
      eq_ratCast, Rat.cast_eq_id, id_eq]
    repeat rw [Finset.sum_add_distrib]
    repeat rw [← Finset.mul_sum]
    ring


-- @@ L203-212 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- Extensionality lemma for `accYY`. -/
lemma accYY_ext {S T : (SMCharges n).Charges}
    (hj : ∀ (j : Fin 5), ∑ i, (toSpecies j) S i = ∑ i, (toSpecies j) T i) :
    accYY S = accYY T := by
  simp only [accYY, toSpecies_apply, Fin.isValue, LinearMap.coe_mk,
    AddHom.coe_mk]
  repeat rw [Finset.sum_add_distrib]
  repeat rw [← Finset.mul_sum]
  simp_all


-- @@ L214-247 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The quadratic bilinear map. -/
@[simps!]
def quadBiLin : BiLinearSymm (SMCharges n).Charges := BiLinearSymm.mk₂
  (fun S => ∑ i, (Q S.1 i * Q S.2 i +
    - 2 * (U S.1 i * U S.2 i) +
    D S.1 i * D S.2 i +
    (- 1) * (L S.1 i * L S.2 i) +
    E S.1 i * E S.2 i))
  (by
    intro a S T
    simp only
    rw [Finset.mul_sum]
    apply Fintype.sum_congr
    intro i
    repeat rw [map_smul]
    simp only [HSMul.hSMul, SMul.smul, toSpecies_apply, Fin.isValue, neg_mul, one_mul]
    ring)
  (by
    intro S1 S2 T
    simp only
    rw [← Finset.sum_add_distrib]
    apply Fintype.sum_congr
    intro i
    repeat rw [map_add]
    simp only [ACCSystemCharges.chargesAddCommMonoid_add, toSpecies_apply, Fin.isValue, neg_mul,
      one_mul]
    ring)
  (by
    intro S T
    simp only [toSpecies_apply, Fin.isValue, neg_mul, one_mul]
    apply Fintype.sum_congr
    intro i
    ring)


-- @@ L249-252 verbatim
/-- The quadratic anomaly cancellation condition. -/
@[simp]
def accQuad : HomogeneousQuadratic (SMCharges n).Charges :=
  (@quadBiLin n).toHomogeneousQuad


-- @@ L254-265 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- Extensionality lemma for `accQuad`. -/
lemma accQuad_ext {S T : (SMCharges n).Charges}
    (h : ∀ j, ∑ i, ((fun a => a^2) ∘ toSpecies j S) i =
    ∑ i, ((fun a => a^2) ∘ toSpecies j T) i) :
    accQuad S = accQuad T := by
  simp only [HomogeneousQuadratic, accQuad, BiLinearSymm.toHomogeneousQuad_apply]
  simp only [quadBiLin, BiLinearSymm.mk₂_toFun_apply]
  repeat rw [Finset.sum_add_distrib]
  repeat rw [← Finset.mul_sum]
  ring_nf
  simp_all


-- @@ L267-305 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The trilinear function defining the cubic. -/
@[simps!]
def cubeTriLin : TriLinearSymm (SMCharges n).Charges := TriLinearSymm.mk₃
  (fun S => ∑ i, (6 * ((Q S.1 i) * (Q S.2.1 i) * (Q S.2.2 i))
    + 3 * ((U S.1 i) * (U S.2.1 i) * (U S.2.2 i))
    + 3 * ((D S.1 i) * (D S.2.1 i) * (D S.2.2 i))
    + 2 * ((L S.1 i) * (L S.2.1 i) * (L S.2.2 i))
    + ((E S.1 i) * (E S.2.1 i) * (E S.2.2 i))))
  (by
    intro a S T R
    simp only
    rw [Finset.mul_sum]
    apply Fintype.sum_congr
    intro i
    repeat rw [map_smul]
    simp only [HSMul.hSMul, SMul.smul, toSpecies_apply, Fin.isValue]
    ring)
  (by
    intro S T R L
    simp only
    rw [← Finset.sum_add_distrib]
    apply Fintype.sum_congr
    intro i
    repeat rw [map_add]
    simp only [ACCSystemCharges.chargesAddCommMonoid_add, toSpecies_apply, Fin.isValue]
    ring)
  (by
    intro S T L
    simp only [toSpecies_apply, Fin.isValue]
    apply Fintype.sum_congr
    intro i
    ring)
  (by
    intro S T L
    simp only [toSpecies_apply, Fin.isValue]
    apply Fintype.sum_congr
    intro i
    ring)


-- @@ L307-309 verbatim
/-- The cubic acc. -/
@[simp]
def accCube : HomogeneousCubic (SMCharges n).Charges := cubeTriLin.toCubic


-- @@ L311-322 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- Extensionality lemma for `accCube`. -/
lemma accCube_ext {S T : (SMCharges n).Charges}
    (h : ∀ j, ∑ i, ((fun a => a^3) ∘ toSpecies j S) i =
    ∑ i, ((fun a => a^3) ∘ toSpecies j T) i) :
    accCube S = accCube T := by
  simp only [HomogeneousCubic, accCube, cubeTriLin, TriLinearSymm.toCubic_apply,
    TriLinearSymm.mk₃_toFun_apply_apply]
  repeat rw [Finset.sum_add_distrib]
  repeat rw [← Finset.mul_sum]
  ring_nf
  simp_all


-- @@ L324-324 verbatim
end SMACCs
