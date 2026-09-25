/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.AnomalyCancellation.Basic

-- @@ L9-16 verbatim
/-!

# Anomaly cancellation conditions for the Standard Model with right-handed neutrinos

This directory is related to the anomaly cancellation conditions (ACCs) for the Standard Model with
right-handed neutrinos (SMν).

-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
open Nat

-- @@ L21-21 verbatim
open BigOperators


-- @@ L23-25 verbatim
/-- The vector space of charges corresponding to the SM fermions with RHN. -/
@[simps!]
def SMνCharges (n : ℕ) : ACCSystemCharges := ⟨6 * n⟩


-- @@ L27-29 verbatim
/-- The vector spaces of charges of one species of fermions in the SM. -/
@[simps!]
def SMνSpecies (n : ℕ) : ACCSystemCharges := ⟨n⟩


-- @@ L31-31 verbatim
namespace SMνCharges


-- @@ L33-33 verbatim
variable {n : ℕ}


-- @@ L35-40 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma sum_one  [AddCommMonoid M] (f : Fin (SMνSpecies 1).numberCharges → M) :
    ∑ i, f i = f ⟨0, by simp⟩ := by
  change  ∑ (i : Fin 1), f i = _
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton]
  rfl


-- @@ L42-46 verbatim
/-- An equivalence between `(SMνCharges n).charges` and `(Fin 6 → Fin n → ℚ)`
splitting the charges into species. -/
@[simps!]
def toSpeciesEquiv : (SMνCharges n).Charges ≃ (Fin 6 → Fin n → ℚ) :=
  ((Equiv.curry _ _ _).symm.trans ((@finProdFinEquiv 6 n).arrowCongr (Equiv.refl ℚ))).symm


-- @@ L48-53 verbatim
/-- Given an `i ∈ Fin 6`, the projection of charges onto a given species. -/
@[simps!]
def toSpecies (i : Fin 6) : (SMνCharges n).Charges →ₗ[ℚ] (SMνSpecies n).Charges where
  toFun S := toSpeciesEquiv S i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


-- @@ L55-60 verbatim
lemma charges_eq_toSpecies_eq (S T : (SMνCharges n).Charges) :
    S = T ↔ ∀ i, toSpecies i S = toSpecies i T := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · exact fun i => congrArg (⇑(toSpecies i)) h
  · apply toSpeciesEquiv.injective
    exact funext (fun i => h i)


-- @@ L62-65 verbatim
lemma toSMSpecies_toSpecies_inv (i : Fin 6) (f : Fin 6 → Fin n → ℚ) :
    (toSpecies i) (toSpeciesEquiv.symm f) = f i := by
  change (toSpeciesEquiv ∘ toSpeciesEquiv.symm) _ i = f i
  simp


-- @@ L67-75 verbatim
lemma toSpecies_one (S : (SMνCharges 1).Charges) (j : Fin 6) :
    toSpecies j S ⟨0, zero_lt_succ 0⟩ = S j := by
  match j with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl


-- @@ L77-78 verbatim
/-- The `Q` charges as a map `Fin n → ℚ`. -/
abbrev Q := @toSpecies n 0

-- @@ L79-80 verbatim
/-- The `U` charges as a map `Fin n → ℚ`. -/
abbrev U := @toSpecies n 1

-- @@ L81-82 verbatim
/-- The `D` charges as a map `Fin n → ℚ`. -/
abbrev D := @toSpecies n 2

-- @@ L83-84 verbatim
/-- The `L` charges as a map `Fin n → ℚ`. -/
abbrev L := @toSpecies n 3

-- @@ L85-86 verbatim
/-- The `E` charges as a map `Fin n → ℚ`. -/
abbrev E := @toSpecies n 4

-- @@ L87-88 verbatim
/-- The `N` charges as a map `Fin n → ℚ`. -/
abbrev N := @toSpecies n 5


-- @@ L90-90 verbatim
end SMνCharges


-- @@ L92-92 verbatim
namespace SMνACCs


-- @@ L94-94 verbatim
open SMνCharges


-- @@ L96-96 verbatim
variable {n : ℕ}


-- @@ L98-115 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The gravitational anomaly equation. -/
def accGrav : (SMνCharges n).Charges →ₗ[ℚ] ℚ where
  toFun S := ∑ i, (6 * Q S i + 3 * U S i + 3 * D S i + 2 * L S i + E S i + N S i)
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
    -- rw [show Rat.cast a = a from rfl]
    ring


-- @@ L117-124 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma accGrav_decomp (S : (SMνCharges n).Charges) :
    accGrav S = 6 * ∑ i, Q S i + 3 * ∑ i, U S i + 3 * ∑ i, D S i + 2 * ∑ i, L S i + ∑ i, E S i +
      ∑ i, N S i := by
  simp only [accGrav, toSpecies_apply, Fin.isValue, LinearMap.coe_mk,
    AddHom.coe_mk]
  repeat rw [Finset.sum_add_distrib]
  repeat rw [← Finset.mul_sum]


-- @@ L126-131 verbatim
/-- Extensionality lemma for `accGrav`. -/
lemma accGrav_ext {S T : (SMνCharges n).Charges}
    (hj : ∀ (j : Fin 6), ∑ i, (toSpecies j) S i = ∑ i, (toSpecies j) T i) :
    accGrav S = accGrav T := by
  rw [accGrav_decomp, accGrav_decomp]
  repeat rw [hj]


-- @@ L133-150 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The `SU(2)` anomaly equation. -/
def accSU2 : (SMνCharges n).Charges →ₗ[ℚ] ℚ where
  toFun S := ∑ i, (3 * Q S i + L S i)
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
    -- rw [show Rat.cast a = a from rfl]
    ring


-- @@ L152-158 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma accSU2_decomp (S : (SMνCharges n).Charges) :
    accSU2 S = 3 * ∑ i, Q S i + ∑ i, L S i := by
  simp only [accSU2, toSpecies_apply, Fin.isValue, LinearMap.coe_mk,
    AddHom.coe_mk]
  repeat rw [Finset.sum_add_distrib]
  repeat rw [← Finset.mul_sum]


-- @@ L160-165 verbatim
/-- Extensionality lemma for `accSU2`. -/
lemma accSU2_ext {S T : (SMνCharges n).Charges}
    (hj : ∀ (j : Fin 6), ∑ i, (toSpecies j) S i = ∑ i, (toSpecies j) T i) :
    accSU2 S = accSU2 T := by
  rw [accSU2_decomp, accSU2_decomp]
  repeat rw [hj]


-- @@ L167-184 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The `SU(3)` anomaly equations. -/
def accSU3 : (SMνCharges n).Charges →ₗ[ℚ] ℚ where
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
    -- rw [show Rat.cast a = a from rfl]
    ring


-- @@ L186-192 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma accSU3_decomp (S : (SMνCharges n).Charges) :
    accSU3 S = 2 * ∑ i, Q S i + ∑ i, U S i + ∑ i, D S i := by
  simp only [accSU3, toSpecies_apply, Fin.isValue, LinearMap.coe_mk,
    AddHom.coe_mk]
  repeat rw [Finset.sum_add_distrib]
  repeat rw [← Finset.mul_sum]


-- @@ L194-199 verbatim
/-- Extensionality lemma for `accSU3`. -/
lemma accSU3_ext {S T : (SMνCharges n).Charges}
    (hj : ∀ (j : Fin 6), ∑ i, (toSpecies j) S i = ∑ i, (toSpecies j) T i) :
    accSU3 S = accSU3 T := by
  rw [accSU3_decomp, accSU3_decomp]
  repeat rw [hj]


-- @@ L201-219 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The `Y²` anomaly equation. -/
def accYY : (SMνCharges n).Charges →ₗ[ℚ] ℚ where
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
    -- rw [show Rat.cast a = a from rfl]
    ring


-- @@ L221-227 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma accYY_decomp (S : (SMνCharges n).Charges) :
    accYY S = ∑ i, Q S i + 8 * ∑ i, U S i + 2 * ∑ i, D S i + 3 * ∑ i, L S i + 6 * ∑ i, E S i := by
  simp only [accYY, toSpecies_apply, Fin.isValue, LinearMap.coe_mk,
    AddHom.coe_mk]
  repeat rw [Finset.sum_add_distrib]
  repeat rw [← Finset.mul_sum]


-- @@ L229-234 verbatim
/-- Extensionality lemma for `accYY`. -/
lemma accYY_ext {S T : (SMνCharges n).Charges}
    (hj : ∀ (j : Fin 6), ∑ i, (toSpecies j) S i = ∑ i, (toSpecies j) T i) :
    accYY S = accYY T := by
  rw [accYY_decomp, accYY_decomp]
  repeat rw [hj]


-- @@ L236-266 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The quadratic bilinear map. -/
@[simps!]
def quadBiLin : BiLinearSymm (SMνCharges n).Charges := BiLinearSymm.mk₂
  (fun S => ∑ i, (Q S.1 i * Q S.2 i +
    - 2 * (U S.1 i * U S.2 i) +
    D S.1 i * D S.2 i +
    (- 1) * (L S.1 i * L S.2 i) +
    E S.1 i * E S.2 i))
  (by
    intro a S T
    simp only
    rw [Finset.mul_sum]
    refine Fintype.sum_congr _ _ fun i ↦ ?_
    repeat rw [map_smul]
    simp only [HSMul.hSMul, SMul.smul, toSpecies_apply, Fin.isValue, neg_mul, one_mul]
    ring)
  (by
    intro S T R
    simp only
    rw [← Finset.sum_add_distrib]
    refine Fintype.sum_congr _ _ fun i ↦ ?_
    repeat rw [map_add]
    simp only [ACCSystemCharges.chargesAddCommMonoid_add, toSpecies_apply, Fin.isValue, neg_mul,
      one_mul]
    ring)
  (by
    intro S T
    simp only [toSpecies_apply, Fin.isValue, neg_mul, one_mul]
    refine Fintype.sum_congr _ _ fun i ↦ ?_
    ring)


-- @@ L268-276 verbatim
lemma quadBiLin_decomp (S T : (SMνCharges n).Charges) :
    quadBiLin S T = ∑ i, Q S i * Q T i - 2 * ∑ i, U S i * U T i +
        ∑ i, D S i * D T i - ∑ i, L S i * L T i + ∑ i, E S i * E T i := by
  rw [quadBiLin]
  rw [BiLinearSymm.mk₂_toFun_apply]
  repeat rw [Finset.sum_add_distrib]
  repeat rw [← Finset.mul_sum]
  simp only [toSpecies_apply, Fin.isValue, neg_mul, one_mul, add_left_inj]
  ring


-- @@ L278-281 verbatim
/-- The quadratic anomaly cancellation condition. -/
@[simp]
def accQuad : HomogeneousQuadratic (SMνCharges n).Charges :=
  (@quadBiLin n).toHomogeneousQuad


-- @@ L283-288 verbatim
lemma accQuad_decomp (S : (SMνCharges n).Charges) :
    accQuad S = ∑ i, (Q S i)^2 - 2 * ∑ i, (U S i)^2 + ∑ i, (D S i)^2 - ∑ i, (L S i)^2
    + ∑ i, (E S i)^2 := by
  change (quadBiLin S) S = _
  rw [quadBiLin_decomp]
  ring_nf


-- @@ L290-297 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- Extensionality lemma for `accQuad`. -/
lemma accQuad_ext {S T : (SMνCharges n).Charges}
    (h : ∀ j, ∑ i, ((fun a => a^2) ∘ toSpecies j S) i =
    ∑ i, ((fun a => a^2) ∘ toSpecies j T) i) :
    accQuad S = accQuad T := by
  rw [accQuad_decomp, accQuad_decomp]
  simp_all


-- @@ L299-334 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The symmetric trilinear form used to define the cubic acc. -/
@[simps!]
def cubeTriLin : TriLinearSymm (SMνCharges n).Charges := TriLinearSymm.mk₃
  (fun S => ∑ i, (6 * ((Q S.1 i) * (Q S.2.1 i) * (Q S.2.2 i))
    + 3 * ((U S.1 i) * (U S.2.1 i) * (U S.2.2 i))
    + 3 * ((D S.1 i) * (D S.2.1 i) * (D S.2.2 i))
    + 2 * ((L S.1 i) * (L S.2.1 i) * (L S.2.2 i))
    + ((E S.1 i) * (E S.2.1 i) * (E S.2.2 i))
    + ((N S.1 i) * (N S.2.1 i) * (N S.2.2 i))))
  (by
    intro a S T R
    simp only
    rw [Finset.mul_sum]
    refine Fintype.sum_congr _ _ fun i ↦ ?_
    repeat rw [map_smul]
    simp only [HSMul.hSMul, SMul.smul, toSpecies_apply, Fin.isValue]
    ring)
  (by
    intro S T R L
    simp only
    rw [← Finset.sum_add_distrib]
    refine Fintype.sum_congr _ _ fun i ↦ ?_
    repeat rw [map_add]
    simp only [ACCSystemCharges.chargesAddCommMonoid_add, toSpecies_apply, Fin.isValue]
    ring)
  (by
    intro S T L
    simp only [toSpecies_apply, Fin.isValue]
    refine Fintype.sum_congr _ _ fun i ↦ ?_
    ring)
  (by
    intro S T L
    simp only [toSpecies_apply, Fin.isValue]
    refine Fintype.sum_congr _ _ fun i ↦ ?_
    ring)


-- @@ L336-343 verbatim
lemma cubeTriLin_decomp (S T R : (SMνCharges n).Charges) :
    cubeTriLin S T R = 6 * ∑ i, (Q S i * Q T i * Q R i) + 3 * ∑ i, (U S i * U T i * U R i) +
      3 * ∑ i, (D S i * D T i * D R i) + 2 * ∑ i, (L S i * L T i * L R i) +
      ∑ i, (E S i * E T i * E R i) + ∑ i, (N S i * N T i * N R i) := by
  rw [cubeTriLin]
  rw [TriLinearSymm.mk₃_toFun_apply_apply]
  repeat rw [Finset.sum_add_distrib]
  repeat rw [← Finset.mul_sum]


-- @@ L345-347 verbatim
/-- The cubic ACC. -/
@[simp]
def accCube : HomogeneousCubic (SMνCharges n).Charges := cubeTriLin.toCubic


-- @@ L349-354 verbatim
lemma accCube_decomp (S : (SMνCharges n).Charges) :
    accCube S = 6 * ∑ i, (Q S i)^3 + 3 * ∑ i, (U S i)^3 + 3 * ∑ i, (D S i)^3 + 2 * ∑ i, (L S i)^3 +
      ∑ i, (E S i)^3 + ∑ i, (N S i)^3 := by
  change cubeTriLin S S S = _
  rw [cubeTriLin_decomp]
  ring_nf


-- @@ L356-363 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- Extensionality lemma for `accCube`. -/
lemma accCube_ext {S T : (SMνCharges n).Charges}
    (h : ∀ j, ∑ i, ((fun a => a^3) ∘ toSpecies j S) i =
    ∑ i, ((fun a => a^3) ∘ toSpecies j T) i) :
    accCube S = accCube T := by
  repeat rw [accCube_decomp]
  simp_all


-- @@ L365-365 verbatim
end SMνACCs
