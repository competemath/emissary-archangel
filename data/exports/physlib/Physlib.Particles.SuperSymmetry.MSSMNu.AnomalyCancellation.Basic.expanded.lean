/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.AnomalyCancellation.Basic

-- @@ L9-15 verbatim
/-!
# The MSSM with 3 families and RHNs

We define the system of ACCs for the MSSM with 3 families and RHNs.
We define the system of charges for 1-species. We prove some basic lemmas about them.

-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
open Nat

-- @@ L20-20 verbatim
open BigOperators


-- @@ L22-24 verbatim
/-- The vector space of charges corresponding to the MSSM fermions. -/
@[simps!]
def MSSMCharges : ACCSystemCharges := ⟨20⟩


-- @@ L26-28 verbatim
/-- The vector spaces of charges of one species of fermions in the MSSM. -/
@[simps!]
def MSSMSpecies : ACCSystemCharges := ⟨3⟩


-- @@ L30-30 verbatim
namespace MSSMCharges


-- @@ L32-34 verbatim
lemma sum_MSSMSpecies_numberCharges_eq_expand [AddCommMonoid M]
    (f : Fin MSSMSpecies.numberCharges → M) :
    ∑ i, f i = f ⟨0, by simp⟩ + f ⟨1, by simp⟩ + f ⟨2, by simp⟩ := Fin.sum_univ_three f


-- @@ L36-41 verbatim
/-- An equivalence between `MSSMCharges.charges` and the space of maps
`(Fin 18 ⊕ Fin 2 → ℚ)`. The first 18 factors corresponds to the SM fermions, while the last two
are the higgsions. -/
@[simps!]
def toSMPlusH : MSSMCharges.Charges ≃ (Fin 18 ⊕ Fin 2 → ℚ) :=
  ((@finSumFinEquiv 18 2).arrowCongr (Equiv.refl ℚ)).symm


-- @@ L43-49 verbatim
/-- An equivalence between `Fin 18 ⊕ Fin 2 → ℚ` and `(Fin 18 → ℚ) × (Fin 2 → ℚ)`. -/
@[simps!]
def splitSMPlusH : (Fin 18 ⊕ Fin 2 → ℚ) ≃ (Fin 18 → ℚ) × (Fin 2 → ℚ) where
  toFun f := (f ∘ Sum.inl, f ∘ Sum.inr)
  invFun f := Sum.elim f.1 f.2
  left_inv f := Sum.elim_comp_inl_inr f
  right_inv _ := rfl


-- @@ L51-55 verbatim
/-- An equivalence between `MSSMCharges.charges` and `(Fin 18 → ℚ) × (Fin 2 → ℚ)`. This
splits the charges up into the SM and the additional ones for the MSSM. -/
@[simps!]
def toSplitSMPlusH : MSSMCharges.Charges ≃ (Fin 18 → ℚ) × (Fin 2 → ℚ) :=
  toSMPlusH.trans splitSMPlusH


-- @@ L57-61 verbatim
/-- An equivalence between `(Fin 18 → ℚ)` and `(Fin 6 → Fin 3 → ℚ)`. -/
@[simps!]
def toSpeciesMaps' : (Fin 18 → ℚ) ≃ (Fin 6 → Fin 3 → ℚ) :=
  ((Equiv.curry _ _ _).symm.trans
    ((@finProdFinEquiv 6 3).arrowCongr (Equiv.refl ℚ))).symm


-- @@ L63-68 verbatim
/-- An equivalence between `MSSMCharges.charges` and `(Fin 6 → Fin 3 → ℚ) × (Fin 2 → ℚ))`.
This splits charges up into the SM and additional fermions, and further splits the SM into
species. -/
@[simps!]
def toSpecies : MSSMCharges.Charges ≃ (Fin 6 → Fin 3 → ℚ) × (Fin 2 → ℚ) :=
  toSplitSMPlusH.trans (Equiv.prodCongr toSpeciesMaps' (Equiv.refl _))


-- @@ L70-76 verbatim
/-- For a given `i ∈ Fin 6` the projection of `MSSMCharges.charges` down to the
corresponding SM species of charges. -/
@[simps!]
def toSMSpecies (i : Fin 6) : MSSMCharges.Charges →ₗ[ℚ] MSSMSpecies.Charges where
  toFun S := (Prod.fst ∘ toSpecies) S i
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl


-- @@ L78-80 verbatim
lemma toSMSpecies_toSpecies_inv (i : Fin 6) (f : (Fin 6 → Fin 3 → ℚ) × (Fin 2 → ℚ)) :
    (toSMSpecies i) (toSpecies.symm f) = f.1 i :=
  congrFun (congrArg Prod.fst (toSpecies.apply_symm_apply f)) i


-- @@ L82-83 verbatim
/-- The `Q` charges as a map `Fin 3 → ℚ`. -/
abbrev Q := toSMSpecies 0

-- @@ L84-85 verbatim
/-- The `U` charges as a map `Fin 3 → ℚ`. -/
abbrev U := toSMSpecies 1

-- @@ L86-87 verbatim
/-- The `D` charges as a map `Fin 3 → ℚ`. -/
abbrev D := toSMSpecies 2

-- @@ L88-89 verbatim
/-- The `L` charges as a map `Fin 3 → ℚ`. -/
abbrev L := toSMSpecies 3

-- @@ L90-91 verbatim
/-- The `E` charges as a map `Fin 3 → ℚ`. -/
abbrev E := toSMSpecies 4

-- @@ L92-93 verbatim
/-- The `N` charges as a map `Fin 3 → ℚ`. -/
abbrev N := toSMSpecies 5


-- @@ L95-100 verbatim
/-- The charge `Hd`. -/
@[simps!]
def Hd : MSSMCharges.Charges →ₗ[ℚ] ℚ where
  toFun S := S ⟨18, Nat.lt_of_sub_eq_succ rfl⟩
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl


-- @@ L102-107 verbatim
/-- The charge `Hu`. -/
@[simps!]
def Hu : MSSMCharges.Charges →ₗ[ℚ] ℚ where
  toFun S := S ⟨19, Nat.lt_of_sub_eq_succ rfl⟩
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl


-- @@ L109-112 verbatim
lemma charges_eq_toSpecies_eq (S T : MSSMCharges.Charges) :
    S = T ↔ (∀ i, toSMSpecies i S = toSMSpecies i T) ∧ Hd S = Hd T ∧ Hu S = Hu T := by
  refine ⟨fun h => h ▸ ⟨fun _ => rfl, rfl, rfl⟩, fun h => toSpecies.injective ?_⟩
  exact Prod.ext (funext h.1) (funext fun | 0 => h.2.1 | 1 => h.2.2)


-- @@ L114-116 verbatim
lemma Hd_toSpecies_inv (f : (Fin 6 → Fin 3 → ℚ) × (Fin 2 → ℚ)) :
    Hd (toSpecies.symm f) = f.2 0 := by
  rfl


-- @@ L118-120 verbatim
lemma Hu_toSpecies_inv (f : (Fin 6 → Fin 3 → ℚ) × (Fin 2 → ℚ)) :
    Hu (toSpecies.symm f) = f.2 1 := by
  rfl


-- @@ L122-122 verbatim
end MSSMCharges


-- @@ L124-124 verbatim
namespace MSSMACCs


-- @@ L126-126 verbatim
open MSSMCharges


-- @@ L128-140 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The gravitational anomaly equation. -/
def accGrav : MSSMCharges.Charges →ₗ[ℚ] ℚ where
  toFun S := ∑ i, (6 * Q S i + 3 * U S i + 3 * D S i
    + 2 * L S i + E S i + N S i) + 2 * (Hd S + Hu S)
  map_add' S T := by
    simp only [map_add, ACCSystemCharges.chargesAddCommMonoid_add,
      sum_MSSMSpecies_numberCharges_eq_expand]
    ring
  map_smul' a S := by
    simp only [map_smul, smul_eq_mul, RingHom.id_apply]
    simp only [HSMul.hSMul, SMul.smul, sum_MSSMSpecies_numberCharges_eq_expand]
    ring


-- @@ L142-149 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- Extensionality lemma for `accGrav`. -/
lemma accGrav_ext {S T : MSSMCharges.Charges}
    (hj : ∀ (j : Fin 6), ∑ i, (toSMSpecies j) S i = ∑ i, (toSMSpecies j) T i)
    (hd : Hd S = Hd T) (hu : Hu S = Hu T) :
    accGrav S = accGrav T := by
  simp only [accGrav, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_add_distrib, ← Finset.mul_sum,
    hj, hd, hu]


-- @@ L151-162 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The anomaly cancellation condition for SU(2) anomaly. -/
def accSU2 : MSSMCharges.Charges →ₗ[ℚ] ℚ where
  toFun S := ∑ i, (3 * Q S i + L S i) + Hd S + Hu S
  map_add' S T := by
    simp only [map_add, ACCSystemCharges.chargesAddCommMonoid_add,
      sum_MSSMSpecies_numberCharges_eq_expand]
    ring
  map_smul' a S := by
    simp only [map_smul, smul_eq_mul, RingHom.id_apply]
    simp only [HSMul.hSMul, SMul.smul, sum_MSSMSpecies_numberCharges_eq_expand]
    ring


-- @@ L164-171 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- Extensionality lemma for `accSU2`. -/
lemma accSU2_ext {S T : MSSMCharges.Charges}
    (hj : ∀ (j : Fin 6), ∑ i, (toSMSpecies j) S i = ∑ i, (toSMSpecies j) T i)
    (hd : Hd S = Hd T) (hu : Hu S = Hu T) :
    accSU2 S = accSU2 T := by
  simp only [accSU2, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_add_distrib, ← Finset.mul_sum,
    hj, hd, hu]


-- @@ L173-184 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The anomaly cancellation condition for SU(3) anomaly. -/
def accSU3 : MSSMCharges.Charges →ₗ[ℚ] ℚ where
  toFun S := ∑ i, (2 * (Q S i) + (U S i) + (D S i))
  map_add' S T := by
    simp only [map_add, ACCSystemCharges.chargesAddCommMonoid_add,
      sum_MSSMSpecies_numberCharges_eq_expand]
    ring
  map_smul' a S := by
    simp only [map_smul, smul_eq_mul, RingHom.id_apply]
    simp only [HSMul.hSMul, SMul.smul, sum_MSSMSpecies_numberCharges_eq_expand]
    ring


-- @@ L186-192 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- Extensionality lemma for `accSU3`. -/
lemma accSU3_ext {S T : MSSMCharges.Charges}
    (hj : ∀ (j : Fin 6), ∑ i, (toSMSpecies j) S i = ∑ i, (toSMSpecies j) T i) :
    accSU3 S = accSU3 T := by
  simp only [accSU3, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_add_distrib, ← Finset.mul_sum,
    hj]


-- @@ L194-206 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The ACC for `Y²`. -/
def accYY : MSSMCharges.Charges →ₗ[ℚ] ℚ where
  toFun S := ∑ i, ((Q S) i + 8 * (U S) i + 2 * (D S) i + 3 * (L S) i
    + 6 * (E S) i) + 3 * (Hd S + Hu S)
  map_add' S T := by
    simp only [map_add, ACCSystemCharges.chargesAddCommMonoid_add,
      sum_MSSMSpecies_numberCharges_eq_expand]
    ring
  map_smul' a S := by
    simp only [map_smul, smul_eq_mul, RingHom.id_apply]
    simp only [HSMul.hSMul, SMul.smul, sum_MSSMSpecies_numberCharges_eq_expand]
    ring


-- @@ L208-215 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- Extensionality lemma for `accGrav`. -/
lemma accYY_ext {S T : MSSMCharges.Charges}
    (hj : ∀ (j : Fin 6), ∑ i, (toSMSpecies j) S i = ∑ i, (toSMSpecies j) T i)
    (hd : Hd S = Hd T) (hu : Hu S = Hu T) :
    accYY S = accYY T := by
  simp only [accYY, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_add_distrib, ← Finset.mul_sum,
    hj, hd, hu]


-- @@ L217-261 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The symmetric bilinear function used to define the quadratic ACC. -/
@[simps!]
def quadBiLin : BiLinearSymm MSSMCharges.Charges := BiLinearSymm.mk₂
  (fun (S, T) => ∑ i, (Q S i * Q T i + (- 2) * (U S i * U T i) +
    D S i * D T i + (- 1) * (L S i * L T i) + E S i * E T i) +
    (- Hd S * Hd T + Hu S * Hu T))
  (by
    intro a S T
    simp only
    rw [mul_add]
    congr 1
    · rw [Finset.mul_sum]
      apply Fintype.sum_congr
      intro i
      repeat rw [map_smul]
      simp only [HSMul.hSMul, SMul.smul, toSMSpecies_apply, Fin.isValue, neg_mul, one_mul]
      ring
    · simp only [map_smul, Hd_apply, Fin.reduceFinMk, Fin.isValue, smul_eq_mul, neg_mul, Hu_apply]
      ring)
  (by
    intro S T R
    simp only
    rw [add_assoc, ← add_assoc (-Hd S * Hd R + Hu S * Hu R) _ _]
    rw [add_comm (-Hd S * Hd R + Hu S * Hu R) _]
    rw [add_assoc]
    rw [← add_assoc _ _ (-Hd S * Hd R + Hu S * Hu R + (-Hd T * Hd R + Hu T * Hu R))]
    congr 1
    · rw [← Finset.sum_add_distrib]
      apply Fintype.sum_congr
      intro i
      repeat rw [map_add]
      simp only [ACCSystemCharges.chargesAddCommMonoid_add, toSMSpecies_apply, Fin.isValue, neg_mul,
        one_mul]
      ring
    · rw [Hd.map_add, Hu.map_add]
      ring)
  (by
    intro S L
    simp only [toSMSpecies_apply, Fin.isValue, neg_mul, one_mul, Hd_apply, Fin.reduceFinMk,
      Hu_apply]
    congr 1
    · simp only [reduceMul, Fin.isValue, sum_MSSMSpecies_numberCharges_eq_expand]
      ring
    · ring)


-- @@ L263-265 verbatim
/-- The quadratic ACC. -/
@[simp]
def accQuad : HomogeneousQuadratic MSSMCharges.Charges := quadBiLin.toHomogeneousQuad


-- @@ L267-276 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- Extensionality lemma for `accQuad`. -/
lemma accQuad_ext {S T : (MSSMCharges).Charges}
    (h : ∀ j, ∑ i, ((fun a => a^2) ∘ toSMSpecies j S) i =
    ∑ i, ((fun a => a^2) ∘ toSMSpecies j T) i)
    (hd : Hd S = Hd T) (hu : Hu S = Hu T) :
    accQuad S = accQuad T := by
  have h1 : ∀ j, ∑ i, (toSMSpecies j S i)^2 = ∑ i, (toSMSpecies j T i)^2 := h
  simp only [HomogeneousQuadratic, accQuad, BiLinearSymm.toHomogeneousQuad_apply, quadBiLin,
    BiLinearSymm.mk₂_toFun_apply, ← pow_two, Finset.sum_add_distrib, ← Finset.mul_sum, h1, hd, hu]


-- @@ L278-288 verbatim
/-- The function underlying the symmetric trilinear form used to define the cubic ACC. -/
def cubeTriLinToFun
    (S : MSSMCharges.Charges × MSSMCharges.Charges × MSSMCharges.Charges) : ℚ :=
  ∑ i, (6 * (Q S.1 i * Q S.2.1 i * Q S.2.2 i)
    + 3 * (U S.1 i * U S.2.1 i * U S.2.2 i)
    + 3 * (D S.1 i * D S.2.1 i * D S.2.2 i)
    + 2 * (L S.1 i * L S.2.1 i * L S.2.2 i)
    + E S.1 i * E S.2.1 i * E S.2.2 i
    + N S.1 i * N S.2.1 i * N S.2.2 i)
    + (2 * Hd S.1 * Hd S.2.1 * Hd S.2.2
    + 2 * Hu S.1 * Hu S.2.1 * Hu S.2.2)


-- @@ L290-294 verbatim
lemma cubeTriLinToFun_map_smul₁ (a : ℚ) (S T R : MSSMCharges.Charges) :
    cubeTriLinToFun (a • S, T, R) = a * cubeTriLinToFun (S, T, R) := by
  simp only [cubeTriLinToFun, map_smul, smul_eq_mul]
  simp only [HSMul.hSMul, SMul.smul, sum_MSSMSpecies_numberCharges_eq_expand]
  ring


-- @@ L296-301 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma cubeTriLinToFun_map_add₁ (S T R L : MSSMCharges.Charges) :
    cubeTriLinToFun (S + T, R, L) = cubeTriLinToFun (S, R, L) + cubeTriLinToFun (T, R, L) := by
  simp only [cubeTriLinToFun, map_add, ACCSystemCharges.chargesAddCommMonoid_add,
    sum_MSSMSpecies_numberCharges_eq_expand]
  ring


-- @@ L303-306 verbatim
lemma cubeTriLinToFun_swap1 (S T R : MSSMCharges.Charges) :
    cubeTriLinToFun (S, T, R) = cubeTriLinToFun (T, S, R) := by
  simp only [cubeTriLinToFun, sum_MSSMSpecies_numberCharges_eq_expand]
  ring


-- @@ L308-311 verbatim
lemma cubeTriLinToFun_swap2 (S T R : MSSMCharges.Charges) :
    cubeTriLinToFun (S, T, R) = cubeTriLinToFun (S, R, T) := by
  simp only [cubeTriLinToFun, sum_MSSMSpecies_numberCharges_eq_expand]
  ring


-- @@ L313-320 verbatim
/-- The symmetric trilinear form used to define the cubic ACC. -/
@[simps!]
def cubeTriLin : TriLinearSymm MSSMCharges.Charges := TriLinearSymm.mk₃
  cubeTriLinToFun
  cubeTriLinToFun_map_smul₁
  cubeTriLinToFun_map_add₁
  cubeTriLinToFun_swap1
  cubeTriLinToFun_swap2


-- @@ L322-324 verbatim
/-- The cubic ACC. -/
@[simp]
def accCube : HomogeneousCubic MSSMCharges.Charges := cubeTriLin.toCubic


-- @@ L326-336 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- Extensionality lemma for `accCube`. -/
lemma accCube_ext {S T : MSSMCharges.Charges}
    (h : ∀ j, ∑ i, ((fun a => a^3) ∘ toSMSpecies j S) i =
    ∑ i, ((fun a => a^3) ∘ toSMSpecies j T) i)
    (hd : Hd S = Hd T) (hu : Hu S = Hu T) :
    accCube S = accCube T := by
  have h1 : ∀ j, ∑ i, (toSMSpecies j S i)^3 = ∑ i, (toSMSpecies j T i)^3 := h
  simp only [HomogeneousCubic, accCube, cubeTriLin, TriLinearSymm.toCubic_apply,
    TriLinearSymm.mk₃_toFun_apply_apply, cubeTriLinToFun, ← pow_three', Finset.sum_add_distrib,
    ← Finset.mul_sum, h1, hd, hu]


-- @@ L338-338 verbatim
end MSSMACCs


-- @@ L340-340 verbatim
open MSSMACCs


-- @@ L342-357 verbatim
/-- The ACCSystem for the MSSM without RHN. -/
@[simps!]
def MSSMACC : ACCSystem where
  toACCSystemCharges := MSSMCharges
  numberLinear := 4
  linearACCs := fun i =>
    match i with
    | 0 => accGrav
    | 1 => accSU2
    | 2 => accSU3
    | 3 => accYY
  numberQuadratic := 1
  quadraticACCs := fun i =>
    match i with
    | 0 => accQuad
  cubicACC := accCube


-- @@ L359-359 verbatim
namespace MSSMACC

-- @@ L360-360 verbatim
open MSSMCharges


-- @@ L362-362 verbatim
lemma cubicACC_apply (S : MSSMACC.Charges) : MSSMACC.cubicACC S = cubeTriLin.toCubic S := rfl


-- @@ L364-364 verbatim
lemma quadSol (S : MSSMACC.QuadSols) : accQuad S.val = 0 := S.quadSol ⟨0, by simp⟩


-- @@ L366-380 verbatim
/-- A solution from a charge satisfying the ACCs. -/
@[simp]
def AnomalyFreeMk (S : MSSMACC.Charges) (hg : accGrav S = 0)
    (hsu2 : accSU2 S = 0) (hsu3 : accSU3 S = 0) (hyy : accYY S = 0)
    (hquad : accQuad S = 0) (hcube : accCube S = 0) : MSSMACC.Sols :=
  ⟨⟨⟨S, by
    intro i
    match i with
    | ⟨0, _⟩ => exact hg
    | ⟨1, _⟩ => exact hsu2
    | ⟨2, _⟩ => exact hsu3
    | ⟨3, _⟩ => exact hyy⟩, by
    intro i
    match i with
    | ⟨0, _⟩ => exact hquad⟩, hcube⟩


-- @@ L382-386 verbatim
lemma AnomalyFreeMk_val (S : MSSMACC.Charges) (hg : accGrav S = 0)
    (hsu2 : accSU2 S = 0) (hsu3 : accSU3 S = 0) (hyy : accYY S = 0)
    (hquad : accQuad S = 0) (hcube : accCube S = 0) :
    (AnomalyFreeMk S hg hsu2 hsu3 hyy hquad hcube).val = S := by
  rfl


-- @@ L388-395 verbatim
/-- A `QuadSol` from a `LinSol` satisfying the quadratic ACC. -/
@[simp]
def AnomalyFreeQuadMk' (S : MSSMACC.LinSols) (hquad : accQuad S.val = 0) :
    MSSMACC.QuadSols :=
  ⟨S, by
    intro i
    match i with
    | ⟨0, _⟩ => exact hquad⟩


-- @@ L397-404 verbatim
/-- A `Sol` from a `LinSol` satisfying the quadratic and cubic ACCs. -/
@[simp]
def AnomalyFreeMk' (S : MSSMACC.LinSols) (hquad : accQuad S.val = 0)
    (hcube : accCube S.val = 0) : MSSMACC.Sols :=
  ⟨⟨S, by
    intro i
    match i with
    | ⟨0, _⟩ => exact hquad⟩, hcube⟩


-- @@ L406-409 verbatim
/-- A `Sol` from a `QuadSol` satisfying the cubic ACCs. -/
@[simp]
def AnomalyFreeMk'' (S : MSSMACC.QuadSols) (hcube : accCube S.val = 0) : MSSMACC.Sols :=
  ⟨S, hcube⟩


-- @@ L411-414 verbatim
lemma AnomalyFreeMk''_val (S : MSSMACC.QuadSols)
    (hcube : accCube S.val = 0) :
    (AnomalyFreeMk'' S hcube).val = S.val := by
  rfl


-- @@ L416-445 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The dot product on the vector space of charges. -/
@[simps!]
def dot : BiLinearSymm MSSMCharges.Charges := BiLinearSymm.mk₂
  (fun S => ∑ i, (Q S.1 i * Q S.2 i + U S.1 i * U S.2 i +
    D S.1 i * D S.2 i + L S.1 i * L S.2 i + E S.1 i * E S.2 i
    + N S.1 i * N S.2 i) + Hd S.1 * Hd S.2 + Hu S.1 * Hu S.2)
  (by
    intro a S T
    repeat rw [(toSMSpecies _).map_smul]
    rw [Hd.map_smul, Hu.map_smul]
    simp only [Fin.isValue, toSMSpecies_apply, reduceMul, sum_MSSMSpecies_numberCharges_eq_expand,
      Fin.zero_eta, Fin.mk_one, Hd_apply, Fin.reduceFinMk, smul_eq_mul, Hu_apply]
    simp only [HSMul.hSMul, SMul.smul, Fin.isValue, toSMSpecies_apply]
    ring)
  (by
    intro S1 S2 T
    simp only [map_add, ACCSystemCharges.chargesAddCommMonoid_add]
    simp only [toSMSpecies_apply, Fin.isValue, Hd_apply, Fin.reduceFinMk, Hu_apply]
    simp only [reduceMul, Fin.isValue, sum_MSSMSpecies_numberCharges_eq_expand, Fin.zero_eta,
      Fin.mk_one]
    simp only [Fin.isValue, Prod.mk_zero_zero, Prod.mk_one_one]
    ring)
  (by
    intro S T
    simp only [toSMSpecies_apply, Fin.isValue, Hd_apply, Fin.reduceFinMk, Hu_apply]
    simp only [reduceMul, Fin.isValue, sum_MSSMSpecies_numberCharges_eq_expand, Fin.zero_eta,
      Fin.mk_one]
    simp only [Fin.isValue, Prod.mk_zero_zero, Prod.mk_one_one]
    ring)


-- @@ L447-447 verbatim
end MSSMACC
