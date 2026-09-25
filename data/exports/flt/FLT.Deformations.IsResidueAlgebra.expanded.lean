/-
Copyright (c) 2025 Javier López-Contreras. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Javier López-Contreras, Kevin Buzzard
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import FLT.Mathlib.RingTheory.LocalRing.Defs
import FLT.Deformations.Lemmas


-- @@ L12-18 verbatim
/-!
# Residue algebras

The typeclass `IsResidueAlgebra 𝓞 A` expressing that an `𝓞`-algebra `A`
has the same residue field as `𝓞`, that is, the induced map on residue
fields is bijective.
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
open Function IsLocalRing


-- @@ L24-24 verbatim
variable (𝓞 : Type*) [CommRing 𝓞]


-- @@ L26-26 verbatim
local notation3:max "𝓴" 𝓞:max => (IsLocalRing.ResidueField 𝓞)


-- @@ L28-28 verbatim
variable (A : Type*) [CommRing A] [Algebra 𝓞 A] [IsLocalRing A]


-- @@ L30-36 expanded
/-- `IsResidueAlgebra 𝓞` indicates that `A` `[Algebra 𝓞 A]` has the same residue field as `𝓞`.
It is sufficient for the natural map 𝓞 to 𝓴 A to be surjective. The actual `≃+*` between residue
fields is given in `IsResidueAlgebra.ringEquiv`.
-/
class IsResidueAlgebra : Prop where
  isSurjective' : Surjective (algebraMap 𝓞 ((IsLocalRing.ResidueField A)))


-- @@ L38-38 verbatim
namespace IsResidueAlgebra


-- @@ L40-40 verbatim
variable [IsResidueAlgebra 𝓞 A]


-- @@ L42-42 expanded
lemma algebraMap_surjective : Surjective (algebraMap 𝓞 ((IsLocalRing.ResidueField A))) :=
  isSurjective'


-- @@ L44-49 expanded
variable [IsLocalRing 𝓞] [IsLocalHom (algebraMap 𝓞 A)] in
lemma algebraMap_bijective :
    Bijective (algebraMap ((IsLocalRing.ResidueField 𝓞)) ((IsLocalRing.ResidueField A))) :=
  by
  have hsurj1 := IsLocalRing.residue_surjective (R := 𝓞)
  have hsurj2 := IsResidueAlgebra.algebraMap_surjective 𝓞 A
  exact
    ⟨(algebraMap ((IsLocalRing.ResidueField 𝓞)) ((IsLocalRing.ResidueField A))).injective,
      (Function.Surjective.of_comp_iff
            (algebraMap ((IsLocalRing.ResidueField 𝓞)) ((IsLocalRing.ResidueField A))) hsurj1).mp
        hsurj2⟩


-- @@ L51-54 expanded
variable [IsLocalRing 𝓞] [IsLocalHom (algebraMap 𝓞 A)] in
/-- The isomorphism of residue fields for a residue algebra. -/
noncomputable def algEquiv : (IsLocalRing.ResidueField 𝓞) ≃ₐ[𝓞] (IsLocalRing.ResidueField A) :=
  .ofBijective (IsScalarTower.toAlgHom _ _ _) (algebraMap_bijective _ _)


-- @@ L56-56 verbatim
instance [IsLocalRing 𝓞] : IsResidueAlgebra 𝓞 𝓞 := ⟨IsLocalRing.residue_surjective⟩


-- @@ L58-58 verbatim
section Quotient


-- @@ L60-64 verbatim
instance (I : Ideal A) [Nontrivial (A ⧸ I)] : IsResidueAlgebra 𝓞 (A ⧸ I) where
  isSurjective' :=
    have : IsLocalHom (Ideal.Quotient.mk I) := .of_surjective _ Ideal.Quotient.mk_surjective
    (IsLocalRing.ResidueField.map_surjective _ Ideal.Quotient.mk_surjective).comp
      (IsResidueAlgebra.algebraMap_surjective 𝓞 A)


-- @@ L66-66 verbatim
end Quotient


-- @@ L68-68 verbatim
section Relative


-- @@ L70-70 verbatim
variable {𝓞 A}

-- @@ L71-71 verbatim
variable {B : Type*} [CommRing B] [Algebra 𝓞 B] [IsLocalRing B] [IsResidueAlgebra 𝓞 B]


-- @@ L73-78 verbatim
omit [IsLocalRing A] [IsResidueAlgebra 𝓞 A] in
lemma of_restrictScalars [Algebra A B] [IsScalarTower 𝓞 A B] : IsResidueAlgebra A B where
  isSurjective' := by
    refine .of_comp (g := algebraMap 𝓞 A) ?_
    rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq]
    exact IsResidueAlgebra.algebraMap_surjective _ _


-- @@ L80-80 verbatim
end Relative


-- @@ L82-82 verbatim
open IsLocalRing


-- @@ L84-84 verbatim
variable {A}


-- @@ L86-90 verbatim
lemma exists_sub_mem_maximalIdeal (r : A) : ∃ a, r - algebraMap 𝓞 A a ∈ maximalIdeal _ := by
  obtain ⟨a, ha⟩ := IsResidueAlgebra.algebraMap_surjective 𝓞 _ (residue _ r)
  refine ⟨a, ?_⟩
  rw [← Ideal.Quotient.eq]
  exact ha.symm


-- @@ L92-94 verbatim
/-- For an `r : A`, this is an arbitrary choice of `x : 𝓞` such that `r ≡ x (mod 𝔪_A)`. -/
noncomputable
def preimage (r : A) : 𝓞 := (exists_sub_mem_maximalIdeal 𝓞 r).choose


-- @@ L96-97 verbatim
lemma preimage_spec (r : A) : r - algebraMap 𝓞 A (preimage 𝓞 r) ∈ maximalIdeal _ :=
  (exists_sub_mem_maximalIdeal 𝓞 r).choose_spec


-- @@ L99-100 verbatim
lemma residue_preimage (r : A) : residue _ (algebraMap _ _ (preimage 𝓞 r)) = residue _ r :=
  (Ideal.Quotient.eq.mpr (preimage_spec 𝓞 r)).symm


-- @@ L102-108 verbatim
variable [IsLocalRing 𝓞] [IsLocalHom (algebraMap 𝓞 A)] in
lemma residue_preimage_eq_iff {r : A} {a} :
    residue _ (preimage 𝓞 r) = a ↔ residue _ r = ResidueField.map (algebraMap 𝓞 A) a := by
  rw [← (IsResidueAlgebra.algebraMap_bijective 𝓞 A).1.eq_iff]
  erw [ResidueField.map_residue]
  rw [residue_preimage]
  rfl


-- @@ L110-110 verbatim
end IsResidueAlgebra
