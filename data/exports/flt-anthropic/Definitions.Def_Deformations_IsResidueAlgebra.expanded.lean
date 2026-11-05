import Mathlib
import Definitions.Def_Mathlib_RingTheory_LocalRing_Defs
import Definitions.Def_Deformations_Deformations_Lemmas


-- @@ L5-5 verbatim
set_option autoImplicit false


-- @@ L7-7 verbatim
open Function IsLocalRing


-- @@ L9-9 verbatim
variable (𝓞 : Type*) [CommRing 𝓞]


-- @@ L11-11 verbatim
local notation3:max "𝓴" 𝓞:max => (IsLocalRing.ResidueField 𝓞)


-- @@ L13-13 verbatim
variable (A : Type*) [CommRing A] [Algebra 𝓞 A] [IsLocalRing A]


-- @@ L15-16 expanded
class IsResidueAlgebra : Prop where
  isSurjective' : Surjective (algebraMap 𝓞 ((IsLocalRing.ResidueField A)))


-- @@ L18-18 verbatim
namespace IsResidueAlgebra


-- @@ L20-20 verbatim
variable [IsResidueAlgebra 𝓞 A]


-- @@ L22-22 expanded
lemma algebraMap_surjective : Surjective (algebraMap 𝓞 ((IsLocalRing.ResidueField A))) :=
  isSurjective'


-- @@ L24-29 expanded
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


-- @@ L31-34 expanded
variable [IsLocalRing 𝓞] [IsLocalHom (algebraMap 𝓞 A)] in
noncomputable def algEquiv : (IsLocalRing.ResidueField 𝓞) ≃ₐ[𝓞] (IsLocalRing.ResidueField A) :=
  .ofBijective (IsScalarTower.toAlgHom _ _ _) (algebraMap_bijective _ _)


-- @@ L36-36 verbatim
instance [IsLocalRing 𝓞] : IsResidueAlgebra 𝓞 𝓞 := ⟨IsLocalRing.residue_surjective⟩


-- @@ L38-38 verbatim
section Quotient


-- @@ L40-44 verbatim
instance (I : Ideal A) [Nontrivial (A ⧸ I)] : IsResidueAlgebra 𝓞 (A ⧸ I) where
  isSurjective' :=
    have : IsLocalHom (Ideal.Quotient.mk I) := .of_surjective _ Ideal.Quotient.mk_surjective
    (IsLocalRing.ResidueField.map_surjective _ Ideal.Quotient.mk_surjective).comp
      (IsResidueAlgebra.algebraMap_surjective 𝓞 A)


-- @@ L46-46 verbatim
end Quotient


-- @@ L48-48 verbatim
section Relative


-- @@ L50-50 verbatim
variable {𝓞 A}

-- @@ L51-51 verbatim
variable {B : Type*} [CommRing B] [Algebra 𝓞 B] [IsLocalRing B] [IsResidueAlgebra 𝓞 B]


-- @@ L53-58 verbatim
omit [IsLocalRing A] [IsResidueAlgebra 𝓞 A] in
lemma of_restrictScalars [Algebra A B] [IsScalarTower 𝓞 A B] : IsResidueAlgebra A B where
  isSurjective' := by
    refine .of_comp (g := algebraMap 𝓞 A) ?_
    rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq]
    exact IsResidueAlgebra.algebraMap_surjective _ _


-- @@ L60-60 verbatim
end Relative


-- @@ L62-62 verbatim
open IsLocalRing


-- @@ L64-64 verbatim
variable {A}


-- @@ L66-70 verbatim
lemma exists_sub_mem_maximalIdeal (r : A) : ∃ a, r - algebraMap 𝓞 A a ∈ maximalIdeal _ := by
  obtain ⟨a, ha⟩ := IsResidueAlgebra.algebraMap_surjective 𝓞 _ (residue _ r)
  refine ⟨a, ?_⟩
  rw [← Ideal.Quotient.eq]
  exact ha.symm


-- @@ L72-73 verbatim
noncomputable
def preimage (r : A) : 𝓞 := (exists_sub_mem_maximalIdeal 𝓞 r).choose


-- @@ L75-76 verbatim
lemma preimage_spec (r : A) : r - algebraMap 𝓞 A (preimage 𝓞 r) ∈ maximalIdeal _ :=
  (exists_sub_mem_maximalIdeal 𝓞 r).choose_spec


-- @@ L78-79 verbatim
lemma residue_preimage (r : A) : residue _ (algebraMap _ _ (preimage 𝓞 r)) = residue _ r :=
  (Ideal.Quotient.eq.mpr (preimage_spec 𝓞 r)).symm


-- @@ L81-87 verbatim
variable [IsLocalRing 𝓞] [IsLocalHom (algebraMap 𝓞 A)] in
lemma residue_preimage_eq_iff {r : A} {a} :
    residue _ (preimage 𝓞 r) = a ↔ residue _ r = ResidueField.map (algebraMap 𝓞 A) a := by
  rw [← (IsResidueAlgebra.algebraMap_bijective 𝓞 A).1.eq_iff]
  erw [ResidueField.map_residue]
  rw [residue_preimage]
  rfl


-- @@ L89-89 verbatim
end IsResidueAlgebra
