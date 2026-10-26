/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import RiemannRoch.Chow.NormalCone.DeformationSpaceGeometry


-- @@ L9-30 verbatim
/-!
# Quotient deformations and the input for specialization

Ported from Paul-Lez/GromovWitten (Apache-2.0), commit fae673f,
file `GromovWitten/AlgebraicGeometry/Cones/DeformationSpecialization.lean`;
adapted to the RRC frozen base (Raph-DG mathlib fork, Lean v4.32.0-rc1) with the top namespace
`GromovWitten` renamed to `SchemeNormalCone`.
The upstream tail (`parameterSection`, `specialFibreCartierDivisor`, `specialFibreCartierIso`)
is **not** ported: it is phrased with GromovWitten's own `Curves.EffectiveCartierDivisor`
(`Curves/CartierDivisors.lean`, ~6.5k lines with its imports), which RRC does not adopt.

Let `P` be the ideal of a closed subscheme of `Spec R`, and put
`B = R ⧸ P`.  The coefficientwise Laurent map induces the actual comparison

`R[It,t⁻¹] ⟶ B[(IB)t,t⁻¹]`.

The map is surjective, including when `P` is prime and the closed subscheme is
integral.  Its kernel is recorded coefficientwise; this is the correct kernel
without a flatness or Tor-independence hypothesis.  Passing to the parameter
quotients gives the closed immersion of the special normal cones, while
inverting the parameter gives the map on the generic trivial families.
-/


-- @@ L32-32 verbatim
set_option autoImplicit true

-- @@ L33-33 verbatim
set_option relaxedAutoImplicit false

-- @@ L34-34 verbatim
set_option maxSynthPendingDepth 3


-- @@ L36-36 verbatim
open CategoryTheory Limits AlgebraicGeometry LaurentPolynomial

-- @@ L37-37 verbatim
open scoped TensorProduct


-- @@ L39-39 verbatim
namespace SchemeNormalCone.AlgebraicGeometry


-- @@ L41-41 verbatim
universe u


-- @@ L43-43 verbatim
noncomputable section


-- @@ L45-45 verbatim
namespace AffineDeformationSpace


-- @@ L47-47 verbatim
section Quotient


-- @@ L49-49 verbatim
variable (R : Type u) [CommRing R] (I : Ideal R) (P : Ideal R)


-- @@ L51-51 verbatim
local notation "q" => (Ideal.Quotient.mk P : R →+* (R ⧸ P))


-- @@ L53-55 verbatim
/-- The extended Rees algebra of the closed subscheme cut out by `P`. -/
abbrev quotientExtendedRees : Type u :=
  extendedRees (R ⧸ P) (I.map q)


-- @@ L57-59 verbatim
/-- The coefficientwise comparison map for the deformation of the closed subscheme. -/
def quotientExtendedReesHom : extendedRees R I →+* quotientExtendedRees R I P :=
  reesBaseChangeHom R I (R ⧸ P)


-- @@ L61-65 verbatim
@[simp]
theorem quotientExtendedReesHom_coe (f : extendedRees R I) :
    ((quotientExtendedReesHom R I P f : quotientExtendedRees R I P) :
        (R ⧸ P)[T;T⁻¹]) = mapLaurent q (f : R[T;T⁻¹]) :=
  rfl


-- @@ L67-78 verbatim
@[simp]
theorem quotientExtendedReesHom_C_mul_T (a : R) (n : ℤ)
    (ha : a ∈ I ^ n.toNat) :
    quotientExtendedReesHom R I P
        ⟨LaurentPolynomial.C a * T n, isExtendedRees_C_mul_T R I ha⟩ =
      ⟨LaurentPolynomial.C (q a) * T n,
        isExtendedRees_C_mul_T (R ⧸ P) (I.map q)
          (by
            rw [← Ideal.map_pow]
            exact Ideal.mem_map_of_mem q ha)⟩ := by
  apply Subtype.ext
  rw [quotientExtendedReesHom_coe, mapLaurent_C_mul_T]


-- @@ L80-99 verbatim
/-- The quotient comparison map is onto.  Its factorization through the tensor product
uses surjectivity of the coefficient quotient and of the canonical Rees tensor map. -/
theorem quotientExtendedReesHom_surjective :
    Function.Surjective (quotientExtendedReesHom R I P) := by
  have hleft : Function.Surjective
      (Algebra.TensorProduct.includeLeft :
        extendedRees R I →ₐ[R] (extendedRees R I) ⊗[R] (R ⧸ P)) :=
    Algebra.TensorProduct.includeLeft_surjective R (extendedRees R I) Ideal.Quotient.mk_surjective
  intro y
  obtain ⟨z, hz⟩ := reesTensorMap_surjective R I (R ⧸ P) y
  obtain ⟨x, rfl⟩ := hleft z
  refine ⟨x, ?_⟩
  rw [← hz]
  apply Subtype.ext
  change mapLaurent q (x : R[T;T⁻¹]) = _
  rw [coe_reesTensorMap]
  change mapLaurent q (x : R[T;T⁻¹]) =
    reesTensorToLaurent R I (R ⧸ P) (x ⊗ₜ[R] 1)
  rw [reesTensorToLaurent_tmul]
  simp


-- @@ L101-121 verbatim
/-- Exact kernel description for the deformation of a quotient: an extended-Rees element
vanishes precisely when every Laurent coefficient lies in `P`. -/
theorem quotientExtendedReesHom_mem_ker_iff (f : extendedRees R I) :
    f ∈ RingHom.ker (quotientExtendedReesHom R I P) ↔
      ∀ n : ℤ, (f : R[T;T⁻¹]).coeff n ∈ P := by
  constructor
  · intro hf n
    have hzero : mapLaurent q (f : R[T;T⁻¹]) = 0 := by
      have := congrArg Subtype.val hf
      exact this
    have hc := congrArg (fun z : (R ⧸ P)[T;T⁻¹] ↦ z.coeff n) hzero
    rw [coeff_mapLaurent] at hc
    exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using hc)
  · intro hf
    apply RingHom.mem_ker.mpr
    apply Subtype.ext
    change mapLaurent q (f : R[T;T⁻¹]) = 0
    refine AddMonoidAlgebra.ext fun n => ?_
    change (mapLaurent q (f : R[T;T⁻¹])).coeff n = 0
    rw [coeff_mapLaurent]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hf n)


-- @@ L123-133 verbatim
@[simp]
theorem quotientExtendedReesHom_parameter :
    quotientExtendedReesHom R I P (parameter R I) =
      parameter (R ⧸ P) (I.map q) := by
  apply Subtype.ext
  change mapLaurent q (T (-1)) = T (-1)
  calc
    mapLaurent q (T (-1)) =
        mapLaurent q (LaurentPolynomial.C (1 : R) * T (-1)) := by simp
    _ = LaurentPolynomial.C (q 1) * T (-1) := mapLaurent_C_mul_T q 1 (-1)
    _ = T (-1) := by simp


-- @@ L135-147 verbatim
/-- The map induced by the quotient comparison on the special fibres. -/
def quotientSpecialFibreMap :
    specialFibreRing R I →+* specialFibreRing (R ⧸ P) (I.map q) :=
  Ideal.quotientMap (parameterIdeal (R ⧸ P) (I.map q))
    (quotientExtendedReesHom R I P) (by
      rw [Ideal.span_le]
      intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst x
      change quotientExtendedReesHom R I P (parameter R I) ∈
        parameterIdeal (R ⧸ P) (I.map q)
      rw [quotientExtendedReesHom_parameter]
      exact Ideal.mem_span_singleton_self _)


-- @@ L149-153 verbatim
@[simp]
theorem quotientSpecialFibreMap_mk (f : extendedRees R I) :
    quotientSpecialFibreMap R I P (Ideal.Quotient.mk _ f) =
      Ideal.Quotient.mk _ (quotientExtendedReesHom R I P f) := by
  exact Ideal.quotientMap_mk


-- @@ L155-159 verbatim
/-- The induced map on special fibres is onto. -/
theorem quotientSpecialFibreMap_surjective :
    Function.Surjective (quotientSpecialFibreMap R I P) := by
  apply Ideal.quotientMap_surjective
  exact quotientExtendedReesHom_surjective R I P


-- @@ L161-165 verbatim
theorem quotientSpecialFibreMap_comp_mk :
    (quotientSpecialFibreMap R I P).comp (Ideal.Quotient.mk (parameterIdeal R I)) =
      (Ideal.Quotient.mk (parameterIdeal (R ⧸ P) (I.map q))).comp
        (quotientExtendedReesHom R I P) := by
  exact Ideal.quotientMap_comp_mk _


-- @@ L167-167 verbatim
/-! ### The actual deformation and normal-cone maps -/


-- @@ L169-173 verbatim
/-- The closed immersion of the deformation of `Spec (R ⧸ P)` into the deformation of `Spec R`.
The map is the spectrum of the coefficientwise extended-Rees quotient map. -/
def quotientDeformationMap :
    space (R ⧸ P) (I.map q) ⟶ space R I :=
  Spec.map (CommRingCat.ofHom (quotientExtendedReesHom R I P))


-- @@ L175-177 verbatim
instance quotientDeformationMap_isClosedImmersion :
    IsClosedImmersion (quotientDeformationMap R I P) :=
  IsClosedImmersion.spec_of_surjective _ (quotientExtendedReesHom_surjective R I P)


-- @@ L179-182 verbatim
/-- The closed immersion of the special fibre of the quotient deformation. -/
def quotientSpecialFibreSchemeMap :
    specialFibre (R ⧸ P) (I.map q) ⟶ specialFibre R I :=
  Spec.map (CommRingCat.ofHom (quotientSpecialFibreMap R I P))


-- @@ L184-186 verbatim
instance quotientSpecialFibreSchemeMap_isClosedImmersion :
    IsClosedImmersion (quotientSpecialFibreSchemeMap R I P) :=
  IsClosedImmersion.spec_of_surjective _ (quotientSpecialFibreMap_surjective R I P)


-- @@ L188-193 verbatim
/-- The normal-cone map obtained from the actual special-fibre quotient maps. -/
def quotientNormalConeMap :
    AffineNormalCone.scheme (R ⧸ P) (I.map q) ⟶ AffineNormalCone.scheme R I :=
  (normalConeIsoSpecialFibre (R ⧸ P) (I.map q)).hom ≫
    quotientSpecialFibreSchemeMap R I P ≫
    (normalConeIsoSpecialFibre R I).inv


-- @@ L195-198 verbatim
instance quotientNormalConeMap_isClosedImmersion :
    IsClosedImmersion (quotientNormalConeMap R I P) := by
  unfold quotientNormalConeMap
  infer_instance


-- @@ L200-208 verbatim
theorem quotientNormalConeMap_comp_normalConeι :
    quotientNormalConeMap R I P ≫ normalConeι R I =
      normalConeι (R ⧸ P) (I.map q) ≫ quotientDeformationMap R I P := by
  unfold quotientNormalConeMap normalConeι quotientSpecialFibreSchemeMap quotientDeformationMap
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  congr 1
  unfold specialFibreι
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, quotientSpecialFibreMap_comp_mk]


-- @@ L210-210 verbatim
/-! ### Generic fibre and Cartier parameter -/


-- @@ L212-215 verbatim
/-- The map on the generic trivial families `Spec (R ⧸ P)[t,t⁻¹] → Spec R[t,t⁻¹]`. -/
def quotientGenericFibreMap :
    genericFibre (R ⧸ P) ⟶ genericFibre R :=
  Spec.map (CommRingCat.ofHom (mapLaurent q))


-- @@ L217-223 verbatim
theorem quotientGenericFibreMap_comp_genericFibreι :
    quotientGenericFibreMap R P ≫ genericFibreι R I =
      genericFibreι (R ⧸ P) (I.map q) ≫ quotientDeformationMap R I P := by
  unfold quotientGenericFibreMap genericFibreι quotientDeformationMap
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  congr 1


-- @@ L225-225 verbatim
end Quotient


-- @@ L227-227 verbatim
end AffineDeformationSpace


-- @@ L229-229 verbatim
end


-- @@ L231-231 verbatim
end SchemeNormalCone.AlgebraicGeometry
