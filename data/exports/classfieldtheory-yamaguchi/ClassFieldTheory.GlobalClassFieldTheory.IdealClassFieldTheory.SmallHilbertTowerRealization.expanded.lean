/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldRealization
import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.SmallHilbertTowerConjugation
import Mathlib.Data.Rat.Cast.Defs


-- @@ L11-11 verbatim
set_option autoImplicit false


-- @@ L13-28 verbatim
/-!
# Actual realization of the two-stage small Hilbert tower

The first small Hilbert class field is the actual finite abelian
subextension selected in `HilbertClassFieldRealization`.  Over its actual
fixed field, the closed finite-index small-Hilbert norm subgroup has a
finite Galois norm neighbourhood.  We embed that neighbourhood in the
rational separable closure compatibly with the already chosen first
stage.  Finite abelian classification then selects the second small
Hilbert class field over the literal first-stage subgroup.

The compatibility of the embedding is essential: an unrelated chosen
copy of the middle number field would produce a class field over a
conjugate closed subgroup rather than over the first-stage subgroup
itself.
-/


-- @@ L30-30 verbatim
open scoped Classical NumberField


-- @@ L32-32 verbatim
noncomputable section


-- @@ L34-34 verbatim
namespace GlobalClassFieldTheory

-- @@ L35-35 verbatim
namespace IdealClassFieldTheory


-- @@ L37-37 verbatim
open AlgebraicNumberTheory

-- @@ L38-38 verbatim
open ClassFormation

-- @@ L39-39 verbatim
open CyclicCohomology

-- @@ L40-40 verbatim
open GlobalClassFields

-- @@ L41-41 verbatim
open KummerTheory

-- @@ L42-42 verbatim
open LocalClassFieldTheory

-- @@ L43-43 verbatim
open RamificationTheory

-- @@ L44-44 verbatim
open Reciprocity


-- @@ L46-52 verbatim
/-- The ordinary idèle-class operations used by the two-stage transport,
fixed at the canonical principal-subgroup quotient. -/
@[instance_reducible]
private noncomputable def smallHilbertTowerIdeleClassCommGroup
    (F : Type) [Field F] [NumberField F] :
    CommGroup (IdeleClassGroup F) :=
  QuotientGroup.Quotient.commGroup (IdeleGroup.principalSubgroup F)


-- @@ L54-54 verbatim
attribute [local instance] smallHilbertTowerIdeleClassCommGroup


-- @@ L56-61 verbatim
private theorem addSubgroup_comap_symm_eq_map
    {A B : Type*} [AddGroup A] [AddGroup B]
    (H : AddSubgroup A) (e : A ≃+ B) :
    H.comap e.symm.toAddMonoidHom =
      H.map e.toAddMonoidHom := by
  exact (AddSubgroup.map_equiv_eq_comap_symm e H).symm


-- @@ L63-72 verbatim
private noncomputable abbrev
    closedFiniteIndexNormAmbientCanonicalBaseAlgebra
    (F : Type) [Field F] [NumberField F]
    (H : Subgroup (IdeleClassGroup F))
    (hclosed : IsClosed (H : Set (IdeleClassGroup F)))
    [H.FiniteIndex] :
    Algebra F
      (closedFiniteIndexClassFieldNormAmbient
        (K := F) H hclosed) :=
  inferInstance


-- @@ L74-74 verbatim
section RationalFixedField


-- @@ L76-79 verbatim
variable
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field)


-- @@ L81-100 verbatim
private noncomputable abbrev smallHilbertTowerMiddleFiniteAbstractField :
    FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
  { field := L.field
    finite := by
      let : Finite
          ((baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
            extensionSubgroup
              (baseField
                (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
              K.field (le_baseField K.field)) :=
        K.finite
      let : Finite
          (K.field.toSubgroup ⧸
            extensionSubgroup K.field L.field L.below) :=
        L.finite
      exact
        FiniteGaloisSubextension.finite_extension_trans
          L.below (le_baseField K.field) }


-- @@ L102-103 verbatim
local notation "E" =>
  abstractFixedField ℚ (SeparableClosure ℚ) L.field


-- @@ L105-106 verbatim
local notation "N" =>
  smallHilbertClassFieldNormAmbient E


-- @@ L108-117 verbatim
private noncomputable instance
    smallHilbertTowerMiddleAbstractQuotientFinite :
    Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          L.field (le_baseField L.field)) :=
  (smallHilbertTowerMiddleFiniteAbstractField K L).finite


-- @@ L119-123 verbatim
private noncomputable instance
    smallHilbertTowerMiddleFiniteDimensional :
    FiniteDimensional ℚ E :=
  abstractFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ) L.field inferInstance


-- @@ L125-128 verbatim
private noncomputable instance
    smallHilbertTowerMiddleNumberField :
    NumberField E :=
  NumberField.of_module_finite ℚ E


-- @@ L130-140 verbatim
/-- The canonical small-Hilbert subgroup over the literal middle field.
This typed endpoint avoids repeatedly reducing the finite-abstract-field
package merely to recover its `field = L.field` projection. -/
noncomputable def smallHilbertTowerMiddleNormSubgroup :
    AddSubgroup
      (ambientFixedAddSubgroup
        rationalIdeleClassRepresentation L.field) :=
  (smallHilbertClassFieldNormSubgroup (K := E)).toAddSubgroup.comap
    (rationalAbstractFixedFieldIdeleClassEquivFixed
      L.field
      (hfinite := smallHilbertTowerMiddleAbstractQuotientFinite K L)).symm.toAddMonoidHom


-- @@ L142-153 verbatim
/-- The typed `comap` endpoint is the canonical transported `map` endpoint.
This uses only the generic additive equivalence law. -/
theorem smallHilbertTowerMiddleNormSubgroup_eq_map :
    smallHilbertTowerMiddleNormSubgroup K L =
      (smallHilbertClassFieldNormSubgroup (K := E)).toAddSubgroup.map
        (rationalAbstractFixedFieldIdeleClassEquivFixed
          L.field
          (hfinite := smallHilbertTowerMiddleAbstractQuotientFinite K L)).toAddMonoidHom := by
  exact addSubgroup_comap_symm_eq_map
    (smallHilbertClassFieldNormSubgroup (K := E)).toAddSubgroup
    (rationalAbstractFixedFieldIdeleClassEquivFixed L.field
      (hfinite := smallHilbertTowerMiddleAbstractQuotientFinite K L))


-- @@ L155-161 verbatim
@[reducible]
private noncomputable def
    smallHilbertTowerNormAmbientAlgebra :
    Algebra E N :=
  closedFiniteIndexNormAmbientCanonicalBaseAlgebra E
    (smallHilbertClassFieldNormSubgroup (K := E))
    (smallHilbertClassFieldNormSubgroup_isClosed (K := E))


-- @@ L163-163 verbatim
attribute [local instance] smallHilbertTowerNormAmbientAlgebra


-- @@ L165-170 verbatim
@[reducible]
private noncomputable def
    smallHilbertTowerNormAmbientSMul :
    SMul E N :=
  Algebra.toSMul
    (self := smallHilbertTowerNormAmbientAlgebra K L)


-- @@ L172-177 verbatim
@[reducible]
private noncomputable def
    smallHilbertTowerNormAmbientModule :
    Module E N :=
  @Algebra.toModule E N _ _
    (smallHilbertTowerNormAmbientAlgebra K L)


-- @@ L179-188 verbatim
private theorem
    smallHilbertTowerNormAmbientScalarTower :
    @IsScalarTower ℚ E N
      (Algebra.toSMul (R := ℚ) (A := E))
      (smallHilbertTowerNormAmbientSMul K L)
      (Algebra.toSMul (R := ℚ) (A := N)) := by
  exact IsScalarTower.of_algebraMap_eq'
    (R := ℚ) (S := E) (A := N)
    (RingHom.ext_rat (algebraMap ℚ N)
      ((algebraMap E N).comp (algebraMap ℚ E)))


-- @@ L190-198 verbatim
private noncomputable def
    smallHilbertTowerNormAmbientAlgHom :
    E →ₐ[ℚ] N :=
  { toRingHom := algebraMap E N
    commutes' := fun r =>
      (RingHom.congr_fun
        (RingHom.ext_rat
          ((algebraMap E N).comp (algebraMap ℚ E))
          (algebraMap ℚ N)) r) }


-- @@ L200-204 verbatim
private theorem smallHilbertTowerNormAmbientAlgHom_apply
    (x : E) :
    smallHilbertTowerNormAmbientAlgHom K L x =
      algebraMap E N x := by
  rfl


-- @@ L206-214 verbatim
private theorem
    smallHilbertTowerNormAmbientIsGalois :
    IsGalois E N := by
  unfold smallHilbertClassFieldNormAmbient
    closedFiniteIndexClassFieldNormAmbient
  exact
    closedFiniteIndexNormAmbientIsGalois
      (smallHilbertClassFieldNormSubgroup (K := E))
      (smallHilbertClassFieldNormSubgroup_isClosed (K := E))


-- @@ L216-216 verbatim
attribute [local instance] smallHilbertTowerNormAmbientIsGalois


-- @@ L218-229 verbatim
private noncomputable def
    smallHilbertNormNeighborhoodForwardAlignment :
    SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ := by
  let j₀ : N →ₐ[ℚ] SeparableClosure ℚ :=
    numberFieldSeparableClosureEmbedding N
  let i₀ : E →ₐ[ℚ] SeparableClosure ℚ :=
    j₀.comp (smallHilbertTowerNormAmbientAlgHom K L)
  exact
    AlgEquiv.ofBijective
      (i₀.liftNormal (SeparableClosure ℚ))
      (AlgHom.normal_bijective
        ℚ (SeparableClosure ℚ) (SeparableClosure ℚ) _)


-- @@ L231-237 verbatim
/-- The separable-closure automorphism which aligns an arbitrary chosen
embedding of the norm-neighbourhood field with the already embedded
middle field. -/
private noncomputable def
    smallHilbertNormNeighborhoodAlignment :
    SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ :=
  (smallHilbertNormNeighborhoodForwardAlignment K L).symm


-- @@ L239-262 verbatim
@[simp]
private theorem smallHilbertNormNeighborhoodForwardAlignment_apply
    (x : E) :
    smallHilbertNormNeighborhoodForwardAlignment K L
        (x : SeparableClosure ℚ) =
      (numberFieldSeparableClosureEmbedding N)
        (algebraMap E N x) := by
  let j₀ : N →ₐ[ℚ] SeparableClosure ℚ :=
    numberFieldSeparableClosureEmbedding N
  let i₀ : E →ₐ[ℚ] SeparableClosure ℚ :=
    j₀.comp (smallHilbertTowerNormAmbientAlgHom K L)
  dsimp only [smallHilbertNormNeighborhoodForwardAlignment,
    AlgEquiv.ofBijective_apply]
  calc
    _ = i₀ x := by
      simpa only [IntermediateField.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply] using
        i₀.liftNormal_commutes (SeparableClosure ℚ) x
    _ = j₀ (algebraMap E N x) := by
      change
        j₀ (smallHilbertTowerNormAmbientAlgHom K L x) =
          j₀ (algebraMap E N x)
      exact congrArg j₀
        (smallHilbertTowerNormAmbientAlgHom_apply K L x)


-- @@ L264-271 verbatim
/-- A controlled embedding of the concrete finite Galois norm
neighbourhood.  Its restriction to the middle field is the literal
inclusion of that fixed field in `SeparableClosure ℚ`. -/
private noncomputable def
    smallHilbertNormNeighborhoodEmbedding :
    N →ₐ[ℚ] SeparableClosure ℚ :=
  (smallHilbertNormNeighborhoodAlignment K L).toAlgHom.comp
    (numberFieldSeparableClosureEmbedding N)


-- @@ L273-286 verbatim
@[simp]
private theorem smallHilbertNormNeighborhoodEmbedding_algebraMap
    (x : E) :
    smallHilbertNormNeighborhoodEmbedding K L
        (algebraMap E N x) =
      (x : SeparableClosure ℚ) := by
  change
    (smallHilbertNormNeighborhoodForwardAlignment K L).symm
        ((numberFieldSeparableClosureEmbedding N)
          (algebraMap E N x)) =
      (x : SeparableClosure ℚ)
  rw [← smallHilbertNormNeighborhoodForwardAlignment_apply K L x]
  exact
    (smallHilbertNormNeighborhoodForwardAlignment K L).symm_apply_apply _


-- @@ L288-294 verbatim
private abbrev smallHilbertNormNeighborhoodEmbeddedBase :
    ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
  closedFixingSubgroup ℚ (SeparableClosure ℚ)
    (AlgHom.fieldRange
      ((smallHilbertNormNeighborhoodEmbedding K L).comp
        (smallHilbertTowerNormAmbientAlgHom K L)))


-- @@ L296-301 verbatim
private abbrev smallHilbertNormNeighborhoodEmbeddedField :
    ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
  closedFixingSubgroup ℚ (SeparableClosure ℚ)
    (AlgHom.fieldRange
      (smallHilbertNormNeighborhoodEmbedding K L))


-- @@ L303-319 verbatim
private theorem smallHilbertNormNeighborhoodEmbeddedField_le_base :
    (smallHilbertNormNeighborhoodEmbeddedField K L).toSubgroup ≤
      (smallHilbertNormNeighborhoodEmbeddedBase K L).toSubgroup := by
  change
    (AlgHom.fieldRange
        (smallHilbertNormNeighborhoodEmbedding K L)).fixingSubgroup ≤
      (AlgHom.fieldRange
        ((smallHilbertNormNeighborhoodEmbedding K L).comp
          (smallHilbertTowerNormAmbientAlgHom K L))).fixingSubgroup
  apply
    (AlgHom.fieldRange
      ((smallHilbertNormNeighborhoodEmbedding K L).comp
        (smallHilbertTowerNormAmbientAlgHom K L))).fixingSubgroup_le
  exact
    AlgHom.range_comp_le_range
      (smallHilbertTowerNormAmbientAlgHom K L)
      (smallHilbertNormNeighborhoodEmbedding K L)


-- @@ L321-342 verbatim
private theorem smallHilbertNormNeighborhoodEmbeddedBase_eq :
    smallHilbertNormNeighborhoodEmbeddedBase K L = L.field := by
  have hi :
      (smallHilbertNormNeighborhoodEmbedding K L).comp
          (smallHilbertTowerNormAmbientAlgHom K L) =
        (abstractFixedField ℚ (SeparableClosure ℚ) L.field).val := by
    apply AlgHom.ext
    intro x
    change smallHilbertNormNeighborhoodEmbedding K L
      (smallHilbertTowerNormAmbientAlgHom K L x) = (x : SeparableClosure ℚ)
    rw [smallHilbertTowerNormAmbientAlgHom_apply K L x]
    exact smallHilbertNormNeighborhoodEmbedding_algebraMap K L x
  change
    closedFixingSubgroup ℚ (SeparableClosure ℚ)
        (AlgHom.fieldRange
          ((smallHilbertNormNeighborhoodEmbedding K L).comp
            (smallHilbertTowerNormAmbientAlgHom K L))) =
      L.field
  rw [hi, IntermediateField.fieldRange_val]
  exact
    closedFixingSubgroup_abstractFixedField_eq
      ℚ (SeparableClosure ℚ) L.field


-- @@ L344-363 verbatim
private noncomputable def
    smallHilbertNormNeighborhoodSeparableClosureEquiv :
    let j := smallHilbertNormNeighborhoodEmbedding K L
    let i := j.comp (smallHilbertTowerNormAmbientAlgHom K L)
    let : Algebra E (SeparableClosure ℚ) :=
      i.toRingHom.toAlgebra
    SeparableClosure E ≃ₐ[E] SeparableClosure ℚ := by
  intro j i alg
  let : @IsScalarTower ℚ E (SeparableClosure ℚ)
      (Algebra.toSMul (R := ℚ) (A := E))
      alg.toSMul
      (Algebra.toSMul (R := ℚ) (A := SeparableClosure ℚ)) :=
    IsScalarTower.of_algebraMap_eq' i.comp_algebraMap.symm
  let : IsSepClosure E (SeparableClosure ℚ) :=
    ⟨IsSepClosure.sep_closed ℚ,
      Algebra.isSeparable_tower_top_of_isSeparable
        ℚ E (SeparableClosure ℚ)⟩
  exact
    IsSepClosure.equiv E
      (SeparableClosure E) (SeparableClosure ℚ)


-- @@ L365-403 verbatim
private noncomputable def
    smallHilbertFiniteGaloisNormNeighborhoodRaw :
    FiniteGaloisSubextension
      (smallHilbertNormNeighborhoodEmbeddedBase K L) := by
  let : @IsScalarTower ℚ E N
      (Algebra.toSMul (R := ℚ) (A := E))
      (smallHilbertTowerNormAmbientSMul K L)
      (Algebra.toSMul (R := ℚ) (A := N)) :=
    smallHilbertTowerNormAmbientScalarTower K L
  let j : N →ₐ[ℚ] SeparableClosure ℚ :=
    smallHilbertNormNeighborhoodEmbedding K L
  let i : E →ₐ[ℚ] SeparableClosure ℚ :=
    j.comp (IsScalarTower.toAlgHom ℚ E N)
  let B : ClosedSubgroup (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
    closedFixingSubgroup ℚ (SeparableClosure ℚ) i.fieldRange
  let T : ClosedSubgroup (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
    smallHilbertNormNeighborhoodEmbeddedField K L
  have hTB : T.toSubgroup ≤ B.toSubgroup := by
    change j.fieldRange.fixingSubgroup ≤ i.fieldRange.fixingSubgroup
    apply i.fieldRange.fixingSubgroup_le
    exact AlgHom.range_comp_le_range (IsScalarTower.toAlgHom ℚ E N) j
  let raw : FiniteGaloisSubextension B := {
    field := T
    below := hTB
    normal := ambientEmbeddedExtensionSubgroup_normal ℚ E N j
      (smallHilbertNormNeighborhoodSeparableClosureEquiv K L)
    finite := ambientEmbeddedExtensionQuotient_finite ℚ E N j
      (smallHilbertNormNeighborhoodSeparableClosureEquiv K L) }
  have hi : IsScalarTower.toAlgHom ℚ E N =
      smallHilbertTowerNormAmbientAlgHom K L := by
    apply AlgHom.ext
    intro x
    exact (IsScalarTower.toAlgHom_apply ℚ E N x).trans
      (smallHilbertTowerNormAmbientAlgHom_apply K L x).symm
  have hB : B = smallHilbertNormNeighborhoodEmbeddedBase K L :=
    congrArg
      (fun f : E →ₐ[ℚ] N =>
        closedFixingSubgroup ℚ (SeparableClosure ℚ) (j.comp f).fieldRange) hi
  exact hB ▸ raw


-- @@ L405-410 verbatim
private noncomputable def rebaseFiniteGaloisSubextension
    {G : Type} [Group G] [TopologicalSpace G]
    {B B' : ClosedSubgroup G} (h : B = B')
    (P : FiniteGaloisSubextension B) :
    FiniteGaloisSubextension B' :=
  h ▸ P


-- @@ L412-419 verbatim
@[simp]
private theorem rebaseFiniteGaloisSubextension_field
    {G : Type} [Group G] [TopologicalSpace G]
    {B B' : ClosedSubgroup G} (h : B = B')
    (P : FiniteGaloisSubextension B) :
    (rebaseFiniteGaloisSubextension h P).field = P.field := by
  cases h
  rfl


-- @@ L421-431 verbatim
private theorem
    rebaseRationalFiniteGaloisSubextension_fixedField_eq
    {B B' : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)}
    (h : B = B') (P : FiniteGaloisSubextension B) :
    (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
      (rebaseFiniteGaloisSubextension h P).below).restrictScalars ℚ =
        (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
          P.below).restrictScalars ℚ := by
  cases h
  rfl


-- @@ L433-440 verbatim
/-- An actual finite Galois norm neighbourhood over the literal
first-stage subgroup.  It is produced by the finite-index Kummer
construction and the controlled embedding above. -/
noncomputable def smallHilbertFiniteGaloisNormNeighborhood :
    FiniteGaloisSubextension L.field :=
  rebaseFiniteGaloisSubextension
    (smallHilbertNormNeighborhoodEmbeddedBase_eq K L)
    (smallHilbertFiniteGaloisNormNeighborhoodRaw K L)


-- @@ L442-449 verbatim
/-- The abstract norm subgroup of the chosen neighbourhood, pinned to the
literal middle-field carrier. -/
noncomputable def smallHilbertFiniteGaloisNormNeighborhoodNormSubgroup :
    AddSubgroup
      (ambientFixedAddSubgroup
        rationalIdeleClassRepresentation L.field) :=
  (smallHilbertFiniteGaloisNormNeighborhood K L).normSubgroup
    rationalIdeleClassRepresentation


-- @@ L451-454 verbatim
private noncomputable abbrev
    smallHilbertFiniteGaloisNormNeighborhoodTopField : Type :=
  abstractRelativeFixedField ℚ (SeparableClosure ℚ)
    (smallHilbertFiniteGaloisNormNeighborhood K L).below


-- @@ L456-457 verbatim
local notation "E₂" =>
  smallHilbertFiniteGaloisNormNeighborhoodTopField K L


-- @@ L459-466 verbatim
private noncomputable instance
    smallHilbertFiniteGaloisNormNeighborhoodQuotientFinite :
    Finite
      (L.field.toSubgroup ⧸
        extensionSubgroup L.field
          (smallHilbertFiniteGaloisNormNeighborhood K L).field
          (smallHilbertFiniteGaloisNormNeighborhood K L).below) :=
  (smallHilbertFiniteGaloisNormNeighborhood K L).finite


-- @@ L468-475 verbatim
private noncomputable instance
    smallHilbertFiniteGaloisNormNeighborhoodFiniteDimensional :
    FiniteDimensional E E₂ :=
  abstractRelativeFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ) L.field
    (smallHilbertFiniteGaloisNormNeighborhood K L).field
    (smallHilbertFiniteGaloisNormNeighborhood K L).below
    inferInstance inferInstance


-- @@ L477-480 verbatim
private noncomputable instance
    smallHilbertFiniteGaloisNormNeighborhoodScalarTower :
    IsScalarTower ℚ E E₂ :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)


-- @@ L482-485 verbatim
private noncomputable instance
    smallHilbertFiniteGaloisNormNeighborhoodAbsoluteFiniteDimensional :
    FiniteDimensional ℚ E₂ :=
  FiniteDimensional.trans ℚ E E₂


-- @@ L487-490 verbatim
private noncomputable instance
    smallHilbertFiniteGaloisNormNeighborhoodNumberField :
    NumberField E₂ :=
  NumberField.of_module_finite ℚ E₂


-- @@ L492-499 verbatim
private noncomputable instance
    smallHilbertFiniteGaloisNormNeighborhoodIsGalois :
    IsGalois E E₂ :=
  abstractRelativeFixedField_isGalois
    ℚ (SeparableClosure ℚ) L.field
    (smallHilbertFiniteGaloisNormNeighborhood K L).field
    (smallHilbertFiniteGaloisNormNeighborhood K L).below
    (smallHilbertFiniteGaloisNormNeighborhood K L).normal


-- @@ L501-519 verbatim
private theorem
    smallHilbertFiniteGaloisNormNeighborhood_fixedField_eq_range :
    (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
      (smallHilbertFiniteGaloisNormNeighborhood K L).below).restrictScalars ℚ =
        AlgHom.fieldRange
          (smallHilbertNormNeighborhoodEmbedding K L) := by
  rw [show
    (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
      (smallHilbertFiniteGaloisNormNeighborhood K L).below).restrictScalars ℚ =
        (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
          (smallHilbertFiniteGaloisNormNeighborhoodRaw K L).below).restrictScalars ℚ
    from
      rebaseRationalFiniteGaloisSubextension_fixedField_eq
        (smallHilbertNormNeighborhoodEmbeddedBase_eq K L)
        (smallHilbertFiniteGaloisNormNeighborhoodRaw K L)]
  exact
    InfiniteGalois.fixedField_fixingSubgroup
      (AlgHom.fieldRange
        (smallHilbertNormNeighborhoodEmbedding K L))


-- @@ L521-529 verbatim
private noncomputable def
    smallHilbertFiniteGaloisNormNeighborhoodTopEquiv :
    N ≃ₐ[ℚ]
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (smallHilbertFiniteGaloisNormNeighborhood K L).below).restrictScalars ℚ :=
  (smallHilbertNormNeighborhoodEmbedding K L).equivFieldRange.trans
    (IntermediateField.equivOfEq
      (smallHilbertFiniteGaloisNormNeighborhood_fixedField_eq_range
        K L).symm)


-- @@ L531-544 verbatim
@[simp]
private theorem
    smallHilbertFiniteGaloisNormNeighborhoodTopEquiv_algebraMap
    (x : E) :
    smallHilbertFiniteGaloisNormNeighborhoodTopEquiv K L
        (algebraMap E N x) =
      algebraMap E
        E₂ x := by
  apply Subtype.ext
  change
    smallHilbertNormNeighborhoodEmbedding K L
        (algebraMap E N x) =
      (x : SeparableClosure ℚ)
  exact smallHilbertNormNeighborhoodEmbedding_algebraMap K L x


-- @@ L546-552 verbatim
private noncomputable def
    smallHilbertFiniteGaloisNormNeighborhoodRelativeTopEquiv :
    N ≃ₐ[E] E₂ := {
  smallHilbertFiniteGaloisNormNeighborhoodTopEquiv K L with
  commutes' := fun x =>
    smallHilbertFiniteGaloisNormNeighborhoodTopEquiv_algebraMap
      K L x }


-- @@ L554-561 verbatim
private theorem
    smallHilbertFiniteGaloisNormNeighborhood_ordinaryNorm_le :
    (_root_.ideleClassNorm E N).range ≤
      smallHilbertClassFieldNormSubgroup (K := E) := by
  simpa only [smallHilbertClassFieldNormAmbient] using
    (closedFiniteIndexClassFieldNormAmbient_normRange_le
      (K := E) (smallHilbertClassFieldNormSubgroup (K := E))
      (smallHilbertClassFieldNormSubgroup_isClosed (K := E)))


-- @@ L563-571 verbatim
private theorem
    smallHilbertFiniteGaloisNormNeighborhood_ordinaryNormRange_eq :
    (_root_.ideleClassNorm E N).range =
      (_root_.ideleClassNorm E E₂).range := by
  simpa only [ordinaryIdeleClassNorm_range_eq_relative] using
    (ideleClassNorm_range_algEquiv
      (K := E)
      (smallHilbertFiniteGaloisNormNeighborhoodRelativeTopEquiv
        K L)).symm


-- @@ L573-595 verbatim
private theorem
    smallHilbertFiniteGaloisNormNeighborhood_abstractNormMap_eq :
    ((smallHilbertFiniteGaloisNormNeighborhood K L).normSubgroup
        rationalIdeleClassRepresentation).map
          (rationalAbstractFixedFieldIdeleClassEquivFixed
            L.field
            (hfinite := smallHilbertTowerMiddleAbstractQuotientFinite K L)).symm.toAddMonoidHom =
      (_root_.ideleClassNorm E E₂).range.toAddSubgroup := by
  change
    (finiteNormSubgroup rationalIdeleClassRepresentation
      L.field
      (smallHilbertFiniteGaloisNormNeighborhood K L).field
      (smallHilbertFiniteGaloisNormNeighborhood K L).below).map
        (rationalAbstractFixedFieldIdeleClassEquivFixed
          L.field
          (hfinite := smallHilbertTowerMiddleAbstractQuotientFinite K L)).symm.toAddMonoidHom =
      (_root_.ideleClassNorm E E₂).range.toAddSubgroup
  exact
    (map_rationalFiniteNormSubgroup_eq_ordinaryIdeleClassNormRange_concrete
      L.field
      (smallHilbertFiniteGaloisNormNeighborhood K L).field
      (smallHilbertFiniteGaloisNormNeighborhood K L).below
      (smallHilbertFiniteGaloisNormNeighborhood K L).normal)


-- @@ L597-610 verbatim
/-- The abstract norm map lands directly in the ordinary norm range of the
chosen neighbourhood.  Composing the two named subgroup equalities here
keeps downstream membership proofs pointwise. -/
private theorem
    smallHilbertFiniteGaloisNormNeighborhood_abstractNormMap_eq_ordinaryNormRange :
    ((smallHilbertFiniteGaloisNormNeighborhood K L).normSubgroup
        rationalIdeleClassRepresentation).map
          (rationalAbstractFixedFieldIdeleClassEquivFixed
            L.field
            (hfinite := smallHilbertTowerMiddleAbstractQuotientFinite K L)).symm.toAddMonoidHom =
      (_root_.ideleClassNorm E N).range.toAddSubgroup :=
  (smallHilbertFiniteGaloisNormNeighborhood_abstractNormMap_eq K L).trans
    (congrArg Subgroup.toAddSubgroup
      (smallHilbertFiniteGaloisNormNeighborhood_ordinaryNormRange_eq K L).symm)


-- @@ L612-625 verbatim
/-- Pointwise form of the combined norm-range equality. -/
private theorem
    smallHilbertFiniteGaloisNormNeighborhood_abstractNormMap_mem_ordinaryNormRange
    (a : Additive (IdeleClassGroup E))
    (ha :
      a ∈ ((smallHilbertFiniteGaloisNormNeighborhood K L).normSubgroup
        rationalIdeleClassRepresentation).map
          (rationalAbstractFixedFieldIdeleClassEquivFixed
            L.field
            (hfinite := smallHilbertTowerMiddleAbstractQuotientFinite K L)).symm.toAddMonoidHom) :
    a ∈ (_root_.ideleClassNorm E N).range.toAddSubgroup :=
  (le_of_eq
    (smallHilbertFiniteGaloisNormNeighborhood_abstractNormMap_eq_ordinaryNormRange
      K L)) ha


-- @@ L627-656 verbatim
/-- The actual finite Galois norm neighbourhood has abstract norm
subgroup contained in the canonical small-Hilbert subgroup of the
middle fixed field.  This is the source-producing norm-topology input;
no norm-openness premise is assumed. -/
theorem smallHilbertFiniteGaloisNormNeighborhood_normSubgroup_le :
    ∀ a : ambientFixedAddSubgroup
        rationalIdeleClassRepresentation L.field,
      a ∈ smallHilbertFiniteGaloisNormNeighborhoodNormSubgroup K L →
        a ∈ smallHilbertTowerMiddleNormSubgroup K L := by
  intro a ha
  change
    a ∈ (smallHilbertFiniteGaloisNormNeighborhood K L).normSubgroup
      rationalIdeleClassRepresentation at ha
  have haMap :
      (rationalAbstractFixedFieldIdeleClassEquivFixed
          L.field
          (hfinite := smallHilbertTowerMiddleAbstractQuotientFinite K L)).symm a ∈
        ((smallHilbertFiniteGaloisNormNeighborhood K L).normSubgroup
          rationalIdeleClassRepresentation).map
            (rationalAbstractFixedFieldIdeleClassEquivFixed
              L.field
              (hfinite := smallHilbertTowerMiddleAbstractQuotientFinite K L)).symm.toAddMonoidHom :=
    ⟨a, ha, rfl⟩
  have haOrdinary :
      (rationalAbstractFixedFieldIdeleClassEquivFixed L.field
        (hfinite := smallHilbertTowerMiddleAbstractQuotientFinite K L)).symm a ∈
        (_root_.ideleClassNorm E N).range.toAddSubgroup :=
    smallHilbertFiniteGaloisNormNeighborhood_abstractNormMap_mem_ordinaryNormRange
      K L _ haMap
  exact smallHilbertFiniteGaloisNormNeighborhood_ordinaryNorm_le K L haOrdinary


-- @@ L658-672 verbatim
/-- The canonical small-Hilbert subgroup of the actual middle fixed
field is open in the genuine norm topology. -/
theorem smallHilbertNormSubgroupInRationalClassFormation_isNormOpen :
    IsNormOpen rationalIdeleClassRepresentation L.field
      (smallHilbertTowerMiddleNormSubgroup K L :
        Set
          (ambientFixedAddSubgroup
            rationalIdeleClassRepresentation L.field)) := by
  rw [normTopology_addSubgroup_isOpen_iff]
  refine
    ⟨smallHilbertFiniteGaloisNormNeighborhood K L, ?_⟩
  change
    smallHilbertFiniteGaloisNormNeighborhoodNormSubgroup K L ≤
      smallHilbertTowerMiddleNormSubgroup K L
  exact smallHilbertFiniteGaloisNormNeighborhood_normSubgroup_le K L


-- @@ L674-687 verbatim
/-- The second small Hilbert class field as an actual finite abelian
subextension of the literal first-stage field. -/
noncomputable def secondSmallHilbertClassFieldSubextension :
    FiniteAbelianSubextension L.field := by
  let H : FiniteAbelianSubextension.NormOpenAddSubgroup
      rationalIdeleClassRepresentation L.field :=
    ⟨smallHilbertTowerMiddleNormSubgroup K L,
      smallHilbertNormSubgroupInRationalClassFormation_isNormOpen K L⟩
  exact
    Classical.choose
      (FiniteAbelianSubextension.normSubgroupMap_surjective
        rationalCyclotomicIdeleClassValuationData
        rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
        (smallHilbertTowerMiddleFiniteAbstractField K L) H)


-- @@ L689-706 verbatim
/-- The second-stage extension realizes exactly the canonical
small-Hilbert norm subgroup of the actual middle field. -/
@[simp]
theorem secondSmallHilbertClassFieldSubextension_normSubgroup :
    (secondSmallHilbertClassFieldSubextension K L).normSubgroup
        rationalIdeleClassRepresentation =
      smallHilbertTowerMiddleNormSubgroup K L := by
  let H : FiniteAbelianSubextension.NormOpenAddSubgroup
      rationalIdeleClassRepresentation L.field :=
    ⟨smallHilbertTowerMiddleNormSubgroup K L,
      smallHilbertNormSubgroupInRationalClassFormation_isNormOpen K L⟩
  have h :=
    Classical.choose_spec
      (FiniteAbelianSubextension.normSubgroupMap_surjective
        rationalCyclotomicIdeleClassValuationData
        rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
        (smallHilbertTowerMiddleFiniteAbstractField K L) H)
  exact congrArg Subtype.val h


-- @@ L708-710 verbatim
private noncomputable abbrev secondSmallHilbertClassFieldTopField : Type :=
  abstractRelativeFixedField ℚ (SeparableClosure ℚ)
    (secondSmallHilbertClassFieldSubextension K L).below


-- @@ L712-712 verbatim
local notation "T₂" => secondSmallHilbertClassFieldTopField K L


-- @@ L714-721 verbatim
private noncomputable instance
    secondSmallHilbertClassFieldSubextensionQuotientFinite :
    Finite
      (L.field.toSubgroup ⧸
        extensionSubgroup L.field
          (secondSmallHilbertClassFieldSubextension K L).field
          (secondSmallHilbertClassFieldSubextension K L).below) :=
  (secondSmallHilbertClassFieldSubextension K L).finite


-- @@ L723-730 verbatim
private noncomputable instance
    secondSmallHilbertClassFieldTopFiniteDimensional :
    FiniteDimensional E T₂ :=
  abstractRelativeFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ) L.field
    (secondSmallHilbertClassFieldSubextension K L).field
    (secondSmallHilbertClassFieldSubextension K L).below
    inferInstance inferInstance


-- @@ L732-735 verbatim
private noncomputable instance
    secondSmallHilbertClassFieldTopScalarTower :
    IsScalarTower ℚ E T₂ :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)


-- @@ L737-740 verbatim
private noncomputable instance
    secondSmallHilbertClassFieldTopAbsoluteFiniteDimensional :
    FiniteDimensional ℚ T₂ :=
  FiniteDimensional.trans ℚ E T₂


-- @@ L742-745 verbatim
private noncomputable instance
    secondSmallHilbertClassFieldTopNumberField :
    NumberField T₂ :=
  NumberField.of_module_finite ℚ T₂


-- @@ L747-754 verbatim
private noncomputable instance
    secondSmallHilbertClassFieldTopIsGalois :
    IsGalois E T₂ :=
  abstractRelativeFixedField_isGalois
    ℚ (SeparableClosure ℚ) L.field
    (secondSmallHilbertClassFieldSubextension K L).field
    (secondSmallHilbertClassFieldSubextension K L).below
    (secondSmallHilbertClassFieldSubextension K L).normal


-- @@ L756-778 verbatim
private theorem
    secondSmallHilbertClassFieldSubextension_abstractNormMap_eq_actualNormRange :
    ((secondSmallHilbertClassFieldSubextension K L).normSubgroup
        rationalIdeleClassRepresentation).map
          (rationalAbstractFixedFieldIdeleClassEquivFixed
            L.field
            (hfinite := smallHilbertTowerMiddleAbstractQuotientFinite K L)).symm.toAddMonoidHom =
      (_root_.ideleClassNorm E T₂).range.toAddSubgroup := by
  change
    (finiteNormSubgroup rationalIdeleClassRepresentation
        L.field
        (secondSmallHilbertClassFieldSubextension K L).field
        (secondSmallHilbertClassFieldSubextension K L).below).map
          (rationalAbstractFixedFieldIdeleClassEquivFixed
            L.field
            (hfinite := smallHilbertTowerMiddleAbstractQuotientFinite K L)).symm.toAddMonoidHom =
      (_root_.ideleClassNorm E T₂).range.toAddSubgroup
  exact
    map_rationalFiniteNormSubgroup_eq_ordinaryIdeleClassNormRange_concrete
      L.field
      (secondSmallHilbertClassFieldSubextension K L).field
      (secondSmallHilbertClassFieldSubextension K L).below
      (secondSmallHilbertClassFieldSubextension K L).normal


-- @@ L780-805 verbatim
private theorem
    secondSmallHilbertClassFieldSubextension_abstractNormMap_eq_smallHilbertNormSubgroup :
    ((secondSmallHilbertClassFieldSubextension K L).normSubgroup
        rationalIdeleClassRepresentation).map
          (rationalAbstractFixedFieldIdeleClassEquivFixed
            L.field
            (hfinite := smallHilbertTowerMiddleAbstractQuotientFinite K L)).symm.toAddMonoidHom =
      (smallHilbertClassFieldNormSubgroup (K := E)).toAddSubgroup := by
  let e : Additive (IdeleClassGroup E) ≃+
      ambientFixedAddSubgroup rationalIdeleClassRepresentation L.field :=
    rationalAbstractFixedFieldIdeleClassEquivFixed L.field
      (hfinite := smallHilbertTowerMiddleAbstractQuotientFinite K L)
  let H : AddSubgroup (Additive (IdeleClassGroup E)) :=
    (smallHilbertClassFieldNormSubgroup (K := E)).toAddSubgroup
  let back : AddSubgroup
      (ambientFixedAddSubgroup rationalIdeleClassRepresentation L.field) →
      AddSubgroup (Additive (IdeleClassGroup E)) :=
    fun n => n.map e.symm.toAddMonoidHom
  have hNorm :
      back ((secondSmallHilbertClassFieldSubextension K L).normSubgroup
        rationalIdeleClassRepresentation) =
      back (smallHilbertTowerMiddleNormSubgroup K L) :=
    congrArg back (secondSmallHilbertClassFieldSubextension_normSubgroup K L)
  have hCancel : back (smallHilbertTowerMiddleNormSubgroup K L) = H :=
    AddSubgroup.map_comap_eq_self_of_surjective e.symm.surjective H
  exact hNorm.trans hCancel


-- @@ L807-818 verbatim
/-- The actual second small Hilbert class field has exactly the intrinsic
small-Hilbert norm range over the literal middle fixed field. -/
@[simp]
theorem secondSmallHilbertClassFieldSubextension_ideleClassNorm_range :
    (_root_.ideleClassNorm E T₂).range =
      smallHilbertClassFieldNormSubgroup (K := E) := by
  apply Subgroup.toAddSubgroup.injective
  exact
    (secondSmallHilbertClassFieldSubextension_abstractNormMap_eq_actualNormRange
      K L).symm.trans
      (secondSmallHilbertClassFieldSubextension_abstractNormMap_eq_smallHilbertNormSubgroup
        K L)


-- @@ L820-832 verbatim
/-- Compatibility of the typed middle endpoint with the canonical endpoint
used by the conjugation API. -/
theorem smallHilbertTowerMiddleNormSubgroup_eq_conjugationEndpoint :
    smallHilbertTowerMiddleNormSubgroup K L =
      smallHilbertNormSubgroupInRationalClassFormation
        (L.toFiniteGaloisExtension.toFiniteAbstractFieldExtension).field := by
  have hField :
      (L.toFiniteGaloisExtension.toFiniteAbstractFieldExtension).field.field =
        L.field := by
    rfl
  unfold smallHilbertNormSubgroupInRationalClassFormation
  cases hField
  exact smallHilbertTowerMiddleNormSubgroup_eq_map K L


-- @@ L834-834 verbatim
end RationalFixedField


-- @@ L836-836 verbatim
section ActualTower


-- @@ L838-838 verbatim
variable (K : Type) [Field K] [NumberField K]


-- @@ L840-848 verbatim
/-- The actual second small Hilbert class field over the selected first
small Hilbert class field of `K`. -/
noncomputable def smallHilbertTowerSecondSubextension :
    FiniteAbelianSubextension
      (smallHilbertClassFieldSubextension K).field :=
  secondSmallHilbertClassFieldSubextension
    (numberFieldTowerFiniteAbstractField K
      (smallHilbertClassFieldNormAmbient K))
    (smallHilbertClassFieldSubextension K)


-- @@ L850-862 verbatim
/-- Exact norm-subgroup equation for the actual second stage. -/
@[simp]
theorem smallHilbertTowerSecondSubextension_normSubgroup :
    (smallHilbertTowerSecondSubextension K).normSubgroup
        rationalIdeleClassRepresentation =
      smallHilbertTowerMiddleNormSubgroup
        (numberFieldTowerFiniteAbstractField K
          (smallHilbertClassFieldNormAmbient K))
        (smallHilbertClassFieldSubextension K) :=
  secondSmallHilbertClassFieldSubextension_normSubgroup
    (numberFieldTowerFiniteAbstractField K
      (smallHilbertClassFieldNormAmbient K))
    (smallHilbertClassFieldSubextension K)


-- @@ L864-878 verbatim
/-- The actual two-stage small Hilbert tower, packaged as a finite
Galois subextension of the original selected base subgroup. -/
noncomputable def smallHilbertTowerGaloisRealization :
    FiniteGaloisSubextension
      (smallHilbertClassFieldBaseSubgroup K) :=
  smallHilbertClassFieldGaloisSubextension
    (numberFieldTowerFiniteAbstractField K
      (smallHilbertClassFieldNormAmbient K))
    (smallHilbertClassFieldSubextension K)
    (smallHilbertTowerSecondSubextension K)
    ((smallHilbertTowerSecondSubextension_normSubgroup K).trans
      (smallHilbertTowerMiddleNormSubgroup_eq_conjugationEndpoint
        (numberFieldTowerFiniteAbstractField K
          (smallHilbertClassFieldNormAmbient K))
        (smallHilbertClassFieldSubextension K)))


-- @@ L880-880 verbatim
end ActualTower


-- @@ L882-882 verbatim
end IdealClassFieldTheory

-- @@ L883-883 verbatim
end GlobalClassFieldTheory
