/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Kevin Buzzard, Ruben Van de Velde
-/
module

public import FLT.Mathlib.GroupTheory.Index
public import FLT.Mathlib.Topology.Algebra.Group.Basic
public import FLT.Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Algebra.Equiv
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Instances.Matrix


-- @@ L18-24 verbatim
/-!
# Miscellaneous lemmas for the Deformations folder

A collection of small auxiliary lemmas used in the deformation-theory
files: existence of open maximal ideals in linearly topologized rings,
continuous group-homomorphism / matrix-coefficient lifts, etc.
-/


-- @@ L26-26 verbatim
@[expose] public section


-- @@ L28-35 verbatim
lemma IsLinearTopology.exists_ideal_isMaximal_and_isOpen
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R] [Nontrivial R] [T0Space R] :
    ∃ I : Ideal R, I.IsMaximal ∧ IsOpen (X := R) I := by
  obtain ⟨I, hI, hI'⟩ := IsLinearTopology.hasBasis_open_ideal.mem_iff.mp
    ((isClosed_singleton (x := (1 : R))).isOpen_compl.mem_nhds (x := 0) (by simp))
  obtain ⟨J, hJ, hIJ⟩ := Ideal.exists_le_maximal I (by simpa [Ideal.eq_top_iff_one] using hI')
  exact ⟨J, hJ, AddSubgroup.isOpen_mono (H₁ := I.toAddSubgroup) (H₂ := J.toAddSubgroup) hIJ hI⟩


-- @@ L37-43 verbatim
/-- The continuous group homomorphism on units induced by a `ContinuousMonoidHom`. -/
@[simps!]
def Units.mapₜ {M N : Type*} [Monoid M] [Monoid N] [TopologicalSpace M] [TopologicalSpace N]
    (f : M →ₜ* N) : Mˣ →ₜ* Nˣ :=
  ⟨Units.map f,
  continuous_induced_rng.mpr (continuous_prodMk.mpr ⟨f.2.comp Units.continuous_val,
    MulOpposite.continuous_op.comp (f.2.comp Units.continuous_coe_inv)⟩)⟩


-- @@ L45-53 verbatim
/-- The `ContinuousAlgHom` between spaces of square matrices induced by an `ContinuousAlgHom`
between their coefficients. This is Matrix.map as an `ContinuousAlgHom`. -/
@[simps!]
def ContinuousAlgHom.mapMatrix
    {R A B n : Type*} [CommSemiring R] [Semiring A] [Semiring B] [TopologicalSpace A]
    [TopologicalSpace B] [Algebra R A] [Algebra R B] (f : A →A[R] B)
    [Fintype n] [DecidableEq n] :
    Matrix n n A →A[R] Matrix n n B :=
  ⟨f.1.mapMatrix, Continuous.matrix_map continuous_id' f.2⟩


-- @@ L55-59 verbatim
/-- Coerce a `ContinuousAlgHom` to `ContinuousMonoidHom`. -/
def ContinuousAlgHom.toContinuousMonoidHom
    {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [TopologicalSpace A]
    [TopologicalSpace B] [Algebra R A] [Algebra R B] (f : A →A[R] B) : A →ₜ* B :=
  ⟨f.1.toMonoidHom, f.2⟩


-- @@ L61-65 verbatim
@[simp]
lemma ContinuousAlgHom.coe_toContinuousMonoidHom
    {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [TopologicalSpace A]
    [TopologicalSpace B] [Algebra R A] [Algebra R B] (f : A →A[R] B) :
    (f.toContinuousMonoidHom : A → B) = f := rfl


-- @@ L67-71 verbatim
instance {α M G : Type*} [Monoid M] [Monoid G] [Monoid α] [MulDistribMulAction α G] :
    MulAction α (M →* G) where
  smul a f := ⟨⟨a • f, by simp⟩, by simp⟩
  one_smul _ := by ext; exact one_smul _ _
  mul_smul a b f := by ext x; change (a * b) • (f x) = a • b • (f x); simp [mul_smul]


-- @@ L73-77 verbatim
@[simp]
lemma MonoidHom.coe_smul
    {α M G : Type*} [Monoid M] [Monoid G] [Monoid α] [MulDistribMulAction α G]
    (a : α) (f : M →* G) :
    ⇑(a • f) = a • ⇑f := rfl


-- @@ L79-84 verbatim
instance {α M G : Type*} [Monoid M] [Monoid G] [Monoid α] [MulDistribMulAction α G]
    [TopologicalSpace M] [TopologicalSpace G] [ContinuousConstSMul α G] :
    MulAction α (M →ₜ* G) where
  smul a f := ⟨a • f, .const_smul f.2 _⟩
  one_smul _ := by ext; exact one_smul _ _
  mul_smul a b f := by ext x; change (a * b) • (f x) = a • b • (f x); simp [mul_smul]


-- @@ L86-91 verbatim
@[simp]
lemma ContinuousMonoidHom.coe_smul
    {α M G : Type*} [Monoid M] [Monoid G] [Monoid α] [MulDistribMulAction α G]
    [TopologicalSpace M] [TopologicalSpace G] [ContinuousConstSMul α G]
    (a : α) (f : M →ₜ* G) :
    ⇑(a • f) = a • ⇑f := rfl


-- @@ L93-95 verbatim
instance {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G] :
    ContinuousConstSMul (ConjAct G) G :=
  ⟨fun _ ↦ .mul (continuous_const.mul continuous_id) continuous_const⟩


-- @@ L97-103 verbatim
@[to_additive]
instance IsTopologicalGroup.discreteUniformity
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [DiscreteTopology G] :
    letI := IsTopologicalGroup.rightUniformSpace G
    DiscreteUniformity G := by
  simp only [discreteUniformity_iff_setRelId_mem_uniformity]
  exact ⟨{1}, by simp [Set.subset_def, ← div_eq_mul_inv, div_eq_one]⟩


-- @@ L105-108 verbatim
lemma IsLocalRing.ResidueField.map_surjective {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (f : R →+* S) [IsLocalHom f] (H : Function.Surjective f) :
    Function.Surjective (IsLocalRing.ResidueField.map f) :=
  Ideal.Quotient.lift_surjective_of_surjective _ _ (Ideal.Quotient.mk_surjective.comp H)


-- @@ L110-113 verbatim
lemma RingHom.continuous_iff_isOpen_ker {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [Ring α] [Semiring β] {f : α →+* β} [DiscreteTopology β] [IsTopologicalAddGroup α] :
    Continuous f ↔ IsOpen (X := α) (RingHom.ker f) :=
  AddMonoidHom.continuous_iff_isOpen_ker (φ := f.toAddMonoidHom)


-- @@ L115-119 verbatim
open Topology in
lemma continuousAt_discrete_rng {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {f : α → β} {x : α} [DiscreteTopology β] :
    ContinuousAt f x ↔ ∀ᶠ y in 𝓝 x, f y = f x := by
  simp [ContinuousAt]


-- @@ L121-126 verbatim
nonrec
instance ContinuousAlgHom.isLocalHom_id {R A : Type*}
    [CommSemiring R] [Semiring A] [Algebra R A] [TopologicalSpace A] :
    IsLocalHom (ContinuousAlgHom.id R A) := by
  convert isLocalHom_id A
  exact ⟨fun ⟨H⟩ ↦ ⟨H⟩, fun ⟨H⟩ ↦ ⟨H⟩⟩


-- @@ L128-134 verbatim
lemma ContinuousAlgHom.isLocalHom_toRingHom {R A B : Type*}
    [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B]
    [TopologicalSpace A] [TopologicalSpace B]
    {f : A →A[R] B} :
    IsLocalHom f.toRingHom ↔ IsLocalHom f :=
  ⟨fun ⟨H⟩ ↦ ⟨H⟩, fun ⟨H⟩ ↦ ⟨H⟩⟩


-- @@ L136-139 verbatim
instance {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [TopologicalSpace A] [TopologicalSpace B]
    (f : A →A[R] B) [IsLocalHom f] : IsLocalHom f.toRingHom := by
  rwa [ContinuousAlgHom.isLocalHom_toRingHom]


-- @@ L141-145 verbatim
instance {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [TopologicalSpace A] [TopologicalSpace B]
    (f : A ≃A[R] B) : IsLocalHom (f : A →A[R] B) := by
  convert isLocalHom_equiv f
  exact ⟨fun ⟨H⟩ ↦ ⟨H⟩, fun ⟨H⟩ ↦ ⟨H⟩⟩


-- @@ L147-150 verbatim
instance {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [TopologicalSpace A] [TopologicalSpace B]
    (f : A →A[R] B) [IsLocalHom f] : IsLocalHom f.toRingHom := by
  rwa [ContinuousAlgHom.isLocalHom_toRingHom]


-- @@ L152-156 verbatim
instance {A B : Type*} [Semiring A] [Semiring B]
    (F : Type*) [EquivLike F A B] [RingEquivClass F A B] (f : F) :
    IsLocalHom (RingHomClass.toRingHom f) := by
  convert isLocalHom_equiv f
  exact ⟨fun ⟨H⟩ ↦ ⟨H⟩, fun ⟨H⟩ ↦ ⟨H⟩⟩


-- @@ L158-159 verbatim
instance {R S} [Semiring R] [Semiring S] (e : R ≃+* S) : IsLocalHom e.toRingHom :=
  ⟨fun x hx ↦ by convert hx.map e.symm; simp⟩


-- @@ L161-169 verbatim
instance ContinuousAlgHom.isLocalHom_comp {R A B C : Type*}
    [CommSemiring R] [Semiring A] [Semiring B] [Semiring C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    {g : B →A[R] C} {f : A →A[R] B}
    [IsLocalHom g] [IsLocalHom f] :
    IsLocalHom (g.comp f) := by
  convert RingHom.isLocalHom_comp g.toRingHom f.toRingHom
  exact ⟨fun ⟨H⟩ ↦ ⟨H⟩, fun ⟨H⟩ ↦ ⟨H⟩⟩


-- @@ L171-172 verbatim
instance {R : Type*} [CommSemiring R] : IsLocalHom (algebraMap R R) :=
  isLocalHom_id R


-- @@ L174-177 verbatim
open IsLocalRing in
instance {R : Type*} [CommRing R] [IsLocalRing R] :
    IsLocalHom (algebraMap R (ResidueField R)) :=
  IsLocalRing.instIsLocalHomResidueFieldRingHomResidue _


-- @@ L179-184 verbatim
/-- Given a field extension, this is an arbitrarily chosen map between their `AlgebraicClosure`s. -/
noncomputable
def AlgebraicClosure.map {K L : Type*} [Field K] [Field L] (f : K →+* L) :
    AlgebraicClosure K →+* AlgebraicClosure L :=
  letI := f.toAlgebra
  (IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] AlgebraicClosure L).toRingHom


-- @@ L186-189 verbatim
lemma AlgebraicClosure.map_algebraMap {K L : Type*} [Field K] [Field L] (f : K →+* L) (x) :
    map f (algebraMap K _ x) = algebraMap _ _ (f x) :=
    letI := f.toAlgebra
    (IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] AlgebraicClosure L).commutes _


-- @@ L191-210 verbatim
nonrec
lemma IsModuleTopology.continuous_det {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] {M : Type*} [AddCommGroup M] [Module A M]
    [TopologicalSpace (Module.End A M)] [IsModuleTopology A (Module.End A M)] :
    Continuous (LinearMap.det : Module.End A M →* A) := by
  classical
  by_cases H : ∃ s : Finset M, Nonempty (Module.Basis s A M)
  · obtain ⟨s, ⟨b⟩⟩ := H
    have : IsModuleTopology A (Matrix s s A) := IsModuleTopology.instPi
    have : ContinuousAdd (Module.End A M) := IsModuleTopology.toContinuousAdd A _
    let e : Module.End A M ≃A[A] Matrix s s A :=
    { __ := algEquivMatrix b,
      continuous_toFun := continuous_of_linearMap (algEquivMatrix b).toLinearMap,
      continuous_invFun := continuous_of_linearMap (algEquivMatrix b).symm.toLinearMap }
    rw [e.symm.isQuotientMap.continuous_iff]
    convert! continuous_id.matrix_det (R := A) (n := s)
    ext M
    exact LinearMap.det_toLin b M
  rw [LinearMap.det, dite_eq_right H]
  exact continuous_of_const fun x ↦ congrFun rfl


-- @@ L212-214 verbatim
/-- `End_A(A) ≃ A`. -/
def Module.endSelf {A : Type*} [CommSemiring A] : Module.End A A ≃ₐ[A] A :=
  AlgEquiv.ofLinearEquiv (LinearMap.ringLmapEquivSelf A A A) (by simp) (by simp)


-- @@ L216-222 verbatim
/-- Given a `ContinuousMonoidHom` from a group to a monoid, we may lift it to map into the group
of units of the monoid. -/
@[simps!]
def ContinuousMonoidHom.toHomUnits {G M : Type*} [Group G] [Monoid M] [TopologicalSpace G]
    [IsTopologicalGroup G] [TopologicalSpace M] (f : G →ₜ* M) : G →ₜ* Mˣ :=
  ⟨MonoidHom.toHomUnits f, continuous_induced_rng.mpr (continuous_prodMk.mpr ⟨f.continuous, by
    simpa [← map_inv] using! MulOpposite.continuous_op.comp (f.continuous.comp continuous_inv)⟩)⟩


-- @@ L224-227 verbatim
/-- `Units.val` as a `ContinuousMonoidHom`. -/
@[simps!]
def Units.coeHomₜ (M : Type*) [Monoid M] [TopologicalSpace M] : Mˣ →ₜ* M :=
  ⟨coeHom M, Units.continuous_val⟩


-- @@ L229-231 verbatim
instance {A n m : Type*} [CommRing A] [TopologicalSpace A]
    [Finite n] [Finite m] [IsTopologicalRing A] :
    IsModuleTopology A (Matrix n m A) := IsModuleTopology.instPi


-- @@ L233-245 verbatim
/-- We can upgrade an `AlgEquiv` between algebras with the module topology
into a `ContinuousAlgEquiv`. -/
def ContinuousAlgEquiv.ofIsModuleTopology {R A B : Type*} [CommSemiring R] [Semiring A]
    [Semiring B] [Algebra R A] [Algebra R B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace R] [IsModuleTopology R A] [IsModuleTopology R B] (e : A ≃ₐ[R] B) :
    A ≃A[R] B where
  __ := e
  continuous_toFun :=
    letI := IsModuleTopology.toContinuousAdd R B
    IsModuleTopology.continuous_of_linearMap e.toLinearMap
  continuous_invFun :=
    letI := IsModuleTopology.toContinuousAdd R A
    IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap


-- @@ L247-249 verbatim
@[simp]
lemma ContinuousMonoidHom.mk_toMonoidHom {M N : Type*} [Monoid M] [Monoid N] [TopologicalSpace M]
  [TopologicalSpace N] (f : M →* N) (hf : Continuous f) : (ContinuousMonoidHom.mk f hf) = f := rfl


-- @@ L251-253 verbatim
@[simp]
lemma ContinuousMonoidHom.coe_mk {M N : Type*} [Monoid M] [Monoid N] [TopologicalSpace M]
  [TopologicalSpace N] (f : M →* N) (hf : Continuous f) : ⇑(ContinuousMonoidHom.mk f hf) = f := rfl


-- @@ L255-266 verbatim
instance {G K L : Type*} [Field K] [Field L] [Algebra K L] [Monoid G] [MulSemiringAction G L]
    [SMulCommClass G K L]
    (E : IntermediateField K L) [Normal K E] : MulSemiringAction G E where
  smul σ x := ⟨σ • x, by
    convert ((MulSemiringAction.toAlgHom K L σ).restrictNormal E x).2
    exact ((MulSemiringAction.toAlgHom K L σ).restrictNormal_commutes E x).symm⟩
  one_smul _ := Subtype.ext (one_smul _ _)
  mul_smul _ _ _ := Subtype.ext (mul_smul _ _ _)
  smul_zero _ := Subtype.ext (smul_zero _)
  smul_add _ _ _ := Subtype.ext (smul_add _ _ _)
  smul_one _ := Subtype.ext (smul_one _)
  smul_mul _ _ _ := Subtype.ext (MulSemiringAction.smul_mul _ _ _)


-- @@ L268-277 verbatim
open NumberField in
instance {G K : Type*} [Field K] [Monoid G] [MulSemiringAction G K] :
    MulSemiringAction G (𝓞 K) where
  smul σ x := ⟨σ • x, x.2.map (MulSemiringAction.toAlgHom ℤ K σ)⟩
  one_smul _ := Subtype.ext (one_smul _ _)
  mul_smul _ _ _ := Subtype.ext (mul_smul _ _ _)
  smul_zero _ := Subtype.ext (smul_zero _)
  smul_add _ _ _ := Subtype.ext (smul_add _ _ _)
  smul_one _ := Subtype.ext (smul_one _)
  smul_mul _ _ _ := Subtype.ext (MulSemiringAction.smul_mul _ _ _)


-- @@ L279-280 verbatim
lemma Subring.algebraMap_def {R : Type*} [CommRing R] (S : Subring R) :
    algebraMap S R = S.subtype := rfl


-- @@ L282-284 verbatim
instance {K A : Type*} [Field K] [CommRing A] [Algebra K A] (R : ValuationSubring K)
    [FaithfulSMul K A] : FaithfulSMul R A :=
  Subsemiring.instFaithfulSMulSubtypeMem R


-- @@ L286-288 verbatim
instance {K L : Type*} [Field K] [Field L] [Algebra K L] [NumberField K]
    (E : IntermediateField K L) [FiniteDimensional K E] : NumberField E where
  to_finiteDimensional := .trans ℚ K E


-- @@ L290-295 verbatim
instance {K L : Type*} [Field K] [Semiring L] (O : ValuationSubring K) [Algebra K L] :
    Algebra O L where
  smul r x := r.1 • x
  algebraMap := (algebraMap K L).comp (algebraMap O K)
  commutes' _ _ := by simp [Algebra.commutes]
  smul_def' _ _ := by simp [← Algebra.smul_def]; rfl


-- @@ L297-301 verbatim
instance IntermediateField.smulCommClass_of_normal
    {K L G : Type*} [Field K] [Field L] [Algebra K L] (E : IntermediateField K L)
    [Monoid G] [MulSemiringAction G L] [SMulCommClass G K L] [Normal K E] :
    SMulCommClass G K E where
  smul_comm g k e := Subtype.ext <| smul_comm g k e.1


-- @@ L303-307 verbatim
instance ValuationSubring.smulCommClass
    (K L G : Type*) [Field K] [Semiring L] (O : ValuationSubring K) [Algebra K L]
    [Monoid G] [MulSemiringAction G L] [SMulCommClass G K L] :
    SMulCommClass G O L where
  smul_comm g o l := smul_comm g o.1 l


-- @@ L309-317 verbatim
noncomputable
instance Additive.instDistrbMulAction
    {G M : Type*} [Monoid G] [Monoid M] [MulDistribMulAction G M] :
    DistribMulAction G (Additive M) where
  smul g m := .ofMul (g • m.toMul)
  one_smul m := one_smul _ m.toMul
  mul_smul g h m := mul_smul g h m.toMul
  smul_zero g := smul_one (N := M) g
  smul_add g m n := MulDistribMulAction.smul_mul g m.toMul n.toMul
