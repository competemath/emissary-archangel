/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.SimpleModule.Isotypic
public import TauCeti.Algebra.Lie.Isotypic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Module


-- @@ L12-49 verbatim
/-!
# Isotypic Lie modules through the universal enveloping algebra

This file transports Mathlib's isotypic-module interface across the universal-enveloping-algebra
dictionary. For an irreducible target type, semisimplicity enters only in the characterization of
an isotypic module by its unique component.

The generic equivalence and submodule interfaces live with the rest of the enveloping-algebra
dictionary in `TauCeti.Algebra.Lie.UniversalEnveloping.Module`. The UEA-independent Lie-level
predicates and component live in `TauCeti.Algebra.Lie.Isotypic`; this file identifies them with
Mathlib's `IsIsotypicOfType`, `IsIsotypic`, and `isotypicComponent` through those interfaces.

## Main results

* `LieModule.isIsotypicOfType_iff_isIsotypicOfType_of_ι_smul`: fixed-type isotypy transport
  for compatible actions.
* `LieModule.isIsotypic_iff_isIsotypic_of_ι_smul`: pairwise isotypy transport for compatible
  actions.
* `LieModule.lieSubmoduleOrderIso_isotypicComponent`: component transport for compatible actions.
* `LieModule.isIsotypicOfType_isotypicComponent`: **the isotypic component of an irreducible type
  is isotypic of that type**, so it really is the largest Lie submodule built from copies of it.
* `LieModule.mem_isotypicComponent_iff_mem_isotypicComponent_asModule`: canonical component
  membership normalization.
* `LieModule.isotypicComponent_eq_top_iff_of_ι_smul`: the top-component criterion for an
  irreducible type.

## Roadmap

This is the universal-enveloping-algebra bridge for Layer 6 of the Lie highest-weight roadmap.
It deliberately stops before highest-weight classification: consumers such as Kostant-form
modules can state that all irreducible Lie submodules are equivalent without rebuilding ring-level
isotypic machinery.

## References

* `Mathlib/RingTheory/SimpleModule/Isotypic.lean` (Junyan Xu): the module-theoretic isotypic
  interface and top-component criterion transported through the enveloping-algebra dictionary.
-/


-- @@ L51-51 verbatim
public section


-- @@ L53-53 verbatim
open UniversalEnvelopingAlgebra


-- @@ L55-55 verbatim
universe u v w


-- @@ L57-57 verbatim
namespace LieModule


-- @@ L59-59 verbatim
open TauCeti.UniversalEnvelopingAlgebra


-- @@ L61-61 verbatim
variable (R : Type u) (L : Type v) (M : Type w)

-- @@ L62-62 verbatim
variable [CommRing R] [LieRing L] [LieAlgebra R L]

-- @@ L63-63 verbatim
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]


-- @@ L65-65 verbatim
local notation "U" => _root_.UniversalEnvelopingAlgebra R L


-- @@ L67-67 verbatim
section Compatible


-- @@ L69-69 verbatim
variable [Module (_root_.UniversalEnvelopingAlgebra R L) M]

-- @@ L70-70 verbatim
variable [IsScalarTower R (_root_.UniversalEnvelopingAlgebra R L) M]

-- @@ L71-71 verbatim
variable {R L M}


-- @@ L73-92 verbatim
/-- Lie-module isotypy of a fixed type is exactly Mathlib's module isotypy for compatible
`U(L)`-actions. -/
theorem isIsotypicOfType_iff_isIsotypicOfType_of_ι_smul
    (hM : ∀ (x : L) (m : M), ι R x • m = ⁅x, m⁆)
    (S : Type*) [AddCommGroup S] [Module R S] [LieRingModule L S] [LieModule R L S]
    [Module U S] [IsScalarTower R U S]
    (hS : ∀ (x : L) (s : S), ι R x • s = ⁅x, s⁆) :
    IsIsotypicOfType R L M S ↔ _root_.IsIsotypicOfType U M S := by
  rw [isIsotypicOfType_iff]
  constructor
  · intro h Q hQ
    obtain ⟨P, rfl⟩ := (lieSubmoduleOrderIso hM).surjective Q
    let : IsIrreducible R L P :=
      (isSimpleModule_lieSubmoduleOrderIso_iff hM P).mp hQ
    exact (nonempty_lieModuleEquiv_iff_nonempty_linearEquiv hM S hS P).mp (h P)
  · intro h P hP
    let : IsSimpleModule U (lieSubmoduleOrderIso hM P) :=
      (isSimpleModule_lieSubmoduleOrderIso_iff hM P).mpr hP
    exact (nonempty_lieModuleEquiv_iff_nonempty_linearEquiv hM S hS P).mpr
      (h (lieSubmoduleOrderIso hM P))


-- @@ L94-118 verbatim
/-- Lie-module isotypy is exactly Mathlib's module isotypy for a compatible `U(L)`-action. -/
theorem isIsotypic_iff_isIsotypic_of_ι_smul
    (hM : ∀ (x : L) (m : M), ι R x • m = ⁅x, m⁆) :
    IsIsotypic R L M ↔ _root_.IsIsotypic U M := by
  rw [isIsotypic_iff]
  simp only [_root_.IsIsotypic]
  constructor
  · intro h Q hQ
    obtain ⟨P, rfl⟩ := (lieSubmoduleOrderIso hM).surjective Q
    let : Module U P := asModule R L P
    let : IsScalarTower R U P := isScalarTower_asModule R L P
    let : IsIrreducible R L P :=
      (isSimpleModule_lieSubmoduleOrderIso_iff hM P).mp hQ
    exact (isIsotypicOfType_iff_isIsotypicOfType_of_ι_smul hM P
      (asModule_ι_smul R L P) |>.mp (h P)).of_linearEquiv_type
      (lieSubmoduleLinearEquiv hM P)
  · intro h P hP
    let : Module U P := asModule R L P
    let : IsScalarTower R U P := isScalarTower_asModule R L P
    let : IsSimpleModule U (lieSubmoduleOrderIso hM P) :=
      (isSimpleModule_lieSubmoduleOrderIso_iff hM P).mpr hP
    exact isIsotypicOfType_iff_isIsotypicOfType_of_ι_smul hM P
      (asModule_ι_smul R L P) |>.mpr
      ((h (lieSubmoduleOrderIso hM P)).of_linearEquiv_type
        (lieSubmoduleLinearEquiv hM P).symm)


-- @@ L120-137 verbatim
/-- A compatible submodule dictionary maps the Lie isotypic component to Mathlib's
`U(L)`-isotypic component. -/
theorem lieSubmoduleOrderIso_isotypicComponent
    (hM : ∀ (x : L) (m : M), ι R x • m = ⁅x, m⁆)
    (S : Type*) [AddCommGroup S] [Module R S] [LieRingModule L S] [LieModule R L S]
    [Module U S] [IsScalarTower R U S]
    (hS : ∀ (x : L) (s : S), ι R x • s = ⁅x, s⁆) :
    lieSubmoduleOrderIso hM (isotypicComponent R L M S) =
      _root_.isotypicComponent U M S := by
  rw [isotypicComponent_def,
    (lieSubmoduleOrderIso hM).map_sSup_eq_sSup_symm_preimage,
    _root_.isotypicComponent]
  congr 1
  ext Q
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  obtain ⟨P, rfl⟩ := (lieSubmoduleOrderIso hM).surjective Q
  rw [(lieSubmoduleOrderIso hM).symm_apply_apply]
  exact nonempty_lieModuleEquiv_iff_nonempty_linearEquiv hM S hS P


-- @@ L139-155 verbatim
/-- The compatible-action form of `LieModule.isIsotypicOfType_isotypicComponent`, from which the
canonical statement below is read off. Its conclusion mentions no `U(L)`-action, so it is not part
of the interface: only the canonical form is exposed. -/
private theorem isIsotypicOfType_isotypicComponent_of_ι_smul
    (hM : ∀ (x : L) (m : M), ι R x • m = ⁅x, m⁆)
    (S : Type*) [AddCommGroup S] [Module R S] [LieRingModule L S] [LieModule R L S]
    [Module U S] [IsScalarTower R U S]
    (hS : ∀ (x : L) (s : S), ι R x • s = ⁅x, s⁆) [IsIrreducible R L S] :
    IsIsotypicOfType R L (isotypicComponent R L M S) S := by
  have : IsSimpleModule U S := (isIrreducible_iff_isSimpleModule hS).mp inferInstance
  let := asModule R L (isotypicComponent R L M S)
  let := isScalarTower_asModule R L (isotypicComponent R L M S)
  rw [isIsotypicOfType_iff_isIsotypicOfType_of_ι_smul
    (asModule_ι_smul R L (isotypicComponent R L M S)) S hS]
  refine (LinearEquiv.isIsotypicOfType_iff (lieSubmoduleLinearEquiv hM _)).mpr ?_
  rw [lieSubmoduleOrderIso_isotypicComponent hM S hS]
  exact IsIsotypicOfType.isotypicComponent U M S


-- @@ L157-167 verbatim
/-- Membership in the Lie isotypic component is membership in the corresponding isotypic component
for compatible `U(L)`-actions. -/
theorem mem_isotypicComponent_iff_mem_isotypicComponent_of_ι_smul
    (hM : ∀ (x : L) (m : M), ι R x • m = ⁅x, m⁆)
    {S : Type*} [AddCommGroup S] [Module R S] [LieRingModule L S] [LieModule R L S]
    [Module U S] [IsScalarTower R U S]
    (hS : ∀ (x : L) (s : S), ι R x • s = ⁅x, s⁆)
    {m : M} :
    m ∈ isotypicComponent R L M S ↔ m ∈ _root_.isotypicComponent U M S := by
  rw [← mem_lieSubmoduleOrderIso hM,
    lieSubmoduleOrderIso_isotypicComponent hM S hS]


-- @@ L169-187 verbatim
/-- For compatible `U(L)`-actions, an irreducible type `S`, and a completely reducible Lie module,
the isotypic component of type `S` is the whole module exactly when the Lie module is isotypic of
type `S`. -/
theorem isotypicComponent_eq_top_iff_of_ι_smul
    (hM : ∀ (x : L) (m : M), ι R x • m = ⁅x, m⁆)
    (S : Type*) [AddCommGroup S] [Module R S] [LieRingModule L S] [LieModule R L S]
    [Module U S] [IsScalarTower R U S]
    (hS : ∀ (x : L) (s : S), ι R x • s = ⁅x, s⁆)
    [IsIrreducible R L S]
    [ComplementedLattice (LieSubmodule R L M)] :
    isotypicComponent R L M S = ⊤ ↔ IsIsotypicOfType R L M S := by
  let : IsSimpleModule U S :=
    (isIrreducible_iff_isSimpleModule hS).mp inferInstance
  let : IsSemisimpleModule U M :=
    (complementedLattice_lieSubmodule_iff_isSemisimpleModule hM).mp inferInstance
  rw [← map_eq_top_iff (lieSubmoduleOrderIso hM),
    lieSubmoduleOrderIso_isotypicComponent hM S hS,
    _root_.isotypicComponent_eq_top_iff,
    isIsotypicOfType_iff_isIsotypicOfType_of_ι_smul hM S hS]


-- @@ L189-189 verbatim
end Compatible


-- @@ L191-191 verbatim
section Canonical


-- @@ L193-193 verbatim
attribute [local instance] asModule isScalarTower_asModule


-- @@ L195-195 verbatim
variable {R L M}


-- @@ L197-205 verbatim
/-- Membership in the Lie isotypic component is membership in the corresponding canonical
`U(L)`-isotypic component. -/
@[simp]
theorem mem_isotypicComponent_iff_mem_isotypicComponent_asModule
    {S : Type*} [AddCommGroup S] [Module R S] [LieRingModule L S] [LieModule R L S]
    {m : M} :
    m ∈ isotypicComponent R L M S ↔ m ∈ _root_.isotypicComponent U M S :=
  mem_isotypicComponent_iff_mem_isotypicComponent_of_ι_smul
    (asModule_ι_smul R L M) (asModule_ι_smul R L S)


-- @@ L207-215 verbatim
/-- **The Lie isotypic component of an irreducible type is isotypic of that type**: every
irreducible Lie submodule of the `S`-isotypic component of `M` is equivalent to `S`. This is
Mathlib's `IsIsotypicOfType.isotypicComponent` read through the dictionary, and it is what makes
the component the largest Lie submodule built from copies of `S`. -/
theorem isIsotypicOfType_isotypicComponent
    (S : Type*) [AddCommGroup S] [Module R S] [LieRingModule L S] [LieModule R L S]
    [IsIrreducible R L S] :
    IsIsotypicOfType R L (isotypicComponent R L M S) S :=
  isIsotypicOfType_isotypicComponent_of_ι_smul (asModule_ι_smul R L M) S (asModule_ι_smul R L S)


-- @@ L217-217 verbatim
end Canonical


-- @@ L219-219 verbatim
end LieModule
