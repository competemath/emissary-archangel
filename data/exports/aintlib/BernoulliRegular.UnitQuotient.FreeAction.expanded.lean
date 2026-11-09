/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import BernoulliRegular.UnitQuotient.DeltaAction


-- @@ L10-21 verbatim
/-!
# Unit quotients: the actual action on the Dirichlet free quotient

This file proves `REF-07c1`.  The actual cyclotomic action on
`E = O_K^*` preserves the torsion subgroup of roots of unity, so it descends
to the torsion-free quotient `E / E_tors`.  Since this quotient is written in
additive notation as `CyclotomicUnitFreePart`, the descended action is packaged
as a `Z`-linear automorphism.

No logarithmic embeddings are used here; the comparison with the Dirichlet
logarithmic lattice is the next step.
-/


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-27 verbatim
open NumberField IsCyclotomicExtension

-- @@ L28-28 verbatim
open scoped NumberField


-- @@ L30-30 verbatim
namespace BernoulliRegular



-- @@ L33-33 verbatim
variable (p : ℕ) [Fact p.Prime]

-- @@ L34-34 verbatim
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]


-- @@ L36-38 verbatim
/-- The canonical `Z`-module structure on the additive form of `E/E_tors`. -/
instance cyclotomicUnitFreePartIntModule : Module ℤ (CyclotomicUnitFreePart K) :=
  AddCommGroup.toIntModule (CyclotomicUnitFreePart K)


-- @@ L40-47 verbatim
/-- The actual cyclotomic unit automorphism preserves torsion units. -/
theorem cyclotomicUnitEquiv_mem_torsion
    (a : CyclotomicUnitDelta p) {u : CyclotomicUnitGroup K}
    (hu : u ∈ CyclotomicUnitTorsion K) :
    cyclotomicUnitEquiv (p := p) K a u ∈ CyclotomicUnitTorsion K :=
  (CommGroup.mem_torsion _).2
    ((cyclotomicUnitEquiv (p := p) K a).toMonoidHom.isOfFinOrder
      ((CommGroup.mem_torsion _).1 hu))


-- @@ L49-64 verbatim
/-- The actual cyclotomic unit automorphism maps the torsion subgroup onto
itself. -/
theorem cyclotomicUnitEquiv_torsion_map (a : CyclotomicUnitDelta p) :
    (CyclotomicUnitTorsion K).map
        (cyclotomicUnitEquiv (p := p) K a).toMonoidHom =
      CyclotomicUnitTorsion K := by
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact cyclotomicUnitEquiv_mem_torsion (p := p) (K := K) a hv
  · intro hu
    refine ⟨(cyclotomicUnitEquiv (p := p) K a).symm u, ?_, ?_⟩
    · exact (CommGroup.mem_torsion _).2
        ((cyclotomicUnitEquiv (p := p) K a).symm.toMonoidHom.isOfFinOrder
          ((CommGroup.mem_torsion _).1 hu))
    · simp


-- @@ L66-75 verbatim
/-- The actual cyclotomic action descended to the multiplicative quotient
`E/E_tors`. -/
noncomputable def cyclotomicUnitFreeQuotientEquiv
    (a : CyclotomicUnitDelta p) :
    (CyclotomicUnitGroup K ⧸ CyclotomicUnitTorsion K) ≃*
      (CyclotomicUnitGroup K ⧸ CyclotomicUnitTorsion K) :=
  QuotientGroup.congr
    (CyclotomicUnitTorsion K) (CyclotomicUnitTorsion K)
    (cyclotomicUnitEquiv (p := p) K a)
    (cyclotomicUnitEquiv_torsion_map (p := p) (K := K) a)


-- @@ L77-83 verbatim
@[simp]
theorem cyclotomicUnitFreeQuotientEquiv_mk
    (a : CyclotomicUnitDelta p) (u : CyclotomicUnitGroup K) :
    cyclotomicUnitFreeQuotientEquiv (p := p) K a
        (cyclotomicUnitFreeClass K u) =
      cyclotomicUnitFreeClass K (cyclotomicUnitEquiv (p := p) K a u) :=
  rfl


-- @@ L85-90 verbatim
/-- The actual cyclotomic action descended to the additive Dirichlet free
quotient `E/E_tors`. -/
noncomputable def cyclotomicUnitFreePartLinearEquiv
    (a : CyclotomicUnitDelta p) :
    CyclotomicUnitFreePart K ≃ₗ[ℤ] CyclotomicUnitFreePart K :=
  (cyclotomicUnitFreeQuotientEquiv (p := p) K a).toAdditive.toIntLinearEquiv


-- @@ L92-98 verbatim
@[simp]
theorem cyclotomicUnitFreePartLinearEquiv_apply_class
    (a : CyclotomicUnitDelta p) (u : CyclotomicUnitGroup K) :
    cyclotomicUnitFreePartLinearEquiv (p := p) K a
        (Additive.ofMul (cyclotomicUnitFreeClass K u)) =
      Additive.ofMul (cyclotomicUnitFreeClass K (cyclotomicUnitEquiv (p := p) K a u)) :=
  rfl


-- @@ L100-129 verbatim
/-- The actual `Delta` action on the additive Dirichlet free quotient. -/
noncomputable def cyclotomicUnitFreePartDeltaAction :
    CyclotomicUnitDelta p →*
      (CyclotomicUnitFreePart K ≃ₗ[ℤ] CyclotomicUnitFreePart K) where
  toFun a := cyclotomicUnitFreePartLinearEquiv (p := p) K a
  map_one' := by
    ext x
    apply Additive.ext
    change cyclotomicUnitFreeQuotientEquiv (p := p) K 1 x.toMul = x.toMul
    refine QuotientGroup.induction_on x.toMul ?_
    intro u
    change cyclotomicUnitFreeQuotientEquiv (p := p) K 1
        (cyclotomicUnitFreeClass K u) =
      cyclotomicUnitFreeClass K u
    rw [cyclotomicUnitFreeQuotientEquiv_mk, cyclotomicUnitEquiv_one_apply]
  map_mul' a b := by
    ext x
    apply Additive.ext
    change cyclotomicUnitFreeQuotientEquiv (p := p) K (a * b) x.toMul =
      cyclotomicUnitFreeQuotientEquiv (p := p) K a
        (cyclotomicUnitFreeQuotientEquiv (p := p) K b x.toMul)
    refine QuotientGroup.induction_on x.toMul ?_
    intro u
    change cyclotomicUnitFreeQuotientEquiv (p := p) K (a * b)
        (cyclotomicUnitFreeClass K u) =
      cyclotomicUnitFreeQuotientEquiv (p := p) K a
        (cyclotomicUnitFreeQuotientEquiv (p := p) K b
          (cyclotomicUnitFreeClass K u))
    rw [cyclotomicUnitFreeQuotientEquiv_mk, cyclotomicUnitFreeQuotientEquiv_mk,
      cyclotomicUnitFreeQuotientEquiv_mk, cyclotomicUnitEquiv_mul_apply]


-- @@ L131-137 verbatim
@[simp]
theorem cyclotomicUnitFreePartDeltaAction_apply_class
    (a : CyclotomicUnitDelta p) (u : CyclotomicUnitGroup K) :
    cyclotomicUnitFreePartDeltaAction (p := p) K a
        (Additive.ofMul (cyclotomicUnitFreeClass K u)) =
      Additive.ofMul (cyclotomicUnitFreeClass K (cyclotomicUnitEquiv (p := p) K a u)) :=
  rfl


-- @@ L139-139 verbatim
end BernoulliRegular


-- @@ L141-141 verbatim
end
