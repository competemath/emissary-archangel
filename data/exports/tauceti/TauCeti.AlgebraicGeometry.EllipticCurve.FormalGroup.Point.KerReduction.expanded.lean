/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Reduction
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Point.Range


-- @@ L11-35 verbatim
/-!
# The formal group is the kernel of reduction

Let `A` be a Dedekind domain with fraction field `F`, let `u` be a height-one prime of `A`, and let
`C` be a Weierstrass curve over the completed valuation ring `O_u` which is elliptic over the
completion `F_u`. The points of `C` over `F_u` reduce modulo `u` (`Point.reduction`), and the
points reducing to `(0 : 1 : 0)` form the kernel of reduction `E₁(F_u)`. This file makes that set a
subgroup and identifies it with the group `Ê(𝔪_u)` of formal-group parameters in the maximal
ideal: Silverman AEC VII.2.2.

## Main definitions

* `WeierstrassCurve.kerReduction`: the kernel of reduction `E₁(F_u)`, as a subgroup of the points
  of `C` over `F_u`.
* `WeierstrassCurve.formalPointAddEquivKerReduction`: the isomorphism `Ê(𝔪_u) ≃+ E₁(F_u)`.

## Main results

* `WeierstrassCurve.range_formalPointHomAdicCompletion_eq_kerReduction`: the image of the formal
  parametrisation is the kernel of reduction.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.2.2.
-/


-- @@ L37-37 verbatim
public section


-- @@ L39-39 verbatim
namespace WeierstrassCurve


-- @@ L41-41 verbatim
open IsDedekindDomain


-- @@ L43-45 verbatim
variable {A : Type*} [CommRing A] [IsDedekindDomain A]
  {F : Type*} [Field F] [Algebra A F] [IsFractionRing A F]
  (u : HeightOneSpectrum A)


-- @@ L47-47 verbatim
local notation "O_u" => u.adicCompletionIntegers F

-- @@ L48-48 verbatim
local notation "F_u" => u.adicCompletion F

-- @@ L49-49 verbatim
local notation "m_u" => IsLocalRing.maximalIdeal O_u


-- @@ L51-52 verbatim
local instance : IsLinearTopology O_u O_u :=
  u.isAdic_maximalIdeal_adicCompletionIntegers (K := F) ▸ Ideal.isLinearTopology m_u


-- @@ L54-55 verbatim
local instance : Fact (IsAdic m_u) :=
  ⟨u.isAdic_maximalIdeal_adicCompletionIntegers (K := F)⟩


-- @@ L57-57 verbatim
variable (C : WeierstrassCurve (u.adicCompletionIntegers F))


-- @@ L59-59 verbatim
variable [(C.baseChange (u.adicCompletion F)).IsElliptic]


-- @@ L61-69 verbatim
open scoped Classical in
/-- **The kernel of reduction** `E₁(F_u)`: the points of `C` over the completion `F_u` that reduce
to `(0 : 1 : 0)` modulo `u`. -/
noncomputable def kerReduction : AddSubgroup (C.baseChange F_u).toAffine.Point :=
  (C.formalPointHomAdicCompletion u).range.copy
    {P | Affine.Point.reduction Valued.v P = ⟦![0, 1, 0]⟧} <| by
      ext P
      rw [Set.mem_ofPred_eq, Affine.Point.reduction_eq_zero_iff, AddMonoidHom.coe_range,
        range_formalPointHomAdicCompletion, Set.mem_ofPred_eq]


-- @@ L71-75 verbatim
open scoped Classical in
@[simp]
theorem mem_kerReduction_iff {P : (C.baseChange F_u).toAffine.Point} :
    P ∈ C.kerReduction u ↔ Affine.Point.reduction Valued.v P = ⟦![0, 1, 0]⟧ :=
  Iff.rfl


-- @@ L77-81 verbatim
open scoped Classical in
/-- **The image of the formal parametrisation is the kernel of reduction.** -/
theorem range_formalPointHomAdicCompletion_eq_kerReduction :
    (C.formalPointHomAdicCompletion u).range = C.kerReduction u :=
  (AddSubgroup.copy_eq _ _ _).symm


-- @@ L83-91 verbatim
open scoped Classical in
/-- **The formal group is the kernel of reduction**, Silverman AEC VII.2.2: the formal
parametrisation `t ↦ (t / w(t), -1 / w(t))` is an isomorphism from the group `Ê(𝔪_u)` of
formal-group parameters in the maximal ideal onto the kernel of reduction `E₁(F_u)`. -/
noncomputable def formalPointAddEquivKerReduction :
    FormalGroupPoint C m_u ≃+ C.kerReduction u :=
  ((C.formalPointHomAdicCompletion u).ofInjective
      (C.formalPointHomAdicCompletion_injective u)).trans
    (AddEquiv.addSubgroupCongr (C.range_formalPointHomAdicCompletion_eq_kerReduction u))


-- @@ L93-98 verbatim
open scoped Classical in
@[simp]
theorem coe_formalPointAddEquivKerReduction_apply (P : FormalGroupPoint C m_u) :
    (C.formalPointAddEquivKerReduction u P : (C.baseChange F_u).toAffine.Point) =
      C.formalPointHomAdicCompletion u P :=
  (rfl)


-- @@ L100-100 verbatim
end WeierstrassCurve
