module

public import BernoulliRegular.Reflection.SingularKummer.TorsionComponent


-- @@ L5-15 verbatim
/-!
# Singular Kummer: finite comparison through a projected subgroup

This file records the finite-group step in the form needed for Lemma 2.1 of
`kummer_reflection.tex`.

If `B` is a finite additive subgroup of `A`, then nontriviality of `B / pB`
forces nontriviality of `B[p]`.  Therefore, if the natural inclusion
`B[p] -> A[p]` lands in a chosen character component of `A[p]`, that component
is nontrivial.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
namespace BernoulliRegular

-- @@ L22-22 verbatim
namespace Reflection

-- @@ L23-23 verbatim
namespace SingularKummer


-- @@ L25-25 verbatim
namespace ProjectedSubgroupComparison


-- @@ L27-27 verbatim
open TorsionComponent


-- @@ L29-29 verbatim
variable {p : ℕ}

-- @@ L30-30 verbatim
variable {A : Type*} [AddCommGroup A]


-- @@ L32-44 verbatim
/-- The inclusion `B[p] -> A[p]` for an additive subgroup `B <= A`. -/
def subgroupTorsionToTorsion (B : AddSubgroup A) (p : ℕ) :
    torsionBySubgroup B p →+ torsionBySubgroup A p where
  toFun x :=
    ⟨(x.1 : A), by
      have hx := congrArg (fun y : B ↦ (y : A)) x.2
      simpa using hx⟩
  map_zero' := by
    apply Subtype.ext
    rfl
  map_add' x y := by
    apply Subtype.ext
    rfl


-- @@ L46-51 verbatim
@[simp]
theorem subgroupTorsionToTorsion_apply_coe
    (B : AddSubgroup A) (p : ℕ) (x : torsionBySubgroup B p) :
    ((subgroupTorsionToTorsion B p x : torsionBySubgroup A p) : A) =
      (x.1 : A) :=
  rfl


-- @@ L53-74 verbatim
/-- If a finite subgroup has nontrivial quotient modulo `p`, and its
`p`-torsion lies in a chosen projected component of `A[p]`, then that projected
component is nontrivial. -/
theorem torsionComponentNontrivial_of_projectedSubgroup
    [NeZero p] (i : ℕ) (ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A))
    (B : AddSubgroup A) [Finite B]
    (hquot : Nontrivial (elementaryQuotient B p))
    (hmem : ∀ x : torsionBySubgroup B p,
      subgroupTorsionToTorsion B p x ∈ torsionComponent (p := p) i ρ) :
    TorsionComponentNontrivial (p := p) i ρ := by
  have htorsion : Nontrivial (torsionBySubgroup B p) :=
    torsionBySubgroup_nontrivial_of_elementaryQuotient_nontrivial
      (A := B) hquot
  obtain ⟨x, hx_ne⟩ := exists_ne (0 : torsionBySubgroup B p)
  refine torsionComponentNontrivial_of_exists_ne_zero_mem ?_
  refine ⟨subgroupTorsionToTorsion B p x, ?_, hmem x⟩
  intro hx_zero
  apply hx_ne
  have hxA : (x.1 : A) = 0 := by
    simpa [subgroupTorsionToTorsion] using
      congrArg (fun y : torsionBySubgroup A p ↦ (y.1 : A)) hx_zero
  exact Subtype.ext (Subtype.ext hxA)


-- @@ L76-76 verbatim
end ProjectedSubgroupComparison


-- @@ L78-78 verbatim
end SingularKummer

-- @@ L79-79 verbatim
end Reflection

-- @@ L80-80 verbatim
end BernoulliRegular


-- @@ L82-82 verbatim
end


-- @@ L84-84 verbatim
end
