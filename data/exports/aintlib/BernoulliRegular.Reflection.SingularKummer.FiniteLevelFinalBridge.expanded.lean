module

public import BernoulliRegular.Reflection.SingularKummer.FiniteLevelQuotientComparison


-- @@ L5-12 verbatim
/-!
# Singular Kummer: final finite-level bridge

This file assembles the exact finite-level subgroup argument.  The exact
projection subgroup covers the quotient component `V_i`, and its `p`-torsion
lies in the matching `A[p]_i` component.  Therefore nontriviality of `V_i`
implies nontriviality of `A[p]_i`.
-/


-- @@ L14-14 verbatim
@[expose] public section


-- @@ L16-16 verbatim
noncomputable section


-- @@ L18-18 verbatim
namespace BernoulliRegular

-- @@ L19-19 verbatim
namespace Reflection

-- @@ L20-20 verbatim
namespace SingularKummer


-- @@ L22-22 verbatim
namespace FiniteLevelFinalBridge


-- @@ L24-24 verbatim
open ElementaryQuotientComponent

-- @@ L25-25 verbatim
open TorsionComponent


-- @@ L27-27 verbatim
variable {p m : ℕ} [NeZero p] [NeZero m]

-- @@ L28-28 verbatim
variable {A : Type*} [AddCommGroup A] [Module (ZMod m) A] [Finite A]


-- @@ L30-59 verbatim
/-- The final finite-level comparison: an exact lifted character idempotent
whose coefficients and character reduce to the expected mod-`p` data converts
nontriviality of `V_i` into nontriviality of the corresponding `A[p]_i`
component. -/
theorem torsionComponentNontrivial_of_finiteLevelCharacter
    (hcard : IsUnit (Fintype.card (CharacterProjection.Delta p) : ZMod p))
    (hm : p ∣ m) (i : ℕ)
    (rho : CharacterProjection.Delta p →* Multiplicative (A ≃+ A))
    (chi : CharacterProjection.Delta p →* (ZMod m)ˣ)
    (hcoeff : ∀ d : CharacterProjection.Delta p,
      ZMod.castHom hm (ZMod p)
          (FiniteLevelIdempotent.coefficient (m := m) chi d) =
        CharacterProjection.characterProjectionCoefficient (p := p) i d)
    (hchi : ∀ d : CharacterProjection.Delta p,
      ZMod.castHom hm (ZMod p) (chi d : ZMod m) = ((d : ZMod p) ^ i))
    (hV : ElementaryComponentNontrivial (p := p) i rho) :
    TorsionComponentNontrivial (p := p) i rho := by
  let B : AddSubgroup A :=
    FiniteLevelAdditiveProjection.componentSubgroup (m := m) rho chi
  exact FiniteLevelProjectionBridge.torsionComponentNontrivial_of_finiteLevelSubgroup
    (p := p) i rho B hV
    (FiniteLevelQuotientComparison.elementaryComponent_le_finiteLevelComponent_image
      (p := p) (m := m) hm i rho chi hcoeff)
    (fun x ↦ by
      exact FiniteLevelTorsionReduction.mem_torsionComponent_of_mem_finiteLevelComponent
        (p := p) (m := m) hcard hm i rho chi hchi
        (x := ProjectedSubgroupComparison.subgroupTorsionToTorsion B p x)
        (by
          change (((x : torsionBySubgroup B p).1 : B) : A) ∈ B
          exact ((x : torsionBySubgroup B p).1 : B).2))


-- @@ L61-61 verbatim
end FiniteLevelFinalBridge


-- @@ L63-63 verbatim
end SingularKummer

-- @@ L64-64 verbatim
end Reflection

-- @@ L65-65 verbatim
end BernoulliRegular


-- @@ L67-67 verbatim
end


-- @@ L69-69 verbatim
end
