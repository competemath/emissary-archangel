/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import BernoulliRegular.Reflection.SingularKummer.CharacterProjection


-- @@ L10-20 verbatim
/-!
# Singular Kummer: `ZMod p` structures on the singular exact sequence

The singular quotient `S` is killed by `p`: for a singular pair
`(I, alpha)` with `(alpha) = I^p`, the `p`-th power of the pair is the
principal pair attached to `alpha`, hence trivial in the quotient by principal
pairs.  The target `A[p]` is killed by `p` by definition.

After passing to additive notation, both sides become `ZMod p`-modules and the
map `S → A[p]` becomes a surjective `ZMod p`-linear map.
-/


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
noncomputable section


-- @@ L26-26 verbatim
open scoped nonZeroDivisors


-- @@ L28-28 verbatim
namespace BernoulliRegular

-- @@ L29-29 verbatim
namespace Reflection

-- @@ L30-30 verbatim
namespace SingularKummer


-- @@ L32-32 verbatim
namespace SingularPair


-- @@ L34-34 verbatim
variable (R K : Type*) [CommRing R] [IsDomain R]

-- @@ L35-35 verbatim
variable [Field K] [Algebra R K] [IsFractionRing R K]


-- @@ L37-46 verbatim
/-- The `p`-th power of a singular pair is the principal pair attached to its
generator. -/
theorem pow_eq_principalPair_generator (p : ℕ) (s : SingularPair R K p) :
    s ^ p = principalPair (R := R) (K := K) p (generator s) := by
  apply Subtype.ext
  apply Prod.ext
  · change ideal s ^ p = toPrincipalIdeal R K (generator s)
    exact (principal_eq_ideal_pow (R := R) (K := K) s).symm
  · change generator s ^ p = generator s ^ p
    rfl


-- @@ L48-54 verbatim
/-- The image of a singular pair in the singular quotient is killed by `p`. -/
theorem singularGroup_mk_pow_eq_one (p : ℕ) (s : SingularPair R K p) :
    ((QuotientGroup.mk s : SingularGroup (R := R) (K := K) p) ^ p) = 1 := by
  rw [← QuotientGroup.mk_pow]
  exact (QuotientGroup.eq_one_iff
    (N := principalPairSubgroup (R := R) (K := K) p) (s ^ p)).2
      ⟨generator s, (pow_eq_principalPair_generator (R := R) (K := K) p s).symm⟩


-- @@ L56-62 verbatim
/-- Every element of the singular quotient is killed by `p`. -/
theorem singularGroup_pow_eq_one (p : ℕ)
    (x : SingularGroup (R := R) (K := K) p) :
    x ^ p = 1 := by
  refine QuotientGroup.induction_on x ?_
  intro s
  exact singularGroup_mk_pow_eq_one (R := R) (K := K) p s


-- @@ L64-68 verbatim
/-- Every element of `A[p]` is killed by `p`, by definition. -/
theorem classGroupPTorsion_pow_eq_one (p : ℕ)
    (x : classGroupPTorsion (R := R) p) :
    x ^ p = 1 :=
  Subtype.ext <| show (x.1 ^ p = 1) from x.2


-- @@ L70-76 verbatim
/-- Additive `ZMod p`-module structure on the singular quotient. -/
instance instModuleZModAdditiveSingularGroup (p : ℕ) :
    Module (ZMod p) (Additive (SingularGroup (R := R) (K := K) p)) :=
  AddCommGroup.zmodModule (n := p) fun x => by
    apply Additive.ext
    rw [toMul_nsmul, toMul_zero]
    exact singularGroup_pow_eq_one (R := R) (K := K) p x.toMul


-- @@ L78-84 verbatim
/-- Additive `ZMod p`-module structure on `A[p]`. -/
instance instModuleZModAdditiveClassGroupPTorsion (p : ℕ) :
    Module (ZMod p) (Additive (classGroupPTorsion (R := R) p)) :=
  AddCommGroup.zmodModule (n := p) fun x => by
    apply Additive.ext
    rw [toMul_nsmul, toMul_zero]
    exact classGroupPTorsion_pow_eq_one (R := R) p x.toMul


-- @@ L86-91 verbatim
/-- The singular quotient map as a `ZMod p`-linear map after passing to
additive notation. -/
def singularGroupClassMapToPTorsionLinear (p : ℕ) :
    Additive (SingularGroup (R := R) (K := K) p) →ₗ[ZMod p]
      Additive (classGroupPTorsion (R := R) p) :=
  (singularGroupClassMapToPTorsion (R := R) (K := K) p).toAdditive.toZModLinearMap p


-- @@ L93-98 verbatim
@[simp]
theorem singularGroupClassMapToPTorsionLinear_apply_toMul (p : ℕ)
    (x : Additive (SingularGroup (R := R) (K := K) p)) :
    (singularGroupClassMapToPTorsionLinear (R := R) (K := K) p x).toMul =
      singularGroupClassMapToPTorsion (R := R) (K := K) p x.toMul :=
  rfl


-- @@ L100-108 verbatim
/-- The linearized singular quotient map is surjective. -/
theorem singularGroupClassMapToPTorsionLinear_surjective (p : ℕ) :
    Function.Surjective
      (singularGroupClassMapToPTorsionLinear (R := R) (K := K) p) := by
  intro y
  obtain ⟨x, hx⟩ :=
    singularGroupClassMapToPTorsion_surjective (R := R) (K := K) p y.toMul
  refine ⟨Additive.ofMul x, ?_⟩
  exact Additive.ext <| hx


-- @@ L110-110 verbatim
end SingularPair


-- @@ L112-112 verbatim
end SingularKummer

-- @@ L113-113 verbatim
end Reflection

-- @@ L114-114 verbatim
end BernoulliRegular


-- @@ L116-116 verbatim
end


-- @@ L118-118 verbatim
end
