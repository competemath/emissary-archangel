import OAI.AlgebraicGeometry.StableCoordinate.DeterminantDomain
import OAI.AlgebraicGeometry.StableCoordinate.ObstructionDefinitions
import OAI.AlgebraicGeometry.StableCoordinate.DeterminantRing


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-12 verbatim
/-!
# Domain instances for the canonical obstruction rings

Transparent adapters from the concrete prime-polynomial proofs in
`DeterminantDomain` to the exact rings used by the filtration and bundle modules.
-/


-- @@ L14-14 verbatim
namespace StableCoordinate.Obstruction


-- @@ L16-16 verbatim
variable (k : Type*) [CommRing k] [IsDomain k] [UniqueFactorizationMonoid k]


-- @@ L18-19 verbatim
theorem quadricRelation_prime : Prime (quadricRelation k) :=
  (DeterminantDomain.quadricRelation_irreducible k).prime


-- @@ L21-22 verbatim
theorem determinantRelation_prime : Prime (determinantRelation k) :=
  (DeterminantDomain.determinantRelation_irreducible k).prime


-- @@ L24-26 verbatim
instance idealB_isPrime : (idealB k).IsPrime := by
  change (Ideal.span {DeterminantDomain.quadricRelation k}).IsPrime
  exact DeterminantDomain.quadricIdeal_isPrime k


-- @@ L28-30 verbatim
instance idealC_isPrime : (idealC k).IsPrime := by
  change (Ideal.span {DeterminantDomain.determinantRelation k}).IsPrime
  exact DeterminantDomain.determinantIdeal_isPrime k


-- @@ L32-32 verbatim
instance B_isDomain : IsDomain (B k) := inferInstance


-- @@ L34-34 verbatim
instance C_isDomain : IsDomain (C k) := inferInstance


-- @@ L36-36 verbatim
end StableCoordinate.Obstruction


-- @@ L38-38 verbatim
namespace StableCoordinate.DeterminantRing


-- @@ L40-40 verbatim
variable (k : Type*) [CommRing k] [IsDomain k] [UniqueFactorizationMonoid k]


-- @@ L42-43 verbatim
theorem relation_prime : Prime (relation k) :=
  (DeterminantDomain.determinantRelation_irreducible k).prime


-- @@ L45-47 verbatim
instance relationIdeal_isPrime : (relationIdeal k).IsPrime := by
  change (Ideal.span {DeterminantDomain.determinantRelation k}).IsPrime
  exact DeterminantDomain.determinantIdeal_isPrime k


-- @@ L49-49 verbatim
instance C_isDomain : IsDomain (C k) := inferInstance


-- @@ L51-51 verbatim
end StableCoordinate.DeterminantRing


-- @@ L53-53 verbatim
namespace StableCoordinate.Obstruction


-- @@ L55-55 verbatim
open MvPolynomial


-- @@ L57-57 verbatim
section Nonzero


-- @@ L59-59 verbatim
variable (k : Type*) [CommRing k] [Nontrivial k]


-- @@ L61-84 verbatim
/-- Every determinant variable has a nonzero image, witnessed by an explicit
matrix of determinant one. -/
theorem cX_ne_zero (i : Fin 5) : cX k i ≠ 0 := by
  let φ : DeterminantRing.C k →ₐ[k] k :=
    DeterminantRing.lift (k := k) (1 : k) 1 0 1 1 (by ring)
  let ψ : DeterminantRing.C k →ₐ[k] k :=
    DeterminantRing.lift (k := k) (1 : k) 0 1 1 1 (by ring)
  intro hz
  fin_cases i
  · have h := congrArg φ hz
    change φ (DeterminantRing.a k) = φ 0 at h
    simp [φ] at h
  · have h := congrArg φ hz
    change φ (DeterminantRing.d k) = φ 0 at h
    simp [φ] at h
  · have h := congrArg ψ hz
    change ψ (DeterminantRing.b k) = ψ 0 at h
    simp [ψ] at h
  · have h := congrArg φ hz
    change φ (DeterminantRing.c k) = φ 0 at h
    simp [φ] at h
  · have h := congrArg φ hz
    change φ (DeterminantRing.u k) = φ 0 at h
    simp [φ] at h


-- @@ L86-93 verbatim
/-- The first factor of the auxiliary leading part of `v` is genuinely nonzero. -/
theorem explicit_au_sub_d_ne_zero : cX k 0 * cX k 4 - cX k 1 ≠ 0 := by
  let φ : DeterminantRing.C k →ₐ[k] k :=
    DeterminantRing.lift (k := k) (1 : k) 0 0 1 1 (by ring)
  intro hz
  have h := congrArg φ hz
  change φ (DeterminantRing.a k * DeterminantRing.u k - DeterminantRing.d k) = φ 0 at h
  simp [φ] at h


-- @@ L95-102 verbatim
/-- The second factor of the auxiliary leading part of `v` is genuinely nonzero. -/
theorem explicit_au_add_d_ne_zero : cX k 0 * cX k 4 + cX k 1 ≠ 0 := by
  let φ : DeterminantRing.C k →ₐ[k] k :=
    DeterminantRing.lift (k := k) (1 : k) 0 0 1 1 (by ring)
  intro hz
  have h := congrArg φ hz
  change φ (DeterminantRing.a k * DeterminantRing.u k + DeterminantRing.d k) = φ 0 at h
  simp [φ] at h


-- @@ L104-116 verbatim
/-- The principal generator of the extended obstruction ideal is nonzero. -/
theorem v_ne_zero : v k ≠ 0 := by
  let φ : DeterminantRing.C k →ₐ[k] k :=
    DeterminantRing.lift (k := k) (1 : k) 0 1 1 0 (by ring)
  have h : φ (DeterminantRing.a k ^ 3 * DeterminantRing.b k +
      DeterminantRing.a k ^ 2 * DeterminantRing.u k ^ 2 -
      DeterminantRing.d k ^ 2) = 1 := by
    simp [φ]
  change φ (v k) = 1 at h
  intro hz
  rw [hz] at h
  change φ (0 : DeterminantRing.C k) = 1 at h
  simp at h


-- @@ L118-118 verbatim
end Nonzero


-- @@ L120-120 verbatim
end StableCoordinate.Obstruction


-- @@ L122-122 verbatim
end OAI
