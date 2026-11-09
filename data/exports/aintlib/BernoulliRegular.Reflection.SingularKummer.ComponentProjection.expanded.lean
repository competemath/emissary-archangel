module

public import BernoulliRegular.Reflection.SingularKummer.ComponentChoice


-- @@ L5-14 verbatim
/-!
# Singular Kummer: component ranges under a surjective map

If a surjective homomorphism commutes with two endomorphisms, then it maps the
range of the source endomorphism onto the range of the target endomorphism.

For the singular-Kummer argument this is the elementary algebra behind
component surjectivity once the character component is realized as the range
of the corresponding projection operator.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
namespace BernoulliRegular

-- @@ L19-19 verbatim
namespace Reflection

-- @@ L20-20 verbatim
namespace SingularKummer


-- @@ L22-22 verbatim
namespace ComponentProjection


-- @@ L24-24 verbatim
variable {G H : Type*} [Group G] [Group H]


-- @@ L26-34 verbatim
/-- A surjective homomorphism commuting with two endomorphisms maps the source
projection range onto the target projection range. -/
theorem map_range_eq_range_of_surjective_of_commute
    (φ : G →* H) (eG : G →* G) (eH : H →* H)
    (hφ : Function.Surjective φ)
    (hcomm : ∀ x : G, φ (eG x) = eH (φ x)) :
    eG.range.map φ = eH.range := by
  rw [MonoidHom.map_range, show φ.comp eG = eH.comp φ from MonoidHom.ext hcomm,
    MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hφ, ← MonoidHom.range_eq_map]


-- @@ L36-36 verbatim
variable (R K : Type*) [CommRing R] [IsDomain R]

-- @@ L37-37 verbatim
variable [Field K] [Algebra R K] [IsFractionRing R K]


-- @@ L39-59 verbatim
/-- Singular-sequence specialization: commuting projection operators on `S`
and `A[p]` give a surjection from the projected singular component to the
projected class-group component. -/
theorem singular_map_range_eq_range_of_commute
    (p : ℕ)
    (eS :
      SingularPair.SingularGroup (R := R) (K := K) p →*
        SingularPair.SingularGroup (R := R) (K := K) p)
    (eA :
      SingularPair.classGroupPTorsion (R := R) p →*
        SingularPair.classGroupPTorsion (R := R) p)
    (hcomm : ∀ x : SingularPair.SingularGroup (R := R) (K := K) p,
      SingularPair.singularGroupClassMapToPTorsion (R := R) (K := K) p (eS x) =
        eA (SingularPair.singularGroupClassMapToPTorsion (R := R) (K := K) p x)) :
    eS.range.map (SingularPair.singularGroupClassMapToPTorsion (R := R) (K := K) p) =
      eA.range :=
  map_range_eq_range_of_surjective_of_commute
    (SingularPair.singularGroupClassMapToPTorsion (R := R) (K := K) p)
    eS eA
    (SingularPair.singularGroupClassMapToPTorsion_surjective (R := R) (K := K) p)
    hcomm


-- @@ L61-80 verbatim
/-- If the projected `A[p]` component is nontrivial, then there is a singular
class in the projected singular component with nontrivial image. -/
theorem exists_singular_projection_lift_of_target_ne_bot
    (p : ℕ)
    (eS :
      SingularPair.SingularGroup (R := R) (K := K) p →*
        SingularPair.SingularGroup (R := R) (K := K) p)
    (eA :
      SingularPair.classGroupPTorsion (R := R) p →*
        SingularPair.classGroupPTorsion (R := R) p)
    (hcomm : ∀ x : SingularPair.SingularGroup (R := R) (K := K) p,
      SingularPair.singularGroupClassMapToPTorsion (R := R) (K := K) p (eS x) =
        eA (SingularPair.singularGroupClassMapToPTorsion (R := R) (K := K) p x))
    (hA : eA.range ≠ ⊥) :
    ∃ x : eS.range,
      SingularPair.singularGroupClassMapToPTorsion (R := R) (K := K) p x.1 ≠ 1 :=
  ComponentChoice.exists_singular_lift_of_component_map_eq_of_ne_bot
    (R := R) (K := K) p eS.range eA.range
    (singular_map_range_eq_range_of_commute (R := R) (K := K) p eS eA hcomm)
    hA


-- @@ L82-82 verbatim
end ComponentProjection


-- @@ L84-84 verbatim
end SingularKummer

-- @@ L85-85 verbatim
end Reflection

-- @@ L86-86 verbatim
end BernoulliRegular


-- @@ L88-88 verbatim
end
