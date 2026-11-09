module

public import BernoulliRegular.Reflection.SingularKummer.SingularPair


-- @@ L5-12 verbatim
/-!
# Singular Kummer: choosing a nontrivial lift from a component

This file isolates the elementary group-theoretic part of the later singular-Kummer lift
argument.  Once a character component of the singular group maps onto the
matching character component of `A[p]`, any nontrivial element in the target
component has a lift in the source component with nontrivial image.
-/


-- @@ L14-14 verbatim
@[expose] public section


-- @@ L16-16 verbatim
namespace BernoulliRegular

-- @@ L17-17 verbatim
namespace Reflection

-- @@ L18-18 verbatim
namespace SingularKummer


-- @@ L20-20 verbatim
namespace ComponentChoice


-- @@ L22-22 verbatim
variable {G H : Type*} [Group G] [Group H]


-- @@ L24-36 verbatim
/-- If `φ` maps the subgroup `S` onto the subgroup `T`, and `T` is nontrivial,
then some element of `S` has nontrivial image. -/
theorem exists_lift_of_map_eq_of_nontrivial
    (φ : G →* H) (S : Subgroup G) (T : Subgroup H)
    [Nontrivial T] (hmap : S.map φ = T) :
    ∃ x : S, φ x.1 ≠ 1 := by
  obtain ⟨y, hy_mem, hy_ne⟩ := Subgroup.exists_ne_one_of_nontrivial T
  have hy_map : y ∈ S.map φ := by
    simpa [hmap] using hy_mem
  obtain ⟨x, hxS, hx⟩ := hy_map
  refine ⟨⟨x, hxS⟩, ?_⟩
  intro hx_one
  exact hy_ne (by rw [← hx, hx_one])


-- @@ L38-44 verbatim
/-- A version using `T ≠ ⊥` instead of a typeclass `Nontrivial T`. -/
theorem exists_lift_of_map_eq_of_ne_bot
    (φ : G →* H) (S : Subgroup G) (T : Subgroup H)
    (hmap : S.map φ = T) (hT : T ≠ ⊥) :
    ∃ x : S, φ x.1 ≠ 1 := by
  have : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot T).2 hT
  exact exists_lift_of_map_eq_of_nontrivial φ S T hmap


-- @@ L46-55 verbatim
/-- Elementwise form: the lift can be viewed in the ambient source group and
its image lies in the target component. -/
theorem exists_mem_lift_with_nontrivial_image_of_ne_bot
    (φ : G →* H) (S : Subgroup G) (T : Subgroup H)
    (hmap : S.map φ = T) (hT : T ≠ ⊥) :
    ∃ x : G, x ∈ S ∧ φ x ∈ T ∧ φ x ≠ 1 := by
  obtain ⟨x, hx_ne⟩ := exists_lift_of_map_eq_of_ne_bot φ S T hmap hT
  refine ⟨x.1, x.2, ?_, hx_ne⟩
  rw [← hmap]
  exact ⟨x.1, x.2, rfl⟩


-- @@ L57-65 verbatim
/-- A surjective component map forces the source component to be nontrivial
whenever the target component is nontrivial. -/
theorem source_ne_bot_of_map_eq_of_target_ne_bot
    (φ : G →* H) (S : Subgroup G) (T : Subgroup H)
    (hmap : S.map φ = T) (hT : T ≠ ⊥) :
    S ≠ ⊥ := by
  obtain ⟨x, hx_ne⟩ := exists_lift_of_map_eq_of_ne_bot φ S T hmap hT
  exact (Subgroup.nontrivial_iff_ne_bot S).1
    ⟨⟨x, 1, fun h ↦ hx_ne (by simpa using congrArg (fun z : S ↦ φ z.1) h)⟩⟩


-- @@ L67-67 verbatim
open scoped nonZeroDivisors


-- @@ L69-69 verbatim
variable (R K : Type*) [CommRing R] [IsDomain R]

-- @@ L70-70 verbatim
variable [Field K] [Algebra R K] [IsFractionRing R K]


-- @@ L72-88 verbatim
/-- Singular-sequence form of the component-lifting lemma.  If a chosen
component of the singular group maps onto a chosen component of `A[p]`, then a
nontrivial element of the target component has a singular lift in the source
component. -/
theorem exists_singular_lift_of_component_map_eq_of_ne_bot
    (p : ℕ)
    (Scomp : Subgroup (SingularPair.SingularGroup (R := R) (K := K) p))
    (Acomp : Subgroup (SingularPair.classGroupPTorsion (R := R) p))
    (hmap :
      Scomp.map (SingularPair.singularGroupClassMapToPTorsion
        (R := R) (K := K) p) = Acomp)
    (hA : Acomp ≠ ⊥) :
    ∃ x : Scomp,
      SingularPair.singularGroupClassMapToPTorsion (R := R) (K := K) p x.1 ≠ 1 :=
  exists_lift_of_map_eq_of_ne_bot
    (SingularPair.singularGroupClassMapToPTorsion (R := R) (K := K) p)
    Scomp Acomp hmap hA


-- @@ L90-106 verbatim
/-- Elementwise singular-sequence form, with membership in the chosen source
and target components recorded explicitly. -/
theorem exists_singular_mem_lift_with_nontrivial_class_of_component_map_eq_of_ne_bot
    (p : ℕ)
    (Scomp : Subgroup (SingularPair.SingularGroup (R := R) (K := K) p))
    (Acomp : Subgroup (SingularPair.classGroupPTorsion (R := R) p))
    (hmap :
      Scomp.map (SingularPair.singularGroupClassMapToPTorsion
        (R := R) (K := K) p) = Acomp)
    (hA : Acomp ≠ ⊥) :
    ∃ x : SingularPair.SingularGroup (R := R) (K := K) p,
      x ∈ Scomp ∧
        SingularPair.singularGroupClassMapToPTorsion (R := R) (K := K) p x ∈ Acomp ∧
          SingularPair.singularGroupClassMapToPTorsion (R := R) (K := K) p x ≠ 1 :=
  exists_mem_lift_with_nontrivial_image_of_ne_bot
    (SingularPair.singularGroupClassMapToPTorsion (R := R) (K := K) p)
    Scomp Acomp hmap hA


-- @@ L108-108 verbatim
end ComponentChoice


-- @@ L110-110 verbatim
end SingularKummer

-- @@ L111-111 verbatim
end Reflection

-- @@ L112-112 verbatim
end BernoulliRegular


-- @@ L114-114 verbatim
end
