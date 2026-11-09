import ModularCurves.LevelStructure.CartierDivisor
import ModularCurves.ForMathlib.BaseChangeAlongCompat


-- @@ L4-19 verbatim
/-!
# Pushforward of a relative effective Cartier divisor along an automorphism

Construction support for `[CHARTER-HOPF]` Wave C leaf `[HG-C3]`
(`.mathlib-quality/decomposition-hopf-c3-cover.md`). For an `S`-automorphism `φ` of the total
space of `π : C ⟶ S` (i.e. `φ.hom ≫ π = π`), `RelEffCartierDiv.mapIso φ` pushes a relative
effective Cartier divisor forward: the ideal sheaf transports by `comap φ.inv`, and the
`finite`/`flat`/`lfp`-over-`S` fields transport because the base change of the iso `φ.inv`
along the divisor inclusion is again an iso.

The `[HG-C3]` cover uses this with `φ = E.translateByIso x` to form the shifted divisor
`x + D` (a degree-`N` divisor whose complement `E ∖ (x + D)` is the second affine chart).
-/

-- v4.33 bump: opens/hom coercions are no longer transparent enough for the
-- `≫`-associativity and `comp_apply` rewrites below.

-- @@ L20-20 verbatim
set_option backward.defeqAttrib.useBackward true

-- @@ L21-21 verbatim
set_option backward.isDefEq.respectTransparency false


-- @@ L23-23 verbatim
open AlgebraicGeometry CategoryTheory Limits


-- @@ L25-25 verbatim
universe u


-- @@ L27-27 verbatim
namespace ModularCurves


-- @@ L29-29 verbatim
namespace RelEffCartierDiv


-- @@ L31-31 verbatim
variable {C S : Scheme.{u}} {π : C ⟶ S}


-- @@ L33-44 verbatim
/-- The inclusion of the pushforward divisor's subscheme, composed with `π`, factors as an
isomorphism followed by the original inclusion-over-`S` — the engine of the transport. -/
theorem comapIso_subschemeι_comp (φ : C ≅ C) (hφ : φ.hom ≫ π = π) (D : RelEffCartierDiv π) :
    (D.ideal.comap φ.inv).subschemeι ≫ π
      = ((D.ideal.comapIso φ.inv).hom ≫ pullback.snd φ.inv D.ideal.subschemeι)
        ≫ (D.ideal.subschemeι ≫ π) := by
  rw [← Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc, Category.assoc]
  congr 1
  have h1 : pullback.fst φ.inv D.ideal.subschemeι ≫ π
      = pullback.fst φ.inv D.ideal.subschemeι ≫ φ.inv ≫ φ.hom ≫ π := by
    rw [Iso.inv_hom_id_assoc]
  rw [h1, ← Category.assoc, pullback.condition, hφ, Category.assoc]


-- @@ L46-61 verbatim
/-- **Pushforward of a relative effective Cartier divisor along an `S`-automorphism** `φ`
(`φ.hom ≫ π = π`). The ideal sheaf is `comap φ.inv`; finiteness / flatness / local finite
presentation transport along the iso. Used for the coset divisor `x + D` in `[HG-C3]`. -/
noncomputable def mapIso (φ : C ≅ C) (hφ : φ.hom ≫ π = π) (D : RelEffCartierDiv π) :
    RelEffCartierDiv π where
  ideal := D.ideal.comap φ.inv
  finite := by
    rw [comapIso_subschemeι_comp φ hφ D]
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite) _ _).mpr D.finite
  flat := by
    rw [comapIso_subschemeι_comp φ hφ D]
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @Flat) _ _).mpr D.flat
  lfp := by
    rw [comapIso_subschemeι_comp φ hφ D]
    exact (MorphismProperty.cancel_left_of_respectsIso
      (P := @LocallyOfFinitePresentation) _ _).mpr D.lfp


-- @@ L63-66 verbatim
@[simp]
theorem mapIso_ideal (φ : C ≅ C) (hφ : φ.hom ≫ π = π) (D : RelEffCartierDiv π) :
    (mapIso φ hφ D).ideal = D.ideal.comap φ.inv :=
  rfl


-- @@ L68-68 verbatim
end RelEffCartierDiv


-- @@ L70-70 verbatim
end ModularCurves
