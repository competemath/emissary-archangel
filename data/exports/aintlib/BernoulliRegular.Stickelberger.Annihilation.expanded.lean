module

public import BernoulliRegular.Stickelberger.Action


-- @@ L5-13 verbatim
/-!
# Stickelberger class-group annihilation package

This file packages the principality result in class-group language.
The current Gauss-sum factorisation API is character-side and applies to the
orbit of the distinguished prime above `p`; the statements here expose that
precise class-group action without introducing a broader class-group module
formalisation yet.
-/


-- @@ L15-15 verbatim
@[expose] public section


-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
open NumberField IsCyclotomicExtension

-- @@ L20-20 verbatim
open scoped NumberField Pointwise nonZeroDivisors


-- @@ L22-22 verbatim
namespace BernoulliRegular


-- @@ L24-24 verbatim
section CharacterSideAnnihilation


-- @@ L26-27 verbatim
variable (p : ℕ) [hp : Fact p.Prime]
  (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {p * (p - 1)} ℚ L]


-- @@ L29-29 verbatim
local instance : NeZero (p - 1) := ⟨Nat.sub_ne_zero_of_lt hp.out.one_lt⟩


-- @@ L31-38 verbatim
/-- A character-side translate of the distinguished prime, bundled as a
nonzero ideal for use in `ClassGroup.mk0`. -/
noncomputable def characterSidePrimeClassIdeal (b : (ZMod (p - 1))ˣ) :
    (Ideal (𝓞 L))⁰ :=
  ⟨sigmaOfCharacterUnit (p := p) L b • distinguishedPrimeAboveP p L,
    mem_nonZeroDivisors_iff_ne_zero.mpr
      (primeAboveP_ne_bot (p := p) (L := L)
        (P := sigmaOfCharacterUnit (p := p) L b • distinguishedPrimeAboveP p L))⟩


-- @@ L40-46 verbatim
/-- The class-group action of a nonnegative character-side group-ring exponent
on the distinguished prime class. Coefficients are read in the same inverse
basis convention as `characterSideStickelbergerIdealAction`. -/
noncomputable def characterSideStickelbergerClassAction
    (E : MonoidAlgebra ℤ (ZMod (p - 1))ˣ) : ClassGroup (𝓞 L) :=
  ∏ b : (ZMod (p - 1))ˣ,
    ClassGroup.mk0 (characterSidePrimeClassIdeal (p := p) (L := L) b) ^ (E.coeff b⁻¹).toNat


-- @@ L48-69 verbatim
/-- The class-group product induced by `E` is the class of the corresponding
ideal product. -/
lemma classGroup_mk0_characterSideStickelbergerIdealAction_eq_classAction
    (E : MonoidAlgebra ℤ (ZMod (p - 1))ˣ)
    (hE : characterSideStickelbergerIdealAction (p := p) (L := L) E ≠ ⊥) :
    ClassGroup.mk0
        (⟨characterSideStickelbergerIdealAction (p := p) (L := L) E,
          mem_nonZeroDivisors_iff_ne_zero.mpr hE⟩ : (Ideal (𝓞 L))⁰) =
      characterSideStickelbergerClassAction (p := p) (L := L) E := by
  let F : (ZMod (p - 1))ˣ → (Ideal (𝓞 L))⁰ := fun b ↦
    (characterSidePrimeClassIdeal (p := p) (L := L) b) ^ (E.coeff b⁻¹).toNat
  have hprod :
      (∏ b : (ZMod (p - 1))ˣ, F b : (Ideal (𝓞 L))⁰).1 =
        characterSideStickelbergerIdealAction (p := p) (L := L) E := by
    simp [F, characterSideStickelbergerIdealAction, characterSidePrimeClassIdeal]
  have hsub :
      (⟨characterSideStickelbergerIdealAction (p := p) (L := L) E,
        mem_nonZeroDivisors_iff_ne_zero.mpr hE⟩ : (Ideal (𝓞 L))⁰) =
        ∏ b : (ZMod (p - 1))ˣ, F b :=
    Subtype.ext <| hprod.symm
  rw [hsub, map_prod]
  simp [F, characterSideStickelbergerClassAction]


-- @@ L71-84 verbatim
/-- The character-side Stickelberger exponent supplied by the
Gauss-sum factorisation annihilates the distinguished-prime class. -/
theorem stickelbergerCharacterCoefficientGroupRingTarget_annihilates_primeClass
    (hp_odd : p ≠ 2) {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) :
    characterSideStickelbergerClassAction (p := p) (L := L)
        (stickelbergerCharacterCoefficientGroupRingTarget (p := p) (L := L) χ) =
      (1 : ClassGroup (𝓞 L)) := by
  rw [← classGroup_mk0_characterSideStickelbergerIdealAction_eq_classAction
    (p := p) (L := L)
    (E := stickelbergerCharacterCoefficientGroupRingTarget (p := p) (L := L) χ)
    (hE := characterSideStickelbergerIdealAction_ne_bot (p := p) (L := L) hp_odd hχ)]
  simpa [characterSideStickelbergerIdealActionClassIdeal] using
    classGroup_mk0_characterSideStickelbergerIdealAction_eq_one
      (p := p) (L := L) hp_odd hχ


-- @@ L86-86 verbatim
end CharacterSideAnnihilation


-- @@ L88-88 verbatim
end BernoulliRegular


-- @@ L90-90 verbatim
end
