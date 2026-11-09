module

public import BernoulliRegular.Reflection.SingularKummer.SingularRepresentative


-- @@ L5-17 verbatim
/-!
# Singular Kummer: character projections are eigenspaces

This file proves the elementary eigenspace calculation for the character
projection

```text
  e_i = |Delta|^{-1} sum_a a^{-i} [a].
```

If an element lies in the range of this projection, then the action of
`b : Delta` on it is multiplication by `b^i`.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
open scoped nonZeroDivisors


-- @@ L25-25 verbatim
namespace BernoulliRegular

-- @@ L26-26 verbatim
namespace Reflection

-- @@ L27-27 verbatim
namespace SingularKummer


-- @@ L29-29 verbatim
namespace CharacterProjection


-- @@ L31-31 verbatim
variable {p : ℕ} [NeZero p]

-- @@ L32-32 verbatim
variable {M : Type*} [AddCommGroup M] [Module (ZMod p) M]


-- @@ L34-43 verbatim
/-- Reindexing coefficient identity for the `i`-th character. -/
theorem characterProjectionCoefficient_inv_mul
    (i : ℕ) (b a : Delta p) :
    characterProjectionCoefficient (p := p) i (b⁻¹ * a) =
      ((b : ZMod p) ^ i) * characterProjectionCoefficient (p := p) i a := by
  have hinv : (b⁻¹ * a)⁻¹ = a⁻¹ * b := by group
  rw [characterProjectionCoefficient, characterProjectionCoefficient, hinv]
  simp only [Units.val_mul]
  rw [mul_pow]
  ring


-- @@ L45-63 verbatim
/-- The character projection is contained in the eigenspace for the
corresponding character. -/
theorem apply_characterProjection
    (i : ℕ) (ρ : Delta p →* M ≃ₗ[ZMod p] M) (b : Delta p) (x : M) :
    ρ b (characterProjection (p := p) i ρ x) =
      ((b : ZMod p) ^ i) • characterProjection (p := p) i ρ x := by
  calc
    ρ b (characterProjection (p := p) i ρ x)
        = ∑ a : Delta p,
            characterProjectionCoefficient (p := p) i a • ρ (b * a) x := by
          simp [characterProjection, projection, map_mul]
    _ = ∑ a : Delta p,
            characterProjectionCoefficient (p := p) i (b⁻¹ * a) • ρ a x := by
          refine Fintype.sum_equiv (Equiv.mulLeft b) _ _ ?_
          intro a
          simp [map_mul]
    _ = ((b : ZMod p) ^ i) • characterProjection (p := p) i ρ x := by
          simp [characterProjection, projection, characterProjectionCoefficient_inv_mul,
            smul_smul, Finset.smul_sum]


-- @@ L65-73 verbatim
/-- Elementwise eigenspace statement for the range of the character
projection. -/
theorem mem_characterProjection_range_apply
    (i : ℕ) (ρ : Delta p →* M ≃ₗ[ZMod p] M) (b : Delta p)
    {x : M}
    (hx : x ∈ LinearMap.range (characterProjection (p := p) i ρ)) :
    ρ b x = ((b : ZMod p) ^ i) • x := by
  obtain ⟨y, rfl⟩ := hx
  exact apply_characterProjection (p := p) i ρ b y


-- @@ L75-75 verbatim
end CharacterProjection


-- @@ L77-77 verbatim
namespace SingularLinearAction

-- @@ L78-78 verbatim
namespace SingularPair


-- @@ L80-80 verbatim
variable (R K : Type*) [CommRing R] [IsDomain R]

-- @@ L81-81 verbatim
variable [Field K] [Algebra R K] [IsFractionRing R K]


-- @@ L83-103 verbatim
/-- Singular-quotient form of the character eigenspace relation.
If the additive class of `x` lies in the `i`-th projection range, then the
action of `b` on `x` is scalar multiplication by `(b : ZMod p)^i` after
passing to additive notation. -/
theorem singularGroup_additive_apply_eq_smul_of_mem_characterProjection_range
    (p : ℕ) [NeZero p] (i : ℕ)
    (ρS :
      CharacterProjection.Delta p →*
        SingularKummer.SingularPair.SingularGroup (R := R) (K := K) p ≃*
          SingularKummer.SingularPair.SingularGroup (R := R) (K := K) p)
    (b : CharacterProjection.Delta p)
    {x : SingularKummer.SingularPair.SingularGroup (R := R) (K := K) p}
    (hx :
      Additive.ofMul x ∈
        LinearMap.range
          (CharacterProjection.characterProjection (p := p) i
            (mulActionToAdditiveLinearAction (p := p) ρS))) :
    Additive.ofMul (ρS b x) =
      ((b : ZMod p) ^ i) • Additive.ofMul x :=
  CharacterProjection.mem_characterProjection_range_apply
      (p := p) i (mulActionToAdditiveLinearAction (p := p) ρS) b hx


-- @@ L105-154 verbatim
/-- Combined representative-and-eigen statement for the singular-Kummer argument.  From a
nontrivial projected component of `A[p]`, choose a singular pair `(I, alpha)`
with nontrivial class image, satisfying `(alpha) = I^p`, whose singular
quotient class lies in the `i`-th projection range and therefore satisfies the
corresponding eigenspace relation. -/
theorem exists_representative_with_eigen_relation_of_target_ne_bot
    (p : ℕ) [NeZero p] (i : ℕ)
    (ρS :
      CharacterProjection.Delta p →*
        SingularKummer.SingularPair.SingularGroup (R := R) (K := K) p ≃*
          SingularKummer.SingularPair.SingularGroup (R := R) (K := K) p)
    (ρA :
      CharacterProjection.Delta p →*
        SingularKummer.SingularPair.classGroupPTorsion (R := R) p ≃*
          SingularKummer.SingularPair.classGroupPTorsion (R := R) p)
    (hρ : ∀ (d : CharacterProjection.Delta p)
        (x : SingularKummer.SingularPair.SingularGroup (R := R) (K := K) p),
      SingularKummer.SingularPair.singularGroupClassMapToPTorsion (R := R) (K := K) p (ρS d x) =
        ρA d (SingularKummer.SingularPair.singularGroupClassMapToPTorsion (R := R) (K := K) p x))
    (hA :
      LinearMap.range
        (CharacterProjection.characterProjection (p := p) i
          (mulActionToAdditiveLinearAction (p := p) ρA)) ≠ ⊥) :
    ∃ s : SingularKummer.SingularPair R K p,
      Additive.ofMul
          (QuotientGroup.mk s :
            SingularKummer.SingularPair.SingularGroup (R := R) (K := K) p) ∈
        LinearMap.range
          (CharacterProjection.characterProjection (p := p) i
            (mulActionToAdditiveLinearAction (p := p) ρS)) ∧
      SingularKummer.SingularPair.classMapToPTorsion (R := R) (K := K) p s ≠ 1 ∧
      toPrincipalIdeal R K (SingularKummer.SingularPair.generator s) =
        SingularKummer.SingularPair.ideal s ^ p ∧
      ∀ b : CharacterProjection.Delta p,
        Additive.ofMul
            (ρS b
              (QuotientGroup.mk s :
                SingularKummer.SingularPair.SingularGroup (R := R) (K := K) p)) =
          ((b : ZMod p) ^ i) •
            Additive.ofMul
              (QuotientGroup.mk s :
                SingularKummer.SingularPair.SingularGroup (R := R) (K := K) p) := by
  obtain ⟨s, hs_component, hs_nontrivial, hs_principal⟩ :=
    exists_representative_in_characterProjection_of_target_ne_bot
      (R := R) (K := K) p i ρS ρA hρ hA
  refine ⟨s, hs_component, hs_nontrivial, hs_principal, ?_⟩
  intro b
  exact
    singularGroup_additive_apply_eq_smul_of_mem_characterProjection_range
      (R := R) (K := K) p i ρS b hs_component


-- @@ L156-156 verbatim
end SingularPair

-- @@ L157-157 verbatim
end SingularLinearAction


-- @@ L159-159 verbatim
end SingularKummer

-- @@ L160-160 verbatim
end Reflection

-- @@ L161-161 verbatim
end BernoulliRegular


-- @@ L163-163 verbatim
end


-- @@ L165-165 verbatim
end
