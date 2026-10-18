import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.Algebra.MvPolynomial.Basic


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-14 verbatim
/-!
# Enlarging the coefficient ring of a derivation

For the two polynomial charts in Section 5, a derivation annihilating the
coefficient ring can be regarded as linear over that ring.  The second lemma
shows that annihilation of the original coefficient algebra implies
annihilation of its localization, so this upgrade introduces no new condition.
-/


-- @@ L16-16 verbatim
namespace StableCoordinate

-- @@ L17-17 verbatim
namespace DerivationScalarUpgrade


-- @@ L19-20 verbatim
variable {k A S : Type*} [CommRing k] [CommRing A] [CommRing S]
  [Algebra k A] [Algebra S A]


-- @@ L22-30 verbatim
/-- View a derivation as linear over any coefficient algebra that it kills. -/
def upgrade (D : Derivation k A A) (hS : ∀ s : S, D (algebraMap S A s) = 0) :
    Derivation S A A where
  toFun := D
  map_add' := D.map_add
  map_smul' s a := by
    simp [Algebra.smul_def, hS]
  map_one_eq_zero' := D.map_one_eq_zero
  leibniz' := D.leibniz


-- @@ L32-34 verbatim
@[simp] theorem upgrade_apply (D : Derivation k A A)
    (hS : ∀ s : S, D (algebraMap S A s) = 0) (a : A) :
    upgrade D hS a = D a := rfl


-- @@ L36-39 verbatim
/-- Changing coefficient rings does not change the iterated function. -/
theorem upgrade_iterate (D : Derivation k A A)
    (hS : ∀ s : S, D (algebraMap S A s) = 0) (n : ℕ) (a : A) :
    (upgrade D hS : A → A)^[n] a = (D : A → A)^[n] a := rfl


-- @@ L41-45 verbatim
/-- Local nilpotence survives the coefficient-ring upgrade. -/
theorem upgrade_locallyNilpotent (D : Derivation k A A)
    (hS : ∀ s : S, D (algebraMap S A s) = 0)
    (hD : ∀ a : A, ∃ n : ℕ, (D : A → A)^[n] a = 0) :
    ∀ a : A, ∃ n : ℕ, (upgrade D hS : A → A)^[n] a = 0 := hD


-- @@ L47-54 verbatim
/-- A nonzero derivation remains nonzero after upgrading its coefficient ring. -/
theorem upgrade_ne_zero (D : Derivation k A A)
    (hS : ∀ s : S, D (algebraMap S A s) = 0) (hD : D ≠ 0) :
    upgrade D hS ≠ 0 := by
  intro h
  apply hD
  ext a
  exact congrArg (fun (E : Derivation S A A) => E a) h


-- @@ L56-68 verbatim
/-- It suffices to check invariance of the images of polynomial generators. -/
theorem annihilates_mvPolynomial {σ : Type*} (D : Derivation k A A)
    (φ : MvPolynomial σ k →ₐ[k] A)
    (hX : ∀ j : σ, D (φ (MvPolynomial.X j)) = 0) :
    ∀ p : MvPolynomial σ k, D (φ p) = 0 := by
  intro p
  induction p using MvPolynomial.induction_on with
  | C r =>
    rw [show MvPolynomial.C r = algebraMap k (MvPolynomial σ k) r from rfl,
      AlgHom.commutes, D.map_algebraMap]
  | add p q hp hq => simp only [map_add, hp, hq, add_zero]
  | mul_X p j hp =>
    simp only [map_mul, Derivation.leibniz, hX, hp, smul_zero, add_zero]


-- @@ L70-70 verbatim
section Localization


-- @@ L72-72 verbatim
variable {R L : Type*} [CommRing R] [CommRing L] [Algebra R L]

-- @@ L73-73 verbatim
variable (M : Submonoid R) [IsLocalization M L]


-- @@ L75-75 verbatim
include M


-- @@ L77-87 verbatim
/-- If a derivation kills the image of the original coefficient algebra,
it also kills the image of its entire localization. -/
theorem annihilates_localization (D : Derivation k A A) (φ : L →+* A)
    (hR : ∀ r : R, D (φ (algebraMap R L r)) = 0) :
    ∀ l : L, D (φ l) = 0 := by
  intro l
  obtain ⟨⟨r, m⟩, hm⟩ := IsLocalization.surj M l
  have hd := congrArg D (congrArg φ hm)
  simp only [map_mul, Derivation.leibniz, hR, smul_eq_mul,
    mul_zero, zero_add] at hd
  exact ((IsLocalization.map_units L m).map φ).mul_right_eq_zero.mp hd


-- @@ L89-89 verbatim
end Localization


-- @@ L91-91 verbatim
end DerivationScalarUpgrade

-- @@ L92-92 verbatim
end StableCoordinate


-- @@ L94-94 verbatim
end OAI
