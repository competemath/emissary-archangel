import OAI.AlgebraicGeometry.CommutingDerivations.DerivationOperations
import Mathlib.LinearAlgebra.LinearIndependent.Defs


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-8 verbatim
/-! Properties of an actual descended family with a common clearing power.
All hypotheses describe explicit maps and identities; none assumes the desired
family properties on the original ring. -/

-- @@ L9-9 verbatim
noncomputable section

-- @@ L10-10 verbatim
namespace AbhyankarSathaye.CommutingDerivations


-- @@ L12-13 verbatim
variable {K A L I : Type*} [CommRing K] [CommRing A] [CommRing L]
  [Algebra K A] [Algebra K L]


-- @@ L15-20 verbatim
theorem descended_fixes_parameter (ι : A →ₐ[K] L) (hinj : Function.Injective ι)
    (c : A) (N : ℕ) (D : Derivation K L L) (d : Derivation K A A)
    (hdesc : ∀ a, ι (d a) = (ι c)^N * D (ι a)) (hfix : D (ι c) = 0) :
    d c = 0 := by
  apply hinj
  simpa [hfix] using hdesc c


-- @@ L22-34 verbatim
theorem descended_kernel (ι : A →ₐ[K] L) (hinj : Function.Injective ι)
    (c : A) (hu : IsUnit (ι c)) (N : ℕ)
    (D : Derivation K L L) (d : Derivation K A A)
    (hdesc : ∀ a, ι (d a) = (ι c)^N * D (ι a)) (a : A) :
    d a = 0 ↔ D (ι a) = 0 := by
  constructor
  · intro hz
    have he := hdesc a
    rw [hz, map_zero] at he
    exact (hu.pow N).mul_right_eq_zero.mp he.symm
  · intro hz
    apply hinj
    simpa [hz] using hdesc a


-- @@ L36-43 verbatim
theorem descended_locallyNilpotent (ι : A →ₐ[K] L) (hinj : Function.Injective ι)
    (c : A) (N : ℕ) (D : Derivation K L L) (d : Derivation K A A)
    (hdesc : ∀ a, ι (d a) = (ι c)^N * D (ι a))
    (hfix : D (ι c) = 0) (hD : LocallyNilpotent D) : LocallyNilpotent d := by
  have hp : D ((ι c)^N) = 0 := by simp [Derivation.leibniz_pow, hfix]
  exact descendDerivation_locallyNilpotent ι hinj ((ι c)^N • D) d
    (by simpa only [Derivation.smul_apply, smul_eq_mul] using hdesc)
    (scaleDerivation_locallyNilpotent D ((ι c)^N) hp hD)


-- @@ L45-56 verbatim
theorem descended_commute (ι : A →ₐ[K] L) (hinj : Function.Injective ι)
    (c : A) (N : ℕ) (D E : Derivation K L L) (d e : Derivation K A A)
    (hd : ∀ a, ι (d a) = (ι c)^N * D (ι a))
    (he : ∀ a, ι (e a) = (ι c)^N * E (ι a))
    (hD : D (ι c) = 0) (hE : E (ι c) = 0)
    (hDE : ∀ a, D (E a) = E (D a)) (a : A) : d (e a) = e (d a) := by
  have hDp : D ((ι c)^N) = 0 := by simp [Derivation.leibniz_pow, hD]
  have hEp : E ((ι c)^N) = 0 := by simp [Derivation.leibniz_pow, hE]
  exact descendDerivation_commute ι hinj ((ι c)^N • D) ((ι c)^N • E) d e
    (by simpa only [Derivation.smul_apply, smul_eq_mul] using hd)
    (by simpa only [Derivation.smul_apply, smul_eq_mul] using he)
    (scaleDerivation_commute D E ((ι c)^N) ((ι c)^N) hDp hEp hDE) a


-- @@ L58-91 verbatim
/-- Localized coordinate slices prove independence over the original ring.
Each slice is required to have an actual denominator-clearing witness. This is
provided by the defining surjectivity of localization, with no assumption that
the slices already lie in A. -/
theorem descended_linearIndependent [Fintype I] [DecidableEq I]
    (ι : A →ₐ[K] L) (hinj : Function.Injective ι) (c : A)
    (hu : IsUnit (ι c)) (N : ℕ)
    (D : I → Derivation K L L) (d : I → Derivation K A A)
    (hdesc : ∀ i a, ι (d i a) = (ι c)^N * D i (ι a))
    (hfix : ∀ i, D i (ι c) = 0)
    (t : I → L) (ht : ∀ i j, D i (t j) = if i = j then 1 else 0)
    (hfrac : ∀ j, ∃ (n : ℕ) (r : A), t j * (ι c)^n = ι r) :
    LinearIndependent A d := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha j
  obtain ⟨n, r, hr⟩ := hfrac j
  have hir (i : I) : D i (ι r) = (ι c)^n * (if i = j then 1 else 0) := by
    rw [← hr, Derivation.leibniz]
    simp [Derivation.leibniz_pow, hfix, ht, smul_eq_mul]
  let ev : Derivation K A A →+ A :=
    { toFun := fun E => E r
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have he : ∑ i, a i * d i r = 0 := by
    have he' := congrArg ev ha
    rw [map_sum, map_zero] at he'
    simpa [ev, Derivation.smul_apply, smul_eq_mul] using he'
  have hj : (ι (a j) * (ι c)^N) * (ι c)^n = 0 := by
    have he' := congrArg ι he
    simpa [map_sum, hdesc, hir, mul_ite, ite_mul, mul_assoc] using he'
  apply hinj
  rw [map_zero]
  exact (hu.pow N).mul_left_eq_zero.mp ((hu.pow n).mul_left_eq_zero.mp hj)


-- @@ L93-93 verbatim
end AbhyankarSathaye.CommutingDerivations


-- @@ L95-95 verbatim
end


-- @@ L97-97 verbatim
end OAI
