import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Degrees


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-15 verbatim
/-!
# Derivations obtained from polynomial coordinate systems

The first step of §3 of the manuscript chooses a partial derivative in a
coordinate distinct from the distinguished coordinate and a positive-degree
invariant.  This file supplies the algebraic part of that choice: partial
derivatives of multivariate polynomials are locally nilpotent, and this
property, nonvanishing, and the values on coordinates transport through an
actual algebra equivalence.
-/


-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
namespace StableCoordinate.CoordinateDerivation


-- @@ L21-21 verbatim
open MvPolynomial


-- @@ L23-23 verbatim
section Partial


-- @@ L25-25 verbatim
variable {k σ : Type*} [CommSemiring k]


-- @@ L27-44 verbatim
/-- A coefficient vanishes once the number of differentiations exceeds the
available exponent in the chosen variable. -/
theorem coeff_iterate_pderiv_eq_zero (i : σ) (p : MvPolynomial σ k)
    (n : ℕ) (m : σ →₀ ℕ) (h : p.degreeOf i < m i + n) :
    (((pderiv i : Derivation k (MvPolynomial σ k)
      (MvPolynomial σ k)) : MvPolynomial σ k → MvPolynomial σ k)^[n] p).coeff m = 0 := by
  classical
  induction n generalizing m with
  | zero =>
      simp only [Nat.add_zero] at *
      by_contra hn
      exact (not_lt_of_ge (monomial_le_degreeOf i (mem_support_iff.mpr hn))) h
  | succ n ih =>
      rw [Function.iterate_succ_apply', coeff_pderiv]
      have hm : p.degreeOf i < (m + Finsupp.single i 1 : σ →₀ ℕ) i + n := by
        simpa only [Finsupp.add_apply, Finsupp.single_eq_same] using
          (show p.degreeOf i < m i + 1 + n by omega)
      rw [ih _ hm, zero_mul]


-- @@ L46-55 verbatim
/-- Multivariate partial derivatives are pointwise locally nilpotent, over an
arbitrary commutative coefficient semiring. -/
theorem pderiv_locallyNilpotent (i : σ) (p : MvPolynomial σ k) :
    ∃ n : ℕ, (((pderiv i : Derivation k (MvPolynomial σ k)
      (MvPolynomial σ k)) : MvPolynomial σ k → MvPolynomial σ k)^[n]) p = 0 := by
  refine ⟨p.degreeOf i + 1, ?_⟩
  ext m
  simp only [AddMonoidAlgebra.coeff_zero]
  apply coeff_iterate_pderiv_eq_zero
  omega


-- @@ L57-57 verbatim
end Partial


-- @@ L59-59 verbatim
section Transport


-- @@ L61-62 verbatim
variable {k A B : Type*} [CommSemiring k] [CommSemiring A] [CommSemiring B]
  [Algebra k A] [Algebra k B]


-- @@ L64-71 verbatim
/-- Transport of a derivation through an algebra equivalence. -/
def transport (e : A ≃ₐ[k] B) (D : Derivation k A A) : Derivation k B B where
  toLinearMap := e.toLinearMap.comp (D.toLinearMap.comp e.symm.toLinearMap)
  map_one_eq_zero' := by simp
  leibniz' a b := by
    simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_mul,
      Derivation.coeFn_coe, Derivation.leibniz, smul_eq_mul, map_add,
      AlgEquiv.apply_symm_apply]


-- @@ L73-74 verbatim
@[simp] theorem transport_apply (e : A ≃ₐ[k] B) (D : Derivation k A A) (b : B) :
    transport e D b = e (D (e.symm b)) := rfl


-- @@ L76-82 verbatim
/-- Iterating a transported derivation is conjugate to iterating the original
one.  In particular, no fixed bound on the nilpotence index is assumed. -/
theorem transport_iterate (e : A ≃ₐ[k] B) (D : Derivation k A A) (n : ℕ) (b : B) :
    ((transport e D : B → B)^[n]) b = e (((D : A → A)^[n]) (e.symm b)) := by
  induction n with
  | zero => simp
  | succ n ih => simp [Function.iterate_succ_apply', ih]


-- @@ L84-90 verbatim
/-- Pointwise local nilpotence is invariant under an algebra equivalence. -/
theorem transport_locallyNilpotent (e : A ≃ₐ[k] B) (D : Derivation k A A)
    (hD : ∀ a, ∃ n : ℕ, ((D : A → A)^[n]) a = 0) :
    ∀ b, ∃ n : ℕ, ((transport e D : B → B)^[n]) b = 0 := by
  intro b
  obtain ⟨n, hn⟩ := hD (e.symm b)
  exact ⟨n, by rw [transport_iterate, hn, map_zero]⟩


-- @@ L92-93 verbatim
@[simp] theorem transport_apply_image (e : A ≃ₐ[k] B) (D : Derivation k A A) (a : A) :
    transport e D (e a) = e (D a) := by simp


-- @@ L95-102 verbatim
/-- Transport does not turn a nonzero derivation into zero. -/
theorem transport_ne_zero (e : A ≃ₐ[k] B) (D : Derivation k A A) (hD : D ≠ 0) :
    transport e D ≠ 0 := by
  intro h
  apply hD
  ext a
  have ha := congrArg (fun E : Derivation k B B => E (e a)) h
  simpa using e.injective (by simpa using ha)


-- @@ L104-104 verbatim
end Transport


-- @@ L106-106 verbatim
section Coordinates


-- @@ L108-108 verbatim
variable {k σ A : Type*} [CommSemiring k] [CommSemiring A] [Algebra k A]


-- @@ L110-113 verbatim
/-- Partial differentiation in a specified member of a polynomial coordinate
system, expressed intrinsically on the target algebra. -/
def coordinatePartial (e : MvPolynomial σ k ≃ₐ[k] A) (i : σ) : Derivation k A A :=
  transport e (pderiv i)


-- @@ L115-117 verbatim
@[simp] theorem coordinatePartial_self (e : MvPolynomial σ k ≃ₐ[k] A) (i : σ) :
    coordinatePartial e i (e (X i)) = 1 := by
  simp [coordinatePartial]


-- @@ L119-121 verbatim
@[simp] theorem coordinatePartial_other (e : MvPolynomial σ k ≃ₐ[k] A)
    {i j : σ} (h : j ≠ i) : coordinatePartial e i (e (X j)) = 0 := by
  simp [coordinatePartial, pderiv_X_of_ne h]


-- @@ L123-125 verbatim
theorem coordinatePartial_locallyNilpotent (e : MvPolynomial σ k ≃ₐ[k] A) (i : σ) :
    ∀ a, ∃ n : ℕ, ((coordinatePartial e i : A → A)^[n]) a = 0 :=
  transport_locallyNilpotent e (pderiv i) (pderiv_locallyNilpotent i)


-- @@ L127-131 verbatim
theorem coordinatePartial_ne_zero [Nontrivial A]
    (e : MvPolynomial σ k ≃ₐ[k] A) (i : σ) : coordinatePartial e i ≠ 0 := by
  intro h
  have hi := congrArg (fun D : Derivation k A A => D (e (X i))) h
  simp at hi


-- @@ L133-142 verbatim
/-- In a polynomial coordinate system, any coordinate can be differentiated
while two distinct other coordinates remain invariant. -/
theorem exists_nonzero_locallyNilpotent_killing_two [Nontrivial A]
    (e : MvPolynomial σ k ≃ₐ[k] A) (i j l : σ) (hji : j ≠ i) (hli : l ≠ i) :
    ∃ D : Derivation k A A, D ≠ 0 ∧
      (∀ a, ∃ n : ℕ, ((D : A → A)^[n]) a = 0) ∧
      D (e (X j)) = 0 ∧ D (e (X l)) = 0 := by
  exact ⟨coordinatePartial e i, coordinatePartial_ne_zero e i,
    coordinatePartial_locallyNilpotent e i,
    coordinatePartial_other e hji, coordinatePartial_other e hli⟩


-- @@ L144-163 verbatim
/-- A proper subalgebra cannot contain every member of a polynomial coordinate
system.  For the manuscript this subalgebra is the degree-at-most-zero part of
the multiplicative integer filtration. -/
theorem exists_coordinate_not_mem (e : MvPolynomial σ k ≃ₐ[k] A)
    (S : Subalgebra k A) (hS : S ≠ ⊤) : ∃ j, e (X j) ∉ S := by
  classical
  by_contra h
  have hX : ∀ j, e (X j) ∈ S := by simpa only [not_exists, not_not] using h
  apply hS
  apply top_unique
  intro a ha
  clear ha
  obtain ⟨p, rfl⟩ := e.surjective a
  induction p using MvPolynomial.induction_on with
  | C r =>
      change e (algebraMap k (MvPolynomial σ k) r) ∈ S
      rw [e.commutes]
      exact S.algebraMap_mem r
  | add p q hp hq => simpa using S.add_mem hp hq
  | mul_X p j hp => simpa using S.mul_mem hp (hX j)


-- @@ L165-183 verbatim
/-- The exact algebraic choice at the start of the coordinate obstruction:
if the distinguished coordinate lies in a proper subalgebra of a polynomial
ring of dimension at least three, a nonzero locally nilpotent derivation
kills both that coordinate and a coordinate outside the subalgebra. -/
theorem exists_lnd_invariant_outside [Nontrivial A] {n : ℕ} (hn : 2 < n)
    (e : MvPolynomial (Fin n) k ≃ₐ[k] A) (S : Subalgebra k A)
    (hS : S ≠ ⊤) (i : Fin n) (hi : e (X i) ∈ S) :
    ∃ D : Derivation k A A, D ≠ 0 ∧
      (∀ a, ∃ r : ℕ, ((D : A → A)^[r]) a = 0) ∧
      D (e (X i)) = 0 ∧ ∃ j : Fin n, j ≠ i ∧ e (X j) ∉ S ∧ D (e (X j)) = 0 := by
  obtain ⟨j, hj⟩ := exists_coordinate_not_mem e S hS
  have hji : j ≠ i := by
    intro h
    apply hj
    simpa [h] using hi
  obtain ⟨l, hli, hlj⟩ := Fin.exists_ne_and_ne_of_two_lt i j hn
  refine ⟨coordinatePartial e l, coordinatePartial_ne_zero e l,
    coordinatePartial_locallyNilpotent e l, coordinatePartial_other e hli.symm,
    j, hji, hj, coordinatePartial_other e hlj.symm⟩


-- @@ L185-185 verbatim
end Coordinates


-- @@ L187-187 verbatim
end StableCoordinate.CoordinateDerivation


-- @@ L189-189 verbatim
end


-- @@ L191-191 verbatim
end OAI
