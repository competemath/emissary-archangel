import OAI.Algebra.AffineCancellation.OrbitRigidity


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
namespace ComplexCancellation.LND

-- @@ L8-8 verbatim
open Polynomial

-- @@ L9-9 verbatim
variable {k R : Type*} [Field k] [CharZero k] [CommRing R] [Algebra k R]


-- @@ L11-15 verbatim
lemma inv_factorial_succ (n : ℕ) :
    ((n + 1 : ℕ) : k) * ((n + 1).factorial : k)⁻¹ = (n.factorial : k)⁻¹ := by
  rw [Nat.factorial_succ, Nat.cast_mul, mul_inv_rev]
  have hn : ((n + 1 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp


-- @@ L17-23 verbatim
lemma derivative_orbit (D : Derivation k R R) (hD : LocallyNilpotent D) (r : R) :
    (orbit D hD r).derivative = orbit D hD (D r) := by
  ext n
  rw [Polynomial.coeff_derivative, orbit_coeff, orbit_coeff,
    ← Function.iterate_succ_apply]
  rw [mul_comm, ← Nat.cast_succ, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul k, smul_smul,
    inv_factorial_succ]


-- @@ L25-48 verbatim
lemma kernel_factorially_closed [IsDomain R] (D : Derivation k R R)
    (hD : LocallyNilpotent D) {r s : R} (hr : r ≠ 0) (hs : s ≠ 0)
    (hrs : D (r * s) = 0) : D r = 0 ∧ D s = 0 := by
  have hor : orbit D hD r ≠ 0 := by
    intro h
    have := congrArg (fun p : R[X] => p.coeff 0) h
    simp at this
    exact hr this
  have hos : orbit D hD s ≠ 0 := by
    intro h
    have := congrArg (fun p : R[X] => p.coeff 0) h
    simp at this
    exact hs this
  have hp := (orbit_constant_iff D hD (r*s)).mpr hrs
  rw [orbit_mul] at hp
  have hn := congrArg Polynomial.natDegree hp
  rw [natDegree_mul hor hos, natDegree_C] at hn
  have hnr : (orbit D hD r).natDegree = 0 := by omega
  have hns : (orbit D hD s).natDegree = 0 := by omega
  constructor
  · apply (orbit_constant_iff D hD r).mp
    simpa using eq_C_of_natDegree_eq_zero hnr
  · apply (orbit_constant_iff D hD s).mp
    simpa using eq_C_of_natDegree_eq_zero hns


-- @@ L50-50 verbatim
end ComplexCancellation.LND

-- @@ L51-51 verbatim
namespace ComplexCancellation.LND

-- @@ L52-52 verbatim
open Polynomial

-- @@ L53-53 verbatim
variable {k R : Type*} [Field k] [CharZero k] [CommRing R] [Algebra k R] [IsDomain R]


-- @@ L55-66 verbatim
lemma fixed_of_dvd (D : Derivation k R R) (hD : LocallyNilpotent D)
    {r : R} (hr : r ∣ D r) : D r = 0 := by
  obtain ⟨s, hs⟩ := hr
  have hdvd : orbit D hD r ∣ (orbit D hD r).derivative := by
    rw [derivative_orbit, hs, orbit_mul]
    exact dvd_mul_right _ _
  have hz := Polynomial.dvd_derivative_iff.mp hdvd
  rw [derivative_orbit] at hz
  apply orbit_injective D hD
  change orbitHom D hD (D r) = orbitHom D hD 0
  rw [map_zero]
  exact hz


-- @@ L68-81 verbatim
lemma polynomial_dX_constant (D : Derivation k k[X] k[X]) (hD : LocallyNilpotent D) :
    D X = C ((D X).coeff 0) := by
  have hformula (f : k[X]) : D f = f.derivative * D X := by
    have he : Polynomial.mkDerivation k (D X) = D := by ext; simp
    calc D f = Polynomial.mkDerivation k (D X) f := congrArg (fun E : Derivation k k[X] k[X] => E f) he.symm
      _ = _ := by simp [Polynomial.mkDerivation_apply, smul_eq_mul]
  have hzero : D (D X) = 0 := fixed_of_dvd D hD (by
    rw [hformula (D X)]; exact dvd_mul_left _ _)
  by_cases hx : D X = 0
  · simp [hx]
  · have hp : (D X).derivative = 0 := by
      rw [hformula, mul_eq_zero] at hzero
      exact hzero.resolve_right hx
    exact Polynomial.eq_C_of_natDegree_eq_zero (Polynomial.derivative_eq_zero.mp hp)


-- @@ L83-83 verbatim
end ComplexCancellation.LND


-- @@ L85-85 verbatim
namespace ComplexCancellation.LND

-- @@ L86-86 verbatim
variable {k R : Type*} [Field k] [CommRing R] [Algebra k R]


-- @@ L88-95 verbatim
lemma nilpotent_add (D : Derivation k R R) {r s : R}
    (hr : ∃ n, (D : R → R)^[n] r = 0) (hs : ∃ n, (D : R → R)^[n] s = 0) :
    ∃ n, (D : R → R)^[n] (r+s) = 0 := by
  obtain ⟨n, hn⟩ := hr
  obtain ⟨m, hm⟩ := hs
  refine ⟨n+m, ?_⟩
  rw [iterate_add, iterate_eq_zero_of_le D hn (Nat.le_add_right _ _),
    iterate_eq_zero_of_le D hm (Nat.le_add_left _ _), add_zero]


-- @@ L97-109 verbatim
lemma nilpotent_mul (D : Derivation k R R) {r s : R}
    (hr : ∃ n, (D : R → R)^[n] r = 0) (hs : ∃ n, (D : R → R)^[n] s = 0) :
    ∃ n, (D : R → R)^[n] (r*s) = 0 := by
  obtain ⟨n, hn⟩ := hr
  obtain ⟨m, hm⟩ := hs
  refine ⟨n+m, ?_⟩
  rw [iterate_leibniz]
  apply Finset.sum_eq_zero
  rintro ⟨i,j⟩ hij
  have hij' : i+j = n+m := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  by_cases hi : n ≤ i
  · rw [iterate_eq_zero_of_le D hn hi, zero_mul, nsmul_zero]
  · rw [iterate_eq_zero_of_le D hm (by omega : m ≤ j), mul_zero, nsmul_zero]


-- @@ L111-119 verbatim
lemma mvPolynomial_locallyNilpotent {σ : Type*}
    (D : Derivation k (MvPolynomial σ k) (MvPolynomial σ k))
    (hX : ∀ i, ∃ n : ℕ, (D : _ → _)^[n] (MvPolynomial.X i) = 0) :
    LocallyNilpotent D := by
  intro r
  induction r using MvPolynomial.induction_on with
  | C c => exact ⟨1, by simp⟩
  | add r s hr hs => exact nilpotent_add D hr hs
  | mul_X r i hr => exact nilpotent_mul D hr (hX i)


-- @@ L121-121 verbatim
end ComplexCancellation.LND


-- @@ L123-123 verbatim
end


-- @@ L125-125 verbatim
end OAI
