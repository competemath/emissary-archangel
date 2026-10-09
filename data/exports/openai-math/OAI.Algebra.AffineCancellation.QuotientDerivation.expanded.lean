import OAI.Algebra.AffineCancellation.Model


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
namespace ComplexCancellation.QuotientDerivation

-- @@ L8-8 verbatim
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]

-- @@ L9-10 verbatim
variable (I : Ideal R) (D : Derivation k R R)
  (hD : ∀ r ∈ I, D r ∈ I)


-- @@ L12-14 verbatim
def linear : (R ⧸ I) →ₗ[k] (R ⧸ I) :=
  (I.restrictScalars k).liftQ ((Ideal.Quotient.mkₐ k I).toLinearMap.comp D.toLinearMap)
    (by intro r hr; exact Ideal.Quotient.eq_zero_iff_mem.mpr (hD r hr))


-- @@ L16-17 verbatim
@[simp] lemma linear_mk (r : R) : linear I D hD (Ideal.Quotient.mk I r) =
    Ideal.Quotient.mk I (D r) := rfl


-- @@ L19-25 verbatim
def derivation : Derivation k (R ⧸ I) (R ⧸ I) := Derivation.mk' (linear I D hD) (by
  intro r s
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
  change linear I D hD ((Ideal.Quotient.mk I) r * (Ideal.Quotient.mk I) s) = _
  rw [← map_mul, linear_mk]
  simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, linear_mk])


-- @@ L27-28 verbatim
@[simp] lemma derivation_mk (r : R) : derivation I D hD (Ideal.Quotient.mk I r) =
    Ideal.Quotient.mk I (D r) := rfl


-- @@ L30-36 verbatim
lemma iterate_mk (r : R) (n : ℕ) :
    (derivation I D hD : (R ⧸ I) → (R ⧸ I))^[n] (Ideal.Quotient.mk I r) =
      Ideal.Quotient.mk I ((D : R → R)^[n] r) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, derivation_mk,
      Function.iterate_succ_apply']


-- @@ L38-43 verbatim
lemma locallyNilpotent (hn : ∀ r, ∃ n, (D : R → R)^[n] r = 0) :
    ∀ r, ∃ n, (derivation I D hD : (R ⧸ I) → (R ⧸ I))^[n] r = 0 := by
  intro r
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨n, hn⟩ := hn r
  exact ⟨n, by rw [iterate_mk, hn, map_zero]⟩


-- @@ L45-51 verbatim
lemma span_singleton_stable {h : R} (hh : D h ∈ Ideal.span {h}) :
    ∀ r ∈ Ideal.span {h}, D r ∈ Ideal.span {h} := by
  intro r hr
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton.mp hr
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
    (Ideal.mul_mem_left _ _ hh)


-- @@ L53-53 verbatim
end ComplexCancellation.QuotientDerivation


-- @@ L55-55 verbatim
end


-- @@ L57-57 verbatim
end OAI
