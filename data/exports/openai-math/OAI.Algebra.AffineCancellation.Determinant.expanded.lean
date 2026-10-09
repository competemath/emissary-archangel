import OAI.Algebra.AffineCancellation.Model


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
namespace ComplexCancellation.Determinant

-- @@ L8-8 verbatim
open MvPolynomial


-- @@ L10-24 verbatim
lemma regular_quotient_of_prime {R : Type*} [CommRing R] [IsDomain R]
    {p h : R} (hp : Prime p) (hph : ¬p ∣ h) :
    IsLeftRegular (Ideal.Quotient.mk (Ideal.span {h}) p) := by
  apply isLeftRegular_iff_right_eq_zero_of_mul.mpr
  intro q hq
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hq
  obtain ⟨c, hc⟩ := hq
  have hpc : p ∣ c := (hp.dvd_or_dvd (show p ∣ h * c by rw [← hc]; exact dvd_mul_right _ _)).resolve_left hph
  obtain ⟨d, rfl⟩ := hpc
  have hr : r = h * d := by
    apply mul_left_cancel₀ hp.ne_zero
    linear_combination hc
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, hr]
  exact dvd_mul_right _ _


-- @@ L26-26 verbatim
abbrev Poly := MvPolynomial (Fin 5) ℂ

-- @@ L27-27 verbatim
abbrev Base := MvPolynomial (Fin 4) ℂ

-- @@ L28-28 verbatim
abbrev Coeff := MvPolynomial (Fin 3) ℂ

-- @@ L29-29 verbatim
abbrev K₀ := FractionRing Coeff

-- @@ L30-30 verbatim
abbrev K := RatFunc K₀


-- @@ L32-32 verbatim
def relation : Poly := X 0 * X 3 - X 2 * X 1 - 1

-- @@ L33-33 verbatim
abbrev T := Poly ⧸ Ideal.span {relation}

-- @@ L34-34 verbatim
def π : Poly →ₐ[ℂ] T := Ideal.Quotient.mkₐ ℂ _

-- @@ L35-35 verbatim
def a : T := π (X 0)

-- @@ L36-36 verbatim
def d : T := π (X 1)

-- @@ L37-37 verbatim
def b : T := π (X 2)

-- @@ L38-38 verbatim
def c : T := π (X 3)

-- @@ L39-39 verbatim
def u : T := π (X 4)

-- @@ L40-40 verbatim
def v : T := a ^ 3 * b - a ^ 2 * u ^ 3 - d ^ 2


-- @@ L42-45 verbatim
def baseEmbedding : Base →ₐ[ℂ] K :=
  (IsScalarTower.toAlgHom ℂ (Polynomial K₀) K).comp
    ((Polynomial.mapAlgHom (IsScalarTower.toAlgHom ℂ Coeff K₀)).comp
      (finSuccEquiv ℂ 3).toAlgHom)


-- @@ L47-50 verbatim
lemma baseEmbedding_injective : Function.Injective baseEmbedding :=
  (RatFunc.algebraMap_injective K₀).comp
    ((Polynomial.map_injective _ (IsFractionRing.injective Coeff K₀)).comp
      (finSuccEquiv ℂ 3).injective)


-- @@ L52-55 verbatim
lemma baseEmbedding_X_zero : baseEmbedding (X 0) = RatFunc.X := by
  change algebraMap (Polynomial K₀) K
    (Polynomial.map (algebraMap Coeff K₀) ((finSuccEquiv ℂ 3) (X 0))) = _
  rw [finSuccEquiv_X_zero, Polynomial.map_X, RatFunc.algebraMap_X]


-- @@ L57-61 verbatim
lemma baseEmbedding_X_succ (i : Fin 3) :
    baseEmbedding (X i.succ) = RatFunc.C (algebraMap Coeff K₀ (X i)) := by
  change algebraMap (Polynomial K₀) K
    (Polynomial.map (algebraMap Coeff K₀) ((finSuccEquiv ℂ 3) (X i.succ))) = _
  rw [finSuccEquiv_X_succ, Polynomial.map_C, RatFunc.algebraMap_C]


-- @@ L63-65 verbatim
def targetValues : Fin 5 → K := ![baseEmbedding (X 1), baseEmbedding (X 2),
  baseEmbedding (X 3), (1 + baseEmbedding (X 3) * baseEmbedding (X 2)) /
    baseEmbedding (X 1), baseEmbedding (X 0)]


-- @@ L67-67 verbatim
def eval : Poly →ₐ[ℂ] K := aeval targetValues


-- @@ L69-72 verbatim
lemma a_field_nonzero : baseEmbedding (X 1) ≠ 0 := by
  intro h
  have hz := baseEmbedding_injective (h.trans (map_zero _).symm)
  exact X_ne_zero (1 : Fin 4) hz


-- @@ L74-79 verbatim
lemma eval_relation : eval relation = 0 := by
  simp only [eval, relation, map_sub, map_mul, map_one, aeval_X]
  simp only [targetValues, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  field_simp [a_field_nonzero]
  ring


-- @@ L81-84 verbatim
def embedding : T →ₐ[ℂ] K := Ideal.Quotient.liftₐ _ eval (by
  intro r hr
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton.mp hr
  rw [map_mul, eval_relation, zero_mul])


-- @@ L86-87 verbatim
@[simp] lemma embedding_π (r : Poly) : embedding (π r) = eval r :=
  Ideal.Quotient.lift_mk _ _ _


-- @@ L89-91 verbatim
lemma determinant : a*c - b*d = 1 := by
  have h : π relation = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  simpa only [relation, map_sub, map_mul, map_one, a, b, c, d, sub_eq_zero] using h


-- @@ L93-97 verbatim
lemma a_regular : IsLeftRegular a := by
  apply regular_quotient_of_prime (MvPolynomial.X_prime (i := 0))
  intro h
  have he := map_dvd (MvPolynomial.eval (fun _ : Fin 5 => (0 : ℂ))) h
  simp [relation] at he


-- @@ L99-99 verbatim
def baseValues : Fin 4 → T := ![u,a,d,b]

-- @@ L100-100 verbatim
def baseMap : Base →ₐ[ℂ] T := aeval baseValues


-- @@ L102-107 verbatim
lemma embedding_baseMap (r : Base) : embedding (baseMap r) = baseEmbedding r := by
  have he : embedding.comp baseMap = baseEmbedding := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [baseMap, baseValues, u, a, d, b, embedding_π, eval, targetValues]
  exact DFunLike.congr_fun he r


-- @@ L109-112 verbatim
lemma baseMap_injective : Function.Injective baseMap := by
  intro r s hrs
  apply baseEmbedding_injective
  rw [← embedding_baseMap, ← embedding_baseMap, hrs]


-- @@ L114-124 verbatim
lemma clears_generator (i : Fin 5) :
    ∃ n : ℕ, ∃ f : Base, a^n * π (X i) = baseMap f := by
  fin_cases i
  · exact ⟨0, X 1, by simp [baseMap, baseValues, a]⟩
  · exact ⟨0, X 2, by simp [baseMap, baseValues, d]⟩
  · exact ⟨0, X 3, by simp [baseMap, baseValues, b]⟩
  · refine ⟨1, 1 + X 3 * X 2, ?_⟩
    simp only [pow_one, map_add, map_one, map_mul, baseMap, aeval_X]
    change a*c = 1+b*d
    linear_combination determinant
  · exact ⟨0, X 0, by simp [baseMap, baseValues, u]⟩


-- @@ L126-144 verbatim
lemma clears (r : T) : ∃ n : ℕ, ∃ f : Base, a^n * r = baseMap f := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ (Ideal.span {relation}) r
  change ∃ n : ℕ, ∃ f : Base, a^n * π r = baseMap f
  induction r using MvPolynomial.induction_on with
  | C z => refine ⟨0, C z, ?_⟩; simp [baseMap, π]
  | add r s hr hs =>
    obtain ⟨n, f, hf⟩ := hr
    obtain ⟨m, g, hg⟩ := hs
    refine ⟨n+m, X 1 ^ m * f + X 1 ^ n * g, ?_⟩
    simp only [map_add, map_mul, map_pow]
    have hb : baseMap (X 1) = a := by simp [baseMap, baseValues]
    rw [hb, ← hf, ← hg, pow_add]
    ring
  | mul_X r i hr =>
    obtain ⟨n, f, hf⟩ := hr
    obtain ⟨m, g, hg⟩ := clears_generator i
    refine ⟨n+m, f*g, ?_⟩
    rw [map_mul, map_mul, ← hf, ← hg, pow_add]
    ring


-- @@ L146-154 verbatim
lemma embedding_injective : Function.Injective embedding := by
  apply (injective_iff_map_eq_zero embedding).mpr
  intro r hr
  obtain ⟨n, f, hf⟩ := clears r
  have h : baseEmbedding f = 0 := by
    rw [← embedding_baseMap, ← hf, map_mul, hr, mul_zero]
  have hfzero : f = 0 := baseEmbedding_injective (h.trans (map_zero _).symm)
  rw [hfzero, map_zero] at hf
  exact isLeftRegular_iff_right_eq_zero_of_mul.mp (a_regular.pow n) r hf


-- @@ L156-156 verbatim
instance : IsDomain T := Function.Injective.isDomain embedding embedding_injective


-- @@ L158-158 verbatim
end ComplexCancellation.Determinant


-- @@ L160-160 verbatim
end


-- @@ L162-162 verbatim
end OAI
