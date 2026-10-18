import OAI.AlgebraicGeometry.StableCoordinate.ZeroFiber


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-11 verbatim
/-!
# Specializing the five-variable presentation at p = 0

This module proves, by explicit algebra maps, that specializing the hypersurface
presentation before or after imposing its defining equation gives the same
coordinate algebra.  No field, reducedness, or geometric assumptions are used.
-/


-- @@ L13-13 verbatim
noncomputable section

-- @@ L14-14 verbatim
namespace StableCoordinate.ZeroFiber

-- @@ L15-15 verbatim
open MvPolynomial


-- @@ L17-17 verbatim
variable (K : Type*) [CommRing K]


-- @@ L19-19 verbatim
abbrev Five := MvPolynomial (Fin 5) K


-- @@ L21-21 verbatim
def sourceX : Five K := X 1 ^ 2 - X 2 ^ 2 + X 0 * X 3


-- @@ L23-24 verbatim
def sourceH : Five K :=
  sourceX K ^ 2 * X 3 - (1 + 2 * X 1 * sourceX K) * X 4 - X 0 * X 4 ^ 2 - X 2


-- @@ L26-26 verbatim
def sourceIdeal : Ideal (Five K) := Ideal.span {sourceH K}

-- @@ L27-27 verbatim
abbrev Hypersurface := Five K ⧸ sourceIdeal K


-- @@ L29-29 verbatim
def hypersurfaceMk : Five K →ₐ[K] Hypersurface K := Ideal.Quotient.mkₐ K _


-- @@ L31-31 verbatim
def parameterIdeal : Ideal (Hypersurface K) := Ideal.span {hypersurfaceMk K (X 0)}

-- @@ L32-32 verbatim
abbrev SourceRing := Hypersurface K ⧸ parameterIdeal K


-- @@ L34-35 verbatim
def sourceMk : Five K →ₐ[K] SourceRing K :=
  (Ideal.Quotient.mkₐ K (parameterIdeal K)).comp (hypersurfaceMk K)


-- @@ L37-39 verbatim
lemma sourceMk_parameter : sourceMk K (X 0) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (Set.mem_singleton _)


-- @@ L41-46 verbatim
lemma sourceMk_relation : sourceMk K (sourceH K) = 0 := by
  have h : hypersurfaceMk K (sourceH K) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (Set.mem_singleton _)
  change Ideal.Quotient.mkₐ K (parameterIdeal K) (hypersurfaceMk K (sourceH K)) = 0
  rw [h, map_zero]


-- @@ L48-49 verbatim
def specialize : Five K →ₐ[K] Ring K :=
  aeval ![0, qmk K (X 0), qmk K (X 1), qmk K (X 2), qmk K (X 3)]


-- @@ L51-53 verbatim
lemma specialize_relation : specialize K (sourceH K) = 0 := by
  have h := qmk_relation K
  simpa [specialize, sourceH, sourceX, relation, squareDifference, map_ofNat] using h


-- @@ L55-62 verbatim
lemma specialize_vanishes : ∀ a ∈ sourceIdeal K, specialize K a = 0 := by
  intro a ha
  have h : sourceIdeal K ≤ RingHom.ker (specialize K).toRingHom := by
    rw [sourceIdeal, Ideal.span_le]
    intro b hb
    rcases Set.mem_singleton_iff.mp hb with rfl
    exact specialize_relation K
  exact h ha


-- @@ L64-65 verbatim
def specializeHypersurface : Hypersurface K →ₐ[K] Ring K :=
  Ideal.Quotient.liftₐ _ (specialize K) (specialize_vanishes K)


-- @@ L67-68 verbatim
@[simp] lemma specializeHypersurface_mk (a : Five K) :
    specializeHypersurface K (hypersurfaceMk K a) = specialize K a := rfl


-- @@ L70-78 verbatim
lemma specializeHypersurface_vanishes :
    ∀ a ∈ parameterIdeal K, specializeHypersurface K a = 0 := by
  intro a ha
  have h : parameterIdeal K ≤ RingHom.ker (specializeHypersurface K).toRingHom := by
    rw [parameterIdeal, Ideal.span_le]
    intro b hb
    rcases Set.mem_singleton_iff.mp hb with rfl
    simp [specialize]
  exact h ha


-- @@ L80-81 verbatim
def specializeQuotient : SourceRing K →ₐ[K] Ring K :=
  Ideal.Quotient.liftₐ _ (specializeHypersurface K) (specializeHypersurface_vanishes K)


-- @@ L83-84 verbatim
@[simp] lemma specializeQuotient_mk (a : Five K) :
    specializeQuotient K (sourceMk K a) = specialize K a := rfl


-- @@ L86-87 verbatim
def includeVariables : Four K →ₐ[K] SourceRing K :=
  aeval ![sourceMk K (X 1), sourceMk K (X 2), sourceMk K (X 3), sourceMk K (X 4)]


-- @@ L89-96 verbatim
lemma includeVariables_relation : includeVariables K (relation K) = 0 := by
  have h := sourceMk_relation K
  simp only [sourceH, sourceX, map_sub, map_add, map_mul, map_pow, map_ofNat,
    map_one] at h
  rw [sourceMk_parameter] at h
  simp only [includeVariables, relation, squareDifference, map_sub, map_add, map_mul,
    map_pow, map_ofNat, map_one, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  linear_combination h


-- @@ L98-105 verbatim
lemma includeVariables_vanishes : ∀ a ∈ relationIdeal K, includeVariables K a = 0 := by
  intro a ha
  have h : relationIdeal K ≤ RingHom.ker (includeVariables K).toRingHom := by
    rw [relationIdeal, Ideal.span_le]
    intro b hb
    rcases Set.mem_singleton_iff.mp hb with rfl
    exact includeVariables_relation K
  exact h ha


-- @@ L107-108 verbatim
def includeQuotient : Ring K →ₐ[K] SourceRing K :=
  Ideal.Quotient.liftₐ _ (includeVariables K) (includeVariables_vanishes K)


-- @@ L110-111 verbatim
@[simp] lemma includeQuotient_mk (a : Four K) :
    includeQuotient K (qmk K a) = includeVariables K a := rfl


-- @@ L113-119 verbatim
lemma specialize_include :
    (specializeQuotient K).comp (includeQuotient K) = AlgHom.id K (Ring K) := by
  apply Ideal.Quotient.algHom_ext
  ext i : 1
  change specializeQuotient K (includeQuotient K (qmk K (X i))) = qmk K (X i)
  rw [includeQuotient_mk]
  fin_cases i <;> simp [includeVariables, specialize]


-- @@ L121-128 verbatim
lemma include_specialize :
    (includeQuotient K).comp (specializeQuotient K) = AlgHom.id K (SourceRing K) := by
  apply Ideal.Quotient.algHom_ext
  apply Ideal.Quotient.algHom_ext
  ext i : 1
  change includeQuotient K (specializeQuotient K (sourceMk K (X i))) = sourceMk K (X i)
  rw [specializeQuotient_mk]
  fin_cases i <;> simp [specialize, includeVariables, sourceMk_parameter]


-- @@ L130-133 verbatim
/-- Specialize `p` to zero in the hypersurface presentation. -/
def specializationEquiv : SourceRing K ≃ₐ[K] Ring K :=
  AlgEquiv.ofAlgHom (specializeQuotient K) (includeQuotient K)
    (specialize_include K) (include_specialize K)


-- @@ L135-138 verbatim
/-- The zero fiber of the five-variable hypersurface presentation is a
three-variable polynomial algebra. -/
def sourceZeroFiberEquiv : SourceRing K ≃ₐ[K] Three K :=
  (specializationEquiv K).trans (presentationEquiv K)


-- @@ L140-140 verbatim
end StableCoordinate.ZeroFiber


-- @@ L142-142 verbatim
end


-- @@ L144-144 verbatim
end OAI
