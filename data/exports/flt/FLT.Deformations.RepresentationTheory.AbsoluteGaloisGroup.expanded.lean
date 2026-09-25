/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Kevin Buzzard, Ruben Van de Velde
-/
module

public import FLT.Deformations.RepresentationTheory.Frobenius
public import FLT.Deformations.RepresentationTheory.IntegralClosure
public import FLT.Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

import FLT.NumberField.Completion.Finite
import Mathlib.FieldTheory.Galois.Infinite


-- @@ L18-25 verbatim
/-!
# Functoriality of the absolute Galois group

For a field extension `K → L`, the induced map between absolute Galois groups
`Γ L → Γ K` is `Field.absoluteGaloisGroup.map` in Mathlib; here we record how it
interacts with the chosen embedding of the algebraic closures, together with
finite-index results for fixing subgroups.
-/


-- @@ L27-27 verbatim
@[expose] public section


-- @@ L29-29 verbatim
variable {K L : Type*} [Field K] [Field L]

-- @@ L30-30 verbatim
variable {A B : Type*} [CommRing A] [TopologicalSpace A] [CommRing B] [TopologicalSpace B]

-- @@ L31-31 verbatim
variable {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

-- @@ L32-32 verbatim
variable {n : Type*} [Fintype n] [DecidableEq n]


-- @@ L34-34 verbatim
open NumberField


-- @@ L36-36 verbatim
variable [NumberField K]


-- @@ L38-38 verbatim
variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))


-- @@ L40-40 verbatim
local notation3 "Γ" K:max => Field.absoluteGaloisGroup K

-- @@ L41-41 verbatim
local notation3 K:max "ᵃˡᵍ" => AlgebraicClosure K

-- @@ L42-42 verbatim
local notation3 "𝔪" => IsLocalRing.maximalIdeal

-- @@ L43-43 verbatim
local notation3 "κ" => IsLocalRing.ResidueField

-- @@ L44-44 verbatim
local notation "Ω" K => IsDedekindDomain.HeightOneSpectrum (𝓞 K)

-- @@ L45-45 verbatim
local notation "Kᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletion K v

-- @@ L46-46 verbatim
local notation "𝒪ᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v


-- @@ L48-49 verbatim
set_option allowUnsafeReducibility true in
attribute [reducible] Field.absoluteGaloisGroup -- lol WTF is going on here


-- @@ L51-57 expanded
omit [NumberField K] in
set_option backward.isDefEq.respectTransparency false in
lemma Field.absoluteGaloisGroup.lift_map (f : K →+* L) (σ : Field.absoluteGaloisGroup L)
    (x : AlgebraicClosure K) : AlgebraicClosure.map f (map f σ x) = σ (AlgebraicClosure.map f x) :=
  by
  let := f.toAlgebra
  let := (AlgebraicClosure.map f).toAlgebra
  exact AlgEquiv.restrictNormal_commutes _ _ _


-- @@ L60-69 verbatim
attribute [local instance 100000]
  instAlgebraSubtypeMemValuationSubring_fLT IntermediateField.algebra'
  Algebra.toSMul Subalgebra.toCommRing Algebra.toModule
  Subalgebra.toRing Ring.toAddCommGroup AddCommGroup.toAddGroup
  ValuationSubring.smulCommClass IntermediateField.toAlgebra
  IntermediateField.smulCommClass_of_normal
  mulSemiringActionIntegralClosure
  Subalgebra.algebra
  CommRing.toCommSemiring
  Valued.toIsUniformAddGroup


-- @@ L71-91 verbatim
attribute [local instance] Valued.toNormedField in
lemma isIntegral_of_spectralNorm_le_one
    {K L Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Field K] [Field L]
    [Valued K Γ₀] [(Valued.v : Valuation K Γ₀).RankOne] [Algebra K L] [Algebra.IsAlgebraic K L]
    {x : L} (hx : spectralNorm K L x ≤ 1) : IsIntegral (Valued.v : Valuation K Γ₀).integer x := by
  have : minpoly K x ∈ Polynomial.lifts (Valued.v : Valuation K Γ₀).integer.subtype := by
    refine (Polynomial.lifts_iff_coeff_lifts _).mpr fun i ↦ ?_
    have := (ciSup_le_iff (spectralValueTerms_bddAbove ..)).mp hx i
    simp only [spectralValueTerms] at this
    split_ifs at this with h
    · conv_rhs at this => rw [← Real.one_rpow (1 / (↑(minpoly K x).natDegree - ↑i) : ℝ)]
      rw [Real.rpow_le_rpow_iff (by positivity) (by positivity) (by aesop)] at this
      simpa [Valuation.mem_integer_iff] using this
    obtain h | h := (le_of_not_gt h).eq_or_lt
    · simp [← h, minpoly.monic (Algebra.IsAlgebraic.isAlgebraic x).isIntegral, one_mem]
    · simp [Polynomial.coeff_eq_zero_of_natDegree_lt h, zero_mem]
  obtain ⟨P, hP, _, hP'⟩ := Polynomial.lifts_and_degree_eq_and_monic this
    (minpoly.monic (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
  refine ⟨P, hP', ?_⟩
  rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap K,
    Subring.algebraMap_def, hP, minpoly.aeval]


-- @@ L93-101 verbatim
lemma spectralNorm_inv
    {K L : Type*} [NontriviallyNormedField K] [Field L] [Algebra K L] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra.IsAlgebraic K L] (x : L) :
    spectralNorm K L (x⁻¹) = (spectralNorm K L x)⁻¹ := by
  by_cases H : x = 0
  · simp [H, spectralNorm_zero]
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← spectralAlgNorm_def, ← spectralAlgNorm_def, ← spectralAlgNorm_mul (K := K) x x⁻¹,
    mul_inv_cancel₀ H, spectralAlgNorm_one]


-- @@ L103-103 expanded
noncomputable instance :
    NontriviallyNormedField (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) :=
  Valued.toNontriviallyNormedField _ _


-- @@ L105-114 expanded
instance valuationRing_integralClosure {L : Type*} [Field L]
    [Algebra (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) L]
    [Algebra.IsAlgebraic (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) L] :
    ValuationRing
      (IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v) L) :=
  by
  refine
    ValuationSubring.instValuationRingSubtypeMem
      ⟨(integralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v)
            L).toSubring,
        ?_⟩
  intro x
  obtain hx | hx :=
    le_total (spectralNorm (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) L x) 1
  · exact .inl (isIntegral_of_spectralNorm_le_one hx)
  · have := inv_le_one_of_one_le₀ hx
    rw [← spectralNorm_inv] at this
    exact .inr (isIntegral_of_spectralNorm_le_one this)


-- @@ L116-120 expanded
/-- The local inertia subgroup of a number field at a prime, defined as a subgroup
of the local galois group. -/
noncomputable def localInertiaGroup :
    Subgroup (Field.absoluteGaloisGroup (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) :=
  (IsLocalRing.maximalIdeal
        (IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v)
          (AlgebraicClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)))).toAddSubgroup.inertia
    (Field.absoluteGaloisGroup (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))


-- @@ L122-136 expanded
open IntermediateField in
/-- The subgroup of the local galois group which is the kernel of the canonical map `Iᵥ → k(v)ˣ`.
Note that this definition is somewhat cheating, abusing the fact that the field corresponding
to this subgroup is `Kᵘʳ(ᵖ⁻¹√ϖ)` (where `p` is `#k(v)` and not the characteristic)
and that all units in `Kᵘʳ` have `p-1`-th roots.

TODO: show that this is indeed the right group. -/
noncomputable def localTameAbelianInertiaGroup :
    Subgroup (Field.absoluteGaloisGroup (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
    where
  carrier :=
    {σ |
      ∀ x,
        x ^
              (Nat.card
                  (IsLocalRing.ResidueField
                    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v)) -
                1) ∈
            fixedField (localInertiaGroup v) →
          σ x = x}
  mul_mem' {σ τ} hσ hτ x hx := by dsimp; rw [hτ x hx, hσ x hx]
  one_mem' _ _ := rfl
  inv_mem' {σ} hσ x
    hx := by
    conv_lhs => rw [← hσ x hx]
    simp [AlgEquiv.aut_inv]


-- @@ L138-139 expanded
instance : CharZero (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) :=
  ((algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)).charZero_iff
        (algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)).injective).mp
    inferInstance


-- @@ L141-144 verbatim
instance {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L] :
    Algebra.IsInvariant K L (L ≃ₐ[K] L) :=
  ⟨fun _ H ↦ (InfiniteGalois.fixedField_fixingSubgroup
    (⊥ : IntermediateField K L)).le fun _ ↦ H _⟩


-- @@ L146-146 expanded
instance :
    Finite
      (IsLocalRing.ResidueField (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v)) :=
  inferInstance


-- @@ L148-153 expanded
instance finite_adicCompletionIntegers_quotient
    {I : Ideal (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v)} [I.IsPrime]
    [NeZero I] : Finite (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v ⧸ I) :=
  by
  obtain rfl :=
    ((IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime
                (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v)).mp
            inferInstance).2.unique
      ⟨NeZero.ne _, ‹I.IsPrime›⟩
      ⟨IsDiscreteValuationRing.not_a_field
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v),
        inferInstanceAs (IsLocalRing.maximalIdeal _).IsPrime⟩
  exact inferInstanceAs <| Finite (IsLocalRing.ResidueField _)


-- @@ L155-161 expanded
instance neZero_maximalIdeal_integralClosure :
    NeZero
      (IsLocalRing.maximalIdeal
        (IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v)
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)))) :=
  by
  have : IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v ≠ ⊤ :=
    by
    refine fun h ↦
      IsDiscreteValuationRing.not_isField
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v) (h ▸ ?_)
    exact
      (Subring.topEquiv (R := IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)).isField
        (Semifield.toIsField (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
  exact
    ⟨(Ideal.bot_lt_of_maximal (IsLocalRing.maximalIdeal _)
          (not_isField_integralClosure (L :=
            AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) _ this)).ne'⟩


-- @@ L163-166 expanded
/-- An arbitrary choice of an (arithmetic) frobenious element of a local galois group. -/
noncomputable def Field.AbsoluteGaloisGroup.adicArithFrob :
    Field.absoluteGaloisGroup (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) :=
  arithFrobAt' (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v)
    (Field.absoluteGaloisGroup (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
    (IsLocalRing.maximalIdeal
      (IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))))


-- @@ L168-168 verbatim
local notation "Frobᵥ" => Field.AbsoluteGaloisGroup.adicArithFrob v


-- @@ L170-172 expanded
lemma Field.AbsoluteGaloisGroup.isArithFrobAt_adicArithFrob :
    IsArithFrobAt (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v)
      (Field.AbsoluteGaloisGroup.adicArithFrob v)
      (IsLocalRing.maximalIdeal
        (IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v)
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)))) :=
  .arithFrobAt' (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v)
    (Field.absoluteGaloisGroup (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
    (IsLocalRing.maximalIdeal
      (IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))))

