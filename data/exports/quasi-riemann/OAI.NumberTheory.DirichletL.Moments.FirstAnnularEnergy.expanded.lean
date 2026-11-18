import OAI.NumberTheory.DirichletL.Moments.FirstAnnularMajorant
import OAI.NumberTheory.DirichletL.Moments.GaussNormalization


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators SchwartzMap

-- @@ L8-8 verbatim
namespace SevenEighths.CenteredMomentFirstAnnularEnergy

-- @@ L9-9 verbatim
open HeckeFamily CanonicalQuadraticSieve CenteredMomentGaussEnergy

-- @@ L10-10 verbatim
open CenteredMomentFirstAnnularMajorant CenteredMomentSectorLocalization

-- @@ L11-11 verbatim
open CenteredMomentCanonicalFirst CenteredMomentSmoothedWindowEnergy

-- @@ L12-12 verbatim
local notation "O"=>HeckeFamily.O


-- @@ L14-14 verbatim
variable {α:Type*}


-- @@ L16-21 verbatim
lemma dyadic_summable (S:Finset α)(a:α→O)(ha:∀i,Supported (Ideal.span {a i}))
    (c:α→ℂ)(j:ℤ):Summable (fun z:O=>dyadicWeight j (normValue z)*‖gaussPolynomial S a ha c z‖^2):=by
  have hs:=gaussEnergy_hasSum_re S a ha c CenteredMomentEnergyProfiles.annulusTemplate.profile
    (dyadicScale j) (dyadicScale_pos j)
  simpa only [CenteredMomentEnergyProfiles.annulusTemplate_apply,Complex.ofReal_re,
    dyadicWeight,normValue_eq_embedding,mul_comm] using hs.summable


-- @@ L23-26 verbatim
lemma weighted_summable (S:Finset α)(a:α→O)(ha:∀i,Supported (Ideal.span {a i}))
    (c:α→ℂ)(H:ℝ)(hH:0<H):
    Summable (fun z:O=>‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re):=by
  simpa only [normValue_eq_embedding] using (gaussEnergy_hasSum_re S a ha c profile H hH).summable


-- @@ L28-57 verbatim
theorem energy_partition (S:Finset α)(a:α→O)(ha:∀i,Supported (Ideal.span {a i}))
    (c:α→ℂ)(H:ℝ)(hH:0<H):
    (gaussEnergy S a ha c profile H).re=
      ∑j∈bands H,∑'z:O,dyadicWeight j (normValue z)*
        (‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re):=by
  have hs:=weighted_summable S a ha c H hH
  have hj (j:ℤ):Summable (fun z:O=>dyadicWeight j (normValue z)*
      (‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re)):=by
    apply hs.of_nonneg_of_le
    · intro z
      exact mul_nonneg (dyadicWeight_bounds j _).1 (mul_nonneg (sq_nonneg _) (profile_nonneg _))
    · intro z
      exact mul_le_of_le_one_left (mul_nonneg (sq_nonneg _) (profile_nonneg _)) (dyadicWeight_bounds j _).2
  have he (z:O):‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re=
      ∑j∈bands H,dyadicWeight j (normValue z)*
        (‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re):=by
    rw [←Finset.sum_mul]
    calc
      _=‖gaussPolynomial S a ha c z‖^2*
          ((∑j∈bands H,dyadicWeight j (normValue z))*(profile (normValue z/H)).re):=by
        rw [←weighted_partition H (normValue z) hH]
      _=_:=by ring
  have hsum:=gaussEnergy_hasSum_re S a ha c profile H hH
  rw [←hsum.tsum_eq]
  simp_rw [←normValue_eq_embedding]
  calc
    _ = ∑'z:O, ∑j∈bands H,dyadicWeight j (normValue z)*
        (‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re) :=
      tsum_congr he
    _ = _ := Summable.tsum_finsetSum (fun j _=>hj j)


-- @@ L59-76 verbatim
theorem energy_le_dyadic (S:Finset α)(a:α→O)(ha:∀i,Supported (Ideal.span {a i}))
    (c:α→ℂ)(H:ℝ)(hH:0<H):
    (gaussEnergy S a ha c profile H).re≤
      ∑j∈bands H,∑'z:O,dyadicWeight j (normValue z)*‖gaussPolynomial S a ha c z‖^2:=by
  rw [energy_partition S a ha c H hH]
  apply Finset.sum_le_sum
  intro j hj
  have hs:=dyadic_summable S a ha c j
  have hdom (z:O):dyadicWeight j (normValue z)*
      (‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re)≤
      dyadicWeight j (normValue z)*‖gaussPolynomial S a ha c z‖^2:=
    mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (sq_nonneg _) (profile_le_one _))
      (dyadicWeight_bounds j _).1
  have hl:Summable (fun z:O=>dyadicWeight j (normValue z)*
      (‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re)):=
    hs.of_nonneg_of_le (fun z=>mul_nonneg (dyadicWeight_bounds j _).1
      (mul_nonneg (sq_nonneg _) (profile_nonneg _))) hdom
  exact hl.tsum_le_tsum hdom hs


-- @@ L78-78 verbatim
end SevenEighths.CenteredMomentFirstAnnularEnergy


-- @@ L80-80 verbatim
end


-- @@ L82-82 verbatim
end OAI
