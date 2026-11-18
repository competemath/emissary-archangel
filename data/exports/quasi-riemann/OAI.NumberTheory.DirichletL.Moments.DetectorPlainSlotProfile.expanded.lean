import OAI.NumberTheory.DirichletL.Moments.DetectorDictionaryUniformHeight
import OAI.NumberTheory.DirichletL.Moments.DetectorDictionarySlots
import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyData
import OAI.NumberTheory.DirichletL.Moments.RetainedEnergy


-- @@ L6-6 verbatim
namespace OAI


-- @@ L8-8 verbatim
noncomputable section


-- @@ L10-10 verbatim
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate

-- @@ L11-11 verbatim
namespace SevenEighths.CenteredMomentDetectorPlainSlotProfile

-- @@ L12-12 verbatim
open HeckeFamily HeckeInverseAmplification HeckeDyadic CenteredMomentDetectorDictionary

-- @@ L13-13 verbatim
open CenteredMomentRetainedEnergy

-- @@ L14-14 verbatim
local notation "O"=>HeckeFamily.O

-- @@ L15-15 verbatim
variable {Δ:ℝ}{D:Parameters.HighData Δ}


-- @@ L17-20 verbatim
lemma conjugate_source_support (F:ProbeFinalAssembly.SourceData D):
    Function.support (fun x=>conj (F.W x))⊆Set.Icc (1:ℝ) 2 := by
  intro x hx
  exact F.complex_support (by simpa using hx)


-- @@ L22-24 verbatim
private lemma conjugate_source_smooth (F : ProbeFinalAssembly.SourceData D) :
    ContDiff ℝ ∞ (fun x => conj (F.W x)) := by
  exact Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)


-- @@ L26-29 verbatim
def slotSchwartz (F:ProbeFinalAssembly.SourceData D)(ζ:ℂ):𝓢(ℝ,ℂ):=
  interpolatedProfile (fun x=>conj (F.W x)) 1 2 (by norm_num)
    (conjugate_source_support F) (conjugate_source_smooth F)
    (1-ζ.re) (-ζ.im)


-- @@ L31-41 verbatim
theorem slotSchwartz_apply (F:ProbeFinalAssembly.SourceData D)(ζ:ℂ)(x:ℝ):
    slotSchwartz F ζ x=conj (F.W x*(x:ℂ)^(ζ-1)) := by
  rw [slotSchwartz,interpolatedProfile_apply]
  unfold twistProfile
  by_cases hw:F.W x=0
  · simp [hw]
  have hx:0<x:=lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (F.complex_support hw).1
  rw [map_mul,conj_positive_cpow _ hx]
  congr 1
  congr 1
  apply Complex.ext <;> simp [HeckeDyadic.shift]


-- @@ L43-48 verbatim
theorem slotSchwartz_support (F:ProbeFinalAssembly.SourceData D)(ζ:ℂ):
    Function.support (slotSchwartz F ζ:ℝ→ℂ)⊆Set.Icc (1:ℝ) 2 := by
  intro x hx
  apply F.complex_support
  intro hw
  exact hx (by rw [slotSchwartz_apply,hw,zero_mul,map_zero])


-- @@ L50-51 verbatim
theorem slotSchwartz_smooth (F:ProbeFinalAssembly.SourceData D)(ζ:ℂ):
    ContDiff ℝ ∞ (slotSchwartz F ζ:ℝ→ℂ):=(slotSchwartz F ζ).smooth ⊤


-- @@ L53-67 verbatim
theorem slotSchwartz_norm (F:ProbeFinalAssembly.SourceData D)(ζ:ℂ)(hζ:ζ.re≤1)(x:ℝ):
    ‖slotSchwartz F ζ x‖≤1 := by
  rw [slotSchwartz_apply,RCLike.norm_conj]
  by_cases hw:F.W x=0
  · simp [hw]
  have hx:=F.complex_support hw
  have hxpos:0<x:=lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hx.1
  have hW:‖F.W x‖≤1 := by
    rw [F.complex_eq,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (F.bounded x).1]
    exact (F.bounded x).2
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
  have hp:x^((ζ-1).re)≤1:=
    (Real.rpow_le_rpow_of_exponent_le hx.1 (by simp only [Complex.sub_re,Complex.one_re];linarith)).trans_eq
      (Real.rpow_zero _)
  simpa only [one_mul] using mul_le_mul hW hp (Real.rpow_nonneg hxpos.le _) zero_le_one


-- @@ L69-74 verbatim
theorem physical_coefficient (F:ProbeFinalAssembly.SourceData D)(η:Character)
    (P:ℝ)(ζ:ℂ)(I:Ideal O):
    physicalSlotCoefficient η F.W P ζ I=
      idealCoeff η.inverse I*slotSchwartz F ζ ((I.absNorm:ℝ)/P) := by
  rw [slotSchwartz_apply]
  rfl


-- @@ L76-81 verbatim
theorem physical_coefficient_norm (F:ProbeFinalAssembly.SourceData D)(η:Character)
    (P:ℝ)(ζ:ℂ)(hζ:ζ.re≤1)(I:Ideal O):
    ‖physicalSlotCoefficient η F.W P ζ I‖≤1 := by
  rw [physical_coefficient,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (idealCoeff_norm_le_one η.inverse I)).trans (slotSchwartz_norm F ζ hζ _)


-- @@ L83-91 verbatim
theorem slotSchwartz_uniform (F:ProbeFinalAssembly.SourceData D)(S:Finset (ℕ×ℕ)):
    ∃J:ℕ,∃C:ℝ,0<C ∧ ∀ζ:ℂ,ζ.re∈Set.Icc (0:ℝ) 1 →
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (slotSchwartz F ζ)≤C*(1+‖ζ.im‖)^J := by
  obtain ⟨J,C,hC,hbound⟩:=interpolatedProfile_uniform (fun x=>conj (F.W x)) 1 2 (by norm_num)
    (conjugate_source_support F) (conjugate_source_smooth F) S
  refine ⟨J,C,hC,?_⟩
  intro ζ hζ
  have hh:=hbound (1-ζ.re) ⟨by linarith [hζ.2],by linarith [hζ.1]⟩ (-ζ.im)
  simpa only [slotSchwartz,norm_neg] using hh


-- @@ L93-102 verbatim
theorem slotSchwartz_height_uniform (F:ProbeFinalAssembly.SourceData D)(S:Finset (ℕ×ℕ)):
    ∃J:ℕ,∃C:ℝ,0<C ∧ ∀{ι:Type*}(ζ:ι→ℂ)(height:ℝ),0≤height →
      (∀i,(ζ i).re=17/50) → (∀i,|(ζ i).im|≤height) → ∀i,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (slotSchwartz F (ζ i))≤C*(1+height)^J := by
  obtain ⟨J,C,hC,hbound⟩:=slotSchwartz_uniform F S
  refine ⟨J,C,hC,?_⟩
  intro ι ζ height hheight hreal him i
  refine (hbound (ζ i) (by rw [hreal i];norm_num)).trans ?_
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact pow_le_pow_left₀ (by positivity) (by simp only [Real.norm_eq_abs];linarith [him i]) J


-- @@ L104-112 verbatim
theorem physical_positive_row {ι:Type*}[Fintype ι][DecidableEq ι]
    (F:ProbeFinalAssembly.SourceData D)(η η₀:Character)(m A z:O)
    (W₁ W₂:ℝ→ℂ)(S:ι→Finset (Ideal O))(P:ι→ℝ)(ζ:ι→ℂ)(t X₁ X₂:ℝ):
    positiveSlotRow η m A z W₁ W₂ S (fun i=>physicalSlotCoefficient η₀ F.W (P i) (ζ i)) P t X₁ X₂=
      positiveSlotRow η m A z W₁ W₂ S
        (fun i I=>idealCoeff η₀.inverse I*slotSchwartz F (ζ i) ((I.absNorm:ℝ)/P i)) P t X₁ X₂ := by
  congr 1
  funext i I
  exact physical_coefficient F η₀ (P i) (ζ i) I


-- @@ L114-114 verbatim
end SevenEighths.CenteredMomentDetectorPlainSlotProfile


-- @@ L116-116 verbatim
end


-- @@ L118-118 verbatim
end OAI
