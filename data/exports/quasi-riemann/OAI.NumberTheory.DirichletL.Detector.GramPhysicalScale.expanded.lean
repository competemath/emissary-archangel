import OAI.NumberTheory.DirichletL.Detector.GramMobiusLattice
import OAI.NumberTheory.DirichletL.Detector.GramNonexceptionalBlock


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical

-- @@ L8-8 verbatim
namespace SevenEighths.ProbeGramCommon

-- @@ L9-9 verbatim
open ProbePhysical CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT

-- @@ L10-10 verbatim
local notation "O" => ActualEisensteinCubic.O

 
-- @@ L12-13 verbatim
def residualScale (C D : SupportedIdeal) (Y : ℝ) : ℝ :=
  Y/((Ideal.absNorm C.val:ℝ)*Ideal.absNorm D.val)


-- @@ L15-18 verbatim
lemma residualScale_pos (C D : SupportedIdeal) (Y : ℝ) (hY : 0<Y) : 0<residualScale C D Y := by
  have hc : (0:ℝ)<Ideal.absNorm C.val := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr C.property.1)
  have hd : (0:ℝ)<Ideal.absNorm D.val := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr D.property.1)
  exact div_pos hY (mul_pos hc hd)


-- @@ L20-24 verbatim
lemma residual_column_ratio (C D I : SupportedIdeal) (Y : ℝ) (hY : 0<Y) :
    (Ideal.absNorm (supportedIdealProduct C (supportedIdealProduct D I)).val:ℝ)/Y=
      (Ideal.absNorm I.val:ℝ)/residualScale C D Y := by
  simp only [supportedIdealProduct,map_mul,Nat.cast_mul,residualScale]
  field_simp

 
-- @@ L26-27 verbatim
def frequencyScale (C : SupportedIdeal) (k : O) (Y Q : ℝ) : ℝ :=
  (Ideal.absNorm C.val:ℝ)*‖eisEmbedding k‖^2/(Y^2/Q)


-- @@ L29-30 verbatim
lemma frequencyScale_nonneg (C : SupportedIdeal) (k : O) (Y Q : ℝ) (hQ : 0≤Q) :
    0≤frequencyScale C k Y Q := by unfold frequencyScale;positivity


-- @@ L32-44 verbatim
theorem original_kernel_residual_scale (C D I J : SupportedIdeal) (k : O)
    (Y Q : ℝ) (hY : 0<Y) (hQ : 0<Q) :
    Q*‖eisEmbedding (primaryGenerator C.val*k)‖^2/
      ‖eisEmbedding (primaryGenerator (supportedIdealProduct C (supportedIdealProduct D I)).val*
        primaryGenerator (supportedIdealProduct C (supportedIdealProduct D J)).val)‖^2=
      frequencyScale C k Y Q/
        (((Ideal.absNorm I.val:ℝ)/residualScale C D Y)*((Ideal.absNorm J.val:ℝ)/residualScale C D Y)) := by
  rw [lowGram_kernel_scale Y Q hY hQ _ _ (primaryGenerator C.val*k),
    residual_column_ratio C D I Y hY,residual_column_ratio C D J Y hY]
  rw [map_mul,norm_mul,mul_pow,ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,
    (primaryGenerator_spec C.val (supported_primaryGenerator_ne_zero C.val C.property)).1]
  unfold frequencyScale
  ring


-- @@ L46-49 verbatim
lemma physicalPoint_first_norm (N : ℝ) (hN : 0<N) (m : O×O) :
    ‖(WithLp.ofLp (ProbeGramLatticeDecay.physicalPoint N m)).1‖^2=‖eisEmbedding m.1‖^2/N := by
  simp only [ProbeGramLatticeDecay.physicalPoint,ProbeGramLatticeDecay.point,WithLp.ofLp_toLp]
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.sqrt_pos.mpr hN),div_pow,Real.sq_sqrt hN.le]


-- @@ L51-54 verbatim
lemma physicalPoint_second_norm (N : ℝ) (hN : 0<N) (m : O×O) :
    ‖(WithLp.ofLp (ProbeGramLatticeDecay.physicalPoint N m)).2‖^2=‖eisEmbedding m.2‖^2/N := by
  simp only [ProbeGramLatticeDecay.physicalPoint,ProbeGramLatticeDecay.point,WithLp.ofLp_toLp]
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.sqrt_pos.mpr hN),div_pow,Real.sq_sqrt hN.le]


-- @@ L56-56 verbatim
end SevenEighths.ProbeGramCommon

-- @@ L57-57 verbatim
end


-- @@ L59-59 verbatim
end OAI
