import OAI.Geometry.Arnold.Homotopy


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe uE uF


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open scoped BigOperators ContDiff

-- @@ L9-9 verbatim
open MeasureTheory Set Filter

-- @@ L10-10 verbatim
open scoped Matrix.Norms.Operator

-- @@ L11-11 verbatim
open scoped Topology

-- @@ L12-12 verbatim
open Function

-- @@ L13-13 verbatim
open ContinuousAlternatingMap


-- @@ L15-15 verbatim
namespace ArnoldCounterexample.CriticalBound

-- @@ L16-16 verbatim
open ArnoldCounterexample.Forms ContinuousAlternatingMap


-- @@ L18-19 verbatim
local instance : TopologicalSpace RM :=
  (inferInstance : NormedAddCommGroup RM).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace


-- @@ L21-69 verbatim
/-- The Haar integral of a closed horizontal cylinder form is independent of
its slice. The bracket condition is algebraic. -/
theorem haar_homotopy_invariant
    (Θ : ℝ × RM → (ℝ × RM) [⋀^Fin 6]→L[ℝ] ℝ)
    (hΘ : ContDiff ℝ ∞ Θ) (hclosed : ∀ p, extDeriv Θ p = 0)
    (hvertical : ∀ (t : ℝ) (A : O5) (i j : Fin 5),
      sliceContraction Θ t A
        (Matrix.vecCons ((A : RM) * (generators i.castSucc * generators j.succ -
          generators j.succ * generators i.castSucc))
          (j.removeNth (i.castSucc.removeNth (fun k ↦ (A : RM) * generators k)))) = 0)
    (a b : ℝ) :
    (∫ A : O5, Θ (a, A) (fun i ↦ (0, (A : RM) * generators i)) ∂haar) =
    (∫ A : O5, Θ (b, A) (fun i ↦ (0, (A : RM) * generators i)) ∂haar) := by
  let : CompactSpace O5 := o5_compactSpace
  let : BorelSpace O5 := o5_borelSpace
  let F : ℝ → O5 → ℝ := fun t A ↦ Θ (t, A) (fun i ↦ (0, (A : RM) * generators i))
  let D : ℝ → O5 → ℝ := fun t A ↦
    (fderiv ℝ Θ (t, A) (1, 0)) (fun i ↦ (0, (A : RM) * generators i))
  have hF : Continuous (Function.uncurry F) := by
    have h := contDiff_alternating_apply hΘ (v := fun i p ↦ (0, p.2 * generators i))
      (fun i ↦ (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × RM ↦ (0 : ℝ))).prodMk
        (contDiff_snd.mul contDiff_const))
    exact h.continuous.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hD : Continuous (Function.uncurry D) := by
    have hd : ContDiff ℝ ∞ (fun p : ℝ × RM ↦ fderiv ℝ Θ p (1, 0)) :=
      (hΘ.fderiv_right (by simp)).clm_apply contDiff_const
    have h := contDiff_alternating_apply hd (v := fun i p ↦ (0, p.2 * generators i))
      (fun i ↦ (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × RM ↦ (0 : ℝ))).prodMk
        (contDiff_snd.mul contDiff_const))
    exact h.continuous.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hd (t : ℝ) (A : O5) : HasDerivAt (fun s ↦ F s A) (D t A) t := by
    have h := ((ContinuousAlternatingMap.apply ℝ (ℝ × RM) ℝ
      (fun i ↦ (0, (A : RM) * generators i))).hasFDerivAt).comp_hasDerivAt t
        ((hΘ.differentiable (by simp) (t, A)).hasFDerivAt.comp_hasDerivAt t
          ((hasDerivAt_id t).prodMk (hasDerivAt_const t (A : RM))))
    exact h
  have dzero (t : ℝ) : ∫ A : O5, D t A ∂haar = 0 := by
    have hz := integral_extDeriv_rightMul_eq_zero (sliceContraction Θ t)
      (sliceContraction_contDiff Θ hΘ t) generators generators_skew (hvertical t)
    convert hz using 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun A ↦
      (cylinder_homotopy_identity Θ (hΘ.differentiable (by simp)) t A
        (hclosed (t, A)) (fun i ↦ (A : RM) * generators i)).symm)
  have hder (t : ℝ) : HasDerivAt (fun s ↦ ∫ A, F s A ∂haar) 0 t := by
    convert hasDerivAt_integral_of_compact haar hF hD hd t using 1
    exact (dzero t).symm
  exact is_const_of_deriv_eq_zero (fun t ↦ (hder t).differentiableAt)
    (fun t ↦ (hder t).deriv) a b


-- @@ L71-71 verbatim
end ArnoldCounterexample.CriticalBound


-- @@ L73-73 verbatim
namespace ArnoldCounterexample.CriticalBound

-- @@ L74-74 verbatim
open ArnoldCounterexample.Forms ContinuousAlternatingMap


-- @@ L76-82 verbatim
lemma symplectic_velocities (i j : Fin 6) :
    symplectic 5 (velocities i) (velocities j) =
      if (i, j) ∈ ({(0, 1), (2, 3), (4, 5)} : Finset (Fin 6 × Fin 6)) then 1
      else if (j, i) ∈ ({(0, 1), (2, 3), (4, 5)} : Finset (Fin 6 × Fin 6)) then -1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [symplectic_apply, velocities, Fin.sum_univ_succ, Pi.single_apply,
      Complex.mul_re, Complex.mul_im, ← sq, baseScale_sq]


-- @@ L84-87 verbatim
lemma cubeForm_velocities : cubeForm (symplectic 5) velocities = 48 := by
  simp only [cubeForm, pairForm_apply, squareForm_apply _ (symplectic_skew 5)]
  simp +decide [Fin.sum_univ_succ, Fin.removeNth, Fin.succAbove, symplectic_velocities]
  norm_num


-- @@ L89-89 verbatim
end ArnoldCounterexample.CriticalBound


-- @@ L91-91 verbatim
namespace ArnoldCounterexample.Forms

-- @@ L92-92 verbatim
open ContinuousAlternatingMap


-- @@ L94-94 verbatim
abbrev ProductSpace := CSpace 5 × CSpace 3


-- @@ L96-98 verbatim
def productSymplectic : ProductSpace →L[ℝ] ProductSpace →L[ℝ] ℝ :=
  (symplectic 5).bilinearComp (.fst ℝ (CSpace 5) (CSpace 3)) (.fst ℝ (CSpace 5) (CSpace 3)) +
  (symplectic 3).bilinearComp (.snd ℝ (CSpace 5) (CSpace 3)) (.snd ℝ (CSpace 5) (CSpace 3))


-- @@ L100-101 verbatim
@[simp] lemma productSymplectic_apply (u v : ProductSpace) :
    productSymplectic u v = symplectic 5 u.1 v.1 + symplectic 3 u.2 v.2 := rfl


-- @@ L103-107 verbatim
lemma productSymplectic_skew (u v : ProductSpace) :
    productSymplectic u v = -productSymplectic v u := by
  simp only [productSymplectic_apply, symplectic_skew 5 u.1 v.1,
    symplectic_skew 3 u.2 v.2]
  ring


-- @@ L109-109 verbatim
def productNormSq (z : ProductSpace) : ℝ := normSq 5 z.1 + normSq 3 z.2


-- @@ L111-112 verbatim
lemma productNormSq_contDiff : ContDiff ℝ ∞ productNormSq :=
  (normSq_contDiff 5 |>.comp contDiff_fst).add (normSq_contDiff 3 |>.comp contDiff_snd)


-- @@ L114-124 verbatim
lemma productNormSq_fderiv (z v : ProductSpace) :
    fderiv ℝ productNormSq z v = -productSymplectic (Complex.I • z) v := by
  have hn5 := (normSq_contDiff 5).differentiable (by simp)
  have hn3 := (normSq_contDiff 3).differentiable (by simp)
  have hd := ((hn5 z.1).hasFDerivAt.comp z hasFDerivAt_fst).add
    ((hn3 z.2).hasFDerivAt.comp z hasFDerivAt_snd)
  rw [show fderiv ℝ productNormSq z = _ from hd.fderiv]
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', normSq_fderiv, productSymplectic_apply, Prod.smul_fst,
    Prod.smul_snd]
  ring


-- @@ L126-135 verbatim
lemma productNormSq_curve_orthogonal {c : ℝ → ProductSpace} {v : ProductSpace} {t : ℝ}
    (hc : HasDerivAt c v t) (hunit : ∀ s, productNormSq (c s) = 1) :
    productSymplectic (Complex.I • c t) v = 0 := by
  have hd := (productNormSq_contDiff.differentiable (by simp) (c t)).hasFDerivAt.comp_hasDerivAt t hc
  have heq : (fun s ↦ productNormSq (c s)) = fun _ : ℝ ↦ 1 := funext hunit
  dsimp only [Function.comp_def] at hd
  rw [heq] at hd
  have hzero := hd.unique (hasDerivAt_const t 1)
  rw [productNormSq_fderiv] at hzero
  exact neg_eq_zero.mp hzero


-- @@ L137-140 verbatim
lemma normSq_real_smul (n : ℕ) (a : ℝ) (z : CSpace n) :
    normSq n (a • z) = a ^ 2 * normSq n z := by
  simp [normSq, Pi.smul_apply, Complex.real_smul, Complex.normSq_mul,
    Complex.normSq_ofReal, Finset.mul_sum, sq]


-- @@ L142-160 verbatim
/-- Differentiating honest circle equivariance, rather than assuming its
infinitesimal consequence. -/
lemma fderiv_circle_equivariant {m n : ℕ} (F : CSpace m → CSpace n)
    (hF : Differentiable ℝ F) (z : CSpace m)
    (hphase : ∀ a : ℂ, Complex.normSq a = 1 → F (a • z) = a • F z) :
    fderiv ℝ F z (Complex.I • z) = Complex.I • F z := by
  let a : ℝ → ℂ := fun t ↦ Complex.exp ((t : ℂ) * Complex.I)
  have ha : HasDerivAt a Complex.I 0 := by
    simpa [a] using ((Complex.ofRealCLM.hasDerivAt).mul_const Complex.I).cexp (x := (0 : ℝ))
  have ha0 : a 0 = 1 := by simp [a]
  have hau (t : ℝ) : Complex.normSq (a t) = 1 := by
    simp [a, Complex.normSq_eq_norm_sq, Complex.norm_exp]
  have heq : (fun t ↦ F (a t • z)) = fun t ↦ a t • F z :=
    funext (fun t ↦ hphase _ (hau t))
  have hd := (hF (a 0 • z)).hasFDerivAt.comp_hasDerivAt 0 (ha.smul_const z)
  rw [ha0, one_smul] at hd
  dsimp only [Function.comp_def] at hd
  rw [heq] at hd
  exact hd.unique (ha.smul_const (F z))


-- @@ L162-162 verbatim
end ArnoldCounterexample.Forms


-- @@ L164-164 verbatim
namespace ArnoldCounterexample.Forms


-- @@ L166-171 verbatim
lemma time_slice_hasDerivAt {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (H : ℝ × E → F) (hH : Differentiable ℝ H) (x : E) (t : ℝ) :
    HasDerivAt (fun s ↦ H (s, x)) (fderiv ℝ H (t, x) (1, 0)) t := by
  exact (hH (t, x)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))


-- @@ L173-178 verbatim
lemma productNormSq_time_tangent {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : ℝ × E → ProductSpace) (hH : ContDiff ℝ ∞ H) (x : E)
    (hunit : ∀ s, productNormSq (H (s, x)) = 1) (t : ℝ) :
    productSymplectic (Complex.I • H (t, x)) (fderiv ℝ H (t, x) (1, 0)) = 0 := by
  apply productNormSq_curve_orthogonal
    (time_slice_hasDerivAt H (hH.differentiable (by simp)) x t) hunit


-- @@ L180-180 verbatim
end ArnoldCounterexample.Forms


-- @@ L182-182 verbatim
namespace ArnoldCounterexample.Forms

-- @@ L183-183 verbatim
open ContinuousAlternatingMap


-- @@ L185-203 verbatim
lemma alternating_eq_zero_on_kernel
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} (hdim : Module.finrank ℝ E ≤ n)
    (θ : E [⋀^Fin n]→L[ℝ] ℝ) (L : E →L[ℝ] ℝ) (hL : L ≠ 0)
    (v : Fin n → E) (hv : ∀ i, L (v i) = 0) : θ v = 0 := by
  apply θ.toAlternatingMap.map_linearDependent
  intro hLI
  let v' : Fin n → L.ker := fun i ↦ ⟨v i, hv i⟩
  have hLI' : LinearIndependent ℝ v' := hLI.of_comp L.ker.subtype
  have htop : L.ker ≠ ⊤ := by
    intro ht
    apply hL
    ext x
    have hx : x ∈ L.ker := by rw [ht]; trivial
    exact hx
  have hc := hLI'.fintype_card_le_finrank
  have hlt := Submodule.finrank_lt htop
  simp only [Fintype.card_fin] at hc
  omega


-- @@ L205-219 verbatim
/-- Six tangent vectors of the unit five-sphere are necessarily dependent. -/
lemma six_form_vanishes_on_unit_sphere
    (θ : CSpace 3 [⋀^Fin 6]→L[ℝ] ℝ) (z : CSpace 3) (hz : normSq 3 z = 1)
    (v : Fin 6 → CSpace 3) (hv : ∀ i, fderiv ℝ (normSq 3) z (v i) = 0) :
    θ v = 0 := by
  apply alternating_eq_zero_on_kernel (L := fderiv ℝ (normSq 3) z) ?_ θ ?_ v hv
  · simp [CSpace, Module.finrank_pi_fintype, Complex.finrank_real_complex]
  · intro h
    have hs := normSq_fderiv 3 z z
    rw [h] at hs
    simp only [_root_.zero_apply, symplectic_I_left] at hs
    have heq : (∑ i : Fin 3, ((z i).re * (z i).re + (z i).im * (z i).im)) = 1 := by
      simpa only [normSq, Complex.normSq_apply] using hz
    rw [heq] at hs
    norm_num at hs


-- @@ L221-221 verbatim
end ArnoldCounterexample.Forms


-- @@ L223-223 verbatim
namespace ArnoldCounterexample.Forms

-- @@ L224-224 verbatim
open ContinuousAlternatingMap


-- @@ L226-243 verbatim
lemma cubeForm_second_radical_on {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hskew : ∀ u v, B u v = -B v u)
    (u w : E) (v : Fin 4 → E) (hw : B u w = 0) (hv : ∀ i, B u (v i) = 0) :
    cubeForm B (Matrix.vecCons w (Matrix.vecCons u v)) = 0 := by
  have hz := cubeForm_radical_on B hskew u (Matrix.vecCons w v) (by
    intro i
    refine Fin.cases hw (fun j ↦ hv j) i)
  have heq : (Matrix.vecCons w (Matrix.vecCons u v)) ∘ Equiv.swap (0 : Fin 6) 1 =
      Matrix.vecCons u (Matrix.vecCons w v) := by
    ext i
    fin_cases i <;> simp [Equiv.swap_apply_def]
  have hs := (cubeForm B).toAlternatingMap.map_swap
    (Matrix.vecCons w (Matrix.vecCons u v)) (show (0 : Fin 6) ≠ 1 by decide)
  rw [heq] at hs
  change cubeForm B (Matrix.vecCons u (Matrix.vecCons w v)) =
    -cubeForm B (Matrix.vecCons w (Matrix.vecCons u v)) at hs
  rw [hz] at hs
  exact neg_eq_zero.mp hs.symm


-- @@ L245-245 verbatim
end ArnoldCounterexample.Forms


-- @@ L247-247 verbatim
end


-- @@ L249-249 verbatim
end OAI
