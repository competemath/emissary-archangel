import OAI.Analysis.LipschitzEquivalence.SmoothMultiplier


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe uH uIndex


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
namespace LipschitzCounterexample.CompactWSC

-- @@ L9-9 verbatim
open scoped ContDiff BigOperators NNReal Topology

-- @@ L10-10 verbatim
open Set Filter MeasureTheory FreeSpace

-- @@ L11-11 verbatim
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]


-- @@ L13-44 verbatim
theorem smoothPair_le_majorant (a : MolecularData H) (f : Smooth H)
    {Q : Set H} (hQ : Convex ℝ Q) (ha : ∀ i, a.p i ∈ Q ∧ a.q i ∈ Q)
    (b : H → ℝ) (hb : Continuous b) (hbound : ∀ x ∈ Q, ‖Smooth.grad x f‖ ≤ b x) :
    |smoothPair a f| ≤ ∑ i, (|a.coeff i| * dist (a.p i) (a.q i))*
      ∫ t in (0:ℝ)..1, b (edge (a.p i) (a.q i) t) := by
  have he (p q : H) (hp : p ∈ Q) (hq : q ∈ Q) :
      |f.val p-f.val q| ≤ dist p q * ∫ t in (0:ℝ)..1, b (edge p q t) := by
    rw [← smooth_edge_integral f p q]
    have hi : IntervalIntegrable (fun t => fderiv ℝ f.val (edge p q t) (p-q)) volume 0 1 :=
      (((f.contDiff.continuous_fderiv (by simp)).comp (edge_continuous p q)).clm_apply continuous_const).intervalIntegrable _ _
    calc
      _ ≤ ∫ t in (0:ℝ)..1, |fderiv ℝ f.val (edge p q t) (p-q)| :=
        intervalIntegral.abs_integral_le_integral_abs (by norm_num)
      _ ≤ ∫ t in (0:ℝ)..1, dist p q * b (edge p q t) := by
        apply intervalIntegral.integral_mono_on (by norm_num) hi.abs
          ((continuous_const.mul (hb.comp (edge_continuous p q))).intervalIntegrable _ _)
        intro t ht
        calc
          _ = ‖fderiv ℝ f.val (edge p q t) (p-q)‖ := (Real.norm_eq_abs _).symm
          _ ≤ ‖fderiv ℝ f.val (edge p q t)‖ * ‖p-q‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ b (edge p q t)*‖p-q‖ := mul_le_mul_of_nonneg_right
            (by rw [← Smooth.norm_grad]; exact hbound _ (edge_mem hQ hp hq ht)) (norm_nonneg _)
          _ = _ := by simp only [Pi.mul_apply,Function.comp_apply,dist_eq_norm]; ring
      _ = _ := intervalIntegral.integral_const_mul _ _
  calc
    |smoothPair a f| = |∑ i, a.coeff i*(f.val (a.p i)-f.val (a.q i))| := rfl
    _ ≤ ∑ i, |a.coeff i*(f.val (a.p i)-f.val (a.q i))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul,mul_assoc]
      exact mul_le_mul_of_nonneg_left (he _ _ (ha i).1 (ha i).2) (abs_nonneg _)


-- @@ L46-67 verbatim
theorem smoothPair_le_masses {ι : Type uIndex} (s : Finset ι) (z : ι → Smooth H)
    (a : MolecularData H) (f : Smooth H) {Q : Set H} (hQ : Convex ℝ Q)
    (ha : ∀ i, a.p i ∈ Q ∧ a.q i ∈ Q) (ε : ℝ)
    (hbound : ∀ x ∈ Q, ‖Smooth.grad x f‖ ≤ (∑ i ∈ s, ‖Smooth.grad x (z i)‖)+ε) :
    |smoothPair a f| ≤ (∑ i ∈ s, gradMass a (z i))+ε*a.cost := by
  classical
  have hb : Continuous (fun x => (∑ i ∈ s, ‖Smooth.grad x (z i)‖)+ε) :=
    (continuous_finsetSum s (fun i _ => (z i).grad_continuous.norm)).add continuous_const
  refine (smoothPair_le_majorant a f hQ ha _ hb hbound).trans_eq ?_
  have he (p q : H) : (∫ t in (0:ℝ)..1, (∑ i ∈ s, ‖Smooth.grad (edge p q t) (z i)‖)+ε) =
      (∑ i ∈ s, ∫ t in (0:ℝ)..1, ‖Smooth.grad (edge p q t) (z i)‖)+ε := by
    have hsum : IntervalIntegrable (fun t => ∑ i ∈ s, ‖Smooth.grad (edge p q t) (z i)‖) volume 0 1 := by
      exact (continuous_finsetSum s (fun i _ => ((z i).grad_continuous.comp (edge_continuous p q)).norm)).intervalIntegrable _ _
    rw [intervalIntegral.integral_add hsum intervalIntegrable_const,
      intervalIntegral.integral_finsetSum (fun i _ => grad_integrable (z i) p q)]
    simp
  simp only [he,mul_add,Finset.sum_add_distrib,Finset.mul_sum,gradMass,MolecularData.cost]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring


-- @@ L69-92 verbatim
theorem correction_pairing_bound {ι : Type uIndex} (s : Finset ι) (z : ι → Smooth H)
    (hz : ∀ i ∈ s, LipschitzWith 1 (z i).val) (f w : Smooth H)
    (hf : LipschitzWith 1 f.val) (a : MolecularData H) {Q : Set H} (hQ : Convex ℝ Q)
    (ha : ∀ i, a.p i ∈ Q ∧ a.q i ∈ Q) (ε : ℝ)
    (herr : ∀ x ∈ Q, ‖Smooth.grad x w-damping s z x • Smooth.grad x f‖ ≤ ε) :
    |smoothPair a w-smoothPair a f| ≤ (∑ i ∈ s, gradMass a (z i))+ε*a.cost := by
  rw [← map_sub]
  apply smoothPair_le_masses s z a (w-f) hQ ha ε
  intro x hx
  have hf' : ‖Smooth.grad x f‖ ≤ 1 := by simpa using f.grad_norm_le hf x
  have hd0 := damping_nonneg s z hz x
  have hd1 := damping_le_one s z hz x
  have he : Smooth.grad x (w-f) = (Smooth.grad x w-damping s z x • Smooth.grad x f)+
      (damping s z x-1) • Smooth.grad x f := by rw [map_sub]; module
  rw [he]
  calc
    _ ≤ ‖Smooth.grad x w-damping s z x • Smooth.grad x f‖+
        ‖(damping s z x-1) • Smooth.grad x f‖ := norm_add_le _ _
    _ ≤ ε+(1-damping s z x) := by
      apply add_le_add (herr x hx)
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr hd1)]
      have hmul := mul_le_mul_of_nonneg_left hf' (sub_nonneg.mpr hd1)
      nlinarith
    _ ≤ _ := by linarith [one_sub_damping_le s z hz x]


-- @@ L94-94 verbatim
end LipschitzCounterexample.CompactWSC

-- @@ L95-95 verbatim
end


-- @@ L97-97 verbatim
end OAI
