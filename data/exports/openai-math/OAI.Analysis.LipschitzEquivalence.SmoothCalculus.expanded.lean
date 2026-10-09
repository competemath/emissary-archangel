import OAI.Analysis.LipschitzEquivalence.FiniteRows


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe uH


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
namespace LipschitzCounterexample.CompactWSC

-- @@ L9-9 verbatim
open scoped ContDiff BigOperators NNReal Topology

-- @@ L10-10 verbatim
open Set Filter MeasureTheory

-- @@ L11-12 verbatim
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]


-- @@ L14-23 verbatim
def smoothSubmodule (H : Type uH) [NormedAddCommGroup H] [NormedSpace ℝ H] :
    Submodule ℝ (H → ℝ) where
  carrier := {f | ContDiff ℝ ∞ f}
  zero_mem' := by exact (contDiff_const : ContDiff ℝ ∞ (fun _ : H => (0:ℝ)))
  add_mem' := by
    intro f g hf hg
    exact (show ContDiff ℝ ∞ f from hf).add (show ContDiff ℝ ∞ g from hg)
  smul_mem' := by
    intro c f hf
    exact (show ContDiff ℝ ∞ f from hf).const_smul c


-- @@ L25-25 verbatim
abbrev Smooth (H : Type uH) [NormedAddCommGroup H] [NormedSpace ℝ H] : Type _ := ↥(smoothSubmodule H)


-- @@ L27-27 verbatim
namespace Smooth


-- @@ L29-32 verbatim
def eval (p : H) : Smooth H →ₗ[ℝ] ℝ where
  toFun f := (f : H → ℝ) p
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl


-- @@ L34-35 verbatim
theorem contDiff {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : Smooth H) : ContDiff ℝ ∞ (f : H → ℝ) := f.property


-- @@ L37-38 verbatim
theorem differentiable (f : Smooth H) : Differentiable ℝ (f : H → ℝ) :=
  f.contDiff.differentiable (by simp)


-- @@ L40-49 verbatim
def grad (p : H) : Smooth H →ₗ[ℝ] H where
  toFun f := gradient (f : H → ℝ) p
  map_add' f g := by
    change (InnerProductSpace.toDual ℝ H).symm (fderiv ℝ ((f : H → ℝ)+(g : H → ℝ)) p) = _
    rw [fderiv_add (f.differentiable p) (g.differentiable p),map_add]
    rfl
  map_smul' c f := by
    change (InnerProductSpace.toDual ℝ H).symm (fderiv ℝ (c • (f : H → ℝ)) p) = _
    rw [fderiv_const_smul (f.differentiable p) c,map_smul]
    rfl


-- @@ L51-51 verbatim
theorem grad_eq (f : Smooth H) (p : H) : grad p f = gradient (f : H → ℝ) p := rfl


-- @@ L53-54 verbatim
theorem norm_grad (f : Smooth H) (p : H) : ‖grad p f‖ = ‖fderiv ℝ (f : H → ℝ) p‖ :=
  (InnerProductSpace.toDual ℝ H).symm.norm_map _


-- @@ L56-58 verbatim
theorem grad_contDiff (f : Smooth H) : ContDiff ℝ ∞ (fun p => grad p f) :=
  (InnerProductSpace.toDual ℝ H).symm.toContinuousLinearEquiv.contDiff.comp
    (f.contDiff.fderiv_right (by simp))


-- @@ L60-61 verbatim
theorem grad_continuous (f : Smooth H) : Continuous (fun p => grad p f) :=
  f.grad_contDiff.continuous


-- @@ L63-66 verbatim
theorem grad_norm_le {C : ℝ≥0} (f : Smooth H) (h : LipschitzWith C (f : H → ℝ)) (p : H) :
    ‖grad p f‖ ≤ C := by
  rw [norm_grad]
  exact norm_fderiv_le_of_lipschitz ℝ h


-- @@ L68-69 verbatim
def mul (f g : Smooth H) : Smooth H := ⟨fun p => (f : H → ℝ) p*(g : H → ℝ) p,
  f.contDiff.mul g.contDiff⟩


-- @@ L71-71 verbatim
@[simp] theorem mul_apply (f g : Smooth H) (p : H) : (f.mul g : H → ℝ) p = f.val p*g.val p := rfl


-- @@ L73-77 verbatim
theorem grad_mul (f g : Smooth H) (p : H) :
    grad p (f.mul g) = f.val p • grad p g + g.val p • grad p f := by
  apply (InnerProductSpace.toDual ℝ H).injective
  simp only [grad_eq,toDual_gradient,map_add,map_smul]
  exact fderiv_mul (f.differentiable p) (g.differentiable p)


-- @@ L79-79 verbatim
end Smooth


-- @@ L81-81 verbatim
def edge (p q : H) (t : ℝ) : H := q+t • (p-q)


-- @@ L83-86 verbatim
theorem edge_continuous {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (p q : H) : Continuous (edge p q) := by
  unfold edge
  fun_prop


-- @@ L88-93 verbatim
theorem edge_mem {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {K : Set H} (hK : Convex ℝ K) {p q : H} (hp : p ∈ K) (hq : q ∈ K)
    {t : ℝ} (ht : t ∈ Icc 0 1) : edge p q t ∈ K := by
  have he : edge p q t = (1-t) • q+t • p := by simp [edge,sub_smul,smul_sub]; module
  rw [he]
  exact hK hq hp (sub_nonneg.mpr ht.2) ht.1 (by ring)


-- @@ L95-98 verbatim
theorem edge_hasDerivAt {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (p q : H) (t : ℝ) : HasDerivAt (edge p q) (p-q) t := by
  unfold edge
  simpa only [id_eq,one_smul] using ((hasDerivAt_id t).smul_const (p-q)).const_add q


-- @@ L100-107 verbatim
theorem smooth_edge_integral (f : Smooth H) (p q : H) :
    (∫ t in (0:ℝ)..1, fderiv ℝ (f : H → ℝ) (edge p q t) (p-q)) = f.val p-f.val q := by
  have hint : IntervalIntegrable (fun t => fderiv ℝ (f : H → ℝ) (edge p q t) (p-q)) volume 0 1 :=
    ((f.contDiff.continuous_fderiv (by simp)).comp (edge_continuous p q)).clm_apply continuous_const
      |>.intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ uIcc (0:ℝ) 1) => (f.differentiable _).hasFDerivAt.comp_hasDerivAt t (edge_hasDerivAt p q t)) hint
  simpa [edge] using h


-- @@ L109-109 verbatim
open FreeSpace


-- @@ L111-113 verbatim
def gradEnergy (a : MolecularData H) (f : Smooth H) : ℝ :=
  ∑ i, (|a.coeff i| *dist (a.p i) (a.q i)) *
    ∫ t in (0:ℝ)..1, ‖Smooth.grad (edge (a.p i) (a.q i) t) f‖^2


-- @@ L115-117 verbatim
def gradMass (a : MolecularData H) (f : Smooth H) : ℝ :=
  ∑ i, (|a.coeff i| *dist (a.p i) (a.q i)) *
    ∫ t in (0:ℝ)..1, ‖Smooth.grad (edge (a.p i) (a.q i) t) f‖


-- @@ L119-123 verbatim
theorem gradEnergy_nonneg (a : MolecularData H) (f : Smooth H) : 0 ≤ gradEnergy a f := by
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (mul_nonneg (abs_nonneg _) dist_nonneg)
  exact intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => sq_nonneg _)


-- @@ L125-129 verbatim
theorem gradMass_nonneg (a : MolecularData H) (f : Smooth H) : 0 ≤ gradMass a f := by
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (mul_nonneg (abs_nonneg _) dist_nonneg)
  exact intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => norm_nonneg _)


-- @@ L131-146 verbatim
theorem gradEnergy_midpoint (a : MolecularData H) (f g : Smooth H) :
    gradEnergy a ((1/2:ℝ) • (f+g)) =
      (gradEnergy a f+gradEnergy a g)/2-gradEnergy a (f-g)/4 := by
  have he (p q : H) :
      (∫ t in (0:ℝ)..1, ‖Smooth.grad (edge p q t) ((1/2:ℝ) • (f+g))‖^2) =
      ((∫ t in (0:ℝ)..1, ‖Smooth.grad (edge p q t) f‖^2)+
       (∫ t in (0:ℝ)..1, ‖Smooth.grad (edge p q t) g‖^2))/2-
       (∫ t in (0:ℝ)..1, ‖Smooth.grad (edge p q t) (f-g)‖^2)/4 := by
    have hf : IntervalIntegrable (fun t : ℝ => ‖Smooth.grad (edge p q t) f‖^2) volume 0 1 := ((f.grad_continuous.comp (edge_continuous p q)).norm.pow 2).intervalIntegrable (μ := volume) (0:ℝ) 1
    have hg : IntervalIntegrable (fun t : ℝ => ‖Smooth.grad (edge p q t) g‖^2) volume 0 1 := ((g.grad_continuous.comp (edge_continuous p q)).norm.pow 2).intervalIntegrable (μ := volume) (0:ℝ) 1
    have hfg : IntervalIntegrable (fun t : ℝ => ‖Smooth.grad (edge p q t) (f-g)‖^2) volume 0 1 := (((f-g).grad_continuous.comp (edge_continuous p q)).norm.pow 2).intervalIntegrable (μ := volume) (0:ℝ) 1
    simp only [map_smul,map_add,hilbert_midpoint_energy,← map_sub]
    rw [intervalIntegral.integral_sub ((hf.add hg).div_const 2) (hfg.div_const 4),
      intervalIntegral.integral_div,intervalIntegral.integral_add hf hg,intervalIntegral.integral_div]
  simp only [gradEnergy,he,mul_sub,← mul_div_assoc,mul_add,Finset.sum_sub_distrib,
    ← Finset.sum_div,Finset.sum_add_distrib]


-- @@ L148-148 verbatim
end LipschitzCounterexample.CompactWSC

-- @@ L149-149 verbatim
end


-- @@ L151-151 verbatim
end OAI
