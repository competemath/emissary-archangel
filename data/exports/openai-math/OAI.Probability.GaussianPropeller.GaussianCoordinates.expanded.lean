import OAI.Probability.GaussianPropeller.CellBounds


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe uE uι


-- @@ L7-7 verbatim
open MeasureTheory ProbabilityTheory

-- @@ L8-8 verbatim
open scoped ENNReal

-- @@ L9-9 verbatim
open scoped RealInnerProductSpace

-- @@ L10-10 verbatim
open scoped RealInnerProductSpace

-- @@ L11-11 verbatim
open MeasureTheory ProbabilityTheory Set

-- @@ L12-12 verbatim
open scoped ENNReal RealInnerProductSpace

-- @@ L13-13 verbatim
open Filter

-- @@ L14-14 verbatim
open scoped Topology

-- @@ L15-15 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L16-16 verbatim
open scoped Topology

-- @@ L17-17 verbatim
open scoped RealInnerProductSpace

-- @@ L18-18 verbatim
open Set Filter

-- @@ L19-19 verbatim
open scoped Topology RealInnerProductSpace

-- @@ L20-20 verbatim
open scoped NNReal

-- @@ L21-21 verbatim
open Set Filter

-- @@ L22-22 verbatim
open scoped Topology RealInnerProductSpace NNReal

-- @@ L23-23 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L24-24 verbatim
open scoped Topology RealInnerProductSpace

-- @@ L25-25 verbatim
open MeasureTheory Set Filter

-- @@ L26-26 verbatim
open scoped Topology BigOperators

-- @@ L27-27 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L28-28 verbatim
open scoped RealInnerProductSpace Topology


-- @@ L30-30 verbatim
namespace GaussianPropeller.Analytic

-- @@ L31-31 verbatim
section FamilyLaw

-- @@ L32-33 verbatim
variable {E : Type uE} {ι : Type uι} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]


-- @@ L35-38 verbatim
lemma covariance_inner_stdGaussian (u v : E) :
    cov[fun x => ⟪u,x⟫, fun x => ⟪v,x⟫; stdGaussian E] = ⟪u,v⟫ := by
  rw [← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
    covarianceBilin_stdGaussian, innerSL_apply_apply]


-- @@ L40-43 verbatim
lemma hasGaussianLaw_innerFamily (v : ι → E) :
    HasGaussianLaw (fun x : E => fun i => ⟪v i,x⟫) (stdGaussian E) := by
  exact (IsGaussian.hasGaussianLaw_id (μ := stdGaussian E)).map_fun
    (ContinuousLinearMap.pi (fun i => InnerProductSpace.toDual ℝ E (v i)))


-- @@ L45-48 verbatim
lemma indep_innerFamily (v : ι → E) (hv : Pairwise (fun i j => ⟪v i,v j⟫ = 0)) :
    iIndepFun (fun i x => ⟪v i,x⟫) (stdGaussian E) := by
  exact (hasGaussianLaw_innerFamily v).iIndepFun_of_covariance_eq_zero
    (fun i j hij => (covariance_inner_stdGaussian _ _).trans (hv hij))


-- @@ L50-54 verbatim
lemma map_inner_stdGaussian (v : E) :
    (stdGaussian E).map (fun x => ⟪v,x⟫) = gaussianReal 0 (‖v‖^2).toNNReal := by
  change (stdGaussian E).map (InnerProductSpace.toDual ℝ E v) = _
  rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian, LinearIsometryEquiv.norm_map]


-- @@ L56-64 verbatim
lemma map_orthonormal_stdGaussian (v : ι → E) (hv : Orthonormal ℝ v) :
    (stdGaussian E).map (fun x => fun i => ⟪v i,x⟫) =
      Measure.pi (fun _ : ι => gaussianReal 0 1) := by
  have hi := indep_innerFamily v (fun _ _ hij => hv.2 hij)
  rw [hi.map_fun_eq_pi_map (fun _ => by fun_prop)]
  congr 1
  funext i
  rw [map_inner_stdGaussian, hv.1 i]
  norm_num


-- @@ L66-66 verbatim
end FamilyLaw


-- @@ L68-68 verbatim
end GaussianPropeller.Analytic


-- @@ L70-70 verbatim
namespace GaussianPropeller.Analytic


-- @@ L72-72 verbatim
open scoped ENNReal


-- @@ L74-74 verbatim
section TripleLaw

-- @@ L75-76 verbatim
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]


-- @@ L78-88 verbatim
lemma map_orthonormal_triple_stdGaussian (v : Fin 3 → E) (hv : Orthonormal ℝ v) :
    (stdGaussian E).map (fun x => (⟪v 0,x⟫, ⟪v 1,x⟫, ⟪v 2,x⟫)) =
      (gaussianReal 0 1).prod ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  have hi := indep_innerFamily v (fun _ _ hij => hv.2 hij)
  have hm (i : Fin 3) : (stdGaussian E).map (fun x => ⟪v i,x⟫) = gaussianReal 0 1 := by
    rw [map_inner_stdGaussian, hv.1 i]
    norm_num
  have hp := hi.indepFun_prodMk (fun _ => by fun_prop) 1 2 0 (by decide) (by decide)
  rw [hp.symm.map_prod_eq_prod_map_map (by fun_prop) (by fun_prop), hm,
    (hi.indepFun (by decide : (1:Fin 3) ≠ 2)).map_prod_eq_prod_map_map
      (by fun_prop) (by fun_prop), hm, hm]


-- @@ L90-99 verbatim
lemma lintegral_orthonormal_triple (v : Fin 3 → E) (hv : Orthonormal ℝ v)
    (f : ℝ × ℝ × ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f (⟪v 0,x⟫,⟪v 1,x⟫,⟪v 2,x⟫) ∂stdGaussian E =
      ∫⁻ s : ℝ, (∫⁻ u : ℝ, (∫⁻ w : ℝ, f (s,u,w) ∂gaussianReal 0 1)
        ∂gaussianReal 0 1) ∂gaussianReal 0 1 := by
  rw [← lintegral_map hf (by fun_prop), map_orthonormal_triple_stdGaussian v hv,
    lintegral_prod _ hf.aemeasurable]
  apply lintegral_congr
  intro s
  exact lintegral_prod _ (hf.comp (measurable_const.prodMk measurable_id)).aemeasurable


-- @@ L101-101 verbatim
end TripleLaw

-- @@ L102-102 verbatim
end GaussianPropeller.Analytic


-- @@ L104-104 verbatim
end OAI
