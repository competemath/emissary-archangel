import OAI.MathematicalPhysics.CriticalSK.SphereSaddle


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
open scoped BigOperators Topology NNReal ENNReal


-- @@ L9-9 verbatim
open MeasureTheory ProbabilityTheory


-- @@ L11-11 verbatim
open scoped ENNReal NNReal


-- @@ L13-13 verbatim
open scoped BigOperators InnerProductSpace


-- @@ L15-15 verbatim
open Module


-- @@ L17-17 verbatim
open scoped BigOperators ENNReal NNReal Real Topology


-- @@ L19-19 verbatim
open MeasureTheory ProbabilityTheory Filter


-- @@ L21-21 verbatim
open scoped BigOperators NNReal


-- @@ L23-23 verbatim
open scoped BigOperators


-- @@ L25-25 verbatim
open Matrix Polynomial


-- @@ L27-27 verbatim
open scoped BigOperators Topology


-- @@ L29-29 verbatim
open Filter


-- @@ L31-31 verbatim
open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise


-- @@ L33-33 verbatim
open Set Metric MeasureTheory MeasureTheory.Measure


-- @@ L35-35 verbatim
open scoped ENNReal NNReal Topology


-- @@ L37-37 verbatim
open MeasureTheory MeasureTheory.Measure Set Metric


-- @@ L39-39 verbatim
open scoped BigOperators ENNReal Topology


-- @@ L41-41 verbatim
open Set MeasureTheory


-- @@ L43-43 verbatim
open scoped BigOperators ENNReal


-- @@ L45-45 verbatim
open MeasureTheory


-- @@ L47-47 verbatim
open Finset Real


-- @@ L49-49 verbatim
open Finset Real Filter


-- @@ L51-51 verbatim
open scoped Topology


-- @@ L53-53 verbatim
open MeasureTheory Filter Set Real


-- @@ L55-55 verbatim
open scoped ENNReal NNReal BigOperators


-- @@ L57-57 verbatim
open scoped NNReal ENNReal BigOperators


-- @@ L59-59 verbatim
open scoped NNReal ENNReal


-- @@ L61-61 verbatim
open ProbabilityTheory


-- @@ L63-63 verbatim
open Metric Set MeasureTheory

-- @@ L64-64 verbatim
open scoped ENNReal Pointwise

-- @@ L65-65 verbatim
namespace CriticalSK


-- @@ L67-67 verbatim
section


-- @@ L69-69 verbatim
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]


-- @@ L71-74 verbatim
omit [Nonempty ι] in
lemma sphereInner_rotation (U : Matrix.orthogonalGroup ι ℝ) (x y : unitSphere ι) :
    inner ℝ (orthogonalSphere U x).val (orthogonalSphere U y).val = inner ℝ x.val y.val :=
  (orthogonalIsometry U).inner_map_map x.val y.val


-- @@ L76-91 verbatim
omit [Nonempty ι] in
lemma spherePairEnergy_haar (lam : ι → ℝ) {u v : EuclideanSpace ℝ ι} {r : ℝ}
    (hu : ‖u‖ = r) (hv : ‖v‖ = r) (horth : inner ℝ u v = 0)
    (p : unitSphere ι × unitSphere ι) :
    (∫ U, spherePairEnergy lam r (orthogonalSphere U p.1, orthogonalSphere U p.2)
      ∂orthogonalHaar ι) = pairMoment lam u v (inner ℝ p.1.val p.2.val) := by
  have hr : 0 ≤ r := hu ▸ norm_nonneg u
  have hnorm (x : unitSphere ι) : ‖r • x.val‖ = r := by
    rw [norm_smul,Real.norm_of_nonneg hr,mem_sphere_zero_iff_norm.mp x.property,mul_one]
  have hxy : inner ℝ (r • p.1.val) (r • p.2.val) = inner ℝ p.1.val p.2.val * r^2 := by
    rw [real_inner_smul_left,real_inner_smul_right]; ring
  rw [← pair_energy_orbit lam (hnorm p.1) (hnorm p.2) hu hv horth
    (sphere_inner_abs_le_one p.1 p.2) hxy]
  apply integral_congr_ae
  filter_upwards [] with U
  simp only [spherePairEnergy,orthogonalSphere,sphereMap,map_smul]


-- @@ L93-111 verbatim
lemma sphereOverlap_weighted_pair (lam : ι → ℝ) {u v : EuclideanSpace ℝ ι} {r : ℝ}
    (hu : ‖u‖ = r) (hv : ‖v‖ = r) (horth : inner ℝ u v = 0)
    (g : ℝ → ℝ) (hg : Continuous g) :
    (∫ q, g q*pairMoment lam u v q ∂sphereOverlapLaw ι) =
      ∫ p : unitSphere ι × unitSphere ι,
        g (inner ℝ p.1.val p.2.val)*spherePairEnergy lam r p ∂(sphereUniform.prod sphereUniform) := by
  have hc : Continuous (fun p : unitSphere ι × unitSphere ι => inner ℝ p.1.val p.2.val) :=
    (continuous_subtype_val.comp continuous_fst).inner (continuous_subtype_val.comp continuous_snd)
  rw [sphereOverlapLaw,integral_map hc.measurable.aemeasurable
    (show AEStronglyMeasurable (fun q => g q * pairMoment lam u v q) _ from
      (hg.mul (pairMoment_continuous lam u v)).aestronglyMeasurable)]
  have hf : Continuous (fun p : unitSphere ι × unitSphere ι =>
      g (inner ℝ p.1.val p.2.val)*spherePairEnergy lam r p) :=
    (hg.comp hc).mul (spherePairEnergy_continuous lam r)
  rw [← spherePair_haar_average _ hf]
  apply integral_congr_ae
  filter_upwards [] with p
  simp only [sphereInner_rotation]
  rw [integral_const_mul,spherePairEnergy_haar lam hu hv horth]


-- @@ L113-120 verbatim
omit [DecidableEq ι] in
lemma sphereTilted_uniform_integral (lam : ι → ℝ) (a r : ℝ) (F : unitSphere ι → ℝ) :
    (∫ u, F u ∂sphereTilted lam a r) =
      (∫ u, Real.exp (a/2*diagonalEnergy lam (r • u.val))*F u ∂sphereUniform) /
        spherePartition lam a r := by
  rw [sphereTilted_integral,sphereUniform_integral,spherePartition,sphereAverage,sphereAverage]
  have ha := ne_of_gt (sphereArea_pos (ι := ι))
  field_simp [ha]


-- @@ L122-139 verbatim
omit [DecidableEq ι] in
lemma sphereTilted_pair_integral (lam : ι → ℝ) (r : ℝ)
    (F : unitSphere ι × unitSphere ι → ℝ) (hF : Continuous F) :
    (∫ p, F p ∂((sphereTilted lam 1 r).prod (sphereTilted lam 1 r))) =
      (∫ p, spherePairEnergy lam r p*F p ∂(sphereUniform.prod sphereUniform)) /
        spherePartition lam 1 r^2 := by
  have hi : Integrable F ((sphereTilted lam 1 r).prod (sphereTilted lam 1 r)) := by
    simpa only [integrableOn_univ] using hF.continuousOn.integrableOn_compact isCompact_univ
  have hi' : Integrable (fun p => spherePairEnergy lam r p*F p)
      (sphereUniform.prod sphereUniform) := by
    have hc : Continuous (fun p : unitSphere ι × unitSphere ι => spherePairEnergy lam r p * F p) :=
      (spherePairEnergy_continuous lam r).mul hF
    simpa only [integrableOn_univ] using hc.continuousOn.integrableOn_compact isCompact_univ
  rw [integral_prod _ hi,integral_prod _ hi']
  simp_rw [sphereTilted_uniform_integral]
  simp_rw [spherePairEnergy_factor,mul_assoc,integral_const_mul]
  simp_rw [← mul_div_assoc,integral_div]
  rw [div_div,← pow_two]


-- @@ L141-141 verbatim
end


-- @@ L143-143 verbatim
section


-- @@ L145-145 verbatim
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


-- @@ L147-149 verbatim
def coordinateReflection (i : ι) : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun j =>
    if j=i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)


-- @@ L151-155 verbatim
lemma coordinateReflection_apply (i j : ι) (x : EuclideanSpace ℝ ι) :
    coordinateReflection i x j = if j=i then -x j else x j := by
  classical
  simp only [coordinateReflection, LinearIsometryEquiv.piLpCongrRight_apply, PiLp.toLp_apply]
  split_ifs <;> rfl


-- @@ L157-163 verbatim
lemma coordinateReflection_energy (lam : ι → ℝ) (i : ι) (x : EuclideanSpace ℝ ι) :
    diagonalEnergy lam (coordinateReflection i x) = diagonalEnergy lam x := by
  unfold diagonalEnergy
  apply Finset.sum_congr rfl
  intro j _
  rw [coordinateReflection_apply]
  split_ifs <;> ring


-- @@ L165-171 verbatim
omit [DecidableEq ι] in
lemma sphereMap_measurableEmbedding (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) :
    MeasurableEmbedding (sphereMap U) := by
  apply (sphereMap_continuous U).measurableEmbedding
  intro u w h
  apply Subtype.ext
  exact U.injective (congrArg Subtype.val h)


-- @@ L173-173 verbatim
variable [Nonempty ι]


-- @@ L175-193 verbatim
lemma sphereTilted_coordinate_cross (lam : ι → ℝ) (a r : ℝ) (i j : ι) (hij : i ≠ j) :
    (∫ u : unitSphere ι, ((r • u.val) i) * ((r • u.val) j) ∂sphereTilted lam a r) = 0 := by
  rw [sphereTilted_integral]
  suffices hn : (∫ u : unitSphere ι, Real.exp (a/2*diagonalEnergy lam (r • u.val)) *
      ((r • u.val) i * (r • u.val) j) ∂(volume : Measure (EuclideanSpace ℝ ι)).toSphere) = 0 by
    rw [hn, zero_div]
  let F := fun u : unitSphere ι => Real.exp (a/2*diagonalEnergy lam (r • u.val)) *
      ((r • u.val) i * (r • u.val) j)
  have he (u : unitSphere ι) : F (sphereMap (coordinateReflection i) u) = -F u := by
    dsimp [F, sphereMap]
    rw [← (coordinateReflection i).map_smul, coordinateReflection_energy]
    simp only [coordinateReflection_apply]
    simp only [ite_eq_left, ite_eq_right hij.symm]
    ring
  have hi := (sphereMap_preserving (coordinateReflection i)).integral_comp
    (sphereMap_measurableEmbedding _) F
  simp_rw [he, integral_neg] at hi
  change (∫ u, F u ∂(volume : Measure (EuclideanSpace ℝ ι)).toSphere) = 0
  linarith only [hi]


-- @@ L195-195 verbatim
end


-- @@ L197-197 verbatim
section


-- @@ L199-210 verbatim
lemma gaussianPairPrefactor_antitone {a b c d : ℝ≥0} (ha : a ≠ 0) (hb : b ≠ 0)
    (hac : a ≤ c) (hbd : b ≤ d) :
    gaussianPairPrefactor c d ≤ gaussianPairPrefactor a b := by
  unfold gaussianPairPrefactor
  have ha' : 0 < (a:ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ha)
  have hb' : 0 < (b:ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hb)
  apply inv_anti₀ (by positivity)
  apply mul_le_mul
  · exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr hac) (by positivity))
  · exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr hbd) (by positivity))
  · positivity
  · positivity


-- @@ L212-212 verbatim
variable {n : ℕ}


-- @@ L214-240 verbatim
lemma gaussianSquareCoordinateDensity_upper_all (v : Fin (n+2) → ℝ≥0) (hv : ∀ i, v i ≠ 0)
    (i : Fin (n+2)) {s : ℝ} (hs : 0 < s) :
    gaussianSquareCoordinateDensity v i s ≤
      8*(v i:ℝ)*Real.pi*gaussianPairPrefactor (v 0) (v 1) := by
  let v' := Function.update v i (2*v i)
  have hv' : ∀ j, v' j ≠ 0 := by
    intro j
    by_cases hj : j=i
    · subst j
      simpa only [v', Function.update_self] using mul_ne_zero (by norm_num : (2:ℝ≥0) ≠ 0) (hv i)
    · simpa only [v', Function.update_of_ne hj] using hv j
  have hvle : ∀ j, v j ≤ v' j := by
    intro j
    by_cases hj : j=i
    · subst j
      simp only [v', Function.update_self]
      exact le_mul_of_one_le_left (by positivity) (by norm_num)
    · simp only [v', Function.update_of_ne hj, le_refl]
  have hp := gaussianPairPrefactor_antitone (hv 0) (hv 1) (hvle 0) (hvle 1)
  calc
    _ ≤ 8*(v i:ℝ)*diagonalSquareDensity v' s :=
      gaussianSquareCoordinateDensity_le_double v i (hv i) hs
    _ ≤ 8*(v i:ℝ)*(Real.pi*gaussianPairPrefactor (v' 0) (v' 1)) :=
      mul_le_mul_of_nonneg_left (diagonalSquareDensity_upper v' hv' hs) (by positivity)
    _ ≤ 8*(v i:ℝ)*(Real.pi*gaussianPairPrefactor (v 0) (v 1)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp Real.pi_pos.le) (by positivity)
    _ = _ := by ring


-- @@ L242-266 verbatim
lemma sphereTilted_coordinate_sq_upper_all (lam : Fin (n+2) → ℝ) (a z : ℝ)
    (v : Fin (n+2) → ℝ≥0) (hv : ∀ i, v i ≠ 0)
    (hq : ∀ i, (v i:ℝ)⁻¹ = z-a*lam i)
    {s m d : ℝ} (hs : 0 < s) (hm : 0 < m) (hm0 : m ≤ v 0) (hm1 : m ≤ v 1)
    (hd : 0 < d) (hmean : (∑ j : Fin n, (v j.succ.succ : ℝ)) = s-d)
    (hvar : 128*(∑ j : Fin n, (v j.succ.succ : ℝ)^2) ≤ d^2)
    (i : Fin (n+2)) :
    (∫ u : unitSphere (Fin (n+2)), ((Real.sqrt s • u.val) i)^2
      ∂sphereTilted lam a (Real.sqrt s)) ≤ 16*(v i:ℝ)*Real.exp (d/m) := by
  rw [sphereTilted_coordinate_sq hv hq hs]
  have hl := diagonalSquareDensity_lower v hv hs hm hm0 hm1 hd hmean hvar
  have hp : 0 < diagonalSquareDensity v s :=
    (div_pos (mul_pos (mul_pos Real.pi_pos (gaussianPairPrefactor_pos (hv 0) (hv 1)))
      (Real.exp_pos _)) (by norm_num)).trans_le hl
  apply (div_le_iff₀ hp).mpr
  apply (gaussianSquareCoordinateDensity_upper_all v hv i hs).trans
  apply le_trans _ (mul_le_mul_of_nonneg_left hl (show 0 ≤ 16*(v i:ℝ)*Real.exp (d/m) by positivity))
  have he : Real.exp (d/m) * Real.exp (-d/m) = 1 := by
    rw [← Real.exp_add, show d/m + -d/m = 0 by ring, Real.exp_zero]
  apply le_of_eq
  symm
  calc
    _ = (8*(v i:ℝ)*Real.pi*gaussianPairPrefactor (v 0) (v 1)) *
        (Real.exp (d/m) * Real.exp (-d/m)) := by ring
    _ = _ := by rw [he, mul_one]


-- @@ L268-268 verbatim
end


-- @@ L270-270 verbatim
section


-- @@ L272-272 verbatim
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]


-- @@ L274-277 verbatim
omit [DecidableEq ι] in
lemma sphereTilted_continuous_integrable (lam : ι → ℝ) (a r : ℝ) {f : unitSphere ι → ℝ}
    (hf : Continuous f) : Integrable f (sphereTilted lam a r) := by
  simpa only [integrableOn_univ] using hf.continuousOn.integrableOn_compact isCompact_univ


-- @@ L279-300 verbatim
lemma sphereTilted_linear_square (lam : ι → ℝ) (a r : ℝ) (c : ι → ℝ) :
    (∫ u : unitSphere ι, (∑ i, c i * (r • u.val) i)^2 ∂sphereTilted lam a r) =
      ∑ i, c i^2 * (∫ u : unitSphere ι, ((r • u.val) i)^2 ∂sphereTilted lam a r) := by
  have hh (u : unitSphere ι) : (∑ i, c i*(r • u.val) i)^2 =
      ∑ i, ∑ j, c i*c j*((r • u.val) i*(r • u.val) j) := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hh]
  rw [integral_finsetSum _ (fun i _ => sphereTilted_continuous_integrable lam a r (by fun_prop))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => sphereTilted_continuous_integrable lam a r (by fun_prop))]
  simp_rw [integral_const_mul]
  rw [Finset.sum_eq_single i]
  · simp only [pow_two]
  · intro j _ hji
    rw [sphereTilted_coordinate_cross lam a r i j hji.symm, mul_zero]
  · simp


-- @@ L302-310 verbatim
lemma sphereTilted_linear_square_le (lam : ι → ℝ) (a r : ℝ) (C : ℝ)
    (hC : ∀ i, (∫ u : unitSphere ι, ((r • u.val) i)^2 ∂sphereTilted lam a r) ≤ C)
    (c : ι → ℝ) :
    (∫ u : unitSphere ι, (∑ i, c i*(r • u.val) i)^2 ∂sphereTilted lam a r) ≤
      C*(∑ i, c i^2) := by
  rw [sphereTilted_linear_square, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  simpa only [mul_comm C] using mul_le_mul_of_nonneg_left (hC i) (sq_nonneg (c i))


-- @@ L312-312 verbatim
end


-- @@ L314-314 verbatim
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]


-- @@ L316-331 verbatim
lemma sphereTilted_overlap_moment (lam : ι → ℝ) (a r : ℝ) :
    (∫ p : unitSphere ι × unitSphere ι,
      (inner ℝ (r • p.1.val) (r • p.2.val))^2
      ∂((sphereTilted lam a r).prod (sphereTilted lam a r))) =
      ∑ i, (∫ u : unitSphere ι, ((r • u.val) i)^2 ∂sphereTilted lam a r)^2 := by
  have hc : Continuous (fun p : unitSphere ι × unitSphere ι =>
      (inner ℝ (r • p.1.val) (r • p.2.val))^2) := by fun_prop
  have hi : Integrable (fun p : unitSphere ι × unitSphere ι =>
      (inner ℝ (r • p.1.val) (r • p.2.val))^2)
      ((sphereTilted lam a r).prod (sphereTilted lam a r)) := by
    simpa only [integrableOn_univ] using hc.continuousOn.integrableOn_compact isCompact_univ
  rw [integral_prod _ hi]
  simp_rw [EuclideanSpace.inner_eq_star_dotProduct,star_trivial,dotProduct,mul_comm]
  simp_rw [sphereTilted_linear_square]
  rw [integral_finsetSum _ (fun i _ => sphereTilted_continuous_integrable lam a r (by fun_prop))]
  simp_rw [integral_mul_const,pow_two]


-- @@ L333-342 verbatim
lemma sphereTilted_overlap_bound (lam : ι → ℝ) (a r C : ℝ) (v : ι → ℝ)
    (hm : ∀ i, (∫ u : unitSphere ι, ((r • u.val) i)^2 ∂sphereTilted lam a r) ≤ C*v i) :
    (∫ p : unitSphere ι × unitSphere ι,
      (inner ℝ (r • p.1.val) (r • p.2.val))^2
      ∂((sphereTilted lam a r).prod (sphereTilted lam a r))) ≤ C^2*(∑ i, v i^2) := by
  rw [sphereTilted_overlap_moment,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  simpa only [mul_pow] using pow_le_pow_left₀
    (integral_nonneg (fun _ => sq_nonneg _)) (hm i) 2


-- @@ L344-354 verbatim
lemma sphereOverlap_weighted_tilted (lam : ι → ℝ) {u v : EuclideanSpace ℝ ι} {r : ℝ}
    (hu : ‖u‖ = r) (hv : ‖v‖ = r) (horth : inner ℝ u v = 0)
    (g : ℝ → ℝ) (hg : Continuous g) :
    (∫ q, g q*pairMoment lam u v q ∂sphereOverlapLaw ι) / spherePartition lam 1 r^2 =
      ∫ p : unitSphere ι × unitSphere ι, g (inner ℝ p.1.val p.2.val)
        ∂((sphereTilted lam 1 r).prod (sphereTilted lam 1 r)) := by
  rw [sphereOverlap_weighted_pair lam hu hv horth g hg]
  have hc : Continuous (fun p : unitSphere ι × unitSphere ι => g (inner ℝ p.1.val p.2.val)) :=
    hg.comp ((continuous_subtype_val.comp continuous_fst).inner (continuous_subtype_val.comp continuous_snd))
  rw [sphereTilted_pair_integral lam r _ hc]
  simp only [mul_comm]


-- @@ L356-363 verbatim
lemma sphereOverlap_square_moment (lam : ι → ℝ) {u v : EuclideanSpace ℝ ι} {r : ℝ}
    (hr : 0 < r) (hu : ‖u‖ = r) (hv : ‖v‖ = r) (horth : inner ℝ u v = 0) :
    (∫ q, q^2*pairMoment lam u v q ∂sphereOverlapLaw ι) / spherePartition lam 1 r^2 =
      (∑ i, (∫ x : unitSphere ι, ((r • x.val) i)^2 ∂sphereTilted lam 1 r)^2) / r^4 := by
  rw [sphereOverlap_weighted_tilted lam hu hv horth (fun q => q^2) (by fun_prop),
    ← sphereTilted_overlap_moment]
  simp_rw [real_inner_smul_left,real_inner_smul_right,mul_pow,integral_const_mul]
  field_simp


-- @@ L365-365 verbatim
end CriticalSK


-- @@ L367-367 verbatim
end


-- @@ L369-369 verbatim
end OAI
