import OAI.Geometry.LatticeCovering.PrimeGrids


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
section

-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
noncomputable section

-- @@ L9-9 verbatim
open MeasureTheory Filter Set

-- @@ L10-10 verbatim
open scoped Topology

-- @@ L11-11 verbatim
noncomputable section

-- @@ L12-12 verbatim
open MeasureTheory Filter Set

-- @@ L13-13 verbatim
open scoped Topology ENNReal

-- @@ L14-14 verbatim
noncomputable section

-- @@ L15-15 verbatim
noncomputable section

-- @@ L16-16 verbatim
noncomputable section

-- @@ L17-17 verbatim
noncomputable section

-- @@ L18-18 verbatim
noncomputable section

-- @@ L19-19 verbatim
noncomputable section

-- @@ L20-20 verbatim
noncomputable section

-- @@ L21-21 verbatim
noncomputable section

-- @@ L22-22 verbatim
noncomputable section

-- @@ L23-23 verbatim
noncomputable section

-- @@ L24-24 verbatim
noncomputable section

-- @@ L25-25 verbatim
noncomputable section

-- @@ L26-26 verbatim
noncomputable section

-- @@ L27-27 verbatim
noncomputable section

-- @@ L28-28 verbatim
noncomputable section

-- @@ L29-29 verbatim
noncomputable section


-- @@ L31-31 verbatim
namespace SingleLatticeCovering.SimplexYoung

-- @@ L32-32 verbatim
open MeasureTheory

-- @@ L33-33 verbatim
open scoped BigOperators


-- @@ L35-39 verbatim
lemma affineCircuitVolumeSum_le_rational {r d : ℕ} (J : Set (Fin d → ℝ)) :
    affineCircuitVolumeSum (r:=r) J ≤ rationalCircuitVolumeSum (r:=r) J := by
  apply ENNReal.tsum_le_tsum
  intro a
  split_ifs <;> simp


-- @@ L41-54 verbatim
lemma affineCircuit_real_term {r d : ℕ} (hr : 0 < r) (hd : 2*(r+1) ≤ d)
    {J : Set (Fin d → ℝ)} (hJ : IsCompact J) :
    (affineCircuitVolumeSum (r:=r) J).toReal / (r.factorial:ℝ) ≤
      4*circuitTerm d (volume.real J) r := by
  have hb := (affineCircuitVolumeSum_le_rational (r:=r) J).trans
    (rationalCircuitVolumeSum_le hr hd hJ)
  have hbr := ENNReal.toReal_mono (by simp) hb
  rw [ENNReal.toReal_ofReal (mul_nonneg
    (mul_nonneg (by positivity) (pow_nonneg (simplexConstant_nonneg r) d))
    (pow_nonneg ENNReal.toReal_nonneg r))] at hbr
  apply (div_le_div_of_nonneg_right hbr (by positivity)).trans_eq
  unfold circuitTerm
  rw [pow_succ,measureReal_def]
  ring


-- @@ L56-67 verbatim
lemma finite_circuitTerm_series_le {d k : ℕ} {V : ℝ}
    (hV : 0 ≤ V) (hVd : V ≤ (d:ℝ)/6) :
    ∑ r ∈ Finset.Icc 3 k, circuitTerm d V r ≤ 4*circuitTerm d V 3 := by
  have hh : (∑ r ∈ Finset.Icc 3 k, ENNReal.ofReal (circuitTerm d V r)) ≤
      ∑' s : ℕ, ENNReal.ofReal (circuitTerm d V (s+3)) := by
    rw [←Finset.Ico_add_one_right_eq_Icc,Finset.sum_Ico_eq_sum_range]
    simpa only [Nat.add_comm] using
      (ENNReal.sum_le_tsum (Finset.range (k+1-3))
        (f:=fun s : ℕ => ENNReal.ofReal (circuitTerm d V (s+3))))
  have hb := hh.trans (tsum_circuitTerm_le hV hVd)
  rw [←ENNReal.ofReal_sum_of_nonneg (fun _ _ => circuitTerm_nonneg _ _ hV)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by norm_num) (circuitTerm_nonneg _ _ hV))).mp hb


-- @@ L69-104 verbatim
lemma rank_two_source {d : ℕ} (hd : 6 ≤ d) {J : Set (Fin d → ℝ)}
    (hJ : IsCompact J) (hVeta : volume.real J ≤ sourceEta d) :
    Real.exp (volume.real J) * ((affineCircuitVolumeSum (r:=2) J).toReal/2) ≤
      128 * Real.exp (-sourceEta d) := by
  have hdR : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hV := measureReal_nonneg (μ:=volume) (s:=J)
  have hVd := hVeta.trans (sourceEta_le_dim (by omega))
  have hpow : (volume.real J)^2 ≤ (d:ℝ)^3 := by
    have hh := pow_le_pow_left₀ hV hVd 2
    have hs : (d:ℝ)^2 ≤ (d:ℝ)^3 := by nlinarith [sq_nonneg (d:ℝ)]
    exact hh.trans hs
  have hb := affineRankTwoCircuitVolumeSum_le hd hJ
  have hbr := ENNReal.toReal_mono (by simp) hb
  rw [ENNReal.toReal_ofReal (mul_nonneg
    (mul_nonneg (by norm_num) (pow_nonneg (simplexConstant_nonneg 3) d)) (sq_nonneg _))] at hbr
  have hs : Real.exp (volume.real J) * ((simplexConstant 3)^d * (volume.real J)^2) ≤
      Real.exp (-sourceEta d) := by
    rw [simplexConstant_three,sharpParallelogramConstant_exp]
    calc
      _ ≤ Real.exp (volume.real J) * (Real.exp (-(d:ℝ)/2*Real.log (27/16:ℝ)) * (d:ℝ)^3) := by gcongr
      _ = Real.exp (volume.real J-(d:ℝ)/2*Real.log (27/16:ℝ)+3*Real.log (d:ℝ)) := by
        have he : (d:ℝ)^3 = Real.exp (3*Real.log (d:ℝ)) := by
          simpa only [Nat.cast_ofNat,Real.exp_log hdR] using (Real.exp_nat_mul (Real.log (d:ℝ)) 3).symm
        rw [he,←Real.exp_add,←Real.exp_add]
        congr 1
        ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hl := Real.log_nonneg hd1
        dsimp [sourceEta] at hVeta ⊢
        linarith
  have hh := mul_le_mul_of_nonneg_left hbr (Real.exp_pos (volume.real J)).le
  change Real.exp (volume.real J) * (affineCircuitVolumeSum (r:=2) J).toReal ≤
    Real.exp (volume.real J) * (256*(simplexConstant 3)^d*(volume.real J)^2) at hh
  nlinarith only [hh,hs]





-- @@ L109-137 verbatim
theorem continuum_circuit_error_source {d k : ℕ} (hk : 2 ≤ k)
    (hd : 2*(k+1) ≤ d) {J : Set (Fin d → ℝ)} (hJ : IsCompact J)
    (hVeta : volume.real J ≤ sourceEta d) :
    Real.exp (volume.real J) * (∑ r ∈ Finset.Icc 2 k,
      (affineCircuitVolumeSum (r:=r) J).toReal/(r.factorial:ℝ)) ≤
        (896/3:ℝ)*Real.exp (-sourceEta d) := by
  classical
  have hV := measureReal_nonneg (μ:=volume) (s:=J)
  have hVd : volume.real J ≤ (d:ℝ)/6 := by
    have hh := hVeta.trans (sourceEta_le_linear d)
    nlinarith [(Nat.cast_nonneg d : (0:ℝ)≤d)]
  have hsum : (∑ r ∈ Finset.Icc 3 k,
      (affineCircuitVolumeSum (r:=r) J).toReal/(r.factorial:ℝ)) ≤
        4*(4*circuitTerm d (volume.real J) 3) := by
    calc
      _ ≤ ∑ r ∈ Finset.Icc 3 k, 4*circuitTerm d (volume.real J) r := by
        apply Finset.sum_le_sum
        intro r hr
        obtain ⟨hr3,hrk⟩ := Finset.mem_Icc.mp hr
        exact affineCircuit_real_term (by omega) (by omega) hJ
      _ = 4*(∑ r ∈ Finset.Icc 3 k, circuitTerm d (volume.real J) r) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (finite_circuitTerm_series_le hV hVd) (by norm_num)
  have hs := circuitTerm_three_source (by omega : 1 ≤ d) hV hVeta
  have htwo := rank_two_source (by omega : 6 ≤ d) hJ hVeta
  have he : Finset.Icc 2 k = insert 2 (Finset.Icc 3 k) := by ext r; simp only [Finset.mem_Icc,Finset.mem_insert]; omega
  rw [he,Finset.sum_insert (by simp),show ((2:ℕ).factorial:ℝ)=2 by norm_num,mul_add]
  have hh := mul_le_mul_of_nonneg_left hsum (Real.exp_pos (volume.real J)).le
  linarith




-- @@ L141-141 verbatim
end SingleLatticeCovering.SimplexYoung


-- @@ L143-143 verbatim
namespace SingleLatticeCovering.ConvexGrid

-- @@ L144-144 verbatim
open MeasureTheory SimplexYoung RogersPreparation



-- @@ L147-169 verbatim
theorem eventually_primeGridVoid_source {d : ℕ} (hd : 270 ≤ d)
    {J : Set (Fin d → ℝ)} (hJ : IsCompact J) (hconv : Convex ℝ J)
    (h0 : 0 ∈ J) (hV : 0 < volume.real J) (hVeta : volume.real J ≤ sourceEta d)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (p : ℕ) [Fact p.Prime], N ≤ p →
      primeGridVoid J hJ p ≤ Real.exp (-volume.real J)+300*Real.exp (-sourceEta d)+ε := by
  have hq : 0 < d/4-1 := by omega
  have hdq : 2*(2*(d/4-1)+1) ≤ d := by omega
  obtain ⟨N,hN⟩ := eventually_primeGridVoid_le hq hdq hJ hconv h0 hV hε
  refine ⟨N,fun p hp hpN => ?_⟩
  have hb := hN p hpN
  have hc := continuum_circuit_error_source (by omega : 2 ≤ 2*(d/4-1)) hdq hJ hVeta
  have hr := poisson_remainder_circuitCutoff hd hV.le hVeta
  have ht := poissonPartial_upper hV.le (2*(d/4-1))
  have heq : poissonPartial (volume.real J) (2*(d/4-1)) =
      ∑ j ∈ Finset.range (2*(d/4-1)+1), (-1:ℝ)^j*(volume.real J)^j/(j.factorial:ℝ) := by
    unfold poissonPartial
    apply Finset.sum_congr rfl
    intro j hj
    rw [show -volume.real J=(-1:ℝ)*volume.real J by ring,mul_pow]
  rw [heq] at ht
  change continuumCircuitError J (2*(d/4-1)) ≤ _ at hc
  linarith [Real.exp_pos (-sourceEta d)]


-- @@ L171-171 verbatim
end SingleLatticeCovering.ConvexGrid









-- @@ L180-180 verbatim
section












-- @@ L192-192 verbatim
section


-- @@ L194-194 verbatim
noncomputable section

-- @@ L195-195 verbatim
namespace SingleLatticeCovering.RogersPreparation

-- @@ L196-196 verbatim
open Horizontal Completion MeasureTheory Set Topology

-- @@ L197-197 verbatim
open scoped ENNReal Pointwise BigOperators


-- @@ L199-201 verbatim
instance lattice_vadd_invariant {m : ℕ} (L : FullLattice m) :
    VAddInvariantMeasure L.module (Fin m → ℝ) volume :=
  inferInstanceAs (VAddInvariantMeasure L.module.toAddSubgroup (Fin m → ℝ) volume)




-- @@ L205-206 verbatim
def periodize {m : ℕ} (L : FullLattice m) (f : (Fin m → ℝ) → ℝ≥0∞)
    (x : Fin m → ℝ) : ℝ≥0∞ := ∑' z : L.module, f (x+z)


-- @@ L208-209 verbatim
def pointCount {m : ℕ} (L : FullLattice m) (J : Set (Fin m → ℝ)) :
    (Fin m → ℝ) → ℝ≥0∞ := periodize L (J.indicator 1)


-- @@ L211-212 verbatim
def cell {m : ℕ} (L : FullLattice m) : Set (Fin m → ℝ) :=
  ZSpan.fundamentalDomain (latticeBasis L.module)


-- @@ L214-216 verbatim
lemma cell_fundamental {m : ℕ} (L : FullLattice m) :
    IsAddFundamentalDomain L.module (cell L) volume :=
  ZLattice.isAddFundamentalDomain (IsZLattice.basis L.module) volume


-- @@ L218-219 verbatim
lemma cell_measurable {m : ℕ} (L : FullLattice m) : MeasurableSet (cell L) :=
  ZSpan.fundamentalDomain_measurableSet _


-- @@ L221-222 verbatim
lemma cell_volume_ne_zero {m : ℕ} (L : FullLattice m) : volume (cell L)≠0 :=
  ZSpan.measure_fundamentalDomain_ne_zero _


-- @@ L224-225 verbatim
lemma cell_volume_ne_top {m : ℕ} (L : FullLattice m) : volume (cell L)≠⊤ :=
  (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne


-- @@ L227-229 verbatim
lemma measurable_periodize {m : ℕ} (L : FullLattice m)
    {f : (Fin m → ℝ) → ℝ≥0∞} (hf : Measurable f) : Measurable (periodize L f) := by
  exact Measurable.tsum (fun z => hf.comp (measurable_id.add measurable_const))



-- @@ L232-246 verbatim
lemma integral_periodize {m : ℕ} (L : FullLattice m)
    {f : (Fin m → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x in cell L, periodize L f x = ∫⁻ x, f x := by
  unfold periodize
  have hm (z : L.module) : Measurable (fun x : Fin m → ℝ => f (x+(z : Fin m → ℝ))) :=
    hf.comp (measurable_id.add measurable_const)
  rw [lintegral_tsum (fun z => (hm z).aemeasurable)]
  convert (cell_fundamental L).lintegral_eq_tsum'' f |>.symm using 1
  congr 1
  funext z
  congr 1
  funext x
  congr 1
  change x+(z : Fin m → ℝ)=(z : Fin m → ℝ)+x
  exact add_comm _ _



-- @@ L249-250 verbatim
def translateLaw {m : ℕ} (L : FullLattice m) : Measure (Fin m → ℝ) :=
  (volume (cell L))⁻¹ • volume.restrict (cell L)


-- @@ L252-256 verbatim
instance translateLaw_probability {m : ℕ} (L : FullLattice m) :
    IsProbabilityMeasure (translateLaw L) where
  measure_univ := by
    simp only [translateLaw,Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul]
    exact ENNReal.inv_mul_cancel (cell_volume_ne_zero L) (cell_volume_ne_top L)


-- @@ L258-266 verbatim
lemma integral_pointCount {m : ℕ} (L : FullLattice m)
    {J : Set (Fin m → ℝ)} (hJ : MeasurableSet J) :
    ∫⁻ x, pointCount L J x ∂translateLaw L =
      volume J / ENNReal.ofReal (ZLattice.covolume L.module) := by
  rw [translateLaw,lintegral_smul_measure,pointCount,
    integral_periodize L (measurable_one.indicator hJ),lintegral_indicator_one hJ]
  have hc := ZLattice.covolume_eq_measure_fundamentalDomain L.module volume (cell_fundamental L)
  rw [hc,measureReal_def,ENNReal.ofReal_toReal (cell_volume_ne_top L)]
  exact mul_comm _ _


-- @@ L268-285 verbatim
lemma pointCount_eq_zero {m : ℕ} (L : FullLattice m) (J : Set (Fin m → ℝ))
    (x : Fin m → ℝ) : pointCount L J x=0 ↔ latticeProjection L.module x ∉
      latticeProjection L.module '' J := by
  classical
  rw [pointCount,periodize,ENNReal.tsum_eq_zero]
  constructor
  · intro h ⟨y,hy,hxy⟩
    have hz : y-x ∈ L.module := (latticeProjection_eq_zero_iff L.module _).mp (by
      rw [map_sub,hxy,sub_self])
    have hh := h ⟨y-x,hz⟩
    have he : x+(y-x)=y := by abel
    simp only [he,Set.indicator_of_mem hy,Pi.one_apply,one_ne_zero] at hh
  · intro hx z
    apply Set.indicator_of_notMem
    intro hz
    apply hx
    refine ⟨x+z,hz,?_⟩
    rw [map_add,(latticeProjection_eq_zero_iff L.module _).mpr z.property,add_zero]




-- @@ L289-289 verbatim
end SingleLatticeCovering.RogersPreparation


-- @@ L291-291 verbatim
end

-- @@ L292-292 verbatim
end


-- @@ L294-294 verbatim
section


-- @@ L296-296 verbatim
noncomputable section

-- @@ L297-297 verbatim
namespace SingleLatticeCovering.RogersPreparation

-- @@ L298-298 verbatim
open Horizontal Completion MeasureTheory Set Topology

-- @@ L299-299 verbatim
open scoped ENNReal Pointwise BigOperators


-- @@ L301-312 verbatim
lemma periodize_periodic {m : ℕ} (L : FullLattice m)
    (f : (Fin m → ℝ) → ℝ≥0∞) (z : L.module) (x : Fin m → ℝ) :
    periodize L f (z+x)=periodize L f x := by
  unfold periodize
  calc
    _ = ∑' w : L.module, f (x+((z+w : L.module) : Fin m → ℝ)) := by
      apply tsum_congr
      intro w
      congr 1
      change (z : Fin m → ℝ)+x+(w : Fin m → ℝ)=x+((z : Fin m → ℝ)+w)
      abel
    _ = _ := (Equiv.addLeft z).tsum_eq (fun w : L.module => f (x+w))


-- @@ L314-323 verbatim
lemma periodize_mul {m : ℕ} (L : FullLattice m)
    (f g : (Fin m → ℝ) → ℝ≥0∞) (x : Fin m → ℝ) :
    periodize L f x*periodize L g x =
      periodize L (fun y => f y*periodize L g y) x := by
  change (∑' z : L.module, f (x+z))*periodize L g x =
    ∑' z : L.module, f (x+z)*periodize L g (x+z)
  rw [←ENNReal.tsum_mul_right]
  apply tsum_congr
  intro z
  rw [add_comm x (z : Fin m → ℝ),periodize_periodic]




-- @@ L327-338 verbatim
lemma integral_periodize_mul {m : ℕ} (L : FullLattice m)
    {f g : (Fin m → ℝ) → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ x in cell L, periodize L f x*periodize L g x =
      ∑' z : L.module, ∫⁻ x, f x*g (x+z) := by
  simp_rw [periodize_mul]
  have hi := integral_periodize L (f := fun y => f y*periodize L g y)
    (hf.mul (measurable_periodize L hg))
  rw [hi]
  simp_rw [periodize,←ENNReal.tsum_mul_left]
  apply lintegral_tsum
  intro z
  exact (hf.mul (hg.comp (measurable_id.add measurable_const))).aemeasurable


-- @@ L340-358 verbatim
lemma pointCount_second_moment {m : ℕ} (L : FullLattice m)
    {J : Set (Fin m → ℝ)} (hJ : MeasurableSet J) :
    ∫⁻ x, pointCount L J x*pointCount L J x ∂translateLaw L =
      (volume (cell L))⁻¹ * ∑' z : L.module,
        volume (J ∩ (fun x : Fin m → ℝ => x+z) ⁻¹' J) := by
  rw [translateLaw,lintegral_smul_measure]
  change (volume (cell L))⁻¹ *
    (∫⁻ x in cell L, periodize L (J.indicator 1) x*periodize L (J.indicator 1) x)=_
  rw [integral_periodize_mul L (measurable_one.indicator hJ) (measurable_one.indicator hJ)]
  congr 1
  apply tsum_congr
  intro z
  have he (x : Fin m → ℝ) :
      J.indicator (1 : (Fin m → ℝ) → ℝ≥0∞) x*J.indicator 1 (x+z)=
      (J ∩ (fun y : Fin m → ℝ => y+z) ⁻¹' J).indicator 1 x := by
    classical
    by_cases hx : x ∈ J <;> by_cases hy : x+(z : Fin m → ℝ)∈J <;> simp [hx,hy]
  simp_rw [he]
  exact lintegral_indicator_one (hJ.inter (hJ.preimage (measurable_id.add measurable_const)))




-- @@ L362-370 verbatim
lemma finite_point_support {m : ℕ} (L : FullLattice m)
    {J : Set (Fin m → ℝ)} (hJ : IsCompact J) (x : Fin m → ℝ) :
    Set.Finite {z : L.module | x+(z : Fin m → ℝ)∈J} := by
  let : DiscreteTopology L.module.toAddSubgroup := L.discrete
  have hc : IsClosed (L.module : Set (Fin m → ℝ)) :=
    L.module.toAddSubgroup.isClosed_of_discreteTopology
  have he : IsClosedEmbedding (fun z : L.module => x+(z : Fin m → ℝ)) :=
    (Homeomorph.addLeft x).isClosedEmbedding.comp (IsClosedEmbedding.subtypeVal hc)
  exact (he.isCompact_preimage hJ).finite_of_discrete




-- @@ L374-374 verbatim
end SingleLatticeCovering.RogersPreparation


-- @@ L376-376 verbatim
end

-- @@ L377-377 verbatim
end


-- @@ L379-379 verbatim
section


-- @@ L381-381 verbatim
noncomputable section

-- @@ L382-382 verbatim
namespace SingleLatticeCovering.RogersPreparation

-- @@ L383-383 verbatim
open Horizontal Completion MeasureTheory Set Topology

-- @@ L384-384 verbatim
open scoped ENNReal Pointwise BigOperators


-- @@ L386-393 verbatim
lemma integral_periodic_shift {m : ℕ} (L : FullLattice m)
    (f : (Fin m → ℝ) → ℝ≥0∞)
    (hf : ∀ (z : L.module) x, f (z+x)=f x) (a : Fin m → ℝ) :
    ∫⁻ x in cell L, f (a+x) = ∫⁻ x in cell L, f x := by
  rw [(measurePreserving_add_left volume a).setLIntegral_comp_emb
    (measurableEmbedding_addLeft a) f (cell L)]
  apply IsAddFundamentalDomain.setLIntegral_eq _ (cell_fundamental L) f hf
  exact (cell_fundamental L).vadd_of_comm a


-- @@ L395-405 verbatim
lemma integral_torus_shift {m : ℕ} (L : FullLattice m)
    (f : Torus m → ℝ≥0∞) (t : Torus m) :
    ∫⁻ x, f (t+latticeProjection L.module x) ∂translateLaw L =
      ∫⁻ x, f (latticeProjection L.module x) ∂translateLaw L := by
  obtain ⟨a,rfl⟩ := latticeProjection_surjective L.module t
  simp only [translateLaw,lintegral_smul_measure]
  congr 1
  simp only [←map_add]
  exact integral_periodic_shift L (fun y => f (latticeProjection L.module y)) (by
    intro z x
    rw [map_add,(latticeProjection_eq_zero_iff L.module _).mpr z.property,zero_add]) a




-- @@ L409-431 verbatim
lemma translateLaw_preserving {m : ℕ} (L : FullLattice m) :
    MeasurePreserving (latticeProjection L.module) (translateLaw L) (torusMeasure m) := by
  let p := latticeProjection L.module
  have hp : Measurable p := p.continuous.measurable
  let ν := (translateLaw L).map p
  have : IsProbabilityMeasure ν := inferInstance
  have hν : ν.IsAddLeftInvariant := by
    constructor
    intro t
    apply Measure.ext_of_lintegral ν
    intro g hg
    have ht : Measurable (fun y : Torus m => t+y) := measurable_const.add measurable_id
    rw [lintegral_map hg ht]
    change (∫⁻ y, g (t+y) ∂(translateLaw L).map p)=∫⁻ y, g y ∂(translateLaw L).map p
    calc
      _ = ∫⁻ x, g (t+p x) ∂translateLaw L := by
        exact lintegral_map (f := fun y => g (t+y)) (g := p) (μ := translateLaw L)
          (hg.comp ht) hp
      _ = ∫⁻ x, g (p x) ∂translateLaw L := integral_torus_shift L g t
      _ = _ := (lintegral_map hg hp).symm
  refine ⟨hp,?_⟩
  have h := Measure.addHaarMeasure_unique ν (⊤ : TopologicalSpace.PositiveCompacts (Torus m))
  simpa only [TopologicalSpace.PositiveCompacts.coe_top,measure_univ,one_smul,torusMeasure] using h


-- @@ L433-442 verbatim
lemma hole_eq_zero_count_probability {m : ℕ} (L : FullLattice m)
    {J : Set (Fin m → ℝ)} (hJ : IsCompact J) :
    L.hole J=translateLaw L {x | pointCount L J x=0} := by
  unfold FullLattice.hole
  have hm : MeasurableSet ((latticeProjection L.module '' J)ᶜ) :=
    (hJ.image (latticeProjection L.module).continuous).measurableSet.compl
  rw [←(translateLaw_preserving L).measure_preimage hm.nullMeasurableSet]
  congr 1
  ext x
  exact (pointCount_eq_zero L J x).symm




-- @@ L446-446 verbatim
end SingleLatticeCovering.RogersPreparation


-- @@ L448-448 verbatim
end

-- @@ L449-449 verbatim
end





-- @@ L454-454 verbatim
noncomputable section

-- @@ L455-455 verbatim
open Module Submodule MeasureTheory

-- @@ L456-456 verbatim
open scoped BigOperators


-- @@ L458-458 verbatim
namespace SingleLatticeCovering.PrimeKernel

-- @@ L459-459 verbatim
variable {ι : Type*} [Fintype ι] [DecidableEq ι]



-- @@ L462-463 verbatim
def tailForm (i : ι) (a : ι → ℤ) (x : ι → ℝ) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, (a j : ℝ)*x j


-- @@ L465-470 verbatim
lemma tailForm_update (i : ι) (a : ι → ℤ) (x : ι → ℝ) (r : ℝ) :
    tailForm i a (Function.update x i r) = tailForm i a x := by
  unfold tailForm
  apply Finset.sum_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]


-- @@ L472-474 verbatim
lemma tailForm_add (i : ι) (a : ι → ℤ) (x y : ι → ℝ) :
    tailForm i a (x+y) = tailForm i a x+tailForm i a y := by
  simp [tailForm, mul_add, Finset.sum_add_distrib]

-- @@ L475-477 verbatim
lemma tailForm_smul (i : ι) (a : ι → ℤ) (r : ℝ) (x : ι → ℝ) :
    tailForm i a (r • x) = r*tailForm i a x := by
  simp only [tailForm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]



-- @@ L480-515 verbatim
def coordinates (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) :
    (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) where
  toFun x := Function.update x i ((x i+tailForm i a x)/p)
  invFun x := Function.update x i ((p : ℝ)*x i-tailForm i a x)
  left_inv x := by
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
    ext j
    by_cases hji : j=i
    · subst j
      simp only [Function.update_self,tailForm_update]
      field_simp [hpR]
      ring
    · simp [Function.update_of_ne hji]
  right_inv x := by
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
    ext j
    by_cases hji : j=i
    · subst j
      simp only [Function.update_self,tailForm_update]
      field_simp [hpR]
      ring
    · simp [Function.update_of_ne hji]
  map_add' x y := by
    ext j
    by_cases hji : j=i
    · subst j
      simp only [Function.update_self,Pi.add_apply,tailForm_add]
      ring
    · simp [Function.update_of_ne hji]
  map_smul' r x := by
    ext j
    by_cases hji : j=i
    · subst j
      simp only [Function.update_self,Pi.smul_apply,smul_eq_mul,tailForm_smul,RingHom.id_apply]
      ring
    · simp [Function.update_of_ne hji]


-- @@ L517-518 verbatim
def basis (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) : Basis ι ℝ (ι → ℝ) :=
  Basis.ofEquivFun (coordinates p hp i a)


-- @@ L520-523 verbatim
lemma basis_repr (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) (x : ι → ℝ) (j : ι) :
    (basis p hp i a).repr x j =
      Function.update x i ((x i+tailForm i a x)/p) j := by
  simp [basis, Basis.ofEquivFun_repr_apply,coordinates]


-- @@ L525-536 verbatim
lemma basis_apply (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) (j k : ι) :
    basis p hp i a j k =
      if k=i then (if j=i then (p : ℝ) else -(a j : ℝ))
      else if j=k then 1 else 0 := by
  simp only [basis, Basis.coe_ofEquivFun,coordinates,LinearEquiv.coe_symm_mk]
  by_cases hki : k=i
  · subst k
    by_cases hji : j=i
    · subst j
      simp [tailForm,Function.update_self,Pi.single_apply,Finset.mem_erase]
    · simp [tailForm,Function.update_self,Pi.single_apply,hji,Finset.mem_erase,eq_comm]
  · simp [Pi.single_apply,hki,eq_comm]


-- @@ L538-539 verbatim
def lattice (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) : Submodule ℤ (ι → ℝ) :=
  Submodule.span ℤ (Set.range (basis p hp i a))


-- @@ L541-543 verbatim
instance lattice_discrete (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) :
    DiscreteTopology (lattice p hp i a) := inferInstanceAs
      (DiscreteTopology (Submodule.span ℤ (Set.range (basis p hp i a))))

-- @@ L544-546 verbatim
instance lattice_full (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) :
    IsZLattice ℝ (lattice p hp i a) := inferInstanceAs
      (IsZLattice ℝ (Submodule.span ℤ (Set.range (basis p hp i a))))


-- @@ L548-565 verbatim
lemma covolume_lattice (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) :
    ZLattice.covolume (lattice p hp i a) = p := by
  change ZLattice.covolume (span ℤ (Set.range (basis p hp i a))) = _
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
    (ZSpan.isAddFundamentalDomain (basis p hp i a) volume),
    ZSpan.volume_real_fundamentalDomain]
  let v : ι → ℝ := fun k => if k=i then p else -(a k : ℝ)
  have he : Matrix.of (basis p hp i a) = ((1 : Matrix ι ι ℝ).updateRow i v).transpose := by
    ext j k
    rw [Matrix.of_apply,basis_apply]
    by_cases hki : k=i
    · subst k; simp [v]
    · simp [Matrix.transpose_apply,Matrix.one_apply,hki,eq_comm]
  have hs : (∑ j, v j • (1 : Matrix ι ι ℝ) j) = v := by
    ext k
    simp [Matrix.one_apply,Pi.smul_apply,smul_eq_mul]
  rw [he,Matrix.det_transpose,←hs,Matrix.det_updateRow_sum]
  simp [v,abs_of_pos (show (0 : ℝ)<p by exact_mod_cast hp)]



-- @@ L568-592 verbatim
lemma integer_mem_iff_dvd (p : ℕ) (hp : 0 < p) (i : ι) (a z : ι → ℤ) :
    (fun j => (z j : ℝ)) ∈ lattice p hp i a ↔
      (p : ℤ) ∣ z i+∑ j ∈ Finset.univ.erase i, a j*z j := by
  rw [lattice,(basis p hp i a).mem_span_iff_repr_mem ℤ]
  simp only [basis_repr]
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  constructor
  · intro h
    obtain ⟨q,hq⟩ := h i
    have hqi : (q : ℝ) = ((z i : ℝ)+tailForm i a (fun j => (z j : ℝ)))/p := by
      simpa only [Function.update_self, algebraMap_int_eq,Int.coe_castRingHom] using hq
    refine ⟨q,?_⟩
    have he := (eq_div_iff hpR).mp hqi
    exact_mod_cast (show (z i : ℝ)+∑ j ∈ Finset.univ.erase i,
      (a j : ℝ)*(z j : ℝ)=(p : ℝ)*q by simpa [tailForm,mul_comm] using he.symm)
  · rintro ⟨q,hq⟩ j
    by_cases hji : j=i
    · subst j
      refine ⟨q,?_⟩
      simp only [Function.update_self]
      apply (eq_div_iff hpR).mpr
      have hr : (z i : ℝ)+∑ j ∈ Finset.univ.erase i,
          (a j : ℝ)*(z j : ℝ)=(p : ℝ)*q := by exact_mod_cast hq
      simpa [tailForm,mul_comm] using hr.symm
    · exact ⟨z j,by simp [Function.update_of_ne hji]⟩



-- @@ L595-611 verbatim
lemma exists_integer_of_mem (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ)
    {x : ι → ℝ} (hx : x ∈ lattice p hp i a) :
    ∃ z : ι → ℤ, (fun j => (z j : ℝ)) = x := by
  have h := ((basis p hp i a).mem_span_iff_repr_mem ℤ x).mp hx
  choose q hq using h
  have hc : coordinates p hp i a x = (fun j => (q j : ℝ)) := by
    ext j
    simpa only [basis,Basis.ofEquivFun_repr_apply,algebraMap_int_eq,Int.coe_castRingHom] using (hq j).symm
  let z : ι → ℤ := Function.update q i ((p : ℤ)*q i-∑ j ∈ Finset.univ.erase i, a j*q j)
  refine ⟨z,?_⟩
  have he : (fun j => (z j : ℝ)) = (coordinates p hp i a).symm (fun j => (q j : ℝ)) := by
    ext j
    by_cases hji : j=i
    · subst j
      simp [z,coordinates,tailForm]
    · simp [z,coordinates,Function.update_of_ne hji]
  rw [he,←hc,LinearEquiv.symm_apply_apply]


-- @@ L613-621 verbatim
lemma mem_lattice_iff (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) (x : ι → ℝ) :
    x ∈ lattice p hp i a ↔ ∃ z : ι → ℤ, (fun j => (z j : ℝ)) = x ∧
      (p : ℤ) ∣ z i+∑ j ∈ Finset.univ.erase i, a j*z j := by
  constructor
  · intro hx
    obtain ⟨z,hz⟩ := exists_integer_of_mem p hp i a hx
    exact ⟨z,hz,(integer_mem_iff_dvd p hp i a z).mp (hz.symm ▸ hx)⟩
  · rintro ⟨z,rfl,hz⟩
    exact (integer_mem_iff_dvd p hp i a z).mpr hz


-- @@ L623-627 verbatim
lemma integer_mem_iff_congruence (p : ℕ) (hp : 0 < p) (i : ι) (a z : ι → ℤ) :
    (fun j => (z j : ℝ)) ∈ lattice p hp i a ↔
      (z i : ZMod p)+∑ j ∈ Finset.univ.erase i, (a j : ZMod p)*(z j : ZMod p)=0 := by
  rw [integer_mem_iff_dvd,←ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Int.cast_add,Int.cast_sum,Int.cast_mul]






-- @@ L633-633 verbatim
end SingleLatticeCovering.PrimeKernel





-- @@ L638-638 verbatim
end

-- @@ L639-639 verbatim
end

-- @@ L640-640 verbatim
end

-- @@ L641-641 verbatim
end

-- @@ L642-642 verbatim
end

-- @@ L643-643 verbatim
end

-- @@ L644-644 verbatim
end

-- @@ L645-645 verbatim
end

-- @@ L646-646 verbatim
end

-- @@ L647-647 verbatim
end

-- @@ L648-648 verbatim
end

-- @@ L649-649 verbatim
end

-- @@ L650-650 verbatim
end

-- @@ L651-651 verbatim
end

-- @@ L652-652 verbatim
end

-- @@ L653-653 verbatim
end

-- @@ L654-654 verbatim
end

-- @@ L655-655 verbatim
end

-- @@ L656-656 verbatim
end

-- @@ L657-657 verbatim
end

-- @@ L658-658 verbatim
end

-- @@ L659-659 verbatim
end

-- @@ L660-660 verbatim
end


-- @@ L662-662 verbatim
end OAI
