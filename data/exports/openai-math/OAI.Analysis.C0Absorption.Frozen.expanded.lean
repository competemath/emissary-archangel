import OAI.Analysis.C0Absorption.Correction


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
open Set Filter Topology

-- @@ L6-6 verbatim
open scoped NNReal BigOperators ZeroAtInfty

-- @@ L7-7 verbatim
open NormedSpace


-- @@ L9-9 verbatim
namespace C0Absorption

-- @@ L10-10 verbatim
noncomputable section

-- @@ L11-11 verbatim
open Set Filter Topology

-- @@ L12-12 verbatim
open scoped NNReal BigOperators ZeroAtInfty


-- @@ L14-19 verbatim
structure FrozenWeights where
  vector : (lev : Level) → Block lev → ℝ
  row : (lev : Level) → Block lev → ℝ
  vector_bound : ∀ lev b, |vector lev b|≤1
  row_bound : ∀ lev, (∑ b : Block lev,|row lev b|)≤2
  pairing : ∀ lev, (∑ b : Block lev,row lev b*vector lev b)=1


-- @@ L21-26 verbatim
def stateWeights (s : C0Ball) : FrozenWeights where
  vector := fun lev => blockVector lev s
  row := fun lev => blockRow lev s
  vector_bound := fun lev b => by rw [abs_of_nonneg (blockVector_nonneg _ _ _)]; exact blockVector_le_one _ _ _
  row_bound := fun lev => by simp only [abs_of_nonneg (blockRow_nonneg _ _ _)]; exact blockRow_sum lev s
  pairing := fun lev => blockRow_vector lev s


-- @@ L28-28 verbatim
def blockInput (lev : Level) (x : C0) (b : Block lev) : ℝ := x (labelIndex (blockLabel lev b))


-- @@ L30-31 verbatim
def rowScalar (W : FrozenWeights) (lev : Level) : C0 →L[ℝ] ℝ :=
  ∑ b : Block lev, (W.row lev b) • c0Eval (labelIndex (blockLabel lev b))


-- @@ L33-35 verbatim
@[simp] theorem rowScalar_apply (W : FrozenWeights) (lev : Level) (x : C0) :
    rowScalar W lev x=∑ b : Block lev,W.row lev b*blockInput lev x b := by
  simp only [rowScalar,sum_apply,smul_apply,smul_eq_mul,c0Eval_apply,blockInput]


-- @@ L37-40 verbatim
def previousScalar (W : FrozenWeights) (lev : Level) : C0 →L[ℝ] ℝ :=
  match lev.2 with
  | 0 => c0Eval (rowIndex lev.1)
  | n+1 => rowScalar W (lev.1,n)


-- @@ L42-43 verbatim
def frozenCorrection (W : FrozenWeights) (γ : Label) : C0 →L[ℝ] ℝ :=
  W.vector γ.level ⟨γ.band,γ.tag⟩ • (previousScalar W γ.level-rowScalar W γ.level)


-- @@ L45-46 verbatim
@[simp] theorem frozenCorrection_apply (W : FrozenWeights) (γ : Label) (x : C0) :
    frozenCorrection W γ x=W.vector γ.level ⟨γ.band,γ.tag⟩*(previousScalar W γ.level x-rowScalar W γ.level x) := rfl


-- @@ L48-48 verbatim
def correction (γ : Label) (s : C0Ball) : ℝ := frozenCorrection (stateWeights s) γ s.val


-- @@ L50-53 verbatim
theorem blockInput_abs_le (lev : Level) (x : C0) (b : Block lev) :
    |blockInput lev x b|≤finiteRadius (blockCoordinates lev) x := by
  apply coordinate_le_finiteRadius
  exact mem_blockCoordinates.mpr ⟨blockLabel lev b,rfl,rfl⟩


-- @@ L55-61 verbatim
theorem finiteRadius_mono {I J : Finset ℕ} (h : I⊆J) (x : C0) : finiteRadius I x≤finiteRadius J x := by
  apply c0_norm_le _ (finiteRadius_nonneg _ _)
  intro k
  rw [finiteProjection_apply]
  split_ifs with hk
  · exact coordinate_le_finiteRadius x (h hk)
  · simpa using finiteRadius_nonneg J x


-- @@ L63-65 verbatim
theorem blockInput_le_radius (lev : Level) (x : C0) (b : Block lev) :
    |blockInput lev x b|≤localRadius lev x :=
  (blockInput_abs_le lev x b).trans (finiteRadius_mono Finset.subset_union_right x)


-- @@ L67-76 verbatim
theorem abs_finite_dot_le {A : Type*} [Fintype A] (u v : A → ℝ) {R : ℝ} (hv : ∀ a, |v a|≤R) :
    |∑ a,u a*v a| ≤ (∑ a,|u a|)*R := by
  calc
    _ ≤ ∑ a,|u a*v a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a,|u a| *R := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hv a) (abs_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm


-- @@ L78-81 verbatim
theorem rowScalar_bound (W : FrozenWeights) (lev : Level) (x : C0) {R : ℝ}
    (hR : 0≤R) (hv : ∀ b,|blockInput lev x b|≤R) : |rowScalar W lev x|≤2*R := by
  rw [rowScalar_apply]
  exact (abs_finite_dot_le _ _ hv).trans (mul_le_mul_of_nonneg_right (W.row_bound lev) hR)


-- @@ L83-85 verbatim
theorem rowScalar_local (W : FrozenWeights) (lev : Level) (x : C0) :
    |rowScalar W lev x|≤2*localRadius lev x :=
  rowScalar_bound W lev x (finiteRadius_nonneg _ _) (blockInput_le_radius lev x)


-- @@ L87-101 verbatim
theorem previousScalar_local (W : FrozenWeights) (lev : Level) (x : C0) :
    |previousScalar W lev x|≤2*localRadius lev x := by
  rcases lev with ⟨i,n⟩
  cases n with
  | zero =>
    change |x (rowIndex i)|≤2*localRadius (i,0) x
    have hle : |x (rowIndex i)|≤localRadius (i,0) x := by
      apply coordinate_le_finiteRadius
      exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
    have hz : 0≤localRadius (i,0) x := finiteRadius_nonneg _ _
    linarith
  | succ n =>
    apply rowScalar_bound W (i,n) x (finiteRadius_nonneg _ _)
    intro b
    exact (blockInput_abs_le _ _ b).trans (finiteRadius_mono Finset.subset_union_left x)


-- @@ L103-105 verbatim
theorem scalar_difference_bound (W : FrozenWeights) (lev : Level) (x : C0) :
    |previousScalar W lev x-rowScalar W lev x|≤4*localRadius lev x := by
  exact (abs_sub _ _).trans (by linarith [previousScalar_local W lev x,rowScalar_local W lev x])


-- @@ L107-112 verbatim
theorem frozenCorrection_local (W : FrozenWeights) (γ : Label) (x : C0) :
    |frozenCorrection W γ x|≤4*localRadius γ.level x := by
  rw [frozenCorrection_apply,abs_mul]
  calc
    _ ≤ 1*(4*localRadius γ.level x) := mul_le_mul (W.vector_bound _ _) (scalar_difference_bound W _ x) (abs_nonneg _) zero_le_one
    _ = _ := one_mul _


-- @@ L114-116 verbatim
theorem frozenCorrection_bound (W : FrozenWeights) (γ : Label) (x : C0) :
    |frozenCorrection W γ x|≤4*‖x‖ :=
  (frozenCorrection_local W γ x).trans (mul_le_mul_of_nonneg_left (finiteRadius_le _ _) (by norm_num))


-- @@ L118-121 verbatim
theorem frozenCorrection_distance (W : FrozenWeights) (γ : Label) (x y : C0) :
    |frozenCorrection W γ x-frozenCorrection W γ y|≤4*dist x y := by
  rw [← map_sub,dist_eq_norm]
  exact frozenCorrection_bound W γ (x-y)


-- @@ L123-128 verbatim
theorem rowScalar_weight_error (W V : FrozenWeights) (lev : Level) (x : C0) {q : ℝ}
    (h : localRadius lev x*(∑ b : Block lev,|W.row lev b-V.row lev b|)≤q) :
    |rowScalar W lev x-rowScalar V lev x|≤q := by
  rw [rowScalar_apply,rowScalar_apply,← Finset.sum_sub_distrib]
  simp only [← sub_mul]
  exact (abs_finite_dot_le _ _ (blockInput_le_radius lev x)).trans (by simpa only [mul_comm] using h)


-- @@ L130-132 verbatim
structure WeightError (W V : FrozenWeights) (x : C0) (q : ℝ) : Prop where
  vector : ∀ lev b, localRadius lev x*|W.vector lev b-V.vector lev b|≤q
  row : ∀ lev, localRadius lev x*(∑ b : Block lev,|W.row lev b-V.row lev b|)≤q


-- @@ L134-140 verbatim
theorem previousScalar_weight_error {W V : FrozenWeights} {x : C0} {q : ℝ}
    (hq : 0≤q) (h : WeightError W V x q) (lev : Level) :
    |previousScalar W lev x-previousScalar V lev x|≤q := by
  rcases lev with ⟨i,n⟩
  cases n with
  | zero => simpa only [previousScalar,sub_self,abs_zero] using hq
  | succ n => exact rowScalar_weight_error W V (i,n) x (h.row (i,n))


-- @@ L142-166 verbatim
theorem correction_weight_error {W V : FrozenWeights} {x : C0} {q : ℝ}
    (hq : 0≤q) (h : WeightError W V x q) (γ : Label) :
    |frozenCorrection W γ x-frozenCorrection V γ x|≤6*q := by
  let b : Block γ.level := ⟨γ.band,γ.tag⟩
  let a := previousScalar W γ.level x-rowScalar W γ.level x
  let a' := previousScalar V γ.level x-rowScalar V γ.level x
  have hb : |a|≤4*localRadius γ.level x := scalar_difference_bound W γ.level x
  have hs : |a-a'|≤2*q := by
    calc
      _ = |(previousScalar W γ.level x-previousScalar V γ.level x)-
          (rowScalar W γ.level x-rowScalar V γ.level x)| := by dsimp [a,a']; congr 1; ring
      _ ≤ |previousScalar W γ.level x-previousScalar V γ.level x|+
          |rowScalar W γ.level x-rowScalar V γ.level x| := abs_sub _ _
      _ ≤ q+q := add_le_add (previousScalar_weight_error hq h _) (rowScalar_weight_error W V _ x (h.row _))
      _ = 2*q := by ring
  calc
    _ = |(W.vector γ.level b-V.vector γ.level b)*a+V.vector γ.level b*(a-a')| := by
      simp only [frozenCorrection_apply]; dsimp only [a,a',b]; congr 1; ring
    _ ≤ |W.vector γ.level b-V.vector γ.level b| *|a|+|V.vector γ.level b| *|a-a'| := by
      simpa only [abs_mul] using abs_add_le ((W.vector γ.level b-V.vector γ.level b)*a) (V.vector γ.level b*(a-a'))
    _ ≤ |W.vector γ.level b-V.vector γ.level b| *(4*localRadius γ.level x)+1*(2*q) :=
      add_le_add (mul_le_mul_of_nonneg_left hb (abs_nonneg _))
        (mul_le_mul (V.vector_bound _ _) hs (abs_nonneg _) zero_le_one)
    _ ≤ 4*q+2*q := by nlinarith [h.vector γ.level b]
    _ = 6*q := by ring


-- @@ L168-168 verbatim
end

-- @@ L169-169 verbatim
end C0Absorption


-- @@ L171-171 verbatim
namespace C0Absorption

-- @@ L172-172 verbatim
noncomputable section

-- @@ L173-173 verbatim
open Set Filter Topology

-- @@ L174-174 verbatim
open scoped NNReal BigOperators ZeroAtInfty


-- @@ L176-177 verbatim
def mixedState (s t : C0Ball) (lev : Level) : C0Ball :=
  if localRadius lev t.val≤localRadius lev s.val then s else t


-- @@ L179-184 verbatim
def mixedWeights (s t : C0Ball) : FrozenWeights where
  vector := fun lev => blockVector lev (mixedState s t lev)
  row := fun lev => blockRow lev (mixedState s t lev)
  vector_bound := fun lev b => (stateWeights (mixedState s t lev)).vector_bound lev b
  row_bound := fun lev => (stateWeights (mixedState s t lev)).row_bound lev
  pairing := fun lev => (stateWeights (mixedState s t lev)).pairing lev


-- @@ L186-201 verbatim
theorem mixed_left_error (s t : C0Ball) :
    WeightError (stateWeights s) (mixedWeights s t) s.val (eta*dist s t) := by
  have hq : 0≤eta*dist s t := mul_nonneg eta_pos.le dist_nonneg
  constructor
  · intro lev b
    change localRadius lev s.val*|blockVector lev s b-blockVector lev (mixedState s t lev) b|≤_
    by_cases h : localRadius lev t.val≤localRadius lev s.val
    · simpa only [mixedState,h,↓reduceIte,sub_self,abs_zero,mul_zero] using hq
    · have hh := blockVector_weighted_distance lev s t b
      simpa only [mixedState,h,↓reduceIte,min_eq_left (le_of_not_ge h)] using hh
  · intro lev
    change localRadius lev s.val*(∑ b : Block lev,|blockRow lev s b-blockRow lev (mixedState s t lev) b|)≤_
    by_cases h : localRadius lev t.val≤localRadius lev s.val
    · simpa only [mixedState,h,↓reduceIte,sub_self,abs_zero,Finset.sum_const_zero,mul_zero] using hq
    · have hh := blockRow_weighted_distance lev s t
      simpa only [mixedState,h,↓reduceIte,min_eq_left (le_of_not_ge h)] using hh


-- @@ L203-218 verbatim
theorem mixed_right_error (s t : C0Ball) :
    WeightError (stateWeights t) (mixedWeights s t) t.val (eta*dist s t) := by
  have hq : 0≤eta*dist s t := mul_nonneg eta_pos.le dist_nonneg
  constructor
  · intro lev b
    change localRadius lev t.val*|blockVector lev t b-blockVector lev (mixedState s t lev) b|≤_
    by_cases h : localRadius lev t.val≤localRadius lev s.val
    · have hh := blockVector_weighted_distance lev t s b
      simpa only [mixedState,h,↓reduceIte,min_eq_left h,dist_comm t s] using hh
    · simpa only [mixedState,h,↓reduceIte,sub_self,abs_zero,mul_zero] using hq
  · intro lev
    change localRadius lev t.val*(∑ b : Block lev,|blockRow lev t b-blockRow lev (mixedState s t lev) b|)≤_
    by_cases h : localRadius lev t.val≤localRadius lev s.val
    · have hh := blockRow_weighted_distance lev t s
      simpa only [mixedState,h,↓reduceIte,min_eq_left h,dist_comm t s] using hh
    · simpa only [mixedState,h,↓reduceIte,sub_self,abs_zero,Finset.sum_const_zero,mul_zero] using hq


-- @@ L220-221 verbatim
theorem abs_sub_three (a b c d : ℝ) : |a-b|≤|a-c|+|c-d|+|d-b| :=
  (abs_sub_le a c b).trans (by linarith [abs_sub_le c d b])


-- @@ L223-223 verbatim
def correctionL : ℝ≥0 := 4+12/1000


-- @@ L225-225 verbatim
theorem correctionL_coe : (correctionL : ℝ)=4+12*eta := by norm_num [correctionL,eta]


-- @@ L227-241 verbatim
theorem correction_lipschitz (γ : Label) : LipschitzWith correctionL (correction γ) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [Real.dist_eq,correctionL_coe]
  let W := mixedWeights s t
  let q := eta*dist s t
  have hq : 0≤q := mul_nonneg eta_pos.le dist_nonneg
  have h1 : |correction γ s-frozenCorrection W γ s.val|≤6*q := correction_weight_error hq (mixed_left_error s t) γ
  have h2 : |frozenCorrection W γ t.val-correction γ t|≤6*q := by
    rw [abs_sub_comm]
    exact correction_weight_error hq (mixed_right_error s t) γ
  have h3 : |frozenCorrection W γ s.val-frozenCorrection W γ t.val|≤4*dist s t := frozenCorrection_distance W γ s.val t.val
  have h := abs_sub_three (correction γ s) (correction γ t) (frozenCorrection W γ s.val) (frozenCorrection W γ t.val)
  dsimp only [q] at h1 h2
  nlinarith


-- @@ L243-244 verbatim
theorem correction_local (γ : Label) (s : C0Ball) : |correction γ s|≤4*localRadius γ.level s.val :=
  frozenCorrection_local (stateWeights s) γ s.val


-- @@ L246-248 verbatim
theorem correction_bound (γ : Label) (s : C0Ball) : |correction γ s|≤4 := by
  have hs : ‖s.val‖≤1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using s.property
  exact (frozenCorrection_bound (stateWeights s) γ s.val).trans (by linarith)


-- @@ L250-251 verbatim
theorem correction_zero (γ : Label) : correction γ ⟨0,by simp⟩=0 := by
  exact map_zero (frozenCorrection (stateWeights _) γ)


-- @@ L253-259 verbatim
theorem correction_band_support {γ : Label} {s : C0Ball} (h : correction γ s≠0) :
    dist (prefixRestrict γ.band s) (bandPoint γ.band γ.tag) ≤ 2*dyadic γ.band := by
  have hv : bandVector γ.band γ.tag (prefixRestrict γ.band s)≠0 := by
    intro hv
    apply h
    simp only [correction,frozenCorrection_apply,stateWeights,blockVector,hv,mul_zero,zero_mul]
  exact (bandVector_support hv).le


-- @@ L261-267 verbatim
theorem correction_radius_support {γ : Label} {s : C0Ball} (h : correction γ s≠0)
    (hj : γ.band.val<levelJ γ.level) : ell γ.band≤localRadius γ.level s.val := by
  have ht : theta (levelJ γ.level) (localRadius γ.level s.val) γ.band≠0 := by
    intro ht
    apply h
    simp only [correction,frozenCorrection_apply,stateWeights,blockVector,ht,zero_mul]
  exact theta_lower_support hj (finiteRadius_nonneg _ _) ht


-- @@ L269-269 verbatim
end

-- @@ L270-270 verbatim
end C0Absorption


-- @@ L272-272 verbatim
end OAI
